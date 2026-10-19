"""
Telegram-бот: проверяет почтовый ящик Mail.ru по IMAP и присылает
в группу Telegram новые письма — заголовок, текст и вложенные файлы.

Все секреты читаются из файла .env (см. .env.example).
"""

import asyncio
import html
import logging
import mimetypes
import os
import re
import sys
from collections.abc import Awaitable, Callable
from dataclasses import dataclass, field
from email import message_from_bytes, policy
from email.header import decode_header, make_header
from email.message import EmailMessage
from email.utils import parseaddr, parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from typing import TypeVar

from aiogram import Bot
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramAPIError, TelegramRetryAfter
from aiogram.types import BufferedInputFile, Message, ReplyParameters
from dotenv import load_dotenv
from imapclient import IMAPClient
from imapclient.exceptions import IMAPClientError

# --- Константы ---------------------------------------------------------------

IMAP_HOST = "imap.mail.ru"
IMAP_PORT = 993
IMAP_FOLDER = "INBOX"
CHECK_INTERVAL_SECONDS = 60
IMAP_TIMEOUT_SECONDS = 60

BASE_DIR = Path(__file__).resolve().parent
LAST_UID_FILE = BASE_DIR / "last_uid.txt"

# В GitHub Actions логи публичного репозитория видны всем,
# поэтому там не пишем в лог имена файлов и имя бота
IN_GITHUB_ACTIONS = os.getenv("GITHUB_ACTIONS") == "true"

# Письмо целиком; PEEK не помечает его прочитанным
FULL_FETCH_KEY = b"BODY.PEEK[]"
FULL_RESPONSE_KEY = b"BODY[]"

# Сколько писем максимум забирать за одну проверку (остальные — в следующий раз),
# чтобы не держать в памяти слишком много вложений сразу
MAX_MAILS_PER_CHECK = 10

# Лимиты Telegram: сообщение — 4096 символов (считаются после разбора HTML-разметки),
# файл от бота — 50 МБ. Кусок текста берём с запасом под заголовок письма.
TEXT_CHUNK_CHARS = 3500
MAX_BODY_CHARS = 14000
MAX_ATTACHMENT_BYTES = 50 * 1024 * 1024

# --- Логирование -------------------------------------------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(BASE_DIR / "bot.log", encoding="utf-8"),
    ],
)
logger = logging.getLogger("mail_notifier")


# --- Конфигурация ------------------------------------------------------------

@dataclass(frozen=True)
class Config:
    telegram_token: str
    telegram_chat_id: int
    mail_user: str
    mail_password: str


def load_config() -> Config:
    """Читает настройки из .env и проверяет, что всё заполнено."""
    load_dotenv(BASE_DIR / ".env")

    required = [
        "TELEGRAM_BOT_TOKEN",
        "TELEGRAM_CHAT_ID",
        "MAILRU_USER",
        "MAILRU_APP_PASSWORD",
    ]
    missing = [name for name in required if not os.getenv(name)]
    if missing:
        raise RuntimeError(
            "Не заданы переменные окружения: " + ", ".join(missing)
            + ". Заполните файл .env по образцу .env.example."
        )

    try:
        chat_id = int(os.environ["TELEGRAM_CHAT_ID"])
    except ValueError as exc:
        raise RuntimeError(
            "TELEGRAM_CHAT_ID должен быть числом (для групп обычно начинается с -100)."
        ) from exc

    return Config(
        telegram_token=os.environ["TELEGRAM_BOT_TOKEN"],
        telegram_chat_id=chat_id,
        mail_user=os.environ["MAILRU_USER"],
        mail_password=os.environ["MAILRU_APP_PASSWORD"],
    )


# --- Хранение последнего UID -------------------------------------------------

def read_last_uid() -> int | None:
    """Возвращает последний обработанный UID или None, если файла ещё нет."""
    if not LAST_UID_FILE.exists():
        return None
    try:
        return int(LAST_UID_FILE.read_text(encoding="utf-8").strip())
    except ValueError:
        logger.warning("Файл %s повреждён, он будет перезаписан.", LAST_UID_FILE.name)
        return None


def save_last_uid(uid: int) -> None:
    """Атомарно сохраняет UID: пишем во временный файл и переименовываем."""
    tmp_file = LAST_UID_FILE.with_suffix(".tmp")
    tmp_file.write_text(str(uid), encoding="utf-8")
    tmp_file.replace(LAST_UID_FILE)


# --- Разбор письма -----------------------------------------------------------

@dataclass(frozen=True)
class Attachment:
    filename: str
    data: bytes


@dataclass
class MailInfo:
    uid: int
    sender: str
    subject: str
    date: str
    body: str
    attachments: list[Attachment] = field(default_factory=list)


def decode_mime(value: str | None) -> str:
    """Декодирует MIME-заголовок (=?UTF-8?B?...?=) в обычную строку."""
    if not value:
        return ""
    try:
        return str(make_header(decode_header(str(value)))).strip()
    except Exception:  # noqa: BLE001 — кривые заголовки встречаются часто
        return str(value).strip()


def format_sender(raw_from: str | None) -> str:
    """Формирует строку отправителя вида «Имя <адрес>»."""
    decoded = decode_mime(raw_from)
    name, address = parseaddr(decoded)
    if name and address:
        return f"{name} <{address}>"
    return address or decoded or "(неизвестный отправитель)"


def format_date(raw_date: str | None) -> str:
    """Приводит дату письма к виду ДД.ММ.ГГГГ ЧЧ:ММ (часовой пояс письма)."""
    if not raw_date:
        return "(дата не указана)"
    try:
        dt = parsedate_to_datetime(str(raw_date))
        return dt.strftime("%d.%m.%Y %H:%M %z").strip()
    except (TypeError, ValueError):
        return str(raw_date).strip()


class _HTMLToText(HTMLParser):
    """Простейшее преобразование HTML-письма в читаемый текст."""

    BLOCK_TAGS = {"p", "div", "tr", "li", "h1", "h2", "h3", "h4", "h5", "h6", "blockquote", "table"}
    SKIP_TAGS = {"script", "style", "head", "title"}

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self._skip_depth = 0

    def handle_starttag(self, tag: str, attrs) -> None:
        if tag in self.SKIP_TAGS:
            self._skip_depth += 1
        elif tag == "br":
            self.parts.append("\n")
        elif tag in self.BLOCK_TAGS:
            self.parts.append("\n")
        elif tag == "td":
            self.parts.append(" ")

    def handle_endtag(self, tag: str) -> None:
        if tag in self.SKIP_TAGS:
            self._skip_depth = max(0, self._skip_depth - 1)
        elif tag in self.BLOCK_TAGS:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if not self._skip_depth:
            self.parts.append(data)


def html_to_text(markup: str) -> str:
    parser = _HTMLToText()
    parser.feed(markup)
    parser.close()
    return "".join(parser.parts)


def normalize_text(text: str) -> str:
    """Убирает лишние пробелы и пустые строки."""
    text = text.replace("\r\n", "\n").replace("\r", "\n").replace("\xa0", " ")
    lines = [re.sub(r"[ \t]+", " ", line).strip() for line in text.split("\n")]
    text = "\n".join(lines)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


def get_part_text(part: EmailMessage) -> str:
    """Достаёт текст из части письма с учётом кодировки."""
    try:
        return part.get_content()
    except (LookupError, UnicodeDecodeError):
        # Неизвестная или неверно указанная кодировка — декодируем «как получится»
        payload = part.get_payload(decode=True) or b""
        try:
            return payload.decode(part.get_content_charset() or "utf-8", errors="replace")
        except LookupError:
            return payload.decode("utf-8", errors="replace")


def extract_body(msg: EmailMessage) -> tuple[str, EmailMessage | None]:
    """Возвращает текст письма и часть, из которой он взят."""
    body_part = msg.get_body(preferencelist=("plain", "html"))
    if body_part is None:
        return "", None
    text = get_part_text(body_part)
    if body_part.get_content_subtype() == "html":
        text = html_to_text(text)
    return normalize_text(text), body_part


def collect_attachments(part: EmailMessage, body_part: EmailMessage | None, out: list[Attachment]) -> None:
    """Рекурсивно собирает вложенные файлы письма."""
    if part is body_part:
        return

    content_type = part.get_content_type()
    filename = part.get_filename()

    # Пересланное письмо целиком — отправляем как .eml
    if content_type == "message/rfc822":
        inner = part.get_payload(0)
        subject = decode_mime(inner.get("Subject")) or "письмо"
        out.append(Attachment(filename or f"{safe_filename(subject)}.eml", inner.as_bytes()))
        return

    if part.is_multipart():
        for sub in part.iter_parts():
            collect_attachments(sub, body_part, out)
        return

    disposition = part.get_content_disposition()
    # Альтернативные версии текста (например, HTML рядом с plain) — не файлы
    if disposition != "attachment" and not filename:
        return
    # Картинки, встроенные в оформление письма (логотипы, подписи), пропускаем
    if disposition != "attachment" and part.get("Content-ID") and part.get_content_maintype() == "image":
        return

    data = part.get_payload(decode=True) or b""
    if not filename:
        extension = mimetypes.guess_extension(content_type) or ".bin"
        filename = f"вложение{extension}"
    out.append(Attachment(safe_filename(filename), data))


def safe_filename(name: str) -> str:
    """Убирает из имени файла символы, недопустимые в Windows и Telegram."""
    name = re.sub(r'[\\/:*?"<>|\r\n\t]+', "_", name).strip(" .")
    return name[:150] or "файл"


def parse_mail(uid: int, raw: bytes) -> MailInfo:
    msg = message_from_bytes(raw, policy=policy.default)
    body, body_part = extract_body(msg)
    attachments: list[Attachment] = []
    collect_attachments(msg, body_part, attachments)
    return MailInfo(
        uid=uid,
        sender=format_sender(msg.get("From")),
        subject=decode_mime(msg.get("Subject")) or "(без темы)",
        date=format_date(msg.get("Date")),
        body=body,
        attachments=attachments,
    )


# --- Работа с почтой ---------------------------------------------------------

def fetch_new_mails(config: Config, last_uid: int | None) -> tuple[list[MailInfo], int]:
    """
    Подключается к IMAP и возвращает список новых писем и максимальный UID в ящике.

    Функция синхронная (imapclient блокирующий), поэтому вызывается
    через asyncio.to_thread, чтобы не блокировать цикл событий.
    """
    with IMAPClient(IMAP_HOST, port=IMAP_PORT, ssl=True, timeout=IMAP_TIMEOUT_SECONDS) as client:
        client.login(config.mail_user, config.mail_password)
        # readonly=True — бот ничего не меняет в ящике
        client.select_folder(IMAP_FOLDER, readonly=True)

        all_uids = client.search(["ALL"])
        max_uid = max(all_uids) if all_uids else 0

        # Первый запуск: запоминаем текущее состояние, старые письма не присылаем
        if last_uid is None:
            return [], max_uid

        # Диапазон "N:*" по стандарту IMAP всегда включает последнее письмо,
        # даже если его UID меньше N, поэтому дополнительно фильтруем
        new_uids = sorted(uid for uid in client.search(["UID", f"{last_uid + 1}:*"]) if uid > last_uid)
        new_uids = new_uids[:MAX_MAILS_PER_CHECK]
        if not new_uids:
            return [], max_uid

        mails: list[MailInfo] = []
        for uid in new_uids:
            # Забираем письма по одному, чтобы не держать все вложения в памяти
            data = client.fetch([uid], [FULL_FETCH_KEY]).get(uid)
            raw = data.get(FULL_RESPONSE_KEY) if data else None
            if not raw:
                logger.warning("Не удалось получить письмо UID=%s", uid)
                continue
            try:
                mails.append(parse_mail(uid, raw))
            except Exception:  # noqa: BLE001 — одно «кривое» письмо не должно ломать остальные
                logger.exception("Не удалось разобрать письмо UID=%s, отправлю только заголовок", uid)
                mails.append(MailInfo(uid, "(не удалось разобрать)", "(не удалось разобрать)", "", ""))
        return mails, max_uid


# --- Работа с Telegram -------------------------------------------------------

T = TypeVar("T")


def log_name(attachment: "Attachment", index: int) -> str:
    """Имя вложения для лога: в GitHub Actions — только порядковый номер."""
    return f"№{index}" if IN_GITHUB_ACTIONS else attachment.filename


async def with_retry(action: Callable[[], Awaitable[T]]) -> T:
    """Выполняет запрос к Telegram; при флуд-контроле ждёт и повторяет один раз."""
    try:
        return await action()
    except TelegramRetryAfter as exc:
        logger.warning("Telegram просит подождать %s с.", exc.retry_after)
        await asyncio.sleep(exc.retry_after)
        return await action()


def split_text(text: str, limit: int) -> list[str]:
    """Делит текст на куски не длиннее limit, по возможности по границе строки."""
    chunks: list[str] = []
    while len(text) > limit:
        cut = text.rfind("\n", 0, limit)
        if cut < limit // 2:
            cut = text.rfind(" ", 0, limit)
        if cut < limit // 2:
            cut = limit
        chunks.append(text[:cut].rstrip())
        text = text[cut:].lstrip()
    if text:
        chunks.append(text)
    return chunks


def build_messages(mail: MailInfo) -> list[str]:
    """Формирует сообщения: заголовок письма + его текст (HTML, всё экранировано)."""
    header = (
        "📧 <b>Новое письмо</b>\n\n"
        f"<b>От:</b> {html.escape(mail.sender)}\n"
        f"<b>Тема:</b> {html.escape(mail.subject)}\n"
        f"<b>Дата:</b> {html.escape(mail.date)}"
    )
    if mail.attachments:
        header += f"\n<b>Вложений:</b> {len(mail.attachments)}"

    body = mail.body or "(письмо без текста)"
    truncated = len(body) > MAX_BODY_CHARS
    if truncated:
        body = body[:MAX_BODY_CHARS]

    chunks = [html.escape(chunk) for chunk in split_text(body, TEXT_CHUNK_CHARS)]
    if truncated:
        chunks[-1] += "\n\n<i>… текст обрезан, полностью письмо — в почтовом ящике</i>"

    messages = [f"{header}\n\n{chunks[0]}"]
    messages.extend(chunks[1:])
    return messages


async def send_mail(bot: Bot, chat_id: int, mail: MailInfo) -> None:
    """Отправляет письмо в Telegram: текст, затем вложения ответом на первое сообщение."""
    messages = build_messages(mail)

    # Первое сообщение обязательно: если оно не ушло, письмо будет отправлено заново
    first: Message = await with_retry(lambda: bot.send_message(chat_id, messages[0]))
    reply = ReplyParameters(message_id=first.message_id, allow_sending_without_reply=True)

    # Остальное отправляем «по возможности»: ошибка не должна приводить к дублю заголовка
    for text in messages[1:]:
        try:
            await with_retry(lambda text=text: bot.send_message(chat_id, text, reply_parameters=reply))
        except TelegramAPIError as exc:
            logger.error("UID=%s: не удалось отправить продолжение текста: %s", mail.uid, exc)

    for index, attachment in enumerate(mail.attachments, start=1):
        if len(attachment.data) > MAX_ATTACHMENT_BYTES:
            size_mb = len(attachment.data) / 1024 / 1024
            logger.warning("UID=%s: файл %s слишком большой (%.1f МБ)", mail.uid, log_name(attachment, index), size_mb)
            await send_note(
                bot, chat_id, reply,
                f"⚠️ Файл <b>{html.escape(attachment.filename)}</b> ({size_mb:.1f} МБ) больше 50 МБ — "
                "Telegram не позволяет боту его отправить. Откройте его в почте.",
            )
            continue

        document = BufferedInputFile(attachment.data, filename=attachment.filename)
        try:
            await with_retry(
                lambda document=document: bot.send_document(chat_id, document, reply_parameters=reply)
            )
            logger.info("UID=%s: отправлен файл %s", mail.uid, log_name(attachment, index))
        except TelegramAPIError as exc:
            logger.error("UID=%s: не удалось отправить файл %s: %s", mail.uid, log_name(attachment, index), exc)
            await send_note(
                bot, chat_id, reply,
                f"⚠️ Не удалось отправить файл <b>{html.escape(attachment.filename)}</b>. Откройте его в почте.",
            )


async def send_note(bot: Bot, chat_id: int, reply: ReplyParameters, text: str) -> None:
    """Служебное сообщение о проблеме с вложением; его ошибки только логируются."""
    try:
        await with_retry(lambda: bot.send_message(chat_id, text, reply_parameters=reply))
    except TelegramAPIError as exc:
        logger.error("Не удалось отправить служебное сообщение: %s", exc)


# --- Основной цикл -----------------------------------------------------------

async def check_mail_once(bot: Bot, config: Config) -> None:
    """Одна итерация: забрать новые письма и переслать их в Telegram."""
    last_uid = read_last_uid()
    mails, max_uid = await asyncio.to_thread(fetch_new_mails, config, last_uid)

    if last_uid is None:
        save_last_uid(max_uid)
        logger.info("Первый запуск: начальный UID = %s, старые письма пропущены.", max_uid)
        return

    if max_uid < last_uid:
        # Такое бывает, если на сервере сменился UIDVALIDITY (ящик пересоздан)
        logger.warning(
            "Максимальный UID на сервере (%s) меньше сохранённого (%s). Сбрасываю счётчик.",
            max_uid, last_uid,
        )
        save_last_uid(max_uid)
        return

    if not mails:
        logger.info("Новых писем нет.")
        return

    logger.info("Новых писем: %s", len(mails))
    for mail in mails:
        await send_mail(bot, config.telegram_chat_id, mail)
        # Сохраняем UID после каждого отправленного письма, чтобы при сбое
        # не потерять и не продублировать уведомления
        save_last_uid(mail.uid)
        logger.info("Отправлено письмо UID=%s (вложений: %s)", mail.uid, len(mail.attachments))


async def run_check(bot: Bot, config: Config) -> bool:
    """Проверка почты с обработкой ошибок. Возвращает True, если всё прошло успешно."""
    try:
        await check_mail_once(bot, config)
        return True
    except IMAPClientError as exc:
        # Сюда попадает и ошибка авторизации (неверный пароль приложения)
        logger.error("Ошибка IMAP: %s", exc)
    except TelegramAPIError as exc:
        logger.error("Ошибка Telegram API: %s", exc)
    except (OSError, TimeoutError) as exc:
        logger.error("Сетевая ошибка: %s", exc)
    except Exception:  # noqa: BLE001 — бот не должен падать из-за одной итерации
        logger.exception("Непредвиденная ошибка при проверке почты")
    return False


async def main(once: bool) -> int:
    """
    once=False — работать постоянно, проверяя почту раз в CHECK_INTERVAL_SECONDS.
    once=True  — одна проверка и выход (для запуска по расписанию, например в GitHub Actions).
    """
    try:
        config = load_config()
    except RuntimeError as exc:
        logger.critical("%s", exc)
        return 1

    bot = Bot(
        token=config.telegram_token,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )

    try:
        try:
            me = await bot.get_me()
        except TelegramAPIError as exc:
            logger.critical("Не удалось подключиться к Telegram (проверьте токен): %s", exc)
            return 1

        name = "" if IN_GITHUB_ACTIONS else f" @{me.username}"
        if once:
            logger.info("Бот%s: разовая проверка почты.", name)
            return 0 if await run_check(bot, config) else 1

        logger.info("Бот%s запущен. Интервал проверки: %s с.", name, CHECK_INTERVAL_SECONDS)
        while True:
            await run_check(bot, config)
            await asyncio.sleep(CHECK_INTERVAL_SECONDS)
    finally:
        await bot.session.close()


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main(once="--once" in sys.argv)))
    except KeyboardInterrupt:
        logger.info("Бот остановлен пользователем.")
