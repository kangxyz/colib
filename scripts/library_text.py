"""Parse the small, shared formatting grammar for Library prose."""

import re


KEY = re.compile(r"[A-Za-z][A-Za-z0-9_-]*")
START = re.compile(r"\\\$|\$\$?|\\[()\[\]]|`|\[@|\bCOL-[0-9]{4,}\b")
MATH = {"$": "$", "$$": "$$", r"\(": r"\)", r"\[": r"\]"}
SCRIPT_DIGITS = {
    "_": str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉"),
    "^": str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹"),
}


def citation_parts(value):
    key, comma, locator = value.partition(",")
    key, locator = key.strip(), locator.strip()
    if not KEY.fullmatch(key) or (comma and not locator):
        raise ValueError(f"Invalid prose citation [@{value}]")
    return key, locator


def closing(text, start, delimiter, group):
    """Find a delimiter outside groups and escaped characters."""
    depth = 0
    index = start
    while index < len(text):
        if depth == 0 and text.startswith(delimiter, index):
            return index
        character = text[index]
        if character == "\\":
            index += 2
            continue
        if character == group[0]:
            depth += 1
        elif character == group[1]:
            depth -= 1
        index += 1
    return -1


def tokens(text):
    """Yield text, code, inline/display TeX, item IDs and bibliography citations."""
    position = 0
    while match := START.search(text, position):
        if match.start() > position:
            yield "text", text[position:match.start()]
        start = match.group()
        position = match.end()
        if start == r"\$":
            yield "text", "$"
            continue
        if start.startswith("COL-"):
            yield "item", start
            continue
        if start in MATH:
            delimiter = MATH[start]
            end = closing(text, position, delimiter, "{}")
            kind = "display" if start in ("$$", r"\[") else "math"
        elif start == "`":
            delimiter = "`"
            end = text.find(delimiter, position)
            kind = "code"
        elif start == "[@":
            delimiter = "]"
            end = closing(text, position, delimiter, "[]")
            kind = "citation"
        else:
            raise ValueError(f"Unexpected closing math delimiter {start}")
        if end == -1 or not (value := text[position:end]).strip():
            raise ValueError(f"Missing content or closing delimiter for {start}")
        if kind in ("code", "citation", "math") and "\n" in value:
            raise ValueError(f"Use one line for {kind} content")
        if kind == "citation":
            citation_parts(value)
        yield kind, value
        position = end + len(delimiter)
    if position < len(text):
        yield "text", text[position:]


def plain_text(text):
    parts = []
    for kind, value in tokens(text):
        if kind in ("math", "display"):
            value = re.sub(
                r"([_^])(?:\{([0-9]+)\}|([0-9]+))",
                lambda match: (match[2] or match[3]).translate(SCRIPT_DIGITS[match[1]]),
                value,
            )
        parts.append(value)
    return "".join(parts)
