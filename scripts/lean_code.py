"""Highlight Lean source for the static Library while preserving its text."""

from html import escape
import re


KEYWORDS = set(
    "abbrev all as attribute axiom by class def deriving do else end example export "
    "extends fun have if import in include inductive infix infixl infixr initialize "
    "instance lemma let local macro match meta module mutual namespace noncomputable "
    "notation omit opaque open partial postulate private protected public return "
    "scoped section set_option structure syntax then theorem universe variable where with"
    .split()
)
SORTS = {"Prop", "Sort", "Type"}
TOKEN = re.compile(
    r"(?P<comment>--[^\n]*|/-)"
    r"""|(?P<string>"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\\n])')"""
    r"|(?P<quoted>«[^»]*»)"
    r"|(?P<command>#[A-Za-z_][\w']*)"
    r"|(?P<identifier>[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*)"
    r"|(?P<number>0[xX][0-9a-fA-F_]+|0[bB][01_]+|\d[\d_]*(?:\.\d[\d_]*)?)"
    r"|(?P<operator>:=|=>|<-|->|[∀∃λ→←↔↦⟶≃⟷≫∘⊗×⊕=<>≤≥≠¬+\-*/])"
)
COMMENT_DELIMITER = re.compile(r"/-|-/")


def block_comment_end(source, start):
    depth = 1
    for match in COMMENT_DELIMITER.finditer(source, start):
        depth += 1 if match[0] == "/-" else -1
        if depth == 0:
            return match.end()
    return len(source)


def highlight(source):
    fragments = []
    position = 0
    while match := TOKEN.search(source, position):
        fragments.append(escape(source[position:match.start()]))
        end = match.end()
        kind = match.lastgroup
        if kind == "comment" and match[0] == "/-":
            end = block_comment_end(source, end)
        if kind == "identifier" and match[0] in KEYWORDS:
            kind = "keyword"
        elif kind == "identifier" and match[0] in SORTS:
            kind = "sort"
        token = escape(source[match.start():end])
        if kind in {"identifier", "quoted"}:
            fragments.append(token)
        else:
            fragments.append(f'<span class="lean-{kind}">{token}</span>')
        position = end
    fragments.append(escape(source[position:]))
    return "".join(fragments)
