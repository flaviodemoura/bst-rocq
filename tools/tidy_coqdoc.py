#!/usr/bin/env python3
"""Clean up rocq doc LaTeX output before it is typeset as boxes.

Removes blank lines (\\coqdocemptyline) at the start and end of each
coqdoccode block, and then drops blocks that became empty, so that every
coqdoccode environment (typeset as a tcolorbox) holds actual code.

Each remaining block gets the key of the first definition it contains as an
optional argument, \\begin{coqdoccode}[<key>], which
paa-2026-2-projeto-enunciado.tex uses to link the box title to that definition
in the repository.

Usage: tidy_coqdoc.py <file.v.tex>...   (files are rewritten in place)
"""
import re
import sys

LEADING = re.compile(r"(\\begin\{coqdoccode\}\n)(?:\\coqdocemptyline\n)+")
TRAILING = re.compile(r"(?:\\coqdocemptyline\n)+(\\end\{coqdoccode\})")
EMPTY = re.compile(r"\\begin\{coqdoccode\}\s*\\end\{coqdoccode\}\n?")
BLOCK = re.compile(r"\\begin\{coqdoccode\}\n(.*?\\end\{coqdoccode\})", re.S)
DEF = re.compile(r"\\coqdef\{([^}]*)\}")
BINDER = re.compile(r":\d+$")  # bound variables, e.g. BST.bst.insert.t:1


def first_definition(body: str):
    for key in DEF.findall(body):
        if not BINDER.search(key) and ".:::" not in key:  # skip notations too
            return key
    return None


def add_key(match: re.Match) -> str:
    key = first_definition(match.group(1))
    opt = f"[{key}]" if key else ""
    return f"\\begin{{coqdoccode}}{opt}\n{match.group(1)}"


def tidy(text: str) -> str:
    text = LEADING.sub(r"\1", text)
    text = TRAILING.sub(r"\1", text)
    text = EMPTY.sub("", text)
    return BLOCK.sub(add_key, text)


for path in sys.argv[1:]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    with open(path, "w", encoding="utf-8") as f:
        f.write(tidy(text))
