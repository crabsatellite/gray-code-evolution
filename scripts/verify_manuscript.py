#!/usr/bin/env python3
"""Fail closed on manuscript, bibliography, and theorem-map drift."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper" / "latex" / "gray_code_evolution.tex"
if not TEX.exists():
    TEX = ROOT / "paper" / "gray_code_evolution.tex"
BIB = ROOT / "paper" / "latex" / "references.bib"
THEOREM_MAP = ROOT / "paper" / "theorem-map.json"
LEAN = ROOT / "lean4"
LEAN_THEOREM_MAP = LEAN / "Hamilton" / "HamiltonianCyclesTheoremMap.lean"


def fail(message: str) -> None:
    raise SystemExit(f"[manuscript:error] {message}")


def cite_keys(text: str) -> set[str]:
    keys: set[str] = set()
    for match in re.finditer(r"\\cite(?:\[[^]]*\])?\{([^}]*)\}", text):
        keys.update(key.strip() for key in match.group(1).split(",") if key.strip())
    return keys


def bibtex_keys(text: str) -> set[str]:
    return set(re.findall(r"(?m)^\s*@[A-Za-z]+\s*\{\s*([^,\s]+)\s*,", text))


def declaration_sources() -> str:
    return "\n".join(
        path.read_text(encoding="utf-8-sig")
        for path in LEAN.rglob("*.lean")
        if ".lake" not in path.parts
    )


def main() -> int:
    tex = TEX.read_text(encoding="utf-8")
    cited = cite_keys(tex)
    inline = set(re.findall(r"\\bibitem\{([^}]+)\}", tex))
    if cited != inline:
        fail(
            "citation key sets differ: "
            f"cited={sorted(cited)}, bibitem={sorted(inline)}"
        )
    if BIB.exists():
        structured = bibtex_keys(BIB.read_text(encoding="utf-8"))
        if cited != structured:
            fail(
                "citation key sets differ: "
                f"cited={sorted(cited)}, bibtex={sorted(structured)}"
            )

    required_reference_tokens = {
        "HHMW": ("10.1090/tran/8199", "1906.06069"),
        "HHNP": ("10.1016/j.dam.2008.06.018",),
        "HM": ("10.1007/s11856-021-2186-1", "1911.12078"),
        "K": ("10.1016/0012-365X(72)90041-6",),
        "MNW": ("2401.14963",),
        "M": ("10.37236/11023", "2202.01280", "(2023)"),
        "Pet": ("10.1137/110847202", "1108.5761"),
        "S": ("10.1016/S0012-365X(99)00273-3",),
        "SU": ("10.1016/0012-365X(91)90376-D",),
    }
    for key, tokens in required_reference_tokens.items():
        match = re.search(
            rf"\\bibitem\{{{re.escape(key)}\}}(.*?)(?=\\bibitem|\\end\{{thebibliography\}})",
            tex,
            re.DOTALL,
        )
        if match is None:
            fail(f"missing inline bibliography entry {key}")
        for token in tokens:
            if token not in match.group(1):
                fail(f"inline bibliography entry {key} is missing {token!r}")

    forbidden = {
        r"\bR\d{3}[A-Z0-9-]*\b": "internal round identifier",
        r"\bGATE-?\d+\b": "internal gate identifier",
        r"\bPLAN_[A-Z0-9_]+\b": "internal plan identifier",
        r"\bfrontier\b": "internal frontier language",
        r"\b(?:ChatGPT|large language model|AI-generated)\b": "AI-process language",
        r"github\.com": "non-archival repository URL",
    }
    for pattern, description in forbidden.items():
        if re.search(pattern, tex, re.IGNORECASE):
            fail(f"{description} found in manuscript")

    for doi in ("10.5281/zenodo.21316751", "10.5281/zenodo.21316750"):
        if doi not in tex:
            fail(f"missing archival DOI {doi}")

    claims = json.loads(THEOREM_MAP.read_text(encoding="utf-8"))
    sources = declaration_sources()
    lean_map = LEAN_THEOREM_MAP.read_text(encoding="utf-8")
    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    for claim in claims:
        label = claim["label"]
        if label not in labels:
            fail(f"theorem-map label is absent from manuscript: {label}")
        for name in claim["lean"]:
            pattern = rf"\b(?:theorem|lemma|def|noncomputable\s+def)\s+{re.escape(name)}\b"
            if re.search(pattern, sources) is None:
                fail(f"theorem-map declaration is absent from Lean sources: {name}")
            if f"\\leanname{{{name}}}" not in tex:
                fail(f"theorem-map declaration is absent from manuscript table: {name}")
            check_pattern = rf"(?m)^\s*#check\s+(?:[A-Za-z_][A-Za-z0-9_']*\.)*{re.escape(name)}\s*$"
            if re.search(check_pattern, lean_map) is None:
                fail(f"theorem-map declaration is not kernel-checked by the Lean map: {name}")

    print(
        f"[manuscript:ok] citations={len(cited)} theorem_map={len(claims)} "
        "archive_dois=2"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
