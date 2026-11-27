"""Extract the published near-cover proof used by BorneRankin687.

Source: OpenAI, Improved Long Gaps Between Primes, Apache-2.0.
Pinned repository: https://github.com/openai/LongGapsBetweenPrimes
Commit: 03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b
"""

import argparse
import hashlib
from pathlib import Path
import re


SOURCE_SHA256 = "c0061db0f6b6c8e379d002a56eec14425368e959d3d3641a4e7aad481f069625"
ROOTS = {
    "eventually_covering_residues",
    "sieveDelta_lt_half",
    "coverEta_pos",
    "coverLength_eq",
    "eventually_coverScale_div_eight",
    "eventually_cover_parameters",
}
IMPORTS = (
    "Mathlib.Analysis.Convex.SpecificFunctions.Basic",
    "Mathlib.Analysis.PSeries",
    "Mathlib.Analysis.SpecialFunctions.ImproperIntegrals",
    "Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics",
    "Mathlib.Analysis.SumIntegralComparisons",
    "Mathlib.Combinatorics.Pigeonhole",
    "Mathlib.NumberTheory.Chebyshev",
    "Mathlib.NumberTheory.EulerProduct.Basic",
    "Mathlib.NumberTheory.Harmonic.Bounds",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.GCongr",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Positivity",
    "Mathlib.Tactic.Ring",
    "Mathlib.Tactic.Tauto",
)


def extract(source: Path) -> str:
    text = source.read_text(encoding="utf-8")
    if hashlib.sha256(text.encode()).hexdigest() != SOURCE_SHA256:
        raise ValueError("The source differs from the pinned upstream proof")
    matches = list(re.finditer(r"^(?:theorem|lemma|def|structure|abbrev)\s+([\w']+)", text, re.M))
    commands = {}
    for i, match in enumerate(matches):
        stop = matches[i + 1].start() if i + 1 < len(matches) else text.index("#print axioms")
        commands[match[1]] = text[match.start():stop].split("\n/--", 1)[0].rstrip()
    keep = set(ROOTS)
    while True:
        expanded = keep.union(*(set(re.findall(r"[\w']+", commands[k])) & commands.keys()
                                for k in keep))
        if expanded == keep:
            break
        keep = expanded
    prefix = text[:text.index("noncomputable section") + len("noncomputable section")]
    prefix = prefix.replace("import Mathlib\n", "\n".join(f"import {name}" for name in IMPORTS) + "\n")
    selected = [cmd for name, cmd in commands.items() if name in keep]
    return "\n\n".join([prefix, *selected, "end\nend LongGapsBetweenPrimes\n"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.source.resolve() == args.output.resolve():
        parser.error("Choose a separate output file")
    result = extract(args.source)
    args.output.write_text(result, encoding="utf-8", newline="\n")
