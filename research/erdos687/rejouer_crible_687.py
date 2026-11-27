"""Rebuild the OpenAI interval sieve from pinned Apache-2.0 Lean sources."""
import argparse
import hashlib
from pathlib import Path
from urllib.request import urlopen


REVISION = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
BASE = f"https://raw.githubusercontent.com/openai/math/{REVISION}/lean/OAI/NumberTheory/Jacobsthal/"
FILES = {
    "Sieve/AlignedPrimeCongruence": "af13ee340862994be60d756cc725cfd1a0a004a5b32241a7d69bbea1dd0d960f",
    "Primes/LargePrimeDeletion": "35cce5c6b035a7150f015ba157cb674be8bb335c8d471f0a9ae90a084b5e815d",
    "Sieve/IntervalBoundingSieve": "0538292904c71f0ad88548465d064aea9020f5785f32d38f5d8b412c06d056d1",
    "Estimates/SquarefreeHarmonic": "2f639f278eaaeee3de289aabad296e26c926e88f2d055ec4d5178d63662feccb",
}


def get_source(name, checkout):
    relative = name + ".lean"
    if checkout:
        raw = (checkout / relative).read_bytes()
    else:
        with urlopen(BASE + relative, timeout=45) as response:
            raw = response.read()
    if hashlib.sha256(raw).hexdigest() != FILES[name]:
        raise ValueError(f"Unexpected source digest for {relative}")
    return raw.decode("utf-8")


def section(source, start, stop):
    begin = source.index(start)
    return source[begin:source.index(stop, begin + len(start))]


def make_module(checkout):
    partition, deletion, interval, squarefree = [get_source(name, checkout) for name in FILES]
    # The corresponding lemmas in the pinned Mathlib 4.33.1 have these names.
    for newer, older in (("ite_eq_right (not_le_of_gt hRq)", "if_neg (not_le_of_gt hRq)"),
                         ("Finset.one_le_prod₀", "Finset.one_le_prod")):
        if squarefree.count(newer) != 1:
            raise ValueError(f"Unexpected occurrence count for {newer}")
        squarefree = squarefree.replace(newer, older)
    imports = sorted({line for src in (partition, deletion, interval, squarefree)
                      for line in src.splitlines() if line.startswith("import Mathlib")})
    # Copy the finite-set definitions and their proofs verbatim. The two
    # analytic modules retain every declaration and their original namespaces.
    parts = [
        "/- Source: OpenAI math, Apache-2.0, commit " + REVISION + ".\n"
        "   Generated selection for the Lean 4.33.1 replay. Upstream license:\n"
        "   https://github.com/openai/math/blob/" + REVISION + "/lean/LICENSE -/",
        "\n".join(imports),
        "namespace OAI\nnamespace Erdos970",
        section(partition, "namespace NumberTheoryLean.SievePartition", "noncomputable def childCell"),
        section(partition, "omit [DecidableEq α] [LinearOrder ι] in\n@[simp] theorem mem_survivors",
                "omit [DecidableEq α] in"),
        section(partition, "def residueBad", "noncomputable def residueCandidates"),
        "end NumberTheoryLean.SievePartition",
        section(deletion, "namespace NumberTheoryLean.LargePrimeDeletion", "def largePrimeFactors"),
        section(deletion, "noncomputable def deletionCell", "theorem card_deletionCell_le_div_add_one"),
        section(deletion, "noncomputable def cutoffSurvivors", "def CompatibleSmallResidues"),
        section(deletion, "noncomputable def coprimeOffsets", "theorem candidate_subset_coprime_union_deletions"),
        "end NumberTheoryLean.LargePrimeDeletion\nend Erdos970\nend OAI",
        interval[interval.index("namespace OAI"):],
        squarefree[squarefree.index("namespace OAI"):],
    ]
    return "\n\n".join(parts)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--sources", type=Path,
                        help="Read files from the upstream Jacobsthal directory instead of HTTPS")
    args = parser.parse_args()
    args.output.write_text(make_module(args.sources), encoding="utf-8")
