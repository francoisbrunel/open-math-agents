"""Assemble the upper bound for the upstream Jacobsthal Lean project."""
import argparse
import hashlib
from pathlib import Path

from rejouer_mertens_687 import make_module


HERE = Path(__file__).resolve().parent
FC_REVISION = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"


def between(text, start, stop):
    begin = text.index(start)
    return text[begin:text.index(stop, begin + len(start))].strip()


def file_text(name):
    return (HERE / name).read_text(encoding="utf-8")


def verified_definition(text, start, digest):
    definition = between(text, start, "\n\n")
    if hashlib.sha256(definition.encode("utf-8")).hexdigest() != digest:
        raise ValueError(f"Catalog definition differs from revision {FC_REVISION}")
    return definition


def namespace_body(name):
    text = file_text(name + ".lean")
    return text[text.index("namespace " + name):]


def assemble(fc, mertens, general=False):
    erdos = (fc / "FormalConjectures/ErdosProblems/687.lean").read_text(encoding="utf-8")
    green = (fc / "FormalConjectures/GreensOpenProblems/46.lean").read_text(encoding="utf-8")
    cover = verified_definition(green, "def IsCoveredByResidues ",
        "62e720cf3b662220a58051e7c7febd7714aaab41b9704eeddff2250b4f8c2f6b")
    target = verified_definition(erdos, "noncomputable def Y ",
        "c7d629df5dace6fab1c03e38098230029e682fe2495933cebf1107c061a25e8e")
    reduction = "OMA.R_Erdos687_erdos_687_variants_iwaniec_R2"
    replay_file = HERE / "ReductionIwaniec.lean"
    if not replay_file.is_file():
        replay_file = HERE / "reductions/Erdos687.erdos_687.variants.iwaniec.R2.lean"
    finite = replay_file.read_text(encoding="utf-8")
    harmonic = file_text("Harmonique687.lean")
    progression = file_text("Progressions687.lean")
    parts = [
        "import Mathlib\nimport SourcePubliee687\n"
        "import OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic",
        "/-! Erdős 687(i), upper bound. Green46.IsCoveredByResidues and Erdos687.Y\n"
        "are copied verbatim from google-deepmind/formal-conjectures, Apache-2.0,\n"
        f"revision {FC_REVISION}. -/",
        "open scoped BigOperators Asymptotics",
        "namespace Green46\n" + cover + "\nend Green46",
        "namespace Erdos687\n" + target + "\nend Erdos687",
        "namespace " + reduction + "\n" + between(finite, "theorem survivor_le_sum ", "theorem main ")
        + "\nend " + reduction,
        "namespace Transfert687\n" + between(file_text("Transfert687.lean"), "def survivors ",
                                            "/-- The parity") + "\nend Transfert687",
        between(progression, "namespace Progressions687", "/-- A uniform bound")
        + "\nend Progressions687",
        between(harmonic, "namespace Harmonique687", "/-- The harmonic estimate")
        + "\nend Harmonique687",
        make_module(mertens).split("import Mathlib", 1)[1],
    ]
    for name in ["GainVariable687", "CribleTransfert687", "StockSource687"]:
        parts.append(namespace_body(name))
    parts.append("""open Filter in
theorem erdos687_log_saving :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  StockSource687.gain_of_interface SourcePubliee687.source_bound

#print axioms erdos687_log_saving""")
    if general:
        definitions = (fc / "FormalConjectures/ErdosProblems/970.lean").read_text(encoding="utf-8")
        bound = verified_definition(definitions, "def IsJacobsthalBound ",
            "0065f876c75bcd824879740c8be1a96d6c61cb1ab06acfe360e514730d68b2aa")
        function = verified_definition(definitions, "noncomputable def jacobsthalFunction ",
            "24ac30e896ed43756aa42882c50a2ee1fe704564fda231c5de85a6c20cef4684")
        parts.append("namespace Erdos970\n" + bound + "\n\n" + function + "\nend Erdos970")
        parts.extend(namespace_body(name) for name in ["SurvieTotale687", "JacobsthalExtension687"])
        parts.append("""open Filter in
theorem jacobsthal_log_saving :
    ∃ η : ℝ, 0 < η ∧ (fun k : ℕ => (Erdos970.jacobsthalFunction k:ℝ)) =O[atTop]
      (fun k : ℕ => (k:ℝ)^2/(Real.log k)^η) :=
  JacobsthalExtension687.gain SourcePubliee687.source_bound

#print axioms jacobsthal_log_saving""")
    return "\n\n".join(parts) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--formal-conjectures", type=Path, required=True)
    parser.add_argument("--mertens-source", type=Path)
    parser.add_argument("--general", action="store_true", help="also assemble the general Jacobsthal bound")
    args = parser.parse_args()
    args.output.write_text(assemble(args.formal_conjectures, args.mertens_source, args.general), encoding="utf-8")
