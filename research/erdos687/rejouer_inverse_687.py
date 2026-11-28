"""Assemble the inverse almost-cover result alongside the native 687 bound."""
import argparse
from pathlib import Path

from rejouer_borne_native_687 import between, file_text, namespace_body
from rejouer_rankin_687 import extract


def block(name, *pieces):
    return "\n\n".join(["namespace " + name, *pieces, "end " + name])


def assemble(fc, long_gaps):
    catalog = (fc / "FormalConjectures/ErdosProblems/687.lean").read_text(encoding="utf-8")
    crt = between(catalog, "theorem lt_primorial_of_isCoveredByResidues ", "\n/--")
    extension = file_text("Extension687.lean")
    source = extract(long_gaps, {"greedy_product_le", "sum_prime_log_div_le", "mem_auxiliaryPrimes"})
    source = source[source.index("namespace LongGapsBetweenPrimes"):]
    # In Mathlib 4.34 the product bound for nonnegative real factors has
    # its own name, distinct from the bound for ordered groups.
    source = source.replace("apply Finset.prod_le_prod\n", "apply Finset.prod_le_prod₀\n")
    parts = [
        "import Mathlib\nimport BorneNative687",
        "/-! Inverse almost-cover comparison. The primorial inequality is from "
        "the pinned formal-conjectures catalog. The elementary prime estimates "
        "are from the pinned OpenAI Improved Long Gaps Between Primes source. "
        "Both sources are under Apache-2.0. -/",
        "open scoped Asymptotics BigOperators",
        block("Erdos687", crt),
        block("Transfert687", between(file_text("Transfert687.lean"),
              "theorem le_Y_of_covered ", "theorem Y47_lower ")),
        block("Extension687", "open Transfert687 Progressions687",
              between(extension, "theorem assign_images ", "theorem extend_given_cover_left "),
              between(extension, "theorem completes_of_card ", "theorem extend_cover {"),
              between(extension, "theorem optimal_cover ", "theorem growth_from_completion ")),
        block("Bords687", "open Extension687 Transfert687 Progressions687",
              between(file_text("Bords687.lean"), "theorem finish_singletons ", "def leftResidue ")),
        block("Comptage687", between(file_text("Comptage687.lean"),
              "theorem prime_count_eight ", "private theorem twice_succ_le_pow ")),
        namespace_body("Croissance687"), source,
        block("Presque687", between(file_text("Presque687.lean"),
              "noncomputable def holes ", "theorem holes_zero_iff ")),
    ]
    parts.extend(namespace_body(name) for name in
                 ("Moments687", "Restes687", "SousPuissance687", "Separation687", "Inverse687"))
    parts += [
        between(file_text("Accroissements687.lean"), "namespace Accroissements687",
                "/-- The old optimal interval") + "\nend Accroissements687",
        namespace_body("Troncature687"),
        """open Filter in
theorem erdos687_inverse_almost_cover :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((Transfert687.survivors (Inverse687.weak H) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧
      (fun H : ℕ => (Inverse687.weak H:ℝ)) =o[atTop] (fun H : ℕ => (Inverse687.full H:ℝ)) :=
  Troncature687.inverse_of_quadratic (Troncature687.quadratic_of_saving erdos687_log_saving)

#print axioms erdos687_inverse_almost_cover""",
    ]
    return "\n\n".join(parts) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--formal-conjectures", type=Path, required=True)
    parser.add_argument("--long-gaps-source", type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(assemble(args.formal_conjectures, args.long_gaps_source),
                           encoding="utf-8", newline="\n")
