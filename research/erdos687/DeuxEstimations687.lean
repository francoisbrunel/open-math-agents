import Transfert687
import Harmonique687

/-! The harmonic input of the log-saving transfer follows unconditionally
from the factorial identity. Only two uniform sieve estimates remain. -/
namespace DeuxEstimations687
open Filter Transfert687
open scoped Asymptotics BigOperators

theorem log_saving_of_two_sieves
    (stock : ∀ᶠ x : ℕ in atTop, ∀ a, stockScale x / 125 ≤
      ((survivors ⌊cutoff x⌋₊ (blockLength x) a).card : ℝ))
    (progression : ∀ᶠ x : ℕ in atTop, ∀ a p, p ∈ x.primesLE \ (⌊cutoff x⌋₊).primesLE →
      (charge (survivors ⌊cutoff x⌋₊ (blockLength x) a) a p : ℝ) ≤
        (5/2 : ℝ) * (classScale x / p)) :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ)^2 / (Real.log x) ^ (401/200 : ℝ)) := by
  apply log_saving_at_cutoff stock progression
  filter_upwards [Harmonique687.harmonic_at_cutoff, eventually_ge_atTop (2:ℕ)] with x h hx
  have hl : 0 < Real.log (x:ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < x by omega))
  have hv : 0 ≤ classScale x := div_nonneg (by positivity) hl.le
  calc
    _ = classScale x * (∑ p ∈ x.primesLE \ (⌊cutoff x⌋₊).primesLE, (1:ℝ)/p) := by
      simp only [Finset.mul_sum, mul_one_div]
    _ ≤ classScale x * ((3/1000:ℝ) * Real.log (Real.log x) / Real.log x) :=
      mul_le_mul_of_nonneg_left h hv
    _ = _ := by unfold stockScale classScale; ring

end DeuxEstimations687
