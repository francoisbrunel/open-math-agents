import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Elementary bookkeeping for the dyadic tail step of Erdős 687.
    The classical prime-counting bound is the same estimate used by the
    earlier Left to Solve reduction R1. This module also handles the
    integer logarithm and the floor in R2's normalization. -/
namespace Comptage687
open Filter

theorem prime_count_eight {x : ℕ} (hx : 2 ≤ x) :
    (Nat.primeCounting x : ℝ) ≤ 8 * (x : ℝ) / Real.log x := by
  have h1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hp := Chebyshev.pi_le_log4_mul_div h1
  rw [Nat.floor_natCast, Real.log_sqrt (Nat.cast_nonneg x)] at hp
  have hl := Real.log_pos h1
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hterm : Real.log 4 * (x:ℝ) / (Real.log x / 2) ≤ 6 * x / Real.log x := by
    rw [div_div_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hl).2
    nlinarith [mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α := ℝ) x)]
  have hs := Real.sqrt_pos.2 (by positivity : (0:ℝ) < x)
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    linarith [Real.log_le_sub_one_of_pos hs, Real.log_sqrt (Nat.cast_nonneg x : (0:ℝ) ≤ x)]
  have hroot : Real.sqrt x ≤ 2 * x / Real.log x := by
    apply (le_div_iff₀ hl).2
    nlinarith [mul_le_mul_of_nonneg_left hlog hs.le, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) x)]
  calc
    _ ≤ _ := hp
    _ ≤ 6 * x / Real.log x + 2 * x / Real.log x := add_le_add hterm hroot
    _ = _ := by ring

private theorem twice_succ_le_pow {k : ℕ} (h : 4 ≤ k) : 2*(k+1) ≤ 2^k := by
  induction k, h using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

theorem normalized_prime_count :
    ∀ᶠ x : ℕ in atTop, x.primesLE.card ≤ 30 * (x / (x.log2+1)) := by
  filter_upwards [eventually_ge_atTop (16 : ℕ)] with x hx
  let k := x.log2
  let d := x / (k+1)
  have hzero : x ≠ 0 := by omega
  have hk : 4 ≤ k := (Nat.le_log2 hzero).2 (by simpa using hx)
  have hpow : 2^k ≤ x := Nat.log2_self_le hzero
  have hd : 2 ≤ d := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).2
    ((twice_succ_le_pow hk).trans hpow)
  have hxlt : x < (d+1)*(k+1) :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).1 (Nat.lt_succ_self d)
  have hscale : (x:ℝ) ≤ ((d:ℝ)+1)*((k:ℝ)+1) := by exact_mod_cast hxlt.le
  have hklog : (k:ℝ) * Real.log 2 ≤ Real.log x := by
    have hp : (2:ℝ)^k ≤ x := by exact_mod_cast hpow
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hp
  have hk' : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogs : (k:ℝ)+1 ≤ (5/2)*Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) k)]
  have hl : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hupper := prime_count_eight (x := x) (by omega)
  have hc : (Nat.primeCounting x:ℝ) ≤ 30*(d:ℝ) := by
    apply hupper.trans
    apply (div_le_iff₀ hl).2
    have hr := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ (d:ℝ)+1 by positivity)
    have hdL := mul_le_mul_of_nonneg_right hd' hl.le
    nlinarith
  rw [Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast hc

end Comptage687
