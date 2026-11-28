import Comptage687
import Mathlib.Tactic

/-! Uniform reciprocal-square tail over prime moduli for the finite
bounded-differences estimate. -/
namespace QueueCarree687
open scoped BigOperators

noncomputable def band (a b : ℕ) : ℝ := ∑ p ∈ b.primesLE \ a.primesLE, (1:ℝ)/(p:ℝ)^2

private theorem first {w : ℕ} (hw : 2 ≤ w) : band w (2*w) ≤ 16/((w:ℝ)*Real.log w) := by
  have wp : (0:ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have lp : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  let W := (2*w).primesLE \ w.primesLE
  have count : (W.card:ℝ) ≤ 16*w/Real.log w := calc
    _ ≤ (Nat.primeCounting (2*w):ℝ) := by
      rw [← Nat.primesLE_card_eq_primeCounting]; exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : W ⊆ _)
    _ ≤ _ := Comptage687.prime_count_eight (by omega)
    _ ≤ _ := by
      push_cast
      have h := Real.log_le_log wp (show (w:ℝ) ≤ 2*w by linarith)
      rw [show (8:ℝ)*(2*w)=16*w by ring]
      exact div_le_div_of_nonneg_left (by positivity) lp h
  have term (p : ℕ) (hp : p ∈ W) : (1:ℝ)/(p:ℝ)^2 ≤ 1/(w:ℝ)^2 := by
    obtain ⟨stored,missing⟩ := Finset.mem_sdiff.mp hp
    have prime := (Nat.mem_primesLE.mp stored).2
    have big : w ≤ p := by_contra fun no => missing (Nat.mem_primesLE.mpr ⟨(lt_of_not_ge no).le,prime⟩)
    gcongr
  calc
    _ ≤ ∑ _p ∈ W, (1:ℝ)/(w:ℝ)^2 := Finset.sum_le_sum term
    _ = (W.card:ℝ)/(w:ℝ)^2 := by simp [div_eq_mul_inv]
    _ ≤ (16*w/Real.log w)/(w:ℝ)^2 := div_le_div_of_nonneg_right count (sq_nonneg _)
    _ = _ := by field_simp

private theorem dyadic (n : ℕ) {w : ℕ} (hw : 2 ≤ w) :
    band w (2^n*w) ≤ 32/((w:ℝ)*Real.log w) := by
  induction n generalizing w with
  | zero => simp [band]; positivity
  | succ n ih =>
    have wp : (0:ℝ) < w := by exact_mod_cast (show 0 < w by omega)
    have lp : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
    have hmul : w ≤ 2*w := by omega
    have last : 2*w ≤ 2^n*(2*w) := Nat.le_mul_of_pos_left _ (pow_pos (by decide) n)
    have add : band w (2*w)+band (2*w) (2^n*(2*w)) = band w (2^n*(2*w)) := by
      have x := Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ)/(p:ℝ)^2) (Nat.primesLE_mono hmul)
      have y := Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ)/(p:ℝ)^2) (Nat.primesLE_mono last)
      have z := Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ)/(p:ℝ)^2) (Nat.primesLE_mono (hmul.trans last))
      unfold band
      linarith only [x,y,z]
    rw [pow_succ,mul_assoc,← add]
    have two := ih (w := 2*w) (by omega)
    push_cast at two
    have logle := Real.log_le_log wp (show (w:ℝ) ≤ 2*w by linarith)
    have h : 32/(2*(w:ℝ)*Real.log (2*w)) ≤ 32/(2*(w:ℝ)*Real.log w) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      gcongr
    calc
      _ ≤ 16/((w:ℝ)*Real.log w)+32/(2*(w:ℝ)*Real.log w) := add_le_add (first hw) (two.trans h)
      _ = _ := by ring

theorem upper {w : ℕ} (hw : 2 ≤ w) (z : ℕ) :
    band w z ≤ 32/((w:ℝ)*Real.log w) := by
  have up : z ≤ 2^z*w := (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_right _ (by omega))
  apply le_trans _ (dyadic z hw)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨mem,out⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr ⟨Nat.primesLE_mono up mem,out⟩
  · intro p _ _
    positivity

end QueueCarree687
#print axioms QueueCarree687.upper
