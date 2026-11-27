import Troncature687

/-! Prime increments of the complete covering maximum. -/
namespace Sauts687
open Filter

noncomputable def jump (p : ℕ) : ℕ := Erdos687.Y p - Erdos687.Y (p-1)

theorem unchanged {n : ℕ} (np : ¬(n+1).Prime) : Erdos687.Y (n+1) = Erdos687.Y n := by
  apply le_antisymm _ (Inverse687.Y_mono (Nat.le_succ n))
  obtain ⟨a,ha⟩ := Extension687.optimal_cover (n+1)
  apply Transfert687.le_Y_of_covered
  refine ⟨a,fun m hm => ?_⟩
  obtain ⟨p,le,pr,hit⟩ := ha m hm
  have neq : p ≠ n+1 := fun e => np (e ▸ pr)
  exact ⟨p,by omega,pr,hit⟩

theorem prefix_sum (x : ℕ) : Erdos687.Y 0 + ∑ p ∈ x.primesLE, jump p = Erdos687.Y x := by
  induction x with
  | zero => simp [Nat.primesLE_zero]
  | succ x ih =>
    rw [Nat.primesLE_succ]
    by_cases pr : (x+1).Prime
    · rw [if_pos pr,Finset.sum_insert (Nat.notMem_primesLE x)]
      have mono := Inverse687.Y_mono (Nat.le_succ x)
      simp only [Nat.succ_eq_add_one,jump,Nat.add_sub_cancel] at *
      omega
    · rw [if_neg pr,unchanged pr,ih]

theorem band_sum {z x : ℕ} (zx : z ≤ x) :
    Erdos687.Y z + ∑ p ∈ x.primesLE \ z.primesLE, jump p = Erdos687.Y x := by
  have h := Finset.sum_sdiff (f := jump) (Nat.primesLE_mono zx)
  have hx := prefix_sum x
  have hz := prefix_sum z
  omega

theorem band_constraint {z x : ℕ} (zx : z ≤ x) {B : ℝ} (nn : 0 ≤ B)
    (every : ∀ p, z < p → p ≤ x → p.Prime → (jump p:ℝ) ≤ B) :
    (Erdos687.Y x:ℝ) ≤ Erdos687.Y z + (x.primeCounting:ℝ)*B := by
  let P := x.primesLE \ z.primesLE
  have sum : (∑ p ∈ P, (jump p:ℝ)) ≤ ∑ _p ∈ P, B := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨inside,outside⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨px,pr⟩ := Nat.mem_primesLE.mp inside
    exact every p (lt_of_not_ge fun le => outside (Nat.mem_primesLE.mpr ⟨le,pr⟩)) px pr
  have count : P.card ≤ x.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card Finset.sdiff_subset
  have lifted : (Erdos687.Y x:ℝ) = Erdos687.Y z + ∑ p ∈ P, (jump p:ℝ) := by
    exact_mod_cast (band_sum zx).symm
  calc
    _ ≤ Erdos687.Y z + ∑ _p ∈ P, B := lifted.trans_le (add_le_add le_rfl sum)
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast count) nn)

theorem large_jump {x z : ℕ} (size : 2 ≤ x) (zx : z ≤ x) {B : ℝ} (nn : 0 ≤ B)
    (excess : (Erdos687.Y z:ℝ) + 8*x/Real.log x*B < Erdos687.Y x) :
    ∃ p, z < p ∧ p ≤ x ∧ p.Prime ∧ B < jump p := by
  by_contra! bad
  have total := band_constraint zx nn bad
  exact (not_lt_of_ge (total.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (Comptage687.prime_count_eight size) nn)))) excess

/-- For any fixed multiplier, every sufficiently large x contains a jump
    exceeding that multiplier times log x above every z with Y(z) <= x. -/
theorem interval_superlog (C : ℝ) (nn : 0 ≤ C) :
    ∀ᶠ x : ℕ in atTop, ∀ z ≤ x, Erdos687.Y z ≤ x →
      ∃ p, z < p ∧ p ≤ x ∧ p.Prime ∧ C*Real.log x < jump p := by
  filter_upwards [Croissance687.superlinear.eventually_gt_atTop (1+8*C),
    eventually_ge_atTop (2:ℕ)] with x high hx
  intro z zx cap
  have xp : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have logp := Real.log_pos (show (1:ℝ)<x by exact_mod_cast (by omega : 1 < x))
  have hh : (1+8*C)*(x:ℝ) < Erdos687.Y x := (lt_div_iff₀ xp).mp high
  apply large_jump hx zx (mul_nonneg nn logp.le)
  have e : 8*(x:ℝ)/Real.log x*(C*Real.log x) = 8*C*x := by field_simp
  rw [e]
  linarith [show (Erdos687.Y z:ℝ) ≤ x by exact_mod_cast cap]

theorem unbounded_jumps (C : ℝ) (nn : 0 ≤ C) (z : ℕ) :
    ∃ p, z < p ∧ p.Prime ∧ C*Real.log p < jump p := by
  obtain ⟨x,h,zx,yx⟩ := ((interval_superlog C nn).and
    ((eventually_ge_atTop z).and (eventually_ge_atTop (Erdos687.Y z)))).exists
  obtain ⟨p,pz,px,pr,big⟩ := h z zx yx
  have cmp := Real.log_le_log (show (0:ℝ)<p by exact_mod_cast pr.pos)
    (show (p:ℝ)≤x by exact_mod_cast px)
  exact ⟨p,pz,pr,(mul_le_mul_of_nonneg_left cmp nn).trans_lt big⟩

/-- A jump counts exactly the lengths for which this cutoff is first needed. -/
theorem plateau {p H : ℕ} (pos : 0 < p) :
    Inverse687.full H = p ↔ Erdos687.Y (p-1) < H ∧ H ≤ Erdos687.Y p := by
  have left := Inverse687.full_le_iff (H := H) (x := p-1)
  have right := Inverse687.full_le_iff (H := H) (x := p)
  omega

/-- The known quadratic upper bound allows the search for each large jump
    to start at the cube root, at every sufficiently large endpoint. -/
theorem cube_intervals (poly : Troncature687.Cubic) (C : ℝ) (nn : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∃ p, k < p ∧ p ≤ k^3 ∧ p.Prime ∧ C*Real.log p < jump p := by
  have grows : Tendsto (fun k : ℕ => k^3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with k hk
    have pos : 1 ≤ k := (le_max_left ..).trans hk
    exact ((le_max_right ..).trans hk).trans (by nlinarith [Nat.mul_le_mul pos pos] : k ≤ k^3)
  filter_upwards [poly,grows.eventually (interval_superlog C nn),eventually_ge_atTop (1:ℕ)]
    with k cap every pos
  have le : k ≤ k^3 := by simpa using Nat.pow_le_pow_right (by omega : 0<k) (by norm_num : 1≤3)
  obtain ⟨p,pk,px,pr,big⟩ := every k le cap
  have cmp := Real.log_le_log (show (0:ℝ)<p by exact_mod_cast pr.pos)
    (show (p:ℝ) ≤ (k^3:ℕ) by exact_mod_cast px)
  exact ⟨p,pk,px,pr,(mul_le_mul_of_nonneg_left cmp nn).trans_lt big⟩

end Sauts687
