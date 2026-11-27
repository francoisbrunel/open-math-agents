import Troncature687

/-! Strict cutoffs and the two different interval endpoints in
    Erdős's 1980 formulation. -/
namespace Convention687
open Filter Inverse687 Transfert687
open scoped Asymptotics

def coversBelow (cut length : ℕ) : Prop := ∃ a : ℕ → ℕ, ∀ n : ℕ, 1 ≤ n → n < length →
  ∃ p < cut, p.Prime ∧ n ≡ a p [MOD p]

theorem least_strict {H x : ℕ} : coversBelow (x+1) (H+1) ↔ full H ≤ x := by
  rw [full_le_iff]
  constructor
  · rintro ⟨a,h⟩
    apply le_Y_of_covered
    refine ⟨a,fun n hn => ?_⟩
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
    obtain ⟨p,px,pr,hit⟩ := h n lo (Nat.lt_succ_of_le up)
    exact ⟨p,Nat.lt_succ_iff.mp px,pr,hit⟩
  · intro le
    obtain ⟨a,h⟩ := Extension687.optimal_cover x
    refine ⟨a,fun n lo up => ?_⟩
    obtain ⟨p,px,pr,hit⟩ := h n (Finset.mem_Icc.mpr ⟨lo,(Nat.lt_succ_iff.mp up).trans le⟩)
    exact ⟨p,Nat.lt_succ_of_le px,pr,hit⟩

theorem extra_endpoint (x H : ℕ) (a : ℕ → ℕ) :
    (survivors x (H+1) a).card ≤ (survivors x H a).card+1 := by
  have sub : survivors x (H+1) a ⊆ insert (H+1) (survivors x H a) := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
    by_cases eq : n=H+1
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,by omega⟩,avoid⟩))
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le ..)

theorem strict_comparison (quad : (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^2)) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((survivors (weak H) (H+1) (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => ((H+1:ℕ):ℝ)/Real.log (H+1:ℕ)) ∧
      (fun H : ℕ => ((weak H+1:ℕ):ℝ)) =o[atTop] (fun H : ℕ => ((full H+1:ℕ):ℝ)) := by
  obtain ⟨a,near,ratio⟩ := Troncature687.inverse_of_quadratic quad
  have ninf : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have succ : Tendsto (fun H : ℕ => ((H+1:ℕ):ℝ)) atTop atTop :=
    ninf.comp (tendsto_atTop.2 (fun k => (eventually_ge_atTop k).mono (fun i hi => by omega)))
  have massInf : Tendsto (fun H : ℕ => ((H+1:ℕ):ℝ)/Real.log (H+1:ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    let C := max 1 c
    have hp : 0<C := lt_of_lt_of_le zero_lt_one (le_max_left ..)
    filter_upwards [succ.eventually (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr hp)),
      eventually_ge_atTop (2:ℕ)] with H bound big
    have l := Real.log_pos (show (1:ℝ)<(H+1:ℕ) by exact_mod_cast (show 1<H+1 by omega))
    change ‖Real.log (H+1:ℕ)‖ ≤ C⁻¹*‖((H+1:ℕ):ℝ)‖ at bound
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg l.le,abs_of_nonneg (Nat.cast_nonneg _)] at bound
    apply (le_max_right 1 c).trans ((le_div_iff₀ l).mpr ?_)
    calc C*Real.log (H+1:ℕ) ≤ C*(C⁻¹*((H+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_left bound hp.le
         _ = _ := by field_simp
  have unit := (Asymptotics.isLittleO_const_id_atTop (1:ℝ)).comp_tendsto massInf
  have adjust : (fun H : ℕ => (H:ℝ)/Real.log H) =O[atTop]
      (fun H : ℕ => ((H+1:ℕ):ℝ)/Real.log (H+1:ℕ)) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (2:ℕ)] with H big
    have hp : (0:ℝ)<H := by positivity
    have l := Real.log_pos (show (1:ℝ)<H by exact_mod_cast big)
    have up := Real.log_le_log (by positivity : (0:ℝ)<(H+1:ℕ)) (show ((H+1:ℕ):ℝ) ≤ (H:ℝ)^2 by
      push_cast; nlinarith [show (2:ℝ) ≤ H by exact_mod_cast big])
    rw [Real.log_pow] at up
    have lj := Real.log_pos (show (1:ℝ)<(H+1:ℕ) by exact_mod_cast (show 1<H+1 by omega))
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hp.le l.le),
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) lj.le),← mul_div_assoc]
    apply (div_le_div_iff₀ l lj).mpr
    push_cast at up ⊢
    nlinarith [mul_le_mul_of_nonneg_left up hp.le]
  have oneFull : (fun _ : ℕ => (1:ℝ)) =o[atTop] (fun H => (full H:ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop 1).comp_tendsto (ninf.comp full_inf)
  refine ⟨a,?_,?_⟩
  · refine (Asymptotics.IsBigO.of_norm_eventuallyLE (g := fun H : ℕ =>
      ((survivors (weak H) H (a H)).card:ℝ)+1) (Eventually.of_forall ?_)).trans_isLittleO
        ((near.trans_isBigO adjust).add unit)
    intro H
    change ‖((survivors (weak H) (H+1) (a H)).card:ℝ)‖ ≤ ((survivors (weak H) H (a H)).card:ℝ)+1
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast extra_endpoint (weak H) H (a H)
  · have h := (ratio.add oneFull).trans_le (k := fun H : ℕ => ((full H+1:ℕ):ℝ)) (fun H => by
      simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]; exact_mod_cast Nat.le_succ _)
    simpa only [Nat.cast_add,Nat.cast_one] using h

end Convention687
