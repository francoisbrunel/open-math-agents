import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Invert the cutoff enlargement afforded by the spare prime budget. -/
namespace ParametreItere687
open Filter
open scoped Asymptotics

noncomputable def cutoff (A : ℝ) (t : ℕ) : ℕ :=
  ⌈A * t / Real.log (Real.log t)⌉₊

theorem scales {A : ℝ} (ha : 1 ≤ A) :
    ∀ᶠ t : ℕ in atTop, let s := cutoff A t
      let L := Real.log (t:ℝ)
      let J := Real.log L
      0 < L ∧ 0 < J ∧ 0 < (s:ℝ) ∧ s ≤ t ∧
      A*t/J ≤ s ∧ (s:ℝ) ≤ 2*A*t/J ∧ L/2 ≤ Real.log s ∧ J/2 ≤ Real.log (Real.log s) := by
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [logs.eventually_ge_atTop 4,(Real.tendsto_log_atTop.comp logs).eventually_ge_atTop (max A 4),
    eventually_ge_atTop (2:ℕ)] with t hL hJ ht
  let s := cutoff A t
  let L := Real.log (t:ℝ)
  let J := Real.log L
  change 4 ≤ L at hL
  change max A 4 ≤ J at hJ
  have Aj := (le_max_left _ _).trans hJ
  have j4 := (le_max_right _ _).trans hJ
  have jp : 0 < J := by linarith
  have lp : 0 < L := by linarith
  have tp : 0 < (t:ℝ) := by exact_mod_cast (show 0 < t by omega)
  have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have jl : J ≤ L/2 := by
    have h := Real.log_le_sub_one_of_pos (half_pos lp)
    rw [Real.log_div lp.ne' (by norm_num)] at h
    change Real.log L ≤ L/2
    linarith
  have lt' : L ≤ (t:ℝ) := by linarith [Real.log_le_sub_one_of_pos tp]
  have at' : (t:ℝ) ≤ A*t := by simpa using mul_le_mul_of_nonneg_right ha tp.le
  have one : 1 ≤ A*t/J := (le_div_iff₀ jp).mpr (by linarith)
  have lo : A*t/J ≤ (s:ℝ) := Nat.le_ceil _
  have sp : 0 < (s:ℝ) := by linarith
  have up : (s:ℝ) ≤ 2*A*t/J := by
    have h : (s:ℝ) < A*t/J+1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ A*t/J)
    linarith [show 2*A*t/J=2*(A*t/J) by ring]
  have st : s ≤ t := Nat.ceil_le.mpr ((div_le_iff₀ jp).mpr (by
    simpa [mul_comm] using mul_le_mul_of_nonneg_right Aj tp.le))
  have cmp : (t:ℝ)/J ≤ s := (div_le_div_of_nonneg_right at' jp.le).trans lo
  have ls := Real.log_le_log (div_pos tp jp) cmp
  rw [Real.log_div tp.ne' jp.ne'] at ls
  have logS : L/2 ≤ Real.log s := by
    change L - Real.log J ≤ Real.log s at ls
    linarith [Real.log_le_sub_one_of_pos jp]
  have ll := Real.log_le_log (half_pos lp) logS
  rw [Real.log_div lp.ne' (by norm_num)] at ll
  exact ⟨lp,jp,sp,st,lo,up,logS,by change J-Real.log 2 ≤ _ at ll; linarith⟩

theorem evolves {A : ℝ} (ha : 1 ≤ A) : Tendsto (cutoff A) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [scales ha, logs.eventually_ge_atTop (2*(b:ℝ))] with t hs hb
  obtain ⟨_,_,sp,_,_,_,ls,_⟩ := hs
  change 2*(b:ℝ) ≤ Real.log t at hb
  exact_mod_cast (show (b:ℝ) ≤ cutoff A t by linarith [Real.log_le_sub_one_of_pos sp])

theorem scale_bound {A e : ℝ} (ha : 1 ≤ A) (he : 0 ≤ e) :
    (fun t : ℕ => (cutoff A t:ℝ)^2 / (Real.log (cutoff A t))^e) =O[atTop]
      (fun t : ℕ => (t:ℝ)^2 / ((Real.log t)^e * (Real.log (Real.log t))^2)) := by
  apply Asymptotics.IsBigO.of_bound ((2*A)^2 * (2:ℝ)^e)
  filter_upwards [scales ha] with t hs
  obtain ⟨lp,jp,sp,_,_,up,ls,_⟩ := hs
  have pos := (half_pos lp).trans_le ls
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2*A*t/Real.log (Real.log t))^2 / (Real.log t/2)^e := by gcongr
    _ = _ := by
      rw [Real.div_rpow lp.le (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
      <;> ring

end ParametreItere687
