import StockFinNatif687
import CribleFinNatif687

namespace TransfertFin687
open Filter GainVariable687 Transfert687 StockFin687
open scoped Asymptotics BigOperators

private theorem scales {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) {x : ℕ}
    (hl : 4 ≤ Real.log (x:ℝ)) (hx : 0 < x) :
    2 ≤ top d x ∧ top d x ≤ x ∧
    Real.log (top d x) = Real.log x - d*Real.log (Real.log x) ∧
    Real.log (x:ℝ)/2 ≤ Real.log (top d x) := by
  let L := Real.log (x:ℝ)
  have hl' : 4 ≤ L := hl
  have hpos : 0 < L := by linarith
  have hxp : (0:ℝ) < x := by exact_mod_cast hx
  have hz : 0 < top d x := div_pos hxp (Real.rpow_pos_of_pos hpos _)
  have hlog : Real.log (top d x) = L - d*Real.log L := by
    rw [top, Real.log_div hxp.ne' (Real.rpow_pos_of_pos hpos _).ne', Real.log_rpow hpos]
  have lower : L/2 ≤ Real.log (top d x) := by
    rw [hlog]
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    linarith [mul_le_mul_of_nonneg_right hhalf hlogL, Real.log_le_sub_one_of_pos hpos]
  refine ⟨(Real.log_le_log_iff (by norm_num) hz).mp ?_,
    div_le_self hxp.le (Real.one_le_rpow (by linarith) hd.le), hlog, lower⟩
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]

private theorem sharp_band {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) (tiny : d ≤ 1/400) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE, (1:ℝ)/p) ≤
        (21/20)*d*Real.log (Real.log x) / Real.log x := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hinf.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp hinf).eventually_ge_atTop
    (400/d), eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  obtain ⟨hz,hzx,hlog,hlower⟩ := scales hd hhalf hL hx
  let S := ∑ p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE, (1:ℝ)/p
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hband := Harmonique687.band_bound hz hzx
  change Real.log (top d x) * S ≤ Real.log x - Real.log (top d x) + 10 at hband
  have hlim : 400 ≤ Real.log (Real.log x)*d := (div_le_iff₀ hd).1 hLL
  have hb : Real.log (top d x)*S ≤ d*Real.log (Real.log x)+10 := by linarith only [hband,hlog]
  change S ≤ _ / Real.log x
  apply (le_div_iff₀ (by change 4 ≤ Real.log (x:ℝ) at hL; linarith)).2
  have close : (399/400)*Real.log (x:ℝ) ≤ Real.log (top d x) := by
    rw [hlog]
    have Lp : 0 < Real.log (x:ℝ) := by change 4 ≤ Real.log (x:ℝ) at hL; linarith
    have nneg : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by change 4 ≤ Real.log (x:ℝ) at hL; linarith)
    linarith [mul_le_mul_of_nonneg_right tiny nneg,Real.log_le_sub_one_of_pos Lp]
  nlinarith only [hb,mul_le_mul_of_nonneg_right close hs,hlim]

open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

private theorem transfer {c K d : ℝ} (hK : 0 < K) (hd : 0 < d) (hhalf : d ≤ 1/2)
    (tiny : d ≤ 1/400) (hdel : (21/20)*d*K < c) (stock : stockBound c d) (progression : progressionBound K d) :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+2*d)) := by

  unfold stockBound at stock
  unfold progressionBound at progression
  apply Asymptotics.IsBigO.trans _ (block_scale hd hhalf)
  apply Asymptotics.IsBigO.of_bound 1
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [stock, progression, sharp_band hd hhalf tiny, hinf.eventually_ge_atTop 4,
    eventually_ge_atTop (1:ℕ)] with x hstock hprog hh hL hx
  obtain ⟨hz,_,_,_⟩ := scales hd hhalf hL hx
  have hl : 0 < Real.log (x:ℝ) := by change 4 ≤ Real.log (x:ℝ) at hL; linarith
  have hll := Real.log_pos (show 1 < Real.log (x:ℝ) by change 4 ≤ Real.log (x:ℝ) at hL; linarith)
  have hzlog : 0 < Real.log (top d x) := Real.log_pos (by linarith)
  have hratio : 1 ≤ (top d x)^2 / (Real.log (top d x))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hzlog)).2
    have h := Real.log_le_sub_one_of_pos (show 0 < top d x by linarith)
    simpa using pow_le_pow_left₀ hzlog.le (show Real.log (top d x) ≤ top d x by linarith) 2
  have hN : 1 ≤ length d x := (Nat.le_floor_iff (by positivity)).2 (by simpa using hratio)
  have hv : 0 < classUnit d x := div_pos (by exact_mod_cast (show 0 < length d x by omega)) hl
  have hw : 0 < stockUnit d x := mul_pos hv (div_pos hll hl)
  have bound : Erdos687.Y x ≤ length d x := by
    apply upper_of_survivor_budget (z := ⌊top d x⌋₊)
    intro a
    let band := x.primesLE \ (⌊top d x⌋₊).primesLE
    let S := survivors ⌊top d x⌋₊ (length d x) a
    change (∑ p ∈ band, charge S a p) < S.card
    have hh' : (∑ p ∈ band, (1:ℝ)/p) ≤ (21/20)*d*Real.log (Real.log x)/Real.log x := hh
    have lt : (∑ p ∈ band, (charge S a p:ℝ)) < (S.card:ℝ) := calc
      _ ≤ ∑ p ∈ band, K*(classUnit d x/p) := Finset.sum_le_sum (hprog a)
      _ = (K*classUnit d x) * (∑ p ∈ band, (1:ℝ)/p) := by
        simp only [Finset.mul_sum, mul_one_div, mul_div_assoc]
      _ ≤ (K*classUnit d x) * ((21/20)*d*Real.log (Real.log x)/Real.log x) :=
        mul_le_mul_of_nonneg_left hh' (mul_nonneg hK.le hv.le)
      _ = ((21/20)*d*K)*stockUnit d x := by unfold stockUnit; ring
      _ < c * stockUnit d x := mul_lt_mul_of_pos_right hdel hw
      _ ≤ _ := hstock a
    exact_mod_cast lt
  simpa using (show (Erdos687.Y x : ℝ) ≤ (length d x : ℝ) by exact_mod_cast bound)

theorem gain_one_two_hundred :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+1/200 : ℝ)) := by
  obtain ⟨c,eqc,_,hs⟩ := sharp_stock (sharp_bridge SourcePubliee687.sharp_bound)
  have margin : (21/20)*(1/400:ℝ)*(9/4) < c := by
    rw [eqc]
    linarith [Real.one_half_lt_eulerMascheroniConstant, Real.add_one_le_exp Real.eulerMascheroniConstant]
  have result := transfer (by norm_num : 0 < (9/4:ℝ)) (by norm_num : 0 < (1/400:ℝ))
    (by norm_num) (by norm_num) margin (hs _ (by norm_num) (by norm_num))
    (ProgressionFine687.uniform_progression (by norm_num) (by norm_num))
  convert result using 1 <;> norm_num

#print axioms gain_one_two_hundred
end TransfertFin687
