import DeuxEstimations687

/-! A logarithmic saving from qualitative sieve constants. The cutoff
exponent is chosen after the two uniform constants are given. -/
namespace GainVariable687
open Filter Transfert687
open scoped BigOperators Asymptotics
open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

noncomputable def top (d : ℝ) (x : ℕ) := (x:ℝ) / (Real.log x)^d
noncomputable def length (d : ℝ) (x : ℕ) := ⌊(top d x)^2 / (Real.log (top d x))^2⌋₊

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

theorem reciprocal_band {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE, (1:ℝ)/p) ≤
        3*d*Real.log (Real.log x) / Real.log x := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hinf.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp hinf).eventually_ge_atTop
    (20/d), eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  obtain ⟨hz,hzx,hlog,hlower⟩ := scales hd hhalf hL hx
  let S := ∑ p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE, (1:ℝ)/p
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hband := Harmonique687.band_bound hz hzx
  change Real.log (top d x) * S ≤ Real.log x - Real.log (top d x) + 10 at hband
  have hlim : 20 ≤ Real.log (Real.log x)*d := (div_le_iff₀ hd).1 hLL
  have hb : Real.log (top d x)*S ≤ d*Real.log (Real.log x)+10 := by linarith only [hband,hlog]
  change S ≤ _ / Real.log x
  apply (le_div_iff₀ (by change 4 ≤ Real.log (x:ℝ) at hL; linarith)).2
  nlinarith only [hb, mul_le_mul_of_nonneg_right hlower hs, hlim]

theorem block_scale {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) :
    (fun x => (length d x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2 / (Real.log x)^(2+2*d)) := by
  apply Asymptotics.IsBigO.of_bound 4
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hinf.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ)] with x hL hx
  obtain ⟨_,_,_,hlower⟩ := scales hd hhalf hL hx
  let L := Real.log (x:ℝ)
  have hl : 0 < L := by change 4 ≤ L at hL; linarith
  have eqpow : L^(2+2*d) = (L^d)^2 * L^2 := by
    rw [show 2+2*d = d*2+2 by ring, Real.rpow_add hl, Real.rpow_mul hl.le]
    norm_num
  have h := calc
    (length d x : ℝ) ≤ (top d x)^2 / (Real.log (top d x))^2 := Nat.floor_le (by positivity)
    _ ≤ (top d x)^2 / (L/2)^2 := by gcongr
    _ = 4 * ((x:ℝ)^2 / L^(2+2*d)) := by
      rw [eqpow]
      change ((x:ℝ)/L^d)^2/(L/2)^2 = _
      field_simp
      ring
  change ‖(length d x : ℝ)‖ ≤ 4 * ‖(x:ℝ)^2 / L^(2+2*d)‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (length d x : ℝ) by positivity),
    abs_of_nonneg (show 0 ≤ (x:ℝ)^2 / L^(2+2*d) by positivity)] using h

noncomputable def classUnit (d : ℝ) (x : ℕ) := (length d x : ℝ) / Real.log x
noncomputable def stockUnit (d : ℝ) (x : ℕ) :=
  classUnit d x * (Real.log (Real.log x) / Real.log x)

def stockBound (c d : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ a, c * stockUnit d x ≤
    ((survivors ⌊top d x⌋₊ (length d x) a).card : ℝ)

def progressionBound (K d : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ a p, p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE →
    (charge (survivors ⌊top d x⌋₊ (length d x) a) a p : ℝ) ≤ K*(classUnit d x/p)

/-- Any positive stock constant and finite positive progression constant
    suffice for some fixed logarithmic saving, if the two sieve estimates
    hold at the selected cutoff. The choice does not depend on x. -/
theorem gain_from_sieve_constants {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/2 ∧
    (stockBound c d → progressionBound K d →
     (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
       (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+2*d))) := by
  let d := min (1/2:ℝ) (c/(6*K))
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hhalf : d ≤ 1/2 := min_le_left _ _
  have hdel : 3*d*K < c := by
    have h := (le_div_iff₀ (show 0 < 6*K by positivity)).1 (min_le_right (1/2:ℝ) (c/(6*K)))
    change d*(6*K) ≤ c at h
    linarith
  refine ⟨d,hd,hhalf,?_⟩
  intro stock progression
  unfold stockBound at stock
  unfold progressionBound at progression
  apply Asymptotics.IsBigO.trans _ (block_scale hd hhalf)
  apply Asymptotics.IsBigO.of_bound 1
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [stock, progression, reciprocal_band hd hhalf, hinf.eventually_ge_atTop 4,
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
    have hh' : (∑ p ∈ band, (1:ℝ)/p) ≤ 3*d*Real.log (Real.log x)/Real.log x := hh
    have lt : (∑ p ∈ band, (charge S a p:ℝ)) < (S.card:ℝ) := calc
      _ ≤ ∑ p ∈ band, K*(classUnit d x/p) := Finset.sum_le_sum (hprog a)
      _ = (K*classUnit d x) * (∑ p ∈ band, (1:ℝ)/p) := by
        simp only [Finset.mul_sum, mul_one_div, mul_div_assoc]
      _ ≤ (K*classUnit d x) * (3*d*Real.log (Real.log x)/Real.log x) :=
        mul_le_mul_of_nonneg_left hh' (mul_nonneg hK.le hv.le)
      _ = (3*d*K)*stockUnit d x := by unfold stockUnit; ring
      _ < c * stockUnit d x := mul_lt_mul_of_pos_right hdel hw
      _ ≤ _ := hstock a
    exact_mod_cast lt
  simpa using (show (Erdos687.Y x : ℝ) ≤ (length d x : ℝ) by exact_mod_cast bound)

/-- Uniformity concerns the two constants. The threshold in x can depend
    on d in both input estimates. -/
theorem exists_log_saving
    (stock : ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d)
    (progression : ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → progressionBound K d) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) := by
  obtain ⟨c,hc,hs⟩ := stock
  obtain ⟨K,hK,hp⟩ := progression
  obtain ⟨d,hd,hh,transfer⟩ := gain_from_sieve_constants hc hK
  exact ⟨2*d,by positivity,transfer (hs d hd hh) (hp d hd hh)⟩

end GainVariable687
