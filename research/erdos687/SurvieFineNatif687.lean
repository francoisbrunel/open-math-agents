import TransfertFinNatif687

/-! Uniform survivor density at the 401/200 length scale after adding a
reserve of arbitrary primes having cardinality comparable to
x log log x / log x. -/
namespace SurvieFine687
open Filter GainVariable687 Transfert687 SurvieTotale687 StockFin687
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

private theorem sharp_band {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) (tiny : d ≤ 1/100) :
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
  have close : (99/100)*Real.log (x:ℝ) ≤ Real.log (top d x) := by
    rw [hlog]
    have Lp : 0 < Real.log (x:ℝ) := by change 4 ≤ Real.log (x:ℝ) at hL; linarith
    have nneg : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by change 4 ≤ Real.log (x:ℝ) at hL; linarith)
    linarith [mul_le_mul_of_nonneg_right tiny nneg,Real.log_le_sub_one_of_pos Lp]
  nlinarith only [hb,mul_le_mul_of_nonneg_right close hs,hlim]
private theorem band_remaining {z x N : ℕ} (h : z ≤ x) (a : ℕ → ℕ) :
    remaining (survivors z N a) (x.primesLE \ z.primesLE) a = survivors x N a := by
  classical
  ext i
  simp only [remaining,survivors,Finset.mem_filter,Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hi,old⟩,newer⟩
    refine ⟨hi,?_⟩
    intro p hp
    by_cases hm : p ∈ z.primesLE
    · exact old p hm
    · exact newer p ⟨hp,hm⟩
  · rintro ⟨hi,avoid⟩
    refine ⟨⟨hi,fun p hp => avoid p ?_⟩,fun p hp => avoid p hp.1⟩
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans h,prime⟩

theorem additional_prime_budget :
    ∃ κ c' : ℝ, 0 < κ ∧ 0 < c' ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (a : ℕ → ℕ) (E : Finset ℕ), (∀ p ∈ E, x < p ∧ p.Prime) →
        (E.card:ℝ) ≤ κ*(x:ℝ)*Real.log (Real.log x)/Real.log x →
        c'*stockUnit (1/400) x ≤
          ((remaining (survivors x (length (1/400) x) a) E a).card:ℝ) := by
  classical
  obtain ⟨c,eqc,hc,hs⟩ := sharp_stock (sharp_bridge SourcePubliee687.sharp_bound)
  let d := (1/400:ℝ)
  let m := c-(21/20)*d*(9/4)
  have hd : 0 < d := by dsimp [d]; norm_num
  have hh : d ≤ 1/2 := by dsimp [d]; norm_num
  have hm : 0 < m := by
    dsimp [m,d]; rw [eqc]
    linarith [Real.one_half_lt_eulerMascheroniConstant, Real.add_one_le_exp Real.eulerMascheroniConstant]
  refine ⟨m/70,m/2,by positivity,by positivity,?_⟩
  have tends : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs d hd hh,ProgressionFine687.uniform_progression hd hh,
    CribleTransfert687.progression_at_reference hd hh,sharp_band hd hh (by dsimp [d]; norm_num),
    tends.eventually_ge_atTop 4,eventually_ge_atTop (1:ℕ)] with x hstock hband hlarge hmass hL hx
  intro a E hE size
  let L := Real.log (x:ℝ)
  let V := classUnit d x
  let W := stockUnit d x
  let z := ⌊top d x⌋₊
  let N := length d x
  let S := survivors z N a
  let T := survivors x N a
  let P := x.primesLE \ z.primesLE
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have Lp : 0 < L := by change 4 ≤ L at hL; linarith
  have LLp : 0 ≤ Real.log L := Real.log_nonneg (by change 4 ≤ L at hL; linarith)
  have Vn : 0 ≤ V := div_nonneg (Nat.cast_nonneg _) Lp.le
  have Wn : 0 ≤ W := mul_nonneg Vn (div_nonneg LLp Lp.le)
  have top_le : top d x ≤ (x:ℝ) := div_le_self xp.le (Real.one_le_rpow (by change 4 ≤ L at hL; linarith) hd.le)
  have zle : z ≤ x := Nat.floor_le_of_le top_le
  have incl : T ⊆ S := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hi,fun p hp => avoid p ?_⟩
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans zle,prime⟩
  have loss1 : (∑ p ∈ P, (charge S a p:ℝ)) ≤ ((21/20)*d*(9/4))*W := calc
    _ ≤ ∑ p ∈ P, (9/4)*(V/p) := Finset.sum_le_sum (hband a)
    _ = ((9/4)*V)*(∑ p ∈ P, (1:ℝ)/p) := by simp only [Finset.mul_sum,mul_one_div,mul_div_assoc]
    _ ≤ ((9/4)*V)*((21/20)*d*Real.log L/L) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by dsimp [W,stockUnit,V,L]; ring
  have loss2 : (∑ p ∈ E, (charge T a p:ℝ)) ≤ (m/2)*W := calc
    _ ≤ ∑ _p ∈ E, 35*(V/x) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨gt,prime⟩ := hE p hp
      have mono : charge T a p ≤ charge S a p :=
        Finset.card_le_card (Finset.filter_subset_filter _ incl)
      exact (show (charge T a p:ℝ) ≤ charge S a p by exact_mod_cast mono).trans
        (hlarge a x p le_rfl top_le gt.le prime (zle.trans_lt gt))
    _ = (E.card:ℝ)*(35*(V/x)) := by simp
    _ ≤ (m/70*(x:ℝ)*Real.log L/L)*(35*(V/x)) := mul_le_mul_of_nonneg_right size (by positivity)
    _ = _ := by change _ = m/2*(V*(Real.log L/L)); field_simp; ring
  have f1 := finite_loss S P a
  change S.card ≤ (remaining (survivors z N a) (x.primesLE \ z.primesLE) a).card + _ at f1
  rw [band_remaining zle] at f1
  have b1 : (S.card:ℝ) ≤ T.card + ∑ p ∈ P, (charge S a p:ℝ) := by exact_mod_cast f1
  have b2 : (T.card:ℝ) ≤ (remaining T E a).card + ∑ p ∈ E, (charge T a p:ℝ) := by
    exact_mod_cast finite_loss T E a
  have start : c*W ≤ (S.card:ℝ) := hstock a
  change (m/2)*W ≤ ((remaining T E a).card:ℝ)
  dsimp [m] at *
  linarith

end SurvieFine687
#print axioms SurvieFine687.additional_prime_budget
