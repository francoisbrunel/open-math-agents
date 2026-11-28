import TransfertFinNatif687
import OAI.NumberTheory.Jacobsthal.Sieve.ClosedEulerIndividualUpper

/-! Keep the asymptotic Mertens product when normalizing the published
survivor bound. Its Euler constant cancels that in the reference margin. -/
namespace BorneProduit687
open Filter GainVariable687 Transfert687 StockFin687 StockSource687
open OAI.Erdos970 OAI.Erdos970.NumberTheoryLean
open scoped Asymptotics BigOperators

private theorem normalized :
    ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
      (99/8080:ℝ)*((height z:ℝ)*Real.log (Real.log z)/(Real.log z)^2) ≤
        ((survivors ⌊z⌋₊ (height z) a).card:ℝ) := by
  obtain ⟨c,eqc,_,source⟩ := StockFin687.sharp_bridge SourcePubliee687.sharp_bound
  have wt : Tendsto width atTop atTop := ErdosSourceReferenceMargin.rootW_tendsto
  have norm := (tendsto_order.mp ReferenceMertens.normalization_tendsto_one).2 (101/100:ℝ) (by norm_num)
  filter_upwards [source,StockFin687.width_eventually,wt.eventually norm,
    wt.eventually_ge_atTop 2,Real.tendsto_log_atTop.eventually_ge_atTop 2] with z raw widthbound mertens wbig Lbig
  intro a
  let w := width z
  let Q := OMA_M3.Qm ⌊w⌋₊
  let E := Real.exp Real.eulerMascheroniConstant
  have ep : 0<E := Real.exp_pos _
  change 2 ≤ w at wbig
  have wp : 0<w := by linarith
  have lw : 0<Real.log w := Real.log_pos (by linarith)
  have Lp : 0<Real.log z := by linarith
  have same : SmallSieveFinite.smallEuler ⌊w⌋₊ = Q := by
    simp only [Q,OMA_M3.Qm,SmallSieveFinite.smallEuler,LargePrimeDeletion.cutoffPrimes,one_div]
  have qp : 0<Q := by
    rw [← same]
    exact (inv_pos.mpr wp).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w (by linarith))
  have mt : Real.exp (-Real.eulerMascheroniConstant)/(Real.log w*Q) ≤ 101/100 := by
    rw [← same]
    simpa only [ReferenceMertens.normalization,← ErdosInverseEuler.smallEuler_eq_primeProduct] using mertens.le
  have scaled := mul_le_mul_of_nonneg_left ((div_le_iff₀ (mul_pos lw qp)).mp mt) ep.le
  have cancel : E*Real.exp (-Real.eulerMascheroniConstant)=1 := by
    dsimp only [E]; rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [cancel] at scaled
  have wlower : (99/100:ℝ)*Real.log (Real.log z) ≤ Real.log w := widthbound.2
  have gain : (99/8080:ℝ)*Real.log (Real.log z) ≤ (E/80)*Q*(Real.log w)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right scaled lw.le,wlower]
  obtain ⟨b,shift⟩ := StockFin687.shift_survivors (height z) ⌊z⌋₊ a
  have h := raw b
  rw [eqc] at h
  calc
    _ = ((99/8080:ℝ)*Real.log (Real.log z))*((height z:ℝ)/(Real.log z)^2) := by ring
    _ ≤ ((E/80)*Q*(Real.log w)^2)*((height z:ℝ)/(Real.log z)^2) :=
      mul_le_mul_of_nonneg_right gain (by positivity)
    _ = (E/80)*((height z:ℝ)*Q/(scale z)^2) := by
      change _ = (E/80)*((height z:ℝ)*Q/(Real.log z/Real.log w)^2)
      field_simp [lw.ne',Lp.ne'] <;> ring
    _ ≤ _ := h.trans (by exact_mod_cast shift)

private theorem stock {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) : stockBound (9801/808000) d := by
  have hcut := StockFin687.cutoff_properties hd hh
  have hinf := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  have ht : Tendsto (top d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hcut,hinf.eventually_ge_atTop (2*b),hinf.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)]
      with x cmp hx big xp
    have tp : 0<top d x := div_pos (by exact_mod_cast xp) (Real.rpow_pos_of_pos (by linarith : 0<Real.log (x:ℝ)) _)
    change 2*b ≤ Real.log x at hx
    linarith [cmp.2.2.1,Real.log_le_sub_one_of_pos tp]
  unfold stockBound
  filter_upwards [ht.eventually normalized,hcut,hinf.eventually_ge_atTop 2] with x raw cmp big
  intro a
  let L := Real.log x
  let t := Real.log (top d x)
  have Lp : 0<L := by change 2≤L at big; linarith
  have LL : 0≤Real.log L := Real.log_nonneg (by change 2≤L at big; linarith)
  have tp : 0<t := cmp.1
  have tL : t≤L := cmp.2.1
  have logt : (99/100)*Real.log L ≤ Real.log t := cmp.2.2.2
  have lt0 : 0 ≤ Real.log t := by linarith
  have h := raw a
  change (99/8080:ℝ)*((length d x:ℝ)*Real.log t/t^2) ≤ _ at h
  calc
    _ = (99/8080:ℝ)*((length d x:ℝ)*((99/100)*Real.log L)/L^2) := by
      dsimp [stockUnit,classUnit,L]; ring
    _ ≤ _ := le_trans (by gcongr) h

/-- The complete interval of gains supplied by the constants used here. -/
theorem upper_with_margin {d : ℝ} (hd : 0 < d) (small : d ≤ 1/100)
    (margin : (21/20)*d*(9/4) < 9801/808000) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+2*d)) :=
  TransfertFin687.transfer (by norm_num) hd (by linarith) small margin
    (stock hd (by linarith)) (ProgressionFine687.uniform_progression hd (by linarith))

/-- This exponent applies to all sufficiently large integer cutoffs. -/
theorem upper : (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
    (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+1/98:ℝ)) := by
  have up := upper_with_margin (by norm_num : 0 < (1/196:ℝ)) (by norm_num) (by norm_num)
  convert up using 1 <;> norm_num

end BorneProduit687
#print axioms BorneProduit687.upper
