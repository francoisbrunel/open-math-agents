import BorneNative687

/-! An explicit logarithmic saving for Erdős 687(i). The first four proofs carry through the actual reference constant chosen in openai/math (Apache-2.0), commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, in SourceRootReference, SourceRootErrorLower and SourceRootCompletion. -/

open scoped Asymptotics BigOperators

namespace OAI.Erdos970

namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosBoundaryIntegral ErdosPositiveReference
open NumberTheoryLean.ReferenceSourceDecomposition
open Erdos970Dependency.InvariantCostBound

open Filter Set
open scoped Topology

theorem fixed_reference_bound :
    ∃ c_L z₀ : ℝ,c_L = Real.exp Real.eulerMascheroniConstant/100 ∧ 0 < c_L ∧ 1 < z₀ ∧ ∀ z : ℝ,z₀ ≤ z →
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
  let c_L : ℝ := Real.exp Real.eulerMascheroniConstant/100
  have hc : 0 < c_L := div_pos (Real.exp_pos _) (by norm_num)
  have hevent := actual_sourceReference_tendsto.eventually (Ioi_mem_nhds actual_reference_limit_positive)
  have he : ∀ᶠ z : ℝ in atTop,
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
    filter_upwards [hevent,rootB_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with z hz hB
    have hz' : c_L < (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := hz
    refine ⟨hz'.le,?_⟩
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    simpa only [mul_comm] using hz'.le
  obtain ⟨z₁,hz₁⟩ := eventually_atTop.mp he
  refine ⟨c_L,max 2 z₁,rfl,hc,by have h := le_max_left (2:ℝ) z₁; linarith,?_⟩
  intro z hz
  exact hz₁ z ((le_max_right _ _).trans hz)

end ErdosSourceReferenceMargin

namespace NumberTheoryLean.SourceRootReference
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceSourceDecomposition ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceAdmission
open LogarithmicBinPartition SourceNodeCoordinates
open ErdosCorrectionLimit ErdosSourceReferenceMargin ErdosInverseBoxHeight
open scoped Topology

theorem fixed_polynomial_margin : ∃ c_L : ℝ,c_L = Real.exp Real.eulerMascheroniConstant/100 ∧ 0 < c_L ∧ ∀ᶠ top : ℝ in atTop,
    c_L ≤ (sourceB top)^2*referencePolynomial (sourceW top) (sourcePrimeSet (sourceW top) top)
      (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).gap := by
  obtain ⟨c_L,T,eqc,hc,_hT,hMargin⟩ := fixed_reference_bound
  refine ⟨c_L,eqc,hc,?_⟩
  filter_upwards [eventually_ge_atTop T,actual_root_eventually (1/100),eventually_gt_atTop (1:ℝ)] with top htop hroot ht1
  have hh := (hMargin top htop).1
  rwa [source_reference_root_polynomial (1/100) top ht1 hroot.2.1] at hh

end NumberTheoryLean.SourceRootReference
end OAI.Erdos970

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceRootErrorLower
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open SourceRootReference SourceCompactErrorMass StoppedErrorReduction CountErrorClassification
open StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInverseBoxHeight ErdosCorrectionLimit ErdosSourceReferenceMargin
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem fixed_stopped_correction (Cmin : ℝ) :
    ∃ c Clen Cs xi₀ : ℝ,c = Real.exp Real.eulerMascheroniConstant/200 ∧ 0 < c ∧ 1 ≤ Clen ∧ 0 < Cs ∧ Cmin ≤ Cs ∧ 0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ eta : ℝ,0 < eta → eta < 1/2 → ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ →
    ∃ rho : ℝ,10 < rho ∧ ∀ Kstop : ℝ,0 < Kstop →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ a : ℕ → ℕ,
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let z := sourceRootNode (1/100) top
      let P := sourcePrimeSet w top
      let v := rootVertex z ∅ P ((Y:ℝ)*V0)
      let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
      c*((Y:ℝ)*V0/B^2)+
        (∑ ps∈stopped w stop P.card v,(countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))) ≤
        countSurvivors Y small a v := by
  obtain ⟨c_L,eqc,hc_L,hRef⟩ := fixed_polynomial_margin
  have heighth : 0 < c_L/8 := by positivity
  obtain ⟨Cbad,K,hCbad,hK,hError⟩ := stopped_error_reduction (1/100) 2 (c_L/8) (by norm_num) (by norm_num) heighth
  obtain ⟨Csmall,B₀,W,hCsmall,hB₀,hW,hError⟩ := hError K (le_refl _)
  let eps := c_L/(8*Csmall)
  let budget := c_L/(8*Cbad)
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  obtain ⟨Clen,Cs,xi₀,hClen,hCs,hCsMin,hxi₀,hxi₀1,hCompact⟩ :=
    source_compact_error_mass K eps budget (1/100) Cmin hK heps hbudget (by norm_num) (by norm_num)
  refine ⟨c_L/2,Clen,Cs,xi₀,by rw [eqc]; ring,by positivity,hClen,hCs,hCsMin,hxi₀,hxi₀1,?_⟩
  intro eta heta0 heta xi hxi hx
  obtain ⟨rho,hrho,hCompact⟩ := hCompact eta heta0 heta xi hxi hx
  refine ⟨rho,hrho,?_⟩
  intro Kstop hKstop
  filter_upwards [hCompact Kstop hKstop,source_root_eventually_data,hRef,
    rootB_tendsto.eventually_ge_atTop B₀,rootW_tendsto.eventually_ge_atTop (max W 2)]
    with top hCompact hData hRef hB hwBound
  obtain ⟨hw,htop,hCompact⟩ := hCompact
  obtain ⟨hY,_hB3,_hw,_hwt,hcomp,h199,h23,hcons,hpower⟩ := hData
  refine ⟨hw,htop,?_⟩
  intro a
  dsimp only
  let w := sourceW top
  let B := sourceB top
  let Y := sourceY top
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  let z := sourceRootNode (1/100) top
  let P := sourcePrimeSet w top
  let mu := (Y:ℝ)*V0
  let v := rootVertex z ∅ P mu
  let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
    (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hwBound
  have hV0 : 0 < V0 := (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hmu : 0 < mu := mul_pos (by exact_mod_cast hY) hV0
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (hB₀.trans hB)
  have hRoot : z.gap=Real.log (Y:ℝ)/Real.log w-(1:ℝ)/100+2 := rfl
  have hErr := hError B w top hB ((le_max_left _ _).trans hwBound) htop hcomp Y hY z hRoot
    rfl h199 h23 hcons rfl rfl hpower a eps heps.le stop
  have hBad := hCompact z a rfl h199 h23 hcons rfl rfl hRoot
  dsimp only at hErr hBad
  have hSmallPay : Csmall*eps=c_L/8 := by dsimp [eps]; field_simp [hCsmall.ne']
  have hBadPay : Cbad*budget=c_L/8 := by dsimp [budget]; field_simp [hCbad.ne']
  have hBadScaled := mul_le_mul_of_nonneg_left hBad hCbad.le
  rw [hBadPay] at hBadScaled
  rw [hSmallPay] at hErr
  let correction := ∑ ps∈stopped w stop P.card v,(countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))
  have hScaled : c_L/2+(B^2/mu)*correction ≤ (B^2/mu)*countSurvivors Y small a v := by
    dsimp only [correction,mu,v,P,small,V0,z,Y,w,B,stop] at *
    nlinarith
  have hf : 0 < B^2/mu := div_pos (sq_pos_of_pos hBpos) hmu
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    _ = c_L/2+(B^2/mu)*correction := by
      change (B^2/mu)*(c_L/2*(mu/B^2)+correction)=_
      field_simp [hmu.ne',hBpos.ne']
    _ ≤ _ := hScaled
end NumberTheoryLean.SourceRootErrorLower


end Erdos970

end OAI


namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Final
open _root_.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.SourceRootErrorLower NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.LogarithmicBinPartition
  NumberTheoryLean.LargePrimeDeletion
  ErdosInverseBoxHeight ErdosCorrectionLimit


theorem fixed_root_survivor_lower : ∃ c : ℝ,c = Real.exp Real.eulerMascheroniConstant/200 ∧ 0 < c ∧ ∀ᶠ top : ℝ in atTop,
    ∀ a : ℕ → ℕ,
    c*((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊/(sourceB top)^2) ≤
      countSurvivors (sourceY top) (cutoffPrimes ⌊sourceW top⌋₊) a
        (rootVertex (sourceRootNode (1/100) top) ∅ (sourcePrimeSet (sourceW top) top)
          ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)) := by
  obtain ⟨eta0,heta0,heta01,hCorrection⟩ := source_stopped_correction
  obtain ⟨c,Clen,Cs,xi0,eqc,hc,hClen,hCs,_hCsMin,hxi0,hxi01,hError⟩ :=
    fixed_stopped_correction 1
  have hClenPos : 0 < Clen := by linarith
  obtain ⟨K,hK,hCorrection⟩ := hCorrection Cs hCs.le
  let eta : ℝ := eta0/2
  let xi : ℝ := min (xi0/2) (1/(40*Clen))
  have heta : 0 < eta := by dsimp [eta];positivity
  have hetaU : eta ≤ eta0 := by dsimp [eta];linarith
  have hetaHalf : eta < 1/2 := by dsimp [eta];linarith
  have hxi : 0 < xi := lt_min (by positivity) (by positivity)
  have hxiU : xi ≤ xi0 := (min_le_left _ _).trans (by linarith)
  have hxi1 : xi ≤ 1 := hxiU.trans hxi01
  obtain ⟨rho,hrho,hError⟩ := hError eta heta hetaHalf xi hxi hxiU
  have hKstop : 0 < 2*K := by positivity
  have hCorrection := hCorrection Clen hClenPos.le eta heta.le hetaU xi hxi hxi1 rho (by linarith)
  refine ⟨c,eqc,hc,?_⟩
  filter_upwards [hError (2*K) hKstop,hCorrection] with top hError hCorrection
  obtain ⟨_hw,_htop,hError⟩ := hError
  obtain ⟨_hwC,_htopC,hCorrection⟩ := hCorrection
  intro a
  have hLower := hError a
  have hSign := hCorrection a
  dsimp only at hLower hSign
  linarith

end Erdos970Final


end Erdos970

end OAI


namespace InterfaceSource687
open Filter

def fixedStatement : Prop :=
  ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant/200 ∧ 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c*((height z:ℝ)*product ⌊width z⌋₊/(scale z)^2) ≤
      ((remaining (height z) ⌊z⌋₊ a).card:ℝ)

end InterfaceSource687

namespace SourcePubliee687


open Filter OAI.Erdos970 OAI.Erdos970.NumberTheoryLean
open ErdosInverseBoxHeight

theorem fixed_bound : InterfaceSource687.fixedStatement := by
  obtain ⟨c,eqc,hc,stock⟩ := Erdos970Final.fixed_root_survivor_lower
  refine ⟨c,eqc,hc,?_⟩
  filter_upwards [stock,Real.tendsto_log_atTop.eventually
    JacobsthalSourceScale.sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ)]
    with z hz hwidth hpos
  have hw : sourceW z ≤ Real.log z := hwidth.2.2
  have hcut : sourceW z ≤ z := by
    linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hpos)]
  intro a
  have h := RootCutoffSurvivors.cutoff_lower_of_root_lower (sourceY z) hcut
    (ErdosCorrectionLimit.sourceRootNode (1/100) z) hz a
  have agree (N b : ℕ) (v : ℕ → ℕ) : InterfaceSource687.remaining N b v =
      LargePrimeDeletion.cutoffSurvivors N b v := by
    classical
    ext i
    simp only [InterfaceSource687.remaining,InterfaceSource687.primes,
      LargePrimeDeletion.cutoffSurvivors,LargePrimeDeletion.cutoffPrimes,
      SievePartition.survivors,SievePartition.residueBad,Finset.mem_filter]
  simpa only [InterfaceSource687.height,InterfaceSource687.width,InterfaceSource687.scale,
    InterfaceSource687.product,InterfaceSource687.primes,sourceY,sourceB,sourceW,
    SmallSieveFinite.smallEuler,LargePrimeDeletion.cutoffPrimes,agree,one_div] using h



end SourcePubliee687

namespace StockExplicite687
open Filter GainVariable687 Transfert687 StockSource687
open OAI.Erdos970.NumberTheoryLean

def fixedStatement : Prop :=
  ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant/200 ∧ 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c * ((height z : ℝ) * OMA_M3.Qm ⌊width z⌋₊ / (scale z)^2) ≤
      ((LargePrimeDeletion.cutoffSurvivors (height z) ⌊z⌋₊ a).card : ℝ)

private theorem shift_survivors (N z : ℕ) (a : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, (LargePrimeDeletion.cutoffSurvivors N z b).card ≤ (survivors z N a).card := by
  let b (p : ℕ) := a p + p - 1
  refine ⟨b, Finset.card_le_card_of_injOn (fun i : ℕ => i+1) ?_ ?_⟩
  · intro i hi
    obtain ⟨hiN,avoid⟩ := LargePrimeDeletion.mem_cutoffSurvivors.mp hi
    change i+1 ∈ survivors z N a
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.succ_pos i,hiN⟩,?_⟩
    intro p hp he
    obtain ⟨hpz,prime⟩ := Nat.mem_primesLE.mp hp
    have pos := prime.pos
    have translate : (b p+1) ≡ a p [MOD p] := by
      have eqn : b p+1 = a p+p := by dsimp [b]; omega
      rw [eqn]
      change (a p+p)%p = a p%p
      simp
    exact avoid p prime hpz (Nat.ModEq.add_right_cancel' 1 ((show i+1 ≡ a p [MOD p] from he).trans translate.symm))
  · intro i _ j _ he
    exact Nat.add_right_cancel he

private theorem width_eventually :
    ∀ᶠ z : ℝ in atTop, 3 ≤ ⌊width z⌋₊ ∧ Real.log (Real.log z)/2 ≤ Real.log (width z) := by
  have hu : Tendsto (fun z : ℝ => Real.log (Real.log z)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have small := Real.isLittleO_log_id_atTop.bound (show 0 < (1/4:ℝ) by norm_num)
  filter_upwards [hu.eventually_ge_atTop 8, hu.eventually small,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hlarge hs ht
  let t := Real.log z
  let u := Real.log t
  change 8 ≤ u at hlarge
  change 2 ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hb : Real.log u ≤ (1/4:ℝ)*u := by
    change ‖Real.log u‖ ≤ (1/4:ℝ)*‖u‖ at hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlogu,abs_of_nonneg hu0.le] using hs
  have hw : Real.log (width z) = u - 2*Real.log u := by
    change Real.log (t/u^2) = _
    rw [Real.log_div ht0.ne' (pow_pos hu0 _).ne',Real.log_pow]
    rfl
  have wp : 0 < width z := div_pos ht0 (pow_pos hu0 _)
  have h3 : (3:ℝ) ≤ width z := by linarith [Real.log_le_sub_one_of_pos wp]
  exact ⟨(Nat.le_floor_iff wp.le).2 (by simpa using h3),by change u/2 ≤ _; linarith⟩

theorem fixed_normalize (h : fixedStatement) :
    ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant/1200 ∧ 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
      c * ((height z:ℝ) * Real.log (Real.log z) / (Real.log z)^2) ≤
        ((survivors ⌊z⌋₊ (height z) a).card:ℝ) := by
  obtain ⟨c,eqc,hc,hs⟩ := h
  refine ⟨c/6,by rw [eqc]; ring,by positivity,?_⟩
  filter_upwards [hs,width_eventually,Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hz hw ht
  intro a
  let w := width z
  have hw' : (3:ℝ) ≤ (⌊w⌋₊:ℝ) := by exact_mod_cast hw.1
  have wp : 0 ≤ w := (Nat.cast_nonneg ⌊w⌋₊).trans (Nat.floor_le (by
    change 0 ≤ Real.log z / _; exact div_nonneg (by linarith) (sq_nonneg _)))
  have floorle : (⌊w⌋₊:ℝ) ≤ w := Nat.floor_le wp
  have hlogf : 0 < Real.log (⌊w⌋₊:ℝ) := Real.log_pos (by linarith)
  have ht' : 0 < Real.log z := by linarith
  have hfw := Real.log_le_log (show (0:ℝ) < ⌊w⌋₊ by linarith) floorle
  have hlw : 0 < Real.log w := hlogf.trans_le hfw
  have euler : 1/(3*Real.log w) ≤ OMA_M3.Qm ⌊w⌋₊ :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)).trans (OMA_M3.main _ hw.1)
  obtain ⟨b,shift⟩ := shift_survivors (height z) ⌊z⌋₊ a
  have en : (0:ℝ) ≤ height z := by positivity
  have positive : 0 ≤ Real.log (Real.log z) := Real.log_nonneg (by linarith)
  have lower : (height z:ℝ) * Real.log (Real.log z) / (6 * (Real.log z)^2) ≤
        (height z:ℝ) * OMA_M3.Qm ⌊w⌋₊ / (scale z)^2 := calc
    _ ≤ (height z:ℝ) * (2*Real.log w) / (6*(Real.log z)^2) := by
      gcongr; linarith [hw.2]
    _ = (height z:ℝ) * (1/(3*Real.log w)) / (scale z)^2 := by
      change _ = _ / (Real.log z / Real.log w)^2
      field_simp
      ring
    _ ≤ _ := by gcongr
  calc
    _ = c*((height z:ℝ)*Real.log (Real.log z)/(6*(Real.log z)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower hc.le
    _ ≤ _ := hz b
    _ ≤ _ := by exact_mod_cast shift

private theorem cutoff_properties {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, 0 < Real.log (top d x) ∧ Real.log (top d x) ≤ Real.log x ∧
      Real.log x/2 ≤ Real.log (top d x) ∧ Real.log (Real.log x)/2 ≤ Real.log (Real.log (top d x)) := by
  have ht : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 4,
    eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  let L := Real.log (x:ℝ)
  change 4 ≤ L at hL
  change 4 ≤ Real.log L at hLL
  have hl : 0 < L := by linarith
  have hp : 0 < (x:ℝ) := by exact_mod_cast hx
  have he : Real.log (top d x) = L-d*Real.log L := by
    rw [top,Real.log_div hp.ne' (Real.rpow_pos_of_pos hl d).ne', Real.log_rpow hl]
  have hlo : L/2 ≤ Real.log (top d x) := by
    rw [he]
    linarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ Real.log L by linarith),Real.log_le_sub_one_of_pos hl]
  have hhi : Real.log (top d x) ≤ L := by rw [he]; nlinarith [mul_nonneg hd.le (show 0 ≤ Real.log L by linarith)]
  have loglo := Real.log_le_log (show 0 < L/2 by positivity) hlo
  rw [Real.log_div hl.ne' (by norm_num)] at loglo
  exact ⟨by linarith,hhi,hlo,by change Real.log L/2 ≤ _; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]⟩

theorem fixed_stock (h : fixedStatement) :
    ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant/2400 ∧ 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d := by
  obtain ⟨c,eqc,hc,hs⟩ := fixed_normalize h
  refine ⟨c/2,by rw [eqc]; ring,by positivity,?_⟩
  intro d hd hh
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcut := cutoff_properties hd hh
  have htop : Tendsto (top d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hcut,hinf.eventually_ge_atTop (2*b),eventually_ge_atTop (1:ℕ),
      hinf.eventually_ge_atTop 2] with x h hL hx hpos
    have hp : 0 < top d x := div_pos (by exact_mod_cast hx) (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (x:ℝ)) _)
    change 2*b ≤ Real.log (x:ℝ) at hL
    linarith [h.2.2.1, Real.log_le_sub_one_of_pos hp]
  unfold stockBound
  filter_upwards [htop.eventually hs,hcut,hinf.eventually_ge_atTop 2] with x h hcmp hL
  intro a
  let L := Real.log (x:ℝ)
  let t := Real.log (top d x)
  let N := length d x
  have hl : 0 < L := by change 2 ≤ L at hL; linarith
  have hll : 0 ≤ Real.log L := Real.log_nonneg (by change 2 ≤ L at hL; linarith)
  have ht : 0 < t := hcmp.1
  have htl : t ≤ L := hcmp.2.1
  have hllt : Real.log L/2 ≤ Real.log t := hcmp.2.2.2
  have hlogt : 0 ≤ Real.log t := by linarith
  have hstock := h a
  change c*((N:ℝ)*Real.log t/t^2) ≤ _ at hstock
  calc
    _ = c*((N:ℝ)*(Real.log L/2)/L^2) := by unfold stockUnit classUnit; dsimp [N,L]; ring
    _ ≤ c*((N:ℝ)*Real.log t/t^2) := by gcongr
    _ ≤ _ := hstock

theorem fixed_bridge (h : InterfaceSource687.fixedStatement) : fixedStatement := by
  have agree (N z : ℕ) (a : ℕ → ℕ) : InterfaceSource687.remaining N z a =
      LargePrimeDeletion.cutoffSurvivors N z a := by
    classical
    ext i
    simp only [InterfaceSource687.remaining,InterfaceSource687.primes,
      LargePrimeDeletion.cutoffSurvivors,LargePrimeDeletion.cutoffPrimes,
      SievePartition.survivors,SievePartition.residueBad,Finset.mem_filter]
  simpa only [fixedStatement,height,width,scale,OMA_M3.Qm,
    InterfaceSource687.fixedStatement,InterfaceSource687.height,InterfaceSource687.width,
    InterfaceSource687.scale,InterfaceSource687.product,InterfaceSource687.primes,agree] using h

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

open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

private theorem transfer {c K d : ℝ} (hK : 0 < K) (hd : 0 < d) (hhalf : d ≤ 1/2)
    (hdel : 3*d*K < c) (stock : stockBound c d) (progression : progressionBound K d) :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+2*d)) := by

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

theorem explicit_gain :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+1/100000 : ℝ)) := by
  obtain ⟨c,eqc,_,hs⟩ := fixed_stock (fixed_bridge SourcePubliee687.fixed_bound)
  have margin : 3*(1/200000:ℝ)*35 < c := by
    rw [eqc]
    linarith [Real.one_half_lt_eulerMascheroniConstant, Real.add_one_le_exp Real.eulerMascheroniConstant]
  have result := transfer (by norm_num : 0 < (35:ℝ)) (by norm_num : 0 < (1/200000:ℝ))
    (by norm_num) margin (hs _ (by norm_num) (by norm_num))
    (CribleTransfert687.uniform_progression_35 (by norm_num) (by norm_num))
  convert result using 1 <;> norm_num

#print axioms explicit_gain
end StockExplicite687
