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

theorem sharp_reference_bound :
    ∃ c_L z₀ : ℝ,c_L = Real.exp Real.eulerMascheroniConstant/40 ∧ 0 < c_L ∧ 1 < z₀ ∧ ∀ z : ℝ,z₀ ≤ z →
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
  let c_L : ℝ := Real.exp Real.eulerMascheroniConstant/40
  have hc : 0 < c_L := div_pos (Real.exp_pos _) (by norm_num)
  have margin : Real.exp Real.eulerMascheroniConstant/40 <
      Real.exp Real.eulerMascheroniConstant*(-(1:ℝ)/100+2*ErdosBoundaryIntegral.signedCoefficientI/Erdos970Dependency.InvariantCostBound.costMass) := by
    have pos := Erdos970Dependency.InvariantCostBound.costMass_pos
    have ratio : (7:ℝ)/200 < 2*ErdosBoundaryIntegral.signedCoefficientI/Erdos970Dependency.InvariantCostBound.costMass := by
      apply (lt_div_iff₀ pos).2
      linarith [ErdosPositiveReference.actual_I_gt_eleven_seventyfive,ErdosPositiveReference.costMass_lt_eight]
    nlinarith [mul_pos (Real.exp_pos Real.eulerMascheroniConstant) (sub_pos.mpr ratio)]
  have hevent := actual_sourceReference_tendsto.eventually (Ioi_mem_nhds margin)
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

theorem sharp_polynomial_margin : ∃ c_L : ℝ,c_L = Real.exp Real.eulerMascheroniConstant/40 ∧ 0 < c_L ∧ ∀ᶠ top : ℝ in atTop,
    c_L ≤ (sourceB top)^2*referencePolynomial (sourceW top) (sourcePrimeSet (sourceW top) top)
      (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).gap := by
  obtain ⟨c_L,T,eqc,hc,_hT,hMargin⟩ := sharp_reference_bound
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

theorem retained_stopped_correction (r : ℝ) (rp : 0 < r) (ru : r < 1) (Cmin : ℝ) :
    ∃ c Clen Cs xi₀ : ℝ,c = r*(Real.exp Real.eulerMascheroniConstant/40) ∧ 0 < c ∧ 1 ≤ Clen ∧ 0 < Cs ∧ Cmin ≤ Cs ∧ 0 < xi₀ ∧ xi₀ ≤ 1 ∧
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
  obtain ⟨c_L,eqc,hc_L,hRef⟩ := sharp_polynomial_margin
  let loss := c_L*(1-r)/4
  have heighth : 0 < loss := div_pos (mul_pos hc_L (sub_pos.mpr ru)) (by norm_num)
  obtain ⟨Cbad,K,hCbad,hK,hError⟩ := stopped_error_reduction (1/100) 2 (loss) (by norm_num) (by norm_num) heighth
  obtain ⟨Csmall,B₀,W,hCsmall,hB₀,hW,hError⟩ := hError K (le_refl _)
  let eps := loss/Csmall
  let budget := loss/Cbad
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  obtain ⟨Clen,Cs,xi₀,hClen,hCs,hCsMin,hxi₀,hxi₀1,hCompact⟩ :=
    source_compact_error_mass K eps budget (1/100) Cmin hK heps hbudget (by norm_num) (by norm_num)
  refine ⟨(r*c_L),Clen,Cs,xi₀,by rw [eqc],by positivity,hClen,hCs,hCsMin,hxi₀,hxi₀1,?_⟩
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
  have hSmallPay : Csmall*eps=loss := by dsimp [eps]; field_simp [hCsmall.ne']
  have hBadPay : Cbad*budget=loss := by dsimp [budget]; field_simp [hCbad.ne']
  have hBadScaled := mul_le_mul_of_nonneg_left hBad hCbad.le
  rw [hBadPay] at hBadScaled
  rw [hSmallPay] at hErr
  let correction := ∑ ps∈stopped w stop P.card v,(countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))
  have hScaled : (r*c_L)+(B^2/mu)*correction ≤ (B^2/mu)*countSurvivors Y small a v := by
    dsimp only [correction,mu,v,P,small,V0,z,Y,w,B,stop,loss] at *
    nlinarith
  have hf : 0 < B^2/mu := div_pos (sq_pos_of_pos hBpos) hmu
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    _ = (r*c_L)+(B^2/mu)*correction := by
      change (B^2/mu)*((r*c_L)*(mu/B^2)+correction)=_
      field_simp [hmu.ne',hBpos.ne']
    _ ≤ _ := hScaled

theorem sharp_stopped_correction (Cmin : ℝ) :
    ∃ c Clen Cs xi₀ : ℝ,c = Real.exp Real.eulerMascheroniConstant/80 ∧ 0 < c ∧ 1 ≤ Clen ∧ 0 < Cs ∧ Cmin ≤ Cs ∧ 0 < xi₀ ∧ xi₀ ≤ 1 ∧
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
  obtain ⟨c,L,S,y,e,rest⟩ := retained_stopped_correction (1/2) (by norm_num) (by norm_num) Cmin
  exact ⟨c,L,S,y,by rw [e]; ring,rest⟩


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


theorem retained_root_survivor_lower (r : ℝ) (rp : 0 < r) (ru : r < 1) : ∃ c : ℝ,c = r*(Real.exp Real.eulerMascheroniConstant/40) ∧ 0 < c ∧ ∀ᶠ top : ℝ in atTop,
    ∀ a : ℕ → ℕ,
    c*((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊/(sourceB top)^2) ≤
      countSurvivors (sourceY top) (cutoffPrimes ⌊sourceW top⌋₊) a
        (rootVertex (sourceRootNode (1/100) top) ∅ (sourcePrimeSet (sourceW top) top)
          ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)) := by
  obtain ⟨eta0,heta0,heta01,hCorrection⟩ := source_stopped_correction
  obtain ⟨c,Clen,Cs,xi0,eqc,hc,hClen,hCs,_hCsMin,hxi0,hxi01,hError⟩ :=
    retained_stopped_correction r rp ru 1
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

theorem sharp_root_survivor_lower : ∃ c : ℝ,c = Real.exp Real.eulerMascheroniConstant/80 ∧ 0 < c ∧ ∀ᶠ top : ℝ in atTop,
    ∀ a : ℕ → ℕ,
    c*((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊/(sourceB top)^2) ≤
      countSurvivors (sourceY top) (cutoffPrimes ⌊sourceW top⌋₊) a
        (rootVertex (sourceRootNode (1/100) top) ∅ (sourcePrimeSet (sourceW top) top)
          ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)) := by
  obtain ⟨c,e,rest⟩ := retained_root_survivor_lower (1/2) (by norm_num) (by norm_num)
  exact ⟨c,by rw [e]; ring,rest⟩



end Erdos970Final


end Erdos970

end OAI


namespace InterfaceSource687
open Filter

def sharpStatement : Prop :=
  ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant/80 ∧ 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c*((height z:ℝ)*product ⌊width z⌋₊/(scale z)^2) ≤
      ((remaining (height z) ⌊z⌋₊ a).card:ℝ)

end InterfaceSource687

namespace SourcePubliee687


open Filter OAI.Erdos970 OAI.Erdos970.NumberTheoryLean
open ErdosInverseBoxHeight

theorem retained_cutoff (r : ℝ) (rp : 0 < r) (ru : r < 1) :
    ∀ᶠ z : ℝ in atTop, ∀ b : ℕ → ℕ,
      (r*(Real.exp Real.eulerMascheroniConstant/40))*
        ((StockSource687.height z:ℝ)*OMA_M3.Qm ⌊StockSource687.width z⌋₊/(StockSource687.scale z)^2)
        ≤ ((LargePrimeDeletion.cutoffSurvivors (StockSource687.height z) ⌊z⌋₊ b).card:ℝ) := by
  obtain ⟨c,eqc,hc,stock⟩ := Erdos970Final.retained_root_survivor_lower r rp ru
  filter_upwards [stock,Real.tendsto_log_atTop.eventually
    JacobsthalSourceScale.sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ)] with z root width pos
  have hw : sourceW z ≤ Real.log z := width.2.2
  have cut : sourceW z ≤ z := by linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans pos)]
  intro b
  have h := RootCutoffSurvivors.cutoff_lower_of_root_lower (sourceY z) cut
    (ErdosCorrectionLimit.sourceRootNode (1/100) z) root b
  rw [eqc] at h
  simpa only [StockSource687.height,StockSource687.width,StockSource687.scale,OMA_M3.Qm,
    sourceY,sourceB,sourceW,SmallSieveFinite.smallEuler,LargePrimeDeletion.cutoffPrimes,one_div] using h

theorem sharp_bound : InterfaceSource687.sharpStatement := by
  obtain ⟨c,eqc,hc,stock⟩ := Erdos970Final.sharp_root_survivor_lower
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

namespace StockFin687
open Filter GainVariable687 Transfert687 StockSource687
open OAI.Erdos970.NumberTheoryLean

def sharpStatement : Prop :=
  ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant/80 ∧ 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c * ((height z : ℝ) * OMA_M3.Qm ⌊width z⌋₊ / (scale z)^2) ≤
      ((LargePrimeDeletion.cutoffSurvivors (height z) ⌊z⌋₊ a).card : ℝ)

theorem shift_survivors (N z : ℕ) (a : ℕ → ℕ) :
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

theorem width_eventually :
    ∀ᶠ z : ℝ in atTop, 3 ≤ ⌊width z⌋₊ ∧ 99/100*Real.log (Real.log z) ≤ Real.log (width z) := by
  have hu : Tendsto (fun z : ℝ => Real.log (Real.log z)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have small := Real.isLittleO_log_id_atTop.bound (show 0 < (1/200:ℝ) by norm_num)
  filter_upwards [hu.eventually_ge_atTop 8, hu.eventually small,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hlarge hs ht
  let t := Real.log z
  let u := Real.log t
  change 8 ≤ u at hlarge
  change 2 ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hb : Real.log u ≤ (1/200:ℝ)*u := by
    change ‖Real.log u‖ ≤ (1/200:ℝ)*‖u‖ at hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlogu,abs_of_nonneg hu0.le] using hs
  have hw : Real.log (width z) = u - 2*Real.log u := by
    change Real.log (t/u^2) = _
    rw [Real.log_div ht0.ne' (pow_pos hu0 _).ne',Real.log_pow]
    rfl
  have wp : 0 < width z := div_pos ht0 (pow_pos hu0 _)
  have h3 : (3:ℝ) ≤ width z := by linarith [Real.log_le_sub_one_of_pos wp]
  exact ⟨(Nat.le_floor_iff wp.le).2 (by simpa using h3),by change 99/100*u ≤ _; linarith⟩

theorem sharp_normalize (h : sharpStatement) :
    ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant*33/8000 ∧ 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
      c * ((height z:ℝ) * Real.log (Real.log z) / (Real.log z)^2) ≤
        ((survivors ⌊z⌋₊ (height z) a).card:ℝ) := by
  obtain ⟨c,eqc,hc,hs⟩ := h
  refine ⟨c*(33/100),by rw [eqc]; ring,by positivity,?_⟩
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
  have lower : (height z:ℝ) * Real.log (Real.log z) / ((100/33:ℝ) * (Real.log z)^2) ≤
        (height z:ℝ) * OMA_M3.Qm ⌊w⌋₊ / (scale z)^2 := calc
    _ ≤ (height z:ℝ) * ((100/99)*Real.log w) / ((100/33:ℝ)*(Real.log z)^2) := by
      gcongr; linarith [hw.2]
    _ = (height z:ℝ) * (1/(3*Real.log w)) / (scale z)^2 := by
      change _ = _ / (Real.log z / Real.log w)^2
      field_simp
      ring
    _ ≤ _ := by gcongr
  calc
    _ = c*((height z:ℝ)*Real.log (Real.log z)/((100/33:ℝ)*(Real.log z)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower hc.le
    _ ≤ _ := hz b
    _ ≤ _ := by exact_mod_cast shift

theorem cutoff_properties {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, 0 < Real.log (top d x) ∧ Real.log (top d x) ≤ Real.log x ∧
      Real.log x/2 ≤ Real.log (top d x) ∧ (99/100)*Real.log (Real.log x) ≤ Real.log (Real.log (top d x)) := by
  have ht : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 100,
    eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  let L := Real.log (x:ℝ)
  change 4 ≤ L at hL
  change 100 ≤ Real.log L at hLL
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
  exact ⟨by linarith,hhi,hlo,by change (99/100)*Real.log L ≤ _; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]⟩

theorem sharp_stock (h : sharpStatement) :
    ∃ c : ℝ, c = Real.exp Real.eulerMascheroniConstant*3267/800000 ∧ 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d := by
  obtain ⟨c,eqc,hc,hs⟩ := sharp_normalize h
  refine ⟨c*(99/100),by rw [eqc]; ring,by positivity,?_⟩
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
  have hllt : (99/100)*Real.log L ≤ Real.log t := hcmp.2.2.2
  have hlogt : 0 ≤ Real.log t := by linarith
  have hstock := h a
  change c*((N:ℝ)*Real.log t/t^2) ≤ _ at hstock
  calc
    _ = c*((N:ℝ)*((99/100)*Real.log L)/L^2) := by unfold stockUnit classUnit; dsimp [N,L]; ring
    _ ≤ c*((N:ℝ)*Real.log t/t^2) := by gcongr
    _ ≤ _ := hstock

theorem sharp_bridge (h : InterfaceSource687.sharpStatement) : sharpStatement := by
  have agree (N z : ℕ) (a : ℕ → ℕ) : InterfaceSource687.remaining N z a =
      LargePrimeDeletion.cutoffSurvivors N z a := by
    classical
    ext i
    simp only [InterfaceSource687.remaining,InterfaceSource687.primes,
      LargePrimeDeletion.cutoffSurvivors,LargePrimeDeletion.cutoffPrimes,
      SievePartition.survivors,SievePartition.residueBad,Finset.mem_filter]
  simpa only [sharpStatement,height,width,scale,OMA_M3.Qm,
    InterfaceSource687.sharpStatement,InterfaceSource687.height,InterfaceSource687.width,
    InterfaceSource687.scale,InterfaceSource687.product,InterfaceSource687.primes,agree] using h


end StockFin687
#print axioms StockFin687.sharp_stock
#print axioms SourcePubliee687.retained_cutoff
