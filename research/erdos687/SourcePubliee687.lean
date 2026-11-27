import InterfaceSource687
import OAI.NumberTheory.Jacobsthal.Conclusions.SourceRootCompletion
import OAI.NumberTheory.Jacobsthal.Estimates.RootCutoffSurvivors

/-! Producer for the original OpenAI Lean 4.34.1 checkout. -/
namespace SourcePubliee687
open Filter OAI.Erdos970 OAI.Erdos970.NumberTheoryLean
open ErdosInverseBoxHeight

theorem source_bound : InterfaceSource687.statement := by
  obtain ⟨c,hc,stock⟩ := Erdos970Final.source_root_survivor_lower
  refine ⟨c,hc,?_⟩
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

#print axioms source_bound
end SourcePubliee687
