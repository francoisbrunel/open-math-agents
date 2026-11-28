import SurvieFineNatif687
import InverseNatif687
import ParametreItere687

/-! A uniform bound for the growth of the catalogue's Y, using the spare
prime budget at a cutoff of order t / log log t. -/
namespace BorneIteree687
open Filter GainVariable687 Transfert687 SurvieTotale687 ParametreItere687
open scoped Asymptotics

theorem upper :
    (fun t : ℕ => (Erdos687.Y t:ℝ)) =O[atTop]
      (fun t : ℕ => (t:ℝ)^2 / ((Real.log t)^(401/200:ℝ) * (Real.log (Real.log t))^2)) := by
  obtain ⟨κ,c,hκ,hc,stock⟩ := SurvieFine687.additional_prime_budget
  let A := max 1 (16/κ)
  have ha : 1 ≤ A := le_max_left _ _
  have enough : 16 ≤ κ*A := by
    have h := (div_le_iff₀ hκ).mp (le_max_right 1 (16/κ))
    simpa [A,mul_comm] using h
  have hlim := ParametreItere687.evolves ha
  have block := (GainVariable687.block_scale (by norm_num : 0 < (1/400:ℝ)) (by norm_num)).comp_tendsto hlim
  have comparison : (fun t : ℕ => (length (1/400) (cutoff A t):ℝ)) =O[atTop]
      (fun t : ℕ => (cutoff A t:ℝ)^2 / (Real.log (cutoff A t))^(401/200:ℝ)) := by
    convert block using 1 <;> norm_num [Function.comp_def]
  apply Asymptotics.IsBigO.trans _ (comparison.trans (scale_bound ha (by norm_num)))
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [ParametreItere687.scales ha,hlim.eventually stock,
    hlim.eventually (stockUnit_pos (by norm_num : 0 < (1/400:ℝ)) (by norm_num)),
    eventually_ge_atTop (2:ℕ)] with t hs hstock hpos ht
  let s := cutoff A t
  let L := Real.log (t:ℝ)
  let J := Real.log L
  obtain ⟨lp,jp,sp,st,lo,_,ls,ll⟩ := hs
  have tp : 0 ≤ (t:ℝ) := Nat.cast_nonneg _
  have slp : 0 < Real.log s := (half_pos lp).trans_le ls
  have logle : Real.log s ≤ L := Real.log_le_log sp (by exact_mod_cast st)
  have lo' : A*t ≤ (s:ℝ)*J := (div_le_iff₀ jp).mp lo
  have capacity : 8*(t:ℝ) ≤ κ*(s:ℝ)*Real.log (Real.log s) := by
    have h1 := mul_le_mul_of_nonneg_right enough tp
    have h2 := mul_le_mul_of_nonneg_left lo' hκ.le
    have h3 := mul_le_mul_of_nonneg_left ll (mul_nonneg hκ.le sp.le)
    change J/2 ≤ Real.log (Real.log s) at ll
    nlinarith only [h1,h2,h3]
  let E := t.primesLE \ s.primesLE
  have big : ∀ p ∈ E, s < p ∧ p.Prime := by
    intro p hp
    obtain ⟨mem,out⟩ := Finset.mem_sdiff.mp hp
    have pr := (Nat.mem_primesLE.mp mem).2
    exact ⟨lt_of_not_ge (fun h => out (Nat.mem_primesLE.mpr ⟨h,pr⟩)),pr⟩
  have small : (E.card:ℝ) ≤ κ*s*Real.log (Real.log s)/Real.log s := calc
    _ ≤ (t.primesLE.card:ℝ) := by exact_mod_cast Finset.card_le_card (show E ⊆ t.primesLE from Finset.sdiff_subset)
    _ ≤ 8*t/L := by simpa only [Nat.primesLE_card_eq_primeCounting] using Comptage687.prime_count_eight ht
    _ ≤ (8*t)/Real.log s := div_le_div_of_nonneg_left (by positivity) slp logle
    _ ≤ _ := div_le_div_of_nonneg_right capacity slp.le
  have bound : Erdos687.Y t ≤ length (1/400) s := by
    apply csSup_le
    · exact ⟨0, fun _ => 0, by simp⟩
    · intro y hy
      obtain ⟨a,cover⟩ := hy
      by_contra! tooLong
      have positive := (mul_pos hc hpos).trans_le (hstock a E big small)
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (by exact_mod_cast positive)
      obtain ⟨inside,extra⟩ := Finset.mem_filter.mp hi
      obtain ⟨interval,old⟩ := Finset.mem_filter.mp inside
      obtain ⟨l,u⟩ := Finset.mem_Icc.mp interval
      obtain ⟨p,pt,pr,hit⟩ := cover i (Finset.mem_Icc.mpr ⟨l,u.trans tooLong.le⟩)
      by_cases psmall : p ∈ s.primesLE
      · exact old p psmall hit
      · exact extra p (Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨pt,pr⟩,psmall⟩) hit
  simpa using (show (Erdos687.Y t:ℝ) ≤ length (1/400) s by exact_mod_cast bound)

end BorneIteree687
#print axioms BorneIteree687.upper
