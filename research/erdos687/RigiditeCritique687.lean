import DispersionBande687
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Joint necessary conditions at the quadratic exponent. The interval
linear sieve supplies the asymptotic envelopes in the accompanying note. -/
namespace RigiditeCritique687
open Filter EcartsMultiples687 DispersionBande687 Set
open scoped Topology BigOperators Interval

/-- Every duplicate hit consumes exactly one unit of the slack between
the upper envelopes of the rows and the lower envelope of the stock. -/
theorem balance (S P : Finset ℕ) (a : ℕ → ℕ) (L : ℝ) (U : ℕ → ℝ)
    (cover : ∀ n ∈ S, ∃ p ∈ P, n%p=a p%p) :
    ((S.card:ℝ)-L)+(∑ p ∈ P, (U p-(occupancy S p (a p%p):ℝ)))+
      (∑ n ∈ S, ((multiplicity P a n-1:ℕ):ℝ)) = (∑ p ∈ P, U p)-L := by
  have h (n : ℕ) (hn : n ∈ S) : 1 ≤ multiplicity P a n := by
    obtain ⟨p,hp,e⟩ := cover n hn
    exact Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,e⟩⟩
  have eq : (∑ n ∈ S, (multiplicity P a n-1))+S.card = ∑ p ∈ P, occupancy S p (a p%p) := calc
    _ = ∑ n ∈ S, (multiplicity P a n-1+1) := by simp [Finset.sum_add_distrib]
    _ = ∑ n ∈ S, multiplicity P a n := Finset.sum_congr rfl (fun n hn => Nat.sub_add_cancel (h n hn))
    _ = _ := by simp only [DispersionBande687.multiplicity,occupancy,Finset.card_filter]; exact Finset.sum_comm
  have re : (∑ n ∈ S, ((multiplicity P a n-1:ℕ):ℝ))+S.card =
      ∑ p ∈ P, (occupancy S p (a p%p):ℝ) := by exact_mod_cast eq
  rw [Finset.sum_sub_distrib]
  linarith

theorem saturation {stock rows repeats lo hi : ℕ → ℝ} {A : ℝ}
    (low : Tendsto lo atTop (𝓝 A)) (high : Tendsto hi atTop (𝓝 A))
    (bounds : ∀ᶠ i in atTop, lo i ≤ stock i ∧ stock i+repeats i=rows i ∧
      0 ≤ repeats i ∧ rows i ≤ hi i) :
    Tendsto stock atTop (𝓝 A) ∧ Tendsto repeats atTop (𝓝 0) ∧
      Tendsto (fun i => hi i-rows i) atTop (𝓝 0) := by
  have st : Tendsto stock atTop (𝓝 A) := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    low high (bounds.mono (fun _ h => h.1))
    (bounds.mono (fun _ h => by linarith [h.2.1,h.2.2.1,h.2.2.2]))
  have ro : Tendsto rows atTop (𝓝 A) := tendsto_of_tendsto_of_tendsto_of_le_of_le' st high
    (bounds.mono (fun _ h => by linarith [h.2.1,h.2.2.1])) (bounds.mono (fun _ h => h.2.2.2))
  refine ⟨st,?_,by simpa using high.sub ro⟩
  apply (show Tendsto (fun i => rows i-stock i) atTop (𝓝 0) by simpa using ro.sub st).congr'
  exact bounds.mono (fun _ h => by linarith [h.2.1])

/-- Integral of the upper linear sieve charges, less the lower linear
sieve stock, in units H/log z. At r=s/2 the expression vanishes. -/
theorem sieve_gap {s r : ℝ} (one : 1 ≤ r) (sr : r < s) :
    (∫ t in (1:ℝ)..r, 2/(t*(s-t))) - (2/s)*Real.log (s-1) =
      (2/s)*Real.log (r/(s-r)) := by
  have sp : 0 < s := by linarith
  have rp : 0 < r := by linarith
  let F := fun t : ℝ => (2/s)*(Real.log t-Real.log (s-t))
  have deriv (t : ℝ) (ht : t ∈ uIcc 1 r) :
      HasDerivAt F (2/(t*(s-t))) t := by
    rw [uIcc_of_le one] at ht
    have tp : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have dt : 0 < s-t := sub_pos.mpr (ht.2.trans_lt sr)
    have h := ((Real.hasDerivAt_log tp.ne').sub
      (((hasDerivAt_const t s).sub (hasDerivAt_id t)).log dt.ne')).const_mul (2/s)
    convert h using 1 <;> try rfl
    all_goals try dsimp [F]
    all_goals field_simp [tp.ne',dt.ne',sp.ne'] <;> ring
  have cont : ContinuousOn (fun t : ℝ => 2/(t*(s-t))) (uIcc 1 r) := by
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    intro t ht
    rw [uIcc_of_le one] at ht
    exact mul_ne_zero (lt_of_lt_of_le zero_lt_one ht.1).ne' (sub_pos.mpr (ht.2.trans_lt sr)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt deriv cont.intervalIntegrable]
  dsimp [F]
  rw [Real.log_one,Real.log_div rp.ne' (sub_pos.mpr sr).ne']
  ring

end RigiditeCritique687
#print axioms RigiditeCritique687.balance
#print axioms RigiditeCritique687.saturation
#print axioms RigiditeCritique687.sieve_gap
