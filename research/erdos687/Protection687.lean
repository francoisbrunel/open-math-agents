import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace Protection687

/-- At least one nonzero residue removes at most the integer average,
    including when the protected set contains multiples of the modulus. -/
theorem sparse_nonzero_class (T : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    ∃ r ∈ Finset.Ico 1 p, (T.filter fun n => n % p = r).card ≤ T.card / (p-1) := by
  have hd : 0 < p-1 := by omega
  have bound : T.card < (Finset.Ico 1 p).card * (T.card / (p-1) + 1) := by
    rw [Nat.card_Ico, mul_comm]
    exact (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self _)
  obtain ⟨r,hr,h⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := fun n => n % p) bound
  exact ⟨r,hr,Nat.le_of_lt_succ h⟩

/-- Choose nonzero residues across an entire band. The union bound charges
    at most the sum of the individual integer averages against the same T. -/
theorem protect_band (P T : Finset ℕ) (hp : ∀ p ∈ P, 2 ≤ p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ P, 0 < a p ∧ a p < p) ∧
      T.card ≤ (T.filter fun n => ∀ p ∈ P, n % p ≠ a p).card +
        ∑ p ∈ P, T.card / (p-1) := by
  classical
  let a (p : ℕ) := if h : p ∈ P then Classical.choose (sparse_nonzero_class T (hp p h)) else 0
  have spec (p : ℕ) (h : p ∈ P) :
      a p ∈ Finset.Ico 1 p ∧ (T.filter fun n => n % p = a p).card ≤ T.card / (p-1) := by
    simpa only [a, dif_pos h] using Classical.choose_spec (sparse_nonzero_class T (hp p h))
  refine ⟨a, fun p h => Finset.mem_Ico.mp (spec p h).1, ?_⟩
  let live := T.filter fun n => ∀ p ∈ P, n % p ≠ a p
  let hit := fun p => T.filter fun n => n % p = a p
  have incl : T ⊆ live ∪ P.biUnion hit := by
    intro n hn
    by_cases h : ∀ p ∈ P, n % p ≠ a p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,h⟩)
    · push Not at h
      obtain ⟨p,hp',eqn⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp',Finset.mem_filter.mpr ⟨hn,eqn⟩⟩)
  have hu := Finset.card_union_le live (P.biUnion hit)
  have hsum : (P.biUnion hit).card ≤ ∑ p ∈ P, T.card / (p-1) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p h => (spec p h).2)
  exact (Finset.card_le_card incl).trans (hu.trans (Nat.add_le_add_left hsum _))

/-- Integer form of the product of survival fractions (p-2)/(p-1).
    The choice of residues is deterministic, and no independence of tests
    on different points or distribution hypothesis on T is required. -/
theorem protect_band_product (P T : Finset ℕ) (hp : ∀ p ∈ P, 2 ≤ p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ P, a p ∈ Finset.Ico 1 p) ∧
      T.card * (∏ p ∈ P, (p-2)) ≤
        (T.filter fun n => ∀ p ∈ P, n % p ≠ a p).card * (∏ p ∈ P, (p-1)) := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert p P hnot ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    obtain ⟨b,hb,hstock⟩ := ih (fun q hq => hp q (Finset.mem_insert_of_mem hq))
    let S := T.filter fun n => ∀ q ∈ P, n % q ≠ b q
    obtain ⟨r,hr,hcut⟩ := sparse_nonzero_class S hp'
    let a := fun q : ℕ => if q = p then r else b q
    have keep : (T.filter fun n => ∀ q ∈ insert p P, n % q ≠ a q) =
        S.filter fun n => n % p ≠ r := by
      ext n
      simp only [Finset.mem_filter, Finset.forall_mem_insert, S]
      have hold : (∀ q ∈ P, n % q ≠ a q) ↔ ∀ q ∈ P, n % q ≠ b q := by
        constructor <;> intro h q hq <;>
          simpa [a, show q ≠ p from fun eq => hnot (eq ▸ hq)] using h q hq
      simp only [hold, a, if_pos rfl]
      tauto
    refine ⟨a, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | h
      · simpa [a] using hr
      · simpa [a, show q ≠ p from fun eq => hnot (eq ▸ h)] using hb q h
    · rw [keep, Finset.prod_insert hnot, Finset.prod_insert hnot]
      let U := S.filter fun n => n % p ≠ r
      let B := S.filter fun n => n % p = r
      have htotal : B.card + U.card = S.card := S.card_filter_add_card_filter_not _
      have hremoved : B.card * (p-1) ≤ S.card :=
        (Nat.le_div_iff_mul_le (by omega)).1 hcut
      have step : S.card * (p-2) ≤ U.card * (p-1) := by
        rw [← htotal] at hremoved ⊢
        rw [show p-1 = (p-2)+1 by omega] at hremoved ⊢
        nlinarith
      change T.card * (∏ q ∈ P, (q-2)) ≤ S.card * (∏ q ∈ P, (q-1)) at hstock
      calc
        _ = (T.card * (∏ q ∈ P, (q-2))) * (p-2) := by ac_rfl
        _ ≤ (S.card * (∏ q ∈ P, (q-1))) * (p-2) := Nat.mul_le_mul_right _ hstock
        _ = (S.card * (p-2)) * (∏ q ∈ P, (q-1)) := by ac_rfl
        _ ≤ (U.card * (p-1)) * (∏ q ∈ P, (q-1)) := Nat.mul_le_mul_right _ step
        _ = _ := by change _ = U.card * _; ac_rfl

end Protection687
