import Mathlib

/-! A pair-intersection correction to the sum of the losses of individual
prime rows. The chosen parent of a row must come earlier in the order.
A parent outside the active set gives no correction. -/
namespace Recouvrements687

open scoped BigOperators

def discounted {α : Type*} [DecidableEq α] (P : Finset ℕ)
    (C : ℕ → Finset α) (parent : ℕ → ℕ) (p : ℕ) : Finset α :=
  if parent p ∈ P then C p \ C (parent p) else C p

theorem union_discounted {α : Type*} [DecidableEq α] (P : Finset ℕ)
    (C : ℕ → Finset α) (parent : ℕ → ℕ)
    (earlier : ∀ p ∈ P, parent p ∈ P → parent p < p) :
    P.biUnion C = P.biUnion (discounted P C parent) := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨p, hp, hit⟩ := Finset.mem_biUnion.mp hi
    let T := P.filter fun q => i ∈ C q
    have existsHit : T.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp,hit⟩⟩
    let q := T.min' existsHit
    have hq : q ∈ T := T.min'_mem existsHit
    obtain ⟨active, found⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_biUnion.mpr ⟨q,active,?_⟩
    by_cases prior : parent q ∈ P
    · simp only [discounted,if_pos prior,Finset.mem_sdiff]
      refine ⟨found,fun other => ?_⟩
      have hmem : parent q ∈ T := Finset.mem_filter.mpr ⟨prior,other⟩
      exact (Nat.not_le_of_gt (earlier q active prior)) (T.min'_le _ hmem)
    · simpa [discounted,prior] using found
  · intro hi
    obtain ⟨p,hp,hit⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_biUnion.mpr ⟨p,hp,?_⟩
    by_cases prior : parent p ∈ P
    · exact (Finset.mem_sdiff.mp (by simpa [discounted,prior] using hit)).1
    · simpa [discounted,prior] using hit

/-- If the corrected charges sum to less than the stock, at least one
position survives every new row. This works for every choice of classes. -/
theorem survivor {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset ℕ)
    (C : ℕ → Finset α) (parent : ℕ → ℕ)
    (earlier : ∀ p ∈ P, parent p ∈ P → parent p < p)
    (stock : (∑ p ∈ P, (discounted P C parent p).card) < S.card) :
    ∃ i ∈ S, ∀ p ∈ P, i ∉ C p := by
  classical
  by_contra! covered
  have sub : S ⊆ P.biUnion C := by
    intro i hi
    obtain ⟨p,hp,hit⟩ := covered i hi
    exact Finset.mem_biUnion.mpr ⟨p,hp,hit⟩
  have count := Finset.card_le_card sub
  rw [union_discounted P C parent earlier] at count
  exact (Nat.not_le_of_gt stock) (count.trans Finset.card_biUnion_le)

end Recouvrements687
#print axioms Recouvrements687.survivor
