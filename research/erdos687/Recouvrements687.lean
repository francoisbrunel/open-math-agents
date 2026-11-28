import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

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

def primeRow (S : Finset ℕ) (a : ℕ → ℕ) (p : ℕ) :=
  S.filter fun n => n % p = a p % p

/-- Two distinct hits in the intersection would differ by a positive
multiple of both coprime moduli. -/
theorem pair_card_le_one {H p q : ℕ} (S : Finset ℕ) (a : ℕ → ℕ)
    (bounded : ∀ n ∈ S, n ≤ H) (co : p.Coprime q) (short : H < p*q) :
    (primeRow S a p ∩ primeRow S a q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨ip,iq⟩ := Finset.mem_inter.mp hi
  obtain ⟨jp,jq⟩ := Finset.mem_inter.mp hj
  have both : i ≡ j [MOD p*q] := (Nat.modEq_and_modEq_iff_modEq_mul co).mp
    ⟨(Finset.mem_filter.mp ip).2.trans (Finset.mem_filter.mp jp).2.symm,
      (Finset.mem_filter.mp iq).2.trans (Finset.mem_filter.mp jq).2.symm⟩
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt ((bounded i (Finset.mem_filter.mp ip).1).trans_lt short),
    Nat.mod_eq_of_lt ((bounded j (Finset.mem_filter.mp jp).1).trans_lt short)] using both

/-- In a short interval the entire one-parent correction can save
at most the number of active primes, regardless of the residues. -/
theorem correction_cap {H : ℕ} (S P : Finset ℕ) (a parent : ℕ → ℕ)
    (bounded : ∀ n ∈ S, n ≤ H) (prime : ∀ p ∈ P, p.Prime)
    (earlier : ∀ p ∈ P, parent p ∈ P → parent p < p)
    (short : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → H < p*q) :
    (∑ p ∈ P, (primeRow S a p).card) ≤
      (∑ p ∈ P, (discounted P (primeRow S a) parent p).card) + P.card := by
  classical
  have row (p : ℕ) (hp : p ∈ P) : (primeRow S a p).card ≤
      (discounted P (primeRow S a) parent p).card + 1 := by
    by_cases h : parent p ∈ P
    · have ne := (earlier p hp h).ne'
      have small := pair_card_le_one S a bounded ((Nat.coprime_primes (prime p hp)
        (prime (parent p) h)).mpr ne) (short p hp _ h ne)
      have parts := Finset.card_sdiff_add_card_inter (primeRow S a p) (primeRow S a (parent p))
      simp only [discounted,if_pos h]
      omega
    · simp [discounted,h]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
    using Finset.sum_le_sum row

end Recouvrements687
#print axioms Recouvrements687.survivor
#print axioms Recouvrements687.correction_cap
