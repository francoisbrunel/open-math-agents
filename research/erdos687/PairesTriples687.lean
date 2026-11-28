import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! A criterion for an uncovered position using all pair and triple
incidences of the remaining prime rows. Here k i is the number of rows
covering position i. All sums use integers and need no division. -/
namespace PairesTriples687

open scoped BigOperators

theorem collision_bound {α : Type*} (S : Finset α) (k : α → ℕ) :
    (∑ i ∈ S, k i * (k i - 1))^2 ≤
      (∑ i ∈ S, (k i - 1)) * ∑ i ∈ S, (k i)^2 * (k i - 1) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun _ _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _)
  intro i _
  exact le_of_eq (by ring)

/-- A full cover fixes the excess multiplicity exactly, so a strict
contradiction to the collision inequality gives a missed position. -/
theorem survivor {α : Type*} (S : Finset α) (k : α → ℕ)
    (test : ((∑ i ∈ S, k i) - S.card) * (∑ i ∈ S, (k i)^2 * (k i - 1)) <
      (∑ i ∈ S, k i * (k i - 1))^2) :
    ∃ i ∈ S, k i = 0 := by
  classical
  by_contra! covered
  have eqn (i : α) (hi : i ∈ S) : k i - 1 + 1 = k i :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (covered i hi))
  have eqsum : (∑ i ∈ S, (k i - 1)) + S.card = ∑ i ∈ S, k i := calc
    _ = ∑ i ∈ S, (k i - 1 + 1) := by simp [Finset.sum_add_distrib]
    _ = _ := Finset.sum_congr rfl eqn
  have excess : (∑ i ∈ S, (k i - 1)) = (∑ i ∈ S, k i) - S.card := by
    rw [← eqsum, Nat.add_sub_cancel]
  have cs := collision_bound S k
  rw [excess] at cs
  exact (Nat.not_le_of_gt test) cs

end PairesTriples687
#print axioms PairesTriples687.survivor
