import Distribution687

/-! Exact factorial moments for a row, conditional on its surviving
indices after the small moduli have been chosen. -/
namespace Dilution687
open Finset Distribution687
open scoped BigOperators

theorem factorial (S P : Finset ℕ) (pos : ∀ q ∈ P, 0<q)
    (inject : ∀ q ∈ P, Set.InjOn (fun n : ℕ => n%q) (S : Set ℕ)) (k : ℕ) :
    (∑ a : Assignment P, (misses P S a).card.choose k) =
      S.card.choose k * ∏ q ∈ P, (q-k) := by
  classical
  rw [factorial_moment]
  calc
    _ = ∑ _T ∈ S.powersetCard k, ∏ q ∈ P, (q-k) := by
      apply sum_congr rfl
      intro T hT
      obtain ⟨sub,size⟩ := mem_powersetCard.mp hT
      apply prod_congr rfl
      intro q hq
      rw [allowed_card T (pos q hq),card_image_of_injOn ((inject q hq).mono sub),size]
    _ = _ := by simp [card_powersetCard]

theorem upper_tail (S P : Finset ℕ) (M : ℕ) (sub : S ⊆ range M)
    (large : ∀ q ∈ P, M<q) (k : ℕ) :
    (univ.filter (fun a : Assignment P => k ≤ (misses P S a).card)).card ≤
      S.card.choose k * ∏ q ∈ P, (q-k) := by
  classical
  have eq := factorial S P (fun q hq => Nat.zero_lt_of_lt (large q hq))
    (fun q hq i hi j hj same => by
      simpa only [Nat.mod_eq_of_lt ((mem_range.mp (sub hi)).trans (large q hq)),
        Nat.mod_eq_of_lt ((mem_range.mp (sub hj)).trans (large q hq))] using same) k
  rw [← eq,card_filter]
  apply sum_le_sum
  intro a _
  split
  next yes => exact Nat.choose_pos yes
  next _ => exact Nat.zero_le _

end Dilution687
#print axioms Dilution687.factorial
#print axioms Dilution687.upper_tail
