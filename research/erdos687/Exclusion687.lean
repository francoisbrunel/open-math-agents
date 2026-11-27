import Std

/-! Soundness of exhaustive residue search with an additive-capacity cutoff.
  The domain can already be parity-compressed. Distinct moduli are unnecessary
  for the rejection implication. -/
namespace Exclusion687

def hit (p r n : Nat) : Bool := n % p == r
def keep (s : List Nat) (p r : Nat) : List Nat := s.filter fun n => !(hit p r n)

def capacity (s : List Nat) (p : Nat) : Nat :=
  ((List.range p).map fun r => (s.filter (hit p r)).length).foldr max 0

theorem le_max_fold {v : Nat} {l : List Nat} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

theorem selected_le_capacity (s : List Nat) {r p : Nat} (h : r < p) :
    (s.filter (hit p r)).length ≤ capacity s p :=
  le_max_fold (List.mem_map.mpr ⟨r,List.mem_range.mpr h,rfl⟩)

theorem split_length (s : List Nat) (p r : Nat) :
    s.length = (keep s p r).length + (s.filter (hit p r)).length := by
  induction s with
  | nil => rfl
  | cons n s ih =>
    cases e : hit p r n <;> simp [keep, e] at ih ⊢ <;> omega

def left (a : Nat → Nat) : List Nat → List Nat → List Nat
  | [], s => s
  | p :: ps, s => left a ps (keep s p (a p % p))

theorem lost_le (a : Nat → Nat) (ps : List Nat) (start big : List Nat)
    (sub : start.Sublist big) (pos : ∀ p ∈ ps, 0 < p) :
    start.length ≤ (left a ps start).length + (ps.map (capacity big)).sum := by
  induction ps generalizing start with
  | nil => simp [left]
  | cons p ps ih =>
    let r := a p % p
    have hcap := selected_le_capacity big (Nat.mod_lt (a p) (pos p (by simp)))
    have hloss := (sub.filter (hit p r)).length_le
    have hnext := ih (keep start p r) (List.filter_sublist.trans sub)
      (fun q hq => pos q (by simp [hq]))
    have hlen := split_length start p r
    change start.length ≤ (left a ps (keep start p r)).length +
      (capacity big p + (ps.map (capacity big)).sum)
    change (big.filter (hit p r)).length ≤ capacity big p at hcap
    omega

def search (k : Nat) : List Nat → List Nat → Bool
  | [], s => decide (s.length ≤ k)
  | p :: ps, s =>
    if k + ((p::ps).map (capacity s)).sum < s.length then false
    else (List.range p).any fun r => search k ps (keep s p r)

theorem accepts_valid (k : Nat) (a : Nat → Nat) (ps s : List Nat)
    (pos : ∀ p ∈ ps, 0 < p) (good : (left a ps s).length ≤ k) : search k ps s = true := by
  induction ps generalizing s with
  | nil => simpa [search, left] using good
  | cons p ps ih =>
    have bound := lost_le a (p::ps) s s (.refl _) pos
    have cut : ¬ k + ((p::ps).map (capacity s)).sum < s.length := by omega
    simp only [search, if_neg cut, List.any_eq_true]
    exact ⟨a p % p, List.mem_range.mpr (Nat.mod_lt _ (pos p (by simp))),
      ih _ (fun q hq => pos q (by simp [hq])) good⟩

theorem rejects_all {k : Nat} {ps s : List Nat} (pos : ∀ p ∈ ps, 0 < p)
    (no : search k ps s = false) (a : Nat → Nat) : k < (left a ps s).length := by
  apply Nat.lt_of_not_ge
  intro h
  have yes := accepts_valid k a ps s pos h
  simp [no] at yes

theorem mem_left (a : Nat → Nat) (ps s : List Nat) (n : Nat) :
    n ∈ left a ps s ↔ n ∈ s ∧ ∀ p ∈ ps, n % p ≠ a p % p := by
  induction ps generalizing s with
  | nil => simp [left]
  | cons p ps ih =>
    simp [left, ih, keep, hit, and_assoc]

theorem left_sublist (a : Nat → Nat) (ps s : List Nat) : (left a ps s).Sublist s := by
  induction ps generalizing s with
  | nil => exact .refl _
  | cons p ps ih => exact (ih _).trans List.filter_sublist

theorem small_rejection (a : Nat → Nat) :
    0 < (left a [2,3,5,7] ((List.range 10).map (·+1))).length :=
  rejects_all (by decide) (by decide) a

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem eight_holes_impossible_23 (a : Nat → Nat) :
    8 < (left a [3,5,7,11,13,17,19,23] (List.range 48)).length :=
  rejects_all (by decide) (by decide) a

section
set_option maxRecDepth 10000
private def phase37 (r t : Nat) := keep (keep (List.range 33) 3 r) 5 t
private def tail37 := [7,11,13,17,19,23,29,31,37]

-- Separate kernel reductions bound memory use when replaying the search.
set_option maxHeartbeats 8000000 in
private theorem leaf00 : search 0 tail37 (phase37 0 0) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf01 : search 0 tail37 (phase37 0 1) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf02 : search 0 tail37 (phase37 0 2) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf03 : search 0 tail37 (phase37 0 3) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf04 : search 0 tail37 (phase37 0 4) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf10 : search 0 tail37 (phase37 1 0) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf11 : search 0 tail37 (phase37 1 1) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf12 : search 0 tail37 (phase37 1 2) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf13 : search 0 tail37 (phase37 1 3) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf14 : search 0 tail37 (phase37 1 4) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf20 : search 0 tail37 (phase37 2 0) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf21 : search 0 tail37 (phase37 2 1) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf22 : search 0 tail37 (phase37 2 2) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf23 : search 0 tail37 (phase37 2 3) = false := by decide
set_option maxHeartbeats 8000000 in
private theorem leaf24 : search 0 tail37 (phase37 2 4) = false := by decide

theorem impossible_37 (a : Nat → Nat) :
    0 < (left a [3,5,7,11,13,17,19,23,29,31,37] (List.range 33)).length := by
  change 0 < (left a tail37 (phase37 (a 3 % 3) (a 5 % 5))).length
  apply rejects_all (by decide)
  have h3 : a 3 % 3 = 0 ∨ a 3 % 3 = 1 ∨ a 3 % 3 = 2 := by omega
  have h5 : a 5 % 5 = 0 ∨ a 5 % 5 = 1 ∨ a 5 % 5 = 2 ∨ a 5 % 5 = 3 ∨ a 5 % 5 = 4 := by omega
  rcases h3 with h | h | h <;> rcases h5 with g | g | g | g | g <;> rw [h,g]
  · exact leaf00
  · exact leaf01
  · exact leaf02
  · exact leaf03
  · exact leaf04
  · exact leaf10
  · exact leaf11
  · exact leaf12
  · exact leaf13
  · exact leaf14
  · exact leaf20
  · exact leaf21
  · exact leaf22
  · exact leaf23
  · exact leaf24

end

end Exclusion687
