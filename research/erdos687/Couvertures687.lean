import Std

/-! Finite certificates for Erdős 687. Lean's kernel evaluates the bounded searches. -/
namespace Couvertures687

abbrev Classes := List (Nat × Nat)

def hit (classes : Classes) (n : Nat) : Bool :=
  classes.any fun (p, r) => n % p == r

def holes (classes : Classes) (length : Nat) : List Nat :=
  ((List.range length).map (· + 1)).filter fun n => !(hit classes n)

theorem mem_holes {s : Classes} {n N : Nat} :
    n ∈ holes s N ↔ 0 < n ∧ n ≤ N ∧ hit s n = false := by
  simp only [holes, List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, h⟩
    exact ⟨by omega, by omega, by simpa using h⟩
  · rintro ⟨hn, hN, h⟩
    exact ⟨⟨n-1, by omega, by omega⟩, by simp [h]⟩

theorem hits_of_no_holes {s : Classes} {N n : Nat} (empty : holes s N = [])
    (lo : 0 < n) (hi : n ≤ N) : hit s n = true := by
  cases h : hit s n with
  | true => rfl
  | false =>
    have hm := mem_holes.mpr ⟨lo, hi, h⟩
    simp [empty] at hm

def at47 : Classes :=
  [(2,1),(3,2),(5,2),(7,4),(11,10),(13,6),(17,13),(19,9),(23,1),
   (29,7),(31,3),(37,16),(41,40),(43,5),(47,31)]

def at71 : Classes :=
  [(2,1),(3,2),(5,2),(7,3),(11,1),(13,5),(17,3),(19,8),(23,7),(29,2),
   (31,2),(37,16),(41,38),(43,28),(47,36),(53,48),(59,6),(61,58),(67,4),(71,40)]

def before73 : Classes :=
  [(2,1),(3,2),(5,1),(7,4),(11,6),(13,12),(17,14),(19,2),(23,1),(29,25),
   (31,21),(37,26),(41,1),(43,22),(47,37),(53,5),(59,30),(61,10),(67,51),(71,49)]

def at73 : Classes := (73,34) :: before73

theorem witness47 : holes at47 99 = [] := by decide
theorem witness47_small : holes (at47.take 9) 99 = [16,34,36,40,48,78,90,94,96] := by decide
theorem witness71 : holes at71 183 = [106] := by decide
theorem witness73_small : holes before73 189 = [34,180] := by decide
theorem witness73 : holes at73 189 = [] := by decide

/-- Row multiplicities in the two-choice relaxation. Repetitions count twice. -/
def twoChoices : Classes :=
  [(5,1),(5,2),(7,1),(7,4),(11,3),(11,8),(13,0),(13,7),(17,2),(17,14),
   (19,4),(19,10),(23,5),(23,5),(29,10),(29,13),(31,16),(31,17),(37,20),(37,23)]

theorem double_coverage :
    ∀ i : Fin 33, (i.val+1) % 3 ≠ 0 →
      2 ≤ (twoChoices.filter fun (p,r) => (i.val+1) % p == r).length := by decide

end Couvertures687
