import Std

/-! A certificate for a full modular cover. Only divisors greater than one
    are required. The catalog bridge takes a prime divisor of each witness. -/
namespace TemoinIntervalle687

def entry (words : Array Nat) (bits n : Nat) : Nat :=
  (words[n/64]?.getD 0 >>> (bits*(n%64))) % (2^bits)

def trial (x a : Nat) (w : Nat → Nat) (n : Nat) : Bool :=
  decide (2 ≤ w n ∧ w n ≤ x ∧ n % w n = a % w n)

def valid (x a : Nat) (w : Nat → Nat) (start len : Nat) : Bool :=
  (List.range' start len).all (trial x a w)

theorem at_position {x a start len n : Nat} {w : Nat → Nat}
    (h : valid x a w start len = true) (lo : start ≤ n) (hi : n < start+len) :
    2 ≤ w n ∧ w n ≤ x ∧ n % w n = a % w n :=
  of_decide_eq_true (List.all_eq_true.mp h n (List.mem_range'_1.mpr ⟨lo,hi⟩))

def Window (x H : Nat) : Prop := ∃ a : Nat, ∀ n, 1 ≤ n → n ≤ H →
  ∃ d, 2 ≤ d ∧ d ≤ x ∧ n % d = a % d

def Slice (x a lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n < hi → ∃ d, 2 ≤ d ∧ d ≤ x ∧ n % d = a % d

def wordEntry (word bits start n : Nat) := (word >>> (bits*(n-start))) % 2^bits

theorem slice {x a start len word bits : Nat}
    (ok : valid x a (wordEntry word bits start) start len=true) :
    Slice x a start (start+len) := fun n low high =>
      ⟨wordEntry word bits start n,at_position ok low high⟩

theorem appendSlice {x a lo mid hi : Nat}
    (left : Slice x a lo mid) (right : Slice x a mid hi) : Slice x a lo hi := by
  intro n low high
  by_cases h : n<mid
  · exact left n low h
  · exact right n (by omega) high

theorem window_of_slice {x a H : Nat} (all : Slice x a 1 (H+1)) :
    Window x H := ⟨a,fun n low high => all n low (by omega)⟩

theorem assemble {x H a : Nat} {w : Nat → Nat}
    (cert : ∀ j : Fin (H/64+1), valid x a w (64*j.val+1) (min 64 (H-64*j.val)) = true) :
    Window x H := by
  refine ⟨a,fun n lo hi => ?_⟩
  let j : Fin (H/64+1) := ⟨(n-1)/64, by omega⟩
  have h := cert j
  change valid x a w (64*((n-1)/64)+1) (min 64 (H-64*((n-1)/64))) = true at h
  exact ⟨w n,at_position h (by omega) (by omega)⟩

end TemoinIntervalle687
