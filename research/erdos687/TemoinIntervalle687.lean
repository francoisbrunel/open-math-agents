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

theorem assemble {x H a : Nat} {w : Nat → Nat}
    (cert : ∀ j : Fin (H/64+1), valid x a w (64*j.val+1) (min 64 (H-64*j.val)) = true) :
    Window x H := by
  refine ⟨a,fun n lo hi => ?_⟩
  let j : Fin (H/64+1) := ⟨(n-1)/64, by omega⟩
  have h := cert j
  change valid x a w (64*((n-1)/64)+1) (min 64 (H-64*((n-1)/64))) = true at h
  exact ⟨w n,at_position h (by omega) (by omega)⟩

end TemoinIntervalle687
