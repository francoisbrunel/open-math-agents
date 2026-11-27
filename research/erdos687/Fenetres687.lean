import Blocs687
import Bords687

/-! Turn a bound on the number of survivors of one long interval into a
    complete cover of a shorter interval with a prescribed prime cutoff. -/
namespace Fenetres687
open Transfert687

/-- If the long interval contains fewer survivors than one more than the
    available primes per full block, some block can be finished individually. -/
theorem cover_of_sparse_blocks {z x H J : ℕ} (hzx : z ≤ x) (a : ℕ → ℕ)
    (few : (survivors z H a).card < H/J*((x.primesLE \ z.primesLE).card+1)) :
    Green46.IsCoveredByResidues x J := by
  by_contra fail
  let r := (x.primesLE \ z.primesLE).card
  have allblocks (b : ℕ → ℕ) : ((r+1:ℕ):ℝ) ≤ (survivors z J b).card := by
    have none : ¬(survivors z J b).card ≤ r := fun h => fail (Bords687.finish_singletons hzx b h)
    exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge none)
  have lower := Blocs687.blocks allblocks H a
  have contrary : H/J*(r+1) ≤ (survivors z H a).card := by exact_mod_cast lower
  exact few.not_ge contrary

/-- An upper bound on the number of required blocks controls the length
    of the long interval directly, including its final partial block. -/
theorem length_lt {z x H q : ℕ} (hzx : z ≤ x) (a : ℕ → ℕ)
    (few : (survivors z H a).card < q*((x.primesLE \ z.primesLE).card+1)) :
    H < q*(Erdos687.Y x+1) := by
  by_contra! h
  have blocks := (Nat.le_div_iff_mul_le (Nat.succ_pos (Erdos687.Y x))).mpr h
  have cover := cover_of_sparse_blocks hzx a (few.trans_le
    (Nat.mul_le_mul_right ((x.primesLE \ z.primesLE).card+1) blocks))
  exact (Nat.not_succ_le_self _) (le_Y_of_covered cover)

/-- An explicit integer lower bound for Y from any single near-cover. -/
theorem near_cover_lower {z x H : ℕ} (hzx : z ≤ x) (a : ℕ → ℕ) :
    H / ((survivors z H a).card / ((x.primesLE \ z.primesLE).card+1) + 1) ≤ Erdos687.Y x := by
  let r := (x.primesLE \ z.primesLE).card
  let m := (survivors z H a).card
  let k := m/(r+1)+1
  let J := H/k
  change J ≤ _
  by_cases pos : J = 0
  · simp [pos]
  have hk : k*J ≤ H := by dsimp [J]; exact Nat.mul_div_le H k
  have blocks : k ≤ H/J := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero pos)).mpr hk
  have lt : m < k*(r+1) := (Nat.div_lt_iff_lt_mul (by omega : 0 < r+1)).mp
    (by dsimp [k]; omega)
  exact le_Y_of_covered (cover_of_sparse_blocks hzx a
    (lt.trans_le (Nat.mul_le_mul_right (r+1) blocks)))

end Fenetres687
