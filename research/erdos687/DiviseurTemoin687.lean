import TemoinIntervalle687
import Mathlib.Data.Nat.Prime.Defs

/-! Turn the machine-checked divisor table into a full covering by primes. -/
namespace DiviseurTemoin687

theorem prime_cover {x H : ℕ} (h : TemoinIntervalle687.Window x H) :
    ∃ a : ℕ, ∀ n, 1 ≤ n → n ≤ H → ∃ p ≤ x, p.Prime ∧ n % p = a % p := by
  obtain ⟨a,all⟩ := h
  refine ⟨a,fun n lo hi => ?_⟩
  obtain ⟨d,two,cap,hit⟩ := all n lo hi
  have dvd := Nat.minFac_dvd d
  refine ⟨d.minFac,(Nat.le_of_dvd (by omega) dvd).trans cap,Nat.minFac_prime (by omega),?_⟩
  calc
    n % d.minFac = (n % d) % d.minFac := (Nat.mod_mod_of_dvd n dvd).symm
    _ = (a % d) % d.minFac := by rw [hit]
    _ = a % d.minFac := Nat.mod_mod_of_dvd a dvd

end DiviseurTemoin687
