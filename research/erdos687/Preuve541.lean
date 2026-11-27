import DiviseurTemoin687
import Semence541

namespace Preuve541

theorem cover : ∃ a : ℕ, ∀ n : ℕ, 1 ≤ n → n ≤ 2057 →
    ∃ p ≤ 541, p.Prime ∧ n % p = a % p :=
  DiviseurTemoin687.prime_cover Semence541.At100.certificate

#print axioms cover

end Preuve541
