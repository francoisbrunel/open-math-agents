import DiviseurTemoin687
import Semence1223

/-! Full interval certificate at cutoff 1223. -/
namespace Preuve1223

theorem cover : ∃ a : ℕ, ∀ n : ℕ, 1 ≤ n → n ≤ 5177 →
    ∃ p ≤ 1223, p.Prime ∧ n % p = a % p :=
  DiviseurTemoin687.prime_cover Semence1223.At200.certificate

#print axioms cover

end Preuve1223
