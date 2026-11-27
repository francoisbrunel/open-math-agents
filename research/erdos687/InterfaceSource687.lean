import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! Quantitative survivor inequality in Mathlib definitions shared by the
    original Jacobsthal project and the Left to Solve project. -/
namespace InterfaceSource687
open Filter
open scoped BigOperators

def primes (z : ℕ) := (Finset.range (z+1)).filter Nat.Prime
noncomputable def width (z : ℝ) := Real.log z/(Real.log (Real.log z))^2
noncomputable def height (z : ℝ) := ⌊z^2/(Real.log z)^2⌋₊
noncomputable def scale (z : ℝ) := Real.log z/Real.log (width z)
noncomputable def product (z : ℕ) : ℝ := ∏ p ∈ primes z, (1-1/(p:ℝ))
noncomputable def remaining (Y z : ℕ) (a : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range Y).filter fun i => ∀ p ∈ primes z, i%p ≠ a p%p

/-- A common statement in elementary Mathlib types for both Lean versions. -/
def statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c*((height z:ℝ)*product ⌊width z⌋₊/(scale z)^2) ≤
      ((remaining (height z) ⌊z⌋₊ a).card:ℝ)

end InterfaceSource687
