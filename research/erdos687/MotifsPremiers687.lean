import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic

/-! Counting positions with a specified exact set of prime hits by
ordinary sieving of a shorter interval. The starting point can be
absorbed into the residues, so the interval here is indexed from zero. -/
namespace MotifsPremiers687
open Finset
open scoped BigOperators

def cell (P K : Finset ℕ) (a : ℕ → ℕ) (H : ℕ) : Finset ℕ :=
  (range H).filter fun n => ∀ p ∈ P, (n%p=a p%p ↔ p ∈ K)

def survivors (P : Finset ℕ) (b : ℕ → ℕ) (M : ℕ) : Finset ℕ :=
  (range M).filter fun j => ∀ p ∈ P, j%p ≠ b p%p

/-- The modulus and induced classes do not depend on the interval length. -/
theorem exact_progression (P K : Finset ℕ) (pr : ∀ p ∈ P, p.Prime)
    (sub : K ⊆ P) (a : ℕ → ℕ) :
    let d := ∏ p ∈ K, p
    ∃ r < d, ∃ b : ℕ → ℕ, ∀ j,
      (∀ p ∈ P, ((r+d*j)%p=a p%p ↔ p ∈ K)) ↔
        ∀ p ∈ P \ K, j%p ≠ b p%p := by
  classical
  let d := ∏ p ∈ K, p
  have nz : ∀ p ∈ K, id p ≠ 0 := fun p hp => (pr p (sub hp)).ne_zero
  have pair : Set.Pairwise (K : Set ℕ) (Function.onFun Nat.Coprime id) :=
    fun p hp q hq ne => (Nat.coprime_primes (pr p (sub hp)) (pr q (sub hq))).mpr ne
  let u := Nat.chineseRemainderOfFinset a id K nz pair
  let r := u.val
  have small : r < d := Nat.chineseRemainderOfFinset_lt_prod a id nz pair
  let t (p : ℕ) := if h : d.Coprime p then (Nat.chineseRemainder h r (a p)).val else 0
  let b (p : ℕ) := t p/d
  have induced (p : ℕ) (hp : p ∈ P \ K) (j : ℕ) :
      r+d*j ≡ a p [MOD p] ↔ j ≡ b p [MOD p] := by
    obtain ⟨inP,out⟩ := mem_sdiff.mp hp
    have cop : d.Coprime p := Nat.coprime_prod_left_iff.mpr fun q hq =>
      (Nat.coprime_primes (pr q (sub hq)) (pr p inP)).mpr (fun eq => out (eq ▸ hq))
    have crt : t p ≡ r [MOD d] ∧ t p ≡ a p [MOD p] := by
      dsimp only [t]; rw [dif_pos cop]; exact (Nat.chineseRemainder cop r (a p)).property
    have rem : t p%d=r := calc
      _ = r%d := crt.1
      _ = r := Nat.mod_eq_of_lt small
    have base : r+d*b p=t p := by rw [← rem]; exact Nat.mod_add_div _ _
    rw [← base] at crt
    constructor
    · intro hit
      exact Nat.ModEq.cancel_left_of_coprime cop.symm
        (Nat.ModEq.add_left_cancel' r (hit.trans crt.2.symm))
    · intro hit; exact ((hit.mul_left d).add_left r).trans crt.2
  refine ⟨r,small,b,?_⟩
  intro j
  constructor
  · intro all p hp eq
    exact (mem_sdiff.mp hp).2 ((all p (mem_sdiff.mp hp).1).mp ((induced p hp j).mpr eq))
  · intro avoid p hp
    by_cases inside : p ∈ K
    · have dv : p ∣ d := dvd_prod_of_mem (fun p : ℕ => p) inside
      have hit : r+d*j ≡ r [MOD p] := Nat.add_modEq_left_iff.mpr (dvd_mul_of_dvd_left dv j)
      exact ⟨fun _ => inside,fun _ => hit.trans (u.property p inside)⟩
    · have out : p ∈ P \ K := mem_sdiff.mpr ⟨hp,inside⟩
      exact ⟨fun h => (avoid p out ((induced p out j).mp h)).elim, fun h => (inside h).elim⟩

theorem lower (P K : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (sub : K ⊆ P) (a : ℕ → ℕ) :
    let d := ∏ p ∈ K, p
    ∃ b : ℕ → ℕ, ∀ H, (survivors (P \ K) b (H/d)).card ≤ (cell P K a H).card := by
  classical
  let d := ∏ p ∈ K, p
  obtain ⟨r,small,b,progression⟩ := exact_progression P K pr sub a
  refine ⟨b,fun H => card_le_card_of_injOn (fun j : ℕ => r+d*j) ?_ ?_⟩
  · intro j hj
    obtain ⟨bound,avoid⟩ := mem_filter.mp hj
    have upto : d*(j+1) ≤ H := (Nat.mul_le_mul_left d (mem_range.mp bound)).trans
      (by simpa [Nat.mul_comm] using Nat.div_mul_le_self H d)
    exact mem_filter.mpr ⟨mem_range.mpr (by
      change r+d*j < H
      change r<d at small
      rw [Nat.mul_succ] at upto
      omega),
      (progression j).mpr avoid⟩
  · intro i _ j _ eq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<d) (Nat.add_left_cancel eq)

/-- One can impose artificial index rows also at the primes dividing d.
This permits an ordinary interval lower sieve with no excluded modulus. -/
theorem lower_from_full (P K : Finset ℕ) (pr : ∀ p ∈ P, p.Prime)
    (sub : K ⊆ P) (a : ℕ → ℕ) (H : ℕ) (L : ℕ) (bound : ∀ b : ℕ → ℕ,
      L ≤ (survivors P b (H/(∏ p ∈ K, p))).card) : L ≤ (cell P K a H).card := by
  obtain ⟨b,h⟩ := lower P K pr sub a
  apply (bound b).trans ((card_le_card ?_).trans (h H))
  intro n hn
  obtain ⟨inside,avoid⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨inside,fun p hp => avoid p (mem_sdiff.mp hp).1⟩

theorem sum_cells (P : Finset ℕ) (family : Finset (Finset ℕ)) (a : ℕ → ℕ)
    (H : ℕ) (sub : ∀ K ∈ family, K ⊆ P) :
    (family.biUnion (fun K => cell P K a H)).card =
      ∑ K ∈ family, (cell P K a H).card := by
  apply card_biUnion
  intro K hK J hJ different
  apply Finset.disjoint_left.mpr
  intro n nK nJ
  obtain ⟨_,atK⟩ := mem_filter.mp nK
  obtain ⟨_,atJ⟩ := mem_filter.mp nJ
  apply different
  ext p
  by_cases hp : p ∈ P
  · exact (atK p hp).symm.trans (atJ p hp)
  · exact ⟨fun yes => (hp (sub K hK yes)).elim, fun yes => (hp (sub J hJ yes)).elim⟩

end MotifsPremiers687
#print axioms MotifsPremiers687.exact_progression
#print axioms MotifsPremiers687.lower
#print axioms MotifsPremiers687.lower_from_full
#print axioms MotifsPremiers687.sum_cells
