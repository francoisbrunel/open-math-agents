import FormalConjectures.ErdosProblems.«687»
import Mathlib.Data.Nat.ChineseRemainder

/-! Prescribing arbitrary rows of a cover costs less than their product in
interval length. This normalizes a growing prefix before estimating Y. -/
namespace ClassesImposees687
open scoped BigOperators

def fixedCover (x H : ℕ) (P : Finset ℕ) (b : ℕ → ℕ) : Prop :=
  ∃ a : ℕ → ℕ, (∀ p ∈ P, a p ≡ b p [MOD p]) ∧
    ∀ i ∈ Finset.Icc 1 H, ∃ p ≤ x, p.Prime ∧ i ≡ a p [MOD p]

private def negClass (v p : ℕ) := p-v%p

private theorem neg_add (v : ℕ) {p : ℕ} (hp : 0<p) : negClass v p+v ≡ 0 [MOD p] := by
  calc
    _ ≡ negClass v p+(v%p) [MOD p] := (Nat.mod_modEq v p).symm.add_left _
    _ = p := Nat.sub_add_cancel (Nat.mod_lt v hp).le
    _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl

/-- A common shift realizes all prescribed classes, even if the original
cover was optimal. The product is one when no rows are prescribed. -/
theorem prescribe {x H : ℕ} (cov : Green46.IsCoveredByResidues x H)
    (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (b : ℕ → ℕ) :
    fixedCover x (H-((∏ p ∈ P,p)-1)) P b := by
  classical
  obtain ⟨a,all⟩ := cov
  let diff (p : ℕ) := a p+negClass (b p) p
  have nz : ∀ p∈P, id p ≠ 0 := fun p hp => (pr p hp).ne_zero
  have pair : Set.Pairwise (P : Set ℕ) (Function.onFun Nat.Coprime id) :=
    fun i hi j hj ne => (Nat.coprime_primes (pr i hi) (pr j hj)).mpr ne
  let t := Nat.chineseRemainderOfFinset diff id P nz pair
  let d := t.val
  have small : d < ∏ p ∈ P,p := Nat.chineseRemainderOfFinset_lt_prod diff id nz pair
  let c (p : ℕ) := a p+negClass d p
  have back {p : ℕ} (hp : 0<p) : c p+d ≡ a p [MOD p] := by
    simpa only [c,Nat.add_assoc,Nat.add_zero] using (neg_add d hp).add_left (a p)
  refine ⟨c,?_,?_⟩
  · intro p hp
    have hit : d ≡ diff p [MOD p] := t.property p hp
    have toA : b p+d ≡ a p [MOD p] := calc
      _ ≡ b p+diff p [MOD p] := hit.add_left _
      _ = a p+(negClass (b p) p+b p) := by dsimp [diff]; omega
      _ ≡ a p [MOD p] := by simpa using (neg_add (b p) (pr p hp).pos).add_left (a p)
    exact Nat.ModEq.add_right_cancel' d ((back (pr p hp).pos).trans toA.symm)
  · intro i hi
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
    obtain ⟨p,px,prime,hit⟩ := all (i+d) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    exact ⟨p,px,prime,Nat.ModEq.add_right_cancel' d (hit.trans (back prime.pos).symm)⟩

theorem at_maximum (x : ℕ) (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (b : ℕ → ℕ) :
    fixedCover x (Erdos687.Y x-((∏ p ∈ P,p)-1)) P b := by
  apply prescribe _ P pr b
  exact Nat.sSup_mem (s := {n : ℕ | Green46.IsCoveredByResidues x n})
    ⟨0,fun _ => 0,by simp⟩ ⟨primorial x,fun _ hn => (Erdos687.lt_primorial_of_isCoveredByResidues hn).le⟩

/-- Every prefix through floor(log base 16 of x) may be prescribed,
including simultaneous zero classes, at a cost of at most sqrt(x). -/
theorem logarithmic_prefix {x : ℕ} (hx : x ≠ 0) (b : ℕ → ℕ) :
    fixedCover x (Erdos687.Y x-x.sqrt) (Nat.log 16 x).primesLE b := by
  let w := Nat.log 16 x
  have sq : (primorial w)^2 ≤ x := calc
    _ ≤ (4^w)^2 := Nat.pow_le_pow_left (primorial_le_four_pow w) 2
    _ = (4^2)^w := by rw [← pow_mul,← pow_mul,Nat.mul_comm w 2]
    _ = 16^w := by norm_num
    _ ≤ _ := Nat.pow_log_le_self 16 hx
  have size : primorial w ≤ x.sqrt := Nat.le_sqrt.mpr (by simpa only [pow_two] using sq)
  obtain ⟨a,agree,all⟩ := at_maximum x w.primesLE (fun p hp => (Nat.mem_primesLE.mp hp).2) b
  refine ⟨a,agree,?_⟩
  intro n hn
  obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
  apply all n (Finset.mem_Icc.mpr ⟨lo,?_⟩)
  change n ≤ Erdos687.Y x-(primorial w-1)
  omega

end ClassesImposees687
#print axioms ClassesImposees687.at_maximum
#print axioms ClassesImposees687.logarithmic_prefix
