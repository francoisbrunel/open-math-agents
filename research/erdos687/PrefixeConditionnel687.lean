import MoyenneConditionnelle687
import ClassesImposees687
import Mertens687

/-! Uniform control of the conditional mean after prescribing a growing
prefix of prime rows. The loss in the mean is at most one CRT period. -/
namespace PrefixeConditionnel687
open ConcentrationClasses687 MoyenneConditionnelle687 Transfert687 Filter
open scoped BigOperators
noncomputable section

private def points (P : Finset ℕ) (H : ℕ) (a : Rows) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 H).filter (fun n => ∀ p ∈ P, n%p ≠ a p%p)

private theorem card_eq (P : Finset ℕ) (H : ℕ) (a : Rows) :
    stock P H a = ((points P H a).card:ℝ) := by
  classical
  simp only [stock,keep,points,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

theorem translated (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (H : ℕ) (a b : Rows) :
    stock P H a ≤ stock P H b + ((∏ p ∈ P,p:ℕ):ℝ) := by
  classical
  obtain ⟨d,small,same⟩ := ClassesImposees687.common_shift P pr a b
  let A := points P H a
  let B := points P H b
  let T := A.filter (fun n => d < n)
  have sub : A ⊆ Finset.Icc 1 d ∪ T := by
    intro n hn
    by_cases h : d < n
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,h⟩)
    · have lo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨lo,by omega⟩)
  have copied : T.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n-d)
    · intro n hn
      obtain ⟨na,dn⟩ := Finset.mem_filter.mp hn
      obtain ⟨win,avoid⟩ := Finset.mem_filter.mp na
      obtain ⟨_,up⟩ := Finset.mem_Icc.mp win
      change n-d ∈ points P H b
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
      intro p hp bad
      apply avoid p hp
      change n ≡ a p [MOD p]
      have h := (Nat.ModEq.add_right d bad).trans (same p hp)
      simpa only [Nat.sub_add_cancel dn.le] using h
    · intro n hn j hj eqn
      have h := (Finset.mem_filter.mp hn).2
      have h' := (Finset.mem_filter.mp hj).2
      change n-d=j-d at eqn
      omega
  have inc := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have sz : (Finset.Icc 1 d).card=d := by simp
  rw [sz] at inc
  rw [card_eq,card_eq]
  exact_mod_cast (show A.card ≤ B.card+(∏ p ∈ P,p) by omega)

def product (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1-(p:ℝ)⁻¹)

theorem local_mean (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (H : ℕ) (a : Rows) :
    (H:ℝ)*product P ≤ stock P H a+((∏ p ∈ P,p:ℕ):ℝ) := by
  have pos (p : ℕ) (hp : p ∈ P.toList) := (pr p (Finset.mem_toList.mp hp)).pos
  have h := sample_mono P.toList (fun b => translated P pr H b a) a
  have all := expected P.toList P.nodup_toList P (fun _ h => Finset.mem_toList.mp h) pos H a
  rw [all,sample_const P.toList pos,Finset.prod_map_toList] at h
  simpa [product,stock,keep,mul_comm] using h

theorem conditional_mean (P R : Finset ℕ) (sub : R ⊆ P) (pr : ∀ p ∈ P, p.Prime)
    (H : ℕ) (a : Rows) :
    (H:ℝ)*product P ≤ sample R.toList (stock P H) a+((∏ p ∈ P \ R,p:ℕ):ℝ) := by
  classical
  let D := ((∏ p ∈ P \ R,p:ℕ):ℝ)
  have pos (p : ℕ) (hp : p ∈ R.toList) := (pr p (sub (Finset.mem_toList.mp hp))).pos
  have av := expected R.toList R.nodup_toList P (fun _ h => sub (Finset.mem_toList.mp h)) pos H a
  have lb := local_mean (P \ R) (fun p hp => pr p (Finset.mem_sdiff.mp hp).1) H a
  have nn (p : ℕ) (hp : p ∈ R) : 0 ≤ 1-(p:ℝ)⁻¹ := by
    have one : (1:ℝ) ≤ p := by exact_mod_cast (pr p (sub hp)).one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ one)
  have rp : 0 ≤ product R := Finset.prod_nonneg nn
  have ru : product R ≤ 1 := Finset.prod_le_one nn (fun p _ => by linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p)])
  have split : product (P \ R)*product R = product P := Finset.prod_sdiff sub
  have t := mul_le_mul_of_nonneg_right lb rp
  have e := mul_le_mul_of_nonneg_left ru (show 0 ≤ D by dsimp [D]; positivity)
  rw [Finset.prod_map_toList,Finset.toList_toFinset] at av
  rw [av,← split]
  change (H:ℝ)*(product (P \ R)*product R) ≤ product R*stock (P \ R) H a+D
  change ((H:ℝ)*product (P \ R))*product R ≤ (stock (P \ R) H a+D)*product R at t
  linarith only [t,e,show (H:ℝ)*(product (P \ R)*product R) =
    ((H:ℝ)*product (P \ R))*product R by ring,
    show (stock (P \ R) H a+D)*product R = product R*stock (P \ R) H a+D*product R by ring]

end
end PrefixeConditionnel687
#print axioms PrefixeConditionnel687.conditional_mean
