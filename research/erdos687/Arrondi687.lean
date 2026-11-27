import ChoixMultiples687

/-! Independent, non-uniform choices of one class per modulus. Conditional
    averaging gives a deterministic cover after a reserve of singleton rows. -/
namespace Arrondi687
open SurvieTotale687

def Law (P : Finset ℕ) (q : ℕ → ℕ → ℝ) : Prop :=
  ∀ p ∈ P, 0 < p ∧ (∀ r ∈ Finset.range p, 0 ≤ q p r) ∧ ∑ r ∈ Finset.range p, q p r = 1

private theorem unit {P q} (law : Law P q) {p : ℕ} (hp : p ∈ P) (n : ℕ) :
    0 ≤ 1-q p (n%p) := by
  obtain ⟨pos,nn,total⟩ := law p hp
  have inside := Finset.mem_range.mpr (Nat.mod_lt n pos)
  have le := Finset.single_le_sum nn inside
  rw [total] at le
  linarith

private theorem choose_row (U : Finset ℕ) {p : ℕ} (pos : 0 < p) (w q : ℕ → ℝ)
    (nn : ∀ r ∈ Finset.range p, 0 ≤ q r) (total : ∑ r ∈ Finset.range p, q r = 1) :
    ∃ r < p, (∑ n ∈ U, if n%p=r then 0 else w n) ≤ ∑ n ∈ U, w n*(1-q (n%p)) := by
  classical
  let f (r : ℕ) := ∑ n ∈ U, if n%p=r then 0 else w n
  have mean : ∑ r ∈ Finset.range p, q r*f r = ∑ n ∈ U, w n*(1-q (n%p)) := by
    simp only [f,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    have inside := Finset.mem_range.mpr (Nat.mod_lt n pos)
    calc
      _ = ∑ r ∈ Finset.range p, (q r*w n - if r=n%p then q r*w n else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases h : r=n%p <;> simp [h,Ne.symm]
      _ = w n*(1-q (n%p)) := by
        rw [Finset.sum_sub_distrib,← Finset.sum_mul,total]
        simp [inside]
        ring
  obtain ⟨r,hr,small⟩ := Finset.exists_min_image (Finset.range p) f
    (Finset.nonempty_range_iff.mpr (by omega))
  refine ⟨r,Finset.mem_range.mp hr,?_⟩
  change f r ≤ _
  rw [← mean]
  calc
    _ = ∑ j ∈ Finset.range p, q j*f r := by rw [← Finset.sum_mul,total,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (small j hj) (nn j hj))

theorem rounding (S P : Finset ℕ) (q : ℕ → ℕ → ℝ) (law : Law P q)
    (w : ℕ → ℝ) (wn : ∀ n, 0 ≤ w n) :
    ∃ a, (∑ n ∈ remaining S P a, w n) ≤
      ∑ n ∈ S, w n * ∏ p ∈ P, (1-q p (n%p)) := by
  classical
  induction P using Finset.induction_on generalizing w with
  | empty => exact ⟨fun _ => 0,by simp [remaining]⟩
  | @insert p P fresh ih =>
    obtain ⟨pos,nn,total⟩ := law p (Finset.mem_insert_self ..)
    have old : Law P q := fun i hi => law i (Finset.mem_insert_of_mem hi)
    let v (n : ℕ) := w n * (1-q p (n%p))
    obtain ⟨a,ha⟩ := ih old v (fun n => mul_nonneg (wn n) (unit law (Finset.mem_insert_self ..) n))
    let U := remaining S P a
    obtain ⟨r,rp,hr⟩ := choose_row U pos w (q p) nn total
    let b := Function.update a p r
    have equal : remaining S (insert p P) b = U.filter (fun n => n%p ≠ r) := by
      have prev (j : ℕ) (hj : j ∈ P) : b j = a j :=
        Function.update_of_ne (ne_of_mem_of_not_mem hj fresh) r a
      have cur : b p = r := Function.update_self ..
      ext n
      simp (config := {contextual := true}) only [remaining,U,Finset.mem_filter,
        Finset.mem_insert,forall_eq_or_imp,prev,cur,Nat.mod_eq_of_lt rp]
      tauto
    refine ⟨b,?_⟩
    calc
      _ = ∑ n ∈ U, if n%p=r then 0 else w n := by
        rw [equal,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases h : n%p=r <;> simp [h]
      _ ≤ ∑ n ∈ U, v n := hr
      _ ≤ _ := ha.trans_eq (by simp only [v,Finset.prod_insert fresh,mul_assoc])

theorem depth_completion {S P R : Finset ℕ} (dis : Disjoint P R)
    (q : ℕ → ℕ → ℝ) (law : Law P q) (t : ℝ)
    (depth : ∀ n ∈ S, t ≤ ∑ p ∈ P, q p (n%p))
    (stock : (S.card:ℝ)*Real.exp (-t) ≤ R.card) :
    Extension687.Completes S (P ∪ R) := by
  classical
  obtain ⟨a,ha⟩ := rounding S P q law (fun _ => 1) (by simp)
  have term (n : ℕ) (hn : n ∈ S) :
      ∏ p ∈ P, (1-q p (n%p)) ≤ Real.exp (-t) := calc
    _ ≤ ∏ p ∈ P, Real.exp (-(q p (n%p))) :=
      Finset.prod_le_prod (fun p hp => unit law hp n) (fun p _ => Real.one_sub_le_exp_neg _)
    _ = Real.exp (-(∑ p ∈ P, q p (n%p))) := by rw [← Real.exp_sum,Finset.sum_neg_distrib]
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg (depth n hn))
  have total := Finset.sum_le_sum term
  simp only [one_mul,Finset.sum_const,nsmul_eq_mul,mul_one] at ha total
  have cap : (remaining S P a).card ≤ R.card := by exact_mod_cast ha.trans (total.trans stock)
  obtain ⟨b,hb⟩ := Extension687.completes_of_card cap
  refine ⟨fun p => if p ∈ P then a p else b p,fun n hn => ?_⟩
  by_cases old : ∃ p ∈ P, n%p = a p%p
  · obtain ⟨p,hp,e⟩ := old
    exact ⟨p,Finset.mem_union_left _ hp,by simpa only [if_pos hp] using e⟩
  · push Not at old
    obtain ⟨p,hp,e⟩ := hb n (Finset.mem_filter.mpr ⟨hn,old⟩)
    have no : p ∉ P := fun present => Finset.disjoint_left.mp dis present hp
    exact ⟨p,Finset.mem_union_right _ hp,by simpa only [if_neg no] using e⟩

end Arrondi687
