import Arrondi687

/-! A necessary condition on any method that bounds the removed weight
    separately for blocks of unrestricted prime classes. -/
namespace GroupesPonderes687
open Arrondi687 SurvieTotale687

noncomputable def density (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1-1/(p:ℝ))

theorem block_capacity {S P : Finset ℕ} {c : ℝ} (w : ℕ → ℝ)
    (wn : ∀ n, 0≤w n) (pos : ∀ p ∈ P, 0<p)
    (cap : ∀ a : ℕ → ℕ, (∑ n ∈ S,w n) ≤ c+∑ n ∈ remaining S P a,w n) :
    (∑ n ∈ S,w n)*(1-density P) ≤ c := by
  let q (p _ : ℕ) := 1/(p:ℝ)
  have law : Law P q := by
    intro p hp
    refine ⟨pos p hp,fun _ _ => by dsimp [q]; positivity,?_⟩
    have pn : (p:ℝ)≠0 := by exact_mod_cast (pos p hp).ne'
    simp [q,pn]
  obtain ⟨a,ha⟩ := rounding S P q law w wn
  change (∑ n ∈ remaining S P a,w n) ≤ ∑ n ∈ S,w n*density P at ha
  rw [← Finset.sum_mul] at ha
  linarith [cap a]

theorem blocks {S J : Finset ℕ} (P : ℕ → Finset ℕ) (w c : ℕ → ℝ)
    (wn : ∀ n, 0≤w n) (pos : ∀ j ∈ J, ∀ p ∈ P j, 0<p)
    (capacity : ∀ j ∈ J, ∀ a : ℕ → ℕ, (∑ n ∈ S,w n) ≤ c j+∑ n ∈ remaining S (P j) a,w n)
    (gap : ∑ j ∈ J,c j < ∑ n ∈ S,w n) (wp : 0<∑ n ∈ S,w n) :
    ∑ j ∈ J, (1-density (P j)) < 1 := by
  apply (mul_lt_mul_iff_right₀ wp).mp
  rw [mul_one,Finset.mul_sum]
  exact (Finset.sum_le_sum (fun j hj => block_capacity w wn (pos j hj) (capacity j hj))).trans_lt gap

private theorem product_floor {J : Finset ℕ} {v : ℕ → ℝ}
    (unit : ∀ j ∈ J, 0≤v j ∧ v j≤1) : 1-∑ j ∈ J,(1-v j) ≤ ∏ j ∈ J,v j := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J fresh ih =>
    have u := unit i (by simp)
    have prev := ih (fun j hj => unit j (by simp [hj]))
    have total : 0≤∑ j ∈ J, (1-v j) := Finset.sum_nonneg (fun j hj => by
      have h := (unit j (by simp [hj])).2; linarith)
    rw [Finset.sum_insert fresh,Finset.prod_insert fresh]
    nlinarith [mul_le_mul_of_nonneg_left prev u.1,
      mul_nonneg (sub_nonneg.mpr u.2) total]

/-- When the overall survival density V is small, a single block
    must contain all but at most 2V of the summed block hit probabilities. -/
theorem concentration {J : Finset ℕ} (v : ℕ → ℝ)
    (unit : ∀ j ∈ J, 0≤v j ∧ v j≤1) (gap : ∑ j ∈ J,(1-v j)<1)
    (small : (∏ j ∈ J,v j)≤Real.exp (-2)) :
    ∃ i ∈ J, v i<1/2 ∧ ∑ j ∈ J.erase i,(1-v j)<2*(∏ j ∈ J,v j) := by
  classical
  have found : ∃ i ∈ J, v i<1/2 := by
    by_contra! high
    have single (i : ℕ) (hi : i ∈ J) : Real.exp (-(2*(1-v i))) ≤ v i := by
      have u := unit i hi
      have h := high i hi
      rw [Real.exp_neg,inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have exp := Real.add_one_le_exp (2*(1-v i))
      nlinarith [mul_le_mul_of_nonneg_left exp u.1, mul_nonneg (by linarith : 0≤2*v i-1) (sub_nonneg.mpr u.2)]
    have cmp := Finset.prod_le_prod (fun i _ => (Real.exp_pos (-(2*(1-v i)))).le) single
    rw [← Real.exp_sum,Finset.sum_neg_distrib,← Finset.mul_sum] at cmp
    exact (not_lt_of_ge (cmp.trans small)) (Real.exp_lt_exp.mpr (by linarith))
  obtain ⟨i,hi,hv⟩ := found
  let A := ∑ j ∈ J.erase i,(1-v j)
  let V := ∏ j ∈ J.erase i,v j
  have sum : (1-v i)+A = ∑ j ∈ J,(1-v j) := Finset.add_sum_erase J (fun j => 1-v j) hi
  have prod : v i*V = ∏ j ∈ J,v j := Finset.mul_prod_erase _ _ hi
  have floor : 1-A≤V := product_floor (fun j hj => unit j (Finset.mem_of_mem_erase hj))
  refine ⟨i,hi,hv,?_⟩
  change A<_
  rw [← prod]
  have : 1/2≤V := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this (unit i hi).1]

end GroupesPonderes687

#print axioms GroupesPonderes687.concentration
