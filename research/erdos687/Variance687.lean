import Distribution687
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic

/-! The two-point counting kernel for interval covers. This is the
elementary divisor expansion underlying the Hausman–Shapiro second moment. -/
namespace Variance687
open Distribution687
open scoped BigOperators

private theorem simultaneous (D : Finset ℕ) (pr : ∀ p ∈ D, p.Prime) (i j : ℕ) :
    (∀ p ∈ D, i%p=j%p) ↔ i ≡ j [MOD ∏ p ∈ D, p] := by
  induction D using Finset.induction_on with
  | empty => simp [Nat.ModEq,Nat.mod_one]
  | @insert p D fresh ih =>
    have old : ∀ q ∈ D, q.Prime := fun q h => pr q (Finset.mem_insert_of_mem h)
    have prime := pr p (Finset.mem_insert_self _ _)
    have co : p.Coprime (∏ q ∈ D, q) := Nat.coprime_prod_right_iff.mpr fun q h =>
      (Nat.coprime_primes prime (old q h)).mpr (fun eq => fresh (eq ▸ h))
    rw [Finset.prod_insert fresh,← Nat.modEq_and_modEq_iff_modEq_mul co,← ih old]
    simp [Nat.ModEq]

theorem pair_choices (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (i j : ℕ) :
    (choices P {i,j}).card =
      ∑ D ∈ P.powerset, if i ≡ j [MOD ∏ p ∈ D, p] then ∏ p ∈ P \ D, (p-2) else 0 := by
  classical
  rw [avoidance]
  have row (p : ℕ) (hp : p ∈ P) :
      (allowed {i,j} p).card = (if i%p=j%p then 1 else 0)+(p-2) := by
    rw [allowed_card _ (pr p hp).pos]
    have two := (pr p hp).two_le
    by_cases eq : i%p=j%p
    · simp [eq]; omega
    · simp [eq]
  rw [Finset.prod_congr rfl row,Finset.prod_add]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.prod_boole]
  have same := simultaneous D (fun p h => pr p (Finset.mem_powerset.mp hD h)) i j
  by_cases yes : ∀ p ∈ D, i%p=j%p
  · rw [if_pos yes,if_pos (same.mp yes),one_mul]
  · rw [if_neg yes,if_neg (fun h => yes (same.mpr h)),zero_mul]

private theorem class_count (H d i : ℕ) (hd : 0 < d) :
    ((Finset.range H).filter fun n => i ≡ n [MOD d]).card ≤ H/d+1 := by
  apply le_trans (b := (Finset.range (H/d+1)).card)
  · apply Finset.card_le_card_of_injOn (fun n : ℕ => n/d)
    · intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le))
    · intro n hn m hm eq
      have en := (Finset.mem_filter.mp hn).2
      have em := (Finset.mem_filter.mp hm).2
      have rem : n%d=m%d := en.symm.trans em
      calc n = n%d+d*(n/d) := (Nat.mod_add_div _ _).symm
           _ = m%d+d*(m/d) := by rw [rem, show n/d=m/d from eq]
           _ = _ := Nat.mod_add_div _ _
  · simp

theorem conditioned_count (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (i H : ℕ) :
    (∑ j ∈ Finset.range H, (choices P {i,j}).card) ≤
      ∑ D ∈ P.powerset, (H/(∏ p ∈ D,p)+1) * ∏ p ∈ P \ D, (p-2) := by
  classical
  simp_rw [pair_choices P pr]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D hD
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  apply Nat.mul_le_mul_right
  apply class_count
  exact Finset.prod_pos fun p hp => (pr p (Finset.mem_powerset.mp hD hp)).pos

/-- After conditioning on one missed position, summing the joint
counts over an interval only costs one extra copy of its single-point count. -/
theorem conditioned_product (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (i H : ℕ) :
    (∑ j ∈ Finset.range H, ((choices P {i,j}).card:ℝ)) ≤
      (H:ℝ)*(∏ p ∈ P, ((p:ℝ)⁻¹+(↑(p-2:ℕ):ℝ))) +
        ∏ p ∈ P, (1+(↑(p-2:ℕ):ℝ)) := by
  classical
  let w := fun p : ℕ => (↑(p-2:ℕ):ℝ)
  have bound := (Nat.cast_le (α := ℝ)).mpr (conditioned_count P pr i H)
  push_cast only [Nat.cast_sum,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_prod] at bound
  apply le_trans bound
  change _ ≤ (H:ℝ)*(∏ p ∈ P, ((p:ℝ)⁻¹+w p)) + ∏ p ∈ P, (1+w p)
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro D hD
  simp only [Finset.prod_const_one,one_mul,Finset.prod_inv_distrib]
  have small := Nat.cast_div_le (α := ℝ) (m := H) (n := ∏ p ∈ D,p)
  rw [div_eq_mul_inv,Nat.cast_prod] at small
  have wn : 0 ≤ ∏ p ∈ P \ D, w p := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  have scaled := mul_le_mul_of_nonneg_right small wn
  dsimp only [w] at *
  linarith only [scaled]

private theorem pair_membership {S P : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S)
    (a : Assignment P) :
    a ∈ choices P {i,j} ↔ i ∈ misses P S a ∧ j ∈ misses P S a := by
  classical
  simp only [choices,allowed,misses,Finset.mem_filter,Finset.mem_univ,true_and,hi,hj,
    Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  exact forall_and

theorem second_moment (P S : Finset ℕ) :
    (∑ a : Assignment P, (misses P S a).card^2) =
      ∑ i ∈ S, ∑ j ∈ S, (choices P {i,j}).card := by
  classical
  have card (a : Assignment P) :
      (misses P S a).card = ∑ i ∈ S, if i ∈ misses P S a then 1 else 0 := by
    rw [← Finset.sum_filter]
    have eq : (S.filter fun i => i ∈ misses P S a) = misses P S a := by
      ext i
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun h => (Finset.mem_filter.mp h).1)
    simp [eq]
  calc
    _ = ∑ a : Assignment P, ∑ i ∈ S, ∑ j ∈ S, if a ∈ choices P {i,j} then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sq,card,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases ni : i ∈ misses P S a
      · by_cases nj : j ∈ misses P S a
        · simp only [if_pos ni,if_pos nj,if_pos ((pair_membership hi hj a).mpr ⟨ni,nj⟩),one_mul]
        · simp only [if_pos ni,if_neg nj,if_neg (fun h => nj ((pair_membership hi hj a).mp h).2),mul_zero]
      · simp only [if_neg ni,if_neg (fun h => ni ((pair_membership hi hj a).mp h).1),zero_mul]
    _ = ∑ i ∈ S, ∑ j ∈ S, ∑ a : Assignment P, if a ∈ choices P {i,j} then 1 else 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp [← Finset.sum_filter]

private theorem first_moment (P S : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) :
    (∑ a : Assignment P, (misses P S a).card) = S.card*∏ p ∈ P, (p-1) := by
  classical
  calc
    _ = ∑ a : Assignment P, ∑ i ∈ S, if a ∈ choices P {i,i} then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
      apply congrArg Finset.card
      ext i
      by_cases hi : i ∈ S
      · have e := pair_membership (P := P) hi hi a
        simp only [and_self] at e
        simpa only [Finset.mem_filter,hi,true_and] using e.symm
      · simp [misses,hi]
    _ = ∑ i ∈ S, (choices P {i,i}).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = _ := by
      have each (i : ℕ) : (choices P {i,i}).card = ∏ p ∈ P, (p-1) := by
        rw [avoidance]
        apply Finset.prod_congr rfl
        intro p hp
        simp [allowed_card _ (pr p hp).pos]
      simp only [each,Finset.sum_const,nsmul_eq_mul, Nat.cast_id]

theorem variance_bound (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (H : ℕ) :
    let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
    (∑ a : Assignment P, (((misses P (Finset.range H) a).card:ℝ) - H*V)^2) ≤
      (H:ℝ)*∏ p ∈ P, ((p:ℝ)-1) := by
  classical
  let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
  let B := ∏ p ∈ P, ((p:ℝ)-1)
  let A := (Fintype.card (Assignment P):ℝ)
  let X := fun a : Assignment P => ((misses P (Finset.range H) a).card:ℝ)
  have ap : A = ∏ p ∈ P, (p:ℝ) := by
    dsimp [A,Assignment]
    simp only [Fintype.card_pi,Fintype.card_fin,Nat.cast_prod]
    exact Finset.prod_coe_sort P fun p : ℕ => (p:ℝ)
  have AB : A*V=B := by
    rw [ap]
    change _*(∏ p ∈ P, (1-(p:ℝ)⁻¹)) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have pn : (p:ℝ) ≠ 0 := by exact_mod_cast (pr p hp).ne_zero
    field_simp
  have cv : (∏ p ∈ P, ((p:ℝ)⁻¹+(↑(p-2:ℕ):ℝ))) = V*B := by
    change _ = (∏ p ∈ P, (1-(p:ℝ)⁻¹))*∏ p ∈ P, ((p:ℝ)-1)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (pr p hp).two_le]
    have pn : (p:ℝ) ≠ 0 := by exact_mod_cast (pr p hp).ne_zero
    push_cast
    field_simp
    ring
  have bw : (∏ p ∈ P, (1+(↑(p-2:ℕ):ℝ))) = B := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (pr p hp).two_le]
    push_cast
    ring
  have first : (∑ a, X a) = (H:ℝ)*B := by
    have eq := congrArg (fun u : ℕ => (u:ℝ)) (first_moment P (Finset.range H) pr)
    simp only [Finset.card_range,Nat.cast_sum,Nat.cast_mul,Nat.cast_prod] at eq
    convert eq using 1
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (pr p hp).one_le,Nat.cast_one]
  have second : (∑ a, (X a)^2) ≤ (H:ℝ)*((H:ℝ)*(V*B)+B) := by
    have eq := congrArg (fun u : ℕ => (u:ℝ)) (second_moment P (Finset.range H))
    simp only [Nat.cast_sum,Nat.cast_pow] at eq
    apply eq.trans_le
    have bound := Finset.sum_le_sum (s := Finset.range H)
      (fun i _ => conditioned_product P pr i H)
    simpa only [cv,bw,Finset.sum_const,nsmul_eq_mul,Finset.card_range] using bound
  change (∑ a, (X a-(H:ℝ)*V)^2) ≤ (H:ℝ)*B
  have expand (a : Assignment P) : (X a-(H:ℝ)*V)^2 =
      (X a)^2-(2*H*V)*X a+((H:ℝ)*V)^2 := by ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,first,
    Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  change _ - _ + A*((H:ℝ)*V)^2 ≤ _
  calc
    _ ≤ (H:ℝ)*((H:ℝ)*(V*B)+B)-(2*H*V)*((H:ℝ)*B)+A*((H:ℝ)*V)^2 := by linarith
    _ = _ := by linear_combination (H:ℝ)^2*V*AB

/-- A full cover misses zero positions and therefore contributes the
square of the mean to the unnormalised variance. -/
theorem cover_count_bound (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (H : ℕ) :
    let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
    ((covers P (Finset.range H)).card:ℝ)*((H:ℝ)*V)^2 ≤
      (H:ℝ)*∏ p ∈ P, ((p:ℝ)-1) := by
  classical
  let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
  let S := Finset.range H
  apply le_trans (b := ∑ a : Assignment P, (((misses P S a).card:ℝ)-H*V)^2) _ (variance_bound P pr H)
  calc
    _ = ∑ _a ∈ covers P S, ((H:ℝ)*V)^2 := by simp [S,V]
    _ = ∑ a ∈ covers P S, (((misses P S a).card:ℝ)-H*V)^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      have empty : misses P S a=∅ := (Finset.mem_filter.mp ha).2
      simp [empty]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => sq_nonneg _)

end Variance687

#print axioms Variance687.pair_choices
#print axioms Variance687.conditioned_count
#print axioms Variance687.conditioned_product
#print axioms Variance687.second_moment
#print axioms Variance687.variance_bound
#print axioms Variance687.cover_count_bound
