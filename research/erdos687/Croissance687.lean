import Bords687
import Comptage687
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Combinatorics.Pigeonhole

/-! An elementary construction of covers of every fixed linear length. -/
namespace Croissance687
open Filter

def remainder (T Q : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  T.filter fun n => ∀ p ∈ Q, n%p ≠ a p%p

noncomputable def density (Q : Finset ℕ) : ℝ := ∏ p ∈ Q, (1-(1:ℝ)/p)

private theorem factor_nonneg {p : ℕ} (hp : 0 < p) : 0 ≤ 1-(1:ℝ)/p := by
  have h : (1:ℝ) ≤ p := by exact_mod_cast hp
  exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr h)

/-- On any finite set there is a choice of classes removing at least the
    expected fraction of its elements. -/
theorem thin (Q T : Finset ℕ) (pos : ∀ p ∈ Q, 0 < p) :
    ∃ a, ((remainder T Q a).card:ℝ) ≤ T.card*density Q := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,by simp [remainder,density]⟩
  | @insert p Q fresh ih =>
    have hp := pos p (Finset.mem_insert_self ..)
    have hpR : (0:ℝ) < p := by exact_mod_cast hp
    obtain ⟨a,ha⟩ := ih (fun q h => pos q (Finset.mem_insert_of_mem h))
    let U := remainder T Q a
    let f := fun n : ℕ => n%p
    have maps : ∀ n ∈ U, f n ∈ Finset.range p := fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp)
    obtain ⟨r,hr,hit⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (b := (U.card:ℝ)/p) maps (Finset.nonempty_range_iff.mpr (by omega))
      (by rw [Finset.card_range,nsmul_eq_mul]; exact le_of_eq (by field_simp))
    let b := Function.update a p r
    have eq : remainder T (insert p Q) b = U.filter (fun n => f n ≠ r) := by
      have old (q : ℕ) (hq : q ∈ Q) : b q = a q :=
        Function.update_of_ne (ne_of_mem_of_not_mem hq fresh) r a
      have curr : b p = r := Function.update_self ..
      ext n
      simp (config := {contextual := true}) only [remainder,U,Finset.mem_filter,
        Finset.mem_insert,forall_eq_or_imp,old,curr,Nat.mod_eq_of_lt (Finset.mem_range.mp hr),f]
      tauto
    have hsum := Finset.card_filter_add_card_filter_not (s := U) (p := fun n => f n = r)
    have hs : ((U.filter fun n => f n = r).card:ℝ) +
        ((U.filter fun n => f n ≠ r).card:ℝ) = U.card := by exact_mod_cast hsum
    refine ⟨b,?_⟩
    rw [eq]
    calc
      _ ≤ (U.card:ℝ)*(1-1/p) := by
        rw [div_eq_mul_inv] at hit
        simp only [one_div]
        nlinarith
      _ ≤ (T.card*density Q)*(1-1/p) := mul_le_mul_of_nonneg_right ha (factor_nonneg hp)
      _ = _ := by simp [density,Finset.prod_insert fresh]; ring

private theorem large_sum (B j : ℕ) :
    ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ B < p) ∧
      (j:ℝ)/2 ≤ ∑ p ∈ Q, (1:ℝ)/p := by
  induction j with
  | zero => exact ⟨∅,by simp,by simp⟩
  | succ j ih =>
    obtain ⟨Q,hQ,hs⟩ := ih
    let k := max B (Q.sup id)+1
    let R := (4^(k.primesBelow.card+1)).succ.primesBelow \ k.primesBelow
    have hr : ∀ p ∈ R, p.Prime ∧ k ≤ p := by
      intro p hp
      obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
      have prime := Nat.prime_of_mem_primesBelow hin
      exact ⟨prime,by simpa [Nat.primesBelow,prime] using hout⟩
    have dis : Disjoint Q R := Finset.disjoint_left.mpr (by
      intro p hq h
      have hle : p ≤ Q.sup id := Finset.le_sup (f := id) hq
      have hlo := (hr p h).2
      dsimp [k] at hlo
      omega)
    refine ⟨Q ∪ R,?_,?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact hQ p h
      · obtain ⟨prime,lo⟩ := hr p h
        exact ⟨prime,by dsimp [k] at lo; omega⟩
    · rw [Finset.sum_union dis,Nat.cast_succ]
      linarith [show 1/2 ≤ ∑ p ∈ R, (1:ℝ)/p from one_half_le_sum_primes_ge_one_div k]

private theorem density_sum (Q : Finset ℕ) (pos : ∀ p ∈ Q, 0 < p) :
    density Q * (1+∑ p ∈ Q, (1:ℝ)/p) ≤ 1 := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp [density]
  | @insert p Q fresh ih =>
    have hp := pos p (Finset.mem_insert_self ..)
    have old : ∀ q ∈ Q, 0 < q := fun q h => pos q (Finset.mem_insert_of_mem h)
    have hd : 0 ≤ density Q := Finset.prod_nonneg fun q h => factor_nonneg (old q h)
    have hu : 0 ≤ (1:ℝ)/p := by positivity
    have hs : 0 ≤ ∑ q ∈ Q, (1:ℝ)/q := Finset.sum_nonneg fun _ _ => by positivity
    specialize ih old
    have d : density (insert p Q) = (1-1/(p:ℝ))*density Q := Finset.prod_insert fresh
    rw [d,Finset.sum_insert fresh,mul_assoc (1-1/(p:ℝ))]
    calc
      _ = density Q*((1-1/p)*(1+(1/p+∑ q ∈ Q, (1:ℝ)/q))) := by ring
      _ ≤ density Q*(1+∑ q ∈ Q, (1:ℝ)/q) := by
        apply mul_le_mul_of_nonneg_left _ hd
        nlinarith [mul_nonneg hu hs,sq_nonneg ((1:ℝ)/p)]
      _ ≤ _ := ih

theorem small_density (B : ℕ) : ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ B < p) ∧
    density Q * (16*B:ℝ) ≤ 1 := by
  obtain ⟨Q,hQ,hs⟩ := large_sum B (32*B)
  have hd : 0 ≤ density Q := Finset.prod_nonneg fun p h => factor_nonneg (hQ p h).1.pos
  refine ⟨Q,hQ,le_trans (mul_le_mul_of_nonneg_left ?_ hd) (density_sum Q fun p h => (hQ p h).1.pos)⟩
  push_cast at hs
  linarith

/-- Outside the fixed smooth numbers, a composite at most Bt has a prime
    divisor at most t outside the reserved set Q. -/
theorem smooth_or_prime {B t y n : ℕ} {Q : Finset ℕ} (hBt : B ≤ t)
    (bounds : ∀ p ∈ Q, B < p ∧ p < y) (hn : 1 ≤ n) (hN : n ≤ B*t)
    (avoid : ∀ p ∈ t.primesLE, p ∉ Q → ¬ p ∣ n) :
    n ∈ (B*t).smoothNumbersUpTo y ∪ (B*t).primesLE := by
  by_cases hs : n ∈ Nat.smoothNumbers y
  · exact Finset.mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨hN,hs⟩)
  rw [Nat.mem_smoothNumbers'] at hs
  push Not at hs
  obtain ⟨q,prime,dvd,lo⟩ := hs
  have out : q ∉ Q := fun h => (bounds q h).2.not_ge lo
  have big : t < q := by
    by_contra! h
    exact avoid q (Nat.mem_primesLE.mpr ⟨h,prime⟩) out dvd
  obtain ⟨m,hm⟩ := dvd
  have bound : m ≤ B := by
    by_contra! h
    have lt := Nat.mul_lt_mul_of_lt_of_le big h.le (by omega : 0 < m)
    nlinarith [hm]
  have one : m = 1 := by
    by_contra h
    have pm := Nat.minFac_prime h
    have mpos : 0 < m := by
      cases m with
      | zero => simp at hm; omega
      | succ _ => omega
    have small := (Nat.minFac_le mpos).trans bound
    exact avoid m.minFac (Nat.mem_primesLE.mpr ⟨small.trans hBt,pm⟩)
      (fun H => (bounds _ H).1.not_ge small) (hm ▸ dvd_mul_of_dvd_right (Nat.minFac_dvd m) q)
  exact Finset.mem_union_right _ (Nat.mem_primesLE.mpr ⟨hN,by simpa [hm,one] using prime⟩)

theorem prime_supply {t : ℕ} (ht : 128 ≤ t) :
    8*(t:ℝ)/Real.log t ≤ (((128*t).primesLE \ t.primesLE).card:ℝ) := by
  let n := 128*t
  have ht' : (128:ℝ) ≤ t := by exact_mod_cast ht
  have hn : (128:ℝ) ≤ n := by dsimp [n]; push_cast; linarith
  have hln := Real.log_pos (show (1:ℝ) < n by linarith)
  have hlt := Real.log_pos (show (1:ℝ) < t by linarith)
  have hr := Real.sqrt_pos.mpr (show (0:ℝ) < n+1 by positivity)
  have lr := Real.log_le_sub_one_of_pos hr
  rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ n+1)] at lr
  have hl : Real.log ((n:ℝ)+1) ≤ n/4 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ n+1 by positivity),
      mul_nonneg (show (0:ℝ) ≤ n-128 by linarith) (show (0:ℝ) ≤ n by positivity),
      sq_nonneg (Real.sqrt ((n:ℝ)+1)-8)]
  have lb : (n:ℝ)/(4*Real.log n) ≤ Nat.primeCounting n := by
    refine le_trans ?_ (Chebyshev.pi_ge n)
    rw [show (n:ℝ)/(4*Real.log n) = (n/4)/Real.log n by ring]
    apply div_le_div_of_nonneg_right _ hln.le
    nlinarith [mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg (α := ℝ) n)]
  have ld : Real.log n ≤ 2*Real.log t := by
    have e : (n:ℝ) = 128*(t:ℝ) := by simp [n]
    rw [e,Real.log_mul (by norm_num) (by positivity)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 128) ht']
  have total : 16*(t:ℝ)/Real.log t ≤ Nat.primeCounting n := by
    apply le_trans _ lb
    apply (div_le_div_iff₀ hlt (by positivity)).mpr
    have e : (n:ℝ) = 128*(t:ℝ) := by simp [n]
    rw [e] at ld ⊢
    nlinarith [mul_le_mul_of_nonneg_left ld (Nat.cast_nonneg (α := ℝ) t)]
  have subset : t.primesLE ⊆ n.primesLE := by
    intro p hp
    obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [n]; omega,pr⟩
  have hc := Finset.card_le_card subset
  change _ ≤ ((n.primesLE \ t.primesLE).card:ℝ)
  rw [Finset.card_sdiff_of_subset subset,Nat.cast_sub hc]
  simp only [Nat.primesLE_card_eq_primeCounting]
  have upper := Comptage687.prime_count_eight (x := t) (by omega)
  calc
    8*(t:ℝ)/Real.log t = 16*t/Real.log t - 8*t/Real.log t := by ring
    _ ≤ _ := sub_le_sub total upper

private theorem smooth_cost (B y : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ t : ℕ in atTop, (((B*t).smoothNumbersUpTo y).card:ℝ) ≤ B*t/Real.log t := by
  let C : ℝ := 2^y.primesBelow.card
  have hc : 0 < C := by dsimp [C]; positivity
  have slow := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).bound (inv_pos.mpr hc)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually slow]
    with t ht hslow
  have ht0 : (0:ℝ) ≤ t := by positivity
  have hl := Real.log_pos (show (1:ℝ) < t by exact_mod_cast ht)
  have hs : Real.log t ≤ C⁻¹*Real.sqrt t := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hl.le,← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hslow
  have hn : ((B*t).sqrt:ℝ)^2 ≤ (B:ℝ)*t := by exact_mod_cast Nat.sqrt_le' (B*t)
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have root : ((B*t).sqrt:ℝ) ≤ B*Real.sqrt t := by
    have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ (B:ℝ)*t by positivity)
    have sq := Real.sq_sqrt ht0
    have eq : ((B:ℝ)*Real.sqrt t)^2 = B^2*(t:ℝ) := by rw [mul_pow,sq]
    nlinarith [show 0 ≤ (B:ℝ)*Real.sqrt t by positivity]
  have hcl : C*Real.log t ≤ Real.sqrt t := by
    calc _ ≤ C*(C⁻¹*Real.sqrt t) := mul_le_mul_of_nonneg_left hs hc.le
         _ = _ := by field_simp
  have initial : (((B*t).smoothNumbersUpTo y).card:ℝ) ≤ C*((B*t).sqrt:ℝ) := by
    dsimp [C]
    exact_mod_cast Nat.smoothNumbersUpTo_card_le (B*t) y
  apply initial.trans
  apply (le_div_iff₀ hl).mpr
  calc
    _ = ((B*t).sqrt:ℝ)*(C*Real.log t) := by ring
    _ ≤ ((B:ℝ)*Real.sqrt t)*Real.sqrt t :=
      mul_le_mul root hcl (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc,Real.mul_self_sqrt ht0]

/-- For every fixed multiplier B, all sufficiently large t admit a cover
    of [1,Bt] using one class for every prime up to 128t. -/
theorem fixed_multiplier (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ t : ℕ in atTop, Green46.IsCoveredByResidues (128*t) (B*t) := by
  classical
  obtain ⟨Q,hQ,hs⟩ := small_density B
  let y := Q.sup id+1
  filter_upwards [smooth_cost B y hB,eventually_ge_atTop (max 128 (max y B))]
    with t smooth ht
  have htB : B ≤ t := by omega
  have ht2 : 2 ≤ t := by omega
  have ht' : (1:ℝ) < t := by exact_mod_cast ht2
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have logt := Real.log_pos ht'
  have cmp : (t:ℝ) ≤ (B:ℝ)*t := by simpa using mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) t)
  have hbt : 2 ≤ B*t := by nlinarith
  let T := (B*t).smoothNumbersUpTo y ∪ (B*t).primesLE
  have Qbound : ∀ q ∈ Q, q < y := fun q h => Nat.lt_succ_of_le (Finset.le_sup (f := id) h)
  have primeCost : (((B*t).primesLE).card:ℝ) ≤ 8*(B*t:ℝ)/Real.log t := by
    rw [Nat.primesLE_card_eq_primeCounting]
    have h := Comptage687.prime_count_eight hbt
    push_cast at h
    exact h.trans (div_le_div_of_nonneg_left (by positivity) logt (Real.log_le_log (by positivity) cmp))
  have cost : (T.card:ℝ) ≤ 9*(B*t:ℝ)/Real.log t := by
    have h : (T.card:ℝ) ≤ ((B*t).smoothNumbersUpTo y).card + (((B*t).primesLE).card:ℝ) := by
      exact_mod_cast Finset.card_union_le ((B*t).smoothNumbersUpTo y) ((B*t).primesLE)
    exact h.trans ((add_le_add smooth primeCost).trans_eq (by ring))
  obtain ⟨a,ha⟩ := thin Q T (fun p h => (hQ p h).1.pos)
  let b := fun p => if p ∈ Q then a p else 0
  apply Bords687.finish_singletons (show t ≤ 128*t by omega) b
  have sub : Transfert687.survivors t (B*t) b ⊆ remainder T Q a := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
    apply Finset.mem_filter.mpr
    constructor
    · apply smooth_or_prime htB (fun p h => ⟨(hQ p h).2,Qbound p h⟩) lo up
      intro p hp out dvd
      exact avoid p hp (by simp [b,out,Nat.mod_eq_zero_of_dvd dvd])
    · intro p hp
      have le := Qbound p hp
      simpa [b,hp] using avoid p (Nat.mem_primesLE.mpr ⟨by omega,(hQ p hp).1⟩)
  have hd : 0 ≤ density Q := Finset.prod_nonneg fun p h => factor_nonneg (hQ p h).1.pos
  have c := mul_le_mul_of_nonneg_right cost hd
  have lim : 9*((B:ℝ)*t)/Real.log t*density Q ≤ 8*t/Real.log t := by
    have a : density Q * (9*B:ℝ) ≤ 8 := by
      nlinarith [mul_nonneg hd (Nat.cast_nonneg (α := ℝ) B)]
    have b := mul_le_mul_of_nonneg_right a (show 0 ≤ (t:ℝ)/Real.log t by positivity)
    calc
      _ = density Q*(9*(B:ℝ))*(t/Real.log t) := by ring
      _ ≤ 8*(t/Real.log t) := b
      _ = _ := by ring
  have cap := ha.trans (c.trans (lim.trans (prime_supply (by omega : 128 ≤ t))))
  exact (Finset.card_le_card sub).trans (by exact_mod_cast cap)

/-- The ratio Y(x)/x tends to infinity along every natural x. -/
theorem superlinear : Tendsto (fun x : ℕ => (Erdos687.Y x:ℝ)/x) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  obtain ⟨K,hK⟩ := exists_nat_gt (max 1 k)
  have kpos : 0 < K := by exact_mod_cast (show (0:ℝ) < K by linarith [le_max_left (1:ℝ) k])
  obtain ⟨t0,ht⟩ := eventually_atTop.mp (fixed_multiplier (256*K) (by omega))
  filter_upwards [eventually_ge_atTop (128*(t0+1))] with x hx
  let t := x/128
  have hxt : x ≤ 256*t := by dsimp [t]; omega
  have htx : 128*t ≤ x := by dsimp [t]; omega
  obtain ⟨a,cover⟩ := ht t (by dsimp [t]; omega)
  have cov : Green46.IsCoveredByResidues x ((256*K)*t) := by
    refine ⟨a,?_⟩
    intro n hn
    obtain ⟨p,le,pr,hit⟩ := cover n hn
    exact ⟨p,le.trans htx,pr,hit⟩
  have hxpos : (0:ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have cap := Transfert687.le_Y_of_covered cov
  have natbound : K*x ≤ Erdos687.Y x := by
    nlinarith [Nat.mul_le_mul_left K hxt]
  have realbound : (K:ℝ)*x ≤ Erdos687.Y x := by exact_mod_cast natbound
  exact (le_div_iff₀ hxpos).mpr ((mul_le_mul_of_nonneg_right
    (le_trans (le_max_right (1:ℝ) k) hK.le) hxpos.le).trans realbound)

end Croissance687
