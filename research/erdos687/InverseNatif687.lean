import Mathlib
import BorneNative687

/-! Inverse almost-cover comparison. The primorial inequality is from the pinned formal-conjectures catalog. The elementary prime estimates are from the pinned OpenAI Improved Long Gaps Between Primes source. Both sources are under Apache-2.0. -/

open scoped Asymptotics BigOperators

namespace Erdos687

theorem lt_primorial_of_isCoveredByResidues {x y : ℕ} (h : Green46.IsCoveredByResidues x y) :
    y < primorial x := by
  obtain ⟨a, ha⟩ := h
  refine lt_of_not_ge fun hy ↦ ?_
  let t := (Finset.range (x + 1)).filter Nat.Prime
  have hs : ∀ p ∈ t, (fun p : ℕ ↦ p) p ≠ 0 := fun p hp ↦ (Finset.mem_filter.1 hp).2.ne_zero
  have pp : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime fun p : ℕ ↦ p) :=
    fun p hp q hq hpq ↦
      (Nat.coprime_primes (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2).2 hpq
  -- By the Chinese remainder theorem, `k ≡ a p + 1 (mod p)` for every prime `p ≤ x`.
  let k := Nat.chineseRemainderOfFinset (fun p ↦ a p + 1) (fun p ↦ p) t hs pp
  have hk : (k : ℕ) < primorial x := Nat.chineseRemainderOfFinset_lt_prod _ _ hs pp
  -- Shift `k` into `[1, primorial x]` without changing its residues.
  obtain ⟨m, hm1, hmP, hmk⟩ :
      ∃ m, 1 ≤ m ∧ m ≤ primorial x ∧ ∀ p ∈ t, m ≡ k [MOD p] := by
    by_cases h0 : (k : ℕ) = 0
    · refine ⟨primorial x, primorial_pos x, le_rfl, fun p hp ↦ ?_⟩
      have hp' := Finset.mem_filter.1 hp
      rw [h0]
      exact Nat.modEq_zero_iff_dvd.2
        (hp'.2.dvd_primorial_iff.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp'.1)))
    · exact ⟨k, Nat.one_le_iff_ne_zero.2 h0, hk.le, fun p _ ↦ Nat.ModEq.refl _⟩
  obtain ⟨p, hpx, hp, hpm⟩ := ha m (Finset.mem_Icc.2 ⟨hm1, hmP.trans hy⟩)
  have hpt : p ∈ t := Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hpx), hp⟩
  have h1 : a p ≡ a p + 1 [MOD p] := hpm.symm.trans ((hmk p hpt).trans (k.2 p hpt))
  have hd : p ∣ 1 := by simpa using (Nat.modEq_iff_dvd' (Nat.le_add_right (a p) 1)).1 h1
  exact hp.not_dvd_one hd

end Erdos687

namespace Transfert687

theorem le_Y_of_covered {x N : ℕ} (h : Green46.IsCoveredByResidues x N) : N ≤ Erdos687.Y x :=
  le_csSup (show BddAbove {y | Green46.IsCoveredByResidues x y} from
    ⟨primorial x, fun _ hy => (Erdos687.lt_primorial_of_isCoveredByResidues hy).le⟩) h

end Transfert687

namespace Extension687

open Transfert687 Progressions687

theorem assign_images (S P : Finset ℕ) (f : ℕ → ℕ) (h : S.card ≤ P.card) :
    ∃ r : ℕ → ℕ, ∀ i ∈ S, ∃ p ∈ P, r p = f i := by
  classical
  obtain ⟨e⟩ : Nonempty (↥S ↪ ↥P) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  let r (p : ℕ) := if hm : ∃ j : S, (e j).val = p then f (Classical.choose hm).val else 0
  refine ⟨r,?_⟩
  intro i hi
  let j : S := ⟨i,hi⟩
  have ex : ∃ k : S, (e k).val = (e j).val := ⟨j,rfl⟩
  have eqn : Classical.choose ex = j := e.injective (Subtype.ext (Classical.choose_spec ex))
  exact ⟨(e j).val,(e j).property,by simp only [r,dif_pos ex,eqn]; rfl⟩

def Completes (S P : Finset ℕ) := ∃ a : ℕ → ℕ, ∀ i ∈ S, ∃ p ∈ P, i%p = a p%p

theorem completes_of_card {S P : Finset ℕ} (h : S.card ≤ P.card) : Completes S P := by
  obtain ⟨r,hr⟩ := assign_images S P id h
  refine ⟨r,?_⟩
  intro i hi
  obtain ⟨p,hp,eqn⟩ := hr i hi
  exact ⟨p,hp,by simp [eqn]⟩

theorem optimal_cover (z : ℕ) : Green46.IsCoveredByResidues z (Erdos687.Y z) := by
  have nonempty : {n : ℕ | Green46.IsCoveredByResidues z n}.Nonempty :=
    ⟨0,fun _ => 0,by simp⟩
  have bounded : BddAbove {n : ℕ | Green46.IsCoveredByResidues z n} :=
    ⟨primorial z,fun _ hn => (Erdos687.lt_primorial_of_isCoveredByResidues hn).le⟩
  exact Nat.sSup_mem nonempty bounded

end Extension687

namespace Bords687

open Extension687 Transfert687 Progressions687

theorem finish_singletons {x z N : ℕ} (hzx : z ≤ x) (a : ℕ → ℕ)
    (cap : (survivors z N a).card ≤ (x.primesLE \ z.primesLE).card) :
    Green46.IsCoveredByResidues x N := by
  classical
  obtain ⟨r,hr⟩ := completes_of_card cap
  let b (p : ℕ) := if p ≤ z then a p else r p
  refine ⟨b,?_⟩
  intro n hn
  by_cases live : n ∈ survivors z N a
  · obtain ⟨p,hp,hit⟩ := hr n live
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hin
    have big : ¬p ≤ z := fun h => hout (Nat.mem_primesLE.mpr ⟨h,prime⟩)
    exact ⟨p,le,prime,by simpa [b,big,Nat.ModEq] using hit⟩
  · have cl : ¬∀ p ∈ z.primesLE, n%p ≠ a p%p := fun h => live (Finset.mem_filter.mpr ⟨hn,h⟩)
    push Not at cl
    obtain ⟨p,hp,hit⟩ := cl
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact ⟨p,le.trans hzx,prime,by simpa [b,le,Nat.ModEq] using hit⟩

end Bords687

namespace Comptage687

theorem prime_count_eight {x : ℕ} (hx : 2 ≤ x) :
    (Nat.primeCounting x : ℝ) ≤ 8 * (x : ℝ) / Real.log x := by
  have h1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hp := Chebyshev.pi_le_log4_mul_div h1
  rw [Nat.floor_natCast, Real.log_sqrt (Nat.cast_nonneg x)] at hp
  have hl := Real.log_pos h1
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hterm : Real.log 4 * (x:ℝ) / (Real.log x / 2) ≤ 6 * x / Real.log x := by
    rw [div_div_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hl).2
    nlinarith [mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α := ℝ) x)]
  have hs := Real.sqrt_pos.2 (by positivity : (0:ℝ) < x)
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    linarith [Real.log_le_sub_one_of_pos hs, Real.log_sqrt (Nat.cast_nonneg x : (0:ℝ) ≤ x)]
  have hroot : Real.sqrt x ≤ 2 * x / Real.log x := by
    apply (le_div_iff₀ hl).2
    nlinarith [mul_le_mul_of_nonneg_left hlog hs.le, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) x)]
  calc
    _ ≤ _ := hp
    _ ≤ 6 * x / Real.log x + 2 * x / Real.log x := add_le_add hterm hroot
    _ = _ := by ring

end Comptage687

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

/-- After zero classes outside Q and arbitrary classes inside Q, the
    only possible survivors are the thinned smooth numbers and primes. -/
theorem candidates {B t y : ℕ} (hBt : B ≤ t) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ B < p ∧ p < y ∧ p ≤ t) (a : ℕ → ℕ) :
    Transfert687.survivors t (B*t) (fun p => if p ∈ Q then a p else 0) ⊆
      remainder ((B*t).smoothNumbersUpTo y ∪ (B*t).primesLE) Q a := by
  intro n hn
  obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
  obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
  apply Finset.mem_filter.mpr
  constructor
  · apply smooth_or_prime hBt (fun p h => ⟨(hQ p h).2.1,(hQ p h).2.2.1⟩) lo up
    intro p hp out dvd
    exact avoid p hp (by simp [out,Nat.mod_eq_zero_of_dvd dvd])
  · intro p hp
    simpa [hp] using avoid p (Nat.mem_primesLE.mpr ⟨(hQ p hp).2.2.2,(hQ p hp).1⟩)

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
  have sub : Transfert687.survivors t (B*t) b ⊆ remainder T Q a :=
    candidates htB Q (fun p h => ⟨(hQ p h).1,(hQ p h).2,Qbound p h,by
      have le := Qbound p h; omega⟩) a
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


namespace LongGapsBetweenPrimes
noncomputable section

lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp =>
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹

def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖natPowerHom σ p‖ < 1 := by
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natPowerHom σ) hprime (N + 1)).2
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

theorem log_le_eulerProduct_one (N : ℕ) : Real.log N ≤ eulerProduct N 1 := by
  have h := sum_smooth_le_eulerProduct (N := N) (by norm_num : (0 : ℝ) < 1)
    (Finset.Icc 1 N) (fun n hn => Nat.mem_smoothNumbers_of_lt
      (by have := Finset.mem_Icc.mp hn; omega)
      (by have := Finset.mem_Icc.mp hn; omega))
  have hlog := log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at hlog
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlog
  simp only [Real.rpow_neg_one] at h
  exact hlog.trans h

theorem tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hexp : -σ < -1 := neg_lt_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num), Nat.cast_one, Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq] at htail
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexp)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_one] using htail

lemma eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ))
    ((N + 1).smoothNumbers) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  have hseries := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowerHom σ) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-σ)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by linarith)) (N + 1)).2
  change HasSum (fun n : (N + 1).smoothNumbers => (n.val : ℝ) ^ (-σ))
    (eulerProduct N σ) at hseries
  rw [hseries.tsum_eq] at ht
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add] at ht
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact ht.trans (tsum_succ_rpow_le hσ)

lemma euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hden : 0 < 1 - p ^ (-(1 + r)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  have hlog : 0 ≤ r * Real.log p := mul_nonneg hr (Real.log_pos hp1).le
  have hpow : 1 - p ^ (-r) ≤ r * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * -r)
    nlinarith
  rw [Real.rpow_neg_one, ← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  rw [← div_eq_inv_mul]
  calc
    (1 - p ^ (-(1 + r))) / (1 - p⁻¹) =
        1 + (1 - p ^ (-r)) / (p - 1) := by
      rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ 1 + (r * Real.log p) / (p - 1) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hpow hpm.le)
    _ ≤ 1 + 2 * r * Real.log p / p := by
      apply add_le_add le_rfl
      apply (div_le_div_iff₀ hpm hp0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hlog]
    _ ≤ Real.exp (2 * r * Real.log p / p) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * r * Real.log p / p)

theorem eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE,
        (1 - (p : ℝ) ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt)
          (by norm_num : -(1 : ℝ) < 0)).le
      · intro p hp
        exact euler_factor_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) hr
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

theorem eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ 2 * Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log N := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hcost : 2 * (Real.log N)⁻¹ * (∑ p ∈ N.primesLE, Real.log p / p) ≤ 6 := by
    calc
      _ ≤ 2 * (Real.log N)⁻¹ * (3 * Real.log N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 := by field_simp; norm_num
  have hzeta : eulerProduct N (1 + (Real.log N)⁻¹) ≤ 1 + Real.log N := by
    simpa using eulerProduct_le_zeta_bound
      (lt_add_of_pos_right 1 (inv_pos.mpr hlog)) N
  calc
    _ ≤ eulerProduct N (1 + (Real.log N)⁻¹) *
        Real.exp (2 * (Real.log N)⁻¹ * ∑ p ∈ N.primesLE, Real.log p / p) :=
      eulerProduct_comparison N (inv_nonneg.mpr hlog.le)
    _ ≤ (1 + Real.log N) * Real.exp 6 :=
      mul_le_mul hzeta (Real.exp_le_exp.mpr hcost) (Real.exp_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

def auxiliaryPrimes (Z Y : ℕ) : Finset ℕ := Y.primesLE \ Z.primesLE

lemma auxiliaryPrimes_prime {Z Y p : ℕ} (hp : p ∈ auxiliaryPrimes Z Y) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

lemma mem_auxiliaryPrimes {Z Y p : ℕ} :
    p ∈ auxiliaryPrimes Z Y ↔ p.Prime ∧ Z < p ∧ p ≤ Y := by
  simp only [auxiliaryPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or, not_le]
  tauto

lemma auxiliary_euler_factorization {Z Y : ℕ} (hZY : Z ≤ Y) (σ : ℝ) :
    (∏ p ∈ auxiliaryPrimes Z Y, (1 - (p : ℝ) ^ (-σ))⁻¹) * eulerProduct Z σ =
      eulerProduct Y σ := Finset.prod_sdiff (Nat.primesLE_mono hZY)

lemma greedy_product_le {W Z : ℕ} (hW : 2 ≤ W) (hWZ : W ≤ Z) :
    (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp 6 * (1 + Real.log W) / Real.log Z := by
  have hprod : 0 < ∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    simpa only [one_div] using sub_pos.mpr
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt))
  have hfactor := auxiliary_euler_factorization hWZ 1
  simp only [Real.rpow_neg_one] at hfactor
  rw [Finset.prod_inv_distrib, inv_mul_eq_div] at hfactor
  simp only [← one_div] at hfactor
  have hcancel := (div_eq_iff hprod.ne').mp hfactor
  have hlog : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) hprod.le
    _ = eulerProduct W 1 := (mul_comm _ _).trans hcancel.symm
    _ ≤ Real.exp 6 * (1 + Real.log W) := eulerProduct_one_le hW

end
end LongGapsBetweenPrimes


namespace Presque687

noncomputable def holes (x H : ℕ) : ℕ :=
  sInf (Set.range fun a : ℕ → ℕ => (Transfert687.survivors x H a).card)

theorem realizes (x H : ℕ) : ∃ a, (Transfert687.survivors x H a).card = holes x H :=
  Nat.sInf_mem (Set.range_nonempty _)

theorem holes_le (x H : ℕ) (a : ℕ → ℕ) : holes x H ≤ (Transfert687.survivors x H a).card :=
  Nat.sInf_le (Set.mem_range_self a)

end Presque687

namespace Moments687
open Filter LongGapsBetweenPrimes
open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

def Rough (W n : ℕ) : Prop := ∀ p ∈ W.primesLE, ¬ p ∣ n

/-- The upper sieve for one residue per prime also bounds rough
    multiples of any fixed divisor d. -/
theorem rough_multiples {W H d : ℕ} (hW : 2 ≤ W) (hd : 0 < d)
    (room : d*W^5 ≤ H) (S : Finset ℕ) (bound : ∀ n ∈ S, n ≤ H)
    (rough : ∀ n ∈ S, Rough W n) (divides : ∀ n ∈ S, d ∣ n) :
    (S.card:ℝ) ≤ 5*((H:ℝ)/d)/Real.log W := by
  let j := H/d+1
  let T := Progressions687.siftedIndices W j (fun _ => 0)
  have sub : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun n => n/d)
    · intro n hn
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (bound n hn))),?_⟩
      intro p hp e
      have pd : p ∣ n/d := Nat.dvd_of_mod_eq_zero (by simpa using e)
      exact rough n hn p hp (pd.trans (Nat.div_dvd_of_dvd (divides n hn)))
    · intro n hn m hm eq
      have e := congrArg (fun k => k*d) eq
      simpa only [Nat.div_mul_cancel (divides n hn),Nat.div_mul_cancel (divides m hm)] using e
  have sieve := SquarefreeHarmonic.cutoffSurvivors_le_log_bound j W (fun _ => 0)
    (show 1 ≤ W by omega) le_rfl
  rw [← CribleTransfert687.index_eq_cutoff] at sieve
  have lo : W^5 ≤ H/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using room)
  have lW := Real.log_pos (show (1:ℝ) < W by exact_mod_cast hW)
  have j1 : (1:ℝ) ≤ (H:ℝ)/d := by
    have h : 1 ≤ H/d := (Nat.one_le_pow _ _ (by omega : 0 < W)).trans lo
    exact (show (1:ℝ) ≤ (H/d:ℕ) by exact_mod_cast h).trans (Nat.cast_div_le ..)
  have js : (j:ℝ) ≤ 2*((H:ℝ)/d) := by
    have cast : ((H/d:ℕ):ℝ) ≤ (H:ℝ)/d := Nat.cast_div_le
    dsimp [j]; push_cast; linarith
  have r : (W:ℝ)^5 ≤ (H:ℝ)/d :=
    (show (W:ℝ)^5 ≤ (H/d:ℕ) by exact_mod_cast lo).trans (Nat.cast_div_le ..)
  have e : (W:ℝ)^4 ≤ ((H:ℝ)/d)/Real.log W := by
    apply (le_div_iff₀ lW).mpr
    calc
      _ ≤ (W:ℝ)^4*W := mul_le_mul_of_nonneg_left
        (by linarith [Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<W)]) (by positivity)
      _ = (W:ℝ)^5 := by ring
      _ ≤ _ := r
  have logle : Real.log (W:ℝ) ≤ Real.log ((W:ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith)
  have main := div_le_div_of_nonneg_left (show 0 ≤ 2*(j:ℝ) by positivity) lW logle
  have scale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left js (by norm_num : (0:ℝ) ≤ 2)) lW.le
  refine (show (S.card:ℝ) ≤ T.card by exact_mod_cast sub).trans (sieve.trans ?_)
  calc
    _ ≤ (2*(2*((H:ℝ)/d)))/Real.log W + ((H:ℝ)/d)/Real.log W := add_le_add (main.trans scale) e
    _ = _ := by ring

/-- A weighted sum over ordered pairs of distinct divisors. This version
    can be used for weights other than logarithms. -/
theorem pair_moment (S P : Finset ℕ) (w : ℕ → ℝ) {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (weight : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ L/2)
    (mass : ∀ n ∈ S, L ≤ ∑ p ∈ P, if p ∣ n then w p else 0)
    (caps : ∀ p ∈ P, ∀ q ∈ P, q ≠ p →
      ((S.filter (fun n => p ∣ n ∧ q ∣ n)).card:ℝ) ≤ D/(p*q:ℝ)) :
    (S.card:ℝ)*(L*(L/2)) ≤ D*(∑ p ∈ P, w p/p)^2 := by
  classical
  let v (n p : ℕ) := if p ∣ n then w p else 0
  have vp (n p : ℕ) (h : p ∈ P) : 0 ≤ v n p ∧ v n p ≤ L/2 := by
    dsimp [v]; split
    · exact weight p h
    · constructor <;> linarith
  have localMass (n : ℕ) (hn : n ∈ S) : L*(L/2) ≤
      ∑ p ∈ P, ∑ q ∈ P.erase p, v n p*v n q := by
    have total : L ≤ ∑ p ∈ P, v n p := mass n hn
    calc
      _ ≤ (∑ p ∈ P, v n p)*(L/2) := mul_le_mul_of_nonneg_right total (by positivity)
      _ = _ := Finset.sum_mul ..
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (vp n p hp).1
        linarith [Finset.sum_erase_add P (v n) hp,(vp n p hp).2]
  have pair (p q : ℕ) (hp : p ∈ P) (hq : q ∈ P.erase p) :
      (∑ n ∈ S, v n p*v n q) ≤ D*(w p/p)*(w q/q) := by
    obtain ⟨ne,hq⟩ := Finset.mem_erase.mp hq
    have bound := mul_le_mul_of_nonneg_right (caps p hp q hq ne)
      (mul_nonneg (weight p hp).1 (weight q hq).1)
    calc
      _ = ∑ n ∈ S, if p ∣ n ∧ q ∣ n then w p*w q else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases a : p ∣ n <;> by_cases b : q ∣ n <;> simp [v,a,b]
      _ = ((S.filter fun n => p ∣ n ∧ q ∣ n).card:ℝ)*(w p*w q) := by
        rw [← Finset.sum_filter]; simp [nsmul_eq_mul]
      _ ≤ _ := bound
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  calc
    _ = ∑ _n ∈ S, L*(L/2) := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum localMass
    _ = ∑ p ∈ P, ∑ n ∈ S, ∑ q ∈ P.erase p, v n p*v n q := Finset.sum_comm
    _ = ∑ p ∈ P, ∑ q ∈ P.erase p, ∑ n ∈ S, v n p*v n q :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, D*(w p/p)*(w q/q) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => pair p q hp hq
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, D*(w p/p)*(w q/q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset ..)
      intro q hq _
      exact mul_nonneg (mul_nonneg hD (div_nonneg (weight p hp).1 (by positivity)))
        (div_nonneg (weight q hq).1 (by positivity))
    _ = _ := by simp only [← Finset.mul_sum,← Finset.sum_mul]; ring

/-- The large squarefree part of a rough and smooth set has a
    second-moment saving in log Z / log H. -/
theorem rough_smooth_squarefree {W Z H : ℕ} (hW : 2 ≤ W) (hZ : 4 ≤ Z) (hH : 2 ≤ H)
    (room : Z^2*W^5 ≤ H) (scale : Real.log Z ≤ Real.log H/4)
    (S : Finset ℕ) (each : ∀ n ∈ S, 0 < n ∧ n ≤ H ∧ Squarefree n ∧ Rough W n ∧
      (∀ p ∈ n.primeFactors, p ≤ Z) ∧ Real.log H/2 ≤ Real.log n) :
    (S.card:ℝ) ≤ 160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2 := by
  have lw := Real.log_pos (show (1:ℝ) < W by exact_mod_cast hW)
  have lh := Real.log_pos (show (1:ℝ) < H by exact_mod_cast hH)
  have lz := Real.log_pos (show (1:ℝ) < Z by exact_mod_cast (show 1 < Z by omega))
  let D := 5*(H:ℝ)/Real.log W
  have bound := pair_moment S Z.primesLE (fun p => Real.log p)
    (L := Real.log H/2) (D := D) (by positivity) (by dsimp [D]; positivity)
  have w (p : ℕ) (hp : p ∈ Z.primesLE) : 0 ≤ Real.log (p:ℝ) ∧ Real.log p ≤ Real.log H/2/2 := by
    obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp hp
    have lo : (1:ℝ) ≤ p := by exact_mod_cast pr.one_le
    constructor
    · exact Real.log_nonneg lo
    · linarith [Real.log_le_log (by positivity : (0:ℝ) < p) (show (p:ℝ) ≤ Z by exact_mod_cast le)]
  have mass (n : ℕ) (hn : n ∈ S) :
      Real.log H/2 ≤ ∑ p ∈ Z.primesLE, if p ∣ n then Real.log (p:ℝ) else 0 := by
    obtain ⟨nz,_,sq,_,smooth,large⟩ := each n hn
    have eq : Z.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
      ext p
      simp only [Finset.mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
      exact ⟨fun h => ⟨h.1.2,h.2,nz.ne'⟩,fun h => ⟨⟨smooth p (Nat.mem_primeFactors.mpr h),h.1⟩,h.2.1⟩⟩
    rw [← Finset.sum_filter,eq,← Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr
      (Nat.mem_primeFactors.mp hp).1.ne_zero),← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree sq]
    exact large
  have cap (p : ℕ) (hp : p ∈ Z.primesLE) (q : ℕ) (hq : q ∈ Z.primesLE) (ne : q ≠ p) :
      ((S.filter fun n => p ∣ n ∧ q ∣ n).card:ℝ) ≤ D/(p*q:ℝ) := by
    obtain ⟨pZ,pp⟩ := Nat.mem_primesLE.mp hp
    obtain ⟨qZ,qp⟩ := Nat.mem_primesLE.mp hq
    have size : p*q ≤ Z^2 := by simpa [pow_two] using Nat.mul_le_mul pZ qZ
    have room' := (Nat.mul_le_mul_right (W^5) size).trans room
    have h := rough_multiples hW (Nat.mul_pos pp.pos qp.pos) room'
      (S.filter fun n => p ∣ n ∧ q ∣ n) (fun n hn => (each n (Finset.mem_filter.mp hn).1).2.1)
      (fun n hn => (each n (Finset.mem_filter.mp hn).1).2.2.2.1) (fun n hn => by
        obtain ⟨_,pd,qd⟩ := Finset.mem_filter.mp hn
        exact ((Nat.coprime_primes pp qp).mpr ne.symm).mul_dvd_of_dvd_of_dvd pd qd)
    refine h.trans_eq ?_
    dsimp [D]; push_cast; ring
  specialize bound w mass cap
  have sum := sum_prime_log_div_le (N := Z) (by omega)
  have s0 : 0 ≤ ∑ p ∈ Z.primesLE, Real.log (p:ℝ)/p :=
    Finset.sum_nonneg fun p h => div_nonneg (w p h).1 (by positivity)
  have log4 := Real.log_le_log (by norm_num : (0:ℝ) < 4) (show (4:ℝ) ≤ Z by exact_mod_cast hZ)
  have sq := pow_le_pow_left₀ s0 (by linarith : (∑ p ∈ Z.primesLE, Real.log (p:ℝ)/p) ≤ 2*Real.log Z) 2
  have final := bound.trans (mul_le_mul_of_nonneg_left sq (show 0 ≤ D by dsimp [D]; positivity))
  apply (le_of_mul_le_mul_right · (show 0 < (Real.log H)^2 by positivity))
  calc
    _ ≤ 8*(D*(2*Real.log Z)^2) := by nlinarith only [final]
    _ = _ := by dsimp [D]; field_simp; ring

/-- A set of exceptions with a square divisor above W has density at
    most 2/(W+1). -/
theorem square_errors {W H : ℕ} (S : Finset ℕ) (bound : ∀ n ∈ S, 0 < n ∧ n ≤ H)
    (bad : ∀ n ∈ S, ∃ d, W < d ∧ d*d ∣ n) :
    (S.card:ℝ) ≤ H*(2/((W:ℝ)+1)) := by
  classical
  let P := Finset.Ioo W (H+1)
  let T := fun d : ℕ => (Finset.Ioc 0 H).filter (fun n => d^2 ∣ n)
  have incl : S ⊆ P.biUnion T := by
    intro n hn
    obtain ⟨lo,up⟩ := bound n hn
    obtain ⟨d,big,dv⟩ := bad n hn
    have dle : d ≤ H := (Nat.le_of_dvd lo ((dvd_mul_right d d).trans dv)).trans up
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_Ioo.mpr ⟨big,by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lo,up⟩,by simpa [pow_two] using dv⟩⟩
  have count := (Finset.card_le_card incl).trans (Finset.card_biUnion_le)
  have one (d : ℕ) : ((T d).card:ℝ) ≤ H*((d:ℝ)^2)⁻¹ := by
    dsimp [T]
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have h : ((H/d^2:ℕ):ℝ) ≤ (H:ℝ)/(d^2:ℕ) := Nat.cast_div_le
    simpa [div_eq_mul_inv] using h
  calc
    _ ≤ ∑ d ∈ P, ((T d).card:ℝ) := by exact_mod_cast count
    _ ≤ ∑ d ∈ P, H*((d:ℝ)^2)⁻¹ := Finset.sum_le_sum fun d _ => one d
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) W (H+1)) (Nat.cast_nonneg H)

end Moments687


namespace Restes687
open Filter LongGapsBetweenPrimes Moments687 Presque687

noncomputable def roughSmooth (H W Z : ℕ) : Finset ℕ := by
  classical
  exact (H.smoothNumbersUpTo (Z+1)).filter (Rough W)

theorem thin_rough {B x W Z : ℕ} (hBW : B ≤ W) (hWZ : W ≤ Z) (hZx : Z ≤ x) :
    (holes x (B*x):ℝ) ≤ ((roughSmooth (B*x) W Z).card+((B*x).primesLE.card:ℝ))*
      Croissance687.density (auxiliaryPrimes W Z) := by
  classical
  let Q := auxiliaryPrimes W Z
  let H := B*x
  let A := roughSmooth H W Z
  let T := A ∪ H.primesLE
  have hQ (p : ℕ) (h : p ∈ Q) := mem_auxiliaryPrimes.mp h
  obtain ⟨a,ha⟩ := Croissance687.thin Q T (fun p h => (hQ p h).1.pos)
  let b := fun p => if p ∈ Q then a p else 0
  have bare := Croissance687.candidates (y := Z+1) (hBW.trans (hWZ.trans hZx)) Q (fun p h => by
    obtain ⟨pr,lo,up⟩ := hQ p h
    exact ⟨pr,by omega,by omega,up.trans hZx⟩) a
  have sub : Transfert687.survivors x H b ⊆ Croissance687.remainder T Q a := by
    intro n hn
    obtain ⟨cand,avoid⟩ := Finset.mem_filter.mp (bare hn)
    refine Finset.mem_filter.mpr ⟨?_,avoid⟩
    rcases Finset.mem_union.mp cand with smooth | prime
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr ⟨smooth,?_⟩
      intro p hp dv
      obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp hp
      have out : p ∉ Q := fun h => (hQ p h).2.1.not_ge le
      exact (Finset.mem_filter.mp hn).2 p (Nat.mem_primesLE.mpr ⟨le.trans (hWZ.trans hZx),pr⟩)
        (by simp [b,out,Nat.mod_eq_zero_of_dvd dv])
    · exact Finset.mem_union_right _ prime
  have nn : 0 ≤ Croissance687.density Q := by
    apply Finset.prod_nonneg
    intro p h
    have lo : (1:ℝ) ≤ p := by exact_mod_cast (hQ p h).1.one_le
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr lo)
  have h := (holes_le x H b).trans (Finset.card_le_card sub)
  refine (show (holes x H:ℝ) ≤ _ by exact_mod_cast h).trans (ha.trans ?_)
  apply mul_le_mul_of_nonneg_right _ nn
  exact_mod_cast Finset.card_union_le A H.primesLE

theorem smooth_total {H W Z : ℕ} (hH : 2 ≤ H) (hW : 4 ≤ W) (hWZ : W ≤ Z)
    (room : Z^2*W^5 ≤ H) (scale : Real.log Z ≤ Real.log H/4) (base : Real.log H ≤ W) :
    ((roughSmooth H W Z).card:ℝ) ≤ 4*((H:ℝ)/Real.log H) +
      160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2 := by
  classical
  let A := roughSmooth H W Z
  let E := A.filter (fun n => ¬Squarefree n)
  let G := A.filter (fun n => Squarefree n ∧ H.sqrt < n)
  have info (n : ℕ) (h : n ∈ A) :
      0 < n ∧ n ≤ H ∧ Rough W n ∧ ∀ p ∈ n.primeFactors, p ≤ Z := by
    obtain ⟨sm,rough⟩ := Finset.mem_filter.mp h
    obtain ⟨hi,smooth⟩ := Nat.mem_smoothNumbersUpTo.mp sm
    refine ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers smooth),hi,rough,?_⟩
    intro p hp
    obtain ⟨prime,dv,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.lt_succ_iff.mp (Nat.mem_smoothNumbers'.mp smooth p prime dv)
  have exc := square_errors (W := W) (H := H) E (fun n h => by
    have e := info n (Finset.mem_filter.mp h).1
    exact ⟨e.1,e.2.1⟩) (fun n h => by
    obtain ⟨hn,notSq⟩ := Finset.mem_filter.mp h
    rw [Nat.squarefree_iff_prime_squarefree] at notSq
    push Not at notSq
    obtain ⟨p,prime,dvd⟩ := notSq
    refine ⟨p,?_,dvd⟩
    by_contra! le
    exact (info n hn).2.2.1 p (Nat.mem_primesLE.mpr ⟨le,prime⟩) ((dvd_mul_right p p).trans dvd))
  have good := rough_smooth_squarefree (W := W) (Z := Z) (H := H) (by omega) (by omega)
    hH room scale G (fun n h => by
      obtain ⟨hn,sq,big⟩ := Finset.mem_filter.mp h
      obtain ⟨pos,up,rough,smooth⟩ := info n hn
      refine ⟨pos,up,sq,rough,smooth,?_⟩
      have hpow : (H:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast (Nat.sqrt_lt'.mp big).le
      have hlog := Real.log_le_log (show (0:ℝ) < H by positivity) hpow
      rw [Real.log_pow] at hlog
      norm_num at hlog
      linarith)
  have incl : A ⊆ (Finset.Icc 1 H.sqrt ∪ E) ∪ G := by
    intro n hn
    by_cases small : n ≤ H.sqrt
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨(info n hn).1,small⟩))
    by_cases sq : Squarefree n
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,sq,by omega⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,sq⟩))
  have cnt := (Finset.card_le_card incl).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have cnt' : (A.card:ℝ) ≤ (H.sqrt:ℝ)+E.card+G.card := by
    simp only [Nat.card_Icc] at cnt
    exact_mod_cast (by omega : A.card ≤ H.sqrt+E.card+G.card)
  have lh := Real.log_pos (show (1:ℝ) < H by exact_mod_cast hH)
  have sqrtle : (H.sqrt:ℝ) ≤ 2*((H:ℝ)/Real.log H) := by
    have sq : (H.sqrt:ℝ)^2 ≤ H := by exact_mod_cast Nat.sqrt_le' H
    have root := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) H)
    have rn := Real.sqrt_nonneg (H:ℝ)
    have rr : (H.sqrt:ℝ) ≤ Real.sqrt H := by nlinarith
    have lb := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show (0:ℝ) < H by positivity))
    rw [Real.log_sqrt (Nat.cast_nonneg H)] at lb
    rw [← mul_div_assoc]
    apply (le_div_iff₀ lh).mpr
    nlinarith [mul_le_mul_of_nonneg_right rr lh.le,mul_le_mul_of_nonneg_left lb rn]
  have ex : (E.card:ℝ) ≤ 2*((H:ℝ)/Real.log H) := by
    apply exc.trans
    calc
      _ ≤ H*(2/Real.log H) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) lh (by linarith)) (Nat.cast_nonneg H)
      _ = _ := by ring
  linarith

/-- The minimum exceptional fraction, normalized by H/log H, is governed
    by log W/log Z plus log Z/log H. -/
theorem band_estimate {B x W Z : ℕ} (hH : 2 ≤ B*x) (hW : 4 ≤ W)
    (hBW : B ≤ W) (hWZ : W ≤ Z) (hZx : Z ≤ x)
    (room : Z^2*W^5 ≤ B*x) (scale : Real.log Z ≤ Real.log (B*x:ℝ)/4)
    (base : Real.log (B*x:ℝ) ≤ W) :
    (holes x (B*x):ℝ) ≤ (B*x:ℝ)/Real.log (B*x:ℝ) *
      (400*Real.exp 6)*(Real.log W/Real.log Z + Real.log Z/Real.log (B*x:ℝ)) := by
  let H := B*x
  have cast : (H:ℝ) = (B:ℝ)*x := by simp [H]
  rw [← cast] at scale base ⊢
  have lH := Real.log_pos (show (1:ℝ) < H by exact_mod_cast hH)
  have lW : 1 ≤ Real.log (W:ℝ) := by
    have le := Real.log_le_log (by norm_num : (0:ℝ) < 4)
      (show (4:ℝ) ≤ W by exact_mod_cast hW)
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow] at le
    norm_num at le
    linarith [Real.log_two_gt_d9]
  have lZ := Real.log_pos (show (1:ℝ) < Z by exact_mod_cast (show 1 < Z by omega))
  have stock := smooth_total (H := H) hH hW hWZ room scale base
  have primes := Comptage687.prime_count_eight hH
  rw [← Nat.primesLE_card_eq_primeCounting] at primes
  have prod := greedy_product_le (by omega : 2 ≤ W) hWZ
  change Croissance687.density _ ≤ _ at prod
  have dp : 0 ≤ Croissance687.density (auxiliaryPrimes W Z) := by
    apply Finset.prod_nonneg
    intro p hp
    have le : (1:ℝ) ≤ p := by exact_mod_cast (mem_auxiliaryPrimes.mp hp).1.one_le
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr le)
  have cost : ((roughSmooth H W Z).card:ℝ)+H.primesLE.card ≤ 12*((H:ℝ)/Real.log H) +
      160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2 := by
    have add := add_le_add stock primes
    linarith [show 8*(H:ℝ)/Real.log H = 8*(H/Real.log H) by ring]
  have d : Croissance687.density (auxiliaryPrimes W Z) ≤ 2*Real.exp 6*Real.log W/Real.log Z := by
    refine prod.trans ((div_le_div_iff_of_pos_right lZ).mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_left lW (Real.exp_pos 6).le]
  have comb := (thin_rough hBW hWZ hZx).trans (mul_le_mul cost d dp (by positivity))
  refine comb.trans ?_
  have eq : (12*((H:ℝ)/Real.log H)+160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2)*
        (2*Real.exp 6*Real.log W/Real.log Z) =
      (H/Real.log H)*Real.exp 6*(24*(Real.log W/Real.log Z)+320*(Real.log Z/Real.log H)) := by
    field_simp [lZ.ne',lH.ne',show Real.log (W:ℝ) ≠ 0 by linarith]; ring
  rw [eq]
  have a : 0 ≤ Real.log W/Real.log Z := by positivity
  have b : 0 ≤ Real.log Z/Real.log H := by positivity
  have c : 0 ≤ (H/Real.log H)*Real.exp 6 := by positivity
  nlinarith [mul_nonneg c a,mul_nonneg c b]

end Restes687


namespace SousPuissance687
open Filter Presque687
open scoped Asymptotics

noncomputable def cut (a : ℝ) (H : ℕ) : ℕ := ⌊Real.exp (a*Real.log H)⌋₊

private theorem cutoff_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ H : ℕ in atTop, 4 ≤ cut a H ∧
      a*Real.log H/2 ≤ Real.log (cut a H) ∧ Real.log (cut a H) ≤ a*Real.log H ∧
      Real.log H ≤ (cut a H:ℝ) := by
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  have slow := Real.isLittleO_log_id_atTop.bound (show 0 < a/2 by positivity)
  filter_upwards [logs.eventually_ge_atTop (max 2 (8/a)),logs.eventually slow] with H hh hslow
  let L := Real.log (H:ℝ)
  change max 2 (8/a) ≤ L at hh
  have l2 := (le_max_left _ _).trans hh
  have al := (div_le_iff₀ ha).mp ((le_max_right _ _).trans hh)
  have big : 4 ≤ cut a H := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    (by change (4:ℝ) ≤ Real.exp (a*L); linarith [Real.add_one_le_exp (a*L)])
  have half : 2 ≤ Real.exp (a*L/2) := by linarith [Real.add_one_le_exp (a*L/2)]
  have square : Real.exp (a*L) = Real.exp (a*L/2)^2 := by
    rw [pow_two,← Real.exp_add,add_halves]
  have floor : Real.exp (a*L) < (cut a H:ℝ)+1 := Nat.lt_floor_add_one _
  have halfFloor : Real.exp (a*L/2) ≤ (cut a H:ℝ) := by nlinarith
  have hi : Real.log (cut a H) ≤ a*L := by
    calc _ ≤ Real.log (Real.exp (a*L)) := Real.log_le_log (by positivity) (Nat.floor_le (Real.exp_nonneg _))
         _ = _ := Real.log_exp _
  have slow' : Real.log L ≤ a*L/2 := by
    change ‖Real.log L‖ ≤ (a/2)*‖L‖ at hslow
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (by linarith : 0 ≤ L)] at hslow
    linarith
  refine ⟨big,?_,hi,?_⟩
  · calc a*L/2 = Real.log (Real.exp (a*L/2)) := (Real.log_exp _).symm
         _ ≤ _ := Real.log_le_log (Real.exp_pos _) halfFloor
  · calc L = Real.exp (Real.log L) := (Real.exp_log (by linarith)).symm
         _ ≤ _ := (Real.exp_le_exp.mpr slow').trans halfFloor

/-- The two logarithmic losses in the finite band estimate can be made
    arbitrarily small, uniformly for bounded or unbounded multipliers. -/
theorem almost_cover_along (X B : ℕ → ℕ) (xinf : Tendsto X atTop atTop) (one : ∀ᶠ x : ℕ in atTop, 1 ≤ B x)
    (small : (fun x : ℕ => Real.log (B x)) =o[atTop] (fun x : ℕ => Real.log (X x))) :
    (fun x : ℕ => (holes (X x) (B x*X x):ℝ)) =o[atTop]
      (fun x : ℕ => ((B x*X x:ℕ):ℝ)/Real.log (B x*X x:ℕ)) := by
  let H := fun i : ℕ => B i*X i
  have inf : Tendsto H atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [one,xinf.eventually_ge_atTop b] with i h hx
    exact hx.trans (by simpa [H] using Nat.mul_le_mul_right (X i) h)
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  let D : ℝ := 400*Real.exp 6
  have hD : 0 < D := by dsimp [D]; positivity
  let a : ℝ := min (1/8) (ε/(3*D))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have eighth : a ≤ 1/8 := min_le_left .. 
  have eps := (le_div_iff₀ (by positivity : 0 < 3*D)).mp (min_le_right (1/8:ℝ) (ε/(3*D)))
  change a*(3*D) ≤ ε at eps
  have aa : a^2 ≤ a := by nlinarith [mul_nonneg ha.le (show 0 ≤ 1-a by linarith)]
  have sumexp : 2*a+5*a^2 ≤ 1 := by nlinarith
  have band := small.bound (show 0 < a^2/2 by positivity)
  filter_upwards [one,band,xinf.eventually_ge_atTop (2:ℕ),inf.eventually (cutoff_bounds ha),
    inf.eventually (cutoff_bounds (sq_pos_of_pos ha))] with i hB hsmall hx hz hw
  let Z := cut a (H i)
  let W := cut (a^2) (H i)
  let L := Real.log (H i:ℝ)
  let Lx := Real.log ((X i):ℝ)
  change 4 ≤ Z ∧ a*L/2 ≤ Real.log Z ∧ Real.log Z ≤ a*L ∧ L ≤ (Z:ℝ) at hz
  change 4 ≤ W ∧ a^2*L/2 ≤ Real.log W ∧ Real.log W ≤ a^2*L ∧ L ≤ (W:ℝ) at hw
  obtain ⟨z4,zlo,zhi,_⟩ := hz
  obtain ⟨w4,wlo,whi,wbase⟩ := hw
  have xx := Real.log_pos (show (1:ℝ) < (X i) by exact_mod_cast hx)
  have hxH : (X i) ≤ H i := by simpa [H] using Nat.mul_le_mul_right (X i) hB
  have hn := hx.trans hxH
  have lpos : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < H i by omega))
  have xlo : Lx ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hxH)
  have bpos : (0:ℝ) < B i := by exact_mod_cast hB
  have blog : 0 ≤ Real.log (B i:ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  change ‖Real.log (B i:ℝ)‖ ≤ a^2/2*‖Lx‖ at hsmall
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg blog,abs_of_nonneg xx.le] at hsmall
  have bw : B i ≤ W := by
    have l := mul_le_mul_of_nonneg_left xlo (show 0 ≤ a^2/2 by positivity)
    exact_mod_cast (Real.log_le_log_iff bpos (by positivity : (0:ℝ) < W)).mp (by linarith)
  have wz : W ≤ Z := Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right aa lpos.le))
  have logH : L = Real.log (B i:ℝ)+Lx := by
    dsimp [L,H,Lx]; rw [Nat.cast_mul,Real.log_mul bpos.ne' (by positivity)]
  have xl : L ≤ 2*Lx := by
    have x0 : 0 ≤ Lx := xx.le
    nlinarith [mul_le_mul_of_nonneg_right (show a^2/2 ≤ 1 by linarith) x0]
  have zx : Z ≤ (X i) := by
    have bound : a*L ≤ Lx := by
      nlinarith [mul_le_mul_of_nonneg_right eighth lpos.le]
    exact_mod_cast (Real.log_le_log_iff (by positivity : (0:ℝ) < Z) (by positivity : (0:ℝ) < (X i))).mp
      (zhi.trans bound)
  have room : Z^2*W^5 ≤ H i := by
    have lhs : Real.log ((Z^2*W^5:ℕ):ℝ) = 2*Real.log Z+5*Real.log W := by
      push_cast; rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]; norm_num
    have cmp : Real.log ((Z^2*W^5:ℕ):ℝ) ≤ L := by
      rw [lhs]
      nlinarith [mul_le_mul_of_nonneg_right sumexp lpos.le]
    exact_mod_cast (Real.log_le_log_iff (by positivity : (0:ℝ) < (Z^2*W^5:ℕ))
      (by positivity : (0:ℝ) < H i)).mp cmp
  have scale : Real.log Z ≤ L/4 := by nlinarith [mul_le_mul_of_nonneg_right eighth lpos.le]
  have cast : (H i:ℝ) = (B i:ℝ)*(X i) := by simp [H]
  have bound := Restes687.band_estimate hn w4 bw wz zx room
    (by simpa [← cast,L] using scale) (by simpa [← cast,L] using wbase)
  rw [← cast] at bound
  have zpos := Real.log_pos (show (1:ℝ) < Z by exact_mod_cast (show 1 < Z by omega))
  have r₁ : Real.log W/Real.log Z ≤ 2*a := (div_le_iff₀ zpos).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left zlo (show 0 ≤ 2*a by positivity)])
  have r₂ : Real.log Z/L ≤ a := (div_le_iff₀ lpos).mpr zhi
  have coeff : D*(Real.log W/Real.log Z+Real.log Z/L) ≤ ε := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add r₁ r₂) hD.le]
  have nn : 0 ≤ (H i:ℝ)/L := div_nonneg (by positivity) lpos.le
  change ‖(holes (X i) (H i):ℝ)‖ ≤ ε*‖(H i:ℝ)/L‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg nn]
  calc
    _ ≤ _ := bound
    _ = (D*(Real.log W/Real.log Z+Real.log Z/L))*((H i:ℝ)/L) := by dsimp [D,L]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff nn

theorem almost_cover (B : ℕ → ℕ) (one : ∀ᶠ x : ℕ in atTop, 1 ≤ B x)
    (small : (fun x : ℕ => Real.log (B x)) =o[atTop] (fun x : ℕ => Real.log x)) :
    (fun x : ℕ => (holes x (B x*x):ℝ)) =o[atTop]
      (fun x : ℕ => ((B x*x:ℕ):ℝ)/Real.log (B x*x:ℕ)) :=
  almost_cover_along id B tendsto_id one small

theorem holes_mono {x h H : ℕ} (le : h ≤ H) : holes x h ≤ holes x H := by
  obtain ⟨a,ha⟩ := realizes x H
  rw [← ha]
  apply (holes_le x h a).trans (Finset.card_le_card ?_)
  intro n hn
  obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
  obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,up.trans le⟩,avoid⟩

/-- The interval need not be a multiple of x. The conclusion supplies
    actual residue classes for each x. -/
theorem arbitrary_length_along (X H : ℕ → ℕ) (xinf : Tendsto X atTop atTop) (large : ∀ᶠ x : ℕ in atTop, X x ≤ H x)
    (scale : (fun x : ℕ => Real.log (H x)-Real.log (X x)) =o[atTop] (fun x : ℕ => Real.log (X x))) :
    ∃ a : ℕ → ℕ → ℕ, (fun x => ((Transfert687.survivors (X x) (H x) (a x)).card:ℝ)) =o[atTop]
      (fun x => (H x:ℝ)/Real.log (H x)) := by
  let B := fun i => H i/X i+1
  have one : ∀ i, 1 ≤ B i := fun _ => Nat.succ_pos _
  have logInf := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)).comp xinf
  have compare (i : ℕ) (hx : 2 ≤ (X i)) (hle : (X i) ≤ H i) :
      H i ≤ B i*(X i) ∧ B i*(X i) ≤ 2*H i := by
    have up := Nat.div_mul_le_self (H i) (X i)
    have lo := (Nat.div_lt_iff_lt_mul (by omega : 0 < (X i))).mp (Nat.lt_succ_self (H i/(X i)))
    refine ⟨lo.le,?_⟩
    dsimp [B]; rw [Nat.add_mul]; omega
  have bsmall : (fun i : ℕ => Real.log (B i)) =o[atTop] (fun i : ℕ => Real.log (X i)) := by
    apply Asymptotics.isLittleO_iff.mpr
    intro ε he
    filter_upwards [large,xinf.eventually_ge_atTop (2:ℕ),scale.bound (half_pos he),
      logInf.eventually_ge_atTop (2*Real.log 2/ε)] with i hle hx hs hl
    have Lx := Real.log_pos (show (1:ℝ) < (X i) by exact_mod_cast hx)
    have hp : (0:ℝ) < H i := by exact_mod_cast (show 0 < H i by omega)
    have bp : 0 < (B i:ℝ) := by exact_mod_cast one i
    have logle := Real.log_le_log (show (0:ℝ) < (X i) by positivity) (show ((X i):ℝ) ≤ H i by exact_mod_cast hle)
    have cc : (B i:ℝ)*(X i) ≤ 2*(H i:ℝ) := by exact_mod_cast (compare i hx hle).2
    have sum := Real.log_le_log (show 0 < (B i:ℝ)*(X i) by positivity) cc
    rw [Real.log_mul bp.ne' (by positivity),Real.log_mul (by norm_num) hp.ne'] at sum
    change 2*Real.log 2/ε ≤ Real.log ((X i):ℝ) at hl
    have lim := (div_le_iff₀ he).mp hl
    change ‖Real.log (H i)-Real.log (X i)‖ ≤ ε/2*‖Real.log ((X i):ℝ)‖ at hs
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr logle),abs_of_nonneg Lx.le] at hs
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast one i)),
      abs_of_nonneg Lx.le]
    linarith
  have near := almost_cover_along X B xinf (Eventually.of_forall one) bsmall
  choose a ha using fun i => realizes (X i) (H i)
  refine ⟨a,Asymptotics.isLittleO_iff.mpr ?_⟩
  intro ε he
  filter_upwards [large,xinf.eventually_ge_atTop (2:ℕ),near.bound (half_pos he)] with i hle hx hb
  obtain ⟨lo,up⟩ := compare i hx hle
  have lh := Real.log_pos (show (1:ℝ) < H i by exact_mod_cast (show 1 < H i by omega))
  have logs := Real.log_le_log (show (0:ℝ) < H i by exact_mod_cast (show 0 < H i by omega))
    (show (H i:ℝ) ≤ (B i*(X i):ℕ) by exact_mod_cast lo)
  have lr : 0 ≤ Real.log ((B i*(X i):ℕ):ℝ) := lh.le.trans logs
  have cb : ((B i*(X i):ℕ):ℝ)/Real.log (B i*(X i):ℕ) ≤ (2*(H i:ℝ))/Real.log (H i) :=
    (div_le_div_of_nonneg_left (by positivity) lh logs).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast up) lh.le)
  change ‖(holes (X i) (B i*(X i)):ℝ)‖ ≤ ε/2*‖((B i*(X i):ℕ):ℝ)/Real.log (B i*(X i):ℕ)‖ at hb
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by positivity) lr)] at hb
  have bound := (show (holes (X i) (H i):ℝ) ≤ holes (X i) (B i*(X i)) by exact_mod_cast holes_mono (x := (X i)) lo).trans
    (hb.trans (mul_le_mul_of_nonneg_left cb (half_pos he).le))
  rw [ha,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by positivity) lh.le)]
  exact bound.trans_eq (by ring)

theorem arbitrary_length (H : ℕ → ℕ) (large : ∀ᶠ x : ℕ in atTop, x ≤ H x)
    (scale : (fun x : ℕ => Real.log (H x)-Real.log x) =o[atTop] (fun x : ℕ => Real.log x)) :
    ∃ a : ℕ → ℕ → ℕ, (fun x => ((Transfert687.survivors x (H x) (a x)).card:ℝ)) =o[atTop]
      (fun x => (H x:ℝ)/Real.log (H x)) :=
  arbitrary_length_along id H tendsto_id large scale

end SousPuissance687


namespace Separation687
open Filter
open scoped Asymptotics

def SubpowerUpper : Prop := ∀ δ > (0:ℝ), (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
  (fun x : ℕ => (x:ℝ)^(1+δ))

theorem eventual_lower : ∀ᶠ x : ℕ in atTop, x ≤ Erdos687.Y x := by
  filter_upwards [Croissance687.superlinear.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)]
    with x h hx
  change 1 ≤ (Erdos687.Y x:ℝ)/x at h
  exact_mod_cast (one_le_div (by positivity)).mp h

theorem excess (upper : SubpowerUpper) :
    (fun x : ℕ => Real.log (Erdos687.Y x)-Real.log x) =o[atTop] (fun x : ℕ => Real.log x) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  obtain ⟨C,hC,bound⟩ := Asymptotics.isBigO_iff'.mp (upper (ε/2) (half_pos he))
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [bound,eventual_lower,eventually_ge_atTop (2:ℕ),logs.eventually_ge_atTop (2*Real.log C/ε)]
    with x h le hx hl
  have pos : (0:ℝ) < x := by positivity
  have yp : (0:ℝ) < Erdos687.Y x := by exact_mod_cast (show 0 < Erdos687.Y x by omega)
  have lx := Real.log_pos (show (1:ℝ) < x by exact_mod_cast hx)
  change ‖(Erdos687.Y x:ℝ)‖ ≤ C*‖(x:ℝ)^(1+ε/2)‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg yp.le,abs_of_nonneg (Real.rpow_nonneg pos.le _)] at h
  have lh := Real.log_le_log yp h
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos pos _).ne',Real.log_rpow pos] at lh
  have lyle := Real.log_le_log pos (show (x:ℝ) ≤ Erdos687.Y x by exact_mod_cast le)
  change 2*Real.log C/ε ≤ Real.log (x:ℝ) at hl
  have lim := (div_le_iff₀ he).mp hl
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr lyle),abs_of_nonneg lx.le]
  linarith

noncomputable def factor (x : ℕ) : ℕ := ⌊Real.log (x:ℝ)⌋₊+1
noncomputable def long (x : ℕ) : ℕ := Erdos687.Y x*factor x

theorem log_factor :
    (fun x : ℕ => Real.log (factor x)) =o[atTop] (fun x : ℕ => Real.log x) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [logs.eventually (Real.isLittleO_log_id_atTop.bound (half_pos he)),
    logs.eventually_ge_atTop (max 2 (2*Real.log 2/ε))] with x hs hl
  let L := Real.log (x:ℝ)
  change max 2 (2*Real.log 2/ε) ≤ L at hl
  have hL := (le_max_left _ _).trans hl
  have hε := (div_le_iff₀ he).mp ((le_max_right _ _).trans hl)
  have hK : 1 ≤ factor x := Nat.succ_pos _
  have hceil : (factor x:ℝ) ≤ 2*L := by
    have h := Nat.floor_le (by linarith : 0 ≤ L)
    change ((⌊L⌋₊+1:ℕ):ℝ) ≤ 2*L
    push_cast; linarith
  have up := Real.log_le_log (show (0:ℝ) < factor x by positivity) hceil
  rw [Real.log_mul (by norm_num) (by linarith)] at up
  change ‖Real.log L‖ ≤ ε/2*‖L‖ at hs
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (by linarith : 0 ≤ L)] at hs
  change ‖Real.log (factor x)‖ ≤ ε*‖L‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hK)),
    abs_of_nonneg (by linarith : 0 ≤ L)]
  linarith

theorem full_negligible : (fun x : ℕ => (Erdos687.Y x:ℝ)) =o[atTop] (fun x : ℕ => (long x:ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [logs.eventually_ge_atTop (1/ε)] with x h
  have hfloor := Nat.lt_floor_add_one (Real.log (x:ℝ))
  change 1/ε ≤ Real.log (x:ℝ) at h
  have hk : 1/ε ≤ (factor x:ℝ) := by dsimp [factor]; push_cast; linarith
  have product := (div_le_iff₀ he).mp hk
  simp only [long,Nat.cast_mul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left product (Nat.cast_nonneg (α := ℝ) (Erdos687.Y x))]

/-- If the upper bound asked in part (iii) holds, an interval longer
    than Y(x) by a factor asymptotic to log x can be covered apart from
    o(H/log H) points, using precisely the same prime cutoff x. -/
theorem weak_separation (upper : SubpowerUpper) :
    ∃ a : ℕ → ℕ → ℕ, (fun x => ((Transfert687.survivors x (long x) (a x)).card:ℝ)) =o[atTop]
      (fun x => (long x:ℝ)/Real.log (long x)) ∧
      (fun x : ℕ => (Erdos687.Y x:ℝ)) =o[atTop] (fun x : ℕ => (long x:ℝ)) := by
  have large : ∀ᶠ x : ℕ in atTop, x ≤ long x := by
    filter_upwards [eventual_lower] with x le
    exact le.trans (by simpa [long] using Nat.mul_le_mul_left (Erdos687.Y x) (show 1 ≤ factor x from Nat.succ_pos _))
  have eq : (fun x : ℕ => Real.log (Erdos687.Y x)-Real.log x + Real.log (factor x)) =ᶠ[atTop]
      (fun x => Real.log (long x)-Real.log x) := by
    filter_upwards [eventual_lower,eventually_ge_atTop (2:ℕ)] with x le hx
    have y0 : (Erdos687.Y x:ℝ) ≠ 0 := by exact_mod_cast (show Erdos687.Y x ≠ 0 by omega)
    have f0 : (factor x:ℝ) ≠ 0 := by exact_mod_cast (show factor x ≠ 0 from Nat.succ_ne_zero _)
    rw [long,Nat.cast_mul,Real.log_mul y0 f0]; ring
  have scale := ((excess upper).add log_factor).congr' eq Filter.EventuallyEq.rfl
  obtain ⟨a,ha⟩ := SousPuissance687.arbitrary_length long large scale
  exact ⟨a,ha,full_negligible⟩

end Separation687


namespace Inverse687
open Filter Separation687
open scoped Asymptotics

theorem Y_mono : Monotone Erdos687.Y := by
  intro z x hz
  obtain ⟨a,ha⟩ := Extension687.optimal_cover z
  apply Transfert687.le_Y_of_covered
  refine ⟨a,fun n hn => ?_⟩
  obtain ⟨p,le,pr,hit⟩ := ha n hn
  exact ⟨p,le.trans hz,pr,hit⟩

noncomputable def full (H : ℕ) : ℕ := sInf {x : ℕ | H ≤ Erdos687.Y x}

theorem full_spec (H : ℕ) : H ≤ Erdos687.Y (full H) := by
  change sInf {x : ℕ | H ≤ Erdos687.Y x} ∈ {x : ℕ | H ≤ Erdos687.Y x}
  apply Nat.sInf_mem
  obtain ⟨x,hx,le⟩ := (Filter.eventually_ge_atTop H |>.and eventual_lower).exists
  exact ⟨x,hx.trans le⟩

theorem full_le_iff {H x : ℕ} : full H ≤ x ↔ H ≤ Erdos687.Y x :=
  ⟨fun le => (full_spec H).trans (Y_mono le),fun le => Nat.sInf_le le⟩

theorem full_inf : Tendsto full atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (Erdos687.Y k+1)] with H h
  by_contra! no
  exact (by omega : ¬H ≤ Erdos687.Y k) (full_le_iff.mp no.le)

theorem full_small : ∀ᶠ H : ℕ in atTop, full H ≤ H :=
  eventual_lower.mono (fun _ h => full_le_iff.mpr h)

noncomputable def reduced (x : ℕ) : ℕ := x / factor x

private theorem bounds : ∀ᶠ x : ℕ in atTop,
    1 ≤ reduced x ∧ reduced x ≤ x ∧ x ≤ 2*reduced x*factor x := by
  filter_upwards [eventually_ge_atTop (2:ℕ)] with x hx
  have xp : (0:ℝ) < x := by positivity
  have log0 := Real.log_nonneg (show (1:ℝ) ≤ x by exact_mod_cast (show 1 ≤ x by omega))
  have kx : factor x ≤ x := by
    have h := Nat.floor_le log0
    have le := Real.log_le_sub_one_of_pos xp
    exact_mod_cast (show (factor x:ℝ) ≤ x by dsimp [factor]; push_cast; linarith)
  have kp : 0 < factor x := Nat.succ_pos _
  have rp : 1 ≤ reduced x := (Nat.div_pos kx kp)
  have cover := (Nat.div_lt_iff_lt_mul kp).mp (Nat.lt_succ_self (x/factor x))
  change x < (reduced x+1)*factor x at cover
  exact ⟨rp,Nat.div_le_self ..,cover.le.trans (Nat.mul_le_mul_right _ (by omega))⟩

private theorem logs_inf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem reduced_loss :
    (fun x : ℕ => Real.log x-Real.log (reduced x)) =o[atTop] (fun x : ℕ => Real.log x) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  filter_upwards [bounds,eventually_ge_atTop (2:ℕ),log_factor.bound (half_pos he),
    logs_inf.eventually_ge_atTop (2*Real.log 2/ε)] with x hb hx hfactor hlog
  obtain ⟨rp,rx,cover⟩ := hb
  have xp : (0:ℝ) < x := by positivity
  have rpos : (0:ℝ) < reduced x := by exact_mod_cast rp
  have kpos : 0 < factor x := Nat.succ_pos _
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast hx)
  have le := Real.log_le_log rpos (show (reduced x:ℝ) ≤ x by exact_mod_cast rx)
  have top := Real.log_le_log xp (show (x:ℝ) ≤ 2*reduced x*factor x by exact_mod_cast cover)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) rpos.ne'] at top
  change 2*Real.log 2/ε ≤ Real.log (x:ℝ) at hlog
  have lim := (div_le_iff₀ he).mp hlog
  change ‖Real.log (factor x)‖ ≤ ε/2*‖Real.log (x:ℝ)‖ at hfactor
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast kpos)),
    abs_of_nonneg lx.le] at hfactor
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le),abs_of_nonneg lx.le]
  linarith

theorem half_log : ∀ᶠ x : ℕ in atTop, Real.log (x:ℝ) ≤ 2*Real.log (reduced x) := by
  filter_upwards [reduced_loss.bound (by norm_num : (0:ℝ)<1/2),bounds,eventually_ge_atTop (2:ℕ)]
    with x h hb hx
  have le := Real.log_le_log (by exact_mod_cast hb.1 : (0:ℝ)<reduced x)
    (show (reduced x:ℝ) ≤ x by exact_mod_cast hb.2.1)
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast hx)
  change ‖Real.log x-Real.log (reduced x)‖ ≤ 1/2*‖Real.log (x:ℝ)‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le),abs_of_nonneg lx.le] at h
  linarith

theorem reduced_inf : Tendsto reduced atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [half_log,bounds,logs_inf.eventually_ge_atTop (2*Real.log (b+1:ℕ))] with x h hb hl
  have bp : (0:ℝ) < (b+1:ℕ) := by positivity
  change 2*Real.log (b+1:ℕ) ≤ Real.log (x:ℝ) at hl
  have le := (Real.log_le_log_iff bp (by exact_mod_cast hb.1 : (0:ℝ)<reduced x)).mp (by linarith)
  exact (Nat.le_succ b).trans (by exact_mod_cast le)

theorem reduced_negligible :
    (fun x : ℕ => (reduced x:ℝ)) =o[atTop] (fun x : ℕ => (x:ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  filter_upwards [logs_inf.eventually_ge_atTop (1/ε)] with x hl
  change 1/ε ≤ Real.log (x:ℝ) at hl
  have f := Nat.lt_floor_add_one (Real.log (x:ℝ))
  have hk : 1/ε ≤ (factor x:ℝ) := by dsimp [factor]; push_cast; linarith
  have scale := (div_le_iff₀ he).mp hk
  have cap : (reduced x:ℝ)*factor x ≤ x := by exact_mod_cast Nat.div_mul_le_self x (factor x)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg (α := ℝ) (reduced x)),
    mul_le_mul_of_nonneg_left cap he.le]

/-- The cutoff used for almost-coverage, as a function of the interval
    length. It is asymptotic to full H / log (full H). -/
noncomputable def weak (H : ℕ) : ℕ := reduced (full H)

theorem weak_negligible :
    (fun H : ℕ => (weak H:ℝ)) =o[atTop] (fun H : ℕ => (full H:ℝ)) :=
  reduced_negligible.comp_tendsto full_inf

/-- If part (iii) holds, the same explicit, asymptotically smaller
    cutoff almost-covers every sufficiently large interval length with
    o(H/log H) exceptions. Full coverage requires precisely full H. -/
theorem inverse_separation (upper : SubpowerUpper) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((Transfert687.survivors (weak H) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧
      (fun H : ℕ => (weak H:ℝ)) =o[atTop] (fun H : ℕ => (full H:ℝ)) := by
  have winf : Tendsto weak atTop atTop := reduced_inf.comp full_inf
  have le : ∀ᶠ H : ℕ in atTop, weak H ≤ H := by
    filter_upwards [full_inf.eventually bounds,full_small] with H h small
    exact h.2.1.trans small
  have scale : (fun H : ℕ => Real.log H-Real.log (weak H)) =o[atTop]
      (fun H : ℕ => Real.log (weak H)) := by
    apply Asymptotics.isLittleO_iff.mpr
    intro ε he
    have quarter : 0 < ε/4 := by positivity
    filter_upwards [full_inf.eventually ((excess upper).bound quarter),
      full_inf.eventually (reduced_loss.bound quarter),full_inf.eventually half_log,
      full_inf.eventually bounds,full_small,full_inf.eventually_ge_atTop 2,
      winf.eventually_ge_atTop 2] with H hs hr hf hb fh f2 w2
    let f := full H
    let w := weak H
    have wf : w ≤ f := hb.2.1
    have wh : w ≤ H := wf.trans fh
    have xy := full_spec H
    have fp : (0:ℝ) < f := by exact_mod_cast (show 0 < full H by omega)
    have wp : (0:ℝ) < w := by exact_mod_cast (show 0 < weak H by omega)
    have hp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have lf := Real.log_pos (show (1:ℝ)<f by exact_mod_cast f2)
    have lw := Real.log_pos (show (1:ℝ)<w by exact_mod_cast w2)
    have wy := Real.log_le_log wp (show (w:ℝ) ≤ H by exact_mod_cast wh)
    have fw := Real.log_le_log wp (show (w:ℝ) ≤ f by exact_mod_cast wf)
    have hy := Real.log_le_log hp (show (H:ℝ) ≤ Erdos687.Y f by exact_mod_cast xy)
    have fy := Real.log_le_log fp (show (f:ℝ) ≤ Erdos687.Y f by exact_mod_cast fh.trans xy)
    change ‖Real.log (Erdos687.Y f)-Real.log f‖ ≤ ε/4*‖Real.log (f:ℝ)‖ at hs
    change ‖Real.log f-Real.log w‖ ≤ ε/4*‖Real.log (f:ℝ)‖ at hr
    change Real.log (f:ℝ) ≤ 2*Real.log w at hf
    change ‖Real.log H-Real.log w‖ ≤ ε*‖Real.log (w:ℝ)‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr wy),abs_of_nonneg lw.le]
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr fy),abs_of_nonneg lf.le] at hs
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr fw),abs_of_nonneg lf.le] at hr
    nlinarith [mul_le_mul_of_nonneg_left hf he.le]
  obtain ⟨a,ha⟩ := SousPuissance687.arbitrary_length_along weak id winf le scale
  exact ⟨a,ha,weak_negligible⟩

end Inverse687


namespace Accroissements687
open Extension687 Progressions687 Transfert687 Presque687
open OAI.Erdos970.NumberTheoryLean

private theorem eighth {J z : ℕ} (cap : J ≤ z^8) : Nat.nthRoot 8 J ≤ z := by
  apply Nat.lt_succ_iff.mp ((Nat.nthRoot_lt_iff (by norm_num : 8 ≠ 0)).mpr ?_)
  exact cap.trans_lt (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by norm_num : 8 ≠ 0))

theorem extreme {J z : ℕ} (big : 256 ≤ J) (cap : J ≤ z^8) (b : ℕ → ℕ) :
    ((siftedIndices z J b).card:ℝ) ≤ 17*J/Real.log J := by
  rw [CribleTransfert687.index_eq_cutoff]
  exact SquarefreeHarmonic.cutoffSurvivors_le_seventeen J z b big (eighth cap)
end Accroissements687

namespace Troncature687
open Filter Transfert687 Progressions687 Presque687
open scoped Asymptotics

/-- Restricting a complete cover at y to primes up to x costs the
    reciprocal mass of the deleted band, divided by log(H/y). -/
theorem truncate {x y H : ℕ} (size : 2 ≤ x) (xy : x ≤ y) (far : 256*y ≤ H)
    (radius : H ≤ x^8) (full : H ≤ Erdos687.Y y) :
    (holes x H:ℝ) ≤ 34*H*(Real.log y-Real.log x+10)/
      (Real.log x*(Real.log H-Real.log y)) := by
  have xp : (0:ℝ) < x := by positivity
  have yp : (0:ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  let L := Real.log (H:ℝ)-Real.log (y:ℝ)
  have lpos : 0 < L := sub_pos.mpr (Real.log_lt_log yp
    (show (y:ℝ)<H by exact_mod_cast (show y<H by omega)))
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast size)
  obtain ⟨a,cov⟩ := Extension687.optimal_cover y
  have covered (n : ℕ) (hn : n ∈ Finset.Icc 1 H) :
      ∃ p ≤ y, p.Prime ∧ n%p = a p%p := by
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
    exact cov n (Finset.mem_Icc.mpr ⟨lo,up.trans full⟩)
  have sum := OMA.R_Erdos687_erdos_687_variants_iwaniec_R2.survivor_le_sum (z := x) a covered
  change (survivors x H a).card ≤ ∑ p ∈ y.primesLE \ x.primesLE, charge (survivors x H a) a p at sum
  have term (p : ℕ) (mem : p ∈ y.primesLE \ x.primesLE) :
      (charge (survivors x H a) a p:ℝ) ≤ (34*H/L)*(1/(p:ℝ)) := by
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨py,pr⟩ := Nat.mem_primesLE.mp hin
    have px : x < p := by
      by_contra! le
      exact hout (Nat.mem_primesLE.mpr ⟨le,pr⟩)
    let J := H/p+1
    have pp : (0:ℝ) < p := by exact_mod_cast pr.pos
    have jm : H < J*p := (Nat.div_lt_iff_lt_mul pr.pos).mp (Nat.lt_succ_self _)
    have big : 256 ≤ J := by
      have q := (Nat.le_div_iff_mul_le pr.pos).mpr ((Nat.mul_le_mul_left 256 py).trans far)
      dsimp [J]; omega
    have cap : J ≤ x^8 := by
      have u := Nat.div_lt_self (by omega : 0 < H) pr.one_lt
      dsimp [J]; omega
    have jp : (0:ℝ) < J := by positivity
    have low : (H:ℝ)/y ≤ J := (div_le_iff₀ yp).mpr (by exact_mod_cast jm.le.trans (Nat.mul_le_mul_left J py))
    have high : (J:ℝ) ≤ 2*H/p := by
      apply (le_div_iff₀ pp).mpr
      have u := Nat.div_mul_le_self H p
      exact_mod_cast (show J*p ≤ 2*H by dsimp [J]; rw [Nat.add_mul]; omega)
    have lj := Real.log_le_log (div_pos hp yp) low
    rw [Real.log_div hp.ne' yp.ne'] at lj
    change L ≤ Real.log (J:ℝ) at lj
    obtain ⟨b,cb⟩ := charge_le_index_sieve (N := H) pr px a
    have saved := Accroissements687.extreme big cap b
    calc
      _ ≤ ((siftedIndices x J b).card:ℝ) := by exact_mod_cast cb
      _ ≤ _ := saved
      _ ≤ 17*J/L := div_le_div_of_nonneg_left (by positivity) lpos lj
      _ ≤ (17*(2*H/p))/L := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left high (by norm_num)) lpos.le
      _ = _ := by ring
  have raw := Harmonique687.band_bound (z := (x:ℝ)) (x := y) (by exact_mod_cast size) (by exact_mod_cast xy)
  rw [Nat.floor_natCast] at raw
  have band : (∑ p ∈ y.primesLE \ x.primesLE, (1:ℝ)/p) ≤
      (Real.log y-Real.log x+10)/Real.log x := (le_div_iff₀ lx).mpr (by rwa [mul_comm])
  calc
    _ ≤ ∑ p ∈ y.primesLE \ x.primesLE, (charge (survivors x H a) a p:ℝ) := by
      exact_mod_cast (holes_le x H a).trans sum
    _ ≤ _ := Finset.sum_le_sum term
    _ = (34*H/L)*(∑ p ∈ y.primesLE \ x.primesLE, (1:ℝ)/p) := (Finset.mul_sum ..).symm
    _ ≤ (34*H/L)*((Real.log y-Real.log x+10)/Real.log x) :=
      mul_le_mul_of_nonneg_left band (by positivity)
    _ = _ := by rw [div_mul_div_comm,mul_comm L (Real.log x)]

/-- If truncation leaves a fixed positive normalized exceptional count,
    then the full interval was only slightly longer on a log scale.
    The constant is independent of the interval and both cutoffs. -/
theorem length_if_many {x y H : ℕ} {ε : ℝ} (he : 0 < ε) (size : 2 ≤ x)
    (xy : x ≤ y) (yh : y ≤ H) (radius : H ≤ x^8) (full : H ≤ Erdos687.Y y)
    (many : ε*((H:ℝ)/Real.log H) ≤ holes x H) :
    Real.log H-Real.log x ≤ (1+272/ε)*(Real.log y-Real.log x+10)+Real.log 256 := by
  have xp : (0:ℝ)<x := by positivity
  have yp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast size)
  have lh := Real.log_pos (show (1:ℝ)<H by exact_mod_cast (show 1<H by omega))
  let S := Real.log (y:ℝ)-Real.log x+10
  have gap := Real.log_le_log xp (show (x:ℝ) ≤ y by exact_mod_cast xy)
  have sp : 0 ≤ S := by dsimp [S]; linarith
  have wide := Real.log_le_log hp (show (H:ℝ) ≤ (x:ℝ)^8 by exact_mod_cast radius)
  rw [Real.log_pow] at wide
  norm_num at wide
  have positive := Real.log_nonneg (show (1:ℝ) ≤ 256 by norm_num)
  by_cases far : 256*y ≤ H
  · let D := Real.log (H:ℝ)-Real.log y
    have dp : 0 < D := sub_pos.mpr (Real.log_lt_log yp (by exact_mod_cast (show y<H by omega)))
    have h := many.trans (truncate size xy far radius full)
    change ε*((H:ℝ)/Real.log H) ≤ 34*H*S/(Real.log x*D) at h
    have crossed : (ε*H)*(Real.log x*D) ≤ (34*H*S)*Real.log H :=
      (div_le_div_iff₀ lh (mul_pos lx dp)).mp (by simpa only [mul_div_assoc] using h)
    have cancel : (H:ℝ)*(ε*D*Real.log x) ≤ H*(34*S*Real.log H) := by
      nlinarith only [crossed]
    have c := (le_of_mul_le_mul_left cancel hp)
    have replace := mul_le_mul_of_nonneg_left wide (show 0 ≤ 34*S by positivity)
    have c' : (ε*D)*Real.log x ≤ (272*S)*Real.log x := by nlinarith only [c,replace]
    have last := le_of_mul_le_mul_right c' lx
    have lift : D ≤ (272/ε)*S := (le_div_iff₀ he).mpr (by nlinarith only [last]) |>.trans_eq
      (show 272*S/ε = (272/ε)*S by ring)
    dsimp [D,S] at lift
    nlinarith only [lift,positive]
  · have height := Real.log_le_log hp (show (H:ℝ) ≤ 256*y by exact_mod_cast (Nat.le_of_not_ge far))
    rw [Real.log_mul (by norm_num) yp.ne'] at height
    have extra : 0 ≤ (272/ε)*S := by positivity
    dsimp [S] at extra
    nlinarith only [height,extra]

/-- A full cover at y forces an almost-cover at every x in the same
    logarithmic scale, uniformly up to length x^8. -/
theorem remove_band (X Y H : ℕ → ℕ) (xinf : Tendsto X atTop atTop)
    (range : ∀ᶠ i : ℕ in atTop, X i ≤ Y i ∧ Y i ≤ H i ∧ H i ≤ (X i)^8 ∧ H i ≤ Erdos687.Y (Y i))
    (gap : (fun i => Real.log (Y i)-Real.log (X i)) =o[atTop] (fun i => Real.log (X i))) :
    (fun i => (holes (X i) (H i):ℝ)) =o[atTop] (fun i => (H i:ℝ)/Real.log (H i)) := by
  classical
  have logs := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)).comp xinf
  have constants (c : ℝ) : (fun _ : ℕ => c) =o[atTop] (fun i => Real.log (X i)) :=
    (Asymptotics.isLittleO_const_id_atTop c).comp_tendsto logs
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  let bad (i : ℕ) := ε*((H i:ℝ)/Real.log (H i)) ≤ holes (X i) (H i)
  let T (i : ℕ) := if bad i then H i else X i
  have xl : ∀ᶠ i : ℕ in atTop, X i ≤ T i := by
    filter_upwards [range] with i hr
    dsimp only [T]
    split <;> first | exact hr.1.trans hr.2.1 | exact le_rfl
  let C := 1+272/ε
  let major (i : ℕ) := C*(Real.log (Y i)-Real.log (X i)+10)+Real.log 256
  have small : major =o[atTop] (fun i => Real.log (X i)) :=
    (((gap.add (constants 10)).const_mul_left C).add (constants (Real.log 256)))
  have bounded : (fun i => Real.log (T i)-Real.log (X i)) =O[atTop] major := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [range,xl,xinf.eventually_ge_atTop 2] with i h ht hx
    have xp : (0:ℝ)<X i := by exact_mod_cast (show 0<X i by omega)
    have le := Real.log_le_log xp (show (X i:ℝ) ≤ T i by exact_mod_cast ht)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le)]
    by_cases b : bad i
    · simpa only [T,if_pos b,major,C] using length_if_many he hx h.1 h.2.1 h.2.2.1 h.2.2.2 b
    · simp only [T,if_neg b,sub_self,major]
      have gy := Real.log_le_log xp (show (X i:ℝ) ≤ Y i by exact_mod_cast h.1)
      have nn : 0 ≤ Real.log (Y i)-Real.log (X i)+10 := by linarith
      have cc : 0 ≤ C := by dsimp [C]; positivity
      linarith [mul_nonneg cc nn,Real.log_nonneg (show (1:ℝ) ≤ 256 by norm_num)]
  obtain ⟨a,ha⟩ := SousPuissance687.arbitrary_length_along X T xinf xl (bounded.trans_isLittleO small)
  filter_upwards [ha.bound he,range,xinf.eventually_ge_atTop 2] with i cover hr hx
  have hh := hx.trans (hr.1.trans hr.2.1)
  have lh := Real.log_pos (show (1:ℝ)<H i by exact_mod_cast hh)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by positivity) lh.le)]
  by_cases b : bad i
  · change ‖((Transfert687.survivors (X i) (T i) (a i)).card:ℝ)‖ ≤
      ε*‖(T i:ℝ)/Real.log (T i)‖ at cover
    simp only [T,if_pos b,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) lh.le)] at cover
    exact (by exact_mod_cast holes_le (X i) (H i) (a i) :
      (holes (X i) (H i):ℝ) ≤ (Transfert687.survivors (X i) (H i) (a i)).card).trans cover
  · exact (lt_of_not_ge b).le

/-- This mild polynomial bound follows already from Iwaniec's classical
    Y(x) = O(x²). Only the displayed exponent is used by the proof. -/
def Cubic : Prop := ∀ᶠ y : ℕ in atTop, Erdos687.Y y ≤ y^3

theorem cubic_of_quadratic (quad : (fun y : ℕ => (Erdos687.Y y:ℝ)) =O[atTop]
    (fun y : ℕ => (y:ℝ)^2)) : Cubic := by
  obtain ⟨C,hc,bound⟩ := Asymptotics.isBigO_iff'.mp quad
  filter_upwards [bound,(tendsto_natCast_atTop_atTop : Tendsto (fun y : ℕ => (y:ℝ)) atTop atTop).eventually_ge_atTop C]
    with y h big
  change ‖(Erdos687.Y y:ℝ)‖ ≤ C*‖(y:ℝ)^2‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (sq_nonneg _)] at h
  exact_mod_cast (show (Erdos687.Y y:ℝ) ≤ (y:ℝ)^3 by
    nlinarith [mul_le_mul_of_nonneg_right big (sq_nonneg (y:ℝ))])

/-- Every smaller cutoff on the same logarithmic scale as the optimal
    full cutoff suffices for almost-coverage, for all large lengths. -/
theorem general_inverse (poly : Cubic) (X : ℕ → ℕ) (xinf : Tendsto X atTop atTop)
    (xf : ∀ᶠ H : ℕ in atTop, X H ≤ Inverse687.full H)
    (gap : (fun H => Real.log (Inverse687.full H)-Real.log (X H)) =o[atTop] (fun H => Real.log (X H))) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((survivors (X H) H (a H)).card:ℝ)) =o[atTop]
      (fun H : ℕ => (H:ℝ)/Real.log H) := by
  have range : ∀ᶠ H : ℕ in atTop, X H ≤ Inverse687.full H ∧ Inverse687.full H ≤ H ∧
      H ≤ (X H)^8 ∧ H ≤ Erdos687.Y (Inverse687.full H) := by
    filter_upwards [xf,Inverse687.full_small,Inverse687.full_inf.eventually poly,
      xinf.eventually_ge_atTop 2,gap.bound (by norm_num : (0:ℝ)<1)] with H le small cap hx hl
    let f := Inverse687.full H
    let x := X H
    have xp : (0:ℝ)<x := by exact_mod_cast (show 0<X H by omega)
    have fp : (0:ℝ)<f := by exact_mod_cast (show 0<Inverse687.full H by omega)
    have hp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
    have spec := Inverse687.full_spec H
    have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast hx)
    have sign := Real.log_le_log xp (show (x:ℝ) ≤ f by exact_mod_cast le)
    change ‖Real.log f-Real.log x‖ ≤ 1*‖Real.log (x:ℝ)‖ at hl
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr sign),abs_of_nonneg lx.le] at hl
    have bound := Real.log_le_log hp (show (H:ℝ) ≤ (f:ℝ)^3 by exact_mod_cast spec.trans cap)
    rw [Real.log_pow] at bound
    have wide : Real.log (H:ℝ) ≤ Real.log ((x:ℝ)^8) := by
      rw [Real.log_pow]; norm_num at bound ⊢; linarith
    exact ⟨le,small,by exact_mod_cast (Real.log_le_log_iff hp (pow_pos xp 8)).mp wide,spec⟩
  have upper := remove_band X Inverse687.full id xinf range gap
  choose a ha using fun H => realizes (X H) H
  exact ⟨a,upper.congr_left (fun H => (congrArg (fun n : ℕ => (n:ℝ)) (ha H)).symm)⟩

/-- A factor asymptotic to log f(H) may be saved, with f(H) the least
    full cutoff. Its sole input is a classical proved polynomial bound. -/
theorem inverse_of_quadratic (quad : (fun y : ℕ => (Erdos687.Y y:ℝ)) =O[atTop]
    (fun y : ℕ => (y:ℝ)^2)) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((survivors (Inverse687.weak H) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧
      (fun H : ℕ => (Inverse687.weak H:ℝ)) =o[atTop] (fun H : ℕ => (Inverse687.full H:ℝ)) := by
  have loss := Inverse687.reduced_loss.comp_tendsto Inverse687.full_inf
  have gap : (fun H => Real.log (Inverse687.full H)-Real.log (Inverse687.weak H)) =o[atTop]
      (fun H => Real.log (Inverse687.weak H)) := by
    refine loss.trans_isBigO (Asymptotics.IsBigO.of_bound 2 ?_)
    filter_upwards [Inverse687.full_inf.eventually Inverse687.half_log] with H h
    change ‖Real.log (Inverse687.full H)‖ ≤ 2*‖Real.log (Inverse687.reduced (Inverse687.full H))‖
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_natCast_nonneg _)] using h
  have small : ∀ H, Inverse687.weak H ≤ Inverse687.full H := fun _ => Nat.div_le_self .. 
  obtain ⟨a,ha⟩ := general_inverse (cubic_of_quadratic quad) Inverse687.weak
    (Inverse687.reduced_inf.comp Inverse687.full_inf) (Eventually.of_forall small) gap
  exact ⟨a,ha,Inverse687.weak_negligible⟩

/-- Convert the native logarithmic improvement to the hypothesis of the
    inverse comparison, using the catalog's exact definition of Y. -/
theorem quadratic_of_saving (saving : ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
    (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η))) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^2) := by
  obtain ⟨η,hη,bound⟩ := saving
  apply bound.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [logs.eventually_ge_atTop 1] with x h
  change 1 ≤ Real.log (x:ℝ) at h
  have den := Real.one_le_rpow h (by linarith : 0 ≤ 2+η)
  have nn := div_nonneg (sq_nonneg (x:ℝ)) (zero_le_one.trans den)
  simpa only [Real.norm_eq_abs,abs_of_nonneg nn,abs_of_nonneg (sq_nonneg (x:ℝ)),one_mul]
    using (div_le_self (sq_nonneg (x:ℝ)) den)

end Troncature687


open Filter in
theorem erdos687_inverse_almost_cover :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((Transfert687.survivors (Inverse687.weak H) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧
      (fun H : ℕ => (Inverse687.weak H:ℝ)) =o[atTop] (fun H : ℕ => (Inverse687.full H:ℝ)) :=
  Troncature687.inverse_of_quadratic (Troncature687.quadratic_of_saving erdos687_log_saving)

#print axioms erdos687_inverse_almost_cover
