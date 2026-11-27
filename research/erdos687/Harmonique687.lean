import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! An elementary bound for the sum of reciprocal primes in a short
logarithmic band. The proof uses the first Mertens estimate for the
von Mangoldt function, obtained directly from the factorial identity. -/
namespace Harmonique687
open Finset Filter
open scoped BigOperators

noncomputable def mangoldtSum (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / d

private theorem factorial_sum (n : ℕ) :
    ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * (↑(n/d) : ℝ) =
      Real.log (n.factorial : ℝ) := by
  rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum, ArithmeticFunction.vonMangoldt_mul_zeta]
  change (∑ d ∈ Ioc 0 n, Real.log d) = _
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]

/-- Uniform additive error, sufficient even when the lower endpoint tends
    to x on the logarithmic scale. -/
theorem first_mertens {n : ℕ} (hn : 0 < n) :
    Real.log n - 1 ≤ mangoldtSum n ∧ mangoldtSum n ≤ Real.log n + (Real.log 4 + 4) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let f (d : ℕ) := ArithmeticFunction.vonMangoldt d
  have hexpand : mangoldtSum n * n = ∑ d ∈ Ioc 0 n, f d * ((n:ℝ)/d) := by
    simp only [mangoldtSum, Finset.sum_mul, f, div_eq_mul_inv]
    apply sum_congr rfl
    intro d hd
    ring
  have hlow : Real.log (n.factorial : ℝ) ≤ mangoldtSum n * n := by
    rw [← factorial_sum, hexpand]
    apply sum_le_sum
    intro d hd
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
  have hhigh : mangoldtSum n * n ≤ Real.log (n.factorial : ℝ) + Chebyshev.psi n := by
    rw [hexpand, ← factorial_sum]
    change _ ≤ _ + ∑ d ∈ Ioc 0 ⌊(n:ℝ)⌋₊, ArithmeticFunction.vonMangoldt d
    rw [Nat.floor_natCast, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hd' : (0:ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have hquot : (n:ℝ)/d ≤ (↑(n/d):ℝ)+1 := by
      apply (div_le_iff₀ hd').2
      exact_mod_cast ((Nat.div_lt_iff_lt_mul (Finset.mem_Ioc.mp hd).1).1
        (Nat.lt_succ_self (n/d))).le
    simpa [mul_add, f] using mul_le_mul_of_nonneg_left hquot
      (ArithmeticFunction.vonMangoldt_nonneg (n := d))
  have fakt_upper : Real.log (n.factorial : ℝ) ≤ (n:ℝ) * Real.log n := by
    have hnat : n.factorial ≤ n^n := Nat.factorial_le_pow n
    simpa [Real.log_pow] using Real.log_le_log (by positivity : (0:ℝ) < n.factorial)
      (show (n.factorial : ℝ) ≤ (n:ℝ)^n by exact_mod_cast hnat)
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)
  have hpi := Real.log_nonneg (show (1:ℝ) ≤ 2*Real.pi by linarith [Real.two_le_pi])
  constructor
  · apply le_of_mul_le_mul_right _ hn'
    linarith [Stirling.le_log_factorial_stirling (Nat.ne_of_gt hn)]
  · apply le_of_mul_le_mul_right _ hn'
    linarith [Chebyshev.psi_le_const_mul_self hn'.le]

/-- Bound the contribution of the primes in (z,x] using only Chebyshev's
uniform bound and the logarithm of the factorial. The lower cutoff is real. -/
theorem band_bound {x : ℕ} {z : ℝ} (hz : 2 ≤ z) (hzx : z ≤ x) :
    Real.log z * (∑ p ∈ x.primesLE \ ⌊z⌋₊.primesLE, (1:ℝ)/p) ≤
      Real.log x - Real.log z + 10 := by
  let m := ⌊z⌋₊
  have hm : 2 ≤ m := (Nat.le_floor_iff (by linarith)).2 (by simpa using hz)
  have hmx : m ≤ x := Nat.floor_le_of_le hzx
  have hm' : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let B := x.primesLE \ m.primesLE
  let D := Ioc 0 x \ Ioc 0 m
  have sub : B ⊆ D := by
    intro p hp
    obtain ⟨hpx, hpm⟩ := mem_sdiff.mp hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hpx
    exact mem_sdiff.mpr ⟨mem_Ioc.mpr ⟨hprime.pos,hle⟩,
      fun h => hpm (Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp h).2,hprime⟩)⟩
  have h1 : Real.log z * (∑ p ∈ B, (1:ℝ)/p) ≤
      ∑ d ∈ D, ArithmeticFunction.vonMangoldt d / d := by
    rw [mul_sum]
    calc
      _ ≤ ∑ p ∈ B, ArithmeticFunction.vonMangoldt p / p := by
        apply sum_le_sum
        intro p hp
        have prime := (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2
        have hmp : m < p := by
          by_contra! h
          exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h,prime⟩)
        have hzp : z ≤ (p:ℝ) := (Nat.lt_floor_add_one z).le.trans
          (by exact_mod_cast (show m+1 ≤ p by omega))
        rw [ArithmeticFunction.vonMangoldt_apply_prime prime, mul_one_div]
        exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hzp) (by positivity)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have ss : Ioc 0 m ⊆ Ioc 0 x := Ioc_subset_Ioc_right hmx
  have hadd : (∑ d ∈ D, ArithmeticFunction.vonMangoldt d / d) + mangoldtSum m =
      mangoldtSum x := sum_sdiff ss
  have hratio : z ≤ 2 * (m:ℝ) := by
    have large : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith [show z < (m:ℝ)+1 from Nat.lt_floor_add_one z]
  have hre := Real.log_le_log (by linarith : 0 < z) hratio
  rw [Real.log_mul (by norm_num) hm'.ne'] at hre
  have h2 := (first_mertens (n := x) (by omega)).2
  have h3 := (first_mertens (n := m) (by omega)).1
  change Real.log z * (∑ p ∈ B, (1:ℝ)/p) ≤ _
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4),
    Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]

/-- The harmonic estimate required by the 1/400 cutoff, with its original
constant 3/1000. No prime number theorem or asymptotic error term is assumed. -/
theorem harmonic_at_cutoff :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ x.primesLE \ ⌊(x:ℝ)/(Real.log x)^(1/400:ℝ)⌋₊.primesLE, (1:ℝ)/p) ≤
        (3/1000:ℝ) * Real.log (Real.log x) / Real.log x := by
  have hLinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLinf.eventually_ge_atTop 4,
    (Real.tendsto_log_atTop.comp hLinf).eventually_ge_atTop 40000,
    eventually_ge_atTop (2:ℕ)] with x hL hLL hx
  let L := Real.log (x:ℝ)
  let z := (x:ℝ) / L^(1/400:ℝ)
  change (4:ℝ) ≤ L at hL
  change (40000:ℝ) ≤ Real.log L at hLL
  have hpos : 0 < L := by linarith
  have hp : 0 < L^(1/400:ℝ) := Real.rpow_pos_of_pos hpos _
  have hxpos : (0:ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : Real.log z = L - (1/400:ℝ)*Real.log L := by
    dsimp only [z]
    rw [Real.log_div hxpos.ne' hp.ne', Real.log_rpow hpos]
  have hlarge : (399/400:ℝ)*L ≤ Real.log z := by
    rw [hlog]
    linarith [Real.log_le_sub_one_of_pos hpos]
  have hzpos : 0 < z := div_pos hxpos hp
  have hz : 2 ≤ z := by
    apply (Real.log_le_log_iff (by norm_num) hzpos).mp
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hzx : z ≤ x := div_le_self hxpos.le (Real.one_le_rpow (by linarith) (by norm_num))
  have hb := band_bound hz hzx
  let S := ∑ p ∈ x.primesLE \ ⌊z⌋₊.primesLE, (1:ℝ)/p
  change Real.log z * S ≤ L - Real.log z + 10 at hb
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hm := mul_le_mul_of_nonneg_right hlarge hs
  have hc : Real.log z * S ≤ (1/400:ℝ)*Real.log L+10 := by linarith only [hb,hlog]
  change S ≤ _ / L
  apply (le_div_iff₀ hpos).2
  nlinarith only [hm, hc, hLL]

end Harmonique687
