import Mathlib
import SourcePubliee687
import OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic

/-! Erdős 687(i), upper bound. Green46.IsCoveredByResidues and Erdos687.Y
are copied verbatim from google-deepmind/formal-conjectures, Apache-2.0,
revision 9097e2f90e66d2f6244209cb1c07f7120d17ec53. -/

open scoped BigOperators Asymptotics

namespace Green46
def IsCoveredByResidues (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 y, ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]
end Green46

namespace Erdos687
noncomputable def Y (x : ℕ) : ℕ :=
  sSup {y : ℕ | Green46.IsCoveredByResidues x y}
end Erdos687

namespace OMA.R_Erdos687_erdos_687_variants_iwaniec_R2
theorem survivor_le_sum {x z N : ℕ} (a : ℕ → ℕ)
    (covered : ∀ n ∈ Finset.Icc 1 N, ∃ p ≤ x, Nat.Prime p ∧ n % p = a p % p) :
    let small := z.primesLE
    let S := (Finset.Icc 1 N).filter fun n => ∀ p ∈ small, n % p ≠ a p % p
    S.card ≤ ∑ p ∈ x.primesLE \ small, (S.filter fun n => n % p = a p % p).card := by
  intro small S
  let band := x.primesLE \ small
  let hits := fun p : ℕ => S.filter fun n => n % p = a p % p
  have incl : S ⊆ band.biUnion hits := by
    intro n hn
    obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, hpx, hp, hres⟩ := covered n hI
    have hsmall : p ∉ small := fun h => hs p h hres
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_sdiff.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hpx, hp⟩, hsmall⟩, Finset.mem_filter.mpr ⟨hn, hres⟩⟩
  exact (Finset.card_le_card incl).trans Finset.card_biUnion_le

-- Also usable at the shorter logarithmic scales of the quantitative sieve.
theorem upper_of_survivor_budget {x z N : ℕ}
    (budget : ∀ a : ℕ → ℕ,
      let S := (Finset.Icc 1 N).filter fun n => ∀ p ∈ z.primesLE, n % p ≠ a p % p
      (∑ p ∈ x.primesLE \ z.primesLE, (S.filter fun n => n % p = a p % p).card) < S.card) :
    Erdos687.Y x ≤ N := by
  apply csSup_le
  · exact ⟨0, fun _ => 0, by simp⟩
  · intro y hy
    obtain ⟨a, ha⟩ := hy
    by_contra! hNy
    have hcov : ∀ n ∈ Finset.Icc 1 N, ∃ p ≤ x, Nat.Prime p ∧ n % p = a p % p := by
      intro n hn
      exact ha n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans hNy.le⟩)
    exact (Nat.not_lt_of_ge (survivor_le_sum (z := z) a hcov)) (budget a)
end OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

namespace Transfert687
def survivors (x N : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ p ∈ x.primesLE, n % p ≠ a p % p

def charge (S : Finset ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  (S.filter fun n => n % p = a p % p).card
end Transfert687

namespace Progressions687

open Filter Transfert687 OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

/-- Indices of a progression start at zero. -/
def siftedIndices (z M : ℕ) (b : ℕ → ℕ) : Finset ℕ :=
  (Finset.range M).filter fun k => ∀ q ∈ z.primesLE, k % q ≠ b q % q

/-- Dividing points of one large-prime class by p embeds its survivors in
    an ordinary sifted interval of at most floor(N/p)+1 indices. -/
theorem charge_le_index_sieve {z N p : ℕ} (hp : p.Prime) (hzp : z < p) (a : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, charge (survivors z N a) a p ≤
      (siftedIndices z (N/p+1) b).card := by
  classical
  let t (q : ℕ) := if h : p.Coprime q then (Nat.chineseRemainder h (a p) (a q)).val else 0
  let b (q : ℕ) := t q / p
  refine ⟨b, Finset.card_le_card_of_injOn (fun n : ℕ => n / p) ?_ ?_⟩
  · intro n hn
    obtain ⟨hs, hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨hI, avoid⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Finset.mem_Icc.mp hI).2)), ?_⟩
    intro q hq hindex
    obtain ⟨hqz, hqprime⟩ := Nat.mem_primesLE.mp hq
    have cop : p.Coprime q := (Nat.coprime_primes hp hqprime).2 (by omega)
    have crt : t q ≡ a p [MOD p] ∧ t q ≡ a q [MOD q] := by
      dsimp only [t]
      rw [dif_pos cop]
      exact (Nat.chineseRemainder cop (a p) (a q)).property
    have hrem : n % p = t q % p := hr.trans crt.1.symm
    have idx : n / p ≡ t q / p [MOD q] := hindex
    have hmod := (idx.mul_left p).add_left (n % p)
    have hsame : n ≡ t q [MOD q] := by
      calc
        n = n % p + p * (n / p) := (Nat.mod_add_div _ _).symm
        _ ≡ n % p + p * (t q / p) [MOD q] := hmod
        _ = t q := by rw [hrem, Nat.mod_add_div]
    exact avoid q hq (hsame.trans crt.2)
  · intro n hn m hm heq
    change n / p = m / p at heq
    obtain ⟨_, hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hs⟩ := Finset.mem_filter.mp hm
    calc
      n = n % p + p * (n / p) := (Nat.mod_add_div _ _).symm
      _ = m % p + p * (m / p) := by rw [hr, hs, heq]
      _ = m := Nat.mod_add_div _ _
end Progressions687

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
end Harmonique687



/-!
Lower bound in Mertens' third theorem: the product of (1 - 1/p) over primes p ≤ x is at
least 1/(3 log x) for x ≥ 3, and equals 1/2 at x = 2.

Credit: the explicit Mertens bound is the merged proof
proofs/Erdos1141.erdos_1141.variants.mertens_third.lean by Sebastian Bachmaier (PR #1431),
reused verbatim (namespace OMA_M3); only the final step x = 2 and the change from 1 / p to
p⁻¹ are new.
-/


namespace OMA_M3
open Real Finset

noncomputable def Sm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p / p
noncomputable def Lm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, -Real.log (1 - 1 / (p:ℝ))
noncomputable def Qm (n : ℕ) : ℝ := ∏ p ∈ (range (n + 1)).filter Nat.Prime, (1 - 1 / (p:ℝ))
noncomputable def cM : ℝ := 2 * Real.log 2 - 1 + 1 / 12
noncomputable def Hm (n : ℕ) : ℝ :=
  Lm n - Real.log (Real.log n) + (Real.log n + cM - Sm n) / Real.log n + 1 / n

lemma filter_succ (n : ℕ) : (range (n + 2)).filter Nat.Prime =
    if (n+1).Prime then insert (n+1) ((range (n+1)).filter Nat.Prime)
    else (range (n+1)).filter Nat.Prime := by
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_filter (n : ℕ) : n + 1 ∉ (range (n+1)).filter Nat.Prime := by simp

lemma Sm_succ (n : ℕ) : Sm (n+1) = Sm n +
    (if (n+1).Prime then Real.log ((n:ℝ)+1) / ((n:ℝ)+1) else 0) := by
  unfold Sm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Lm_succ (n : ℕ) : Lm (n+1) = Lm n +
    (if (n+1).Prime then -Real.log (1 - 1 / ((n:ℝ)+1)) else 0) := by
  unfold Lm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_succ (n : ℕ) : Qm (n+1) = Qm n *
    (if (n+1).Prime then (1 - 1 / ((n:ℝ)+1)) else 1) := by
  unfold Qm
  rw [filter_succ]
  split_ifs
  · rw [prod_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_nonneg (n : ℕ) : 0 ≤ Qm n := by
  unfold Qm
  apply prod_nonneg
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 1 / (p:ℝ) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma Qm_anti (n : ℕ) : ∀ m, n ≤ m → Qm m ≤ Qm n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    rw [Qm_succ]
    refine le_trans ?_ ih
    split_ifs
    · have h0 := Qm_nonneg m
      have h1 : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
      nlinarith
    · simp

lemma Qm_eq_exp (n : ℕ) : Qm n = Real.exp (- Lm n) := by
  unfold Qm Lm
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 0 < 1 - 1 / (p:ℝ) := by
    have : 1 / (p:ℝ) < 1 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  rw [neg_neg, Real.exp_log this]

lemma log_fact_le (t : ℕ) (ht : 1 ≤ t) :
    Real.log (t.factorial) ≤ ((t:ℝ)+1) * Real.log t - t + 1 := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    have htp : (0:ℝ) < t := by exact_mod_cast ht
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.one_sub_inv_le_log_of_pos (x := ((t:ℝ)+1)/t) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h1
    have h2 : 1 - (t:ℝ) / (t+1) = 1 / (t+1) := by field_simp; ring
    rw [h2] at h1
    have h3 : 1 ≤ ((t:ℝ)+1) * (Real.log (t+1) - Real.log t) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    push_cast
    nlinarith

lemma sum_div_log_le (t : ℕ) :
    ∑ p ∈ (range (t+1)).filter Nat.Prime, ((t / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (t.factorial) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s := (range (t+1)).filter Nat.Prime) ?_ ?_)
  · apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
    rw [Nat.factorization_factorial hpp (Nat.lt_succ_of_le (Nat.log_le_self p t))]
    have h1 : 1 ∈ Ico 1 (t+1) := by
      simp only [mem_Ico]; have := hpp.two_le; omega
    have := Finset.single_le_sum (f := fun i => t / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simp only [pow_one] at this
    exact_mod_cast this
  · intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    rw [Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨hpp, Nat.dvd_factorial hpp.pos hpt, Nat.factorial_ne_zero t⟩
  · intro p _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

lemma theta_le (t : ℕ) :
    ∑ p ∈ (range (t+1)).filter Nat.Prime, Real.log p ≤ 2 * Real.log 2 * t := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg t)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range] at h
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [this] at h
  linarith

lemma log_aux (t : ℝ) (ht : 64 ≤ t) : Real.log t + 1 ≤ t / 12 := by
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have h1 := Real.log_le_sub_one_of_pos (x := t / 64) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num), h64] at h1
  have := Real.log_two_lt_d9
  linarith

lemma mertens1 (t : ℕ) (ht : 64 ≤ t) : Sm t ≤ Real.log t + cM := by
  have htr : (64:ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t:ℝ) * Sm t ≤ ∑ p ∈ (range (t+1)).filter Nat.Prime,
      (((t / p : ℕ) : ℝ) * Real.log p + Real.log p) := by
    unfold Sm
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp2 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hlt := Nat.lt_mul_div_succ t hpp.pos
    have hle : (t:ℝ) ≤ p * (((t / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt.le
    have : (t:ℝ) / p ≤ ((t / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp2]; linarith
    have hl := Real.log_natCast_nonneg p
    calc (t:ℝ) * (Real.log p / p) = ((t:ℝ) / p) * Real.log p := by ring
      _ ≤ (((t / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right this hl
      _ = _ := by ring
  rw [sum_add_distrib] at h1
  have h2 := sum_div_log_le t
  have h3 := theta_le t
  have h4 := log_fact_le t (by omega)
  have h5 := log_aux t htr
  have htp : (0:ℝ) < t := by linarith
  have key : (t:ℝ) * Sm t ≤ t * (Real.log t + cM) := by
    unfold cM; nlinarith
  exact le_of_mul_le_mul_left key htp

lemma key_ineq (a b u : ℝ) (ha : 0 < a) (hab : a < b) (hu : -a ≤ u) :
    u / b - Real.log b ≤ u / a - Real.log a := by
  have hb : 0 < b := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (x := b / a) (by positivity)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have e1 : u / b - u / a = -(u * (b - a)) / (a * b) := by field_simp; ring
  have e2 : 1 - a / b = (b - a) / b := by field_simp
  have h2 : -(u * (b - a)) / (a * b) ≤ (b - a) / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    have : 0 < b - a := by linarith
    have : -u * (b - a) ≤ a * (b - a) := mul_le_mul_of_nonneg_right (by linarith) this.le
    nlinarith
  linarith

lemma H_step (m : ℕ) (hm : 64 ≤ m) : Hm (m+1) ≤ Hm m := by
  have hS := mertens1 m hm
  have hmr : (64:ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 < Real.log m := Real.log_pos (by linarith)
  have hab : Real.log m < Real.log ((m:ℝ)+1) := Real.log_lt_log (by linarith) (by linarith)
  have hb : 0 < Real.log ((m:ℝ)+1) := by linarith
  have K := key_ineq _ _ (cM - Sm m) ha hab (by linarith)
  have hD : -Real.log (1 - 1 / ((m:ℝ)+1)) ≤ 1 / m := by
    have e : 1 - 1 / ((m:ℝ)+1) = ((m:ℝ)+1)⁻¹ * m := by field_simp; ring
    have := Real.log_le_sub_one_of_pos (x := ((m:ℝ)+1) / m) (by positivity)
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_inv]
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e2 : ((m:ℝ)+1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have hinv : 1 / ((m:ℝ)+1) ≤ 1 / m := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hinv0 : 0 ≤ 1 / ((m:ℝ)+1) := by positivity
  have ea : (Real.log m + cM - Sm m) / Real.log m = 1 + (cM - Sm m) / Real.log m := by
    field_simp; ring
  unfold Hm
  rw [Lm_succ, Sm_succ]
  push_cast
  rw [ea]
  split_ifs
  · have eb : (Real.log ((m:ℝ)+1) + cM - (Sm m + Real.log ((m:ℝ)+1) / ((m:ℝ)+1)))
        / Real.log ((m:ℝ)+1) = 1 + (cM - Sm m) / Real.log ((m:ℝ)+1) - 1 / ((m:ℝ)+1) := by
      field_simp; ring
    rw [eb]; linarith
  · have eb : (Real.log ((m:ℝ)+1) + cM - (Sm m + 0))
        / Real.log ((m:ℝ)+1) = 1 + (cM - Sm m) / Real.log ((m:ℝ)+1) := by
      field_simp; ring
    rw [eb]; linarith

lemma H_le (n : ℕ) (hn : 64 ≤ n) : Hm n ≤ Hm 64 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (H_step n hn) ih

lemma log_ge (p q m : ℕ) (hq : 0 < q) (h : 2 ^ m ≤ p ^ q) :
    (m:ℝ) / q * Real.log 2 ≤ Real.log p := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; rw [zero_pow hq.ne'] at h; have := Nat.one_le_two_pow (n := m); omega
    · exact h0
  have : (m:ℝ) * Real.log 2 ≤ q * Real.log p := by
    rw [← Real.log_pow, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h
  rw [div_mul_eq_mul_div, div_le_iff₀ hq']
  linarith

lemma filt64 : (Finset.range 65).filter Nat.Prime =
    {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61} := by decide

lemma Q64 : Qm 64 = 770527199232000/5855632691117327 := by
  unfold Qm
  rw [filt64]
  norm_num [prod_insert]

lemma S64 : (419/100 : ℝ) * Real.log 2 ≤ Sm 64 := by
  unfold Sm
  rw [filt64]
  norm_num [sum_insert]
  have h3 := log_ge 3 2 3 (by norm_num) (by norm_num)
  have h5 := log_ge 5 4 9 (by norm_num) (by norm_num)
  have h7 := log_ge 7 4 11 (by norm_num) (by norm_num)
  have h11 := log_ge 11 3 10 (by norm_num) (by norm_num)
  have h13 := log_ge 13 3 11 (by norm_num) (by norm_num)
  have h17 := log_ge 17 1 4 (by norm_num) (by norm_num)
  have h19 := log_ge 19 1 4 (by norm_num) (by norm_num)
  have h23 := log_ge 23 2 9 (by norm_num) (by norm_num)
  have h29 := log_ge 29 4 19 (by norm_num) (by norm_num)
  have h31 := log_ge 31 4 19 (by norm_num) (by norm_num)
  have h37 := log_ge 37 1 5 (by norm_num) (by norm_num)
  have h41 := log_ge 41 3 16 (by norm_num) (by norm_num)
  have h43 := log_ge 43 3 16 (by norm_num) (by norm_num)
  have h47 := log_ge 47 2 11 (by norm_num) (by norm_num)
  have h53 := log_ge 53 3 17 (by norm_num) (by norm_num)
  have h59 := log_ge 59 4 23 (by norm_num) (by norm_num)
  have h61 := log_ge 61 4 23 (by norm_num) (by norm_num)
  norm_num at h3 h5 h7 h11 h13 h17 h19 h23 h29 h31 h37 h41 h43 h47 h53 h59 h61
  have := Real.log_two_gt_d9
  linarith

lemma H64 : Hm 64 ≤ Real.log 3 := by
  have hL : Lm 64 = -Real.log (Qm 64) := by
    rw [Qm_eq_exp, Real.log_exp]; ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hℓ : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have hℓpos : 0 < Real.log 64 := by rw [hℓ]; linarith
  have hS := S64
  have hX : (Real.log 64 + cM - Sm 64) / Real.log 64 ≤ 0.44 - 1/64 := by
    rw [div_le_iff₀ hℓpos]; unfold cM; rw [hℓ]; linarith
  have hE : Real.exp 0.44 ≤ 3 * Real.log 64 * (770527199232000/5855632691117327) := by
    have e : Real.exp (0.44:ℝ) = Real.exp 0.055 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 0.055 ≤ 1 / (1 - 0.055) :=
      Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    have h2 : Real.exp 0.055 ^ 8 ≤ (1 / (1 - 0.055)) ^ 8 :=
      pow_le_pow_left₀ (Real.exp_pos _).le h1 8
    rw [e, hℓ]
    norm_num at h2 ⊢
    linarith
  have hlog : (0.44:ℝ) ≤ Real.log 3 + Real.log (Real.log 64)
      + Real.log (770527199232000/5855632691117327) := by
    have := Real.log_le_log (Real.exp_pos _) hE
    rw [Real.log_exp, Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by norm_num) hℓpos.ne'] at this
    exact this
  unfold Hm
  rw [hL, Q64]
  simp only [Nat.cast_ofNat]
  linarith

lemma big (n : ℕ) (hn : 64 ≤ n) : 1 / (3 * Real.log n) ≤ Qm n := by
  have hH := le_trans (H_le n hn) H64
  have hS := mertens1 n hn
  have hnr : (64:ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hnn : 0 ≤ (Real.log n + cM - Sm n) / Real.log n := div_nonneg (by linarith) hlogpos.le
  have h1n : 0 ≤ 1 / (n:ℝ) := by positivity
  have hL : Lm n ≤ Real.log 3 + Real.log (Real.log n) := by unfold Hm at hH; linarith
  rw [Qm_eq_exp]
  have e : 1 / (3 * Real.log n) = Real.exp (-(Real.log 3 + Real.log (Real.log n))) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hlogpos]
    rw [one_div]
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

lemma small (a b : ℕ) (qb r : ℝ) (hQ : Qm b = qb) (hr : r ≤ Real.log a) (hrpos : 0 < r)
    (h : 1 ≤ 3 * r * qb) (n : ℕ) (han : a ≤ n) (hnb : n ≤ b) :
    1 / (3 * Real.log n) ≤ Qm n := by
  have ha : (a:ℝ) ≤ n := by exact_mod_cast han
  have hapos : 0 < (a:ℝ) := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; simp at hr; linarith
    · exact_mod_cast h0
  have hlog : Real.log a ≤ Real.log n := Real.log_le_log hapos ha
  calc 1 / (3 * Real.log n) ≤ 1 / (3 * r) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ ≤ qb := by rw [div_le_iff₀ (by positivity)]; linarith
    _ = Qm b := hQ.symm
    _ ≤ Qm n := Qm_anti n b hnb

lemma Q4 : Qm 4 = 1/3 := by
  unfold Qm
  rw [show (Finset.range (4+1)).filter Nat.Prime = {2,3} by decide]
  norm_num [prod_insert]

lemma Q10 : Qm 10 = 8/35 := by
  unfold Qm
  rw [show (Finset.range (10+1)).filter Nat.Prime = {2,3,5,7} by decide]
  norm_num [prod_insert]

lemma Q42 : Qm 42 = 19110297600/131710070791 := by
  unfold Qm
  rw [show (Finset.range (42+1)).filter Nat.Prime = {2,3,5,7,11,13,17,19,23,29,31,37,41} by decide]
  norm_num [prod_insert]

lemma main (n : ℕ) (hn : 3 ≤ n) : 1 / (3 * Real.log n) ≤ Qm n := by
  have hl2 := Real.log_two_gt_d9
  rcases le_or_gt n 4 with h4 | h4
  · have := log_ge 3 2 3 (by norm_num) (by norm_num)
    norm_num at this
    exact small 3 4 (1/3) 1.03 Q4 (by push_cast; linarith) (by norm_num) (by norm_num) n hn h4
  rcases le_or_gt n 10 with h10 | h10
  · have := log_ge 5 4 9 (by norm_num) (by norm_num)
    norm_num at this
    exact small 5 10 (8/35) 1.5 Q10 (by push_cast; linarith) (by norm_num) (by norm_num) n
      (by omega) h10
  rcases le_or_gt n 42 with h42 | h42
  · have := log_ge 11 3 10 (by norm_num) (by norm_num)
    norm_num at this
    exact small 11 42 _ 2.3 Q42 (by push_cast; linarith) (by norm_num) (by norm_num) n
      (by omega) h42
  rcases le_or_gt n 64 with h64 | h64
  · have := log_ge 43 3 16 (by norm_num) (by norm_num)
    norm_num at this
    exact small 43 64 _ 3 Q64 (by push_cast; linarith) (by norm_num) (by norm_num) n
      (by omega) h64
  exact big n h64.le

end OMA_M3




namespace GainVariable687
open Filter Transfert687
open scoped BigOperators Asymptotics
open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

noncomputable def top (d : ℝ) (x : ℕ) := (x:ℝ) / (Real.log x)^d
noncomputable def length (d : ℝ) (x : ℕ) := ⌊(top d x)^2 / (Real.log (top d x))^2⌋₊

private theorem scales {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) {x : ℕ}
    (hl : 4 ≤ Real.log (x:ℝ)) (hx : 0 < x) :
    2 ≤ top d x ∧ top d x ≤ x ∧
    Real.log (top d x) = Real.log x - d*Real.log (Real.log x) ∧
    Real.log (x:ℝ)/2 ≤ Real.log (top d x) := by
  let L := Real.log (x:ℝ)
  have hl' : 4 ≤ L := hl
  have hpos : 0 < L := by linarith
  have hxp : (0:ℝ) < x := by exact_mod_cast hx
  have hz : 0 < top d x := div_pos hxp (Real.rpow_pos_of_pos hpos _)
  have hlog : Real.log (top d x) = L - d*Real.log L := by
    rw [top, Real.log_div hxp.ne' (Real.rpow_pos_of_pos hpos _).ne', Real.log_rpow hpos]
  have lower : L/2 ≤ Real.log (top d x) := by
    rw [hlog]
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    linarith [mul_le_mul_of_nonneg_right hhalf hlogL, Real.log_le_sub_one_of_pos hpos]
  refine ⟨(Real.log_le_log_iff (by norm_num) hz).mp ?_,
    div_le_self hxp.le (Real.one_le_rpow (by linarith) hd.le), hlog, lower⟩
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]

theorem reciprocal_band {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE, (1:ℝ)/p) ≤
        3*d*Real.log (Real.log x) / Real.log x := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hinf.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp hinf).eventually_ge_atTop
    (20/d), eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  obtain ⟨hz,hzx,hlog,hlower⟩ := scales hd hhalf hL hx
  let S := ∑ p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE, (1:ℝ)/p
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hband := Harmonique687.band_bound hz hzx
  change Real.log (top d x) * S ≤ Real.log x - Real.log (top d x) + 10 at hband
  have hlim : 20 ≤ Real.log (Real.log x)*d := (div_le_iff₀ hd).1 hLL
  have hb : Real.log (top d x)*S ≤ d*Real.log (Real.log x)+10 := by linarith only [hband,hlog]
  change S ≤ _ / Real.log x
  apply (le_div_iff₀ (by change 4 ≤ Real.log (x:ℝ) at hL; linarith)).2
  nlinarith only [hb, mul_le_mul_of_nonneg_right hlower hs, hlim]

theorem block_scale {d : ℝ} (hd : 0 < d) (hhalf : d ≤ 1/2) :
    (fun x => (length d x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2 / (Real.log x)^(2+2*d)) := by
  apply Asymptotics.IsBigO.of_bound 4
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hinf.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ)] with x hL hx
  obtain ⟨_,_,_,hlower⟩ := scales hd hhalf hL hx
  let L := Real.log (x:ℝ)
  have hl : 0 < L := by change 4 ≤ L at hL; linarith
  have eqpow : L^(2+2*d) = (L^d)^2 * L^2 := by
    rw [show 2+2*d = d*2+2 by ring, Real.rpow_add hl, Real.rpow_mul hl.le]
    norm_num
  have h := calc
    (length d x : ℝ) ≤ (top d x)^2 / (Real.log (top d x))^2 := Nat.floor_le (by positivity)
    _ ≤ (top d x)^2 / (L/2)^2 := by gcongr
    _ = 4 * ((x:ℝ)^2 / L^(2+2*d)) := by
      rw [eqpow]
      change ((x:ℝ)/L^d)^2/(L/2)^2 = _
      field_simp
      ring
  change ‖(length d x : ℝ)‖ ≤ 4 * ‖(x:ℝ)^2 / L^(2+2*d)‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (length d x : ℝ) by positivity),
    abs_of_nonneg (show 0 ≤ (x:ℝ)^2 / L^(2+2*d) by positivity)] using h

noncomputable def classUnit (d : ℝ) (x : ℕ) := (length d x : ℝ) / Real.log x
noncomputable def stockUnit (d : ℝ) (x : ℕ) :=
  classUnit d x * (Real.log (Real.log x) / Real.log x)

def stockBound (c d : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ a, c * stockUnit d x ≤
    ((survivors ⌊top d x⌋₊ (length d x) a).card : ℝ)

def progressionBound (K d : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ a p, p ∈ x.primesLE \ (⌊top d x⌋₊).primesLE →
    (charge (survivors ⌊top d x⌋₊ (length d x) a) a p : ℝ) ≤ K*(classUnit d x/p)

/-- Any positive stock constant and finite positive progression constant
    suffice for some fixed logarithmic saving, if the two sieve estimates
    hold at the selected cutoff. The choice does not depend on x. -/
theorem gain_from_sieve_constants {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/2 ∧
    (stockBound c d → progressionBound K d →
     (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
       (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+2*d))) := by
  let d := min (1/2:ℝ) (c/(6*K))
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hhalf : d ≤ 1/2 := min_le_left _ _
  have hdel : 3*d*K < c := by
    have h := (le_div_iff₀ (show 0 < 6*K by positivity)).1 (min_le_right (1/2:ℝ) (c/(6*K)))
    change d*(6*K) ≤ c at h
    linarith
  refine ⟨d,hd,hhalf,?_⟩
  intro stock progression
  unfold stockBound at stock
  unfold progressionBound at progression
  apply Asymptotics.IsBigO.trans _ (block_scale hd hhalf)
  apply Asymptotics.IsBigO.of_bound 1
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [stock, progression, reciprocal_band hd hhalf, hinf.eventually_ge_atTop 4,
    eventually_ge_atTop (1:ℕ)] with x hstock hprog hh hL hx
  obtain ⟨hz,_,_,_⟩ := scales hd hhalf hL hx
  have hl : 0 < Real.log (x:ℝ) := by change 4 ≤ Real.log (x:ℝ) at hL; linarith
  have hll := Real.log_pos (show 1 < Real.log (x:ℝ) by change 4 ≤ Real.log (x:ℝ) at hL; linarith)
  have hzlog : 0 < Real.log (top d x) := Real.log_pos (by linarith)
  have hratio : 1 ≤ (top d x)^2 / (Real.log (top d x))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hzlog)).2
    have h := Real.log_le_sub_one_of_pos (show 0 < top d x by linarith)
    simpa using pow_le_pow_left₀ hzlog.le (show Real.log (top d x) ≤ top d x by linarith) 2
  have hN : 1 ≤ length d x := (Nat.le_floor_iff (by positivity)).2 (by simpa using hratio)
  have hv : 0 < classUnit d x := div_pos (by exact_mod_cast (show 0 < length d x by omega)) hl
  have hw : 0 < stockUnit d x := mul_pos hv (div_pos hll hl)
  have bound : Erdos687.Y x ≤ length d x := by
    apply upper_of_survivor_budget (z := ⌊top d x⌋₊)
    intro a
    let band := x.primesLE \ (⌊top d x⌋₊).primesLE
    let S := survivors ⌊top d x⌋₊ (length d x) a
    change (∑ p ∈ band, charge S a p) < S.card
    have hh' : (∑ p ∈ band, (1:ℝ)/p) ≤ 3*d*Real.log (Real.log x)/Real.log x := hh
    have lt : (∑ p ∈ band, (charge S a p:ℝ)) < (S.card:ℝ) := calc
      _ ≤ ∑ p ∈ band, K*(classUnit d x/p) := Finset.sum_le_sum (hprog a)
      _ = (K*classUnit d x) * (∑ p ∈ band, (1:ℝ)/p) := by
        simp only [Finset.mul_sum, mul_one_div, mul_div_assoc]
      _ ≤ (K*classUnit d x) * (3*d*Real.log (Real.log x)/Real.log x) :=
        mul_le_mul_of_nonneg_left hh' (mul_nonneg hK.le hv.le)
      _ = (3*d*K)*stockUnit d x := by unfold stockUnit; ring
      _ < c * stockUnit d x := mul_lt_mul_of_pos_right hdel hw
      _ ≤ _ := hstock a
    exact_mod_cast lt
  simpa using (show (Erdos687.Y x : ℝ) ≤ (length d x : ℝ) by exact_mod_cast bound)

/-- Uniformity concerns the two constants. The threshold in x can depend
    on d in both input estimates. -/
theorem exists_log_saving
    (stock : ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d)
    (progression : ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → progressionBound K d) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) := by
  obtain ⟨c,hc,hs⟩ := stock
  obtain ⟨K,hK,hp⟩ := progression
  obtain ⟨d,hd,hh,transfer⟩ := gain_from_sieve_constants hc hK
  exact ⟨2*d,by positivity,transfer (hs d hd hh) (hp d hd hh)⟩

end GainVariable687


namespace CribleTransfert687
open Filter Transfert687 GainVariable687 Progressions687
open scoped Asymptotics
open OAI.Erdos970.NumberTheoryLean

theorem index_eq_cutoff (J z : ℕ) (b : ℕ → ℕ) :
    siftedIndices z J b = LargePrimeDeletion.cutoffSurvivors J z b := by
    ext i
    simp only [siftedIndices, Finset.mem_filter, Finset.mem_range, LargePrimeDeletion.mem_cutoffSurvivors]
    constructor
    · rintro ⟨hi,avoid⟩
      exact ⟨hi,fun p hp hpz => avoid p (Nat.mem_primesLE.mpr ⟨hpz,hp⟩)⟩
    · rintro ⟨hi,avoid⟩
      exact ⟨hi,fun p hp => avoid p (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hp).1⟩

theorem index_upper (J z : ℕ) (b : ℕ → ℕ) (h : J ≤ z) :
    ((siftedIndices z J b).card : ℝ) ≤ 255*(1+(J:ℝ)/Real.log J) := by
  rw [index_eq_cutoff]
  exact SquarefreeHarmonic.cutoffSurvivors_le_uniform_log J z b h

/-- This separates the analytic sieve from all rounding questions. -/
theorem charge_upper {N z p : ℕ} (hp : p.Prime) (hzp : z < p) (a : ℕ → ℕ)
    (hJ : N/p+1 ≤ z) :
    (charge (survivors z N a) a p : ℝ) ≤
      255*(1+(↑(N/p+1):ℝ)/Real.log (↑(N/p+1):ℝ)) := by
  obtain ⟨b,hb⟩ := charge_le_index_sieve (N := N) hp hzp a
  exact (show (charge (survivors z N a) a p : ℝ) ≤
    ((siftedIndices z (N/p+1) b).card:ℝ) by exact_mod_cast hb).trans (index_upper _ _ _ hJ)

private theorem length_lower {x : ℕ} {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2)
    (hx : 1 ≤ x) (hL : 4 ≤ Real.log (x:ℝ))
    (hpow : 2*(Real.log (x:ℝ))^4 ≤ Real.sqrt x) (hlz : 0 < Real.log (top d x)) :
    (x:ℝ)*Real.sqrt x ≤ (length d x : ℝ) := by
  let L := Real.log (x:ℝ)
  have hL' : 4 ≤ L := hL
  have hpos : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  have hM : 1 ≤ Real.sqrt x := by
    rw [Real.one_le_sqrt]; exact_mod_cast hx
  have hden : L^d ≤ L := by
    simpa using (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (show d ≤ 1 by linarith))
  have hlow : (x:ℝ)/L ≤ top d x :=
    div_le_div_of_nonneg_left hxpos.le (Real.rpow_pos_of_pos hpos _) hden
  have htop : top d x ≤ x := div_le_self hxpos.le (Real.one_le_rpow (by linarith) hd.le)
  have hlog := Real.log_le_log (div_pos hxpos (Real.rpow_pos_of_pos hpos d)) htop
  change Real.log (top d x) ≤ L at hlog
  have big : 2*(x:ℝ)*Real.sqrt x ≤ ((x:ℝ)/L)^2 / L^2 := by
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (x:ℝ)*Real.sqrt x by positivity)
    have hs := Real.sq_sqrt hxpos.le
    have hprod : 2*(x:ℝ)*Real.sqrt x*L^4 ≤ (x:ℝ)^2 := by
      calc
        _ = ((x:ℝ)*Real.sqrt x)*(2*L^4) := by ring
        _ ≤ ((x:ℝ)*Real.sqrt x)*Real.sqrt x := hp
        _ = (x:ℝ) * (Real.sqrt x)^2 := by ring
        _ = (x:ℝ)^2 := by rw [hs]; ring
    calc
      _ ≤ (x:ℝ)^2/L^4 := (le_div_iff₀ (by positivity)).2 hprod
      _ = _ := by field_simp
  have cmp : ((x:ℝ)/L)^2/L^2 ≤ (top d x)^2/(Real.log (top d x))^2 := by gcongr
  have floorlt := Nat.lt_floor_add_one ((top d x)^2/(Real.log (top d x))^2)
  change _ < (length d x : ℝ)+1 at floorlt
  have h1 : (1:ℝ) ≤ (x:ℝ)*Real.sqrt x :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx) hM
  linarith [big.trans cmp]

/-- A class modulo q can be estimated using any smaller reference modulus p
    between the real cutoff and x. This includes primes q above x. -/
theorem progression_at_reference {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (p q : ℕ), p ≤ x → top d x ≤ (p:ℝ) →
      p ≤ q → q.Prime → ⌊top d x⌋₊ < q →
      (charge (survivors ⌊top d x⌋₊ (length d x) a) a q : ℝ) ≤ 35*(classUnit d x/p) := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have small := (isLittleO_log_rpow_atTop (show 0 < (1/10:ℝ) by norm_num)).bound
    (show (0:ℝ) < 1 by norm_num)
  filter_upwards [hinf.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ),
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop).eventually small]
    with x hL hx hslow
  let L := Real.log (x:ℝ)
  let z := top d x
  let N := length d x
  have hL' : 4 ≤ L := hL
  have hl : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  have hslow' : L ≤ (x:ℝ)^(1/10:ℝ) := by
    change ‖L‖ ≤ 1 * ‖(x:ℝ)^(1/10:ℝ)‖ at hslow
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl.le,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul] using hslow
  have hfifth : L^5 ≤ Real.sqrt x := by
    calc
      _ ≤ ((x:ℝ)^(1/10:ℝ))^5 := pow_le_pow_left₀ hl.le hslow' _
      _ = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, show (1/2:ℝ) = (1/10:ℝ)*5 by norm_num, Real.rpow_mul hxpos.le]
        norm_num
  have hpow : 2*L^4 ≤ Real.sqrt x := by
    calc
      _ ≤ L*L^4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = L^5 := by ring
      _ ≤ _ := hfifth
  have hML : L ≤ Real.sqrt x := by
    have hp : 1 ≤ L^3 := one_le_pow₀ (by linarith)
    have hL4 : L ≤ L^4 := by nlinarith [mul_le_mul_of_nonneg_left hp hl.le]
    linarith [show 0 ≤ L^4 by positivity]
  have hpden := Real.rpow_pos_of_pos hl d
  have hlog : Real.log z = L-d*Real.log L := by
    change Real.log ((x:ℝ)/L^d) = _
    rw [Real.log_div hxpos.ne' hpden.ne', Real.log_rpow hl]
  have hlower : L/2 ≤ Real.log z := by
    rw [hlog]
    linarith [mul_le_mul_of_nonneg_right hh (Real.log_nonneg (show 1 ≤ L by linarith)),
      Real.log_le_sub_one_of_pos hl]
  have hzlog : 2 ≤ Real.log z := by linarith
  have hzpos : 0 < z := div_pos hxpos hpden
  have hz : 2 ≤ z := by linarith [Real.log_le_sub_one_of_pos hzpos]
  have hN : (x:ℝ)*Real.sqrt x ≤ (N:ℝ) := length_lower hd hh hx hL hpow (by linarith)
  have hNup : (N:ℝ) ≤ z^2 / (Real.log z)^2 := Nat.floor_le (by positivity)
  intro a p q px hzpr hpq prime hzp
  change z ≤ (p:ℝ) at hzpr
  have hpr := hzpos.trans_le hzpr
  have ppos : 0 < p := by exact_mod_cast hpr
  let M := (N:ℝ)/p
  let J := N/p+1
  have hMJ : M ≤ (J:ℝ) := (div_le_iff₀ hpr).2 (by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul ppos).1 (Nat.lt_succ_self (N/p))).le)
  have hJM : (J:ℝ) ≤ M+1 := by
    dsimp [J,M]; push_cast
    exact add_le_add Nat.cast_div_le (le_refl (1:ℝ))
  have hMlow : Real.sqrt x ≤ M := (le_div_iff₀ hpr).2 <| calc
    _ ≤ Real.sqrt x*(x:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast px) (by positivity)
    _ = _ := mul_comm _ _
    _ ≤ _ := hN
  have hMup : M ≤ z/2 := (div_le_iff₀ hpr).2 <| calc
    (N:ℝ) ≤ z^2/(Real.log z)^2 := hNup
    _ ≤ z^2/(2:ℝ)^2 := by gcongr
    _ ≤ (z/2)*p := by nlinarith [mul_le_mul_of_nonneg_left hzpr hzpos.le, sq_nonneg z]
  have hJz : J ≤ ⌊z⌋₊ := (Nat.le_floor_iff hzpos.le).2 (by linarith)
  have hlogJ : L/2 ≤ Real.log (J:ℝ) := by
    simpa only [Real.log_sqrt hxpos.le] using Real.log_le_log (Real.sqrt_pos.2 hxpos) (hMlow.trans hMJ)
  have h256 : (256:ℝ) ≤ M := by
    have hfour := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hL' 5
    norm_num at hfour
    linarith
  have hJ256 : 256 ≤ J := by exact_mod_cast (show (256:ℝ) ≤ J by linarith)
  have hquot : (J:ℝ)/Real.log J ≤ (35/17)*(M/L) := calc
    _ ≤ ((35/34)*M)/(L/2) := by gcongr; linarith
    _ = _ := by ring
  obtain ⟨b,hb⟩ := charge_le_index_sieve (N := N) prime hzp a
  have incl : siftedIndices ⌊z⌋₊ (N/q+1) b ⊆ siftedIndices ⌊z⌋₊ J b := by
    intro i hi
    obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hI).trans_le (Nat.add_le_add_right (Nat.div_le_div_left hpq ppos) 1)),avoid⟩
  have embedded := hb.trans (Finset.card_le_card incl)
  rw [index_eq_cutoff] at embedded
  have found := SquarefreeHarmonic.cutoffSurvivors_le_seventeen_of_le_cutoff J ⌊z⌋₊ b hJ256 hJz
  calc
    _ ≤ ((LargePrimeDeletion.cutoffSurvivors J ⌊z⌋₊ b).card:ℝ) := by exact_mod_cast embedded
    _ ≤ 17*((J:ℝ)/Real.log J) := by simpa only [mul_div_assoc] using found
    _ ≤ 17*((35/17)*(M/L)) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 35*(M/L) := by ring
    _ = _ := by unfold classUnit; dsimp [M,N,L]; ring

theorem uniform_progression_35 {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    progressionBound 35 d := by
  filter_upwards [progression_at_reference hd hh] with x estimate
  intro a p hp
  obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hin
  have large : ⌊top d x⌋₊ < p := lt_of_not_ge fun h => hout (Nat.mem_primesLE.mpr ⟨h,prime⟩)
  have ref : top d x ≤ (p:ℝ) := (Nat.lt_floor_add_one _).le.trans
    (by exact_mod_cast (show ⌊top d x⌋₊+1 ≤ p by omega))
  exact estimate a p p le ref le_rfl prime large

theorem uniform_progression {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    progressionBound 1275 d := by
  filter_upwards [uniform_progression_35 hd hh] with x h
  intro a p hp
  have nn : 0 ≤ classUnit d x/(p:ℝ) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (Nat.cast_nonneg _)
  exact (h a p hp).trans (mul_le_mul_of_nonneg_right (by norm_num) nn)

/-- Only the uniform lower-sieve stock estimate remains. -/
theorem gain_from_stock
    (stock : ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  exists_log_saving stock ⟨35, by norm_num, fun _ hd hh => uniform_progression_35 hd hh⟩

end CribleTransfert687


namespace StockSource687
open Filter GainVariable687 Transfert687
open scoped Asymptotics BigOperators
open OAI.Erdos970.NumberTheoryLean

noncomputable def width (z : ℝ) : ℝ := Real.log z / (Real.log (Real.log z))^2
noncomputable def height (z : ℝ) : ℕ := ⌊z^2 / (Real.log z)^2⌋₊
noncomputable def scale (z : ℝ) : ℝ := Real.log z / Real.log (width z)

/-- The published quantitative input, with the authors' zero-based
cutoff-survivor set. The Euler product runs through floor(width z). -/
def sourceStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c * ((height z : ℝ) * OMA_M3.Qm ⌊width z⌋₊ / (scale z)^2) ≤
      ((LargePrimeDeletion.cutoffSurvivors (height z) ⌊z⌋₊ a).card : ℝ)

private theorem shift_survivors (N z : ℕ) (a : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, (LargePrimeDeletion.cutoffSurvivors N z b).card ≤ (survivors z N a).card := by
  let b (p : ℕ) := a p + p - 1
  refine ⟨b, Finset.card_le_card_of_injOn (fun i : ℕ => i+1) ?_ ?_⟩
  · intro i hi
    obtain ⟨hiN,avoid⟩ := LargePrimeDeletion.mem_cutoffSurvivors.mp hi
    change i+1 ∈ survivors z N a
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.succ_pos i,hiN⟩,?_⟩
    intro p hp he
    obtain ⟨hpz,prime⟩ := Nat.mem_primesLE.mp hp
    have pos := prime.pos
    have translate : (b p+1) ≡ a p [MOD p] := by
      have eqn : b p+1 = a p+p := by dsimp [b]; omega
      rw [eqn]
      change (a p+p)%p = a p%p
      simp
    exact avoid p prime hpz (Nat.ModEq.add_right_cancel' 1 ((show i+1 ≡ a p [MOD p] from he).trans translate.symm))
  · intro i _ j _ he
    exact Nat.add_right_cancel he

private theorem width_eventually :
    ∀ᶠ z : ℝ in atTop, 3 ≤ ⌊width z⌋₊ ∧ Real.log (Real.log z)/2 ≤ Real.log (width z) := by
  have hu : Tendsto (fun z : ℝ => Real.log (Real.log z)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have small := Real.isLittleO_log_id_atTop.bound (show 0 < (1/4:ℝ) by norm_num)
  filter_upwards [hu.eventually_ge_atTop 8, hu.eventually small,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hlarge hs ht
  let t := Real.log z
  let u := Real.log t
  change 8 ≤ u at hlarge
  change 2 ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hb : Real.log u ≤ (1/4:ℝ)*u := by
    change ‖Real.log u‖ ≤ (1/4:ℝ)*‖u‖ at hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlogu,abs_of_nonneg hu0.le] using hs
  have hw : Real.log (width z) = u - 2*Real.log u := by
    change Real.log (t/u^2) = _
    rw [Real.log_div ht0.ne' (pow_pos hu0 _).ne',Real.log_pow]
    rfl
  have wp : 0 < width z := div_pos ht0 (pow_pos hu0 _)
  have h3 : (3:ℝ) ≤ width z := by linarith [Real.log_le_sub_one_of_pos wp]
  exact ⟨(Nat.le_floor_iff wp.le).2 (by simpa using h3),by change u/2 ≤ _; linarith⟩

/-- A real-cutoff estimate, before composing with any exponent d. -/
theorem normalize_source (h : sourceStatement) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
      c * ((height z:ℝ) * Real.log (Real.log z) / (Real.log z)^2) ≤
        ((survivors ⌊z⌋₊ (height z) a).card:ℝ) := by
  obtain ⟨c,hc,hs⟩ := h
  refine ⟨c/6,by positivity,?_⟩
  filter_upwards [hs,width_eventually,Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hz hw ht
  intro a
  let w := width z
  have hw' : (3:ℝ) ≤ (⌊w⌋₊:ℝ) := by exact_mod_cast hw.1
  have wp : 0 ≤ w := (Nat.cast_nonneg ⌊w⌋₊).trans (Nat.floor_le (by
    change 0 ≤ Real.log z / _; exact div_nonneg (by linarith) (sq_nonneg _)))
  have floorle : (⌊w⌋₊:ℝ) ≤ w := Nat.floor_le wp
  have hlogf : 0 < Real.log (⌊w⌋₊:ℝ) := Real.log_pos (by linarith)
  have ht' : 0 < Real.log z := by linarith
  have hfw := Real.log_le_log (show (0:ℝ) < ⌊w⌋₊ by linarith) floorle
  have hlw : 0 < Real.log w := hlogf.trans_le hfw
  have euler : 1/(3*Real.log w) ≤ OMA_M3.Qm ⌊w⌋₊ :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)).trans (OMA_M3.main _ hw.1)
  obtain ⟨b,shift⟩ := shift_survivors (height z) ⌊z⌋₊ a
  have en : (0:ℝ) ≤ height z := by positivity
  have positive : 0 ≤ Real.log (Real.log z) := Real.log_nonneg (by linarith)
  have lower : (height z:ℝ) * Real.log (Real.log z) / (6 * (Real.log z)^2) ≤
        (height z:ℝ) * OMA_M3.Qm ⌊w⌋₊ / (scale z)^2 := calc
    _ ≤ (height z:ℝ) * (2*Real.log w) / (6*(Real.log z)^2) := by
      gcongr; linarith [hw.2]
    _ = (height z:ℝ) * (1/(3*Real.log w)) / (scale z)^2 := by
      change _ = _ / (Real.log z / Real.log w)^2
      field_simp
      ring
    _ ≤ _ := by gcongr
  calc
    _ = c*((height z:ℝ)*Real.log (Real.log z)/(6*(Real.log z)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower hc.le
    _ ≤ _ := hz b
    _ ≤ _ := by exact_mod_cast shift

private theorem cutoff_properties {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, 0 < Real.log (top d x) ∧ Real.log (top d x) ≤ Real.log x ∧
      Real.log x/2 ≤ Real.log (top d x) ∧ Real.log (Real.log x)/2 ≤ Real.log (Real.log (top d x)) := by
  have ht : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 4,
    eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  let L := Real.log (x:ℝ)
  change 4 ≤ L at hL
  change 4 ≤ Real.log L at hLL
  have hl : 0 < L := by linarith
  have hp : 0 < (x:ℝ) := by exact_mod_cast hx
  have he : Real.log (top d x) = L-d*Real.log L := by
    rw [top,Real.log_div hp.ne' (Real.rpow_pos_of_pos hl d).ne', Real.log_rpow hl]
  have hlo : L/2 ≤ Real.log (top d x) := by
    rw [he]
    linarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ Real.log L by linarith),Real.log_le_sub_one_of_pos hl]
  have hhi : Real.log (top d x) ≤ L := by rw [he]; nlinarith [mul_nonneg hd.le (show 0 ≤ Real.log L by linarith)]
  have loglo := Real.log_le_log (show 0 < L/2 by positivity) hlo
  rw [Real.log_div hl.ne' (by norm_num)] at loglo
  exact ⟨by linarith,hhi,hlo,by change Real.log L/2 ≤ _; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]⟩

theorem stock_of_published (h : sourceStatement) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d := by
  obtain ⟨c,hc,hs⟩ := normalize_source h
  refine ⟨c/2,by positivity,?_⟩
  intro d hd hh
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcut := cutoff_properties hd hh
  have htop : Tendsto (top d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hcut,hinf.eventually_ge_atTop (2*b),eventually_ge_atTop (1:ℕ),
      hinf.eventually_ge_atTop 2] with x h hL hx hpos
    have hp : 0 < top d x := div_pos (by exact_mod_cast hx) (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (x:ℝ)) _)
    change 2*b ≤ Real.log (x:ℝ) at hL
    linarith [h.2.2.1, Real.log_le_sub_one_of_pos hp]
  unfold stockBound
  filter_upwards [htop.eventually hs,hcut,hinf.eventually_ge_atTop 2] with x h hcmp hL
  intro a
  let L := Real.log (x:ℝ)
  let t := Real.log (top d x)
  let N := length d x
  have hl : 0 < L := by change 2 ≤ L at hL; linarith
  have hll : 0 ≤ Real.log L := Real.log_nonneg (by change 2 ≤ L at hL; linarith)
  have ht : 0 < t := hcmp.1
  have htl : t ≤ L := hcmp.2.1
  have hllt : Real.log L/2 ≤ Real.log t := hcmp.2.2.2
  have hlogt : 0 ≤ Real.log t := by linarith
  have hstock := h a
  change c*((N:ℝ)*Real.log t/t^2) ≤ _ at hstock
  calc
    _ = c*((N:ℝ)*(Real.log L/2)/L^2) := by unfold stockUnit classUnit; dsimp [N,L]; ring
    _ ≤ c*((N:ℝ)*Real.log t/t^2) := by gcongr
    _ ≤ _ := hstock

/-- The complete transfer from the quantitative source bound to the upper
bound on the official Y. The existence of a matching lower bound is separate. -/
theorem gain_of_published (h : sourceStatement) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  CribleTransfert687.gain_from_stock (stock_of_published h)

theorem source_of_interface (h : InterfaceSource687.statement) : sourceStatement := by
  have agree (N z : ℕ) (a : ℕ → ℕ) : InterfaceSource687.remaining N z a =
      LargePrimeDeletion.cutoffSurvivors N z a := by
    classical
    ext i
    simp only [InterfaceSource687.remaining,InterfaceSource687.primes,
      LargePrimeDeletion.cutoffSurvivors,LargePrimeDeletion.cutoffPrimes,
      SievePartition.survivors,SievePartition.residueBad,Finset.mem_filter]
  simpa only [sourceStatement,height,width,scale,OMA_M3.Qm,
    InterfaceSource687.statement,InterfaceSource687.height,InterfaceSource687.width,
    InterfaceSource687.scale,InterfaceSource687.product,InterfaceSource687.primes,agree] using h

theorem gain_of_interface (h : InterfaceSource687.statement) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  gain_of_published (source_of_interface h)

end StockSource687


open Filter in
theorem erdos687_log_saving :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  StockSource687.gain_of_interface SourcePubliee687.source_bound

#print axioms erdos687_log_saving

namespace Erdos970
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}
end Erdos970

namespace SurvieTotale687
open Filter Transfert687 GainVariable687

def remaining (S P : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ := by
  classical
  exact S.filter fun n => ∀ p ∈ P, n%p ≠ a p%p

theorem finite_loss (S P : Finset ℕ) (a : ℕ → ℕ) :
    S.card ≤ (remaining S P a).card + ∑ p ∈ P, charge S a p := by
  classical
  let C (p : ℕ) := S.filter fun n => n%p=a p%p
  have incl : S ⊆ remaining S P a ∪ P.biUnion C := by
    intro n hn
    by_cases h : ∀ p ∈ P, n%p ≠ a p%p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,h⟩)
    · push Not at h
      obtain ⟨p,hp,e⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hn,e⟩⟩)
  exact (Finset.card_le_card incl).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_biUnion_le _))

private theorem band_remaining {z x N : ℕ} (h : z ≤ x) (a : ℕ → ℕ) :
    remaining (survivors z N a) (x.primesLE \ z.primesLE) a = survivors x N a := by
  classical
  ext i
  simp only [remaining,survivors,Finset.mem_filter,Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hi,old⟩,newer⟩
    refine ⟨hi,?_⟩
    intro p hp
    by_cases hm : p ∈ z.primesLE
    · exact old p hm
    · exact newer p ⟨hp,hm⟩
  · rintro ⟨hi,avoid⟩
    refine ⟨⟨hi,fun p hp => avoid p ?_⟩,fun p hp => avoid p hp.1⟩
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans h,prime⟩

/-- A uniform positive stock persists after adjoining up to x/log x further
    prime classes. Those primes can have arbitrarily large moduli. -/
theorem robust_stock (source : InterfaceSource687.statement) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/2 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (E : Finset ℕ),
        (∀ p ∈ E, x < p ∧ p.Prime) → (E.card:ℝ) ≤ (x:ℝ)/Real.log x →
        c*stockUnit d x ≤ ((remaining (survivors x (length d x) a) E a).card:ℝ) := by
  classical
  obtain ⟨c,hc,hs⟩ := StockSource687.stock_of_published (StockSource687.source_of_interface source)
  let d := min (1/2:ℝ) (c/210)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hh : d ≤ 1/2 := min_le_left _ _
  have delta : 210*d ≤ c := by
    have := min_le_right (1/2:ℝ) (c/210)
    dsimp [d]; linarith
  refine ⟨d,hd,hh,c/4,by positivity,?_⟩
  have tends : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs d hd hh,CribleTransfert687.uniform_progression_35 hd hh,
    CribleTransfert687.progression_at_reference hd hh,reciprocal_band hd hh,
    tends.eventually_ge_atTop 4,(Real.tendsto_log_atTop.comp tends).eventually_ge_atTop (140/c),
    eventually_ge_atTop (1:ℕ)] with x hstock hband hlarge hmass hL hll hx
  intro a E hE size
  let L := Real.log (x:ℝ)
  let V := classUnit d x
  let W := stockUnit d x
  let z := ⌊top d x⌋₊
  let N := length d x
  let S := survivors z N a
  let T := survivors x N a
  let P := x.primesLE \ z.primesLE
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have Lp : 0 < L := by change 4 ≤ L at hL; linarith
  have LLp : 0 ≤ Real.log L := Real.log_nonneg (by change 4 ≤ L at hL; linarith)
  have Vn : 0 ≤ V := div_nonneg (Nat.cast_nonneg _) Lp.le
  have Wn : 0 ≤ W := mul_nonneg Vn (div_nonneg LLp Lp.le)
  have top_le : top d x ≤ (x:ℝ) := div_le_self xp.le (Real.one_le_rpow (by change 4 ≤ L at hL; linarith) hd.le)
  have zle : z ≤ x := Nat.floor_le_of_le top_le
  have incl : T ⊆ S := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hi,fun p hp => avoid p ?_⟩
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans zle,prime⟩
  have loss1 : (∑ p ∈ P, (charge S a p:ℝ)) ≤ (c/2)*W := calc
    _ ≤ ∑ p ∈ P, 35*(V/p) := Finset.sum_le_sum (hband a)
    _ = (35*V)*(∑ p ∈ P, (1:ℝ)/p) := by simp only [Finset.mul_sum,mul_one_div,mul_div_assoc]
    _ ≤ (35*V)*(3*d*Real.log L/L) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (105*d)*W := by dsimp [W,stockUnit,V,L]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) Wn
  have loss2 : (∑ p ∈ E, (charge T a p:ℝ)) ≤ (c/4)*W := calc
    _ ≤ ∑ _p ∈ E, 35*(V/x) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨gt,prime⟩ := hE p hp
      have mono : charge T a p ≤ charge S a p :=
        Finset.card_le_card (Finset.filter_subset_filter _ incl)
      exact (show (charge T a p:ℝ) ≤ charge S a p by exact_mod_cast mono).trans
        (hlarge a x p le_rfl top_le gt.le prime (zle.trans_lt gt))
    _ = (E.card:ℝ)*(35*(V/x)) := by simp
    _ ≤ ((x:ℝ)/L)*(35*(V/x)) := mul_le_mul_of_nonneg_right size (by positivity)
    _ = 35*(V/L) := by field_simp
    _ ≤ (c/4)*W := by
      have scale : 140 ≤ c*Real.log L := by
        change 140/c ≤ Real.log L at hll
        linarith [(div_le_iff₀ hc).1 hll]
      have aux := mul_le_mul_of_nonneg_right (show 35 ≤ c/4*Real.log L by linarith) (div_nonneg Vn Lp.le)
      calc
        _ ≤ (c/4*Real.log L)*(V/L) := aux
        _ = (c/4)*W := by change _ = (c/4)*(V*(Real.log L/L)); ring
  have f1 := finite_loss S P a
  change S.card ≤ (remaining (survivors z N a) (x.primesLE \ z.primesLE) a).card + _ at f1
  rw [band_remaining zle] at f1
  have b1 : (S.card:ℝ) ≤ T.card + ∑ p ∈ P, (charge S a p:ℝ) := by exact_mod_cast f1
  have b2 : (T.card:ℝ) ≤ (remaining T E a).card + ∑ p ∈ E, (charge T a p:ℝ) := by
    exact_mod_cast finite_loss T E a
  have start : c*W ≤ (S.card:ℝ) := hstock a
  change c/4*W ≤ ((remaining T E a).card:ℝ)
  linarith

theorem stockUnit_pos {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, 0 < stockUnit d x := by
  have tends := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [tends.eventually_ge_atTop 4,eventually_ge_atTop (1:ℕ)] with x hL hx
  let L := Real.log (x:ℝ)
  change 4 ≤ L at hL
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have lp : 0 < L := by linarith
  have llp : 0 < Real.log L := Real.log_pos (by linarith)
  have zp : 0 < top d x := div_pos xp (Real.rpow_pos_of_pos lp _)
  have logz : Real.log (top d x) = L-d*Real.log L := by
    rw [top,Real.log_div xp.ne' (Real.rpow_pos_of_pos lp d).ne',Real.log_rpow lp]
  have pos : 0 < Real.log (top d x) := by
    rw [logz]
    linarith [mul_le_mul_of_nonneg_right hh llp.le,Real.log_le_sub_one_of_pos lp]
  have hr : 1 ≤ (top d x)^2/(Real.log (top d x))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos pos)).2
    simpa using pow_le_pow_left₀ pos.le
      (show Real.log (top d x) ≤ top d x by linarith [Real.log_le_sub_one_of_pos zp]) 2
  have length_pos : 1 ≤ length d x := (Nat.le_floor_iff (by positivity)).2 (by simpa using hr)
  exact mul_pos (div_pos (by exact_mod_cast length_pos) lp) (div_pos llp lp)

/-- A set of at most x/log x primes of arbitrary size cannot cover this
    length. Extra small prime classes are supplied by the full sieve. -/
theorem arbitrary_primes (source : InterfaceSource687.statement) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/2 ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → (P.card:ℝ) ≤ (x:ℝ)/Real.log x →
      ∀ a : ℕ → ℕ, ∃ i ∈ Finset.Icc 1 (length d x), ∀ p ∈ P, i%p ≠ a p%p := by
  obtain ⟨d,hd,hh,c,hc,stock⟩ := robust_stock source
  refine ⟨d,hd,hh,?_⟩
  filter_upwards [stock,stockUnit_pos hd hh] with x bound pos
  intro P primes size a
  let E := P \ x.primesLE
  have big : ∀ p ∈ E, x < p ∧ p.Prime := by
    intro p hp
    obtain ⟨mem,out⟩ := Finset.mem_sdiff.mp hp
    exact ⟨lt_of_not_ge (fun h => out (Nat.mem_primesLE.mpr ⟨h,primes p mem⟩)),primes p mem⟩
  have small : (E.card:ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card (show E ⊆ P from Finset.sdiff_subset)
  have positive := (mul_pos hc pos).trans_le (bound a E big (small.trans size))
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (by exact_mod_cast positive)
  obtain ⟨inside,extra⟩ := Finset.mem_filter.mp hi
  obtain ⟨interval,old⟩ := Finset.mem_filter.mp inside
  refine ⟨i,interval,?_⟩
  intro p hp
  by_cases h : p ∈ x.primesLE
  · exact old p h
  · exact extra p (Finset.mem_sdiff.mpr ⟨hp,h⟩)

end SurvieTotale687


namespace JacobsthalExtension687
open Filter GainVariable687 Erdos970
open scoped Asymptotics

/-- An interval free of any assigned collection of k prime classes gives
    the signed-interval coprimality condition in the catalog. -/
theorem interval_bound {k N : ℕ}
    (avoids : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k → ∀ a : ℕ → ℕ,
      ∃ i ∈ Finset.Icc 1 N, ∀ p ∈ P, i%p ≠ a p%p) :
    Erdos970.IsJacobsthalBound k N := by
  intro n hn count A
  let a (p : ℕ) := ((1-A) % (p:ℤ)).toNat
  obtain ⟨i,hi,clear⟩ := avoids n.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1) count a
  obtain ⟨lo,hiN⟩ := Finset.mem_Icc.mp hi
  refine ⟨i-1,by omega,Nat.coprime_of_dvd ?_⟩
  intro p prime hit divides
  have mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨prime,divides,hn.ne'⟩
  have pp : (p:ℤ) ≠ 0 := by exact_mod_cast prime.ne_zero
  have lift : (a p:ℤ) = (1-A)%(p:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ pp)
  have residue : (a p:ℤ) ≡ 1-A [ZMOD (p:ℤ)] := by simp [lift,Int.ModEq]
  have hz : (1-A) ≡ (i:ℤ) [ZMOD (p:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    have e : (i:ℤ)-(1-A) = A+((i-1:ℕ):ℤ) := by omega
    rw [e]
    exact Int.ofNat_dvd_left.mpr hit
  exact clear p mem (Int.natCast_modEq_iff.mp (residue.trans hz).symm)

noncomputable def cutoff (k : ℕ) : ℕ := ⌈2*(k:ℝ)*Real.log k⌉₊

private theorem scales :
    ∀ᶠ k : ℕ in atTop, 0 < Real.log k ∧ k ≤ cutoff k ∧
      (cutoff k:ℝ) ≤ 3*k*Real.log k ∧ (k:ℝ) ≤ (cutoff k:ℝ)/Real.log (cutoff k) := by
  have inc : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have small := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/3 by norm_num)
  filter_upwards [inc.eventually small,(Real.tendsto_log_atTop.comp inc).eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with k hs hL hk
  let L := Real.log (k:ℝ)
  change 2 ≤ L at hL
  have kp : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have lp : 0 < L := by linarith
  have hlk : L ≤ (1/3)*(k:ℝ) := by
    change ‖L‖ ≤ (1/3:ℝ)*‖(k:ℝ)‖ at hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg lp.le,abs_of_nonneg kp.le] using hs
  have lo : 2*(k:ℝ)*L ≤ cutoff k := Nat.le_ceil _
  have up : (cutoff k:ℝ) ≤ 3*k*L := by
    have ceil_lt : (cutoff k:ℝ) < 2*k*L+1 := Nat.ceil_lt_add_one (by positivity)
    have kr : (2:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg (sub_nonneg.mpr kr) (sub_nonneg.mpr hL)]
  have kx : k ≤ cutoff k := by
    exact_mod_cast (show (k:ℝ) ≤ cutoff k by nlinarith [mul_nonneg kp.le (sub_nonneg.mpr hL)])
  have xs : (cutoff k:ℝ) ≤ (k:ℝ)^2 := by
    nlinarith [mul_nonneg kp.le (show 0 ≤ (k:ℝ)-3*L by linarith)]
  have logp := Real.log_pos (show (1:ℝ) < cutoff k by exact_mod_cast (by omega : 1 < cutoff k))
  have xu : Real.log (cutoff k) ≤ 2*L := by
    have xpos : (0:ℝ) < cutoff k := kp.trans_le (by exact_mod_cast kx)
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log xpos xs
  refine ⟨lp,kx,up,(le_div_iff₀ logp).2 ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left xu kp.le]

private theorem evolves : Tendsto cutoff atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [scales,eventually_ge_atTop n] with k h hk
  exact hk.trans h.2.1

private theorem scale_bound {d : ℝ} (hd : 0 < d) :
    (fun k : ℕ => (cutoff k:ℝ)^2/(Real.log (cutoff k))^(2+2*d)) =O[atTop]
      (fun k : ℕ => (k:ℝ)^2/(Real.log k)^(2*d)) := by
  apply Asymptotics.IsBigO.of_bound 9
  filter_upwards [scales,eventually_ge_atTop (2:ℕ)] with k h hk
  obtain ⟨lp,kx,xup,_⟩ := h
  have kp : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have logs := Real.log_le_log kp (show (k:ℝ) ≤ cutoff k by exact_mod_cast kx)
  have xp : 0 < Real.log (cutoff k) := lp.trans_le logs
  simp only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (cutoff k:ℝ)^2/(Real.log (cutoff k))^(2+2*d) by positivity),
    abs_of_nonneg (show 0 ≤ (k:ℝ)^2/(Real.log k)^(2*d) by positivity)]
  calc _ ≤ (3*k*Real.log k)^2/(Real.log k)^(2+2*d) := by gcongr
       _ = _ := by
         rw [Real.rpow_add lp,Real.rpow_two]
         field_simp
         ring

/-- The quantitative source bound also yields a power of log k saving on
    general Jacobsthal numbers, for integers with at most k prime divisors. -/
theorem gain (source : InterfaceSource687.statement) :
    ∃ η : ℝ, 0 < η ∧ (fun k : ℕ => (Erdos970.jacobsthalFunction k:ℝ)) =O[atTop]
      (fun k : ℕ => (k:ℝ)^2/(Real.log k)^η) := by
  obtain ⟨d,hd,hh,clean⟩ := SurvieTotale687.arbitrary_primes source
  refine ⟨2*d,by positivity,?_⟩
  have len : (fun k : ℕ => (length d (cutoff k):ℝ)) =O[atTop]
      (fun k : ℕ => (cutoff k:ℝ)^2/(Real.log (cutoff k))^(2+2*d)) :=
    (block_scale hd hh).comp_tendsto evolves
  apply Asymptotics.IsBigO.trans _ (len.trans (scale_bound hd))
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [scales,evolves.eventually clean] with k h sieve
  have bound : Erdos970.IsJacobsthalBound k (length d (cutoff k)) := by
    apply interval_bound
    intro P primes count
    exact sieve P primes ((show (P.card:ℝ) ≤ k by exact_mod_cast count).trans h.2.2.2)
  have endpt : Erdos970.jacobsthalFunction k ≤ length d (cutoff k) := Nat.sInf_le bound
  simpa using (show (Erdos970.jacobsthalFunction k:ℝ) ≤ (length d (cutoff k):ℝ) by exact_mod_cast endpt)

end JacobsthalExtension687


open Filter in
theorem jacobsthal_log_saving :
    ∃ η : ℝ, 0 < η ∧ (fun k : ℕ => (Erdos970.jacobsthalFunction k:ℝ)) =O[atTop]
      (fun k : ℕ => (k:ℝ)^2/(Real.log k)^η) :=
  JacobsthalExtension687.gain SourcePubliee687.source_bound

#print axioms jacobsthal_log_saving
