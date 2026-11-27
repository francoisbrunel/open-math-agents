import SurvieTotale687
import FormalConjectures.ErdosProblems.«970»

/-! A consequence of the strengthened survivor count for arbitrary sets of
    prime divisors, in the catalog's normalization of Jacobsthal's function. -/
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
