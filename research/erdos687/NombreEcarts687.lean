import DilatationCarree687

/-! Uniform exclusion of any bounded number of exceptional prime rows. -/
namespace NombreEcarts687
open Filter Transfert687 StabiliteCarree687
open scoped BigOperators

def cap (K : ℕ) : ℕ → ℕ → ℕ
  | 0,u => u
  | n+1,u => cap K n (K*u*u)

private theorem le_cap {K : ℕ} (hk : 0<K) (n u : ℕ) (hu : 0<u) : u ≤ cap K n u := by
  induction n generalizing u with
  | zero => exact le_rfl
  | succ n ih =>
    have h : u ≤ K*u*u := by
      calc u = 1*1*u := by simp
           _ ≤ K*u*u := by gcongr <;> omega
    exact h.trans (ih _ (by positivity))

private theorem absorb {K : ℕ} (hk : 0<K) (n : ℕ) (E : Finset ℕ)
    (size : E.card ≤ n) (prime : ∀ p ∈ E, Nat.Prime p)
    (d u : ℕ) (hd : 0<d) (hu : d≤u) :
    ∃ D : ℕ, d ∣ D ∧ 0<D ∧ D ≤ cap K n u ∧
      (∀ p, Nat.Prime p → p ∣ D → p ∣ d ∨ p ∈ E) ∧
      (∀ p ∈ E, ¬p ∣ D → K*D < p) := by
  classical
  induction n generalizing E d u with
  | zero =>
    have empty : E=∅ := Finset.card_eq_zero.mp (by omega)
    subst E
    exact ⟨d,dvd_refl _,hd,hu,fun _ _ h => Or.inl h,by simp⟩
  | succ n ih =>
    by_cases done : ∀ p ∈ E, ¬p ∣ d → K*d < p
    · exact ⟨d,dvd_refl _,hd,hu.trans (le_cap hk _ _ (by omega)),fun _ _ h => Or.inl h,done⟩
    push Not at done
    obtain ⟨q,hq,_,small⟩ := done
    have qu : d*q ≤ K*u*u := calc
      _ ≤ d*(K*d) := Nat.mul_le_mul_left _ small
      _ = K*d*d := by ring
      _ ≤ K*u*u := by gcongr
    have sz : (E.erase q).card ≤ n := by rw [Finset.card_erase_of_mem hq]; omega
    obtain ⟨D,div,dp,bu,support,gap⟩ := ih (E.erase q) sz
      (fun p h => prime p (Finset.mem_of_mem_erase h)) (d*q) (K*u*u)
      (Nat.mul_pos hd (prime q hq).pos) qu
    refine ⟨D,dvd_trans (dvd_mul_right d q) div,dp,bu,?_,?_⟩
    · intro p hp hpD
      rcases support p hp hpD with old | inside
      · rcases hp.dvd_mul.mp old with h | h
        · exact Or.inl h
        · rcases (Nat.dvd_prime (prime q hq)).mp h with unit | eq
          · exact (hp.ne_one unit).elim
          · exact Or.inr (eq ▸ hq)
      · exact Or.inr (Finset.mem_of_mem_erase inside)
    · intro p hpe hpD
      have ne : p≠q := by
        intro eq
        subst p
        exact hpD (dvd_trans (dvd_mul_left q d) div)
      exact gap p (Finset.mem_erase.mpr ⟨ne,hpe⟩) hpD

/-- For every prescribed t there is one fixed exponent m such that, at
all sufficiently large k, every complete profile differs from every
local center at more than t primes. Both the center and the primes
may vary with the profile and with k. -/
theorem many_changes (t : ℕ) : ∃ m : ℕ, 2 ≤ m ∧
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
    (∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p=a p%p) →
    ∀ b ∈ Finset.Icc 1 ((k^m)^2), t < (changes (k^m) (fun _ => b) a).card := by
  classical
  let K := 17408*(t+1)
  let B := cap K t 1
  let m := 6144*B
  have kp : 0<K := by dsimp [K]; omega
  have bp : 1≤B := le_cap kp _ _ (by decide)
  have hm : 2 ≤ m := by dsimp [m]; omega
  refine ⟨m,hm,?_⟩
  have allD := (eventually_all_finset (Finset.Icc 1 B)).2 (fun D hD =>
    DilatationCarree687.tail_separation m D hm (Finset.mem_Icc.mp hD).1)
  filter_upwards [allD] with k sep
  intro a full b hb
  let E := changes (k^m) (fun _ => b) a
  change t<E.card
  by_contra! small
  have primes (p : ℕ) (hp : p∈E) := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  obtain ⟨D,_,dp,bound,support,gap⟩ := absorb kp t E small primes 1 1 (by decide) le_rfl
  have different : ∀ p ∈ (k^m).primesLE, p ∣ D → a p%p ≠ b%p := by
    intro p hp hpD
    have pr := (Nat.mem_primesLE.mp hp).2
    rcases support p pr hpD with unit | he
    · exact (pr.not_dvd_one unit).elim
    · exact Ne.symm (Finset.mem_filter.mp he).2
  have separation := sep D (Finset.mem_Icc.mpr ⟨dp,bound⟩) a full b hb different
  let F := E.filter (fun p => ¬p ∣ D)
  have positiveK : 0<(K:ℝ) := by exact_mod_cast kp
  have mass : (D:ℝ)*(∑ p ∈ F, (1:ℝ)/p) ≤ (t:ℝ)/K := calc
    _ = ∑ p ∈ F, (D:ℝ)*(1/p) := Finset.mul_sum _ _ _
    _ ≤ ∑ _p ∈ F, (1:ℝ)/K := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨he,nd⟩ := Finset.mem_filter.mp hp
      have pp : 0<(p:ℝ) := by exact_mod_cast (primes p he).pos
      rw [mul_one_div,div_le_div_iff₀ pp positiveK,one_mul,mul_comm]
      exact_mod_cast (gap p he nd).le
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast
        ((Finset.card_le_card (Finset.filter_subset _ E)).trans small)) positiveK.le
  have tail : (t:ℝ)/K ≤ 1/17408 := by
    apply (div_le_iff₀ positiveK).2
    dsimp [K]; push_cast; linarith
  have main : (D:ℝ)*(24/m) ≤ 1/256 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < (m:ℝ) by exact_mod_cast (show 0 < m by omega))).2
    have br : (D:ℝ) ≤ B := by exact_mod_cast bound
    dsimp only [m]; push_cast; linarith
  change 1/64 ≤ (D:ℝ)*(24/m+68*(∑ p ∈ F, (1:ℝ)/p)) at separation
  nlinarith only [separation,main,mass.trans tail]

end NombreEcarts687
#print axioms NombreEcarts687.many_changes
