import Transfert687

/-! Finite form of the Jacobsthal–least-prime implication (Kanold).
    The variable b can include the starting offset of the progression. -/
namespace ProgressionPremiere687

theorem factor_classes {q b : ℕ} (cop : q.Coprime b) :
    ∃ a : ℕ → ℕ, ∀ n p : ℕ, p.Prime → p ∣ q*n+b → n ≡ a p [MOD p] := by
  classical
  let a (p : ℕ) := if h : ∃ n : ℕ, p ∣ q*n+b then Classical.choose h else 0
  refine ⟨a,?_⟩
  intro n p prime hit
  have exists_hit : ∃ m : ℕ, p ∣ q*m+b := ⟨n,hit⟩
  have chosen : p ∣ q*(a p)+b := by
    simpa only [a,dif_pos exists_hit] using Classical.choose_spec exists_hit
  have unit : p.Coprime q := prime.coprime_iff_not_dvd.mpr (fun pq => by
    have pb : p ∣ b := (Nat.dvd_add_right (dvd_mul_of_dvd_left pq n)).mp hit
    have one := Nat.dvd_gcd pq pb
    rw [cop.gcd_eq_one] at one
    exact prime.not_dvd_one one)
  apply Nat.ModEq.cancel_left_of_coprime unit
  exact Nat.ModEq.add_right_cancel' b
    ((Nat.modEq_zero_iff_dvd.mpr hit).trans (Nat.modEq_zero_iff_dvd.mpr chosen).symm)

theorem cover_of_small_factors {q b x H : ℕ} (cop : q.Coprime b)
    (factors : ∀ n ∈ Finset.Icc 1 H, ∃ p ≤ x, p.Prime ∧ p ∣ q*n+b) :
    H ≤ Erdos687.Y x := by
  obtain ⟨a,classes⟩ := factor_classes cop
  apply Transfert687.le_Y_of_covered
  refine ⟨a,?_⟩
  intro n hn
  obtain ⟨p,bound,prime,hit⟩ := factors n hn
  exact ⟨p,bound,prime,classes n p prime hit⟩

/-- A full block longer than Y(x) contains a term with no prime factor ≤ x. -/
theorem rough_term {q b x H : ℕ} (cop : q.Coprime b) (long : Erdos687.Y x < H) :
    ∃ n ∈ Finset.Icc 1 H, ∀ p ≤ x, p.Prime → ¬ p ∣ q*n+b := by
  by_contra! small
  exact (Nat.not_le_of_gt long) (cover_of_small_factors cop small)

/-- Below x² a composite term has a prime factor ≤ x. This gives a prime
    in any reduced progression satisfying the displayed finite window bound. -/
theorem prime_in_progression {q b x H : ℕ} (cop : q.Coprime b) (start : 2 ≤ q+b)
    (long : Erdos687.Y x < H) (room : q*H+b ≤ x^2) :
    ∃ n ∈ Finset.Icc 1 H, (q*n+b).Prime ∧ x < q*n+b := by
  obtain ⟨n,hn,rough⟩ := rough_term cop long
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
  have low : 2 ≤ q*n+b := by
    have le := Nat.mul_le_mul_left q lo
    simp only [Nat.mul_one] at le
    omega
  have high := (Nat.add_le_add_right (Nat.mul_le_mul_left q hi) b).trans room
  have pr := Nat.minFac_prime (by omega : q*n+b ≠ 1)
  have big : x < (q*n+b).minFac := by
    by_contra! le
    exact rough _ le pr (Nat.minFac_dvd _)
  have prime : (q*n+b).Prime := by
    by_contra composite
    have sq := Nat.minFac_sq_le_self (by omega : 0 < q*n+b) composite
    nlinarith [Nat.mul_self_lt_mul_self big]
  exact ⟨n,hn,prime,by simpa [prime.minFac_eq] using big⟩

open Filter
open scoped Asymptotics

theorem room_of_upper_power {α δ : ℝ} (nonneg : 0 ≤ α) (gap : α+δ < 2) (K : ℕ)
    (upper : (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^α)) :
    ∀ᶠ x : ℕ in atTop, ∀ q b : ℕ, b < q → (q:ℝ) ≤ (x:ℝ)^δ →
      K*(q*(Erdos687.Y x+1)+b) ≤ x^2 := by
  obtain ⟨C,hC,est⟩ := upper.exists_pos
  have grows := (tendsto_rpow_atTop (show 0 < 2-(α+δ) by linarith)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [est.bound,grows.eventually_ge_atTop ((K:ℝ)*(C+2)),eventually_ge_atTop (1:ℕ)] with x hx large xpos
  intro q b hb small
  have one : (1:ℝ) ≤ x := by exact_mod_cast xpos
  have pos : (0:ℝ) < x := by linarith
  have power := Real.one_le_rpow one nonneg
  have y : (Erdos687.Y x : ℝ) ≤ C*(x:ℝ)^α := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (Erdos687.Y x : ℝ) by positivity),
      abs_of_nonneg (Real.rpow_nonneg pos.le α)] using hx
  have factor : (Erdos687.Y x : ℝ)+2 ≤ (x:ℝ)^α*(C+2) := by nlinarith
  have rb : (b:ℝ) ≤ q := by exact_mod_cast hb.le
  have base : (q:ℝ)*((Erdos687.Y x:ℝ)+1)+b ≤ (x:ℝ)^(α+δ)*(C+2) := calc
    _ ≤ (q:ℝ)*((Erdos687.Y x:ℝ)+2) := by linarith
    _ ≤ (x:ℝ)^δ*((x:ℝ)^α*(C+2)) := mul_le_mul small factor (by positivity) (by positivity)
    _ = (x:ℝ)^(α+δ)*(C+2) := by rw [Real.rpow_add pos]; ring
  have roomR : (K:ℝ)*((q:ℝ)*((Erdos687.Y x:ℝ)+1)+b) ≤ (x:ℝ)^2 := calc
    _ ≤ (K:ℝ)*((x:ℝ)^(α+δ)*(C+2)) := mul_le_mul_of_nonneg_left base (Nat.cast_nonneg _)
    _ = (x:ℝ)^(α+δ)*((K:ℝ)*(C+2)) := by ring
    _ ≤ (x:ℝ)^(α+δ)*(x:ℝ)^(2-(α+δ)) := mul_le_mul_of_nonneg_left large (by positivity)
    _ = _ := by rw [← Real.rpow_add pos,show α+δ+(2-(α+δ))=2 by ring,Real.rpow_two]
  exact_mod_cast roomR

/-- An upper exponent for Y gives primes uniformly in reduced progressions
    up to the complementary exponent, with a strict margin in the sum. -/
theorem moduli_of_upper_power {α δ : ℝ} (nonneg : 0 ≤ α) (gap : α+δ < 2)
    (upper : (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^α)) :
    ∀ᶠ x : ℕ in atTop, ∀ q b : ℕ, 2 ≤ q → b < q → q.Coprime b → (q:ℝ) ≤ (x:ℝ)^δ →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x^2 ∧ p ≡ b [MOD q] := by
  filter_upwards [room_of_upper_power nonneg gap 1 upper] with x broad
  intro q b hq hb cop small
  have room : q*(Erdos687.Y x+1)+b ≤ x^2 := by simpa using broad q b hb small
  obtain ⟨n,hn,prime,big⟩ := prime_in_progression cop (by omega) (Nat.lt_succ_self _) room
  exact ⟨q*n+b,prime,big,(Nat.add_le_add_right (Nat.mul_le_mul_left q (Finset.mem_Icc.mp hn).2) b).trans room,
    by simp [Nat.ModEq]⟩

/-- In particular a near-linear estimate for Y would give a least prime
    of at most 4 q^(2+ε) in every reduced residue class modulo large q. -/
theorem least_prime_of_near_linear
    (upper : ∀ e > (0:ℝ), (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^(1+e))) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ b < q, q.Coprime b →
      ∃ p : ℕ, p.Prime ∧ p ≡ b [MOD q] ∧ (p:ℝ) ≤ 4*(q:ℝ)^(2+ε) := by
  let t := 1+ε/2
  let δ := t⁻¹
  have ht : 1 < t := by dsimp [t]; linarith
  have tp : 0 < t := by linarith
  have dp : 0 < δ := inv_pos.mpr tp
  have ds : δ < 1 := by dsimp [δ]; exact (inv_lt_one₀ tp).mpr ht
  have epos : 0 < (1-δ)/2 := by linarith
  have primes := moduli_of_upper_power (δ := δ) (show 0 ≤ 1+(1-δ)/2 by linarith)
    (by linarith) (upper _ epos)
  obtain ⟨X,after⟩ := Filter.eventually_atTop.1 primes
  filter_upwards [eventually_ge_atTop (max X 2)] with q hq
  intro b hb cop
  have q2 : 2 ≤ q := (le_max_right _ _).trans hq
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have qp : (0:ℝ) ≤ q := Nat.cast_nonneg _
  let u := (q:ℝ)^t
  let x := ⌈u⌉₊
  have qu : (q:ℝ) ≤ u := by
    simpa [u] using Real.rpow_le_rpow_of_exponent_le q1 ht.le
  have ux : u ≤ (x:ℝ) := Nat.le_ceil _
  have qx : q ≤ x := by exact_mod_cast qu.trans ux
  have fit : (q:ℝ) ≤ (x:ℝ)^δ := calc
    _ = u^δ := by dsimp [u,δ]; rw [← Real.rpow_mul qp,mul_inv_cancel₀ tp.ne',Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (qp.trans qu) ux dp.le
  obtain ⟨p,pr,_,bound,cls⟩ := after x ((le_max_left _ _).trans (hq.trans qx)) q b q2 hb cop fit
  have xu : (x:ℝ) ≤ 2*u := by
    have hh : (x:ℝ) < u+1 := Nat.ceil_lt_add_one (qp.trans qu)
    linarith
  have scale : u^2 = (q:ℝ)^(2+ε) := by
    dsimp [u]
    rw [← Real.rpow_two,← Real.rpow_mul qp]
    congr 1
    dsimp [t]
    ring
  refine ⟨p,pr,cls,?_⟩
  have cast : (p:ℝ) ≤ (x:ℝ)^2 := by exact_mod_cast bound
  rw [← scale]
  nlinarith [sq_nonneg u, pow_le_pow_left₀ (Nat.cast_nonneg x) xu 2]

end ProgressionPremiere687

#print axioms ProgressionPremiere687.prime_in_progression
#print axioms ProgressionPremiere687.moduli_of_upper_power
#print axioms ProgressionPremiere687.least_prime_of_near_linear
