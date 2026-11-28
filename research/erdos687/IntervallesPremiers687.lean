import PrimesRares687

/-! Short-interval prime counts forced by bounds on the covering maximum. -/
namespace IntervallesPremiers687
open Filter PrimesRares687
open scoped Asymptotics

/-- Every interval below the square of the small-prime cutoff contains
more primes than the entire reserve band if its length exceeds Y. -/
theorem short_interval {b H y x : ℕ} (start : 1 ≤ b) (cutoff : y ≤ x)
    (room : b+H ≤ y^2) (long : Erdos687.Y x < H) :
    (x.primesLE \ y.primesLE).card < ((b+H).primesLE \ b.primesLE).card := by
  have count := many_primes_of_long (q := 1) (b := b) (by simp : Nat.Coprime 1 b)
    (by omega) cutoff (by simpa [Nat.add_comm] using room) long
  apply lt_of_lt_of_le count
  apply Finset.card_le_card_of_injOn (fun n : ℕ => n+b)
  · intro n hn
    obtain ⟨mem,prime,_⟩ := Finset.mem_filter.mp hn
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp mem
    simp only [Nat.one_mul] at prime
    change n+b ∈ (b+H).primesLE \ b.primesLE
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,prime⟩,
      fun h => (by have := (Nat.mem_primesLE.mp h).1; omega)⟩
  · intro i _ j _ eq
    exact Nat.add_right_cancel eq

/-- If Y has a near-linear upper bound, every translated interval of
length k^(1+ε) with initial point between k² and 2k² contains more
primes than the whole interval (2k,4k], uniformly in the initial point. -/
theorem many_in_short_intervals
    (upper : ∀ e > (0:ℝ), (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^(1+e))) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ b : ℕ, k^2 ≤ b → b ≤ 2*k^2 →
      ((4*k).primesLE \ (2*k).primesLE).card <
        ((b+⌊(k:ℝ)^(1+ε)⌋₊).primesLE \ b.primesLE).card := by
  have four : Tendsto (fun k : ℕ => 4*k) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with k hk
    omega
  obtain ⟨C,hC,est⟩ := (upper (ε/2) (by positivity)).exists_pos
  let a := 1+ε/2
  have grows := (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  have room := ProgressionPremiere687.room_of_upper_power (α := 1+1/2) (δ := 0)
    (by norm_num) (by norm_num) 16 (upper (1/2) (by norm_num))
  filter_upwards [four.eventually est.bound, four.eventually room,
    grows.eventually_ge_atTop (C*4^a+1),eventually_ge_atTop (1:ℕ)] with k big small spare hk
  intro b lo hi
  have square := small 1 0 (by decide) (by simp)
  simp only [one_mul,add_zero] at square
  have size : Erdos687.Y (4*k)+1 ≤ k^2 := by
    norm_num [mul_pow] at square
    omega
  have result := short_interval (b := b) (y := 2*k) (x := 4*k)
    (H := Erdos687.Y (4*k)+1) (by nlinarith) (by omega)
    (by nlinarith only [hi,size]) (Nat.lt_succ_self _)
  have kp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have k1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ka := Real.one_le_rpow k1 (show 0 ≤ a by dsimp [a]; linarith)
  have yp : (Erdos687.Y (4*k):ℝ) ≤ C*(4*(k:ℝ))^a := by
    change ‖(Erdos687.Y (4*k):ℝ)‖ ≤ C*‖((4*k:ℕ):ℝ)^a‖ at big
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _), Nat.cast_mul, Nat.cast_ofNat] at big
    exact big
  rw [Real.mul_rpow (by norm_num) kp.le] at yp
  change C*4^a+1 ≤ (k:ℝ)^(ε/2) at spare
  have fits : Erdos687.Y (4*k)+1 ≤ ⌊(k:ℝ)^(1+ε)⌋₊ := by
    apply (Nat.le_floor_iff (Real.rpow_nonneg kp.le _)).2
    push_cast
    rw [show 1+ε=a+ε/2 by dsimp [a]; ring,Real.rpow_add kp]
    nlinarith only [yp,ka,mul_le_mul_of_nonneg_left spare (Real.rpow_nonneg kp.le a)]
  apply lt_of_lt_of_le result
  apply Finset.card_le_card
  intro p hp
  obtain ⟨h,avoid⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨pmax,prime⟩ := Nat.mem_primesLE.mp h
  exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,prime⟩,avoid⟩

end IntervallesPremiers687

#print axioms IntervallesPremiers687.short_interval
#print axioms IntervallesPremiers687.many_in_short_intervals
