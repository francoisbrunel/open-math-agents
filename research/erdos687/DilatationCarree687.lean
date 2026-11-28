import StabiliteCarree687

/-! Survivor bounds and separation after absorbing exceptional primes into a dilation. -/
namespace DilatationCarree687
open Filter Transfert687
open scoped BigOperators

/-- Count large prime distances after dilating by D. -/
theorem prime_distances {D z : ℕ} (hd : 0 < D) (hz : 512*D ≤ z) :
    (z:ℝ)^2/(64*Real.log z) ≤
      D*(((z^2/(2*D)).primesLE \ z.primesLE).card:ℝ) := by
  let h := z^2/(2*D)
  have dp : 0 < 2*D := by omega
  have zbig : 512 ≤ z := by omega
  have zh : z ≤ h := (Nat.le_div_iff_mul_le dp).2 (by
    simpa only [pow_two] using Nat.mul_le_mul_left z (show 2*D ≤ z by omega))
  have t : z^2 < (h+1)*(2*D) := (Nat.div_lt_iff_lt_mul dp).mp (Nat.lt_succ_self h)
  have fl : z^2 ≤ 4*D*h := by
    nlinarith only [t,Nat.mul_le_mul_left D (show 1 ≤ h by omega)]
  have lp := Real.log_pos (show (1:ℝ) < z by exact_mod_cast (show 1 < z by omega))
  have hp := Real.log_pos (show (1:ℝ) < h by exact_mod_cast (show 1 < h by omega))
  have dr : 0 < (D:ℝ) := by exact_mod_cast hd
  have lu : Real.log (h:ℝ) ≤ 2*Real.log z := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log
      (by exact_mod_cast (show 0 < h by omega) : 0 < (h:ℝ))
      (show (h:ℝ) ≤ (z:ℝ)^2 by exact_mod_cast (Nat.div_le_self (z^2) (2*D)))
  have lower : (z:ℝ)^2/(32*Real.log z) ≤ D*(Nat.primeCounting h:ℝ) := calc
    _ ≤ (4*D*(h:ℝ))/(32*Real.log z) := div_le_div_of_nonneg_right (by exact_mod_cast fl) (by positivity)
    _ = (D:ℝ)*((h:ℝ)/(4*(2*Real.log z))) := by ring
    _ ≤ (D:ℝ)*((h:ℝ)/(4*Real.log h)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (CentreCarre687.pi_lower
      (by exact_mod_cast (show 128 ≤ h by omega))) dr.le
  have upper := mul_le_mul_of_nonneg_left (Comptage687.prime_count_eight (show 2 ≤ z by omega)) dr.le
  have small : (D:ℝ)*(8*z/Real.log z) ≤ (z:ℝ)^2/(64*Real.log z) := by
    rw [← mul_div_assoc,show (z:ℝ)^2/(64*Real.log z)=((z:ℝ)^2/64)/Real.log z by ring]
    apply div_le_div_of_nonneg_right _ lp.le
    have zr : 512*(D:ℝ) ≤ z := by exact_mod_cast hz
    nlinarith only [mul_le_mul_of_nonneg_right zr (Nat.cast_nonneg (α := ℝ) z)]
  have sub : z.primesLE ⊆ h.primesLE := by
    intro p hp'
    obtain ⟨pz,pr⟩ := Nat.mem_primesLE.mp hp'
    exact Nat.mem_primesLE.mpr ⟨pz.trans zh,pr⟩
  change _ ≤ D*(((h.primesLE \ z.primesLE).card):ℝ)
  rw [Finset.card_sdiff_of_subset sub,Nat.cast_sub (Finset.card_le_card sub)]
  simp only [Nat.primesLE_card_eq_primeCounting]
  nlinarith only [lower,upper,small,show (z:ℝ)^2/(32*Real.log z)=2*((z:ℝ)^2/(64*Real.log z)) by ring]

/-- Rows differing from the center are precisely the primes dividing D. -/
theorem dilated_stock {z D b : ℕ} (hd : 0 < D) (hz : 512*D ≤ z)
    (hb : b ∈ Finset.Icc 1 (z^2)) (a : ℕ → ℕ)
    (rows : ∀ p ∈ z.primesLE, (a p%p ≠ b%p) ↔ p ∣ D) :
    (z:ℝ)^2/(64*Real.log z) ≤ D*((survivors z (z^2) a).card:ℝ) := by
  let N := z^2
  let Q := (N/(2*D)).primesLE \ z.primesLE
  let f (q : ℕ) := if b ≤ N/2 then b+D*q else b-D*q
  obtain ⟨bl,bu⟩ := Finset.mem_Icc.mp hb
  change b ≤ N at bu
  have bounds {q : ℕ} (hq : q ∈ Q) : z < q ∧ D*q ≤ N/2 ∧ q.Prime := by
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨qh,pr⟩ := Nat.mem_primesLE.mp hin
    have t := (Nat.le_div_iff_mul_le (show 0 < 2*D by omega)).mp qh
    have u : (D*q)*2 ≤ N := by simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using t
    exact ⟨lt_of_not_ge (fun e => hout (Nat.mem_primesLE.mpr ⟨e,pr⟩)),
      (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 u,pr⟩
  have hits : Q.card ≤ (survivors z N a).card := by
    apply Finset.card_le_card_of_injOn f
    · intro q hq
      obtain ⟨big,up,prime⟩ := bounds hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_,?_⟩
      · dsimp [f]; split <;> omega
      · intro p hp hit
        obtain ⟨pz,pp⟩ := Nat.mem_primesLE.mp hp
        have equiv : f q ≡ b [MOD p] ↔ p ∣ D*q := by
          by_cases left : b ≤ N/2
          · have e : f q=b+D*q := if_pos left
            constructor
            · intro h
              simpa [e] using h.symm.dvd'
            · intro h
              simpa [e] using (Nat.modEq_zero_iff_dvd.mpr h).add_left b
          · have dist : b-f q=D*q := by dsimp [f]; rw [if_neg left]; omega
            have le : f q ≤ b := by dsimp [f]; rw [if_neg left]; omega
            simpa only [dist] using Nat.modEq_iff_dvd' le
        by_cases div : p ∣ D
        · exact (rows p hp).2 div (hit.symm.trans (equiv.2 (dvd_mul_of_dvd_left div q)))
        · have same : a p%p=b%p := by by_contra ne; exact div ((rows p hp).1 ne)
          rcases pp.dvd_mul.mp (equiv.1 (hit.trans same)) with bad | dq
          · exact div bad
          · rcases (Nat.dvd_prime prime).mp dq with unit | eq
            · exact pp.ne_one unit
            · omega
    · intro i hi j hj eq
      have ih := (bounds hi).2.1
      have jh := (bounds hj).2.1
      have e : D*i=D*j := by dsimp [f] at eq; split at eq <;> omega
      exact Nat.eq_of_mul_eq_mul_left hd e
  exact (prime_distances hd hz).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hits) (by positivity))

/-- Remove any prescribed small prime factors already known to differ
from the center, then measure the remaining discrepancy. -/
theorem tail_separation (m D : ℕ) (hm : 2 ≤ m) (hd : 0 < D) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
    (∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p=a p%p) →
    ∀ b ∈ Finset.Icc 1 ((k^m)^2), (∀ p ∈ (k^m).primesLE, p ∣ D → a p%p ≠ b%p) →
      1/64 ≤ (D:ℝ)*(24/m + 68*(∑ p ∈ (StabiliteCarree687.changes (k^m)
        (fun _ => b) a).filter (fun p => ¬ p ∣ D), (1:ℝ)/p)) := by
  classical
  filter_upwards [DensiteCarree687.thin_of_cover m hm,eventually_ge_atTop (1024+512*D)] with k thin hk
  intro a full b hb different
  let z := k^m
  have kz : k ≤ z := by simpa [z] using Nat.pow_le_pow_right (by omega : 0 < k) (show 1 ≤ m by omega)
  let c (p : ℕ) := if p ∣ D then a p else b
  have rows : ∀ p ∈ z.primesLE, (c p%p ≠ b%p) ↔ p ∣ D := by
    intro p hp
    by_cases e : p ∣ D
    · simp [c,e,different p hp e]
    · simp [c,e]
  have es : StabiliteCarree687.changes z c a =
      (StabiliteCarree687.changes z (fun _ => b) a).filter (fun p => ¬ p ∣ D) := by
    ext p
    by_cases e : p ∣ D <;> simp [StabiliteCarree687.changes,c,e]
  let W := (z:ℝ)^2/Real.log z
  have zp : 0 < (z:ℝ) := by exact_mod_cast (show 0 < z by omega)
  have lp := Real.log_pos (show (1:ℝ) < z by exact_mod_cast (show 1 < z by omega))
  have wp : 0 < W := by dsimp [W]; positivity
  have stock := dilated_stock hd (show 512*D ≤ z by omega) hb c rows
  have diff := StabiliteCarree687.stability (show 1024 ≤ z by omega) c a
  rw [es] at diff
  have small := thin a full
  have s1 : (z:ℝ)^2/(64*Real.log z)=(1/64:ℝ)*W := by dsimp [W]; ring
  have s2 : 68*(z:ℝ)^2/Real.log z=68*W := by dsimp [W]; ring
  have s3 : (24/(m:ℝ))*(z:ℝ)^2/Real.log z=(24/m)*W := by dsimp [W]; ring
  change _ ≤ (24/(m:ℝ))*(z:ℝ)^2/Real.log z at small
  rw [s1] at stock
  rw [s2] at diff
  rw [s3] at small
  apply le_of_mul_le_mul_right (a := W) _ wp
  nlinarith only [stock,mul_le_mul_of_nonneg_left diff (Nat.cast_nonneg (α := ℝ) D),
    mul_le_mul_of_nonneg_left small (Nat.cast_nonneg (α := ℝ) D)]

end DilatationCarree687
#print axioms DilatationCarree687.prime_distances
#print axioms DilatationCarree687.dilated_stock
#print axioms DilatationCarree687.tail_separation
