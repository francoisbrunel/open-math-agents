import DensiteCarree687
import Comptage687

/-! Exclude one family of thin completable profiles unconditionally:
all the small prime classes passing through a common point of the window. -/
namespace CentreCarre687
open Filter Transfert687

private theorem pi_lower {n : ℕ} (hn : (128:ℝ) ≤ n) :
    (n:ℝ)/(4*Real.log n) ≤ Nat.primeCounting n := by
  have pos := Real.log_pos (show (1:ℝ) < n by linarith)
  have hr := Real.sqrt_pos.mpr (show (0:ℝ) < n+1 by positivity)
  have lr := Real.log_le_sub_one_of_pos hr
  rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ n+1)] at lr
  have hl : Real.log ((n:ℝ)+1) ≤ n/4 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ n+1 by positivity),
      mul_nonneg (show (0:ℝ) ≤ n-128 by linarith) (show (0:ℝ) ≤ n by positivity),
      sq_nonneg (Real.sqrt ((n:ℝ)+1)-8)]
  refine le_trans ?_ (Chebyshev.pi_ge n)
  rw [show (n:ℝ)/(4*Real.log n) = (n/4)/Real.log n by ring]
  apply div_le_div_of_nonneg_right _ pos.le
  nlinarith [mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ Real.log 2 by
    linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg (α := ℝ) n)]

private theorem prime_stock {z : ℕ} (hz : 512 ≤ z) :
    (z:ℝ)^2/(64*Real.log z) ≤ (((z^2/2).primesLE \ z.primesLE).card:ℝ) := by
  let h := z^2/2
  have z2 : 2 ≤ z := by omega
  have zr : (512:ℝ) ≤ z := by exact_mod_cast hz
  have lp := Real.log_pos (show (1:ℝ) < z by linarith)
  have square : 512*z ≤ z^2 := by simpa only [pow_two] using Nat.mul_le_mul_right z hz
  have fl : z^2 ≤ 4*h := by dsimp [h]; omega
  have zh : z ≤ h := by dsimp [h]; omega
  have h128 : (128:ℝ) ≤ h := by exact_mod_cast (show 128 ≤ h by omega)
  have hp := Real.log_pos (show (1:ℝ) < h by linarith)
  have lu : Real.log (h:ℝ) ≤ 2*Real.log z := by
    have up : h ≤ z^2 := Nat.div_le_self _ _
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (by positivity : 0 < (h:ℝ))
      (show (h:ℝ) ≤ (z:ℝ)^2 by exact_mod_cast up)
  have lower : (z:ℝ)^2/(32*Real.log z) ≤ Nat.primeCounting h := by
    apply le_trans _ (pi_lower h128)
    calc
      _ ≤ 4*(h:ℝ)/(32*Real.log z) := div_le_div_of_nonneg_right (by exact_mod_cast fl) (by positivity)
      _ = (h:ℝ)/(4*(2*Real.log z)) := by ring
      _ ≤ _ := by gcongr
  have estimate := Comptage687.prime_count_eight z2
  have sub : z.primesLE ⊆ h.primesLE := by
    intro p hp'
    obtain ⟨up,pr⟩ := Nat.mem_primesLE.mp hp'
    exact Nat.mem_primesLE.mpr ⟨up.trans zh,pr⟩
  change _ ≤ ((h.primesLE \ z.primesLE).card:ℝ)
  rw [Finset.card_sdiff_of_subset sub,Nat.cast_sub (Finset.card_le_card sub)]
  simp only [Nat.primesLE_card_eq_primeCounting]
  have small : 8*(z:ℝ)/Real.log z ≤ (z:ℝ)^2/(64*Real.log z) := by
    rw [show (z:ℝ)^2/(64*Real.log z)=((z:ℝ)^2/64)/Real.log z by ring]
    apply div_le_div_of_nonneg_right _ lp.le
    nlinarith only [mul_le_mul_of_nonneg_right zr (Nat.cast_nonneg (α := ℝ) z)]
  linarith only [lower,estimate,small,show (z:ℝ)^2/(32*Real.log z)=2*((z:ℝ)^2/(64*Real.log z)) by ring]

/-- Each large prime distance gives a different survivor on the longer
side of the common representative. -/
theorem aligned_stock {z b : ℕ} (hz : 512 ≤ z) (hb : b ∈ Finset.Icc 1 (z^2))
    (a : ℕ → ℕ) (aligned : ∀ p ∈ z.primesLE, a p%p=b%p) :
    (z:ℝ)^2/(64*Real.log z) ≤ ((survivors z (z^2) a).card:ℝ) := by
  let N := z^2
  let Q := (N/2).primesLE \ z.primesLE
  let f (q : ℕ) := if b ≤ N/2 then b+q else b-q
  obtain ⟨bl,bu⟩ := Finset.mem_Icc.mp hb
  change b ≤ N at bu
  have bounds {q : ℕ} (hq : q ∈ Q) : z < q ∧ q ≤ N/2 ∧ q.Prime := by
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨qh,pr⟩ := Nat.mem_primesLE.mp hin
    exact ⟨lt_of_not_ge (fun e => hout (Nat.mem_primesLE.mpr ⟨e,pr⟩)),qh,pr⟩
  have hits : Q.card ≤ (survivors z N a).card := by
    apply Finset.card_le_card_of_injOn f
    · intro q hq
      obtain ⟨big,up,prime⟩ := bounds hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_,?_⟩
      · dsimp [f]; split <;> omega
      · intro p hp congruence
        have eq : f q ≡ b [MOD p] := congruence.trans (aligned p hp)
        have div : p ∣ q := by
          by_cases left : b ≤ N/2
          · simpa [f,left] using eq.symm.dvd'
          · have dist : b-f q=q := by dsimp [f]; rw [if_neg left]; omega
            simpa only [dist] using eq.dvd'
        obtain ⟨pz,pp⟩ := Nat.mem_primesLE.mp hp
        rcases (Nat.dvd_prime prime).mp div with unit | same
        · exact pp.ne_one unit
        · omega
    · intro i hi j hj eq
      have ih := (bounds hi).2.1
      have jh := (bounds hj).2.1
      dsimp [f] at eq
      split at eq <;> omega
  exact (prime_stock hz).trans (by exact_mod_cast hits)

theorem no_aligned_cover (m : ℕ) (hm : 1536 < m) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ, ∀ b ∈ Finset.Icc 1 ((k^m)^2),
      (∀ p ∈ (k^m).primesLE, a p%p=b%p) →
      ¬ (∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p=a p%p) := by
  filter_upwards [DensiteCarree687.thin_of_cover m (by omega),eventually_ge_atTop (512:ℕ)] with k thin hk
  intro a b hb aligned covered
  let z := k^m
  have kz : k ≤ z := by simpa [z] using Nat.pow_le_pow_right (by omega : 0 < k) (show 1 ≤ m by omega)
  have z512 := hk.trans kz
  have low := aligned_stock z512 hb a aligned
  have up := thin a covered
  have lp : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have strict : 24/(m:ℝ) < 1/64 := (div_lt_iff₀ mp).mpr (by
    have ml : (1536:ℝ) < m := by exact_mod_cast hm
    linarith)
  have contradiction := lt_of_lt_of_le
    (mul_lt_mul_of_pos_right strict (show 0 < (z:ℝ)^2/Real.log z by positivity)) (by
      change (1/64:ℝ)*((z:ℝ)^2/Real.log z) ≤ ((survivors z (z^2) a).card:ℝ)
      convert low using 1 <;> ring)
  apply (not_lt_of_ge up)
  convert contradiction using 1 <;> ring

end CentreCarre687
#print axioms CentreCarre687.aligned_stock
#print axioms CentreCarre687.no_aligned_cover
