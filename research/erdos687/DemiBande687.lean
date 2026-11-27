import CribleTransfert687

/-! Unconditional upper estimate for the sum of the large-prime deletions
    in the dyadic R2 reduction of the quadratic Jacobsthal bound. -/
namespace DemiBande687
open Filter Transfert687 Progressions687 OAI.Erdos970.NumberTheoryLean
open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

private theorem ten_mul {k : ℕ} (h : 10 ≤ k) : 10*(k+1) ≤ 2^k := by
  induction k, h using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

private theorem scale {x : ℕ} (hx : 1024 ≤ x) :
    (x:ℝ)/Real.log x ≤ (15/8:ℝ)*(x/(x.log2+1):ℕ) := by
  let k := x.log2
  let d := x/(k+1)
  have hk : 10 ≤ k := (Nat.le_log2 (by omega : x ≠ 0)).2 (by simpa using hx)
  have powle : 2^k ≤ x := Nat.log2_self_le (by omega)
  have hd : 10 ≤ d := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).2 ((ten_mul hk).trans powle)
  have hxlt : x < (d+1)*(k+1) :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).1 (Nat.lt_succ_self d)
  have hlog : (k:ℝ)*Real.log 2 ≤ Real.log x := by
    have powR : (2:ℝ)^k ≤ x := by exact_mod_cast powle
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) powR
  have kl : (k:ℝ)*(2/3) ≤ Real.log x := by
    have c : (2/3:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact (mul_le_mul_of_nonneg_left c (Nat.cast_nonneg k)).trans hlog
  have kR : (10:ℝ) ≤ k := by exact_mod_cast hk
  have dR : (10:ℝ) ≤ d := by exact_mod_cast hd
  have hxR : (x:ℝ) ≤ ((d:ℝ)+1)*((k:ℝ)+1) := by exact_mod_cast hxlt.le
  have bound := mul_le_mul (by linarith : (d:ℝ)+1 ≤ 11/10*d)
    (by linarith : (k:ℝ)+1 ≤ 11/10*k) (by positivity) (by positivity)
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < x)))).2
  change (x:ℝ) ≤ (15/8:ℝ)*d*Real.log x
  nlinarith [mul_le_mul_of_nonneg_left kl (Nat.cast_nonneg (α := ℝ) d),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) d)]

private theorem class_bound {x p : ℕ} (hx : 1024 ≤ x) (hp : p.Prime) (hpx : p ≤ x)
    (hlarge : x/2 < p) (a : ℕ → ℕ) :
    charge (survivors (x/2) (x^2) a) a p ≤ 64*(x/(x.log2+1)) := by
  let J := x^2/p+1
  let z := x/2
  have zlo : 512 ≤ z := by dsimp [z]; omega
  have xup : x ≤ 2*z+1 := by dsimp [z]; omega
  have Jlo : x ≤ J := by
    have h : x ≤ x^2/p := (Nat.le_div_iff_mul_le hp.pos).2 (by
      simpa only [pow_two] using Nat.mul_le_mul_left x hpx)
    dsimp [J]; omega
  have Jup : J ≤ 2*x := by
    have h : x < 2*p := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left h (by omega : 0 < x)
    change x^2/p+1 ≤ 2*x
    apply (Nat.div_lt_iff_lt_mul hp.pos).2
    nlinarith
  have hroot : Nat.nthRoot 8 J ≤ z := by
    apply Nat.le_of_lt_succ
    apply (Nat.nthRoot_lt_iff (by decide : 8 ≠ 0)).2
    calc J ≤ 2*x := Jup
         _ < (z+1)^2 := by nlinarith [Nat.mul_le_mul_left z zlo]
         _ ≤ (z+1)^8 := pow_le_pow_right₀ (by omega) (by decide)
  obtain ⟨b,hb⟩ := charge_le_index_sieve (N := x^2) hp hlarge a
  rw [CribleTransfert687.index_eq_cutoff] at hb
  have h17 := SquarefreeHarmonic.cutoffSurvivors_le_seventeen J z b (by omega) hroot
  have hl := Real.log_pos (show 1 < (x:ℝ) by exact_mod_cast (by omega : 1 < x))
  have logle := Real.log_le_log (show 0 < (x:ℝ) by positivity) (show (x:ℝ) ≤ J by exact_mod_cast Jlo)
  have Jreal : (J:ℝ) ≤ 2*x := by exact_mod_cast Jup
  let d := x/(x.log2+1)
  have hr : (charge (survivors z (x^2) a) a p : ℝ) ≤ 64*(d:ℝ) := calc
    _ ≤ ((LargePrimeDeletion.cutoffSurvivors J z b).card:ℝ) := by exact_mod_cast hb
    _ ≤ 17*(J:ℝ)/Real.log J := h17
    _ ≤ 17*(2*(x:ℝ))/Real.log x := by gcongr
    _ = 34*((x:ℝ)/Real.log x) := by ring
    _ ≤ 34*((15/8:ℝ)*d) := mul_le_mul_of_nonneg_left (scale hx) (by norm_num)
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  exact_mod_cast hr

/-- H2 holds for every x >= 1024. The proof actually yields 960 in place
    of the reduction's coefficient 1000. -/
theorem dyadic_budget {x : ℕ} (hx : 1024 ≤ x) (a : ℕ → ℕ) :
    (∑ p ∈ x.primesLE \ (x/2).primesLE, charge (survivors (x/2) (x^2) a) a p) ≤
      960*(x/(x.log2+1))^2 := by
  let d := x/(x.log2+1)
  let P := x.primesLE \ (x/2).primesLE
  have countR : (Nat.primeCounting x : ℝ) ≤ 15*(d:ℝ) := calc
    _ ≤ 8*x/Real.log x := Comptage687.prime_count_eight (by omega)
    _ = 8*((x:ℝ)/Real.log x) := by ring
    _ ≤ 8*((15/8:ℝ)*d) := mul_le_mul_of_nonneg_left (scale hx) (by norm_num)
    _ = _ := by ring
  have count : x.primesLE.card ≤ 15*d := by
    rw [Nat.primesLE_card_eq_primeCounting]; exact_mod_cast countR
  have pcount : P.card ≤ 15*d := (Finset.card_le_card Finset.sdiff_subset).trans count
  calc _ ≤ ∑ _p ∈ P, 64*d := by
         apply Finset.sum_le_sum
         intro p hp
         obtain ⟨hmem,hout⟩ := Finset.mem_sdiff.mp hp
         obtain ⟨hpx,prime⟩ := Nat.mem_primesLE.mp hmem
         exact class_bound hx prime hpx (lt_of_not_ge (fun h => hout (Nat.mem_primesLE.mpr ⟨h,prime⟩))) a
       _ = P.card*(64*d) := by simp
       _ ≤ (15*d)*(64*d) := Nat.mul_le_mul_right _ pcount
       _ = _ := by dsimp [d]; ring

theorem H2_proved : H2 := by
  filter_upwards [eventually_ge_atTop (1024:ℕ)] with x hx
  intro a
  exact (dyadic_budget hx a).trans (Nat.mul_le_mul_right _ (by decide : 960 ≤ 1000))

end DemiBande687
