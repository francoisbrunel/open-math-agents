import Presque687

/-! Two distinct prime divisors detect squarefree smooth integers that
    remain after sieving by all small primes. The cofactor left after
    removing both divisors still avoids those small primes. -/
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
