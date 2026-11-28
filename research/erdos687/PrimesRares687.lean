import ProgressionPremiere687
import Extension687

/-! A sparse progression yields a lower bound for the actual covering
    maximum when distinct reserve primes can cover the remaining indices. -/
namespace PrimesRares687
open ProgressionPremiere687

def primeIndices (q b y H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter fun n => (q*n+b).Prime ∧ y < q*n+b

theorem cover_of_sparse_progression {x y H q b : ℕ} (cop : q.Coprime b) (start : 2 ≤ q+b)
    (cutoff : y ≤ x) (room : q*H+b ≤ y^2)
    (sparse : (primeIndices q b y H).card ≤ (x.primesLE \ y.primesLE).card) :
    H ≤ Erdos687.Y x := by
  classical
  obtain ⟨a,classes⟩ := factor_classes cop
  obtain ⟨r,reserve⟩ := Extension687.assign_images _ _ id sparse
  apply Transfert687.le_Y_of_covered
  refine ⟨fun p => if p ≤ y then a p else r p,?_⟩
  intro n hn
  by_cases rare : n ∈ primeIndices q b y H
  · obtain ⟨p,hp,eq⟩ := reserve n rare
    obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    have fresh : ¬ p ≤ y := fun small => (Finset.mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨small,pr⟩)
    exact ⟨p,le,pr,by simpa only [if_neg fresh,eq,id_eq] using (Nat.ModEq.refl n : n ≡ n [MOD p])⟩
  · let m := q*n+b
    obtain ⟨nlo,nhi⟩ := Finset.mem_Icc.mp hn
    have low : 2 ≤ m := by
      have h := Nat.mul_le_mul_left q nlo
      simp only [Nat.mul_one] at h
      dsimp [m]; omega
    have high : m ≤ y^2 := (Nat.add_le_add_right (Nat.mul_le_mul_left q nhi) b).trans room
    have le : m.minFac ≤ y := by
      by_contra! large
      have pr : m.Prime := by
        by_contra comp
        have sq := Nat.minFac_sq_le_self (by omega : 0 < m) comp
        nlinarith [Nat.mul_self_lt_mul_self large]
      exact rare (Finset.mem_filter.mpr ⟨hn,pr,by simpa [pr.minFac_eq] using large⟩)
    have pr := Nat.minFac_prime (by omega : m ≠ 1)
    exact ⟨m.minFac,le.trans cutoff,pr,by simpa [le] using classes n _ pr (Nat.minFac_dvd m)⟩

theorem many_primes_of_long {x y H q b : ℕ} (cop : q.Coprime b) (start : 2 ≤ q+b)
    (cutoff : y ≤ x) (room : q*H+b ≤ y^2) (long : Erdos687.Y x < H) :
    (x.primesLE \ y.primesLE).card < (primeIndices q b y H).card := by
  by_contra! sparse
  exact (Nat.not_le_of_gt long) (cover_of_sparse_progression cop start cutoff room sparse)

open Filter
open scoped Asymptotics

/-- At a complementary modulus exponent, each reduced class must contain
    more primes up to floor(x/2)^2 than there are primes in (x/2,x]. -/
theorem many_moduli_of_upper_power {α δ : ℝ} (nonneg : 0 ≤ α) (gap : α+δ < 2)
    (upper : (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^α)) :
    ∀ᶠ x : ℕ in atTop, ∀ q b : ℕ, 2 ≤ q → b < q → q.Coprime b → (q:ℝ) ≤ (x:ℝ)^δ →
      (x.primesLE \ (x/2).primesLE).card <
      (((x/2)^2).primesLE.filter (fun p => x/2 < p ∧ p%q=b%q)).card := by
  filter_upwards [room_of_upper_power nonneg gap 9 upper,eventually_ge_atTop (2:ℕ)] with x broad hx
  intro q b hq hb cop small
  have bound := broad q b hb small
  have half : x ≤ 3*(x/2) := by omega
  have cmp : x^2 ≤ 9*(x/2)^2 := by nlinarith [Nat.mul_self_le_mul_self half]
  have room : q*(Erdos687.Y x+1)+b ≤ (x/2)^2 := by omega
  have cnt := many_primes_of_long cop (by omega) (Nat.div_le_self x 2) room (Nat.lt_succ_self _)
  apply lt_of_lt_of_le cnt
  apply Finset.card_le_card_of_injOn (fun n : ℕ => q*n+b)
  · intro n hn
    obtain ⟨mem,pr,big⟩ := Finset.mem_filter.mp hn
    have le := (Nat.add_le_add_right (Nat.mul_le_mul_left q (Finset.mem_Icc.mp mem).2) b).trans room
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨le,pr⟩,big,by simp⟩
  · intro n _ m _ eq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) (Nat.add_right_cancel eq)

end PrimesRares687

#print axioms PrimesRares687.many_primes_of_long
#print axioms PrimesRares687.many_moduli_of_upper_power
