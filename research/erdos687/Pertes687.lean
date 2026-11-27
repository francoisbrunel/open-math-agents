import Protection687
import Transfert687

/-! A lower bound on possible simultaneous losses from a band of primes. -/
namespace Pertes687
open Transfert687

def deleted (x z N : ℕ) (a : ℕ → ℕ) := survivors z N a \ survivors x N a

/-- Protect a set against the old primes, then delete its surviving
    elements simultaneously by prescribing zero at the fresh primes. -/
theorem simultaneous_loss {x z N : ℕ} (Q T : Finset ℕ) (old : Q ⊆ z.primesLE)
    (range : T ⊆ Finset.Icc 1 N)
    (small : ∀ n ∈ T, ∀ p ∈ z.primesLE, p ∉ Q → ¬p ∣ n)
    (large : ∀ n ∈ T, ∃ p ∈ x.primesLE \ z.primesLE, p ∣ n) :
    ∃ a : ℕ → ℕ, T.card*(∏ p ∈ Q, (p-2)) ≤ (deleted x z N a).card*(∏ p ∈ Q, (p-1)) := by
  classical
  obtain ⟨b,good,stock⟩ := Protection687.protect_band_product Q T
    (fun p hp => (Nat.mem_primesLE.mp (old hp)).2.two_le)
  let a (p : ℕ) := if p ∈ Q then b p else 0
  refine ⟨a,stock.trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_))⟩
  intro n hn
  obtain ⟨hT,avoid⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_sdiff.mpr
  constructor
  · refine Finset.mem_filter.mpr ⟨range hT,?_⟩
    intro p hp hit
    by_cases hQ : p ∈ Q
    · exact avoid p hQ (by simpa only [a,if_pos hQ,Nat.mod_eq_of_lt (Finset.mem_Ico.mp (good p hQ)).2] using hit)
    · exact small n hT p hp hQ (Nat.dvd_of_mod_eq_zero (by simpa [a,hQ] using hit))
  · intro live
    obtain ⟨p,hp,dvd⟩ := large n hT
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
    have outside : p ∉ Q := fun h => hout (old h)
    exact (Finset.mem_filter.mp live).2 p hin (by simp [a,outside,Nat.mod_eq_zero_of_dvd dvd])

/-- Each ordered semiprime p*q pays once: the factors lie on opposite
    sides of z, so the products do not collide. Q is the protected band
    of small factors and P is any chosen large-prime band. -/
theorem semiprime_loss {x z N : ℕ} (P Q : Finset ℕ)
    (hP : P ⊆ x.primesLE \ z.primesLE) (hQ : Q ⊆ z.primesLE) :
    ∃ a : ℕ → ℕ, (∑ p ∈ P, (Q.filter fun q => p*q ≤ N).card)*(∏ q ∈ Q, (q-2))
      ≤ (deleted x z N a).card*(∏ q ∈ Q, (q-1)) := by
  classical
  let pairs := (P ×ˢ Q).filter fun u => u.1*u.2 ≤ N
  let prod (u : ℕ × ℕ) := u.1*u.2
  let T := pairs.image prod
  have sides (p : ℕ) (hp : p ∈ P) : p.Prime ∧ z < p := by
    obtain ⟨hin,out⟩ := Finset.mem_sdiff.mp (hP hp)
    have prime := (Nat.mem_primesLE.mp hin).2
    exact ⟨prime,lt_of_not_ge (fun le => out (Nat.mem_primesLE.mpr ⟨le,prime⟩))⟩
  have distinct : Set.InjOn prod (↑pairs : Set (ℕ × ℕ)) := by
    rintro ⟨p,q⟩ hu ⟨r,s⟩ hv he
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
    have pprime := (sides p hp).1
    have ss := Nat.mem_primesLE.mp (hQ hs)
    change p*q=r*s at he
    have divide : p ∣ r*s := he ▸ Nat.dvd_mul_right p q
    have pr : p=r := by
      rcases pprime.dvd_mul.mp divide with h | h
      · exact (Nat.prime_dvd_prime_iff_eq pprime (sides r hr).1).mp h
      · have eqn := (Nat.prime_dvd_prime_iff_eq pprime ss.2).mp h
        have := (sides p hp).2
        omega
    subst r
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left pprime.pos he)
  have count : T.card = ∑ p ∈ P, (Q.filter fun q => p*q ≤ N).card := calc
    _ = pairs.card := Finset.card_image_of_injOn distinct
    _ = ∑ u ∈ P ×ˢ Q, if u.1*u.2 ≤ N then 1 else 0 := by simp [pairs]
    _ = _ := by rw [Finset.sum_product]; simp
  rw [← count]
  apply simultaneous_loss Q T hQ
  · intro n hn
    obtain ⟨⟨p,q⟩,hu,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hpq,le⟩ := Finset.mem_filter.mp hu
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (sides p hp).1.pos (Nat.mem_primesLE.mp (hQ hq)).2.pos,le⟩
  · intro n hn r hr outside dvd
    obtain ⟨⟨p,q⟩,hu,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
    obtain ⟨rz,prime⟩ := Nat.mem_primesLE.mp hr
    rcases prime.dvd_mul.mp dvd with h | h
    · have eqn := (Nat.prime_dvd_prime_iff_eq prime (sides p hp).1).mp h
      have := (sides p hp).2
      omega
    · have eqn := (Nat.prime_dvd_prime_iff_eq prime (Nat.mem_primesLE.mp (hQ hq)).2).mp h
      exact outside (eqn ▸ hq)
  · intro n hn
    obtain ⟨⟨p,q⟩,hu,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,_⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
    exact ⟨p,hP hp,Nat.dvd_mul_right p q⟩

end Pertes687
