import Extension687

/-! A sharp 26-position extension certificate and a general admissible-tuple
    obstruction to longer uniform extensions by singleton classes. -/
namespace Roue687
open Extension687 Progressions687

private def wheel (a b c d : ℕ) :=
  (Finset.range 26).filter fun i => i%2 ≠ a ∧ i%3 ≠ b ∧ i%5 ≠ c ∧ i%7 ≠ d

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem wheel_bound : ∀ a : Fin 2, ∀ b : Fin 3, ∀ c : Fin 5, ∀ d : Fin 7,
    (wheel a b c d).card ≤ 7 := by decide

/-- Seven fresh primes extend any optimal cover by at least 26 positions,
    regardless of where the old cover lies or how large its length is. -/
theorem seven_extend_by_26 {x z : ℕ} (hz : 7 ≤ z) (hzx : z ≤ x)
    (hfresh : 7 ≤ (x.primesLE \ z.primesLE).card) :
    Erdos687.Y z + 26 ≤ Erdos687.Y x := by
  apply growth_from_capacity hzx
  intro a
  let r (p : ℕ) (hp : 0 < p) : Fin p := ⟨a p%p,Nat.mod_lt _ hp⟩
  have bound := wheel_bound (r 2 (by decide)) (r 3 (by decide))
    (r 5 (by decide)) (r 7 (by decide))
  apply (Finset.card_le_card ?_).trans (bound.trans hfresh)
  intro i hi
  obtain ⟨hJ,h⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hJ,?_⟩
  exact ⟨h 2 (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩),
    h 3 (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩),
    h 5 (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩),
    h 7 (Nat.mem_primesLE.mpr ⟨hz,by decide⟩)⟩

/-- The uniform capacity test with seven available primes is sharp at
    length 26. Eight admissible points do fit in [0,27). -/
theorem eight_can_survive_27 {z : ℕ} (hz : 8 ≤ z) :
    ∃ b, 8 ≤ (siftedIndices z 27 b).card := by
  classical
  let T : Finset ℕ := {0,2,6,8,12,18,20,26}
  have size : T.card = 8 := by decide
  apply (capacity_iff_tuple hz).2
  refine ⟨T,by decide,size,?_⟩
  intro p hp
  by_cases h : p ≤ 8
  · interval_cases p <;> first | exact False.elim (by revert hp; decide)
                                | exact ⟨1,by decide,by decide⟩
                                | exact ⟨4,by decide,by decide⟩
                                | exact ⟨3,by decide,by decide⟩
  · have fewer : (T.image (fun i => i%p)).card < (Finset.range p).card := by
      rw [Finset.card_range]
      exact Finset.card_image_le.trans_lt (by omega)
    obtain ⟨r,hr,hm⟩ := Finset.exists_mem_notMem_of_card_lt_card fewer
    exact ⟨r,Finset.mem_range.mp hr,fun i hi eqn => hm (Finset.mem_image.mpr ⟨i,hi,eqn⟩)⟩

/-- Any k primes in (k,m] form an admissible tuple. This bounds what an
    extension proof based solely on uniform singleton capacity can deliver. -/
theorem prime_tuple_barrier {k m z : ℕ} (hkz : k ≤ z)
    (hk : k ≤ (m.primesLE \ k.primesLE).card) :
    ∃ b, k ≤ (siftedIndices z (m+1) b).card := by
  classical
  obtain ⟨S,hS,size⟩ := Finset.exists_subset_card_eq hk
  apply (capacity_iff_tuple hkz).2
  refine ⟨S,?_,size,?_⟩
  · intro i hi
    obtain ⟨him,_⟩ := Finset.mem_sdiff.mp (hS hi)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp him).1)
  · intro p hp
    by_cases hpk : p ≤ k
    · refine ⟨0,hp.pos,?_⟩
      intro i hi he
      obtain ⟨him,hik⟩ := Finset.mem_sdiff.mp (hS hi)
      have prime := (Nat.mem_primesLE.mp him).2
      have heq := (Nat.prime_dvd_prime_iff_eq hp prime).mp (Nat.dvd_of_mod_eq_zero he)
      exact hik (Nat.mem_primesLE.mpr ⟨heq ▸ hpk,prime⟩)
    · have fewer : (S.image (fun i => i%p)).card < (Finset.range p).card := by
        rw [Finset.card_range]
        exact Finset.card_image_le.trans_lt (by omega)
      obtain ⟨r,hr,hm⟩ := Finset.exists_mem_notMem_of_card_lt_card fewer
      exact ⟨r,Finset.mem_range.mp hr,fun i hi eqn => hm (Finset.mem_image.mpr ⟨i,hi,eqn⟩)⟩

end Roue687
