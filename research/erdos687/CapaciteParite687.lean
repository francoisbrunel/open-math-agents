import Paires687
import Roue687

/-! Capacity of one fresh class inside a sifted prefix. -/
namespace CapaciteParite687
open Progressions687 Extension687 Paires687

/-- In a fresh residue class the quotient indices again avoid one residue
    for each old prime. The zero-based interval permits J = p*k exactly. -/
theorem class_indices {z J p k : ℕ} (prime : p.Prime) (fresh : z < p)
    (len : J ≤ p*k) (b : ℕ → ℕ) (r : ℕ) :
    ∃ v : ℕ → ℕ, ((siftedIndices z J b).filter (fun i => i%p=r%p)).card ≤
      (siftedIndices z k v).card := by
  classical
  let t (q : ℕ) := if h : p.Coprime q then (Nat.chineseRemainder h r (b q)).val else 0
  let v (q : ℕ) := t q/p
  refine ⟨v,Finset.card_le_card_of_injOn (fun i : ℕ => i/p) ?_ ?_⟩
  · intro i hi
    obtain ⟨hS,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hJ,avoid⟩ := Finset.mem_filter.mp hS
    change i/p ∈ siftedIndices z k v
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul prime.pos).2
      (by simpa only [Nat.mul_comm k p] using (Finset.mem_range.mp hJ).trans_le len)),?_⟩
    intro q hq clash
    obtain ⟨qz,qprime⟩ := Nat.mem_primesLE.mp hq
    have cop : p.Coprime q := (Nat.coprime_primes prime qprime).2 (by omega)
    have crt : t q ≡ r [MOD p] ∧ t q ≡ b q [MOD q] := by
      dsimp only [t]
      rw [dif_pos cop]
      exact (Nat.chineseRemainder cop r (b q)).property
    have rem : i%p=t q%p := hr.trans crt.1.symm
    have hit : i ≡ t q [MOD q] := calc
      i = i%p+p*(i/p) := (Nat.mod_add_div _ _).symm
      _ ≡ i%p+p*(t q/p) [MOD q] := ((show i/p ≡ t q/p [MOD q] from clash).mul_left p).add_left _
      _ = t q := by rw [rem,Nat.mod_add_div]
    exact avoid q hq (hit.trans crt.2)
  · intro i hi j hj h
    change i/p=j/p at h
    have rem := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    calc i = i%p+p*(i/p) := (Nat.mod_add_div _ _).symm
         _ = j%p+p*(j/p) := by rw [rem,h]
         _ = j := Nat.mod_add_div _ _

/-- Conversely any residual pattern on the shorter interval can be
    realized along multiples of the fresh prime. -/
theorem realize_indices {z J p k : ℕ} (prime : p.Prime) (fresh : z < p)
    (room : ∀ i < k, p*i < J) (b : ℕ → ℕ) :
    ∃ a : ℕ → ℕ, (siftedIndices z k b).card ≤
      ((siftedIndices z J a).filter (fun n => n%p=0)).card := by
  let a (q : ℕ) := p*b q
  refine ⟨a,Finset.card_le_card_of_injOn (fun i : ℕ => p*i) ?_ ?_⟩
  · intro i hi
    obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (room i (Finset.mem_range.mp hI)),?_⟩,by simp⟩
    intro q hq hit
    obtain ⟨le,qprime⟩ := Nat.mem_primesLE.mp hq
    have cop : q.Coprime p := (Nat.coprime_primes qprime prime).2 (by omega)
    exact avoid q hq (Nat.ModEq.cancel_left_of_coprime cop (show p*i ≡ p*b q [MOD q] from hit))
  · intro i _ j _ eqn
    exact Nat.eq_of_mul_eq_mul_left prime.pos eqn

/-- The maximum possible load of one fresh class is exactly the maximum
    survivor count in a prefix of ceiling(J/p) indices. -/
theorem large_class_iff {z J p m : ℕ} (prime : p.Prime) (fresh : z < p) (nonempty : 0 < J) :
    (∃ (a : ℕ → ℕ) (r : ℕ), m ≤ ((siftedIndices z J a).filter (fun i => i%p=r%p)).card) ↔
      ∃ b, m ≤ (siftedIndices z ((J-1)/p+1) b).card := by
  let k := (J-1)/p+1
  have reach : J ≤ p*k := by
    have lt : J-1 < k*p := (Nat.div_lt_iff_lt_mul prime.pos).1 (Nat.lt_succ_self ((J-1)/p))
    rw [Nat.mul_comm p k]
    exact (by omega : J ≤ k*p)
  constructor
  · rintro ⟨a,r,large⟩
    obtain ⟨b,le⟩ := class_indices prime fresh reach a r
    exact ⟨b,large.trans le⟩
  · rintro ⟨b,large⟩
    have room (i : ℕ) (hi : i < k) : p*i < J := by
      have hi' : i ≤ (J-1)/p := by dsimp [k] at hi; omega
      have bound := (Nat.mul_le_mul_right p hi').trans (Nat.div_mul_le_self (J-1) p)
      rw [Nat.mul_comm] at bound
      omega
    obtain ⟨a,le⟩ := realize_indices prime fresh room b
    refine ⟨a,0,(large.trans le).trans (Finset.card_le_card ?_)⟩
    intro n hn
    obtain ⟨hs,zero⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hs,by simpa using zero⟩

/-- A single progression already permits all admissible m-tuples that
    fit in its quotient interval. -/
theorem class_iff_tuple {z J p m : ℕ} (prime : p.Prime) (fresh : z < p) (hn : 0 < J) (hm : m ≤ z) :
    (∃ (a : ℕ → ℕ) (r : ℕ), m ≤ ((siftedIndices z J a).filter (fun i => i%p=r%p)).card) ↔
      ∃ T ⊆ Finset.range ((J-1)/p+1), T.card=m ∧ Admissible T :=
  (large_class_iff prime fresh hn).trans (capacity_iff_tuple hm)

theorem from_short_capacity {x z J k m : ℕ} (len : J ≤ k*(z+1))
    (cap : ∀ v, (siftedIndices z k v).card ≤ m) (b : ℕ → ℕ)
    {p : ℕ} (hp : p ∈ x.primesLE \ z.primesLE) (r : ℕ) :
    ((siftedIndices z J b).filter (fun i => i%p=r%p)).card ≤ m := by
  obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
  have prime := (Nat.mem_primesLE.mp hin).2
  have fresh : z < p := lt_of_not_ge fun h => hout (Nat.mem_primesLE.mpr ⟨h,prime⟩)
  have reach : J ≤ p*k := (len.trans (Nat.mul_le_mul_left k fresh)).trans_eq (Nat.mul_comm k p)
  obtain ⟨v,le⟩ := class_indices prime fresh reach b r
  exact le.trans (cap v)

private def smallWheel (k a b : ℕ) := (Finset.range k).filter fun i => i%2 ≠ a ∧ i%3 ≠ b

private theorem cap2 {z : ℕ} (hz : 2 ≤ z) (v : ℕ → ℕ) :
    (siftedIndices z 2 v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hir,ia⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjr,ja⟩ := Finset.mem_filter.mp hj
  have two : 2 ∈ z.primesLE := Nat.mem_primesLE.mpr ⟨hz,Nat.prime_two⟩
  have := ia 2 two
  have := ja 2 two
  have := Finset.mem_range.mp hir
  have := Finset.mem_range.mp hjr
  omega

theorem singletons_through_two {x z J : ℕ} (hz : 2 ≤ z) (len : J ≤ 2*(z+1)) (b : ℕ → ℕ) :
    let S := siftedIndices z J b
    let P := x.primesLE \ z.primesLE
    Covered S P ↔ S.card ≤ P.card := by
  classical
  intro S P
  constructor
  · rintro ⟨a,ha⟩
    let C (p : ℕ) := S.filter fun i => i%p=a p%p
    have incl : S ⊆ P.biUnion C := by
      intro i hi
      obtain ⟨p,hp,hit⟩ := ha i hi
      exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hi,hit⟩⟩
    calc S.card ≤ (P.biUnion C).card := Finset.card_le_card incl
         _ ≤ ∑ p ∈ P, (C p).card := Finset.card_biUnion_le
         _ ≤ ∑ _p ∈ P, 1 := Finset.sum_le_sum fun p hp => from_short_capacity len (cap2 hz) b hp (a p)
         _ = _ := by simp
  · exact completes_of_card

/-- Through cutoff 13 the eight-point witness at length 27 defeats every
    possible assignment of seven fresh classes, including grouped assignments. -/
theorem sharp_uniform_26 {x z : ℕ} (hz : 13 ≤ z) (count : (x.primesLE \ z.primesLE).card ≤ 7) :
    ∃ b, ¬ Covered (siftedIndices z 27 b) (x.primesLE \ z.primesLE) := by
  obtain ⟨b,hb⟩ := Roue687.eight_can_survive_27 (z := z) (by omega)
  refine ⟨b,fun cover => ?_⟩
  have bound := (singletons_through_two (x := x) (z := z) (J := 27) (by omega) (by omega) b).1 cover
  omega

private theorem cap6 {z : ℕ} (hz : 3 ≤ z) (v : ℕ → ℕ) :
    (siftedIndices z 6 v).card ≤ 2 := by
  have h : ∀ a : Fin 2, ∀ b : Fin 3, (smallWheel 6 a b).card ≤ 2 := by decide
  apply (Finset.card_le_card ?_).trans (h ⟨v 2%2,Nat.mod_lt _ (by decide)⟩
    ⟨v 3%3,Nat.mod_lt _ (by decide)⟩)
  intro i hi
  obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hI,avoid 2 (Nat.mem_primesLE.mpr ⟨by omega,Nat.prime_two⟩),
    avoid 3 (Nat.mem_primesLE.mpr ⟨hz,by decide⟩)⟩

/-- Sieving by 2 and 3 extends the exact disjoint-pair criterion to six
    times the lower cutoff for the fresh moduli. -/
theorem pairs_through_six {x z J : ℕ} (hz : 3 ≤ z) (len : J ≤ 6*(z+1)) (b : ℕ → ℕ) :
    let S := siftedIndices z J b
    let P := x.primesLE \ z.primesLE
    Covered S P ↔ PairBudget S P :=
  covered_iff_pairs (fun _ hp r => from_short_capacity len (cap6 hz) b hp r)

/-- The seven-point wheel bound also applies to each individual fresh class
    on a prefix twenty-six times as long. -/
theorem seven_per_class {x z J : ℕ} (hz : 7 ≤ z) (len : J ≤ 26*(z+1))
    (b : ℕ → ℕ) {p : ℕ} (hp : p ∈ x.primesLE \ z.primesLE) (r : ℕ) :
    ((siftedIndices z J b).filter (fun i => i%p=r%p)).card ≤ 7 :=
  from_short_capacity len (Roue687.capacity_26 hz) b hp r

end CapaciteParite687
