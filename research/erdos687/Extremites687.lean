import Roue687
import Paires687

/-! At the first length exceeding a uniform capacity bound, an extremal
    tuple uses both endpoints. A new prime dividing their distance can
    cover them together. -/
namespace Extremites687
open Extension687 Progressions687 Transfert687

private theorem erase_ends {z J r : ℕ}
    (cap : ∀ b, (siftedIndices z J b).card ≤ r) (b : ℕ → ℕ) :
    let S := siftedIndices z (J+1) b
    (S.erase J).card ≤ r ∧ (S.erase 0).card ≤ r := by
  classical
  let S := siftedIndices z (J+1) b
  constructor
  · apply (Finset.card_le_card ?_).trans (cap b)
    intro i hi
    obtain ⟨hne,hs⟩ := Finset.mem_erase.mp hi
    obtain ⟨hb,avoid⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hb; omega),avoid⟩
  · let v (p : ℕ) := b p+p-1
    apply (Finset.card_le_card_of_injOn (fun i : ℕ => i-1) ?_ ?_).trans (cap v)
    · intro i hi
      obtain ⟨hne,hs⟩ := Finset.mem_erase.mp hi
      obtain ⟨hb,avoid⟩ := Finset.mem_filter.mp hs
      have hiJ := Finset.mem_range.mp hb
      change i-1 ∈ siftedIndices z J v
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩
      intro p hp eqn
      have pp := (Nat.mem_primesLE.mp hp).2.pos
      have iadd : i-1+1 = i := by omega
      have padd : v p+1 = b p+p := by dsimp [v]; omega
      have ht := (show i-1 ≡ v p [MOD p] from eqn).add_right 1
      rw [iadd,padd] at ht
      exact avoid p hp (by simpa [Nat.ModEq] using ht)
    · intro i hi j hj eqn
      have h1 := (Finset.mem_erase.mp hi).1
      have h2 := (Finset.mem_erase.mp hj).1
      change i-1 = j-1 at eqn
      omega

theorem endpoint_gain {x z J r p : ℕ} (hzx : z ≤ x) (hJ : 0 < J)
    (cap : ∀ b, (siftedIndices z J b).card ≤ r)
    (fresh : r ≤ (x.primesLE \ z.primesLE).card)
    (hp : p ∈ x.primesLE \ z.primesLE) (hdvd : p ∣ J) :
    Erdos687.Y z + (J+1) ≤ Erdos687.Y x := by
  classical
  apply growth_from_completion hzx
  intro b
  let S := siftedIndices z (J+1) b
  let P := x.primesLE \ z.primesLE
  by_cases fit : S.card ≤ P.card
  · exact completes_of_card fit
  obtain ⟨hR,hL⟩ := erase_ends cap b
  change (S.erase J).card ≤ r at hR
  change (S.erase 0).card ≤ r at hL
  change r ≤ P.card at fresh
  have hzero : 0 ∈ S := by
    by_contra h
    rw [Finset.erase_eq_of_notMem h] at hL
    omega
  have hlast : J ∈ S := by
    by_contra h
    rw [Finset.erase_eq_of_notMem h] at hR
    omega
  have hs := Finset.card_erase_add_one hlast
  apply Paires687.covered_of_pairs
  refine ⟨{p},Finset.singleton_subset_iff.mpr hp,fun _ => {0,J},fun _ => 0,?_,?_,?_⟩
  · intro q hq
    have qe : q = p := Finset.mem_singleton.mp hq
    subst q
    refine ⟨by simp [Ne.symm hJ.ne'],?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · subst i; exact ⟨hzero,rfl⟩
    · have ij := Finset.mem_singleton.mp h
      subst i
      exact ⟨hlast,by simp [Nat.mod_eq_zero_of_dvd hdvd]⟩
  · simp
  · simp only [Finset.card_singleton]
    change S.card ≤ P.card+1
    omega

/-- Maximal covers through 2 have odd length: if the length were even,
    one of the two adjacent boundary points would use the old class of 2. -/
theorem Y_odd {z : ℕ} (hz : 2 ≤ z) : Odd (Erdos687.Y z) := by
  let y := Erdos687.Y z
  change Odd y
  by_contra no
  have even : y%2 = 0 := by rw [Nat.odd_iff] at no; omega
  obtain ⟨a,ha⟩ := optimal_cover z
  have longer : Green46.IsCoveredByResidues z (y+1) := by
    by_cases h : a 2%2 = 0
    · refine ⟨fun p => a p+1,?_⟩
      intro n hn
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
      by_cases first : n=1
      · subst n
        exact ⟨2,hz,Nat.prime_two,by change 1%2 = (a 2+1)%2; omega⟩
      · obtain ⟨p,hp,prime,he⟩ := ha (n-1) (Finset.mem_Icc.mpr ⟨by omega,by change n-1 ≤ y; omega⟩)
        exact ⟨p,hp,prime,by simpa only [Nat.sub_add_cancel lo] using he.add_right 1⟩
    · refine ⟨a,?_⟩
      intro n hn
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
      by_cases ht : n ≤ y
      · exact ha n (Finset.mem_Icc.mpr ⟨lo,ht⟩)
      · exact ⟨2,hz,Nat.prime_two,by change n%2 = a 2%2; omega⟩
  have impossible : y+1 ≤ y := le_Y_of_covered longer
  omega

/-- An exact parity reduction for computational covers. The odd primes
    must cover the zero-based interval with half as many positions. -/
theorem cover_iff_odd_primes {x y : ℕ} (hx : 2 ≤ x) :
    Green46.IsCoveredByResidues x y ↔
      ∃ b : ℕ → ℕ, ∀ i < y/2, ∃ p ∈ x.primesLE, p ≠ 2 ∧ i%p = b p%p := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    let t := if a 2%2=0 then 1 else 2
    let f (i : ℕ) := 2*i+t
    let b (p : ℕ) := if h : ∃ j, f j%p=a p%p then Classical.choose h else 0
    refine ⟨b,?_⟩
    intro i hi
    have ht : t=1 ∨ t=2 := by by_cases h : a 2%2=0 <;> simp [t,h]
    obtain ⟨p,hpx,prime,hit⟩ := ha (f i) (Finset.mem_Icc.mpr
      ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩)
    have odd : p ≠ 2 := by
      rintro rfl
      change (2*i+t)%2 = a 2%2 at hit
      dsimp [t] at hit
      split at hit <;> omega
    have ex : ∃ j, f j%p=a p%p := ⟨i,hit⟩
    have congruence : f i ≡ f (b p) [MOD p] := by
      change f i%p = f (b p)%p
      rw [hit]
      simpa [b,ex] using (Classical.choose_spec ex).symm
    have cop := (Nat.coprime_primes prime Nat.prime_two).2 odd
    exact ⟨p,Nat.mem_primesLE.mpr ⟨hpx,prime⟩,odd,
      Nat.ModEq.cancel_left_of_coprime cop (Nat.ModEq.add_right_cancel' t congruence)⟩
  · rintro ⟨b,hb⟩
    let a (p : ℕ) := if p=2 then 1 else 2*(b p+1)
    refine ⟨a,?_⟩
    intro n hn
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
    by_cases h : n%2=1
    · exact ⟨2,hx,Nat.prime_two,by simpa [Nat.ModEq,a] using h⟩
    · let i := n/2-1
      obtain ⟨p,hp,odd,he⟩ := hb i (by dsimp [i]; omega)
      have eqn : 2*(i+1)=n := by dsimp [i]; omega
      obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
      exact ⟨p,le,prime,by simpa only [a,if_neg odd,eqn] using
        ((show i ≡ b p [MOD p] from he).add_right 1).mul_left 2⟩

/-- With 13 among seven fresh primes the sharp singleton gain of 26 becomes
    at least 28. The two extra positions use pairing and parity. -/
theorem seven_with_13_extend_by_28 {x z : ℕ} (hz : 7 ≤ z) (hzx : z ≤ x)
    (fresh : 7 ≤ (x.primesLE \ z.primesLE).card) (h13 : 13 ∈ x.primesLE \ z.primesLE) :
    Erdos687.Y z + 28 ≤ Erdos687.Y x := by
  have h := endpoint_gain hzx (by decide : 0 < 26) (Roue687.capacity_26 hz) fresh h13 (by decide)
  obtain ⟨k,hk⟩ := Y_odd (z := z) (by omega)
  obtain ⟨l,hl⟩ := Y_odd (z := x) (by omega)
  omega

end Extremites687
