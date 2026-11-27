import Extremites687

/-! Use both ends of the same cover to rule out incompatible configurations
    among the survivors. -/
namespace Bords687
open Extension687 Transfert687 Progressions687

def rightResidue (y : ℕ) (a : ℕ → ℕ) (p : ℕ) := a p+(p-1)*(y+1)

theorem extend_given_cover_right {x z y J : ℕ} (hzx : z ≤ x) (a : ℕ → ℕ)
    (ha : ∀ n ∈ Finset.Icc 1 y, ∃ p ≤ z, p.Prime ∧ n ≡ a p [MOD p])
    (close : Completes (siftedIndices z J (rightResidue y a)) (x.primesLE \ z.primesLE)) :
    Green46.IsCoveredByResidues x (y+J) := by
  classical
  obtain ⟨r,hr⟩ := close
  let b := rightResidue y a
  let v (p : ℕ) := if p ≤ z then a p else r p+(y+1)
  refine ⟨v,?_⟩
  intro n hn
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
  by_cases inside : n ≤ y
  · obtain ⟨p,le,prime,h⟩ := ha n (Finset.mem_Icc.mpr ⟨lo,inside⟩)
    exact ⟨p,le.trans hzx,prime,by simpa [v,le] using h⟩
  · let i := n-(y+1)
    have pos : i+(y+1)=n := by dsimp [i]; omega
    have below : i < J := by dsimp [i]; omega
    by_cases live : i ∈ siftedIndices z J b
    · obtain ⟨p,hp,hit⟩ := hr i live
      obtain ⟨inP,out⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp inP
      have big : ¬p ≤ z := fun h => out (Nat.mem_primesLE.mpr ⟨h,prime⟩)
      exact ⟨p,le,prime,by simpa only [v,if_neg big,pos] using (show i ≡ r p [MOD p] from hit).add_right (y+1)⟩
    · have clash : ¬∀ p ∈ z.primesLE, i%p ≠ b p%p := fun h => live
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr below,h⟩)
      push Not at clash
      obtain ⟨p,hp,hit⟩ := clash
      obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
      have eqn : b p+(y+1) = a p+p*(y+1) := by
        dsimp [b,rightResidue]
        rw [Nat.add_assoc,← Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel prime.pos]
      have same : b p+(y+1) ≡ a p [MOD p] := by rw [eqn]; simp [Nat.ModEq]
      exact ⟨p,le.trans hzx,prime,by simpa only [v,if_pos le,pos] using
        (((show i ≡ b p [MOD p] from hit).add_right (y+1)).trans same)⟩

private def wheel (a b c d : ℕ) :=
  (Finset.range 27).filter fun i => i%2≠a ∧ i%3≠b ∧ i%5≠c ∧ i%7≠d

/-- The complete list of choices modulo 2,3,5,7 attaining eight survivors
    in [0,27). The four profiles contain three distinct point sets. -/
def exceptional (a b c d : ℕ) : Prop :=
  a=1 ∧ b=1 ∧ ((c=2 ∧ d=2) ∨ (c=3 ∧ d=1) ∨ (c=3 ∧ d=4) ∨ (c=4 ∧ d=3))

instance (a b c d : ℕ) : Decidable (exceptional a b c d) := by unfold exceptional; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem classify : ∀ a : Fin 2, ∀ b : Fin 3, ∀ c : Fin 5, ∀ d : Fin 7,
    7 < (wheel a b c d).card ↔ exceptional a b c d := by decide

theorem profile_of_eight {z : ℕ} (hz : 7 ≤ z) (a : ℕ → ℕ) (large : 7 < (siftedIndices z 27 a).card) :
    exceptional (a 2%2) (a 3%3) (a 5%5) (a 7%7) := by
  let r (p : ℕ) (hp : 0 < p) : Fin p := ⟨a p%p,Nat.mod_lt _ hp⟩
  apply (classify (r 2 (by decide)) (r 3 (by decide)) (r 5 (by decide)) (r 7 (by decide))).1
  apply large.trans_le (Finset.card_le_card ?_)
  intro i hi
  obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hI,?_⟩
  exact ⟨avoid 2 (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩),
    avoid 3 (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩),
    avoid 5 (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩),
    avoid 7 (Nat.mem_primesLE.mpr ⟨hz,by decide⟩)⟩

/-- If both ends of an old cover require eight singleton primes, both
    shifted profiles must belong to the same four-element list. -/
theorem growth_of_incompatible_profiles {x z : ℕ} (hz : 7 ≤ z) (hzx : z ≤ x)
    (fresh : 7 ≤ (x.primesLE \ z.primesLE).card)
    (different : ∀ a : ℕ → ℕ,
      let y := Erdos687.Y z
      let l := fun p => a p+27-1
      let r := rightResidue y a
      ¬(exceptional (l 2%2) (l 3%3) (l 5%5) (l 7%7) ∧
        exceptional (r 2%2) (r 3%3) (r 5%5) (r 7%7))) :
    Erdos687.Y z + 28 ≤ Erdos687.Y x := by
  let y := Erdos687.Y z
  obtain ⟨a,covered⟩ := optimal_cover z
  let l := fun p => a p+27-1
  let r := rightResidue y a
  have one : (siftedIndices z 27 l).card ≤ 7 ∨ (siftedIndices z 27 r).card ≤ 7 := by
    by_contra! bad
    exact different a ⟨profile_of_eight hz l bad.1,profile_of_eight hz r bad.2⟩
  have gain : y+27 ≤ Erdos687.Y x := by
    rcases one with left | right
    · exact le_Y_of_covered (extend_given_cover_left hzx a covered (completes_of_card (left.trans fresh)))
    · exact le_Y_of_covered (extend_given_cover_right hzx a covered (completes_of_card (right.trans fresh)))
  obtain ⟨m,hm⟩ := Extremites687.Y_odd (z := z) (by omega)
  obtain ⟨n,hn⟩ := Extremites687.Y_odd (z := x) (by omega)
  dsimp [y] at gain
  omega

theorem growth_if_not_divisible_by_three {x z : ℕ} (hz : 7 ≤ z) (hzx : z ≤ x)
    (fresh : 7 ≤ (x.primesLE \ z.primesLE).card) (hy : Erdos687.Y z%3 ≠ 0) :
    Erdos687.Y z+28 ≤ Erdos687.Y x := by
  apply growth_of_incompatible_profiles hz hzx fresh
  intro a
  dsimp only
  rintro ⟨left,right⟩
  have hL := left.2.1
  have hR := right.2.1
  change (a 3+27-1)%3=1 at hL
  change (a 3+(3-1)*(Erdos687.Y z+1))%3=1 at hR
  omega

def exceptionalLengths : Finset ℕ := {21,27,33,123,129,135,177,183,189}

private def five : Fin 4 → ℕ := ![2,3,3,4]
private def seven : Fin 4 → ℕ := ![2,1,4,3]

private theorem pattern {a b c d : ℕ} (h : exceptional a b c d) :
    ∃ j : Fin 4, c=five j ∧ d=seven j := by
  rcases h.2.2 with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem compatible_lengths : ∀ t : Fin 210, ∀ i j : Fin 4,
    (t.val+27)%2=0 → (t.val+27)%3=0 →
    (five j+(t.val+27))%5=five i → (seven j+(t.val+27))%7=seven i →
    t.val ∈ exceptionalLengths := by decide

/-- Beyond the uniform 26-position barrier, two opposite extensions give
    at least 28 positions for every old maximal length outside nine
    explicitly listed residues modulo 210. -/
theorem growth_outside_nine {x z : ℕ} (hz : 7 ≤ z) (hzx : z ≤ x)
    (fresh : 7 ≤ (x.primesLE \ z.primesLE).card)
    (hy : Erdos687.Y z%210 ∉ exceptionalLengths) : Erdos687.Y z+28 ≤ Erdos687.Y x := by
  apply growth_of_incompatible_profiles hz hzx fresh
  intro a
  let y := Erdos687.Y z
  let t : Fin 210 := ⟨y%210,Nat.mod_lt _ (by decide)⟩
  let l (p : ℕ) := a p+27-1
  let r := rightResidue y a
  change ¬(exceptional (l 2%2) (l 3%3) (l 5%5) (l 7%7) ∧ exceptional (r 2%2) (r 3%3) (r 5%5) (r 7%7))
  rintro ⟨hl,hr⟩
  change exceptional (l 2%2) (l 3%3) (l 5%5) (l 7%7) at hl
  change exceptional (r 2%2) (r 3%3) (r 5%5) (r 7%7) at hr
  have shift (p : ℕ) (hp : p ∣ 210) (pp : 0 < p) : (r p%p+(t.val+27))%p=l p%p := by
    have mt : t.val ≡ y [MOD p] := Nat.mod_mod_of_dvd y hp
    have offset : r p+(y+27) = (a p+26)+p*(y+1) := calc
      _ = (a p+26)+((p-1)*(y+1)+(y+1)) := by dsimp [r,rightResidue]; omega
      _ = _ := by rw [← Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel pp]
    have ll : l p = a p+26 := by dsimp [l]
    calc r p%p+(t.val+27) ≡ r p+(y+27) [MOD p] :=
           (Nat.mod_modEq (r p) p).add (mt.add_right 27)
         _ = (a p+26)+p*(y+1) := offset
         _ ≡ l p [MOD p] := by simp [Nat.ModEq,ll]
  obtain ⟨i,i5,i7⟩ := pattern hl
  obtain ⟨j,j5,j7⟩ := pattern hr
  have two := shift 2 (by decide) (by decide)
  have three := shift 3 (by decide) (by decide)
  rw [hr.1,hl.1] at two
  rw [hr.2.1,hl.2.1] at three
  apply hy
  exact compatible_lengths t i j (by omega) (by omega)
    (by simpa only [i5,j5] using shift 5 (by decide) (by decide))
    (by simpa only [i7,j7] using shift 7 (by decide) (by decide))

end Bords687
