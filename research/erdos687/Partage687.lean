import Bords687

/-! Three further exceptional lengths allow a split extension. -/
namespace Partage687
open Bords687 Extension687 Progressions687 Transfert687

def exceptions : Finset ℕ := {21,27,33,123,177,183}

private def wheelCount (J : ℕ) (b : ℕ → ℕ) :=
  ((Finset.range J).filter fun i => i%2≠b 2%2 ∧ i%3≠b 3%3 ∧ i%5≠b 5%5 ∧ i%7≠b 7%7).card

private def base (a : Fin 2) (b : Fin 3) (c : Fin 5) (d : Fin 7) (p : ℕ) : ℕ :=
  if p=2 then a else if p=3 then b else if p=5 then c else d

private def oldLength : Fin 3 → ℕ := ![129,135,189]
private def addedLeft : Fin 3 → ℕ := ![14,4,14]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private theorem three_cases : ∀ t : Fin 3, ∀ a : Fin 2, ∀ b : Fin 3, ∀ c : Fin 5, ∀ d : Fin 7,
    let v := base a b c d
    let L := addedLeft t
    wheelCount 27 (leftResidue 27 v) ≤ 7 ∨
    wheelCount 27 (rightResidue (oldLength t) v) ≤ 7 ∨
    wheelCount L (leftResidue L v) + wheelCount (28-L) (rightResidue (oldLength t) v) ≤ 7 := by decide

private theorem restrict_to_wheel {z : ℕ} (hz : 7 ≤ z) (J : ℕ) (a b : ℕ → ℕ)
    (eqn : ∀ p, p=2 ∨ p=3 ∨ p=5 ∨ p=7 → b p ≡ a p [MOD p]) :
    (siftedIndices z J a).card ≤ wheelCount J b := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hJ,avoid⟩ := Finset.mem_filter.mp hi
  have clear (p : ℕ) (h : p=2 ∨ p=3 ∨ p=5 ∨ p=7) : i%p ≠ b p%p := by
    have pin : p ∈ z.primesLE := by
      rcases h with rfl | rfl | rfl | rfl <;> exact Nat.mem_primesLE.mpr ⟨by omega,by decide⟩
    exact fun clash => avoid p pin (clash.trans (eqn p h))
  exact Finset.mem_filter.mpr ⟨hJ,clear 2 (by decide),clear 3 (by decide),clear 5 (by decide),clear 7 (by decide)⟩

/-- Out of the 105 odd residue classes of the old maximal length modulo
    210, only the listed six can defeat this seven-singleton argument. -/
theorem growth_outside_six {x z : ℕ} (hz : 7 ≤ z) (hzx : z ≤ x)
    (fresh : 7 ≤ (x.primesLE \ z.primesLE).card) (avoid : Erdos687.Y z%210 ∉ exceptions) :
    Erdos687.Y z + 28 ≤ Erdos687.Y x := by
  classical
  by_cases outside : Erdos687.Y z%210 ∉ exceptionalLengths
  · exact growth_outside_nine hz hzx fresh outside
  push Not at outside
  let y := Erdos687.Y z
  have which : y%210=129 ∨ y%210=135 ∨ y%210=189 := by
    simp only [exceptions,exceptionalLengths,Finset.mem_insert,Finset.mem_singleton] at outside avoid
    dsimp [y]; tauto
  obtain ⟨t,ht⟩ : ∃ t : Fin 3, oldLength t=y%210 := by
    rcases which with h | h | h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  obtain ⟨a,covered⟩ := optimal_cover z
  let f (p : ℕ) (hp : 0 < p) : Fin p := ⟨a p%p,Nat.mod_lt _ hp⟩
  let b := base (f 2 (by decide)) (f 3 (by decide)) (f 5 (by decide)) (f 7 (by decide))
  let L := addedLeft t
  have small : L ≤ 28 := by fin_cases t <;> decide
  have same (p : ℕ) (h : p=2 ∨ p=3 ∨ p=5 ∨ p=7) : b p ≡ a p [MOD p] := by
    rcases h with rfl | rfl | rfl | rfl <;> simp [b,base,f,Nat.ModEq]
  have hL (M : ℕ) : (siftedIndices z M (leftResidue M a)).card ≤ wheelCount M (leftResidue M b) :=
    restrict_to_wheel hz M _ _ fun p h => (same p h).add_right _
  have hR (M : ℕ) : (siftedIndices z M (rightResidue y a)).card ≤ wheelCount M (rightResidue (oldLength t) b) := by
    apply restrict_to_wheel hz
    intro p h
    have divides : p ∣ 210 := by rcases h with rfl | rfl | rfl | rfl <;> decide
    have shifted : oldLength t ≡ y [MOD p] := by rw [ht]; exact Nat.mod_mod_of_dvd y divides
    exact (same p h).add ((shifted.add_right 1).mul_left (p-1))
  have use_split (M N : ℕ) (size : 27 ≤ M+N)
      (cap : (siftedIndices z M (leftResidue M a)).card + (siftedIndices z N (rightResidue y a)).card ≤ 7) :
      Erdos687.Y z + 28 ≤ Erdos687.Y x := by
    have g := le_Y_of_covered (extend_both (y := y) hzx a covered (cap.trans fresh))
    obtain ⟨m,hm⟩ := Extremites687.Y_odd (z := z) (by omega)
    obtain ⟨n,hn⟩ := Extremites687.Y_odd (z := x) (by omega)
    dsimp [y] at g
    omega
  have choices := three_cases t (f 2 (by decide)) (f 3 (by decide)) (f 5 (by decide)) (f 7 (by decide))
  change wheelCount 27 (leftResidue 27 b) ≤ 7 ∨ wheelCount 27 (rightResidue (oldLength t) b) ≤ 7 ∨
    wheelCount L (leftResidue L b)+wheelCount (28-L) (rightResidue (oldLength t) b) ≤ 7 at choices
  rcases choices with left | right | both
  · exact use_split 27 0 (by decide) (by simpa [siftedIndices] using (hL 27).trans left)
  · exact use_split 0 27 (by decide) (by simpa [siftedIndices] using (hR 27).trans right)
  · exact use_split L (28-L) (by omega) ((Nat.add_le_add (hL L) (hR (28-L))).trans both)

end Partage687
