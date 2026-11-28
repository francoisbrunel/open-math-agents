module
public import VerificationPoids687

/-! Assembly for a wheel certificate whose records can split the class of 19.
    Group files import only Std. The interpretation is in NoyauPondere687. -/
@[expose] public section
namespace Branches19_687
open VerificationPoids687

def Witness (L N : Nat) (ps : List Nat) (j : Nat) : Prop :=
  ∃ F rows, rows.map Prod.fst = ps ∧ check F L N rows = true ∧
    digit B (F % (B^19-1)) j = 0

def Cases (L N : Nat) (ps : List Nat) (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → Witness L N ps j

theorem one {L N ps j} (h : Witness L N ps j) : Cases L N ps j j := by
  intro i lo hi
  simpa only [Nat.le_antisymm hi lo] using h

theorem joinCases {L N ps lo mid hi} (a : Cases L N ps lo mid)
    (b : Cases L N ps (mid+1) hi) : Cases L N ps lo hi := by
  intro i left right
  by_cases h : i ≤ mid
  · exact a i left h
  · exact b i (by omega) right

def Core (L N : Nat) (ps : List Nat) : Prop :=
  Encoded L N (19 :: ps) ∨ Cases L N ps 0 18

def Segment (ps : List Nat) (H lo hi : Nat) : Prop :=
  ∀ t, lo ≤ t → t ≤ hi → ∃ L N, t < L ∧ L+N ≤ t+H+1 ∧ Core L N ps

theorem leaf {ps H lo hi L N} (before : hi < L) (fits : L+N ≤ lo+H+1)
    (h : Core L N ps) : Segment ps H lo hi := by
  intro t left right
  exact ⟨L,N,by omega,by omega,h⟩

theorem join {ps H lo mid hi} (a : Segment ps H lo mid)
    (b : Segment ps H (mid+1) hi) : Segment ps H lo hi := by
  intro t left right
  by_cases h : t ≤ mid
  · exact a t left h
  · exact b t (by omega) right
end Branches19_687
