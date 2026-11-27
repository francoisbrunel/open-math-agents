import Std

/-! Executable input and local assembly for ordinary-kernel certificate replay. -/
namespace VerificationPoids687

abbrev B : Nat := 2^32
abbrev half : Nat := 2^31
abbrev ceiling : Nat := 65535
def digit (B F i : Nat) := F/B^i%B
def ones (B n : Nat) := (B^n-1)/(B-1)
def phase (L p : Nat) := (p-L%p)%p

def rowCheck (F L : Nat) (q : Nat × Nat) : Bool :=
  let p := q.1
  let c := q.2
  let foldedWord := F%(B^p-1)
  if p ≤ 17 then decide (0<p ∧ digit B foldedWord (phase L p)=0)
  else
    let pad := foldedWord+(half-1-c)*ones B p
    decide (c<half ∧ pad &&& ((half-1)*ones B p) = pad)

def check (F L N : Nat) (rows : List (Nat × Nat)) : Bool :=
  decide (F<B^N ∧ N*ceiling<half ∧ F &&& (ceiling*ones B N)=F ∧
    (rows.map Prod.snd).sum < F%(B-1)) && rows.all (rowCheck F L)

def Encoded (L N : Nat) (ps : List Nat) : Prop :=
  ∃ F rows, rows.map Prod.fst=ps ∧ check F L N rows=true

def Segment (ps : List Nat) (H lo hi : Nat) : Prop :=
  ∀ t, lo≤t → t≤hi → ∃ L N, t<L ∧ L+N≤t+H+1 ∧ Encoded L N ps

theorem leaf {ps H lo hi L N} (before : hi<L) (fits : L+N≤lo+H+1)
    (certificate : Encoded L N ps) : Segment ps H lo hi := by
  intro t left right
  exact ⟨L,N,by omega,by omega,certificate⟩

theorem join {ps H lo mid hi} (l : Segment ps H lo mid) (r : Segment ps H (mid+1) hi) :
    Segment ps H lo hi := by
  intro t low high
  by_cases h : t≤mid
  · exact l t low h
  · exact r t (by omega) high

end VerificationPoids687
