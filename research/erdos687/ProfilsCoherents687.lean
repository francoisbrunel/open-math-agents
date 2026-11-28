import ClassesImposees687
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Baire.Lemmas

/-! Passing from bounds for individual infinite assignments to a uniform
bound on the covering maximum. CRT absorbs the cost of a fixed prefix.
The bound may be established on any nonmeagre set of infinite profiles. -/
namespace ProfilsCoherents687
open Set Filter
open scoped Asymptotics
abbrev Rows := ℕ → ℕ
def covers (a : Rows) (x H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 1 H, ∃ p ≤ x, p.Prime ∧ n ≡ a p [MOD p]

private theorem shorten {a : Rows} {x H h : ℕ} (c : covers a x H) (le : h ≤ H) : covers a x h := by
  intro n hn
  obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
  exact c n (Finset.mem_Icc.mpr ⟨lo,up.trans le⟩)

private theorem open_covers (x H : ℕ) : IsOpen {a : Rows | covers a x H} := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  apply Filter.mem_of_superset ((PiNat.isOpen_cylinder (fun _ => ℕ) a (x+1)).mem_nhds
    (PiNat.self_mem_cylinder a _))
  intro b hb n hn
  obtain ⟨p,px,pr,hit⟩ := ha n hn
  exact ⟨p,px,pr,by rwa [(PiNat.mem_cylinder_iff.mp hb) p (by omega)]⟩

def boundedAt (u h : ℕ → ℕ) (M N : ℕ) : Set Rows :=
  ⋂ n, ⋂ (_ : N ≤ n), {a : Rows | covers a (u n) (M*h n+1)}ᶜ

def good (u h : ℕ → ℕ) : Set Rows := ⋃ i : ℕ × ℕ, boundedAt u h i.1 i.2

private theorem closed_at (u h : ℕ → ℕ) (M N : ℕ) : IsClosed (boundedAt u h M N) :=
  isClosed_iInter (fun n => isClosed_iInter (fun _ => (open_covers (u n) (M*h n+1)).isClosed_compl))

theorem prescribed_through (x K : ℕ) (b : Rows) :
    ∃ a : Rows, (∀ p ≤ K, a p = b p) ∧ covers a x (Erdos687.Y x-(primorial K-1)) := by
  obtain ⟨r,agree,full⟩ := ClassesImposees687.at_maximum x K.primesLE
    (fun p hp => (Nat.mem_primesLE.mp hp).2) b
  let a := fun p => if p ≤ K then b p else r p
  refine ⟨a,fun i hi => by simp [a,hi],?_⟩
  intro n hn
  obtain ⟨p,px,pr,hit⟩ := full n hn
  refine ⟨p,px,pr,?_⟩
  by_cases small : p ≤ K
  · simpa [a,small] using hit.trans (agree p (Nat.mem_primesLE.mpr ⟨small,pr⟩))
  · simpa [a,small] using hit

private theorem prescribed (x K : ℕ) (b : Rows) :
    ∃ a ∈ PiNat.cylinder b K, covers a x (Erdos687.Y x-(primorial K-1)) := by
  obtain ⟨a,agree,hit⟩ := prescribed_through x K b
  exact ⟨a,PiNat.mem_cylinder_iff.mpr (fun p hp => agree p hp.le),hit⟩

/-- Even the starting threshold and multiplicative constant may initially
depend on the entire infinite profile. A uniform additive loss is one
fixed primorial and is independent of the cutoff. -/
theorem uniform_of_nonmeagre (u h : ℕ → ℕ) (many : ¬IsMeagre (good u h)) :
    ∃ M D N : ℕ, ∀ n ≥ N, Erdos687.Y (u n) ≤ M*h n+D := by
  classical
  obtain ⟨i,inside⟩ : ∃ i : ℕ × ℕ, (interior (boundedAt u h i.1 i.2)).Nonempty := by
    by_contra! none
    apply many
    apply isMeagre_iUnion
    intro i
    apply IsNowhereDense.isMeagre
    rw [IsNowhereDense,(closed_at u h i.1 i.2).closure_eq]
    exact none i
  obtain ⟨v,hv⟩ := inside
  obtain ⟨U,⟨b,K,rfl⟩,_,inc⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hv isOpen_interior
  refine ⟨i.1,primorial K,i.2,?_⟩
  intro n hn
  obtain ⟨a,pre,full⟩ := prescribed (u n) K b
  have yes : a ∈ boundedAt u h i.1 i.2 := interior_subset (inc pre)
  have no : ¬covers a (u n) (i.1*h n+1) := Set.mem_iInter.mp (Set.mem_iInter.mp yes n) hn
  by_contra! counter
  exact no (shorten full (by omega))

theorem contains_all_of_uniform (u h : ℕ → ℕ) (M N : ℕ)
    (bound : ∀ n ≥ N, Erdos687.Y (u n) ≤ M*h n) : good u h = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  apply Set.mem_iUnion.mpr
  refine ⟨(M,N),Set.mem_iInter.mpr (fun n => Set.mem_iInter.mpr (fun hn c => ?_))⟩
  have lower : M*h n+1 ≤ Erdos687.Y (u n) := by
    apply le_csSup (s := {H : ℕ | Green46.IsCoveredByResidues (u n) H})
      (a := M*h n+1) ⟨primorial (u n),fun _ cov => (Erdos687.lt_primorial_of_isCoveredByResidues cov).le⟩
    exact ⟨a,c⟩
  have up := bound n hn
  omega

/-- A category criterion for an actual asymptotic upper estimate of Y.
Only the cutoff sequence and the target scale are chosen uniformly. -/
theorem upper_of_nonmeagre (u h : ℕ → ℕ) (positive : ∀ᶠ n in atTop, 1 ≤ h n)
    (many : ¬IsMeagre (good u h)) :
    (fun n => (Erdos687.Y (u n):ℝ)) =O[atTop] (fun n => (h n:ℝ)) := by
  obtain ⟨M,D,N,bound⟩ := uniform_of_nonmeagre u h many
  apply Asymptotics.IsBigO.of_bound ((M:ℝ)+D)
  filter_upwards [positive,eventually_ge_atTop N] with n hn nN
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have inc : D ≤ D*h n := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left D hn
  have b := (bound n nN).trans (Nat.add_le_add_left inc (M*h n))
  exact_mod_cast (show Erdos687.Y (u n) ≤ (M+D)*h n by simpa only [Nat.add_mul] using b)

/-- A single coherent assignment reaches the maximum up to any prescribed
diverging additive error infinitely often. Such assignments form a
residual set in the product topology. -/
theorem near_optimal_residual (u e : ℕ → ℕ) (large : Tendsto e atTop atTop) :
    {a : Rows | ∀ N, ∃ n ≥ N, covers a (u n) (Erdos687.Y (u n)-e n)} ∈ residual Rows := by
  let U := fun N : ℕ => ⋃ n, ⋃ (_ : N ≤ n),
    {a : Rows | covers a (u n) (Erdos687.Y (u n)-e n)}
  have residualU (N : ℕ) : U N ∈ residual Rows := by
    apply residual_of_dense_open
    · exact isOpen_iUnion (fun n => isOpen_iUnion (fun _ => open_covers _ _))
    · apply dense_iff_inter_open.mpr
      intro V op ne
      obtain ⟨v,hv⟩ := ne
      obtain ⟨_,⟨b,K,rfl⟩,_,inc⟩ :=
        (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hv op
      obtain ⟨n,hn,margin⟩ := ((Filter.eventually_ge_atTop N).and
        (large.eventually_ge_atTop (primorial K))).exists
      obtain ⟨a,pre,full⟩ := prescribed (u n) K b
      exact ⟨a,inc pre,Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hn,shorten full (by omega)⟩⟩⟩
  have all := countable_iInter_mem.mpr residualU
  apply Filter.mem_of_superset all
  intro a ha N
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp ha N)
  obtain ⟨atN,hit⟩ := Set.mem_iUnion.mp hn
  exact ⟨n,atN,hit⟩

private noncomputable def stage (u : ℕ → ℕ) : ℕ → Rows
  | 0 => Classical.choose (prescribed_through (u 0) 0 (fun _ => 0))
  | j+1 => Classical.choose (prescribed_through (u (j+1)) (u j) (stage u j))

/-- Simultaneous near-maximality at every prescribed increasing cutoff.
The explicit loss at a stage depends only on the preceding cutoff. -/
theorem simultaneous (u : ℕ → ℕ) (grow : StrictMono u) :
    ∃ a : Rows, covers a (u 0) (Erdos687.Y (u 0)) ∧ ∀ j,
      covers a (u (j+1)) (Erdos687.Y (u (j+1))-(primorial (u j)-1)) := by
  classical
  have next (j : ℕ) := Classical.choose_spec (prescribed_through (u (j+1)) (u j) (stage u j))
  have stable {i j : ℕ} (le : i ≤ j) {p : ℕ} (old : p ≤ u i) : stage u j p=stage u i p := by
    induction j,le using Nat.le_induction with
    | base => rfl
    | succ j ij ih =>
      exact ((next j).1 p (old.trans (grow.monotone ij))).trans ih
  let a := fun p => stage u p p
  have agree (j p : ℕ) (up : p ≤ u j) : a p=stage u j p := by
    rcases le_total j p with jp|pj
    · exact stable jp up
    · exact (stable pj (grow.id_le p)).symm
  have inherit (j H : ℕ) (h : covers (stage u j) (u j) H) : covers a (u j) H := by
    intro n hn
    obtain ⟨p,pj,pr,hit⟩ := h n hn
    exact ⟨p,pj,pr,by rwa [agree j p pj]⟩
  refine ⟨a,inherit 0 _ ?_,fun j => inherit (j+1) _ (next j).2⟩
  simpa only [primorial_zero,Nat.sub_self,Nat.sub_zero,stage] using
    (Classical.choose_spec (prescribed_through (u 0) 0 (fun _ => 0))).2

end ProfilsCoherents687
#print axioms ProfilsCoherents687.uniform_of_nonmeagre
#print axioms ProfilsCoherents687.upper_of_nonmeagre
#print axioms ProfilsCoherents687.near_optimal_residual
#print axioms ProfilsCoherents687.simultaneous
