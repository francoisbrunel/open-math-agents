import CribleTransfert687

/-! Lower-side application: extend an existing cover without changing the
relative positions in its already covered portion. -/
namespace Extension687
open Transfert687 Progressions687

theorem assign_images (S P : Finset ℕ) (f : ℕ → ℕ) (h : S.card ≤ P.card) :
    ∃ r : ℕ → ℕ, ∀ i ∈ S, ∃ p ∈ P, r p = f i := by
  classical
  obtain ⟨e⟩ : Nonempty (↥S ↪ ↥P) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  let r (p : ℕ) := if hm : ∃ j : S, (e j).val = p then f (Classical.choose hm).val else 0
  refine ⟨r,?_⟩
  intro i hi
  let j : S := ⟨i,hi⟩
  have ex : ∃ k : S, (e k).val = (e j).val := ⟨j,rfl⟩
  have eqn : Classical.choose ex = j := e.injective (Subtype.ext (Classical.choose_spec ex))
  exact ⟨(e j).val,(e j).property,by simp only [r,dif_pos ex,eqn]; rfl⟩

theorem extend_cover {x z y J : ℕ} (hzx : z ≤ x)
    (covered : Green46.IsCoveredByResidues z y)
    (budget : ∀ b : ℕ → ℕ, (siftedIndices z J b).card ≤ (x.primesLE \ z.primesLE).card) :
    Green46.IsCoveredByResidues x (y+J) := by
  classical
  obtain ⟨a,ha⟩ := covered
  by_cases h0 : J = 0
  · subst J
    refine ⟨a,?_⟩
    intro n hn
    obtain ⟨p,hp,prime,he⟩ := ha n (by simpa using hn)
    exact ⟨p,hp.trans hzx,prime,he⟩
  let b (p : ℕ) := a p + J - 1
  obtain ⟨r,hr⟩ := assign_images _ _ (fun i => i+1) (budget b)
  let v (p : ℕ) := if p ≤ z then a p+J else r p
  refine ⟨v,?_⟩
  intro n hn
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
  by_cases htail : J < n
  · obtain ⟨p,hp,prime,he⟩ := ha (n-J) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    refine ⟨p,hp.trans hzx,prime,?_⟩
    simpa only [v,if_pos hp,Nat.sub_add_cancel htail.le] using he.add_right J
  · let i := n-1
    have hin : i+1 = n := by dsimp [i]; omega
    by_cases hsurv : i ∈ siftedIndices z J b
    · obtain ⟨p,hp,he⟩ := hr i hsurv
      obtain ⟨hpx,hnot⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hpx
      have hlarge : ¬p ≤ z := fun h => hnot (Nat.mem_primesLE.mpr ⟨h,prime⟩)
      exact ⟨p,le,prime,by simp only [v,if_neg hlarge,he,hin]; rfl⟩
    · have clash : ¬∀ p ∈ z.primesLE, i%p ≠ b p%p := fun h => hsurv
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [i]; omega),h⟩)
      push Not at clash
      obtain ⟨p,hp,he⟩ := clash
      obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
      have eqn : b p+1 = a p+J := by dsimp [b]; omega
      refine ⟨p,le.trans hzx,prime,?_⟩
      simpa only [v,if_pos le,hin,eqn] using (show i ≡ b p [MOD p] from he).add_right 1

theorem growth_from_capacity {x z J : ℕ} (hzx : z ≤ x)
    (h : ∀ b : ℕ → ℕ, (siftedIndices z J b).card ≤ (x.primesLE \ z.primesLE).card) :
    Erdos687.Y z + J ≤ Erdos687.Y x := by
  have nonempty : {n : ℕ | Green46.IsCoveredByResidues z n}.Nonempty :=
    ⟨0,fun _ => 0,by simp⟩
  have bounded : BddAbove {n : ℕ | Green46.IsCoveredByResidues z n} :=
    ⟨primorial z,fun _ hn => (Erdos687.lt_primorial_of_isCoveredByResidues hn).le⟩
  have cov : Green46.IsCoveredByResidues z (Erdos687.Y z) := Nat.sSup_mem nonempty bounded
  exact le_Y_of_covered (extend_cover hzx cov h)

/-- A lower bound for an increment of Y, from the number of fresh primes. -/
theorem growth_from_fresh_primes {x z J : ℕ} (hzx : z ≤ x) (hJz : J ≤ z)
    (h : 255*(1+(J:ℝ)/Real.log J) ≤ ((x.primesLE \ z.primesLE).card:ℝ)) :
    Erdos687.Y z + J ≤ Erdos687.Y x := by
  apply growth_from_capacity hzx
  intro b
  exact_mod_cast (CribleTransfert687.index_upper J z b hJz).trans h

/-- Each prime misses some residue among the elements of an admissible tuple. -/
def Admissible (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ i ∈ S, i % p ≠ r

/-- Exact threshold: once z ≥ k, some sieve leaves k indices in [0,J)
    precisely when an admissible k-tuple fits in that interval. -/
theorem capacity_iff_tuple {z J k : ℕ} (hk : k ≤ z) :
    (∃ b, k ≤ (siftedIndices z J b).card) ↔
      ∃ S ⊆ Finset.range J, S.card = k ∧ Admissible S := by
  classical
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hb
    refine ⟨S,fun i hi => (Finset.mem_filter.mp (hS hi)).1,hcard,?_⟩
    intro p prime
    by_cases hp : p ≤ z
    · exact ⟨b p % p,Nat.mod_lt _ prime.pos,fun i hi =>
        (Finset.mem_filter.mp (hS hi)).2 p (Nat.mem_primesLE.mpr ⟨hp,prime⟩)⟩
    · have fewer : (S.image (fun i => i % p)).card < (Finset.range p).card := by
        rw [Finset.card_range]
        exact Finset.card_image_le.trans_lt (by omega)
      obtain ⟨r,hr,miss⟩ := Finset.exists_mem_notMem_of_card_lt_card fewer
      exact ⟨r,Finset.mem_range.mp hr,fun i hi eqn => miss (Finset.mem_image.mpr ⟨i,hi,eqn⟩)⟩
  · rintro ⟨S,hS,hcard,ha⟩
    let b (p : ℕ) := if hp : p.Prime then Classical.choose (ha p hp) else 0
    refine ⟨b,hcard ▸ Finset.card_le_card (show S ⊆ siftedIndices z J b from ?_)⟩
    intro i hi
    refine Finset.mem_filter.mpr ⟨hS hi,?_⟩
    intro p hp
    have prime := (Nat.mem_primesLE.mp hp).2
    obtain ⟨hlt,miss⟩ := Classical.choose_spec (ha p prime)
    simpa only [b,dif_pos prime,Nat.mod_eq_of_lt hlt] using miss i hi

/-- If r new primes are available and no admissible (r+1)-tuple fits
    in [0,J), every optimal cover through z extends by J positions. -/
theorem growth_from_tuple_diameter {x z J r : ℕ} (hzx : z ≤ x) (hk : r+1 ≤ z)
    (hr : r ≤ (x.primesLE \ z.primesLE).card)
    (hn : ¬∃ S ⊆ Finset.range J, S.card = r+1 ∧ Admissible S) :
    Erdos687.Y z + J ≤ Erdos687.Y x := by
  apply growth_from_capacity hzx
  intro b
  have no : ¬r+1 ≤ (siftedIndices z J b).card :=
    fun h => hn ((capacity_iff_tuple hk).mp ⟨b,h⟩)
  omega

end Extension687
