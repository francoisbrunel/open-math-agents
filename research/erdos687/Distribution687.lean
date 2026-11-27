import FormalConjectures.ErdosProblems.«687»
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Exact generating function for the distribution of uncovered positions. -/
namespace Distribution687

abbrev Assignment (P : Finset ℕ) := (p : ↥P) → Fin p.val

noncomputable def misses (P S : Finset ℕ) (a : Assignment P) : Finset ℕ := by
  classical
  exact S.filter fun n => ∀ p, n%p.val≠(a p).val

noncomputable def allowed (T : Finset ℕ) (p : ℕ) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter fun r => ∀ n ∈ T, n%p≠r.val

noncomputable def choices (P T : Finset ℕ) : Finset (Assignment P) := by
  classical
  exact Finset.univ.filter fun a => ∀ p, a p ∈ allowed T p.val

/-- Avoidance constraints factor exactly over all the moduli. -/
theorem avoidance (P T : Finset ℕ) :
    (choices P T).card = ∏ p ∈ P, (allowed T p).card := by
  classical
  let e : ↥(choices P T) ≃ ((p : ↥P) → ↥(allowed T p.val)) := {
    toFun := fun a p => ⟨a.val p,(Finset.mem_filter.mp a.property).2 p⟩
    invFun := fun b => ⟨fun p => (b p).val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p => (b p).property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    _ = ∏ p : ↥P, (allowed T p.val).card := by
      simpa only [Fintype.card_coe,Fintype.card_pi] using Fintype.card_congr e
    _ = _ := Finset.prod_coe_sort P (fun p => (allowed T p).card)

theorem allowed_card (T : Finset ℕ) {p : ℕ} (pp : 0<p) :
    (allowed T p).card = p-(T.image (fun n => n%p)).card := by
  classical
  let R := T.image (fun n => (⟨n%p,Nat.mod_lt n pp⟩ : Fin p))
  have eq : allowed T p = Finset.univ \ R := by
    ext r
    simp [allowed,R,Fin.ext_iff]
  have embed : R.image Fin.val = T.image (fun n => n%p) := by simp [R,Finset.image_image,Function.comp_def]
  rw [eq,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
    ← embed,Finset.card_image_of_injective _ Fin.val_injective]

private theorem subset_iff {P S T : Finset ℕ} (inside : T⊆S) (a : Assignment P) :
    T⊆misses P S a ↔ a ∈ choices P T := by
  classical
  simp only [misses,choices,allowed,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro all p n hn
    exact (Finset.mem_filter.mp (all hn)).2 p
  · intro all n hn
    exact Finset.mem_filter.mpr ⟨inside hn,fun p => all p n hn⟩

private theorem expansion (U : Finset ℕ) (t : ℤ) :
    (1+t)^U.card = ∑ T ∈ U.powerset, t^T.card := by
  simpa [add_comm] using Finset.prod_add (fun _ : ℕ => t) (fun _ => (1:ℤ)) U

/-- The right-hand side uses only occupied-residue counts of subsets of S. -/
theorem generating (P S : Finset ℕ) (t : ℤ) :
    (∑ a : Assignment P, (1+t)^(misses P S a).card) =
    ∑ T ∈ S.powerset, t^T.card*(∏ p ∈ P, ((allowed T p).card:ℤ)) := by
  classical
  have row (a : Assignment P) : (1+t)^(misses P S a).card =
      ∑ T ∈ S.powerset, if a ∈ choices P T then t^T.card else 0 := by
    rw [expansion,← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_filter,Finset.mem_powerset]
    constructor
    · intro h
      have inside : T⊆S := h.trans (Finset.filter_subset _ _)
      exact ⟨inside,(subset_iff inside a).mp h⟩
    · rintro ⟨inside,h⟩
      exact (subset_iff inside a).mpr h
  simp_rw [row]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have eq : (Finset.univ.filter (fun a : Assignment P => a ∈ choices P T)) = choices P T := by ext; simp
  rw [eq,avoidance]
  push_cast
  ring

noncomputable def covers (P S : Finset ℕ) : Finset (Assignment P) := by
  classical
  exact Finset.univ.filter fun a => misses P S a=∅

theorem inclusion_exclusion (P S : Finset ℕ) :
    ((covers P S).card:ℤ) =
    ∑ T ∈ S.powerset, (-1:ℤ)^T.card*(∏ p ∈ P, ((allowed T p).card:ℤ)) := by
  classical
  rw [← generating]
  rw [show 1+(-1:ℤ)=0 by decide]
  have atZero (a : Assignment P) : (0:ℤ)^(misses P S a).card =
      if misses P S a=∅ then 1 else 0 := by
    by_cases empty : misses P S a=∅
    · simp [empty]
    · simp [empty,zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr empty))]
  simp [atZero,covers,← Finset.sum_filter]

theorem factorial_moment (P S : Finset ℕ) (k : ℕ) :
    (∑ a : Assignment P, (misses P S a).card.choose k) =
    ∑ T ∈ S.powersetCard k, ∏ p ∈ P, (allowed T p).card := by
  classical
  have per (a : Assignment P) :
      (misses P S a).card.choose k =
        ∑ T ∈ S.powersetCard k, if a ∈ choices P T then 1 else 0 := by
    rw [← Finset.card_powersetCard,← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    apply congrArg Finset.card
    ext T
    simp only [Finset.mem_powersetCard,Finset.mem_filter]
    constructor
    · rintro ⟨h,size⟩
      have inside : T⊆S := h.trans (Finset.filter_subset _ _)
      exact ⟨⟨inside,size⟩,(subset_iff inside a).mp h⟩
    · rintro ⟨⟨inside,size⟩,h⟩
      exact ⟨(subset_iff inside a).mpr h,size⟩
  simp_rw [per]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  have eq : (Finset.univ.filter (fun a : Assignment P => a ∈ choices P T)) = choices P T := by ext; simp
  rw [eq,avoidance]
  push_cast <;> rfl

theorem cover_possible (x H : ℕ) :
    0<(covers x.primesLE (Finset.Icc 1 H)).card ↔ Green46.IsCoveredByResidues x H := by
  classical
  let P := x.primesLE
  let S := Finset.Icc 1 H
  constructor
  · intro h
    obtain ⟨a,ha⟩ := Finset.card_pos.mp h
    have empty : misses P S a=∅ := (Finset.mem_filter.mp ha).2
    let b (p : ℕ) := if hp : p ∈ P then (a ⟨p,hp⟩).val else 0
    refine ⟨b,?_⟩
    intro n hn
    by_contra! none
    have mem : n ∈ misses P S a := by
      apply Finset.mem_filter.mpr
      refine ⟨hn,fun p h => ?_⟩
      obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp p.property
      exact none p.val le prime (by simpa [b,p.property,Nat.ModEq,Nat.mod_eq_of_lt (a p).isLt] using h)
    simpa [empty] using mem
  · rintro ⟨b,hb⟩
    let a (p : ↥P) : Fin p.val := ⟨b p.val%p.val,Nat.mod_lt _ (Nat.mem_primesLE.mp p.property).2.pos⟩
    apply Finset.card_pos.mpr
    refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩⟩
    intro n hn
    obtain ⟨inside,none⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,le,prime,hit⟩ := hb n inside
    exact none ⟨p,Nat.mem_primesLE.mpr ⟨le,prime⟩⟩ hit

/-- Positive sign is equivalent to a full cover. Zero is equivalent
    to an obstruction, expressed entirely with finite residue counts. -/
theorem threshold (x H : ℕ) : H≤Erdos687.Y x ↔
    0 < ∑ T ∈ (Finset.Icc 1 H).powerset, (-1:ℤ)^T.card*
      ∏ p ∈ x.primesLE, ((p-(T.image (fun n => n%p)).card:ℕ):ℤ) := by
  classical
  let S := Finset.Icc 1 H
  have val := inclusion_exclusion x.primesLE S
  have eq (T : Finset ℕ) :
      (∏ p ∈ x.primesLE,((allowed T p).card:ℤ)) =
      ∏ p ∈ x.primesLE, ((p-(T.image (fun n => n%p)).card:ℕ):ℤ) :=
    Finset.prod_congr rfl (fun p hp => by rw [allowed_card T (Nat.mem_primesLE.mp hp).2.pos])
  simp_rw [eq] at val
  change H≤Erdos687.Y x ↔ (0:ℤ)<_
  rw [← val,Nat.cast_pos,cover_possible]
  have bounded : BddAbove {h : ℕ | Green46.IsCoveredByResidues x h} :=
    ⟨primorial x,fun _ covered => (Erdos687.lt_primorial_of_isCoveredByResidues covered).le⟩
  constructor
  · intro le
    have nonempty : {h : ℕ | Green46.IsCoveredByResidues x h}.Nonempty :=
      ⟨0,fun _ => 0,by simp⟩
    have optimal : Green46.IsCoveredByResidues x (Erdos687.Y x) :=
      Nat.sSup_mem nonempty bounded
    obtain ⟨a,all⟩ := optimal
    exact ⟨a,fun n hn => all n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans le⟩)⟩
  · exact fun h => le_csSup bounded h

/-- One complete assignment would alone contribute the entire threshold
    to this nonnegative moment. The bound concerns all residue choices. -/
theorem moment_excludes (x H m r : ℕ) (small :
    (∑ a : Assignment x.primesLE,
      (Int.natAbs (((misses x.primesLE (Finset.Icc 1 H) a).card:ℤ)-m))^(2*r)) < m^(2*r)) :
    ¬Green46.IsCoveredByResidues x H := by
  classical
  intro possible
  obtain ⟨a,inside⟩ := Finset.card_pos.mp ((cover_possible x H).mpr possible)
  have empty : misses _ _ a=∅ := (Finset.mem_filter.mp inside).2
  have term := Finset.single_le_sum (f := fun a : Assignment x.primesLE =>
    (Int.natAbs (((misses x.primesLE (Finset.Icc 1 H) a).card:ℤ)-m))^(2*r))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  rw [empty] at term
  exact (Nat.not_lt_of_ge (by simpa using term)) small

/-- Every starting position of an H-window in a longer covered interval
    gives a different assignment, including when the original classes
    have several prime hits at a position. -/
theorem shifts {x y H : ℕ} (covered : Green46.IsCoveredByResidues x y) (fits : H≤y) :
    y-H+1 ≤ (covers x.primesLE (Finset.Icc 1 H)).card := by
  classical
  let P := x.primesLE
  let t := y-H
  let pad := primorial x-t
  have width := Erdos687.lt_primorial_of_isCoveredByResidues covered
  have sum : t+pad=primorial x := by dsimp [pad,t]; omega
  obtain ⟨a,all⟩ := covered
  let g (j : ℕ) : Assignment P := fun p =>
    ⟨(a p.val+pad+j)%p.val,Nat.mod_lt _ (Nat.mem_primesLE.mp p.property).2.pos⟩
  have inside {j : ℕ} (hj : j≤t) : g j ∈ covers P (Finset.Icc 1 H) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro n hn
    obtain ⟨interval,avoid⟩ := Finset.mem_filter.mp hn
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp interval
    obtain ⟨p,px,pr,hit⟩ := all (n+(t-j)) (Finset.mem_Icc.mpr ⟨by omega,by dsimp [t] at *; omega⟩)
    let q : ↥P := ⟨p,Nat.mem_primesLE.mpr ⟨px,pr⟩⟩
    apply avoid q
    change n ≡ a p+pad+j [MOD p]
    have per : primorial x ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (pr.dvd_primorial_iff.mpr px)
    calc
      n ≡ n+primorial x [MOD p] := by simpa using (per.add_left n).symm
      _ = n+(t-j)+(pad+j) := by omega
      _ ≡ a p+(pad+j) [MOD p] := hit.add_right _
      _ = _ := by omega
  have distinct {j k : ℕ} (le : j<k) (top : k≤t) (eq : g j=g k) : False := by
    have each (p : ℕ) (hp : p ∈ P) : p ∣ k-j := by
      have same := congrArg Fin.val (congrFun eq ⟨p,hp⟩)
      have mod : a p+pad+j ≡ a p+pad+k [MOD p] := same
      exact (Nat.ModEq.add_left_cancel' (a p+pad) mod).dvd'
    have divides : primorial x ∣ k-j := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_primes_dvd _ (fun p hp => (Nat.mem_primesLE.mp hp).2.prime) each
    have up := Nat.le_of_dvd (Nat.sub_pos_of_lt le) divides
    dsimp [t] at top
    omega
  have count := Finset.card_le_card_of_injOn (s := Finset.range (t+1)) (t := covers P (Finset.Icc 1 H))
    g (fun j hj => inside (by have := Finset.mem_range.mp hj; omega))
    (fun j hj k hk eq => by
      have a := Finset.mem_range.mp hj
      have b := Finset.mem_range.mp hk
      rcases lt_trichotomy j k with h|h|h
      · exact (distinct h (by omega) eq).elim
      · exact h
      · exact (distinct h (by omega) eq.symm).elim)
  simpa only [Finset.card_range] using count

theorem upper_from_count (x H : ℕ) : Erdos687.Y x < H+(covers x.primesLE (Finset.Icc 1 H)).card := by
  by_cases fits : H≤Erdos687.Y x
  · have nonempty : {h : ℕ | Green46.IsCoveredByResidues x h}.Nonempty := ⟨0,fun _ => 0,by simp⟩
    have bounded : BddAbove {h : ℕ | Green46.IsCoveredByResidues x h} :=
      ⟨primorial x,fun _ covered => (Erdos687.lt_primorial_of_isCoveredByResidues covered).le⟩
    have covered : Green46.IsCoveredByResidues x (Erdos687.Y x) := Nat.sSup_mem nonempty bounded
    have count := shifts covered fits
    omega
  · omega

/-- To bound the maximum up to a factor of two, it suffices to bound
    the number of covering assignments by the length of the interval. -/
theorem twice_of_few {x H : ℕ} (few : (covers x.primesLE (Finset.Icc 1 H)).card≤H) :
    Erdos687.Y x < 2*H := by have h := upper_from_count x H; omega

theorem twice_from_moment {x H m r : ℕ} (mean : 0 < m)
    (bound : (∑ a : Assignment x.primesLE,
      (Int.natAbs (((misses x.primesLE (Finset.Icc 1 H) a).card:ℤ)-m))^(2*r)) ≤ H*m^(2*r)) :
    Erdos687.Y x < 2*H := by
  classical
  let S := Finset.Icc 1 H
  let P := x.primesLE
  let V (a : Assignment P) := (Int.natAbs (((misses P S a).card:ℤ)-m))^(2*r)
  have eq (a : Assignment P) (h : a ∈ covers P S) : V a=m^(2*r) := by
    have none : misses P S a=∅ := (Finset.mem_filter.mp h).2
    simp [V,none]
  have count : (covers P S).card*m^(2*r)≤H*m^(2*r) := calc
    _ = ∑ _a ∈ covers P S,m^(2*r) := by simp
    _ = ∑ a ∈ covers P S,V a := Finset.sum_congr rfl (fun a h => (eq a h).symm)
    _ ≤ ∑ a : Assignment P,V a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
    _ ≤ _ := bound
  exact twice_of_few (Nat.le_of_mul_le_mul_right count (Nat.pow_pos mean))

/-- The first length at which the number of full assignments is at most
    the length. The definition only counts assignments. -/
noncomputable def countThreshold (x : ℕ) : ℕ :=
  sInf {H | (covers x.primesLE (Finset.Icc 1 H)).card ≤ H}

theorem threshold_comparison (x : ℕ) :
    countThreshold x ≤ Erdos687.Y x + 1 ∧ Erdos687.Y x < 2*countThreshold x := by
  let A := {H : ℕ | (covers x.primesLE (Finset.Icc 1 H)).card ≤ H}
  have zero : (covers x.primesLE (Finset.Icc 1 (Erdos687.Y x+1))).card=0 := by
    by_contra! positive
    have h := (cover_possible x _).mp (Nat.pos_of_ne_zero positive)
    have bounded : BddAbove {y : ℕ | Green46.IsCoveredByResidues x y} :=
      ⟨primorial x,fun _ covered => (Erdos687.lt_primorial_of_isCoveredByResidues covered).le⟩
    exact Nat.not_succ_le_self _ (le_csSup bounded h)
  have high : Erdos687.Y x+1 ∈ A := by
    change (covers x.primesLE (Finset.Icc 1 (Erdos687.Y x+1))).card ≤ Erdos687.Y x+1
    rw [zero]
    exact Nat.zero_le _
  have h : sInf A ∈ A := Nat.sInf_mem ⟨_,high⟩
  exact ⟨Nat.sInf_le high,twice_of_few h⟩

end Distribution687

#print axioms Distribution687.factorial_moment
#print axioms Distribution687.threshold
#print axioms Distribution687.threshold_comparison
#print axioms Distribution687.twice_from_moment
