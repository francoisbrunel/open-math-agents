import DensiteCarree687
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.MeanInequalities

/-! A necessary condition for a completion that only measures the initial
survivor set. Falling factorials count tuples with distinct entries. -/
namespace EcartsMultiples687
open Filter Transfert687
open scoped BigOperators

def occupancy (S : Finset ℕ) (p r : ℕ) : ℕ :=
  (S.filter (fun n => n%p=r)).card

noncomputable def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1:ℝ)/p

def energy (S P : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ p ∈ P, p^j * ∑ r ∈ Finset.range p, (occupancy S p r).descFactorial (j+1)

/-- Necessary for completion, simultaneously on all subsets of the stock.
No choice of the final residue classes occurs in the inequality. -/
theorem cover_moment (S P : Finset ℕ) (j : ℕ) (pos : ∀ p ∈ P, 0 < p)
    (a : ℕ → ℕ) (cover : ∀ n ∈ S, ∃ p ∈ P, n%p=a p%p) :
    ((S.card-j*P.card:ℕ):ℝ)^(j+1) ≤ (harmonic P)^j*(energy S P j:ℝ) := by
  classical
  rcases P.eq_empty_or_nonempty with empty | ne
  · subst P
    have es : S=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro n hn; simpa using cover n hn)
    simp [es,harmonic,energy]
  let C (p : ℕ) := S.filter fun n => n%p=a p%p
  let v (p : ℕ) := (C p).card-j
  have sub : S ⊆ P.biUnion C := by
    intro n hn
    obtain ⟨p,hp,eq⟩ := cover n hn
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hn,eq⟩⟩
  have slots : S.card ≤ ∑ p ∈ P, (C p).card := (Finset.card_le_card sub).trans Finset.card_biUnion_le
  have low : S.card-j*P.card ≤ ∑ p ∈ P, v p := by
    have up : (∑ p ∈ P, (C p).card) ≤ ∑ p ∈ P, (v p+j) :=
      Finset.sum_le_sum (fun p _ => by dsimp [v]; omega)
    rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_comm P.card j] at up
    omega
  let h := harmonic P
  have pp (p : ℕ) (hp : p∈P) : 0 < (p:ℝ) := by exact_mod_cast pos p hp
  have hp : 0<h := Finset.sum_pos (fun p hmem => one_div_pos.mpr (pp p hmem)) ne
  let w (p : ℕ) := ((1:ℝ)/p)/h
  let y (p : ℕ) := h*p*(v p:ℝ)
  have norm : ∑ p ∈ P, w p = 1 := by
    simp only [w,← Finset.sum_div]
    exact div_self hp.ne'
  have jensen := (convexOn_pow (𝕜 := ℝ) (j+1)).map_sum_le
    (fun p (_ : p∈P) => (show 0 ≤ w p by dsimp [w]; positivity)) norm
    (p := y) (fun p (_ : p∈P) => (show 0 ≤ y p by dsimp [y]; positivity))
  simp only [smul_eq_mul] at jensen
  have mean : (∑ p ∈ P, w p*y p) = ∑ p ∈ P, (v p:ℝ) := by
    apply Finset.sum_congr rfl
    intro p hmem
    dsimp [w,y]; field_simp [hp.ne',(pp p hmem).ne']
  rw [mean] at jensen
  have term (p : ℕ) (hmem : p∈P) :
      w p*(y p)^(j+1) ≤ h^j*((p^j * ∑ r ∈ Finset.range p,
        (occupancy S p r).descFactorial (j+1):ℕ):ℝ) := by
    have fall : (v p)^(j+1) ≤ ((C p).card).descFactorial (j+1) := by
      simpa [v] using Nat.pow_sub_le_descFactorial (C p).card (j+1)
    have one : (v p)^(j+1) ≤ ∑ r ∈ Finset.range p, (occupancy S p r).descFactorial (j+1) :=
      fall.trans (Finset.single_le_sum (f := fun r => (occupancy S p r).descFactorial (j+1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.mod_lt (a p) (pos p hmem))))
    calc
      _ = h^j*((p:ℝ)^j*(v p:ℝ)^(j+1)) := by
        dsimp only [w,y]
        simp only [mul_pow,pow_succ]
        field_simp [hp.ne',(pp p hmem).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mul_le_mul_left (p^j) one) (by positivity)
  calc
    _ ≤ (∑ p ∈ P, (v p:ℝ))^(j+1) := pow_le_pow_left₀ (by positivity) (by exact_mod_cast low) _
    _ ≤ ∑ p ∈ P, w p*(y p)^(j+1) := jensen
    _ ≤ _ := by
      simpa only [energy,Nat.cast_sum,Finset.mul_sum] using Finset.sum_le_sum term

/-- A bound on the tuple statistic on even one subset suffices to
rule out a whole square-scale profile and interpolate a power saving. -/
theorem upper_of_tuple_bound (m : ℕ) (hm : 2 ≤ m)
    (witness : ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
      ((survivors (k^m) ((k^m)^2) a).card:ℝ) ≤
        (24/(m:ℝ))*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ) →
      ∃ T ⊆ survivors (k^m) ((k^m)^2) a, ∃ j : ℕ,
        let P := (k^(m+1)).primesLE \ (k^m).primesLE
        (harmonic P)^j*(energy T P j:ℝ) < ((T.card-j*P.card:ℕ):ℝ)^(j+1)) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^((2*(m:ℝ))/(m+1))) := by
  apply DensiteCarree687.upper_of_no_thin_completions m hm
  filter_upwards [witness] with k wit
  rintro ⟨a,thin,full⟩
  obtain ⟨T,sub,j,small⟩ := wit a thin
  apply (not_lt_of_ge (cover_moment T _ j (fun p hp =>
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.pos) a ?_)) small
  intro n hn
  obtain ⟨inside,avoid⟩ := Finset.mem_filter.mp (sub hn)
  obtain ⟨p,px,pr,hit⟩ := full n inside
  exact ⟨p,Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨px,pr⟩,fun h => avoid p h hit⟩,hit⟩

private theorem row_floor (S : Finset ℕ) {p : ℕ} (hp : 0 < p) (j : ℕ) :
    ((S.card-j*p:ℕ):ℝ)^(j+1) ≤
      (p^j * ∑ r ∈ Finset.range p, (occupancy S p r).descFactorial (j+1):ℕ) := by
  let v (r : ℕ) := occupancy S p r-j
  have total : S.card = ∑ r ∈ Finset.range p, occupancy S p r :=
    Finset.card_eq_sum_card_fiberwise (f := fun n => n%p) (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp))
  have low : S.card-j*p ≤ ∑ r ∈ Finset.range p, v r := by
    have aux : (∑ r ∈ Finset.range p, occupancy S p r) ≤ ∑ r ∈ Finset.range p, (v r+j) :=
      Finset.sum_le_sum (fun r _ => by dsimp [v]; omega)
    rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Finset.card_range,mul_comm p j] at aux
    omega
  have jensen := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.range p) (f := fun r => (v r:ℝ))
    (show (1:ℝ) ≤ ((j+1:ℕ):ℝ) by exact_mod_cast (show 1 ≤ j+1 by omega))
    (fun _ _ => Nat.cast_nonneg _)
  rw [show ((j+1:ℕ):ℝ)-1=(j:ℝ) by push_cast; ring] at jensen
  simp only [Real.rpow_natCast,Finset.card_range] at jensen
  calc
    _ ≤ (∑ r ∈ Finset.range p, (v r:ℝ))^(j+1) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast low) _
    _ ≤ _ := jensen
    _ ≤ _ := by
      push_cast
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r _
      exact_mod_cast (show (v r)^(j+1) ≤ (occupancy S p r).descFactorial (j+1) by
        simpa [v] using Nat.pow_sub_le_descFactorial (occupancy S p r) (j+1))

/-- If this parameter condition holds, the moment inequality holds for
every possible test set, even ones for which completion is impossible. -/
theorem order_barrier (S P : Finset ℕ) (j : ℕ) (pos : ∀ p ∈ P, 0 < p)
    (bar : 1 ≤ (harmonic P)^j*((P.filter fun p => p ≤ P.card).card:ℝ)) :
    ((S.card-j*P.card:ℕ):ℝ)^(j+1) ≤ (harmonic P)^j*(energy S P j:ℝ) := by
  let R := P.filter (fun p => p ≤ P.card)
  let V := ((S.card-j*P.card:ℕ):ℝ)^(j+1)
  let f (p : ℕ) := p^j * ∑ r ∈ Finset.range p, (occupancy S p r).descFactorial (j+1)
  have each (p : ℕ) (hp : p∈R) : V ≤ (f p:ℝ) := by
    obtain ⟨inside,le⟩ := Finset.mem_filter.mp hp
    apply le_trans _ (row_floor S (pos p inside) j)
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.sub_le_sub_left (Nat.mul_le_mul_left j le) S.card
  have budget : (R.card:ℝ)*V ≤ (energy S P j:ℝ) := calc
    _ = ∑ _p ∈ R, V := by simp
    _ ≤ ∑ p ∈ R, (f p:ℝ) := Finset.sum_le_sum each
    _ ≤ _ := by exact_mod_cast (Finset.sum_le_sum_of_subset (f := f) (Finset.filter_subset _ P))
  have hnon : 0 ≤ harmonic P := Finset.sum_nonneg (fun _ _ => by positivity)
  have vnon : 0 ≤ V := by dsimp [V]; positivity
  calc
    _ = 1*V := (one_mul V).symm
    _ ≤ ((harmonic P)^j*R.card)*V := mul_le_mul_of_nonneg_right bar vnon
    _ = (harmonic P)^j*((R.card:ℝ)*V) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left budget (pow_nonneg hnon j)

end EcartsMultiples687
#print axioms EcartsMultiples687.cover_moment
#print axioms EcartsMultiples687.upper_of_tuple_bound
#print axioms EcartsMultiples687.order_barrier
