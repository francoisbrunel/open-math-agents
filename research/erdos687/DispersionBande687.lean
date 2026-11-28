import EcartsMultiples687

/-! Fourth centered moment for coverage of the initial survivors. -/
namespace DispersionBande687
open Filter Transfert687 EcartsMultiples687
open scoped BigOperators

noncomputable def fourth (S P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (∑ r ∈ Finset.range p, ((p:ℝ)*(occupancy S p r:ℝ)-S.card)^4)/p

theorem deviation (S P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p) (a : ℕ → ℕ) :
    ((∑ p ∈ P, (occupancy S p (a p%p):ℝ))-harmonic P*(S.card:ℝ))^4 ≤
      (harmonic P)^3*fourth S P := by
  classical
  rcases P.eq_empty_or_nonempty with empty | ne
  · subst P
    simp [EcartsMultiples687.harmonic,fourth]
  let N (p : ℕ) := occupancy S p (a p%p)
  let h := harmonic P
  let s := (S.card:ℝ)
  have pp (p : ℕ) (hp : p∈P) : 0 < (p:ℝ) := by exact_mod_cast pos p hp
  have hp : 0<h := Finset.sum_pos (fun p hmem => one_div_pos.mpr (pp p hmem)) ne
  let w (p : ℕ) := ((1:ℝ)/p)/h
  let y (p : ℕ) := h*((p:ℝ)*N p-s)
  have norm : ∑ p ∈ P, w p=1 := by simp only [w,← Finset.sum_div]; exact div_self hp.ne'
  have jensen := ((show Even 4 by decide).convexOn_pow (𝕜 := ℝ)).map_sum_le
    (fun p (_ : p∈P) => (show 0 ≤ w p by dsimp [w]; positivity)) norm
    (p := y) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at jensen
  have mean : (∑ p ∈ P, w p*y p) = (∑ p ∈ P, (N p:ℝ))-h*s := by
    have eq : (∑ p ∈ P, w p*y p) = ∑ p ∈ P, ((N p:ℝ)-(1/p)*s) := by
      apply Finset.sum_congr rfl
      intro p hmem
      dsimp only [w,y]; field_simp [hp.ne',(pp p hmem).ne'] <;> ring
    rw [eq,Finset.sum_sub_distrib,← Finset.sum_mul]
    rfl
  have term (p : ℕ) (hmem : p∈P) : w p*(y p)^4 ≤
      h^3*((∑ r ∈ Finset.range p, ((p:ℝ)*(occupancy S p r:ℝ)-s)^4)/p) := by
    calc
      _ = h^3*((((p:ℝ)*N p-s)^4)/p) := by
        dsimp only [w,y]; field_simp [hp.ne',(pp p hmem).ne'] <;> ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (pp p hmem).le
        exact Finset.single_le_sum (f := fun r => ((p:ℝ)*(occupancy S p r:ℝ)-s)^4)
          (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.mod_lt (a p) (pos p hmem)))
  calc
    _ = (∑ p ∈ P, w p*y p)^4 := by rw [mean]
    _ ≤ ∑ p ∈ P, w p*(y p)^4 := jensen
    _ ≤ _ := by simpa only [fourth,Finset.mul_sum] using Finset.sum_le_sum term

def multiplicity (P : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) := (P.filter (fun p => n%p=a p%p)).card

/-- Count duplicate hits exactly on a complete cover. The available
fourth-moment budget is determined by the small-prime stock alone. -/
theorem overlap_budget (S P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p)
    (a : ℕ → ℕ) (cover : ∀ n ∈ S, ∃ p ∈ P, n%p=a p%p) :
    ((1-harmonic P)*(S.card:ℝ)+(∑ n ∈ S, ((multiplicity P a n-1:ℕ):ℝ)))^4 ≤
      (harmonic P)^3*fourth S P := by
  classical
  have count : (∑ n ∈ S, multiplicity P a n) = ∑ p ∈ P, occupancy S p (a p%p) := by
    simp only [multiplicity,occupancy,Finset.card_filter]
    exact Finset.sum_comm
  have hit (n : ℕ) (hn : n∈S) : 1 ≤ multiplicity P a n := by
    obtain ⟨p,hp,e⟩ := cover n hn
    exact Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,e⟩⟩
  have idn : (∑ n ∈ S, (multiplicity P a n-1))+S.card = ∑ p ∈ P, occupancy S p (a p%p) := calc
    _ = ∑ n ∈ S, (multiplicity P a n-1+1) := by simp [Finset.sum_add_distrib]
    _ = _ := (Finset.sum_congr rfl (fun n hn => Nat.sub_add_cancel (hit n hn))).trans count
  have idr : (∑ n ∈ S, ((multiplicity P a n-1:ℕ):ℝ))+S.card =
      ∑ p ∈ P, (occupancy S p (a p%p):ℝ) := by exact_mod_cast idn
  have upper := deviation S P pos a
  rw [← idr] at upper
  convert upper using 1 <;> ring

theorem required_fourth (S P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p)
    (short : harmonic P ≤ 1) (a : ℕ → ℕ) (cover : ∀ n ∈ S, ∃ p ∈ P, n%p=a p%p) :
    ((1-harmonic P)*(S.card:ℝ))^4 ≤ (harmonic P)^3*fourth S P := by
  apply le_trans _ (overlap_budget S P pos a cover)
  apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr short) (Nat.cast_nonneg _))
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

/-- The centered statistic expands into collisions of two, three, and
four independent draws of survivor positions. -/
theorem collision_identity (S : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    (∑ r ∈ Finset.range p, ((p:ℝ)*(occupancy S p r:ℝ)-S.card)^4)/p =
      (p:ℝ)^3*(∑ r ∈ Finset.range p, (occupancy S p r:ℝ)^4)
      -4*(S.card:ℝ)*(p:ℝ)^2*(∑ r ∈ Finset.range p, (occupancy S p r:ℝ)^3)
      +6*(S.card:ℝ)^2*(p:ℝ)*(∑ r ∈ Finset.range p, (occupancy S p r:ℝ)^2)
      -3*(S.card:ℝ)^4 := by
  let s := (S.card:ℝ)
  let n (r : ℕ) : ℝ := occupancy S p r
  have count : S.card = ∑ r ∈ Finset.range p, occupancy S p r :=
    Finset.card_eq_sum_card_fiberwise (f := fun i => i%p) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i hp))
  have total : ∑ r ∈ Finset.range p, n r = s := by
    dsimp only [n,s]
    exact_mod_cast count.symm
  have expand (r : ℕ) : ((p:ℝ)*n r-s)^4 =
      (p:ℝ)^4*(n r)^4-4*s*(p:ℝ)^3*(n r)^3+6*s^2*(p:ℝ)^2*(n r)^2
      -4*s^3*(p:ℝ)*n r+s^4 := by ring
  change (∑ r ∈ Finset.range p, ((p:ℝ)*n r-s)^4)/p = _
  simp_rw [expand]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul,total]
  apply (div_eq_iff (by exact_mod_cast hp.ne' : (p:ℝ) ≠ 0)).2
  dsimp only [n,s]; ring

/-- A single off-center thin profile can be tested using any subset and
one fourth moment; no growing order is required by this reduction. -/
theorem upper_of_fourth (m : ℕ) (hm : 2 ≤ m)
    (witness : ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
      ((survivors (k^m) ((k^m)^2) a).card:ℝ) ≤
        (24/(m:ℝ))*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ) →
      ∃ T ⊆ survivors (k^m) ((k^m)^2) a,
        let P := (k^(m+1)).primesLE \ (k^m).primesLE
        harmonic P ≤ 1 ∧ (harmonic P)^3*fourth T P < ((1-harmonic P)*(T.card:ℝ))^4) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^((2*(m:ℝ))/(m+1))) := by
  apply DensiteCarree687.upper_of_no_thin_completions m hm
  filter_upwards [witness] with k wit
  rintro ⟨a,thin,full⟩
  obtain ⟨T,sub,short,small⟩ := wit a thin
  apply (not_lt_of_ge (required_fourth T _ (fun p hp =>
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.pos) short a ?_)) small
  intro n hn
  obtain ⟨inside,avoid⟩ := Finset.mem_filter.mp (sub hn)
  obtain ⟨p,px,pr,hit⟩ := full n inside
  exact ⟨p,Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨px,pr⟩,fun h => avoid p h hit⟩,hit⟩

end DispersionBande687
#print axioms DispersionBande687.overlap_budget
#print axioms DispersionBande687.required_fourth
#print axioms DispersionBande687.collision_identity
#print axioms DispersionBande687.upper_of_fourth
