import StockSource687

/-! Quantitative stock left after the full sieve and a further sparse
    collection of arbitrarily large prime moduli. -/
namespace SurvieTotale687
open Filter Transfert687 GainVariable687

def remaining (S P : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ := by
  classical
  exact S.filter fun n => ∀ p ∈ P, n%p ≠ a p%p

theorem finite_loss (S P : Finset ℕ) (a : ℕ → ℕ) :
    S.card ≤ (remaining S P a).card + ∑ p ∈ P, charge S a p := by
  classical
  let C (p : ℕ) := S.filter fun n => n%p=a p%p
  have incl : S ⊆ remaining S P a ∪ P.biUnion C := by
    intro n hn
    by_cases h : ∀ p ∈ P, n%p ≠ a p%p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,h⟩)
    · push Not at h
      obtain ⟨p,hp,e⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hn,e⟩⟩)
  exact (Finset.card_le_card incl).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_biUnion_le _))

private theorem band_remaining {z x N : ℕ} (h : z ≤ x) (a : ℕ → ℕ) :
    remaining (survivors z N a) (x.primesLE \ z.primesLE) a = survivors x N a := by
  classical
  ext i
  simp only [remaining,survivors,Finset.mem_filter,Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hi,old⟩,newer⟩
    refine ⟨hi,?_⟩
    intro p hp
    by_cases hm : p ∈ z.primesLE
    · exact old p hm
    · exact newer p ⟨hp,hm⟩
  · rintro ⟨hi,avoid⟩
    refine ⟨⟨hi,fun p hp => avoid p ?_⟩,fun p hp => avoid p hp.1⟩
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans h,prime⟩

/-- A uniform positive stock persists after adjoining up to x/log x further
    prime classes. Those primes can have arbitrarily large moduli. -/
theorem robust_stock (source : InterfaceSource687.statement) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/2 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (E : Finset ℕ),
        (∀ p ∈ E, x < p ∧ p.Prime) → (E.card:ℝ) ≤ (x:ℝ)/Real.log x →
        c*stockUnit d x ≤ ((remaining (survivors x (length d x) a) E a).card:ℝ) := by
  classical
  obtain ⟨c,hc,hs⟩ := StockSource687.stock_of_published (StockSource687.source_of_interface source)
  let d := min (1/2:ℝ) (c/210)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hh : d ≤ 1/2 := min_le_left _ _
  have delta : 210*d ≤ c := by
    have := min_le_right (1/2:ℝ) (c/210)
    dsimp [d]; linarith
  refine ⟨d,hd,hh,c/4,by positivity,?_⟩
  have tends : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs d hd hh,CribleTransfert687.uniform_progression_35 hd hh,
    CribleTransfert687.progression_at_reference hd hh,reciprocal_band hd hh,
    tends.eventually_ge_atTop 4,(Real.tendsto_log_atTop.comp tends).eventually_ge_atTop (140/c),
    eventually_ge_atTop (1:ℕ)] with x hstock hband hlarge hmass hL hll hx
  intro a E hE size
  let L := Real.log (x:ℝ)
  let V := classUnit d x
  let W := stockUnit d x
  let z := ⌊top d x⌋₊
  let N := length d x
  let S := survivors z N a
  let T := survivors x N a
  let P := x.primesLE \ z.primesLE
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have Lp : 0 < L := by change 4 ≤ L at hL; linarith
  have LLp : 0 ≤ Real.log L := Real.log_nonneg (by change 4 ≤ L at hL; linarith)
  have Vn : 0 ≤ V := div_nonneg (Nat.cast_nonneg _) Lp.le
  have Wn : 0 ≤ W := mul_nonneg Vn (div_nonneg LLp Lp.le)
  have top_le : top d x ≤ (x:ℝ) := div_le_self xp.le (Real.one_le_rpow (by change 4 ≤ L at hL; linarith) hd.le)
  have zle : z ≤ x := Nat.floor_le_of_le top_le
  have incl : T ⊆ S := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hi,fun p hp => avoid p ?_⟩
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans zle,prime⟩
  have loss1 : (∑ p ∈ P, (charge S a p:ℝ)) ≤ (c/2)*W := calc
    _ ≤ ∑ p ∈ P, 35*(V/p) := Finset.sum_le_sum (hband a)
    _ = (35*V)*(∑ p ∈ P, (1:ℝ)/p) := by simp only [Finset.mul_sum,mul_one_div,mul_div_assoc]
    _ ≤ (35*V)*(3*d*Real.log L/L) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (105*d)*W := by dsimp [W,stockUnit,V,L]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) Wn
  have loss2 : (∑ p ∈ E, (charge T a p:ℝ)) ≤ (c/4)*W := calc
    _ ≤ ∑ _p ∈ E, 35*(V/x) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨gt,prime⟩ := hE p hp
      have mono : charge T a p ≤ charge S a p :=
        Finset.card_le_card (Finset.filter_subset_filter _ incl)
      exact (show (charge T a p:ℝ) ≤ charge S a p by exact_mod_cast mono).trans
        (hlarge a x p le_rfl top_le gt.le prime (zle.trans_lt gt))
    _ = (E.card:ℝ)*(35*(V/x)) := by simp
    _ ≤ ((x:ℝ)/L)*(35*(V/x)) := mul_le_mul_of_nonneg_right size (by positivity)
    _ = 35*(V/L) := by field_simp
    _ ≤ (c/4)*W := by
      have scale : 140 ≤ c*Real.log L := by
        change 140/c ≤ Real.log L at hll
        linarith [(div_le_iff₀ hc).1 hll]
      have aux := mul_le_mul_of_nonneg_right (show 35 ≤ c/4*Real.log L by linarith) (div_nonneg Vn Lp.le)
      calc
        _ ≤ (c/4*Real.log L)*(V/L) := aux
        _ = (c/4)*W := by change _ = (c/4)*(V*(Real.log L/L)); ring
  have f1 := finite_loss S P a
  change S.card ≤ (remaining (survivors z N a) (x.primesLE \ z.primesLE) a).card + _ at f1
  rw [band_remaining zle] at f1
  have b1 : (S.card:ℝ) ≤ T.card + ∑ p ∈ P, (charge S a p:ℝ) := by exact_mod_cast f1
  have b2 : (T.card:ℝ) ≤ (remaining T E a).card + ∑ p ∈ E, (charge T a p:ℝ) := by
    exact_mod_cast finite_loss T E a
  have start : c*W ≤ (S.card:ℝ) := hstock a
  change c/4*W ≤ ((remaining T E a).card:ℝ)
  linarith

theorem stockUnit_pos {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, 0 < stockUnit d x := by
  have tends := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [tends.eventually_ge_atTop 4,eventually_ge_atTop (1:ℕ)] with x hL hx
  let L := Real.log (x:ℝ)
  change 4 ≤ L at hL
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have lp : 0 < L := by linarith
  have llp : 0 < Real.log L := Real.log_pos (by linarith)
  have zp : 0 < top d x := div_pos xp (Real.rpow_pos_of_pos lp _)
  have logz : Real.log (top d x) = L-d*Real.log L := by
    rw [top,Real.log_div xp.ne' (Real.rpow_pos_of_pos lp d).ne',Real.log_rpow lp]
  have pos : 0 < Real.log (top d x) := by
    rw [logz]
    linarith [mul_le_mul_of_nonneg_right hh llp.le,Real.log_le_sub_one_of_pos lp]
  have hr : 1 ≤ (top d x)^2/(Real.log (top d x))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos pos)).2
    simpa using pow_le_pow_left₀ pos.le
      (show Real.log (top d x) ≤ top d x by linarith [Real.log_le_sub_one_of_pos zp]) 2
  have length_pos : 1 ≤ length d x := (Nat.le_floor_iff (by positivity)).2 (by simpa using hr)
  exact mul_pos (div_pos (by exact_mod_cast length_pos) lp) (div_pos llp lp)

/-- A set of at most x/log x primes of arbitrary size cannot cover this
    length. Extra small prime classes are supplied by the full sieve. -/
theorem arbitrary_primes (source : InterfaceSource687.statement) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/2 ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → (P.card:ℝ) ≤ (x:ℝ)/Real.log x →
      ∀ a : ℕ → ℕ, ∃ i ∈ Finset.Icc 1 (length d x), ∀ p ∈ P, i%p ≠ a p%p := by
  obtain ⟨d,hd,hh,c,hc,stock⟩ := robust_stock source
  refine ⟨d,hd,hh,?_⟩
  filter_upwards [stock,stockUnit_pos hd hh] with x bound pos
  intro P primes size a
  let E := P \ x.primesLE
  have big : ∀ p ∈ E, x < p ∧ p.Prime := by
    intro p hp
    obtain ⟨mem,out⟩ := Finset.mem_sdiff.mp hp
    exact ⟨lt_of_not_ge (fun h => out (Nat.mem_primesLE.mpr ⟨h,primes p mem⟩)),primes p mem⟩
  have small : (E.card:ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card (show E ⊆ P from Finset.sdiff_subset)
  have positive := (mul_pos hc pos).trans_le (bound a E big (small.trans size))
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (by exact_mod_cast positive)
  obtain ⟨inside,extra⟩ := Finset.mem_filter.mp hi
  obtain ⟨interval,old⟩ := Finset.mem_filter.mp inside
  refine ⟨i,interval,?_⟩
  intro p hp
  by_cases h : p ∈ x.primesLE
  · exact old p h
  · exact extra p (Finset.mem_sdiff.mpr ⟨hp,h⟩)

end SurvieTotale687
