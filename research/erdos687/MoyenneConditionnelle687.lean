import ConcentrationClasses687
import StabiliteCarree687

/-! Conditional survivor counts when only a designated set of rows is
randomized. Other rows may be prescribed adversarially. -/
namespace MoyenneConditionnelle687
open ConcentrationClasses687 Transfert687 Filter
open scoped BigOperators
noncomputable section

def keep (P : Finset ℕ) (n : ℕ) (a : Rows) : ℝ := by
  classical
  exact if ∀ q ∈ P, n%q ≠ a q%q then 1 else 0

def stock (P : Finset ℕ) (H : ℕ) (a : Rows) : ℝ :=
  ∑ n ∈ Finset.Icc 1 H, keep P n a

theorem same_stock (z H : ℕ) (a : Rows) :
    stock z.primesLE H a = ((survivors z H a).card:ℝ) := by
  classical
  simp only [stock,keep,survivors,← Finset.sum_filter,Finset.sum_const,
    nsmul_eq_mul,mul_one]

private theorem draw_one {p : ℕ} {P : Finset ℕ} (hp : 0 < p) (mem : p ∈ P)
    (n : ℕ) (a : Rows) :
    draw p (keep P n) a = (1-(p:ℝ)⁻¹)*keep (P.erase p) n a := by
  classical
  have equiv {r : ℕ} (hr : r < p) : (∀ q ∈ P, n%q ≠ (Function.update a p r q)%q) ↔
      (∀ q ∈ P.erase p, n%q ≠ a q%q) ∧ n%p ≠ r := by
    constructor
    · intro h
      refine ⟨?_,by simpa [Nat.mod_eq_of_lt hr] using h p mem⟩
      intro q hq
      obtain ⟨neq,m⟩ := Finset.mem_erase.mp hq
      simpa [Function.update_of_ne neq] using h q m
    · rintro ⟨h,other⟩ q hq
      by_cases eq : q=p
      · subst q; simpa [Nat.mod_eq_of_lt hr] using other
      · simpa [Function.update_of_ne eq] using h q (Finset.mem_erase.mpr ⟨eq,hq⟩)
  by_cases yes : ∀ q ∈ P.erase p, n%q ≠ a q%q
  · have val (r : ℕ) (hr : r ∈ Finset.range p) :
        keep P n (Function.update a p r) = 1-(if r=n%p then (1:ℝ) else 0) := by
      unfold keep
      by_cases e : r=n%p
      · rw [if_neg (fun h => ((equiv (Finset.mem_range.mp hr)).mp h).2 e.symm),if_pos e]
        ring
      · rw [if_pos ((equiv (Finset.mem_range.mp hr)).mpr ⟨yes,Ne.symm e⟩),if_neg e,sub_zero]
    have rhs : keep (P.erase p) n a = 1 := if_pos yes
    change (∑ r ∈ Finset.range p, keep P n (Function.update a p r))/(p:ℝ) = _
    rw [rhs,Finset.sum_congr rfl val,Finset.sum_sub_distrib]
    simp [Finset.mem_range.mpr (Nat.mod_lt n hp)]
    <;> field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne']
  · have val (r : ℕ) (hr : r ∈ Finset.range p) : keep P n (Function.update a p r) = 0 := by
      exact if_neg (fun h => yes (((equiv (Finset.mem_range.mp hr)).mp h).1))
    have rhs : keep (P.erase p) n a = 0 := if_neg yes
    change (∑ r ∈ Finset.range p, keep P n (Function.update a p r))/(p:ℝ) = _
    rw [rhs,Finset.sum_eq_zero val,zero_div,mul_zero]

theorem draw_stock {p : ℕ} {P : Finset ℕ} (hp : 0 < p) (mem : p ∈ P) (H : ℕ) :
    draw p (stock P H) = fun a => (1-(p:ℝ)⁻¹)*stock (P.erase p) H a := by
  funext a
  change (∑ r ∈ Finset.range p, ∑ n ∈ Finset.Icc 1 H, keep P n (Function.update a p r))/(p:ℝ) = _
  rw [Finset.sum_comm,Finset.sum_div,stock,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n _ => draw_one hp mem n a)

theorem expected (ps : List ℕ) (distinct : ps.Nodup) (P : Finset ℕ)
    (sub : ∀ p ∈ ps, p ∈ P) (pos : ∀ p ∈ ps, 0 < p) (H : ℕ) (a : Rows) :
    sample ps (stock P H) a =
      (ps.map (fun p : ℕ => 1-(p:ℝ)⁻¹)).prod*stock (P \ ps.toFinset) H a := by
  classical
  induction ps generalizing P with
  | nil => simp [sample]
  | cons p ps ih =>
    have no := List.nodup_cons.mp distinct
    have hp := pos p (by simp)
    have mem := sub p (by simp)
    have hp' (q : ℕ) (hq : q ∈ ps) := pos q (List.mem_cons_of_mem _ hq)
    have hs (q : ℕ) (hq : q ∈ ps) : q ∈ P.erase p :=
      Finset.mem_erase.mpr ⟨fun e => no.1 (e ▸ hq),sub q (List.mem_cons_of_mem _ hq)⟩
    have sets : P.erase p \ ps.toFinset = P \ (p::ps).toFinset := by
      ext q; simp; tauto
    have av := sample_affine ps hp' (stock (P.erase p) H) (1-(p:ℝ)⁻¹) 0 a
    simp only [add_zero] at av
    rw [sample,draw_stock hp mem,av,ih no.2 (P.erase p) hs hp',sets]
    simp [mul_assoc]

/-- Uniform coordinate oscillation, irrespective of which other rows
are random, fixed in advance, or set to deliberately exceptional values. -/
theorem row_osc {z : ℕ} (hz : 1024 ≤ z) (p : ℕ) :
    osc (stock z.primesLE (z^2)) p ((68*(z:ℝ)^2/Real.log z)*(1/(p:ℝ))) := by
  intro a b agree
  simp only [same_stock]
  have sub : StabiliteCarree687.changes z a b ⊆ {p} := by
    intro q hq
    by_contra missing
    have neq : q ≠ p := by simpa using missing
    exact (Finset.mem_filter.mp hq).2 (by rw [agree q neq])
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r : ℕ => 1/(r:ℝ))
    sub (fun _ _ _ => by positivity)
  simp only [Finset.sum_singleton] at h
  have l : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  apply (StabiliteCarree687.stability hz a b).trans
  gcongr

def canComplete (z x H : ℕ) (b : Rows) : Prop :=
  ∃ a : Rows, (∀ p ∈ z.primesLE, a p%p=b p%p) ∧
    ∀ n ∈ Finset.Icc 1 H, ∃ p ≤ x, p.Prime ∧ n%p=a p%p

def chance (ps : List ℕ) (z x H : ℕ) (a : Rows) : ℝ := by
  classical
  exact sample ps (fun b => if canComplete z x H b then 1 else 0) a

/-- A finite exponential bound against adaptive completion. The exact
conditional mean on the unresampled rows is the theorem expected. -/
theorem square_tail (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ k : ℕ in Filter.atTop, let z := k^m
      let f := stock z.primesLE (z^2)
      let c := fun p : ℕ => (68*(z:ℝ)^2/Real.log z)*(1/(p:ℝ))
      let B := (24/(m:ℝ))*(z:ℝ)^2/Real.log z
      ∀ (ps : List ℕ) (a : Rows) (δ : ℝ), (∀ p ∈ ps, 0 < p) → 0 < δ →
        0 < energy ps c → B+δ ≤ sample ps f a →
        chance ps z (k^(m+1)) (z^2) a ≤ Real.exp (-δ^2/(2*energy ps c)) := by
  classical
  filter_upwards [DensiteCarree687.thin_of_cover m hm,Filter.eventually_ge_atTop (1024:ℕ)]
    with k thin big
  let z := k^m
  let f := stock z.primesLE (z^2)
  let c := fun p : ℕ => (68*(z:ℝ)^2/Real.log z)*(1/(p:ℝ))
  let B := (24/(m:ℝ))*(z:ℝ)^2/Real.log z
  have kp : 0 < k := by omega
  have mp : 1 ≤ m := by omega
  have hz : 1024 ≤ z := big.trans (by simpa only [z,pow_one] using Nat.pow_le_pow_right kp mp)
  have L := Real.log_pos (show (1:ℝ) < z by exact_mod_cast (show 1 < z by omega))
  dsimp only
  intro ps a δ pos gap en meanBound
  apply lower_tail ps f c _ a (canComplete z (k^(m+1)) (z^2)) gap en
  · intro b hb
    obtain ⟨u,agree,full⟩ := hb
    have e : survivors z (z^2) b = survivors z (z^2) u := by
      ext n
      simp only [survivors,Finset.mem_filter]
      exact and_congr_right (fun _ => forall_congr' fun p => forall_congr' fun hp => by rw [agree p hp])
    have up : f b ≤ B := by
      dsimp only [f]
      rw [same_stock,e]
      exact thin u full
    change B+δ ≤ sample ps f a at meanBound
    linarith
  · intro p hp
    have pp : (0:ℝ) < p := by exact_mod_cast pos p hp
    exact ⟨pos p hp,by dsimp [c]; positivity, row_osc hz p⟩

end
end MoyenneConditionnelle687
#print axioms MoyenneConditionnelle687.expected
#print axioms MoyenneConditionnelle687.row_osc
#print axioms MoyenneConditionnelle687.square_tail
