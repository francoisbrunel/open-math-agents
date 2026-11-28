import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-! A finite bounded-differences estimate for independently resampling
prime rows while any other rows are held fixed. The moment generating
function argument uses the convex chord bound and cosh(u) ≤ exp(u²/2). -/
namespace ConcentrationClasses687
noncomputable section
open scoped BigOperators
abbrev Rows := ℕ → ℕ

def mean (p : ℕ) (f : ℕ → ℝ) : ℝ := (∑ r ∈ Finset.range p,f r)/(p:ℝ)

private theorem mean_const {p : ℕ} (hp : 0 < p) (c : ℝ) :
    mean p (fun _ => c) = c := by
  simp only [mean,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne']

private theorem mean_mono {p : ℕ} {f g : ℕ → ℝ} (h : ∀ r < p, f r ≤ g r) :
    mean p f ≤ mean p g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun r hr => h r (Finset.mem_range.mp hr)) (Nat.cast_nonneg _)

private theorem mean_affine {p : ℕ} (hp : 0 < p) (f : ℕ → ℝ) (u v : ℝ) :
    mean p (fun r => u*f r+v) = u*mean p f+v := by
  simp only [mean,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul]
  field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne']
  <;> ring

def osc (f : Rows → ℝ) (p : ℕ) (c : ℝ) : Prop :=
  ∀ a b : Rows, (∀ q, q ≠ p → a q=b q) → f a ≤ f b+c

def draw (p : ℕ) (f : Rows → ℝ) (a : Rows) :=
  mean p (fun r => f (Function.update a p r))

noncomputable def sample : List ℕ → (Rows → ℝ) → Rows → ℝ
  | [],f => f
  | p::ps,f => sample ps (draw p f)

theorem sample_mono (ps : List ℕ) {f g : Rows → ℝ} (h : ∀ a, f a ≤ g a) :
    ∀ a, sample ps f a ≤ sample ps g a := by
  induction ps generalizing f g with
  | nil => exact h
  | cons p ps ih => exact ih (fun a => mean_mono (fun r _ => h (Function.update a p r)))

theorem sample_affine (ps : List ℕ) (pos : ∀ p ∈ ps, 0 < p)
    (f : Rows → ℝ) (u v : ℝ) (a : Rows) :
    sample ps (fun b => u*f b+v) a = u*sample ps f a+v := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    have eqn : draw p (fun b => u*f b+v) = fun b => u*draw p f b+v :=
      funext fun b => mean_affine (pos p (by simp)) _ u v
    simp only [sample,eqn]
    exact ih (fun q h => pos q (by simp [h])) _

theorem sample_const (ps : List ℕ) (pos : ∀ p ∈ ps, 0 < p) (v : ℝ) (a : Rows) :
    sample ps (fun _ => v) a = v := by
  simpa only [zero_mul,zero_add] using sample_affine ps pos (fun _ => 0) 0 v a

private theorem draw_osc {p q : ℕ} (hp : 0 < p) {f : Rows → ℝ} {c : ℝ}
    (h : osc f q c) : osc (draw p f) q c := by
  intro a b agree
  have t (r : ℕ) : f (Function.update a p r) ≤ f (Function.update b p r)+c := by
    apply h
    intro j neq
    by_cases jp : j=p
    · simp [jp]
    · simpa [Function.update_of_ne jp] using agree j neq
  calc
    draw p f a ≤ mean p (fun r => 1*f (Function.update b p r)+c) :=
      mean_mono (fun r _ => by simpa using t r)
    _ = _ := by rw [mean_affine hp]; simp [draw]

private theorem chord {t c u : ℝ} (cp : 0 < c) (lo : -c ≤ u) (hi : u ≤ c) :
    Real.exp (t*u) ≤ ((Real.exp (t*c)-Real.exp (-(t*c)))/(2*c))*u + Real.cosh (t*c) := by
  let a := (c+u)/(2*c)
  let b := (c-u)/(2*c)
  have ap : 0 ≤ a := div_nonneg (by linarith) (by positivity)
  have bp : 0 ≤ b := div_nonneg (by linarith) (by positivity)
  have ab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have h := convexOn_exp.2 (Set.mem_univ (t*c)) (Set.mem_univ (-(t*c))) ap bp ab
  simp only [smul_eq_mul] at h
  have eqn : a*(t*c)+b*(-(t*c))=t*u := by dsimp [a,b]; field_simp; ring
  rw [eqn] at h
  calc
    _ ≤ _ := h
    _ = _ := by dsimp [a,b]; rw [Real.cosh_eq]; field_simp; ring

private theorem row_mgf {p : ℕ} (hp : 0 < p) {f : Rows → ℝ} {c : ℝ} (cp : 0 < c)
    (h : osc f p c) (a : Rows) (t : ℝ) :
    draw p (fun b => Real.exp (t*f b)) a ≤
      Real.exp ((t*c)^2/2)*Real.exp (t*draw p f a) := by
  let X := fun r => f (Function.update a p r)
  let μ := mean p X
  have pair (r s : ℕ) : X r ≤ X s+c := h _ _ (fun q nq => by simp [Function.update_of_ne nq])
  have high (r : ℕ) : X r ≤ μ+c := calc
    _ = mean p (fun _ => X r) := (mean_const hp _).symm
    _ ≤ mean p (fun s => 1*X s+c) := mean_mono (fun s _ => by simpa using pair r s)
    _ = _ := by rw [mean_affine hp]; simp [μ]
  have low (r : ℕ) : μ ≤ X r+c := by
    calc
      _ ≤ mean p (fun _ => X r+c) := mean_mono (fun s _ => pair s r)
      _ = _ := mean_const hp _
  let slope := (Real.exp (t*c)-Real.exp (-(t*c)))/(2*c)
  have bound : mean p (fun r => Real.exp (t*(X r-μ))) ≤ Real.cosh (t*c) := calc
    _ ≤ mean p (fun r => slope*(X r-μ)+Real.cosh (t*c)) :=
      mean_mono (fun r _ => chord cp (by linarith [low r]) (by linarith [high r]))
    _ = mean p (fun r => slope*X r+(Real.cosh (t*c)-slope*μ)) := by
      congr 1; funext r; ring
    _ = _ := by rw [mean_affine hp]; dsimp [μ]; ring
  have eqn (r : ℕ) : Real.exp (t*X r) = Real.exp (t*μ)*Real.exp (t*(X r-μ))+0 := by
    rw [← Real.exp_add,add_zero]; congr 1; ring
  change mean p (fun r => Real.exp (t*X r)) ≤ Real.exp _*Real.exp (t*μ)
  simp_rw [eqn,mean_affine hp,add_zero]
  rw [mul_comm (Real.exp ((t*c)^2/2))]
  exact mul_le_mul_of_nonneg_left (bound.trans (Real.cosh_le_exp_half_sq _)) (Real.exp_nonneg _)

def energy (ps : List ℕ) (c : ℕ → ℝ) : ℝ := (ps.map (fun p => (c p)^2)).sum

theorem mgf (ps : List ℕ) (f : Rows → ℝ) (c : ℕ → ℝ)
    (bounds : ∀ p ∈ ps, 0 < p ∧ 0 < c p ∧ osc f p (c p)) (a : Rows) (t : ℝ) :
    sample ps (fun b => Real.exp (t*f b)) a ≤
      Real.exp (t^2*energy ps c/2)*Real.exp (t*sample ps f a) := by
  induction ps generalizing f with
  | nil => simp [sample,energy]
  | cons p ps ih =>
    obtain ⟨hp,cp,h⟩ := bounds p (by simp)
    have tail (q : ℕ) (hq : q ∈ ps) := bounds q (List.mem_cons_of_mem _ hq)
    have applied := ih (draw p f) (fun q hq => ⟨(tail q hq).1,(tail q hq).2.1,
      draw_osc hp (tail q hq).2.2⟩)
    let K := Real.exp ((t*c p)^2/2)
    calc
      _ ≤ sample ps (fun b => K*Real.exp (t*draw p f b)+0) a :=
        sample_mono ps (fun b => by simpa [K] using row_mgf hp cp h b t) a
      _ = K*sample ps (fun b => Real.exp (t*draw p f b)) a :=
        (sample_affine ps (fun q hq => (tail q hq).1) _ K 0 a).trans (add_zero _)
      _ ≤ K*(Real.exp (t^2*energy ps c/2)*Real.exp (t*sample ps (draw p f) a)) :=
        mul_le_mul_of_nonneg_left applied (Real.exp_nonneg _)
      _ = _ := by
        change Real.exp _*(Real.exp _*_) = Real.exp _*_
        rw [← mul_assoc,← Real.exp_add]
        congr 2
        simp [energy]; ring

theorem lower_tail (ps : List ℕ) (f : Rows → ℝ) (c : ℕ → ℝ)
    (bounds : ∀ p ∈ ps, 0 < p ∧ 0 < c p ∧ osc f p (c p)) (a : Rows)
    (E : Rows → Prop) [DecidablePred E] {δ : ℝ} (gap : 0 < δ) (ep : 0 < energy ps c)
    (necessary : ∀ b, E b → f b ≤ sample ps f a-δ) :
    sample ps (fun b => if E b then 1 else 0) a ≤ Real.exp (-δ^2/(2*energy ps c)) := by
  let μ := sample ps f a
  let t := δ/energy ps c
  let K := Real.exp (t*(μ-δ))
  have tp : 0<t := div_pos gap ep
  have each (b : Rows) :
      (if E b then (1:ℝ) else 0) ≤ K*Real.exp ((-t)*f b)+0 := by
    by_cases yes : E b
    · simp only [yes,if_true,K,← Real.exp_add,add_zero]
      apply Real.one_le_exp_iff.mpr
      nlinarith only [mul_le_mul_of_nonneg_left (necessary b yes) tp.le]
    · simp only [yes,if_false,add_zero]
      exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ sample ps (fun b => K*Real.exp ((-t)*f b)+0) a := sample_mono ps each a
    _ = K*sample ps (fun b => Real.exp ((-t)*f b)) a :=
      (sample_affine ps (fun p hp => (bounds p hp).1) _ K 0 a).trans (add_zero _)
    _ ≤ K*(Real.exp ((-t)^2*energy ps c/2)*Real.exp ((-t)*μ)) :=
      mul_le_mul_of_nonneg_left (mgf ps f c bounds a (-t)) (Real.exp_nonneg _)
    _ = _ := by
      dsimp only [K,t]
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      field_simp [ep.ne']
      ring

end
end ConcentrationClasses687
#print axioms ConcentrationClasses687.mgf
#print axioms ConcentrationClasses687.lower_tail
