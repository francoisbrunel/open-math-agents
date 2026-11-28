import StockFinNatif687
import GrillesBande687

/-! Rectangular obstructions are present for every pair of remaining
primes on square windows, even after discarding half the initial stock.
This uses the native published Jacobsthal survivor theorem. -/
namespace GrillesCarrees687
open Filter Transfert687 StockSource687

private theorem mass (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
      4*(k^m)^2 ≤ k*(survivors (k^m) ((k^m)^2) a).card := by
  obtain ⟨c,_,cp,stock⟩ := StockFin687.sharp_normalize (StockFin687.sharp_bridge SourcePubliee687.sharp_bound)
  have inc : Tendsto (fun k : ℕ => ((k^m:ℕ):ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b,eventually_ge_atTop (1:ℕ)] with k bk hk
    exact bk.trans (by simpa using Nat.pow_le_pow_right hk hm)
  let C : ℝ := 8*(m:ℝ)^4/c
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have Cpos : 0<C := by dsimp [C]; positivity
  have little := ((Real.isLittleO_pow_log_id_atTop (n := 4)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)).bound (one_div_pos.mpr Cpos)
  have both := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp inc)).eventually_ge_atTop 1
  filter_upwards [inc.eventually stock,both,(Real.tendsto_log_atTop.comp inc).eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ),little] with k lower ll lg hk sm
  intro a
  let z := k^m
  let L := Real.log z
  let N := height z
  change 1 ≤ Real.log L at ll
  change 2 ≤ L at lg
  have zp : 0 < (z:ℝ) := by dsimp [z]; positivity
  have lp : 0<L := by linarith
  have lz : L ≤ z := by dsimp [L]; linarith [Real.log_le_sub_one_of_pos zp]
  have npos : 1 ≤ N := (Nat.le_floor_iff (by positivity)).2 (by
    rw [Nat.cast_one,le_div_iff₀ (by positivity),one_mul]
    exact pow_le_pow_left₀ lp.le lz _)
  have nr : 1 ≤ (N:ℝ) := by exact_mod_cast npos
  have nz : N ≤ z^2 := by
    apply Nat.floor_le_of_le
    push_cast
    exact div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith : 1 ≤ L))
  have flo := Nat.lt_floor_add_one ((z:ℝ)^2/L^2)
  change (z:ℝ)^2/L^2 < (N:ℝ)+1 at flo
  have zr : (z:ℝ)^2 ≤ 2*(N:ℝ)*L^2 := (div_le_iff₀ (by positivity)).mp (by linarith)
  have source := lower a
  rw [Nat.floor_natCast] at source
  change c*((N:ℝ)*Real.log L/L^2) ≤ ((survivors z N a).card:ℝ) at source
  have sub : survivors z N a ⊆ survivors z (z^2) a := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,up.trans nz⟩,avoid⟩
  let s : ℝ := (survivors z (z^2) a).card
  have src : c*((N:ℝ)*Real.log L) ≤ s*L^2 := (div_le_iff₀ (by positivity)).mp (by
    rw [mul_div_assoc]
    exact source.trans (by dsimp only [s]; exact_mod_cast Finset.card_le_card sub))
  have floorstock : c*(z:ℝ)^2 ≤ 2*L^4*s := by
    have llN := mul_le_mul_of_nonneg_left ll (show 0≤c*(N:ℝ) by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left zr cp.le,
      mul_le_mul_of_nonneg_right src (sq_nonneg L),mul_le_mul_of_nonneg_right llN (sq_nonneg L)]
  change ‖(Real.log k)^4‖ ≤ (1/C)*‖(k:ℝ)‖ at sm
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg k)] at sm
  have t := mul_le_mul_of_nonneg_left sm Cpos.le
  rw [← mul_assoc,mul_one_div,div_self Cpos.ne',one_mul] at t
  have logz : L=(m:ℝ)*Real.log k := by simp [L,z,Real.log_pow]
  have t' : 8*L^4 ≤ c*k := by
    change (8*(m:ℝ)^4/c)*(Real.log k)^4 ≤ k at t
    rw [div_mul_eq_mul_div,div_le_iff₀ cp] at t
    rw [logz]; nlinarith only [t]
  have last : c*(4*(z:ℝ)^2) ≤ c*((k:ℝ)*s) := by
    have sn : 0 ≤ s := Nat.cast_nonneg _
    nlinarith only [floorstock,mul_le_mul_of_nonneg_right t' sn]
  have out := (mul_le_mul_iff_right₀ cp).mp last
  dsimp only [s] at out
  exact_mod_cast out

theorem half_stock_rectangles (m : ℕ) (hm : 5 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ, ∀ T ⊆ survivors (k^m) ((k^m)^2) a,
    (survivors (k^m) ((k^m)^2) a).card ≤ 2*T.card →
    ∀ p q : ℕ, p.Prime → q.Prime → p≠q → k^m < p → k^m < q →
      p ≤ k^(m+1) → q ≤ k^(m+1) →
      ∃ u v c d : ℕ, u≠v ∧ c≠d ∧ ∀ r ∈ ({u,v}:Finset ℕ), ∀ t ∈ ({c,d}:Finset ℕ),
        ∃ n ∈ T, n%p=r ∧ n%q=t := by
  filter_upwards [mass m (by omega),eventually_ge_atTop (2:ℕ)] with k enough hk
  intro a T sub half p q pr qr ne zp zq px qx
  let z := k^m
  let x := k^(m+1)
  have kp : 0 < k := by omega
  have zpos : 0 < z := pow_pos kp _
  have xpos : 0 < x := pow_pos kp _
  have zx : z ≤ x := Nat.pow_le_pow_right kp (by omega)
  have hs := (enough a).trans (Nat.mul_le_mul_left k half)
  have h2 : 2*z^2 ≤ k*T.card := by
    change 4*z^2 ≤ k*(2*T.card) at hs; nlinarith only [hs]
  have powcomp : k^2*x^3 ≤ z^4 := calc
    _ = k^(2+(m+1)*3) := by simp only [x,pow_mul,pow_add]
    _ ≤ k^(m*4) := Nat.pow_le_pow_right kp (by omega)
    _ = _ := pow_mul _ _ _
  have gt : 4*x^3 ≤ T.card^2 := by
    have h : k^2*(4*x^3) ≤ k^2*T.card^2 := by
      nlinarith only [Nat.pow_le_pow_left h2 2,powcomp]
    exact Nat.le_of_mul_le_mul_left h (pow_pos kp 2)
  have subs : T ⊆ Finset.Icc 1 (z^2) := sub.trans (Finset.filter_subset _ _)
  have size : T.card ≤ z^2 := by simpa using Finset.card_le_card subs
  have budget : q*(p^2+T.card) ≤ 2*x^3 := calc
    _ ≤ x*(x^2+x^2) := Nat.mul_le_mul qx (Nat.add_le_add
      (Nat.pow_le_pow_left px 2) (size.trans (Nat.pow_le_pow_left zx 2)))
    _ = _ := by ring
  have short : z^2 < p*q := by simpa only [pow_two] using Nat.mul_lt_mul_of_lt_of_lt zp zq
  apply GrillesBande687.rectangle T pr.pos qr.pos
    (GrillesBande687.short_injective ((Nat.coprime_primes pr qr).mpr ne) short T
      (fun i hi => (Finset.mem_Icc.mp (subs hi)).2))
  exact budget.trans_lt ((show 2*x^3 < 4*x^3 by nlinarith only [pow_pos xpos 3]).trans_le gt)

end GrillesCarrees687
#print axioms GrillesCarrees687.half_stock_rectangles
