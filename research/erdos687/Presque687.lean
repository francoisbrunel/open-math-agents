import BorneRankin687

/-! Minimum number of exceptions in the almost-cover variant mentioned
    by Erdős. The complete-cover problem asks where this number is zero. -/
namespace Presque687
open Filter LongGapsBetweenPrimes
open scoped Asymptotics

noncomputable def holes (x H : ℕ) : ℕ :=
  sInf (Set.range fun a : ℕ → ℕ => (Transfert687.survivors x H a).card)

theorem realizes (x H : ℕ) : ∃ a, (Transfert687.survivors x H a).card = holes x H :=
  Nat.sInf_mem (Set.range_nonempty _)

theorem holes_le (x H : ℕ) (a : ℕ → ℕ) : holes x H ≤ (Transfert687.survivors x H a).card :=
  Nat.sInf_le (Set.mem_range_self a)

theorem holes_zero_iff {x H : ℕ} : holes x H = 0 ↔ H ≤ Erdos687.Y x := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := realizes x H
    apply Transfert687.le_Y_of_covered (Bords687.finish_singletons le_rfl a ?_)
    simp [ha,h]
  · intro le
    obtain ⟨a,ha⟩ := Extension687.optimal_cover x
    have empty : Transfert687.survivors x H a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
      obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
      obtain ⟨p,hp,pr,hit⟩ := ha n (Finset.mem_Icc.mpr ⟨lo,up.trans le⟩)
      exact avoid p (Nat.mem_primesLE.mpr ⟨hp,pr⟩) hit
    simpa [empty] using holes_le x H a

/-- The bound holds uniformly in B, with an explicit loss from the
    interval of reserved primes. -/
theorem uniform_band : ∀ᶠ x : ℕ in atTop, ∀ B : ℕ, 2 ≤ B → B ≤ coverZ x →
    (holes x (B*x):ℝ) ≤ (10*Real.exp 6)*((B*x:ℝ)/Real.log (B*x:ℝ))*
      ((1+Real.log B)/Real.log (coverZ x)) := by
  have inf : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [inf.eventually eventually_smooth_count,inf.eventually eventually_cover_parameters]
    with x hs hp
  intro B hB hBZ
  let Z := coverZ (x:ℝ)
  let H := B*x
  let S := H.smoothNumbersUpTo (Z+1)
  let Q := auxiliaryPrimes B Z
  have xreal : (2:ℝ) ≤ x := hp.1
  have x2 : 2 ≤ x := by exact_mod_cast xreal
  have lX : 2 ≤ Real.log (x:ℝ) := hp.2.1
  obtain ⟨_,_,_,_,_,_,_,_,hhigh⟩ := hp
  have Zx : Z ≤ x := by simpa [Z] using coverZ_le_floor (by linarith : (0:ℝ)<x) hhigh
  have bx := hBZ.trans Zx
  have Hx : x ≤ H := by dsimp [H]; nlinarith
  have lH := Real.log_pos (show (1:ℝ) < H by exact_mod_cast (show 1 < H by omega))
  have ll : Real.log H ≤ 2*Real.log x := by
    have e : (H:ℝ) = (B:ℝ)*x := by simp [H]
    rw [e,Real.log_mul (by positivity) (by positivity)]
    linarith [Real.log_le_log (show (0:ℝ) < B by positivity) (show (B:ℝ) ≤ x by exact_mod_cast bx)]
  have smooth : (S.card:ℝ) ≤ (H:ℝ)/Real.log x ^ 3 := by
    apply hs H (by exact_mod_cast Hx) S
    · intro n h
      obtain ⟨hi,mem⟩ := Nat.mem_smoothNumbersUpTo.mp h
      have nz := Nat.ne_zero_of_mem_smoothNumbers mem
      exact Finset.mem_Icc.mpr ⟨by omega,hi⟩
    · intro n h p pr dv
      exact Nat.lt_succ_iff.mp (Nat.mem_smoothNumbers'.mp (Nat.mem_smoothNumbersUpTo.mp h).2 p pr dv)
  have cost : ((S ∪ H.primesLE).card:ℝ) ≤ 10*((H:ℝ)/Real.log H) := by
    have rough := Comptage687.prime_count_eight (x := H) (by omega)
    have sm : (S.card:ℝ) ≤ (H:ℝ)/Real.log H := by
      apply smooth.trans (div_le_div_of_nonneg_left (by positivity) lH ?_)
      nlinarith [mul_nonneg (show 0 ≤ Real.log (x:ℝ)-2 by linarith)
        (sq_nonneg (Real.log (x:ℝ))),sq_nonneg (Real.log (x:ℝ)-1)]
    have union : ((S ∪ H.primesLE).card:ℝ) ≤ (S.card:ℝ)+Nat.primeCounting H := by
      exact_mod_cast (Finset.card_union_le S H.primesLE).trans_eq (by rw [Nat.primesLE_card_eq_primeCounting])
    calc
      _ ≤ _ := union
      _ ≤ (H:ℝ)/Real.log H + 8*H/Real.log H := add_le_add sm rough
      _ ≤ _ := by have nn : 0 ≤ (H:ℝ)/Real.log H := by positivity
                  nlinarith [show 8*(H:ℝ)/Real.log H = 8*(H/Real.log H) by ring]
  obtain ⟨a,ha⟩ := Croissance687.thin Q (S ∪ H.primesLE)
    (fun p h => (mem_auxiliaryPrimes.mp h).1.pos)
  let b := fun p => if p ∈ Q then a p else 0
  have subset := Croissance687.candidates (y := Z+1) bx Q (fun p h => by
    obtain ⟨prime,lo,hi⟩ := mem_auxiliaryPrimes.mp h
    exact ⟨prime,lo,by omega,hi.trans Zx⟩) a
  have lower := (holes_le x H b).trans (Finset.card_le_card subset)
  have density := greedy_product_le hB hBZ
  change Croissance687.density Q ≤ _ at density
  have dn : 0 ≤ Croissance687.density Q := by
    apply Finset.prod_nonneg
    intro p h
    have pr := (mem_auxiliaryPrimes.mp h).1
    have pp : (1:ℝ) ≤ p := by exact_mod_cast pr.one_le
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr pp)
  have final := (show (holes x H:ℝ) ≤ _ by exact_mod_cast lower).trans
    (ha.trans (mul_le_mul cost density dn (by positivity)))
  refine final.trans_eq ?_
  dsimp [H]
  push_cast
  ring

noncomputable def multiplier (x : ℕ) : ℕ :=
  ⌊Real.exp (Real.log x/Real.log (Real.log x))⌋₊

noncomputable def length (x : ℕ) : ℕ := multiplier x*x

/-- The chosen multiplier grows like x^(1/log log x). The fraction of
    exceptions relative to H/log H tends to zero. -/
theorem sparse :
    (fun x : ℕ => (holes x (length x):ℝ)) =o[atTop]
      (fun x : ℕ => (length x:ℝ)/Real.log (length x)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  let C := smoothScaleConstant
  let D : ℝ := 10*Real.exp 6
  have hc : 0 < C := smoothScaleConstant_pos
  have hd : 0 < D := by dsimp [D]; positivity
  have inf : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have log1 := Real.tendsto_log_atTop.comp inf
  have log2 := Real.tendsto_log_atTop.comp log1
  have log3 := Real.tendsto_log_atTop.comp log2
  filter_upwards [uniform_band,inf.eventually eventually_cover_parameters,
    log3.eventually_ge_atTop (max (2*C) (4*D*C/ε)),log2.eventually_ge_atTop 4]
    with x band hp h3 h2
  let L := Real.log (x:ℝ)
  let M := Real.log L
  let E := Real.log M
  let v := L/M
  change 4 ≤ M at h2
  change max (2*C) (4*D*C/ε) ≤ E at h3
  have hL : 2 ≤ L := hp.2.1
  have posM : 0 < M := by linarith
  have posv : 0 < v := div_pos (by linarith) posM
  have v1 : 1 ≤ v := (one_le_div posM).mpr
    (by dsimp [M]; linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < L)])
  have vb : 2 ≤ multiplier x := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    (by change (2:ℝ) ≤ Real.exp v; linarith [Real.add_one_le_exp v])
  have numerator : 1+Real.log (multiplier x) ≤ 2*v := by
    have hl := Real.log_le_log (by positivity : (0:ℝ) < multiplier x)
      (Nat.floor_le (Real.exp_nonneg v))
    rw [Real.log_exp] at hl
    linarith
  have identity : coverLogZ x = v*E/C := by unfold coverLogZ; dsimp [v,E,M,L,C]; ring
  have eq : C*coverLogZ x = v*E := by rw [identity]; field_simp
  have long : 2*v ≤ coverLogZ x := by
    rw [identity]
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left ((le_max_left _ _).trans h3) posv.le]
  have bz : multiplier x ≤ coverZ x := Nat.floor_mono (Real.exp_le_exp.mpr (by linarith : v ≤ coverLogZ x))
  have logcut : coverLogZ x/2 ≤ Real.log (coverZ x) := by
    have big : 2 ≤ Real.exp (coverLogZ x/2) := by linarith [Real.add_one_le_exp (coverLogZ x/2)]
    have sq : Real.exp (coverLogZ x) = Real.exp (coverLogZ x/2)^2 := by
      rw [pow_two,← Real.exp_add,add_halves]
    have fl : Real.exp (coverLogZ x) < (coverZ x:ℝ)+1 := Nat.lt_floor_add_one _
    calc
      _ = Real.log (Real.exp (coverLogZ x/2)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by nlinarith)
  have logpos : 0 < Real.log (coverZ x) := by linarith
  have ratio : D*((1+Real.log (multiplier x))/Real.log (coverZ x)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ logpos).mpr
    have epsE := (div_le_iff₀ he).mp ((le_max_right _ _).trans h3)
    have scaled := mul_le_mul_of_nonneg_left epsE posv.le
    have raw : 4*D*v ≤ ε*coverLogZ x := by
      apply (le_of_mul_le_mul_right · hc)
      nlinarith only [scaled,congrArg (fun u : ℝ => ε*u) eq]
    nlinarith [mul_le_mul_of_nonneg_left numerator hd.le,
      mul_le_mul_of_nonneg_left logcut he.le]
  have large : 2 ≤ length x := by
    have xx : 2 ≤ x := by exact_mod_cast hp.1
    dsimp [length]; nlinarith
  have unitpos : 0 ≤ (length x:ℝ)/Real.log (length x) :=
    div_nonneg (by positivity) (Real.log_pos (by exact_mod_cast (show 1 < length x by omega))).le
  have h := band (multiplier x) vb bz
  have cast : (length x:ℝ) = (multiplier x:ℝ)*x := by simp [length]
  rw [← cast] at h
  simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),abs_of_nonneg unitpos]
  exact h.trans (by
    calc _ = (D*((1+Real.log (multiplier x))/Real.log (coverZ x)))*((length x:ℝ)/Real.log (length x)) := by dsimp [D]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right ratio unitpos)

/-- Every fixed power of log x is eventually smaller than the multiplier. -/
theorem large_multiplier (k : ℕ) : ∀ᶠ x : ℕ in atTop,
    (Real.log (x:ℝ))^k ≤ (multiplier x:ℝ) := by
  have inf : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have log1 := Real.tendsto_log_atTop.comp inf
  have log2 := Real.tendsto_log_atTop.comp log1
  have small := (isLittleO_rpow_exp_atTop 2).bound
    (show 0 < ((k:ℝ)+2)⁻¹ by positivity)
  filter_upwards [log2.eventually small,log2.eventually_ge_atTop 2,log1.eventually_ge_atTop 2]
    with x h hm hl
  let L := Real.log (x:ℝ)
  let M := Real.log L
  change 2 ≤ L at hl
  change 2 ≤ M at hm
  have e : Real.exp M = L := Real.exp_log (by linarith)
  have power : M^2 ≤ ((k:ℝ)+2)⁻¹*L := by
    change ‖M^(2:ℝ)‖ ≤ ((k:ℝ)+2)⁻¹*‖Real.exp M‖ at h
    simpa only [Real.rpow_two,e,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg M),
      abs_of_nonneg (by linarith : 0 ≤ L)] using h
  have bound : ((k:ℝ)+2)*M^2 ≤ L := by
    have h' := mul_le_mul_of_nonneg_left power (show 0 ≤ (k:ℝ)+2 by positivity)
    calc _ ≤ _ := h'
         _ = _ := by field_simp
  have exponent : ((k:ℝ)+1)*M ≤ L/M := (le_div_iff₀ (by linarith)).mpr (by nlinarith)
  have expo := Real.exp_le_exp.mpr exponent
  have lhs : Real.exp (((k:ℝ)+1)*M) = L^k*L := by
    rw [add_mul,one_mul,Real.exp_add,Real.exp_nat_mul,e]
  rw [lhs] at expo
  have fl := Nat.lt_floor_add_one (Real.exp (L/M))
  change _ < (multiplier x:ℝ)+1 at fl
  change L^k ≤ _
  nlinarith [one_le_pow₀ (by linarith : 1 ≤ L) (n := k),
    mul_nonneg (show 0 ≤ L-2 by linarith) (show 0 ≤ L^k by positivity)]

theorem polylog_negligible (k : ℕ) :
    (fun x : ℕ => (x:ℝ)*Real.log x^k) =o[atTop] (fun x : ℕ => (length x:ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  have inf := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [large_multiplier (k+1),inf.eventually_ge_atTop (max 1 (1/ε))] with x hm hl
  change max 1 (1/ε) ≤ Real.log (x:ℝ) at hl
  have lpos : 0 ≤ Real.log (x:ℝ) := by linarith [le_max_left 1 (1/ε)]
  have εL := (div_le_iff₀ he).mp ((le_max_right _ _).trans hl)
  have step : (x:ℝ)*Real.log x^k ≤ ε*((x:ℝ)*Real.log x^(k+1)) := by
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left εL (show 0 ≤ (x:ℝ)*Real.log x^k by positivity)]
  have out := step.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) x)) he.le)
  simpa [length,Real.norm_eq_abs,abs_of_nonneg lpos,mul_comm] using out

/-- Under any polylogarithmic upper bound for complete covers, the
    almost-covered interval above is asymptotically longer. -/
theorem conditional_separation {k : ℕ}
    (upper : (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)*Real.log x^k)) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =o[atTop] (fun x : ℕ => (length x:ℝ)) :=
  upper.trans_isLittleO (polylog_negligible k)

end Presque687
