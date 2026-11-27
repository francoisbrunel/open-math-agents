import StockSource687
import DemiBande687

/-! Transfer a uniform local survivor density to longer intervals. -/
namespace Blocs687
open Filter Transfert687 StockSource687
open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

private theorem split {z M N : ℕ} (a : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, (survivors z M a).card + (survivors z N b).card ≤
      (survivors z (M+N) a).card := by
  classical
  let b (p : ℕ) := a p + (p-1)*M
  let A := survivors z M a
  let B := (survivors z N b).image (fun n => n+M)
  have sep : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hB
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hB
    have lo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
    have hiM := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
    omega
  have incl : A ∪ B ⊆ survivors z (M+N) a := by
    intro i hi
    rcases Finset.mem_union.mp hi with hA | hB
    · obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hA
      obtain ⟨lo,hiM⟩ := Finset.mem_Icc.mp hI
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,by omega⟩,avoid⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hj
      obtain ⟨lo,hiN⟩ := Finset.mem_Icc.mp hI
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
      intro p hp hit
      have pos := (Nat.mem_primesLE.mp hp).2.pos
      have eqn : b p+M = a p+p*M := by
        dsimp [b]
        rw [Nat.add_assoc, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel pos]
      have shift : b p+M ≡ a p [MOD p] := by
        rw [eqn]
        simp [Nat.ModEq]
      exact avoid p hp (Nat.ModEq.add_right_cancel' M ((show j+M ≡ a p [MOD p] from hit).trans shift.symm))
  have cardB : B.card = (survivors z N b).card :=
    Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
  refine ⟨b,?_⟩
  simpa only [Finset.card_union_of_disjoint sep,cardB,A] using Finset.card_le_card incl

/-- Every full block contributes the same guaranteed number of survivors,
    even though the translated residues differ for each block. -/
theorem blocks {z J : ℕ} {u : ℝ} (h : ∀ a, u ≤ ((survivors z J a).card:ℝ))
    (N : ℕ) (a : ℕ → ℕ) :
    (N/J:ℕ)*u ≤ ((survivors z N a).card:ℝ) := by
  have many (k : ℕ) : ∀ b, (k:ℝ)*u ≤ ((survivors z (k*J) b).card:ℝ) := by
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      obtain ⟨e,he⟩ := split (M := k*J) (N := J) (z := z) b
      have bound := add_le_add (ih b) (h e)
      rw [Nat.succ_mul,Nat.cast_succ,add_mul,one_mul]
      exact bound.trans (by exact_mod_cast he)
  have incl : survivors z (N/J*J) a ⊆ survivors z N a := by
    intro n hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
    obtain ⟨lo,upper⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,upper.trans (Nat.div_mul_le_self N J)⟩,avoid⟩
  exact (many (N/J) a).trans (by exact_mod_cast Finset.card_le_card incl)

theorem H1_of_interface (published : InterfaceSource687.statement) : H1 := by
  obtain ⟨c,hc,stock⟩ := normalize_source (source_of_interface published)
  let z (x : ℕ) := x/2
  have tends : Tendsto (fun x => (z x:ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (2*k)] with x hx
    dsimp [z]; omega
  have logs := Real.tendsto_log_atTop.comp tends
  filter_upwards [tends.eventually stock,logs.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp logs).eventually_ge_atTop (4000/c),
    eventually_ge_atTop (4:ℕ)] with x hs hL hll hx
  intro a
  let L := Real.log (z x:ℝ)
  let J := height (z x)
  let d := x/(x.log2+1)
  change 2 ≤ L at hL
  change 4000/c ≤ Real.log L at hll
  have Lpos : 0 < L := by linarith
  have cstock : 4000 ≤ c*Real.log L := by linarith [(div_le_iff₀ hc).1 hll]
  have zx : z x ≤ x := Nat.div_le_self _ _
  have zp : (0:ℝ) < z x := by exact_mod_cast (by dsimp [z]; omega : 0 < z x)
  have Lle : L ≤ z x := by linarith [Real.log_le_sub_one_of_pos zp]
  have rad : 0 ≤ (z x:ℝ)^2/L^2 := by positivity
  have Jpos : 1 ≤ J := (Nat.le_floor_iff rad).2 (by
    rw [Nat.cast_one]
    apply (le_div_iff₀ (sq_pos_of_pos Lpos)).2
    nlinarith [sq_nonneg ((z x:ℝ)-L),mul_nonneg Lpos.le (sub_nonneg.mpr Lle)])
  have Jle : J ≤ x^2 := by
    have zxr : (z x:ℝ) ≤ x := by exact_mod_cast zx
    have jfloor : (J:ℝ) ≤ (z x:ℝ)^2/L^2 := Nat.floor_le rad
    exact_mod_cast (calc (J:ℝ) ≤ (z x:ℝ)^2/L^2 := jfloor
                        _ ≤ (z x:ℝ)^2 := div_le_self (sq_nonneg _) (by nlinarith)
                        _ ≤ (x:ℝ)^2 := by gcongr)
  let q := x^2/J
  have qpos : 1 ≤ q := (Nat.le_div_iff_mul_le Jpos).2 (by simpa using Jle)
  have half : x^2 ≤ 2*(q*J) := calc
    _ ≤ (q+1)*J := ((Nat.div_lt_iff_lt_mul Jpos).1 (Nat.lt_succ_self q)).le
    _ ≤ (2*q)*J := Nat.mul_le_mul_right J (by omega)
    _ = _ := by ring
  have bl := blocks (z := z x) (J := J) (u := c*((J:ℝ)*Real.log L/L^2))
    (by intro b; simpa only [Nat.floor_natCast] using hs b) (x^2) a
  change (q:ℝ)*(c*((J:ℝ)*Real.log L/L^2)) ≤ _ at bl
  have logtop : L ≤ (x.log2+1:ℕ) := by
    have top : (z x:ℝ) ≤ (2:ℝ)^(x.log2+1) := by
      exact_mod_cast zx.trans (Nat.lt_log2_self (n := x)).le
    have ht := Real.log_le_log zp top
    rw [Real.log_pow] at ht
    have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    exact ht.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) l2)
  have dL : (d:ℝ)*L ≤ x := calc
    _ ≤ (d:ℝ)*(x.log2+1:ℕ) := mul_le_mul_of_nonneg_left logtop (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast Nat.div_mul_le_self x (x.log2+1)
  have d2 : (d:ℝ)^2*L^2 ≤ (x:ℝ)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) dL 2
  have halfR : (x:ℝ)^2 ≤ 2*((q:ℝ)*(J:ℝ)) := by exact_mod_cast half
  have qs : 0 < (q:ℝ)*(J:ℝ) :=
    mul_pos (by exact_mod_cast qpos) (by exact_mod_cast Jpos)
  have strict : 1000*(d:ℝ)^2 < (q:ℝ)*(c*((J:ℝ)*Real.log L/L^2)) := by
    rw [show (q:ℝ)*(c*((J:ℝ)*Real.log L/L^2)) = ((q:ℝ)*(J:ℝ))*(c*Real.log L)/L^2 by ring]
    apply (lt_div_iff₀ (sq_pos_of_pos Lpos)).2
    nlinarith [mul_le_mul_of_nonneg_left cstock qs.le]
  exact_mod_cast strict.trans_le bl

end Blocs687
