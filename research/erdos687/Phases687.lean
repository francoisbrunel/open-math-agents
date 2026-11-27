import NoyauPondere687
import FormalConjectures.ErdosProblems.«687»

/-! Translating and reflecting a finite core obstruction verifies an upper
    bound for the covering maximum in the catalog. -/

namespace Phases687
open NoyauPondere687

def Covers (H : ℕ) (primes : List ℕ) (a : ℕ → ℕ) :=
  ∀ n, 1 ≤ n → n ≤ H → ∃ p ∈ primes, n ≡ a p [MOD p]

def Normal (t : ℕ) (primes : List ℕ) (a : ℕ → ℕ) :=
  ∀ p ∈ primes, p≤17 → t+a p ≡ 0 [MOD p]

theorem phase_add (L : ℕ) {p : ℕ} (pp : 0<p) : phase L p + L ≡ 0 [MOD p] := by
  calc
    _ ≡ (p-L%p)+(L%p) [MOD p] := (Nat.mod_modEq _ _).add (Nat.mod_modEq _ _).symm
    _ = p := Nat.sub_add_cancel (Nat.mod_lt _ pp).le
    _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl

theorem core_excludes {H T L N : ℕ} {ps : List ℕ} {a : ℕ → ℕ}
    (positive : ∀ p ∈ ps, 0<p) (lo : T<L) (hi : L+N≤T+H+1)
    (obs : Obstruction L N ps) (norm : Normal T ps a) : ¬Covers H ps a := by
  intro all
  let d := L-T
  have eqn : T+d=L := by dsimp [d]; omega
  let r (p : ℕ) := a p+phase d p
  apply obs r
  · intro p hp old
    have pp := positive p hp
    have hz : r p+L ≡ 0 [MOD p] := calc
      _ = (T+a p)+(phase d p+d) := by rw [← eqn]; dsimp [r]; omega
      _ ≡ 0+0 [MOD p] := (norm p hp old).add (phase_add d pp)
      _ = 0 := rfl
    have eq := Nat.ModEq.add_right_cancel' L (hz.trans (phase_add L pp).symm)
    simpa [phase] using (show r p%p=(phase L p)%p from eq)
  · intro i iN
    obtain ⟨p,hp,hit⟩ := all (d+i) (by dsimp [d]; omega) (by omega)
    refine ⟨p,hp,?_⟩
    change i ≡ r p [MOD p]
    have hz := (phase_add d (positive p hp)).add_right i
    have key := hit.add_left (phase d p)
    simpa [r,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (show i ≡ phase d p+(d+i) [MOD p] from by
        simpa [Nat.add_assoc] using hz.symm).trans key

theorem reflect {H t u P : ℕ} {ps : List ℕ} {a : ℕ → ℕ}
    (positive : ∀ p ∈ ps, 0<p)
    (old_dvd : ∀ p ∈ ps, p≤17 → p ∣ P)
    (mirror : P ∣ t+u+H+1)
    (norm : Normal t ps a) (covered : Covers H ps a) :
    ∃ b, Normal u ps b ∧ Covers H ps b := by
  let b (p : ℕ) := H+1+phase (a p) p
  refine ⟨b,?_,?_⟩
  · intro p hp old
    have pp := positive p hp
    have hv : t ≡ phase (a p) p [MOD p] :=
      Nat.ModEq.add_right_cancel' _ ((norm p hp old).trans (phase_add _ pp).symm)
    have zero : t+u+H+1 ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr ((old_dvd p hp old).trans mirror)
    calc
      _ = (u+(H+1))+phase (a p) p := by dsimp [b]; omega
      _ ≡ (u+(H+1))+t [MOD p] := hv.symm.add_left _
      _ = t+u+H+1 := by omega
      _ ≡ 0 [MOD p] := zero
  · intro n low high
    obtain ⟨p,hp,hit⟩ := covered (H+1-n) (by omega) (by omega)
    have hh : phase (a p) p+(H+1-n) ≡ 0 [MOD p] :=
      (hit.add_left _).trans (phase_add _ (positive p hp))
    have res := hh.add_right n
    refine ⟨p,hp,?_⟩
    simpa only [Nat.zero_add,show phase (a p) p+(H+1-n)+n=b p by dsimp [b]; omega] using res.symm

/-- All small classes are removed by one translation. -/
theorem common_phase (a : ℕ → ℕ) :
    ∃ c : ℕ, ∀ p ∈ (17:ℕ).primesLE, c+a p ≡ 0 [MOD p] := by
  let S := (17:ℕ).primesLE
  have nz : ∀ p ∈ S, (fun q : ℕ => q) p ≠ 0 := fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero
  have pairs : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime fun p : ℕ => p) :=
    fun p hp q hq h => (Nat.coprime_primes (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hq).2).mpr h
  let c := Nat.chineseRemainderOfFinset (fun p => phase (a p) p) id S nz pairs
  exact ⟨c,fun p hp => ((c.2 p hp).add_right _).trans (phase_add _ (Nat.mem_primesLE.mp hp).2.pos)⟩

/-- For length 6890, checking these 255256 consecutive starts suffices
    to exclude all assignments of all primes, with no restriction on x. -/
theorem wheel6890 {x : ℕ} {ps : List ℕ}
    (primes : ∀ p, p ∈ ps ↔ p≤x ∧ p.Prime)
    (reject : ∀ t, 507064≤t → t≤762319 → ∀ a, Normal t ps a → ¬Covers 6890 ps a) :
    Erdos687.Y x < 6890 := by
  suffices every : ∀ y, Green46.IsCoveredByResidues x y → y < 6890 by
    have h : Erdos687.Y x ≤ 6889 :=
      csSup_le ⟨0,fun _ => 0,by simp⟩ (fun y hy => Nat.le_of_lt_succ (every y hy))
    exact Nat.lt_succ_of_le h
  intro y all
  obtain ⟨a,ha⟩ := all
  by_contra! le
  have cov : Covers 6890 ps a := by
    intro n hn hN
    obtain ⟨p,hp,pr,h⟩ := ha n (Finset.mem_Icc.mpr ⟨hn,hN.trans le⟩)
    exact ⟨p,(primes p).mpr ⟨hp,pr⟩,h⟩
  have pos : ∀ p ∈ ps, 0<p := fun p hp => ((primes p).mp hp).2.pos
  have dvd : ∀ p ∈ ps, p≤17 → p ∣ 510510 := by
    intro p hp old
    rw [show 510510=primorial 17 by decide]
    exact ((primes p).mp hp).2.dvd_primorial_iff.mpr old
  obtain ⟨c,hc⟩ := common_phase a
  let s := (c+3446)%510510
  let t := 507064+s
  have sb : s<510510 := Nat.mod_lt _ (by decide)
  have ht : t ≡ c [MOD 510510] := by
    calc
      _ ≡ 507064+(c+3446) [MOD 510510] := (Nat.mod_modEq _ _).add_left _
      _ = c+510510 := by omega
      _ ≡ c [MOD 510510] := (Nat.modEq_add_modulus_iff.mpr (Nat.ModEq.refl c)).symm
  have norm : Normal t ps a := by
    intro p hp old
    exact ((ht.of_dvd (dvd p hp old)).add_right _).trans
      (hc p (Nat.mem_primesLE.mpr ⟨old,((primes p).mp hp).2⟩))
  by_cases first : s≤255255
  · exact reject t (by dsimp [t]; omega) (by dsimp [t]; omega) a norm cov
  · let u := 507064+(510511-s)
    have mirror : 510510 ∣ t+u+6890+1 := by
      refine ⟨3,?_⟩
      dsimp [t,u]; omega
    obtain ⟨b,nb,cb⟩ := reflect pos dvd mirror norm cov
    exact reject u (by dsimp [u]; omega) (by dsimp [u]; omega) b nb cb

end Phases687
