/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBRateAnnulus38 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBDiagonal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15AModel

/-!
# [18] Lemma 3.8 with an explicit rate exponent

The existing results for [18] Lemma 3.8 state their rate existentially:
`Lemma38Source.annulus38OneScaleBadBound_of_L27_G4` (one representative scale, from Lemma 2.7 and five Proposition 2.10 tests)
and `MesoModel.annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound` (union over the `4k + 1` representative scales).
Their proofs use the explicit rates `min α₂₇ α₂.₁₀` and `α / 2`. For an exponent uniform in the ambient radius
(`α = α(γ)` chosen before `ρ`), the rate must be visible in the statement. This file copies the two
proofs under new names, with the statements changed only by fixing the rate (the proofs retain their original bodies; private helpers are copied with the prefix `epsB_`):

* `Annulus38Rate F ρ a` — `MesoModel.Annulus38OneScaleBadBound F ρ` with rate exponent `a`;
* `annulus38Rate_of_L27_G4` — one-scale bound, rate `min α27 α`;
* `L38Rate F ρ a` — `CellFamily.Lemma38AnnulusHitBad F ρ` with rate exponent `a` (`L38Rate.lemma38AnnulusHitBad`);
* `l38Rate_of_annulus38Rate` — representative-scale union, rate `a / 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-- `MesoModel.Annulus38OneScaleBadBound F ρ` with the rate exponent `a` fixed. -/
def Annulus38Rate (F : CellFamily.RandomCellFamily) (ρ a : ℝ) : Prop :=
  ∃ β A₈ C : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 ≤ C ∧
    ∀ k (z : ℂ) (r : ℝ) (j : ℕ), CellFamily.mesh k ^ β ≤ r → r ≤ ρ →
      ball z r ⊆ ball (0 : ℂ) ρ →
      F.P (MesoModel.Annulus38OneScaleGood F k z r β A₈ j)ᶜ ≤
        ENNReal.ofReal (C * CellFamily.mesh k ^ a)

/-- `CellFamily.Lemma38AnnulusHitBad F ρ` with the rate exponent `a` fixed. -/
def L38Rate (F : CellFamily.RandomCellFamily) (ρ a : ℝ) : Prop :=
  ∃ β₈ : ℝ, 0 < β₈ ∧ ∃ A₈ C₈ : ℝ,
    ∀ k (z : ℂ) (r : ℝ), CellFamily.mesh k ^ β₈ ≤ r → r ≤ ρ → ball z r ⊆ ball (0 : ℂ) ρ →
      F.P (CellFamily.Lemma38EnvironmentGood F k z r β₈ A₈)ᶜ ≤
        ENNReal.ofReal (C₈ * CellFamily.mesh k ^ a)
theorem L38Rate.lemma38AnnulusHitBad {F : CellFamily.RandomCellFamily} {ρ a : ℝ} (ha : 0 < a)
    (h : L38Rate F ρ a) : CellFamily.Lemma38AnnulusHitBad F ρ := by
  obtain ⟨β₈, hβ₈, A₈, C₈, h⟩ := h
  exact ⟨a, ha, β₈, hβ₈, A₈, C₈, h⟩

/-- **The one-scale Lemma 3.8 bound with its rate `min α27 α` exposed** (body of
`Lemma38Source.annulus38OneScaleBadBound_of_L27_G4`). -/
theorem annulus38Rate_of_L27_G4
    (F : CellFamily.RandomCellFamily)
    {ρ rhoG4 q betaG4 A α α27 C27 Cfail : ℝ}
    (hρ : 0 < ρ) (hρgap : ρ < rhoG4) (hrho1 : rhoG4 < 1)
    (hq : 0 < q) (hq1 : q < 1)
    (hbetaG4 : 0 < betaG4) (hα : 0 < α) (hα27 : 0 < α27)
    (hA : 0 ≤ A) (hC27 : 0 ≤ C27) (hCfail : 0 ≤ Cfail)
    (hpeano : CellFamily.PeanosphereG0 F)
    (h27 : ∀ k, F.P {ω | GMS3.CellDiamBound (F.H k ω) rhoG4
      (CellFamily.mesh k ^ q)}ᶜ ≤ ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27))
    (h210 : ∀ k (D : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) rhoG4 100 betaG4 D f →
      F.P (GMS4.Prop210Bad F k D f (2 * A)
        (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)) :
    Annulus38Rate F ρ (min α27 α) := by
  obtain ⟨β, β', hβ, hβ1, hβ', hβ6, hq40, hβ'20, hα20,
    hβ'q, hβ'G4, _⟩ := Lemma38Source.chooseScaleExponents hq hq1 hbetaG4 hα
  have hq20 : 20 * β ≤ q := by linarith
  have hgap : 0 < (rhoG4 - ρ) / 2 := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      1 ≤ k ∧ CellFamily.mesh k ^ β ≤ 1 / 10 ∧
        CellFamily.mesh k ^ q < (rhoG4 - ρ) / 2 := by
    filter_upwards [eventually_ge_atTop 1,
      Lemma38Source.eventually_meshPow_lt hβ (by norm_num : (0 : ℝ) < 1 / 10),
      Lemma38Source.eventually_meshPow_lt hq hgap] with k hk hlow hδ
    exact ⟨hk, hlow.le, hδ⟩
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  let a : ℝ := min α27 α
  have ha : 0 < a := lt_min hα27 hα
  let Cbase : ℝ := C27 + 5 * Cfail
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  let C : ℝ := Cbase + (CellFamily.mesh K ^ a)⁻¹
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg hCbase
      (inv_nonneg.mpr (Real.rpow_nonneg (GMSLemma27.mesh_pos K).le a))
  refine ⟨β, 120002 * (A + 1), C, hβ, hβ1, hC, ?_⟩
  intro k z r j hrlow hrρ hball
  by_cases hk : K ≤ k
  · obtain ⟨hk1, hlow, hδgap⟩ := hK k hk
    have hbound := Lemma38Source.oneScaleBad_le_of_inputs F k j z hk1 hrlow hrρ hball
      hρ hρgap hrho1 hβ hβ' hbetaG4 hβ6 hβ'q hβ'G4
      hq20 hβ'20 hα20 hA hC27 hCfail hlow hδgap (h27 k)
      hpeano h210
    have hCbase_le : Cbase ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right
        (inv_nonneg.mpr (Real.rpow_nonneg (GMSLemma27.mesh_pos K).le a))
    exact hbound.trans (ENNReal.ofReal_le_ofReal (by
      change Cbase * CellFamily.mesh k ^ a ≤ C * CellFamily.mesh k ^ a
      exact mul_le_mul_of_nonneg_right hCbase_le
        (Real.rpow_nonneg (GMSLemma27.mesh_pos k).le a)))
  · have hk' : k ≤ K := Nat.le_of_not_ge hk
    have hmesh : CellFamily.mesh K ≤ CellFamily.mesh k := EpsB.mesh_antitone hk'
    have hpow : CellFamily.mesh K ^ a ≤ CellFamily.mesh k ^ a :=
      Real.rpow_le_rpow (GMSLemma27.mesh_pos K).le hmesh ha.le
    have hsmall : 1 ≤ C * CellFamily.mesh k ^ a := by
      have hNpos : 0 < CellFamily.mesh K ^ a :=
        Real.rpow_pos_of_pos (GMSLemma27.mesh_pos K) a
      have hbase : 1 ≤ (CellFamily.mesh K ^ a)⁻¹ * CellFamily.mesh K ^ a := by
        rw [inv_mul_cancel₀ hNpos.ne']
      have hmon := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hNpos.le)
      have hCinv : (CellFamily.mesh K ^ a)⁻¹ ≤ C := by
        dsimp [C]
        linarith
      have hmon' := mul_le_mul_of_nonneg_right hCinv
        (Real.rpow_nonneg (GMSLemma27.mesh_pos k).le a)
      nlinarith [hbase, hmon, hmon']
    calc
      F.P (MesoModel.Annulus38OneScaleGood F k z r β
        (120002 * (A + 1)) j)ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ a) :=
        ENNReal.ofReal_le_ofReal hsmall

/-! ### Grid of representative scales (private helpers of `MesoModel/Annulus38.lean`, copied) -/

private theorem epsB_gridPow_reaches_unit (k : ℕ) :
    (2 : ℝ) ^ k ≤ (5 / 4 : ℝ) ^ (4 * k) := by
  have hbase : 2 ≤ (5 / 4 : ℝ) ^ 4 := by norm_num
  calc
    (2 : ℝ) ^ k ≤ ((5 / 4 : ℝ) ^ 4) ^ k := pow_le_pow_left₀ (by norm_num) hbase _
    _ = (5 / 4 : ℝ) ^ (4 * k) := by rw [← pow_mul]

private theorem epsB_mesh_le_one (k : ℕ) : CellFamily.mesh k ≤ 1 := by
  rw [show CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ by simp [CellFamily.mesh, zpow_neg]]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

private theorem epsB_mesh_le_rpow_of_beta_le_one (k : ℕ) {β : ℝ}
    (_hβ0 : 0 < β) (hβ1 : β ≤ 1) : CellFamily.mesh k ≤ CellFamily.mesh k ^ β := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (zpow_pos (by norm_num : (0 : ℝ) < 2) _) (epsB_mesh_le_one k) hβ1
  simpa [CellFamily.mesh, Real.rpow_one] using h

private theorem epsB_rawScale_crosses {β : ℝ} (k : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    1 / 10 ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) := by
  have hmesh : CellFamily.mesh k ≤ CellFamily.mesh k ^ β :=
    epsB_mesh_le_rpow_of_beta_le_one k hβ0 hβ1
  have hmesh' : (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by
    simp [zpow_neg]
  have hmeshEq : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
    exact hmesh'
  have hp := epsB_gridPow_reaches_unit k
  have hpowPos : 0 < (2 : ℝ) ^ k := by positivity
  have hmul : 1 ≤ ((2 : ℝ) ^ k)⁻¹ * (5 / 4 : ℝ) ^ (4 * k) := by
    calc
      1 = ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ k := by field_simp
      _ ≤ ((2 : ℝ) ^ k)⁻¹ * (5 / 4 : ℝ) ^ (4 * k) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hpowPos.le)
  have hprod : CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) ≤
      CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) :=
    mul_le_mul_of_nonneg_right hmesh (pow_nonneg (by norm_num) _)
  have hprod' : 1 ≤ CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) := by
    calc
      1 ≤ ((2 : ℝ) ^ k)⁻¹ * (5 / 4 : ℝ) ^ (4 * k) := hmul
      _ = CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) := by rw [← hmeshEq]
  calc
    1 / 10 ≤ 1 := by norm_num
    _ ≤ CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) := hprod'
    _ ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) := hprod

private theorem epsB_scaleGrid_covers {β : ℝ} (k : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hlow : CellFamily.mesh k ^ β ≤ 1 / 10) {s : ℝ}
    (hslo : CellFamily.mesh k ^ β ≤ s) (hshi : s ≤ 1 / 10) :
    ∃ j ≤ 4 * k, MesoModel.annulus38ScaleRepresentative k β j ≤ s ∧
      s ≤ min (5 * MesoModel.annulus38ScaleRepresentative k β j / 4) (1 / 10) := by
  let raw : ℕ → ℝ := fun j => CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ j
  have hcross : s ≤ raw (4 * k) := by
    have hs := epsB_rawScale_crosses k hβ0 hβ1
    dsimp [raw]
    calc
      s ≤ 1 / 10 := hshi
      _ ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) := hs
  have hHas : ∃ n, s ≤ raw n := ⟨4 * k, hcross⟩
  let n := Nat.find hHas
  have hn : s ≤ raw n := Nat.find_spec hHas
  have hnle : n ≤ 4 * k := Nat.find_min' hHas hcross
  by_cases hn0 : n = 0
  · subst n
    refine ⟨0, by omega, ?_, ?_⟩
    · dsimp [MesoModel.annulus38ScaleRepresentative, raw]
      rw [pow_zero, mul_one]
      exact le_trans (min_le_left _ _) hslo
    · have hfind0 : Nat.find hHas = 0 := hn0
      have hn' : s ≤ CellFamily.mesh k ^ β := by
        rw [hfind0] at hn
        simpa [raw] using hn
      have hrep : MesoModel.annulus38ScaleRepresentative k β 0 = CellFamily.mesh k ^ β := by
        change min (CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ 0) (1 / 10) = _
        rw [pow_zero, mul_one, min_eq_left hlow]
      have hsEq : s = CellFamily.mesh k ^ β := le_antisymm hn' hslo
      rw [hrep]
      rw [hsEq]
      apply le_min
      · have hlowpos : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos
          (zpow_pos (by norm_num : (0 : ℝ) < 2) _) β
        nlinarith
      · exact hlow
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let j := n - 1
    have hjn : j + 1 = n := by omega
    have hprev : ¬ s ≤ raw j := Nat.find_min hHas (by omega)
    have hprevlt : raw j < s := lt_of_not_ge hprev
    have hrawSucc : raw n = raw j * (5 / 4 : ℝ) := by
      dsimp [raw]
      rw [← hjn, pow_succ]
      ring
    have hrep : MesoModel.annulus38ScaleRepresentative k β j = raw j := by
      dsimp [MesoModel.annulus38ScaleRepresentative]
      rw [min_eq_left (le_of_lt (lt_of_lt_of_le hprevlt hshi))]
    refine ⟨j, by omega, ?_, ?_⟩
    · rw [hrep]
      exact le_of_lt hprevlt
    · have hscaleEq : 5 * raw j / 4 = raw j * (5 / 4 : ℝ) := by ring
      apply le_min
      · rw [hrep, hscaleEq]
        rw [hrawSucc] at hn
        exact hn
      · exact hshi

private theorem epsB_gridCard_mul_mesh_rpow {α : ℝ} (hα : 0 < α) (k : ℕ) :
    (4 * (k : ℝ) + 1) * CellFamily.mesh k ^ α ≤
      (1 + 4 / ((2 : ℝ) ^ (α / 2) - 1)) * CellFamily.mesh k ^ (α / 2) := by
  let b : ℝ := (2 : ℝ) ^ (-α / 2)
  let q : ℝ := (2 : ℝ) ^ (α / 2)
  have hq1 : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hqpos : 0 < q := by linarith
  have hbpos : 0 < b := by positivity
  have hbq : b * q = 1 := by
    dsimp [b, q]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hexp : -α / 2 + α / 2 = 0 := by ring
    rw [hexp]
    simp
  have hbpow : b ^ k = (q ^ k)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← mul_pow, hbq, one_pow]
  have hBern : ∀ n : ℕ, 1 + (n : ℝ) * (q - 1) ≤ q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hd : 0 ≤ q - 1 := le_of_lt (sub_pos.mpr hq1)
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hqEq : q = 1 + (q - 1) := by ring
        have hstep : 1 + ((n + 1 : ℕ) : ℝ) * (q - 1) ≤
            (1 + (n : ℝ) * (q - 1)) * q := by
          rw [hqEq]
          push_cast
          nlinarith [mul_nonneg hn (sq_nonneg (q - 1))]
        calc
          1 + ((n + 1 : ℕ) : ℝ) * (q - 1) ≤
              (1 + (n : ℝ) * (q - 1)) * q := hstep
          _ ≤ q ^ n * q := mul_le_mul_of_nonneg_right ih hqpos.le
          _ = q ^ (n + 1) := by rw [pow_succ]
  have hratio : (k : ℝ) / q ^ k ≤ 1 / (q - 1) := by
    apply (div_le_div_iff₀ (pow_pos hqpos k) (sub_pos.mpr hq1)).2
    have h := hBern k
    nlinarith
  have hkbound : (k : ℝ) * b ^ k ≤ 1 / (q - 1) := by
    calc
      (k : ℝ) * b ^ k = (k : ℝ) / q ^ k := by rw [hbpow, ← div_eq_mul_inv]
      _ ≤ 1 / (q - 1) := hratio
  have hbkle : b ^ k ≤ 1 := by
    rw [hbpow]
    have hqk : 1 ≤ q ^ k := by
      have h := hBern k
      have hd : 0 ≤ (k : ℝ) * (q - 1) := mul_nonneg (Nat.cast_nonneg k)
        (le_of_lt (sub_pos.mpr hq1))
      linarith
    exact inv_le_one_of_one_le₀ hqk
  have hcount : (4 * (k : ℝ) + 1) * b ^ k ≤ 4 / (q - 1) + 1 := by
    calc
      (4 * (k : ℝ) + 1) * b ^ k = 4 * ((k : ℝ) * b ^ k) + b ^ k := by ring
      _ ≤ 4 * (1 / (q - 1)) + 1 := add_le_add
        (mul_le_mul_of_nonneg_left hkbound (by norm_num)) hbkle
      _ = 4 / (q - 1) + 1 := by ring
  have hmeshHalf : CellFamily.mesh k ^ (α / 2) = b ^ k := by
    rw [MatedCRTHarmonic.GMSLemma27.mesh_rpow_eq]
    congr 1
    dsimp [b]
    congr 1
    ring
  have hmeshPow : CellFamily.mesh k ^ α = (CellFamily.mesh k ^ (α / 2)) ^ 2 := by
    calc
      CellFamily.mesh k ^ α = CellFamily.mesh k ^ (α / 2 + α / 2) := by congr 1; ring
      _ = CellFamily.mesh k ^ (α / 2) * CellFamily.mesh k ^ (α / 2) :=
        Real.rpow_add (zpow_pos (by norm_num : (0 : ℝ) < 2) _) _ _
      _ = (CellFamily.mesh k ^ (α / 2)) ^ 2 := by ring
  calc
    (4 * (k : ℝ) + 1) * CellFamily.mesh k ^ α =
        ((4 * (k : ℝ) + 1) * b ^ k) * b ^ k := by rw [hmeshPow, hmeshHalf]; ring
    _ ≤ (4 / (q - 1) + 1) * b ^ k :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hbpos.le _)
    _ = (1 + 4 / ((2 : ℝ) ^ (α / 2) - 1)) * CellFamily.mesh k ^ (α / 2) := by
      rw [hmeshHalf]
      dsimp [q]
      ring

/-- **The union over the representative scales with its rate `a / 2` exposed** (body of
`MesoModel.annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound`). -/
theorem l38Rate_of_annulus38Rate (F : CellFamily.RandomCellFamily) (ρ : ℝ) {α : ℝ} (hα : 0 < α)
    (hinput : Annulus38Rate F ρ α) : L38Rate F ρ (α / 2) := by
  rcases hinput with ⟨β, A₈, C, hβ, hβ1, hC, hscale⟩
  let C₈ : ℝ := C * (1 + 4 / ((2 : ℝ) ^ (α / 2) - 1))
  have hα₈ : 0 < α / 2 := by linarith
  have hq : 1 < (2 : ℝ) ^ (α / 2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hC₈ : 0 ≤ C₈ := by
    dsimp [C₈]
    positivity
  refine ⟨β, hβ, A₈, C₈, fun k z r hkr hr hball => ?_⟩
  let target : Set F.Ω := CellFamily.Lemma38EnvironmentGood F k z r β A₈
  by_cases hlow : CellFamily.mesh k ^ β ≤ 1 / 10
  · let I : Finset ℕ := Finset.range (4 * k + 1)
    let bad : ℕ → Set F.Ω := fun j => (MesoModel.Annulus38OneScaleGood F k z r β A₈ j)ᶜ
    let allBad : Set F.Ω := ⋃ j ∈ I, bad j
    have hbadGrid : F.P allBad ≤
        (I.card : ℝ≥0∞) * ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
      apply GMS4.finite_union_measure_le_card_mul
      intro j hj
      exact hscale k z r j hkr hr hball
    have hgridGood : allBadᶜ ⊆ target := by
      intro ω hω
      change ∀ s ∈ Set.Icc (CellFamily.mesh k ^ β) (1 / 10),
        ∀ x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s * r)),
          ENNReal.ofReal (1 - A₈ / Real.sqrt (Real.log s⁻¹)) ≤
            (F.G k ω).walkLaw x {ω' | CellFamily.HitsBefore (F.H k ω).cell z s r
              ((F.G k ω).vertexPath ω')}
      intro s hs x hx
      obtain ⟨j, hj, hjlow, hjhigh⟩ := epsB_scaleGrid_covers k hβ hβ1 hlow hs.1 hs.2
      have hjI : j ∈ I := by
        simp [I]
        omega
      have hnotBad : ω ∉ bad j := by
        intro hmem
        have hnotUnion : ¬ ω ∈ ⋃ i ∈ I, bad i := by
          simpa only [allBad, Set.mem_compl_iff] using hω
        apply hnotUnion
        exact Set.mem_iUnion₂.mpr ⟨j, hjI, hmem⟩
      have hblock : ω ∈ MesoModel.Annulus38OneScaleGood F k z r β A₈ j := by
        simpa [bad] using hnotBad
      exact hblock s ⟨hjlow, hjhigh⟩ x hx
    have hbadTarget : F.P targetᶜ ≤
        ENNReal.ofReal (C₈ * CellFamily.mesh k ^ (α / 2)) := by
      have hcardReal : (I.card : ℝ) = 4 * (k : ℝ) + 1 := by
        simp [I]
      have hreal : (I.card : ℝ) * (C * CellFamily.mesh k ^ α) ≤
          C₈ * CellFamily.mesh k ^ (α / 2) := by
        rw [hcardReal]
        calc
          (4 * (k : ℝ) + 1) * (C * CellFamily.mesh k ^ α) =
              C * ((4 * (k : ℝ) + 1) * CellFamily.mesh k ^ α) := by ring
          _ ≤ C * ((1 + 4 / ((2 : ℝ) ^ (α / 2) - 1)) *
              CellFamily.mesh k ^ (α / 2)) :=
            mul_le_mul_of_nonneg_left (epsB_gridCard_mul_mesh_rpow hα k) hC
          _ = C₈ * CellFamily.mesh k ^ (α / 2) := by dsimp [C₈]; ring
      have htargetSub : targetᶜ ⊆ allBad := by
        intro ω hω
        by_contra hnot
        exact hω (hgridGood hnot)
      calc
        F.P targetᶜ ≤ F.P allBad := measure_mono htargetSub
        _ ≤ (I.card : ℝ≥0∞) * ENNReal.ofReal (C * CellFamily.mesh k ^ α) := hbadGrid
        _ = ENNReal.ofReal ((I.card : ℝ) * (C * CellFamily.mesh k ^ α)) := by
          rw [show (I.card : ℝ≥0∞) = ENNReal.ofReal (I.card : ℝ) by simp,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ ≤ ENNReal.ofReal (C₈ * CellFamily.mesh k ^ (α / 2)) :=
          ENNReal.ofReal_le_ofReal hreal
    simpa [target] using hbadTarget
  · have hempty : Set.Icc (CellFamily.mesh k ^ β) (1 / 10) = ∅ := by
      ext s
      constructor
      · intro hs
        exact False.elim ((not_le_of_gt (lt_of_not_ge hlow)) (le_trans hs.1 hs.2))
      · intro hs
        exact False.elim hs
    have htarget : target = Set.univ := by
      ext ω
      simp only [target, CellFamily.Lemma38EnvironmentGood, Set.mem_ofPred_eq,
        Set.mem_univ, iff_true]
      intro s hs
      have hs' : s ∈ (∅ : Set ℝ) := by rw [← hempty]; exact hs
      exact False.elim (Set.notMem_empty s hs')
    change F.P targetᶜ ≤ _
    rw [htarget]
    simp

end MatedCRTHarmonic.GMSMain.EpsB
