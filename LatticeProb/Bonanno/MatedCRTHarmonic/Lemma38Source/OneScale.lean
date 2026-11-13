/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Lemma38Source.OneScale at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Lemma38Source.Numerics
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# The one-scale Lemma 3.8 event

The fixed representative uses one set of five Proposition 2.10 tests for its
entire `5/4` block. The deterministic inclusion below retains the full
interval event in `MesoModel.Annulus38OneScaleGood`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped ENNReal Topology

namespace MatedCRTHarmonic.Lemma38Source

private theorem C100_margins :
    16 * Real.pi ≤ (100 : ℝ) ∧
      2 * ((Real.log 10) ^ 2)⁻¹ ≤ (100 : ℝ) := by
  have hπ := Real.pi_le_four
  have hlog : 1 ≤ Real.log 10 := by
    have he : Real.exp 1 < 10 := Real.exp_one_lt_three.trans (by norm_num)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he.le
  have hlogSq : 1 ≤ (Real.log 10) ^ 2 := by nlinarith
  have hinv : ((Real.log 10) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogSq
  constructor <;> nlinarith

/-- Explicit mesh-scale assumptions that ensure the five test pairs and G3's
geometric conditions hold at one representative. -/
theorem fiveInputGood_subset_annulus38Good
    (F : CellFamily.RandomCellFamily) (k j : ℕ) (z : ℂ)
    {r ρ rhoG4 q β β' betaG4 A α : ℝ}
    (hk : 1 ≤ k) (hrlow : CellFamily.mesh k ^ β ≤ r)
    (hball : ball z r ⊆ ball (0 : ℂ) ρ)
    (hρ : 0 < ρ) (hρgap : ρ < rhoG4) (hrho1 : rhoG4 < 1)
    (hβ : 0 < β) (hβ' : 0 < β') (hbetaG4 : 0 < betaG4)
    (hβ6 : 6 * β ≤ betaG4) (hβ'q : β' ≤ q)
    (hβ'G4 : β' ≤ betaG4)
    (hq20 : 20 * β ≤ q) (hβ'20 : 20 * β ≤ β')
    (hα20 : 20 * β ≤ α) (hA : 0 ≤ A)
    (hlow : CellFamily.mesh k ^ β ≤ 1 / 10)
    (hδgap : CellFamily.mesh k ^ q < (rhoG4 - ρ) / 2) :
    fiveInputGood F k z
      (MesoModel.annulus38ScaleRepresentative k β j * r) r
      (r + (rhoG4 - ρ) / 2) (CellFamily.mesh k ^ β') A α
      rhoG4 (CellFamily.mesh k ^ q) ⊆
    MesoModel.Annulus38OneScaleGood F k z r β (120002 * (A + 1)) j := by
  let s := MesoModel.annulus38ScaleRepresentative k β j
  let ε := CellFamily.mesh k
  let δ := ε ^ q
  let w := ε ^ β'
  let η := ε ^ α
  let R₁ := r + (rhoG4 - ρ) / 2
  have hε := GMSLemma27.mesh_pos k
  have hε1 := GMSLemma27.mesh_lt_one (by omega : k ≠ 0)
  have hslo : ε ^ β ≤ s := representative_lower hlow
  have hs : 0 < s := (Real.rpow_pos_of_pos hε β).trans_le hslo
  have hs10 : s ≤ 1 / 10 := min_le_right _ _
  have hr : 0 < r := (Real.rpow_pos_of_pos hε β).trans_le hrlow
  have hr1 : r < 1 := by
    have hcenter := center_add_radius_le_of_ball_subset hr hball
    nlinarith [norm_nonneg z]
  have houter := outerBallMargins hr hball hρgap hrho1 hδgap
  have hR : r ≤ R₁ := houter.2.1
  have hR1 : R₁ < 1 := houter.2.2.1
  have hballR : ball z R₁ ⊆ ball 0 rhoG4 := houter.2.2.2.1
  have hclosed : closedBall z R₁ ⊆ ball 0 rhoG4 := houter.2.2.2.2
  have hRδ : r + δ < R₁ := houter.1
  have hι : 0 < s * r := mul_pos hs hr
  have hι1 : s * r ≤ 1 := by nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith) hr.le]
  have hδ0 : 0 ≤ δ := (Real.rpow_pos_of_pos hε q).le
  have hw : 0 < w := Real.rpow_pos_of_pos hε β'
  have hη : 0 ≤ η := (Real.rpow_pos_of_pos hε α).le
  have hδι : δ ≤ (s * r) ^ 10 :=
    meshPow_le_innerPowTen hε hε1.le hslo hrlow hq20
  have hwι : w ≤ (s * r) ^ 10 :=
    meshPow_le_innerPowTen hε hε1.le hslo hrlow hβ'20
  have hηι : η ≤ (s * r) ^ 10 :=
    meshPow_le_innerPowTen hε hε1.le hslo hrlow hα20
  have hδw : δ ≤ w := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hβ'q
  have h6 : 6 * δ ≤ s * r := by
    have hpow : (s * r) ^ 10 ≤ (s * r) ^ 2 :=
      pow_le_pow_of_le_one hι.le hι1 (by omega)
    have hsq : (s * r) ^ 2 ≤ (s * r) / 10 := by
      have hsr10 : s * r ≤ 1 / 10 := by
        nlinarith [mul_nonneg (show 0 ≤ 1 - r by linarith) hs.le]
      nlinarith
    linarith
  have hadm := fiveAdmissible_uniform hk j z hβ hlow hrlow hR hR1 hballR
    (by linarith) hrho1 C100_margins.1 C100_margins.2 hbetaG4 hβ6 hβ'G4
  intro ω hinput
  change ∀ s' ∈ Icc s (min (5 * s / 4) (1 / 10)),
      ∀ x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s' * r)),
        ENNReal.ofReal (1 - (120002 * (A + 1)) /
          Real.sqrt (Real.log s'⁻¹)) ≤
          (F.G k ω).walkLaw x
            {ω' | CellFamily.HitsBefore (F.H k ω).cell z s' r
              ((F.G k ω).vertexPath ω')}
  intro s' hs' x hx
  have hss' : s ≤ s' := hs'.1
  have hs'5 : 4 * s' ≤ 5 * s := by
    have h := hs'.2.trans (min_le_left _ _)
    linarith
  have hs'10 : s' ≤ 1 / 10 := hs'.2.trans (min_le_right _ _)
  have hlog : 0 < Real.log (r / (s * r)) := by
    have h10 : 10 * (s * r) ≤ r := by nlinarith
    linarith [(annulusLogMargins hι h10 hr1.le).1]
  have hκ : 0 < (Real.sqrt (Real.log (r / (s * r))))⁻¹ := by
    exact inv_pos.mpr (Real.sqrt_pos.2 hlog)
  have hwalk := fiveInput_walkLaw_interval F k ω hinput hr hs hss' hs'5 hs10
    hs'10 hδ0 h6 hRδ hw hδw hA hη hκ hclosed hx
  have hnum := lemma38Error_le_target hs hss' hs'10 hr hr1.le hδ0 hδι
    hw.le hwι hA hη hηι
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left hnum 1)).trans hwalk

/-- At every sufficiently small dyadic mesh, the exact whole-interval bad
event has the two source polynomial costs. -/
theorem oneScaleBad_le_of_inputs
    (F : CellFamily.RandomCellFamily) (k j : ℕ) (z : ℂ)
    {r ρ rhoG4 q β β' betaG4 A α α27 C27 Cfail : ℝ}
    (hk : 1 ≤ k) (hrlow : CellFamily.mesh k ^ β ≤ r) (hrρ : r ≤ ρ)
    (hball : ball z r ⊆ ball (0 : ℂ) ρ)
    (hρ : 0 < ρ) (hρgap : ρ < rhoG4) (hrho1 : rhoG4 < 1)
    (hβ : 0 < β) (hβ' : 0 < β') (hbetaG4 : 0 < betaG4)
    (hβ6 : 6 * β ≤ betaG4) (hβ'q : β' ≤ q) (hβ'G4 : β' ≤ betaG4)
    (hq20 : 20 * β ≤ q) (hβ'20 : 20 * β ≤ β')
    (hα20 : 20 * β ≤ α) (hA : 0 ≤ A)
    (hC27 : 0 ≤ C27) (hCfail : 0 ≤ Cfail)
    (hlow : CellFamily.mesh k ^ β ≤ 1 / 10)
    (hδgap : CellFamily.mesh k ^ q < (rhoG4 - ρ) / 2)
    (h27 : F.P {ω | GMS3.CellDiamBound (F.H k ω) rhoG4
      (CellFamily.mesh k ^ q)}ᶜ ≤ ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27))
    (hpeano : CellFamily.PeanosphereG0 F)
    (h210 : ∀ k (D : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) rhoG4 100 betaG4 D f →
      F.P (GMS4.Prop210Bad F k D f (2 * A)
        (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)) :
    F.P (MesoModel.Annulus38OneScaleGood F k z r β
      (120002 * (A + 1)) j)ᶜ ≤
      ENNReal.ofReal ((C27 + 5 * Cfail) *
        CellFamily.mesh k ^ min α27 α) := by
  let s := MesoModel.annulus38ScaleRepresentative k β j
  let R₁ := r + (rhoG4 - ρ) / 2
  have hr : 0 < r := by
    have hmesh := GMSLemma27.mesh_pos k
    exact (Real.rpow_pos_of_pos hmesh β).trans_le hrlow
  have houter := outerBallMargins hr hball hρgap hrho1 hδgap
  have hR : r ≤ R₁ := houter.2.1
  have hR1 : R₁ < 1 := houter.2.2.1
  have hballR : ball z R₁ ⊆ ball 0 rhoG4 := houter.2.2.2.1
  have hadm := fiveAdmissible_uniform hk j z hβ hlow hrlow hR hR1 hballR
    (by linarith) hrho1 C100_margins.1 C100_margins.2 hbetaG4 hβ6 hβ'G4
  have hsub := fiveInputGood_subset_annulus38Good F k j z hk hrlow hball
    hρ hρgap hrho1 hβ hβ' hbetaG4 hβ6 hβ'q hβ'G4
    hq20 hβ'20 hα20 hA hlow hδgap
  have hinput := fiveInputBad_le F k z (s * r) r R₁
    (CellFamily.mesh k ^ β') h27 hpeano h210 hadm
  calc
    F.P (MesoModel.Annulus38OneScaleGood F k z r β
        (120002 * (A + 1)) j)ᶜ ≤
        F.P (fiveInputGood F k z (s * r) r R₁ (CellFamily.mesh k ^ β')
          A α rhoG4 (CellFamily.mesh k ^ q))ᶜ :=
      measure_mono (Set.compl_subset_compl.mpr hsub)
    _ ≤ ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27) +
        ENNReal.ofReal (5 * Cfail * CellFamily.mesh k ^ α) := hinput
    _ ≤ ENNReal.ofReal ((C27 + 5 * Cfail) *
        CellFamily.mesh k ^ min α27 α) :=
      two_rates_le_min k hC27 hCfail

private theorem mesh_antitone : Antitone CellFamily.mesh := by
  intro a b hab
  rw [show CellFamily.mesh a = ((2 : ℝ) ^ a)⁻¹ by simp [CellFamily.mesh, zpow_neg, zpow_natCast],
    show CellFamily.mesh b = ((2 : ℝ) ^ b)⁻¹ by simp [CellFamily.mesh, zpow_neg, zpow_natCast]]
  apply inv_anti₀ (by positivity)
  gcongr
  norm_num

/-- The source one-scale outer-measure interface, conditional on one exact
uniform Proposition 2.10 per-test bound and Lemma 2.7's checked diameter bound. -/
theorem annulus38OneScaleBadBound_of_L27_G4
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
    MesoModel.Annulus38OneScaleBadBound F ρ := by
  obtain ⟨β, β', hβ, hβ1, hβ', hβ6, hq40, hβ'20, hα20,
    hβ'q, hβ'G4, _⟩ := chooseScaleExponents hq hq1 hbetaG4 hα
  have hq20 : 20 * β ≤ q := by linarith
  have hgap : 0 < (rhoG4 - ρ) / 2 := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      1 ≤ k ∧ CellFamily.mesh k ^ β ≤ 1 / 10 ∧
        CellFamily.mesh k ^ q < (rhoG4 - ρ) / 2 := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_meshPow_lt hβ (by norm_num : (0 : ℝ) < 1 / 10),
      eventually_meshPow_lt hq hgap] with k hk hlow hδ
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
  refine ⟨a, β, 120002 * (A + 1), C, ha, hβ, hβ1, hC, ?_⟩
  intro k z r j hrlow hrρ hball
  by_cases hk : K ≤ k
  · obtain ⟨hk1, hlow, hδgap⟩ := hK k hk
    have hbound := oneScaleBad_le_of_inputs F k j z hk1 hrlow hrρ hball
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
    have hmesh : CellFamily.mesh K ≤ CellFamily.mesh k := mesh_antitone hk'
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

end MatedCRTHarmonic.Lemma38Source
