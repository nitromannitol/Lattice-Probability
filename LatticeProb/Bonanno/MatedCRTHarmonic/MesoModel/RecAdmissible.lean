/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.RecAdmissible at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma34
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# Deterministic test-pair admissibility for the recurrence adapter

The tests are the three functions in GMS3's Theorem 1.4 input. The inequalities below expose the
numerical margins needed by GMS4's Proposition 2.10 admissibility predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic.GMS3
private theorem recBallFrontierVolume {ρ C : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hC : 16 * π ≤ C) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    volume (thickening r (frontier (ball (0 : ℂ) ρ))) ≤ ENNReal.ofReal (C * r) := by
  have hsub : thickening r (frontier (ball (0 : ℂ) ρ)) ⊆
      {u : ℂ | |‖u‖ - ρ| < r} := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := mem_thickening_iff.mp hu
    have hv' : ‖v‖ = ρ := by
      simpa only [mem_sphere_iff_norm, sub_zero] using
        (frontier_ball_subset_sphere hv)
    have hn := abs_norm_sub_norm_le u v
    have hd : ‖u - v‖ < r := by simpa only [dist_eq_norm] using huv
    simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
  calc
    volume (thickening r (frontier (ball (0 : ℂ) ρ))) ≤
      volume {u : ℂ | |‖u‖ - ρ| < r} := measure_mono hsub
    _ ≤ ENNReal.ofReal (4 * π * r * (ρ + r)) := by
      simpa only [sub_zero] using
        (volume_radialShell_le (z := (0 : ℂ)) (a := ρ) (r := r) hρ hr.1.le)
    _ ≤ ENNReal.ofReal (C * r) := by
      apply ENNReal.ofReal_le_ofReal
      have hr0 : 0 ≤ r := hr.1.le
      have hr1 : r < 1 := hr.2
      have hfac : 0 ≤ 4 * π * r := by positivity
      calc
        4 * π * r * (ρ + r) ≤ 4 * π * r * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hfac
        _ = 8 * π * r := by ring
        _ ≤ C * r := mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hr.1.le

/-- Proposition 2.10 admissibility for the two-circle boundary layer on the outer ball. -/
theorem recBallLayer_admissible {ε s ρ ρ₁ w rho C beta : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hρ₁ : 0 < ρ₁)
    (hρ₁rho : ρ₁ ≤ rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C)
    (hbeta : 0 < beta) (hw : 0 < w)
    (hOne : 1 ≤ C * ε ^ (-beta)) (hLip : w⁻¹ ≤ C * ε ^ (-beta)) :
    MatedCRTHarmonic.GMS4.Prop210Admissible ε rho C beta
      (ball 0 ρ₁) (lemma34Layer s ρ w) := by
  have hrho : 0 < rho := hρ₁.trans_le hρ₁rho
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  have hLips : LipschitzWith (Real.toNNReal w⁻¹) (lemma34Layer s ρ w) := by
    unfold lemma34Layer
    simpa only [max_self] using
      (lipschitzWith_radialBump 0 s hw).max (lipschitzWith_radialBump 0 ρ hw)
  refine ⟨hε, hε1, hrho, hrho1, hC1, hbeta,
    isOpen_ball, isConnected_ball hρ₁, ball_subset_ball hρ₁rho,
    ?_, ?_, ?_⟩
  · intro r hr
    exact recBallFrontierVolume hρ₁.le (hρ₁rho.trans_lt hrho1) hC r hr
  · intro z hz
    have hnonneg : 0 ≤ lemma34Layer s ρ w z := by
      unfold lemma34Layer
      exact le_trans (radialBump_nonneg 0 s w z) (le_max_left _ _)
    have hle : lemma34Layer s ρ w z ≤ 1 := by
      unfold lemma34Layer
      exact max_le (radialBump_le_one 0 s w z) (radialBump_le_one 0 ρ w z)
    exact ⟨hnonneg, hle.trans hOne⟩
  · intro z hz v hv
    have hdist := hLips.dist_le_mul z v
    rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.mpr hw.le)] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_right hLip dist_nonneg)

/-- The constant and boundary-layer growth inequalities follow from the selected exponent. -/
theorem recMeshOneAndLayer {β' betaG4 C : ℝ}
    (hC : 1 ≤ C) (hbeta : 0 ≤ betaG4) (hβ' : β' ≤ betaG4) :
    (∀ k : ℕ, 1 ≤ k → 1 ≤ C * CellFamily.mesh k ^ (-betaG4)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (CellFamily.mesh k ^ β')⁻¹ ≤ C * CellFamily.mesh k ^ (-betaG4)) := by
  constructor
  · intro k hk
    have hε := GMSLemma27.mesh_pos k
    have hε1 := (GMSLemma27.mesh_lt_one (by omega : k ≠ 0)).le
    have hpow : 1 ≤ CellFamily.mesh k ^ (-betaG4) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (neg_nonpos.mpr hbeta)
    calc
      (1 : ℝ) ≤ CellFamily.mesh k ^ (-betaG4) := hpow
      _ = 1 * CellFamily.mesh k ^ (-betaG4) := by ring
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

  · intro k hk
    have hε := GMSLemma27.mesh_pos k
    have hε1 := (GMSLemma27.mesh_lt_one (by omega : k ≠ 0)).le
    calc
      (CellFamily.mesh k ^ β')⁻¹ = CellFamily.mesh k ^ (-β') :=
        (Real.rpow_neg hε.le β').symm
      _ ≤ CellFamily.mesh k ^ (-betaG4) :=
        Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
      _ = 1 * CellFamily.mesh k ^ (-betaG4) := by ring
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

end MatedCRTHarmonic.MesoModel
