/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P2HeatDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P2HeatBasic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteCoverGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusFieldLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourCrossing
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenConnectedFinite

 














set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric (DistC IsPiecewiseC1Path lfppLen)
open LQGMetric.DDDF (crossLenIn)

namespace SupercriticalLQGUniqueness.B2.Polylog

 


theorem aroundDist_lfppMetric_le_lfppLen (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (A : EuclideanAnnulus) {γ : ℝ → ℂ} {u v : ℂ} (hγ : IsPiecewiseC1Path γ u v)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ A.toSet)
    (hdisc : LQGMetric.Disconnects (γ '' Icc (0 : ℝ) 1) A.innerBoundary A.outerBoundary) :
    aroundDist (Median.lfppMetric ξ a φ) A ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ γ := by
  have hc := Median.lfppMetric_isCurve ξ a φ hγ
  have hdisc' : Disconnects (γ '' Icc (0 : ℝ) 1) A.innerBoundary A.outerBoundary :=
    (Uniqueness.Toolkit.PathInfimum.disconnects_iff_path_hit_of_closed
      (isCompact_Icc.image_of_continuousOn hγ.continuousOn).isClosed).2 hdisc
  calc aroundDist (Median.lfppMetric ξ a φ) A ≤ (Median.lfppMetric ξ a φ).len γ 0 1 := by
        unfold aroundDist
        exact iInf_le_of_le γ (iInf_le_of_le 0 (iInf_le_of_le 1 (iInf_le_of_le hc
          (iInf_le_of_le hA (iInf_le_of_le hdisc' le_rfl)))))
    _ ≤ _ := Median.lfppMetric_len_le_lfppLen ξ a φ hγ

 
theorem crossLenIn_le_lfppDOn {ξ : ℝ} {f : ℂ → ℝ} {U K₁ K₂ : Set ℂ} {z w : ℂ}
    (hz : z ∈ K₁) (hw : w ∈ K₂) :
    crossLenIn ξ f U K₁ K₂ ≤ LQGMetric.LFPP.lfppDOn ξ f U z w :=
  iInf₂_le_of_le z hz (iInf₂_le_of_le w hw le_rfl)

 



theorem aroundDist_lfppMetric_le_of_four (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (A : EuclideanAnnulus) (z w : Fin 4 → ℂ) (hz : ∀ j, z j ∈ Strong.cfgSet₁ A j)
    (hw : ∀ j, w j ∈ Strong.cfgSet₂ A j) (T : ℝ) (hT : 0 ≤ T)
    (hcross : ∀ j, ENNReal.ofReal ((a : ℝ)⁻¹) *
      crossLenIn ξ φ (Strong.cfgOpens A j : Set ℂ) {z j} {w j} ≤ ENNReal.ofReal T) :
    aroundDist (Median.lfppMetric ξ a φ) A ≤ ENNReal.ofReal (4 * T + 1) := by
  have ha : (0 : ℝ) < a := a.2
  have hb : ∀ j, crossLenIn ξ φ (Strong.cfgOpens A j : Set ℂ) (Strong.cfgSet₁ A j)
      (Strong.cfgSet₂ A j) < ENNReal.ofReal ((a : ℝ) * (T + 1 / 8)) := by
    intro j
    have h1 : crossLenIn ξ φ (Strong.cfgOpens A j : Set ℂ) {z j} {w j} ≤
        ENNReal.ofReal ((a : ℝ) * T) := by
      have hmul := mul_le_mul_right (hcross j) (ENNReal.ofReal (a : ℝ))
      rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_mul, ← ENNReal.ofReal_mul ha.le] at hmul
      exact hmul
    have h2 : crossLenIn ξ φ (Strong.cfgOpens A j : Set ℂ) (Strong.cfgSet₁ A j)
        (Strong.cfgSet₂ A j) ≤ crossLenIn ξ φ (Strong.cfgOpens A j : Set ℂ) {z j} {w j} :=
      (crossLenIn_le_lfppDOn (hz j) (hw j)).trans
        (le_iInf₂ fun z' hz' => le_iInf₂ fun w' hw' => by
          rw [Set.mem_singleton_iff] at hz' hw'
          subst hz' hw'
          exact le_rfl)
    refine lt_of_le_of_lt (h2.trans h1) ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith
  have hsum : ENNReal.ofReal ((a : ℝ) * (T + 1 / 8)) + ENNReal.ofReal ((a : ℝ) * (T + 1 / 8)) +
      ENNReal.ofReal ((a : ℝ) * (T + 1 / 8)) + ENNReal.ofReal ((a : ℝ) * (T + 1 / 8)) <
      ENNReal.ofReal ((a : ℝ) * (4 * T + 1)) := by
    have hp : 0 ≤ (a : ℝ) * (T + 1 / 8) := by positivity
    rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by positivity) hp,
      ← ENNReal.ofReal_add (by positivity) hp, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith
  obtain ⟨γ, u, v, hγ, hγA, hdisc, hlen⟩ :=
    DG20Pt.around_loop_of_four_crossLen A ξ φ _ _ _ _ _ (hb 0) (hb 1) (hb 2) (hb 3) hsum
  calc aroundDist (Median.lfppMetric ξ a φ) A ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ γ :=
        aroundDist_lfppMetric_le_lfppLen ξ a φ A hγ hγA hdisc
    _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * ENNReal.ofReal ((a : ℝ) * (4 * T + 1)) :=
        mul_le_mul_of_nonneg_left hlen.le zero_le
    _ = ENNReal.ofReal (4 * T + 1) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), ← mul_assoc, inv_mul_cancel₀ ha.ne',
          one_mul]

 



theorem exists_across_lower_of_field_bound (A : EuclideanAnnulus) :
    ∃ R κ : ℝ, 0 < κ ∧ ∀ (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (M : ℝ),
      (∀ x ∈ closedBall (0 : ℂ) R, |φ x| ≤ M) →
      ENNReal.ofReal ((a : ℝ)⁻¹ * (Real.exp (-(|ξ| * M)) * κ)) ≤
        acrossDist (Median.lfppMetric ξ a φ) A := by
  obtain ⟨d, q, hd, -, hqFin, -, hcover⟩ := PfeAxioms.exists_across_finite_cover A
  obtain ⟨R₀, hR₀⟩ := hqFin.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨R₀ + d, 3 * d / 4 - d / 16, by linarith, ?_⟩
  intro ξ a φ M hφ
  obtain ⟨z, hzq, hbound⟩ :=
    PfeAxioms.exists_finite_cross_below_across A d hd q hcover ξ a φ
  have hball : closedBall z d ⊆ closedBall (0 : ℂ) (R₀ + d) := by
    apply closedBall_subset_closedBall'
    have := mem_closedBall.mp (hR₀ hzq)
    linarith
  have hlow := DG20Pt.dg20_annulus_crossing_lower_of_field_bound ξ φ z (d / 16) (3 * d / 4) d M
    (by linarith) (fun x hx => hφ x (hball hx))
  rw [lfppMetric_eq_normalizedLFPPMetric]
  refine le_trans ?_ hbound
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt a.2))]
  exact mul_le_mul_of_nonneg_left hlow zero_le

 




theorem exists_around_upper_of_field_bound (A : EuclideanAnnulus) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (M : ℝ),
      (∀ x ∈ A.toSet, |φ x| ≤ M) →
      aroundDist (Median.lfppMetric ξ a φ) A ≤
        ENNReal.ofReal ((a : ℝ)⁻¹ * (Real.exp (|ξ| * M) * κ)) := by
  let φ₀ : ℂ → ℝ := fun _ => 0
  let c : Fin 4 → ℝ≥0∞ := fun j => crossLenIn 0 φ₀ (Strong.cfgOpens A j : Set ℂ)
    (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j)
  have hfin : ∀ j : Fin 4, c j ≠ ∞ := by
    intro j
    obtain ⟨-, -, -, -, -, h₁, h₂, hs₁, hs₂, -, hU⟩ := DG20Pt.around_polar_data A j
    obtain ⟨z, hz⟩ := h₁.nonempty
    obtain ⟨w, hw⟩ := h₂.nonempty
    have hne : LQGMetric.LFPP.lfppDOn 0 φ₀ (Strong.cfgOpens A j : Set ℂ) z w ≠ ∞ :=
      DG20Pt.pt_dist_internal_finite_of_open_connected 0 φ₀ continuous_const _
        (Strong.cfgOpens A j).isOpen hU z w (hs₁ hz) (hs₂ hw)
    exact ((crossLenIn_le_lfppDOn hz hw).trans_lt hne.lt_top).ne
  have hlt : ∀ j : Fin 4, c j < c j + 1 := fun j => ENNReal.lt_add_right (hfin j) one_ne_zero
  have hSfin : (c 0 + 1) + (c 1 + 1) + (c 2 + 1) + (c 3 + 1) ≠ ∞ := by
    simp only [ne_eq, ENNReal.add_eq_top, hfin, ENNReal.one_ne_top, or_self, not_false_eq_true]
  obtain ⟨γ, u, v, hγ, hγA, hdisc, hlen⟩ :=
    DG20Pt.around_loop_of_four_crossLen A 0 φ₀ _ _ _ _ _ (hlt 0) (hlt 1) (hlt 2) (hlt 3)
      (ENNReal.lt_add_right hSfin one_ne_zero)
  have hγfin : lfppLen 0 φ₀ γ ≠ ∞ := ne_top_of_lt hlen
  refine ⟨(lfppLen 0 φ₀ γ).toReal + 1, by positivity, ?_⟩
  intro ξ a φ M hφ
  have hcmp : lfppLen ξ φ γ ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppLen ξ φ₀ γ :=
    LQGMetric.DDDF.lfppLen_le_of_abs_sub_le fun t ht => by
      simpa [φ₀] using hφ (γ t) (hγA t ht)
  have hzero : lfppLen ξ φ₀ γ = lfppLen 0 φ₀ γ := by
    simp only [lfppLen, φ₀, mul_zero]
  have hκ : lfppLen 0 φ₀ γ ≤ ENNReal.ofReal ((lfppLen 0 φ₀ γ).toReal + 1) :=
    calc lfppLen 0 φ₀ γ = ENNReal.ofReal (lfppLen 0 φ₀ γ).toReal :=
          (ENNReal.ofReal_toReal hγfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  calc aroundDist (Median.lfppMetric ξ a φ) A ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ γ :=
        aroundDist_lfppMetric_le_lfppLen ξ a φ A hγ hγA hdisc
    _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * (ENNReal.ofReal (Real.exp (|ξ| * M)) *
          ENNReal.ofReal ((lfppLen 0 φ₀ γ).toReal + 1)) := by
        rw [hzero] at hcmp
        exact mul_le_mul_right (hcmp.trans (mul_le_mul_right hκ _)) _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt a.2))]

end SupercriticalLQGUniqueness.B2.Polylog
