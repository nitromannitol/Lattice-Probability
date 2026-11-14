/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Costs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4LFPPCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Dilate

 

























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness.B2.Polylog

open Uniqueness.Toolkit.CompactPathInfimum (compactPathInf)

 

 
def closedAnn (z : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {w | r₁ ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ r₂}

lemma isCompact_closedAnn (z : ℂ) (r₁ r₂ : ℝ) : IsCompact (closedAnn z r₁ r₂) := by
  refine (isCompact_closedBall z r₂).of_isClosed_subset ?_ fun w hw => by
    rw [mem_closedBall, dist_eq_norm]; exact hw.2
  exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)

 

def acrossIn (D : LSCMetric) (z : ℂ) (r₁ r₂ : ℝ) : ℝ≥0∞ :=
  compactPathInf D (closedAnn z r₁ r₂) (sphere z r₁) (sphere z r₂)

theorem measurable_acrossIn (z : ℂ) (r₁ r₂ : ℝ) :
    Measurable fun D : LSCMetric => acrossIn D z r₁ r₂ :=
  Uniqueness.Toolkit.CompactPathInfimum.compactPathInf_measurable (isCompact_closedAnn z r₁ r₂)
    (isCompact_sphere z r₁) (isCompact_sphere z r₂)

 
def annAt (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) : EuclideanAnnulus :=
  ⟨(z, r₁, r₂), h₁, h₁₂⟩

@[simp] lemma annAt_center (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).center = z := rfl
@[simp] lemma annAt_innerRadius (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).innerRadius = r₁ := rfl
@[simp] lemma annAt_outerRadius (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).outerRadius = r₂ := rfl

 
theorem acrossDist_le_acrossIn (D : LSCMetric) (z : ℂ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₁₂ : r₁ < r₂) : acrossDist D (annAt z r₁ r₂ h₁ h₁₂) ≤ acrossIn D z r₁ r₂ := by
  unfold acrossIn compactPathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun _ => le_iInf fun hE => le_iInf fun hF => ?_
  have hab : a ∈ Icc a b := ⟨le_rfl, hP.1⟩
  have hbb : b ∈ Icc a b := ⟨hP.1, le_rfl⟩
  calc acrossDist D (annAt z r₁ r₂ h₁ h₁₂) ≤ D (P a, P b) :=
        iInf₂_le_of_le (P a) hE (iInf₂_le (P b) hF)
    _ = edist (D.pt (P a)) (D.pt (P b)) := rfl
    _ ≤ D.len P a b := eVariationOn.edist_le (D.pt ∘ P) hab hbb

 
theorem compactPathInf_eq_iInf_internal (D : LSCMetric) (S E F : Set ℂ) :
    compactPathInf D S E F = ⨅ (p : S × S) (_ : (p.1 : ℂ) ∈ E) (_ : (p.2 : ℂ) ∈ F),
      D.internal S p := by
  apply le_antisymm
  · refine le_iInf fun p => le_iInf fun hE => le_iInf fun hF => ?_
    unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPS => le_iInf fun ha => le_iInf fun hb => ?_
    exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPS (iInf_le_of_le (ha ▸ hE) (iInf_le_of_le (hb ▸ hF) le_rfl))))))
  · unfold compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPS => le_iInf fun hE => le_iInf fun hF => ?_
    refine iInf_le_of_le (⟨P a, hPS a ⟨le_rfl, hP.1⟩⟩, ⟨P b, hPS b ⟨hP.1, le_rfl⟩⟩)
      (iInf_le_of_le hE (iInf_le_of_le hF ?_))
    unfold LSCMetric.internal
    exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPS (iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl))))))

 

theorem acrossIn_eq_of_internal_eq {D E : LSCMetric} {Y : Set ℂ} {z : ℂ} {r₁ r₂ : ℝ}
    (hY : closedAnn z r₁ r₂ ⊆ Y) (h : D.internal Y = E.internal Y) :
    acrossIn D z r₁ r₂ = acrossIn E z r₁ r₂ := by
  unfold acrossIn
  rw [compactPathInf_eq_iInf_internal, compactPathInf_eq_iInf_internal,
    Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq D E hY h]

 
theorem acrossIn_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hcTop : c ≠ ∞) (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (z : ℂ) (r₁ r₂ : ℝ) :
    acrossIn E z r₁ r₂ = c * acrossIn D z r₁ r₂ := by
  unfold acrossIn compactPathInf
  simp only [Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

 

lemma image_add_closedAnn (z c : ℂ) (r₁ r₂ : ℝ) :
    (fun x => x + z) '' closedAnn c r₁ r₂ = closedAnn (c + z) r₁ r₂ := by
  ext w
  simp only [mem_image, closedAnn, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [add_sub_add_right_eq_sub]
  · intro hw
    exact ⟨w - z, by rwa [sub_sub, add_comm z c], sub_add_cancel w z⟩

lemma image_add_sphere (z c : ℂ) (ρ : ℝ) : (fun x => x + z) '' sphere c ρ = sphere (c + z) ρ := by
  ext w
  simp only [mem_image, mem_sphere, dist_eq_norm]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [add_sub_add_right_eq_sub]
  · intro hw
    exact ⟨w - z, by rwa [sub_sub, add_comm z c], sub_add_cancel w z⟩

lemma image_smul_sphere {r : ℝ} (hr : 0 < r) (c : ℂ) (ρ : ℝ) :
    (fun x => r • x) '' sphere c ρ = sphere (r • c) (r * ρ) := by
  have hnorm : ∀ x : ℂ, ‖r • x - r • c‖ = r * ‖x - c‖ := fun x => by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  ext w
  simp only [mem_image, mem_sphere, dist_eq_norm]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hnorm, hx]
  · intro hw
    refine ⟨r⁻¹ • w, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    have hw' : ‖w - r • c‖ = r * ‖r⁻¹ • w - c‖ := by
      rw [← hnorm, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hw'] at hw
    exact mul_left_cancel₀ hr.ne' hw

 
end SupercriticalLQGUniqueness.B2.Polylog
