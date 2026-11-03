/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeyl2Mv at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl2Fam
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Weakly harmonic distributions: the mollified function is harmonic (task P2-MKH, leaf (H))

For `T ∈ 𝒟'(V)` with `T(−Δf/2π) = 0` for all `f ∈ C_c^∞(V)`, `weylFun T z = T(rbump s (· − z))`
is harmonic on `V` (`harmonicOnNhd_weylFun`). Proof (mean value form of Weyl's lemma): near
`z₀` it is a continuous function (`transFam`), and its circle average over `∂B(z, s)` is `T`
applied to the circle average of the translated mollifiers, a radial test function of mass `1`
around `z`; by `pair_eq_of_radial` this is `T(rbump δ (· − z))`. Then QuantumZipper
`K3.harmonicOnNhd_of_meanValue`. Source: Hörmander, *ALPDO I*, Thm 4.4.1 (mollification) and
the mean value characterization of harmonic functions (e.g. Evans, *PDE*, §2.2.3, Thm 3).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped Real Distributions

namespace LQGMetric
namespace MarkovWeyl2

/-- the radial projection onto `B̄(z₀, δ)` -/
def projB (z₀ : ℂ) (δ : ℝ) (z : ℂ) : ℂ := z₀ + (z - z₀) / ((max 1 (‖z - z₀‖ / δ) : ℝ) : ℂ)

lemma max_projB_pos (z₀ : ℂ) (δ : ℝ) (z : ℂ) : 0 < max 1 (‖z - z₀‖ / δ) :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

lemma continuous_projB (z₀ : ℂ) (δ : ℝ) : Continuous (projB z₀ δ) := by
  refine continuous_const.add ((continuous_id.sub continuous_const).div
    (Complex.continuous_ofReal.comp (continuous_const.max
      ((continuous_id.sub continuous_const).norm.div_const δ))) fun z => ?_)
  exact_mod_cast (max_projB_pos z₀ δ z).ne'

lemma norm_projB_sub_le {δ : ℝ} (hδ : 0 < δ) (z₀ z : ℂ) : ‖projB z₀ δ z - z₀‖ ≤ δ := by
  rw [projB, add_sub_cancel_left, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (max_projB_pos z₀ δ z), div_le_iff₀ (max_projB_pos z₀ δ z)]
  calc ‖z - z₀‖ = δ * (‖z - z₀‖ / δ) := by field_simp
    _ ≤ δ * max 1 (‖z - z₀‖ / δ) := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le

lemma projB_eq {δ : ℝ} (hδ : 0 < δ) {z₀ z : ℂ} (hz : ‖z - z₀‖ ≤ δ) : projB z₀ δ z = z := by
  have : max 1 (‖z - z₀‖ / δ) = 1 := max_eq_left ((div_le_one hδ).2 hz)
  rw [projB, this]; simp

/-- the compact `B̄(z₀, 2δ)` -/
def ballK2 (z₀ : ℂ) (δ : ℝ) : Compacts ℂ := ⟨closedBall z₀ (2 * δ), isCompact_closedBall _ _⟩

lemma closedBall_sub_ballK2 {δ : ℝ} {z₀ q : ℂ} (hq : ‖q - z₀‖ ≤ δ) :
    closedBall q δ ⊆ (ballK2 z₀ δ : Set ℂ) := by
  intro y hy
  show y ∈ closedBall z₀ (2 * δ)
  rw [mem_closedBall, dist_eq_norm] at hy ⊢
  calc ‖y - z₀‖ = ‖(y - q) + (q - z₀)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖y - q‖ + ‖q - z₀‖ := norm_add_le _ _
    _ ≤ 2 * δ := by linarith

variable {V : Opens ℂ} (T : DistOn V)
  (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0)
  {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) (hB : closedBall z₀ (4 * δ) ⊆ V)

include hδ hB in
lemma ballK2_sub : (ballK2 z₀ δ : Set ℂ) ⊆ V :=
  (closedBall_subset_closedBall (by linarith)).trans hB

/-- the translation family `z ↦ rbump δ (· − proj z)` in `𝓓_{B̄(z₀, 2δ)}` -/
def projFam (z : ℂ) : 𝓓^{⊤}_{ballK2 z₀ δ}(ℂ, ℝ) :=
  transFam (contDiff_rbump δ) (fun y hy => rbump_eq_zero hδ.le hy)
    (q := projB z₀ δ) (fun z => closedBall_sub_ballK2 (norm_projB_sub_le hδ z₀ z)) z

/-- the localized candidate `u(z) = T(rbump δ (· − proj z))`, continuous on `ℂ` -/
def uLoc (z : ℂ) : ℝ :=
  (T.comp (TestFunction.ofSupportedInCLM ℝ (ballK2_sub hδ hB))) (projFam hδ z)

lemma continuous_uLoc : Continuous (uLoc T hδ hB) :=
  (T.comp (TestFunction.ofSupportedInCLM ℝ (ballK2_sub hδ hB))).continuous.comp
    (continuous_transFam (contDiff_rbump δ) (fun y hy => rbump_eq_zero hδ.le hy)
      (fun z => closedBall_sub_ballK2 (norm_projB_sub_le hδ z₀ z)) (continuous_projB z₀ δ))

include hT in
lemma uLoc_eq_weylFun {z : ℂ} (hz : ‖z - z₀‖ ≤ δ) : uLoc T hδ hB z = weylFun T z := by
  have hzV : closedBall z δ ⊆ V := (closedBall_sub_ballK2 hz).trans (ballK2_sub hδ hB)
  rw [weylFun_eq T hT hδ hzV]
  show T (TestFunction.ofSupportedIn (ballK2_sub hδ hB) (projFam hδ z)) = _
  congr 1
  refine TestFunction.ext fun x => ?_
  show rbump δ (x - projB z₀ δ z) = rbump δ (x - z)
  rw [projB_eq hδ hz]

include hT in
/-- **Mean value property** of the localized candidate on `B(z₀, δ)`. -/
theorem meanValue_uLoc : QuantumZipper.K3.MeanValueOn (uLoc T hδ hB) (ball z₀ δ) := by
  intro z hz s hs hzs
  have hz' : ‖z - z₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hz
  have hcm : ∀ θ, ‖circleMap z s θ - z₀‖ < δ := fun θ => by
    have : circleMap z s θ ∈ ball z₀ δ := hzs (by
      rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hs])
    rwa [mem_ball, dist_eq_norm] at this
  have hs2 : s < 2 * δ := by
    have e : ‖circleMap z s 0 - z‖ = s := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hs]
    have := norm_sub_le_norm_sub_add_norm_sub (circleMap z s 0) z₀ z
    rw [norm_sub_rev z₀ z] at this
    linarith [hcm 0]
  have hV' : closedBall z (δ + s) ⊆ V := by
    refine Subset.trans ?_ hB
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    calc ‖y - z₀‖ = ‖(y - z) + (z - z₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - z‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ 4 * δ := by linarith
  have hzV : closedBall z δ ⊆ V :=
    (closedBall_subset_closedBall (by linarith)).trans hV'
  set Fc := transFam (K := ballK2 z₀ δ) (contDiff_rbump δ) (fun y hy => rbump_eq_zero hδ.le hy)
    (q := circleMap z s) (fun θ => closedBall_sub_ballK2 (hcm θ).le) with hFc
  obtain ⟨I, hI, hTI⟩ := TestIntegral.exists_testIntegral (F := Fc) 0 (2 * π)
    (continuous_transFam _ _ _ (continuous_circleMap z s))
  set T' := T.comp (TestFunction.ofSupportedInCLM ℝ (ballK2_sub hδ hB)) with hT'
  have hu : ∀ θ, uLoc T hδ hB (circleMap z s θ) = T' (Fc θ) := by
    intro θ
    show T' (projFam hδ _) = T' (Fc θ)
    congr 1
    refine ContDiffMapSupportedIn.ext fun y => ?_
    show rbump δ (y - projB z₀ δ (circleMap z s θ)) = rbump δ (y - circleMap z s θ)
    rw [projB_eq hδ (hcm θ).le]
  rw [QuantumZipper.CoordReg.integral_circleUnif_eq_circleAverage
    (continuous_uLoc T hδ hB).measurable, Real.circleAverage_def, smul_eq_mul]
  simp_rw [hu]
  rw [← hTI T', uLoc_eq_weylFun T hT hδ hB hz'.le, weylFun_eq T hT hδ hzV]
  have hcz : ∀ w θ, w + z - circleMap z s θ = w - circleMap 0 s θ := by
    intro w θ; simp only [circleMap, zero_add]; ring
  have hIw : ∀ w, I (w + z) = ∫ θ in (0 : ℝ)..2 * π, rbump δ (w - circleMap 0 s θ) := by
    intro w
    rw [hI]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hFc, transFam_apply, hcz]
  have hI1 : ∫ y, I y = 2 * π := by
    have h1 := hTI ((ofCont (ContinuousMap.const ℂ 1)).comp
      (TestFunction.ofSupportedInCLM ℝ (subset_univ _)))
    change ofCont _ (TestFunction.ofSupportedIn (subset_univ (ballK2 z₀ δ : Set ℂ)) I) =
      ∫ θ in (0 : ℝ)..2 * π,
        ofCont _ (TestFunction.ofSupportedIn (subset_univ (ballK2 z₀ δ : Set ℂ)) (Fc θ)) at h1
    have h2 : ∀ θ, ofCont (ContinuousMap.const ℂ 1)
        (TestFunction.ofSupportedIn (subset_univ (ballK2 z₀ δ : Set ℂ)) (Fc θ)) = 1 := by
      intro θ
      rw [ofCont_apply]
      show ∫ x, rbump δ (x - circleMap z s θ) * 1 = 1
      simp only [mul_one]
      rw [integral_sub_right_eq_self (fun x => rbump δ x), integral_rbump hδ]
    simp only [h2, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, ofCont_apply,
      ContinuousMap.const_apply] at h1
    exact h1
  show (2 * π)⁻¹ * T (TestFunction.ofSupportedIn (ballK2_sub hδ hB) I) = _
  rw [← smul_eq_mul, ← map_smul]
  refine pair_eq_of_radial T hT (ρ₁ := fun y => (2 * π)⁻¹ * I (y + z)) (ρ₂ := rbump δ)
    (contDiff_const.mul (I.contDiff.comp (contDiff_id.add contDiff_const))) (contDiff_rbump δ) ?_
    (isRad_rbump δ) (r := δ + s) ?_ (fun y hy => rbump_eq_zero hδ.le (by linarith)) ?_ hV'
    (fun x => ?_)
    (fun x => rfl)
  · intro a y
    simp only [hIw, integral_rbump_circle_rot]
  · intro y hy
    show (2 * π)⁻¹ * I (y + z) = 0
    rw [hIw, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ _ =>
      rbump_eq_zero hδ.le ?_]
    · simp
    · have h3 := norm_sub_norm_le y (circleMap 0 s θ)
      rw [norm_circleMap_zero, abs_of_pos hs] at h3
      linarith
  · rw [integral_const_mul, integral_add_right_eq_self (fun y => I y) z, hI1, integral_rbump hδ]
    field_simp
  · show (2 * π)⁻¹ * I x = (2 * π)⁻¹ * I (x - z + z)
    rw [sub_add_cancel]

include hT in
theorem harmonicOnNhd_uLoc : HarmonicOnNhd (uLoc T hδ hB) (ball z₀ δ) :=
  QuantumZipper.K3.harmonicOnNhd_of_meanValue (continuous_uLoc T hδ hB) isOpen_ball
    (meanValue_uLoc T hT hδ hB)

omit hδ hB in
include hT in
/-- **Weyl's lemma, harmonicity.** The mollified function `weylFun T` is harmonic on `V`. -/
theorem harmonicOnNhd_weylFun : HarmonicOnNhd (weylFun T) V := by
  intro z₀ hz₀
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 V.isOpen z₀ hz₀
  have hδ : 0 < ε / 8 := by positivity
  have hB : closedBall z₀ (4 * (ε / 8)) ⊆ V := (closedBall_subset_ball (by linarith)).trans hεV
  have h := harmonicOnNhd_uLoc T hT hδ hB z₀ (mem_ball_self hδ)
  refine (harmonicAt_congr_nhds ?_).1 h
  filter_upwards [ball_mem_nhds z₀ hδ] with z hz
  exact uLoc_eq_weylFun T hT hδ hB (by rw [mem_ball, dist_eq_norm] at hz; exact hz.le)

end MarkovWeyl2
end LQGMetric
