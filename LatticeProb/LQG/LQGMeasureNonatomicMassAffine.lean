import Mathlib
import LatticeProb.LQG.LQGMeasureInputs

/-!
# The whole-plane GFF and its LQG measure under a complex affine map

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Fact 2.1 III and IV. For `a ∈ ℂ ∖ {0}` and `b ∈ ℂ`, the field
`h^ℂ(a · + b) - h^ℂ_{|a|}(b)` is a whole-plane GFF (`wholePlaneGFFAffineInvariance_lp`, module `LatticeProb.Gauss.GFFAffineInvariance`).
Its LQG measure is `e^{-γ (h^ℂ_{|a|}(b) + Q log |a|)} μ₀((· - b)/a)⁻¹` (the coordinate change of Duplantier-Sheffield 2011,
Prop. 2.1, and Sheffield-Wang 2016, Theorem 1.1, as the literature hypothesis `LQGMeasureCoordChangeLP` at `α₀ = 0`;
the additive constant of `IsLQGLimit`), and on balls it reads `e^{-γ (h^ℂ_{|a|}(b) + Q log |a|)} μ₀(B_{|a| r}(a w + b))`.
These are the rescalings of Fact 2.1 IV used for Lemma 2.4 of Bou-Rabee-Gwynne.

The only literature input is `LQGMeasureCoordChangeLP` (module `LatticeProb.LQG.LQGMeasureInputs`), used as a hypothesis.
-/

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory Metric Filter Set Topology LatticeProb.Gauss LatticeProb.LQG
open scoped ENNReal

/-- Adding a constant `c` to the circle averages multiplies the LQG limit by `e^{γc}`. -/
theorem isLQGLimit_add_const {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ} (h : IsLQGLimit γ hε m) (c : ℝ) :
    IsLQGLimit γ (fun ε z => hε ε z + c) (ENNReal.ofReal (Real.exp (γ * c)) • m) := by
  have hm := h.isLocallyFiniteMeasure
  have happrox : ∀ ε, lqgApprox γ (fun ε z => hε ε z + c) ε =
      ENNReal.ofReal (Real.exp (γ * c)) • lqgApprox γ hε ε := by
    intro ε
    simp only [lqgApprox]
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
    ring_nf
  refine ⟨⟨fun x => ?_⟩, fun f hf hfc => ?_⟩
  · obtain ⟨U, hU, hfin⟩ := hm.finiteAtNhds x
    exact ⟨U, hU, by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩
  · simp only [happrox, integral_smul_measure]
    exact (h.tendsto_integral f hf hfc).const_smul _

/-- The image of a ball under `x ↦ (x - b)/a`: `((x - b)/a)⁻¹' B_r(w) = B_{|a| r}(a w + b)`. -/
theorem map_affine_ball (m : Measure ℂ) {a : ℂ} (ha : a ≠ 0) (b w : ℂ) (r : ℝ) :
    (m.map fun x => (x - b) / a) (ball w r) = m (ball (a * w + b) (‖a‖ * r)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_ball]
  congr 1
  ext x
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [show (x - b) / a - w = (x - (a * w + b)) / a by field_simp; ring, norm_div,
    div_lt_iff₀ hna, mul_comm r ‖a‖]

variable {Ω : Type*}

/-- Circle averages of `h^ℂ(a · + b) - h^ℂ_{|a|}(b)` (the output of `wholePlaneGFFAffineInvariance_lp`). -/
noncomputable def affineCircle (hcirc : Ω → ℝ → ℂ → ℝ) (a b : ℂ) : Ω → ℝ → ℂ → ℝ :=
  fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b

/-- Pairings of `h^ℂ(a · + b) - h^ℂ_{|a|}(b)` (the output of `wholePlaneGFFAffineInvariance_lp`). -/
noncomputable def affinePairing (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (a b : ℂ) :
    Ω → (ℂ → ℝ) → ℝ :=
  fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x

/-- The candidate LQG measure of `h^ℂ(a · + b) - h^ℂ_{|a|}(b)`:
`e^{-γ (h^ℂ_{|a|}(b) + Q log |a|)} μ₀((· - b)/a)⁻¹`. -/
noncomputable def affineMeasure (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ) (a b : ℂ) :
    Ω → Measure ℂ :=
  fun ω => ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)))) •
    (μ₀ ω).map fun x => (x - b) / a

theorem affineMeasure_ball (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ) {a : ℂ} (ha : a ≠ 0)
    (b : ℂ) (ω : Ω) (w : ℂ) (r : ℝ) :
    affineMeasure γ hcirc μ₀ a b ω (ball w r) =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)))) *
        μ₀ ω (ball (a * w + b) (‖a‖ * r)) := by
  rw [affineMeasure, Measure.smul_apply, smul_eq_mul, map_affine_ball _ ha]

/-- `fieldCircleAverage 0` is the identity. -/
theorem fieldCircleAverage_zero_lp (hcirc : ℝ → ℂ → ℝ) : fieldCircleAverage 0 hcirc = hcirc := by
  funext r z; simp [fieldCircleAverage]

/-- The LQG measure of the affine image of the field (`α₀ = 0`), from the literature input `LQGMeasureCoordChangeLP`. -/
theorem isLQGMeasureOfField_affine [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ₀ : Ω → Measure ℂ} (hCC : LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsLQGMeasureOfField P γ 0 (affineCircle hcirc a b) (affineMeasure γ hcirc μ₀ a b) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [hCC hGFF hγ hγ2 hQ μ₀ hμ₀] with ω hω
  have h := (isLQGLimit_add_const (hω a ha b) (-(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)))
  rw [fieldCircleAverage_zero_lp] at h ⊢
  have heq : (fun ε z => hcirc ω (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖ +
      -(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)) = affineCircle hcirc a b ω := by
    funext ε z; simp only [affineCircle]; ring
  rw [heq] at h
  exact h

end LatticeProb.LQG.LQGMeasureNonatomicMass
