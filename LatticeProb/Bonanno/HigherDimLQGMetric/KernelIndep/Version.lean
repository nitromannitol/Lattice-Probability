/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.Version at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Basic
import LatticeProb.Bonanno.HigherDimLFPP.Field.Version

/-!
# Continuous versions of white-noise vector families

Port of `HigherDimLFPP.exists_isBandVersion`; the Kolmogorov argument uses only a quadratic
increment bound, not the special form of a band vector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN IsWhiteNoise)

/-- A vector family with quadratic increments has a continuous measurable white-noise version. -/
theorem exists_contVersion {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) (v : Rd d → WN d)
    {L a : ℝ} (ha : 0 < a)
    (hv : ∀ z w, ‖v z - v w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2) :
    ∃ X : Rd d → Ω → ℝ, (∀ ω, Continuous fun z => X z ω) ∧
      (∀ z, Measurable (X z)) ∧ ∀ z, X z =ᵐ[P] W (v z) := by
  set Z : (Fin d → ℝ) → Ω → ℝ := fun q => W (v (WithLp.toLp 2 q)) with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q => hW.measurable _
  set c : ℝ := max L 0 * d / a ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set M : ℝ := QuantumZipper.gaussianAbsMoment (2 * (d + 1)) with hM
  have hM0 : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * (d + 1)) ((2 * (d + 1) : ℕ) : ℝ) K R := by
    intro R
    refine ⟨c ^ (d + 1) * M, by positivity, fun q _ q' _ => ?_⟩
    have hlaw := hW.hasLaw_sub (v (WithLp.toLp 2 q)) (v (WithLp.toLp 2 q'))
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hW.measurable _).sub (hW.measurable _)) (d + 1) hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [hZ]
    rw [hE]
    refine ENNReal.ofReal_le_ofReal ?_
    set x : ℝ := ‖v (WithLp.toLp 2 q) - v (WithLp.toLp 2 q')‖ ^ 2 with hx
    have hx0 : 0 ≤ x := sq_nonneg _
    have hxc : x ≤ c * ‖q - q'‖ ^ 2 := by
      have h1 := hv (WithLp.toLp 2 q) (WithLp.toLp 2 q')
      rw [← WithLp.toLp_sub] at h1
      have h2 := HigherDimLFPP.norm_toLp_sq_le_dim_mul (q - q')
      calc x ≤ L * ‖(WithLp.toLp 2 (q - q') : Rd d)‖ ^ 2 / a ^ 2 := h1
        _ ≤ (max L 0) * ‖(WithLp.toLp 2 (q - q') : Rd d)‖ ^ 2 / a ^ 2 := by gcongr; exact le_max_left _ _
        _ ≤ (max L 0) * (d * ‖q - q'‖ ^ 2) / a ^ 2 := by gcongr
        _ = c * ‖q - q'‖ ^ 2 := by rw [hc]; ring
    have hcoe : ((x.toNNReal : NNReal) : ℝ) = x := Real.coe_toNNReal _ hx0
    rw [hcoe, Real.rpow_natCast]
    calc x ^ (d + 1) * M ≤ (c * ‖q - q'‖ ^ 2) ^ (d + 1) * M := by gcongr
      _ = c ^ (d + 1) * M * ‖q - q'‖ ^ (2 * (d + 1)) := by ring
  have hpos : (d : ℝ) < ((2 * (d + 1) : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := Z) hZm (p := 2 * (d + 1)) (by omega) hpos hmom
  refine ⟨fun z ω => Y (WithLp.ofLp z) ω, fun ω => ?_, fun z => hYm _, fun z => ?_⟩
  · exact (hYc ω).comp (PiLp.continuous_ofLp 2 _)
  · have h := hYZ (WithLp.ofLp z)
    simp only [hZ, WithLp.toLp_ofLp] at h
    exact h

end HigherDimLQGMetric
