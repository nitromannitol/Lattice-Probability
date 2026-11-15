import LatticeProb.Analysis.WedgeArcSineUniqueness
import LatticeProb.Analysis.WedgeSineOrthogonality
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Sine modes in the Hilbert space of a circular arc -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal ComplexConjugate

namespace LatticeProb

/-- Surface measure restricted to the symmetric arc of opening `θ`. -/
noncomputable def wedgeArcSurfaceMeasure (θ : ℝ) : Measure (sphere (0 : ℂ) 1) :=
  (volume : Measure ℂ).toSphere.restrict
    {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)}

instance (θ : ℝ) : IsFiniteMeasure (wedgeArcSurfaceMeasure θ) := by
  unfold wedgeArcSurfaceMeasure
  infer_instance

/-- The normalized positive angular sine modes. -/
noncomputable def wedgeArcSineMode (θ : ℝ) (n : ℕ) (z : sphere (0 : ℂ) 1) : ℂ :=
  (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ (n + 1) z.val.arg : ℝ)

theorem wedgeArcSineMode_memLp (θ : ℝ) (n : ℕ) :
    MemLp (wedgeArcSineMode θ n) 2 (wedgeArcSurfaceMeasure θ) := by
  have hm : Measurable (wedgeArcSineMode θ n) := by
    unfold wedgeArcSineMode LQGMetric.HeatSq.sinMode
    fun_prop (disch := exact Complex.measurable_arg)
  apply MemLp.of_bound hm.aestronglyMeasurable |Real.sqrt (2 / θ)|
  filter_upwards [] with z
  simp only [wedgeArcSineMode, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    |Real.sqrt (2 / θ)| * |LQGMetric.HeatSq.sinMode (-θ / 2) θ (n + 1) z.val.arg|
        ≤ |Real.sqrt (2 / θ)| * 1 := by
          gcongr
          exact Real.abs_sin_le_one _
    _ = _ := mul_one _

/-- The positive sine mode as an element of the complex L² space. -/
noncomputable def wedgeArcSineLp (θ : ℝ) (n : ℕ) :
    Lp ℂ 2 (wedgeArcSurfaceMeasure θ) :=
  (wedgeArcSineMode_memLp θ n).toLp (wedgeArcSineMode θ n)

/-- The positive normalized modes are orthonormal. -/
theorem orthonormal_wedgeArcSineLp {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    Orthonormal ℂ (wedgeArcSineLp θ) := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [MeasureTheory.L2.inner_def]
  have heq : (fun z => inner ℂ (wedgeArcSineLp θ j z) (wedgeArcSineLp θ k z)) =ᵐ[wedgeArcSurfaceMeasure θ]
      (fun z : sphere (0 : ℂ) 1 => (((Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ (j + 1) z.val.arg) *
        (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ (k + 1) z.val.arg) : ℝ) : ℂ)) := by
    filter_upwards [(wedgeArcSineMode_memLp θ j).coeFn_toLp,
      (wedgeArcSineMode_memLp θ k).coeFn_toLp] with z hj hk
    change wedgeArcSineLp θ j z = _ at hj
    change wedgeArcSineLp θ k z = _ at hk
    rw [hj, hk]
    simp [wedgeArcSineMode, RCLike.inner_apply, ← Complex.ofReal_mul, mul_comm]
  rw [integral_congr_ae heq, integral_complex_ofReal]
  rw [show (∫ z : sphere (0 : ℂ) 1,
    (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ (j + 1) z.val.arg) *
    (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ (k + 1) z.val.arg)
    ∂(wedgeArcSurfaceMeasure θ)) = if j + 1 = k + 1 then 1 else 0 from
      integral_sinMode_mul_sinMode_toSphere hθ hθ' (by omega)]
  split_ifs <;> simp_all

end LatticeProb
