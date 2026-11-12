/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareCK2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK1
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
`HeatSq.integral_sqDirKernel_mul`: on `D = (a, a+L)²`,
`∫_D p^D_s(x, y') p^D_r(y', y) dy' = p^D_{s+r}(x, y)` for `s, r > 0` — the semigroup property
of the killed heat kernel used in DDDF's covariance computation for `η_t`
(`tightness.tex:1517–1523`), here for the product image kernel `sqDirKernel` (D19,
D-DDDF-11). Proof: Fubini (`integral_prod_mul` through `Complex.measurableEquivRealProd`)
and the one-dimensional identity `integral_intervalDirKernel_mul`.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace HeatSq

/-- The open square `(a, a+L)²`; DFGPS/DDDF use `a = −1`, `L = 3`. -/
def sqOpen (a L : ℝ) : Set ℂ := {z | a < z.re ∧ z.re < a + L ∧ a < z.im ∧ z.im < a + L}

lemma sqOpen_eq_preimage (a L : ℝ) :
    sqOpen a L = Complex.measurableEquivRealProd ⁻¹' (Ioo a (a + L) ×ˢ Ioo a (a + L)) := by
  ext z; simp [sqOpen, and_assoc]

lemma measurableSet_sqOpen (a L : ℝ) : MeasurableSet (sqOpen a L) := by
  rw [sqOpen_eq_preimage]
  exact Complex.measurableEquivRealProd.measurable (measurableSet_Ioo.prod measurableSet_Ioo)

/-- Integrals of products of functions of `re` and `im` over the square factorize. -/
lemma integral_sqOpen_re_mul_im (a L : ℝ) (F G : ℝ → ℝ) :
    ∫ z in sqOpen a L, F z.re * G z.im =
      (∫ t in Ioo a (a + L), F t) * ∫ t in Ioo a (a + L), G t := by
  rw [sqOpen_eq_preimage]
  have := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => F p.1 * G p.2)
    (Ioo a (a + L) ×ˢ Ioo a (a + L))
  simp only [Complex.measurableEquivRealProd_apply] at this
  rw [this, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_mul]

/-- **Chapman–Kolmogorov for the square kernel**. -/
theorem integral_sqDirKernel_mul {a L s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hL : 0 < L)
    (x y : ℂ) :
    ∫ y' in sqOpen a L, sqDirKernel a L s x y' * sqDirKernel a L r y' y =
      sqDirKernel a L (s + r) x y := by
  have e : (fun y' : ℂ => sqDirKernel a L s x y' * sqDirKernel a L r y' y) =
      fun y' => (intervalDirKernel a L s x.re y'.re * intervalDirKernel a L r y'.re y.re) *
        (intervalDirKernel a L s x.im y'.im * intervalDirKernel a L r y'.im y.im) := by
    funext y'; unfold sqDirKernel; ring
  rw [e, integral_sqOpen_re_mul_im a L (fun t => intervalDirKernel a L s x.re t *
      intervalDirKernel a L r t y.re) (fun t => intervalDirKernel a L s x.im t *
      intervalDirKernel a L r t y.im), ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, integral_intervalDirKernel_mul hs hr hL,
    integral_intervalDirKernel_mul hs hr hL]
  rfl

end HeatSq
end LQGMetric
