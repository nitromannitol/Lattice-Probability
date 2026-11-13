/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.GFFMod at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFF
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyPoint

/-!
# Bounded boundary data; fields modulo `cℤ`; lateral part

* `exists_isGFFBoundary_of_bounded`: `exists_isGFFBoundary` for bounded harmonic data (the case of
  IG1's piecewise-constant boundary data).
* `φ₀` and `normMod c h`: the normalized
  representative of `h` modulo `cℤ`, `(h, φ₀) ∈ [0,c)`, with `φ₀` a fixed bump of mass one
  (IG4 = arXiv:1302.4738, L1103: "fix φ₀ ∈ C_c^∞ with ∫ φ₀ = 1"; `φ₀ := LQGMetric.refTest`).
  Lemmas, all **exact for every field**: measurability, `normMod c (h + c k) = normMod c h`,
  `(normMod c h, φ₀) ∈ [0,c)`, `normMod c h = h` on the transversal, idempotence; the a.s.
  versions for a whole-plane GFF are kept as corollaries. The whole-plane GFF modulo `rℤ`
  (independent uniform constant, IG4 L1103–1108) is `IsWPGFFMod` in `GFFWP.lean`.
* `lateralPartC h := h − (z ↦ h_{|z|}(0))` (DMS Lemma 4.2–4.4, L1996, L2029, L2187: the
  lateral part of a whole-plane field); junk: the radial function is replaced by `0` when it is
  not locally integrable (mathlib `Distribution.ofFun`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace MatedCRTHarmonic.MoTPort

open LQGMetric GFFBdry

/-! ## Fields modulo `cℤ` -/
/-- the fixed bump `φ₀ ∈ C_c^∞(ℂ)` with `∫ φ₀ = 1` used to normalize fields modulo constants
(IG4 L1103: "fix φ₀ ∈ C_c^∞ with ∫ φ₀ = 1"); it is LQGMetric's reference test function
`refTest` (the standard mollifier supported in `B₁(0)`). -/
def φ₀ : TestC := refTest

lemma integral_φ₀ : ∫ x, φ₀ x = 1 := integral_refTest

/-- the normalized representative of `h` modulo `cℤ`: `h − c⌊(h, φ₀)/c⌋`, so that
`(h, φ₀) ∈ [0,c)` -/
def normMod (c : ℝ) (h : Field) : Field :=
  addConst h (-c * ⌊h φ₀ / c⌋)

namespace NormMod

lemma addConst_addConst (h : Field) (a b : ℝ) :
    addConst (addConst h a) b = addConst h (a + b) := by
  ext φ
  simp only [GFFInv.addConst_apply]
  ring

lemma addConst_zero (h : Field) : addConst h 0 = h := by
  ext φ
  simp only [GFFInv.addConst_apply, mul_zero, add_zero]

lemma addConst_apply_φ₀ (h : Field) (a : ℝ) : addConst h a φ₀ = h φ₀ + a := by
  rw [GFFInv.addConst_apply, integral_φ₀, one_mul]

lemma measurable_addConst_prod : Measurable fun p : Field × ℝ => addConst p.1 p.2 :=
  GFFInv.measurable_distC_iff.2 fun φ => by
    simp only [GFFInv.addConst_apply]
    exact ((measurable_distOn_apply φ).comp measurable_fst).add (measurable_snd.const_mul _)

theorem measurable_normMod (c : ℝ) : Measurable (normMod c) := by
  have hf : Measurable fun h : Field => -c * (⌊h φ₀ / c⌋ : ℝ) :=
    ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      ((measurable_distOn_apply φ₀).div_const c).floor).const_mul _
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [normMod, GFFInv.addConst_apply]
  exact (measurable_distOn_apply φ).add (hf.const_mul _)

/-- adding an integer multiple of `c` does not change the normalized representative
(exact, for every field) -/
theorem normMod_addConst_intMul {c : ℝ} (hc : c ≠ 0) (h : Field) (k : ℤ) :
    normMod c (addConst h (c * k)) = normMod c h := by
  unfold normMod
  rw [addConst_apply_φ₀, addConst_addConst,
    show (h φ₀ + c * k) / c = h φ₀ / c + k by field_simp,
    Int.floor_add_intCast]
  congr 1
  push_cast
  ring

/-- a field already in the transversal `(h, φ₀) ∈ [0,c)` is its own normalized representative -/
theorem normMod_eq_self {c : ℝ} (hc : 0 < c) {h : Field} (hh : h φ₀ ∈ Ico 0 c) :
    normMod c h = h := by
  have : ⌊h φ₀ / c⌋ = 0 := by
    rw [Int.floor_eq_iff]
    refine ⟨by simpa using div_nonneg hh.1 hc.le, ?_⟩
    rw [Int.cast_zero, zero_add, div_lt_one hc]
    exact hh.2
  rw [normMod, this, Int.cast_zero, mul_zero, addConst_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end NormMod

/-! ## Lateral part of a whole-plane field -/

/-- the radial part `z ↦ h_{|z|}(0)` of a field, as a function -/
def radialFun (h : Field) : ℂ → ℝ := fun z => circleAvg h ‖z‖ 0

/-- the lateral part `h − h_{|·|}(0)` (DMS Lemmas 4.2–4.4); the radial part is replaced by the
junk value `0` when `radialFun h` is not locally integrable -/
def lateralPartC (h : Field) : Field := h - ofFunC (radialFun h)

lemma lateralPartC_apply {h : Field} (hr : LocallyIntegrable (radialFun h) volume) (φ : TestC) :
    lateralPartC h φ = h φ - ∫ x, φ x * radialFun h x := by
  show h φ - ofFunC (radialFun h) φ = _
  rw [ofFunC, Distribution.ofFun_apply (hr.locallyIntegrableOn _)]
  rfl

end MatedCRTHarmonic.MoTPort
