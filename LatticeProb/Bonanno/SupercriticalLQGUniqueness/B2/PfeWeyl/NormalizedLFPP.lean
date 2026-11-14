/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPWeyl
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Dilate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq

 




set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
def inverseNormalizer (a : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(a : ℝ)⁻¹, Set.mem_Ioi.mpr (inv_pos.mpr (Set.mem_Ioi.mp a.property))⟩

 
def normalizedLFPPMetric (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) : LSCMetric :=
  B2.LscTop.smulMetric (inverseNormalizer a) (lfppLSCMetric ξ φ)

@[simp] theorem normalizedLFPPMetric_apply (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    normalizedLFPPMetric ξ a φ p =
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p := by
  rw [normalizedLFPPMetric, B2.LscTop.smulMetric_apply,
    lfppLSCMetric_apply]
  rfl

 

theorem normalizedLFPPMetric_toLSCFun (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    (normalizedLFPPMetric ξ a φ).toLSCFun.1 p = rescaledLFPP ξ a φ p := by
  rw [LSCMetric.toLSCFun_apply, normalizedLFPPMetric_apply]
  rfl

 


end SupercriticalLQGUniqueness.B2.PfeWeyl
