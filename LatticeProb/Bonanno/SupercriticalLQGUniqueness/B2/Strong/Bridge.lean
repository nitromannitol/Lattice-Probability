/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.Bridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsWeakLQGMetric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6B

 









set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC TestC ofCont addFun addConst IsGFFPlusCont affineComp)

namespace SupercriticalLQGUniqueness.B2.Strong

theorem testDilate_eq_testAffinePull (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    testDilate r z = LQGMetric.testAffinePull (r : ℝ) z := by
  ext φ x
  rw [LQGMetric.testAffinePull_apply _ _ (ne_of_gt r.2)]
  show φ (LQGMetric.affMap (r : ℝ) z x) = _
  congr 1
  simp [LQGMetric.affMap, div_eq_inv_mul, sub_eq_add_neg, Complex.real_smul]
  ring

 
theorem scaleTranslateDist_eq_affineComp (r : Set.Ioi (0 : ℝ)) (z : ℂ) (h : DistC) :
    scaleTranslateDist r z h = affineComp (r : ℝ) z h := by
  show ((r : ℝ) ^ 2)⁻¹ • h.comp (testDilate r z) = _
  rw [testDilate_eq_testAffinePull]
  rfl

 
theorem scaleTranslateDist_one (z : ℂ) (h : DistC) :
    scaleTranslateDist ⟨1, Set.mem_Ioi.mpr one_pos⟩ z h = translateDist z h := by
  rw [scaleTranslateDist_eq_affineComp, translateDist_eq_affineComp_one]

theorem addConst_zero (g : DistC) : addConst g 0 = g := by
  show g + ofCont (ContinuousMap.const ℂ (0 : ℝ)) = g
  have : ofCont (ContinuousMap.const ℂ (0 : ℝ)) = 0 := by ext φ; simp [LQGMetric.ofCont]
  rw [this, add_zero]

theorem addFun_addConst_const (g : DistC) (a b : ℝ) :
    addFun (addConst g a) (ContinuousMap.const ℂ b) = addConst g (a + b) := by
  show addFun (addFun g (ContinuousMap.const ℂ a)) (ContinuousMap.const ℂ b) =
    addFun g (ContinuousMap.const ℂ (a + b))
  rw [LQGMetric.DFGPS.T12.addFun_addFun']
  congr 1

 
theorem translation_of_strong {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hS : IsStrongLQGMetric ξ Q D) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (D (translateDist z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z) := by
  intro Ω _ P _ h hh z
  filter_upwards [hS.2.2.2.2.1 P h hh ⟨1, Set.mem_Ioi.mpr one_pos⟩ z] with ω hω u v
  have := hω u v
  simp only [one_smul, Real.log_one, mul_zero, addConst_zero, scaleTranslateDist_one] at this
  exact this.symm

end SupercriticalLQGUniqueness.B2.Strong
