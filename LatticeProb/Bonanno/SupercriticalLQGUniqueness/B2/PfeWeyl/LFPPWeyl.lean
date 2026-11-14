/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPWeyl at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.LFPP
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField

 





set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem isExtMetric_lfppDistance (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    IsExtMetric (lfppDistance ξ φ) := by
  constructor
  · intro z
    rw [B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_self convex_univ (Set.mem_univ z)
  constructor
  · intro z w hzw
    apply LQGMetric.LFPP.lfppDReal_eq_zero φ.continuous
    unfold LQGMetric.LFPP.lfppDReal
    rw [← B2.LscTop.lfppDistance_eq_lfppD, hzw]
    rfl
  constructor
  · intro z w
    rw [B2.LscTop.lfppDistance_eq_lfppD,
      B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_comm z w
  · intro x y z
    rw [B2.LscTop.lfppDistance_eq_lfppD,
      B2.LscTop.lfppDistance_eq_lfppD,
      B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_triangle x y z

 


def lfppLSCMetric (ξ : ℝ) (φ : C(ℂ, ℝ)) : LSCMetric :=
  ⟨lfppDistance ξ φ,
    isExtMetric_lfppDistance ξ φ,
    (B2.LscTop.continuous_lfppDistance ξ φ).lowerSemicontinuous⟩

@[simp] theorem lfppLSCMetric_apply (ξ : ℝ) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppLSCMetric ξ φ p = lfppDistance ξ φ p := rfl

 
end SupercriticalLQGUniqueness.B2.PfeWeyl
