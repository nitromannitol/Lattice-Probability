/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Analysis.WeightedGradient at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.DirichletSpace
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Global normalized weighted gradients

The single Hilbert space is `lp (fun _ : V × V => ℝ) 2`. All ordered pairs are
included, with zero conductance giving zero coordinate. No connectedness,
countability, finite support, or boundary assumption is imposed.
-/

set_option autoImplicit false

namespace ReflectedGMS

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- Normalized gradient coordinate on each ordered pair. -/
noncomputable def weightedGradientCoord (f : V → ℝ) (p : V × V) : ℝ :=
  Real.sqrt (G.c p.1 p.2 / 2) * (f p.2 - f p.1)

/-- The normalization gives exactly one half of the ordered-pair energy density. -/
theorem weightedGradientCoord_sq (f : V → ℝ) (p : V × V) :
    weightedGradientCoord G f p ^ 2 = G.gradSq f p / 2 := by
  rw [weightedGradientCoord, mul_pow,
    Real.sq_sqrt (div_nonneg (G.c_nonneg _ _) (by norm_num))]
  simp only [ReflectedWalk.ConductanceGraph.gradSq]
  ring

/-- Every finite-energy scalar function has a square-summable global gradient. -/
theorem weightedGradientCoord_memℓp {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    Memℓp (weightedGradientCoord G f) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    weightedGradientCoord_sq] using hf.div_const 2

/-- The normalized gradient as a genuine vector of the global ordered-pair Hilbert space. -/
noncomputable def weightedGradient (f : V → ℝ) (hf : G.HasFiniteEnergy f) :
    lp (fun _ : V × V => ℝ) 2 :=
  ⟨weightedGradientCoord G f, weightedGradientCoord_memℓp G hf⟩

@[simp] theorem weightedGradient_apply (f : V → ℝ) (hf : G.HasFiniteEnergy f)
    (p : V × V) :
    weightedGradient G f hf p = Real.sqrt (G.c p.1 p.2 / 2) * (f p.2 - f p.1) := rfl

/-- The squared Hilbert norm is half the full ordered-pair energy sum. -/
theorem weightedGradient_norm_sq (f : V → ℝ) (hf : G.HasFiniteEnergy f) :
    ‖weightedGradient G f hf‖ ^ 2 = G.Energy f := by
  have h := lp.norm_rpow_eq_tsum (E := fun _ : V × V => ℝ)
    (p := 2) (by norm_num) (weightedGradient G f hf)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  rw [h]
  change (∑' p, weightedGradientCoord G f p ^ 2) = _
  simp_rw [weightedGradientCoord_sq]
  exact tsum_div_const

end ReflectedGMS
