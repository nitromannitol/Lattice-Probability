/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedEnergyAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.NormalContraction
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTargetL2
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# The algebra of bounded full-energy functions

The full finite-energy space already has linear operations. The product estimate
below adds the operation needed for the countable regular core, using the existing
`Subalgebra` type. No finite-support closure is introduced.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

theorem gradSq_mul_le {f g : V → ℝ} {A B : ℝ}
    (hf : ∀ x, |f x| ≤ A) (hg : ∀ x, |g x| ≤ B) (p : V × V) :
    G.gradSq (f * g) p ≤
      2 * A ^ 2 * G.gradSq g p + 2 * B ^ 2 * G.gradSq f p := by
  have hf2 : (f p.2) ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hf p.2))).2 (hf p.2)
  have hg1 : (g p.1) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hg p.1))).2 (hg p.1)
  have hsq : (f p.2 * g p.2 - f p.1 * g p.1) ^ 2 ≤
      2 * A ^ 2 * (g p.2 - g p.1) ^ 2 +
        2 * B ^ 2 * (f p.2 - f p.1) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hf2 (sq_nonneg (g p.2 - g p.1))
    have h2 := mul_le_mul_of_nonneg_right hg1 (sq_nonneg (f p.2 - f p.1))
    nlinarith [sq_nonneg (f p.2 * (g p.2 - g p.1) - g p.1 * (f p.2 - f p.1))]
  have hc := mul_le_mul_of_nonneg_left hsq (G.c_nonneg p.1 p.2)
  simpa only [ReflectedWalk.ConductanceGraph.gradSq, Pi.mul_apply] using
    hc.trans_eq (by ring)

/-- Products of bounded full finite-energy functions have full finite energy. -/
theorem hasFiniteEnergy_mul_of_bounded {f g : V → ℝ} {A B : ℝ}
    (hf : ∀ x, |f x| ≤ A) (hg : ∀ x, |g x| ≤ B)
    (hEf : G.HasFiniteEnergy f) (hEg : G.HasFiniteEnergy g) :
    G.HasFiniteEnergy (f * g) :=
  Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg _ p)
    (gradSq_mul_le G hf hg) ((hEg.mul_left (2 * A ^ 2)).add (hEf.mul_left (2 * B ^ 2)))

end ReflectedGMS.FullNetworkForm
