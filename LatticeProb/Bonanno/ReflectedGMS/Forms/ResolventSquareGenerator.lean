/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventSquareGenerator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyCarreDuChamp
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale

/-!
# Weak square-generator identity for a vertex occupation potential

This file combines the full-domain resolvent variational identity with the
full-energy carré-du-champ product identity.  The result is purely analytic:
it does not identify a stochastic bracket or exclude compactification-boundary
terms.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace

namespace ReflectedGMS

open FullNetworkForm

variable {V : Type*}

theorem inner_weightedValue_eq_tsum
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (f g : V → ℝ)
    (hf : HasSpeedL2 m f) (hg : HasSpeedL2 m g) :
    ⟪weightedValue m f hf, weightedValue m g hg⟫_ℝ =
      ∑' x : V, m x * f x * g x := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  simp only [Real.inner_apply, weightedValue_apply]
  have hsqrt : Real.sqrt (m x) * Real.sqrt (m x) = m x :=
    Real.mul_self_sqrt (hm x).le
  rw [show Real.sqrt (m x) * f x * (Real.sqrt (m x) * g x) =
      (Real.sqrt (m x) * Real.sqrt (m x)) * f x * g x by ring,
    hsqrt]

private theorem summable_speed_mul_mul
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (f g : V → ℝ)
    (hf : HasSpeedL2 m f) (hg : HasSpeedL2 m g) :
    Summable (fun x : V ↦ m x * f x * g x) := by
  have hs := lp.summable_inner (𝕜 := ℝ) (G := fun _ : V => ℝ)
    (weightedValue m f hf) (weightedValue m g hg)
  refine hs.congr (fun x ↦ ?_)
  simp only [Real.inner_apply, weightedValue_apply]
  have hsqrt : Real.sqrt (m x) * Real.sqrt (m x) = m x :=
    Real.mul_self_sqrt (hm x).le
  rw [show Real.sqrt (m x) * f x * (Real.sqrt (m x) * g x) =
      (Real.sqrt (m x) * Real.sqrt (m x)) * f x * g x by ring,
    hsqrt]

private theorem vertexOccupationPotential_eq_scaled_parameterized
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (y : V) :
    (vertexOccupationPotential G m alpha · y) =
      (1 / alpha) • parameterizedResolventFunction G m (1 / alpha)
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) := by
  funext x
  rw [← unweight_vertexOccupationPotentialValue G m ha x y]
  unfold vertexOccupationPotentialValue parameterizedResolventFunction unweight
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

end ReflectedGMS
