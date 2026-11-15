import LatticeProb.Prob.CorrelatedBMIndependentHalves
import LatticeProb.Prob.BrownianExit

/-! # Normalization of a forward Brownian pair -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The forward coordinates, divided by `√2`, have generator `Δ / 4`. -/
noncomputable def normalizedForwardSpace (t : ℝ≥0) (ω : Path2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => halfPath (i, true) t ω / Real.sqrt 2)

/-- The normalized forward pair has the Euclidean Brownian normalization. -/
theorem isBrownianSpace_normalizedForwardSpace {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) :
    IsBrownianSpace 2 0 normalizedForwardSpace μ := by
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_forall_lrCoord_zero_eq_zero hμ] with ω hω
    ext i
    simp [normalizedForwardSpace, halfPath, hω]
  · intro i
    have heq : (fun t ω => Real.sqrt ((2 : ℕ) : ℝ) * (normalizedForwardSpace t ω i - (0 : EuclideanSpace ℝ (Fin 2)) i)) =
        halfPath (i, true) := by
      funext t ω
      simp only [normalizedForwardSpace, PiLp.toLp_apply, PiLp.zero_apply, sub_zero]
      norm_num only [Nat.cast_ofNat]
      field_simp
    rw [heq]
    exact isBrownianReal_halfPath hμ (i, true)
  · have hind := (iIndepFun_halfPath hμ).precomp
      (g := fun i : Fin 2 => (i, true)) (by intro i j h; exact Prod.mk.inj h |>.1)
    have hind' := hind.comp (fun _ (f : ℝ≥0 → ℝ) t => f t / Real.sqrt 2)
      (fun _ => Measurable.of_eval fun t => (measurable_pi_apply t).div_const _)
    simpa only [Function.comp_def, normalizedForwardSpace, PiLp.toLp_apply] using hind'

end LatticeProb.CorrelatedBM
