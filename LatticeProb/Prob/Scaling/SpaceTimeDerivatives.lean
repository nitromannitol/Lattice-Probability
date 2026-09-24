/- Spatial derivatives of smooth functions on space-time.

Moved from Parking-Sharpness.
-/
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
namespace LatticeProb.Scaling.SpaceTimeDerivatives

variable {d : ℕ}

/-- Differentiation along a spatial coordinate, with the time coordinate fixed. -/
def spaceDeriv (ψ : ℝ × (Fin d → ℝ) → ℝ) (i : Fin d)
    (p : ℝ × (Fin d → ℝ)) : ℝ := fderiv ℝ ψ p (0, Pi.single i 1)

/-- The spatial derivative of a smooth function is smooth. -/
theorem contDiff_spaceDeriv {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (spaceDeriv ψ i) :=
  (hψ.fderiv_right (by simp)).clm_apply contDiff_const

/-- The spatial derivative's support lies within the original function's support. -/
theorem tsupport_spaceDeriv_subset (ψ : ℝ × (Fin d → ℝ) → ℝ) (i : Fin d) :
    tsupport (spaceDeriv ψ i) ⊆ tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)

/-- The ordinary derivative of a one-coordinate slice of `ψ` in a spatial direction agrees
with `spaceDeriv` evaluated on that slice. -/
theorem deriv_spaceSlice {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : Differentiable ℝ ψ) (p : ℝ × (Fin d → ℝ)) (i : Fin d) (s : ℝ) :
    deriv (fun t => ψ (p.1, Function.update p.2 i t)) s =
      spaceDeriv ψ i (p.1, Function.update p.2 i s) :=
  ((hψ _).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s p.1).prodMk (hasDerivAt_update p.2 i s))).deriv

/-- The second ordinary derivative of a one-coordinate slice in a spatial direction agrees with
the iterated `spaceDeriv` in that same direction. -/
theorem second_deriv_spaceSlice {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : ℝ × (Fin d → ℝ)) (i : Fin d) :
    deriv (fun s => deriv (fun t => ψ (p.1, Function.update p.2 i t)) s) (p.2 i) =
      spaceDeriv (spaceDeriv ψ i) i p := by
  simp_rw [deriv_spaceSlice (hψ.differentiable (by simp)) p i]
  rw [deriv_spaceSlice ((contDiff_spaceDeriv hψ i).differentiable (by simp)) p i,
    Function.update_eq_self]

end LatticeProb.Scaling.SpaceTimeDerivatives
