import LatticeProb.Analysis.Schauder.ContinuumC2
import LatticeProb.Analysis.Schauder.HessianBound
import LatticeProb.Analysis.Schauder.SineSeriesBounded

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.ContinuumC2Free`.

# Second-order bounds of the Dirichlet inverse without the Schauder estimate

For `u = (−DΔ_Q)⁻¹ f` the bounds `|u| + ‖∇u‖ + ‖∇²u‖ ≤ C c3Norm f / D` on `ℝ^d` of
`exists_norm_iteratedFDeriv_dirichletInverse_le_two` are re-proved without the interior Schauder
estimate (GT01, Theorem 4.6).  The Hessian bound comes instead from the heat-semigroup bound
`exists_norm_iteratedFDeriv_two_le_of_bounded`, which needs only `|u| ≤ c3Norm f / (8D)`, the bound
`‖∇Δu‖ = ‖∇ sineSum f‖ / D ≤ c3Norm f / D`, and the qualitative fact that `u` has bounded
derivatives of order at most `4`.  The gradient bound is then deduced from the sup and Hessian
bounds exactly as before.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- **Hessian bound of the Dirichlet inverse, Schauder-free**: `‖D²u‖ ≤ C c3Norm f / D` on `ℝ^d`
with `C` independent of `D` and `f`, from the heat-semigroup Hessian bound applied to `u`, with
`|u| ≤ c3Norm f / (8D)` and `‖∇Δu‖ = ‖∇ sineSum f‖ / D ≤ c3Norm f / D`. -/
theorem exists_norm_iteratedFDeriv_two_dirichletInverse_le_free (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : ℝ), 0 < D → ∀ f : Euc d → ℝ, Sobolev.IsTestFn (unitCube d) f →
      ∀ z : Euc d, ‖iteratedFDeriv ℝ 2 (dirichletInverse D f) z‖ ≤ C * c3Norm f / D := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_iteratedFDeriv_two_le_of_bounded (d := d)
  refine ⟨K * (1 / 8 + 1), by positivity, fun D hD f hf z => ?_⟩
  have hc : 0 ≤ c3Norm f := (abs_nonneg _).trans (abs_le_c3Norm hf 0)
  have hbd : BoundedDerivs 4 (dirichletInverse D f) :=
    ⟨(dirichletInverse_spec hd D hD f hf).1 4, fun k _ =>
      exists_bound_iteratedFDeriv_dirichletInverse hd hD f hf k⟩
  have hLap : laplacianSum (dirichletInverse D f) = fun x => (-D⁻¹) * sineSum f x :=
    funext fun x => by
      rw [laplacianSum_dirichletInverse_eq hd hD f hf x]
      ring
  have hsd : Differentiable ℝ (sineSum f) :=
    ((sineSum_spec hd D hD f hf).1 1).differentiable (by norm_num)
  have hgrad : ∀ y, ‖fderiv ℝ (laplacianSum (dirichletInverse D f)) y‖ ≤ c3Norm f / D := by
    intro y
    rw [hLap, fderiv_const_mul (hsd y), norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.2 hD)]
    have h1 : ‖fderiv ℝ (sineSum f) y‖ ≤ c3Norm f := by
      have := (sineSum_spec hd D hD f hf).2.2 1 (by norm_num) y
      rwa [norm_iteratedFDeriv_one] at this
    calc D⁻¹ * ‖fderiv ℝ (sineSum f) y‖ ≤ D⁻¹ * c3Norm f :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hD.le)
      _ = c3Norm f / D := by ring
  have h := hKb (dirichletInverse D f) (c3Norm f / D / 8) (c3Norm f / D) hbd
    (fun y => abs_dirichletInverse_le hd hD f hf y) hgrad z
  calc ‖iteratedFDeriv ℝ 2 (dirichletInverse D f) z‖
      ≤ K * (c3Norm f / D / 8 + c3Norm f / D) := h
    _ = K * (1 / 8 + 1) * c3Norm f / D := by ring

/-- `exists_norm_iteratedFDeriv_dirichletInverse_le_two` without the Schauder hypothesis. -/
theorem exists_norm_iteratedFDeriv_dirichletInverse_le_two_free (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : ℝ), 0 < D → ∀ f : Euc d → ℝ, Sobolev.IsTestFn (unitCube d) f →
      ∀ z : Euc d, |dirichletInverse D f z| ≤ C * c3Norm f / D ∧
        ‖fderiv ℝ (dirichletInverse D f) z‖ ≤ C * c3Norm f / D ∧
        ‖iteratedFDeriv ℝ 2 (dirichletInverse D f) z‖ ≤ C * c3Norm f / D := by
  obtain ⟨C₂, hC₂, hH⟩ := exists_norm_iteratedFDeriv_two_dirichletInverse_le_free hd
  refine ⟨1 + C₂, by positivity, fun D hD f hf z => ?_⟩
  have hc : 0 ≤ c3Norm f := (abs_nonneg _).trans (abs_le_c3Norm hf 0)
  have hcD : 0 ≤ c3Norm f / D := div_nonneg hc hD.le
  have hCt : 0 ≤ C₂ * (c3Norm f / D) := mul_nonneg hC₂ hcD
  have e1 : (1 + C₂) * c3Norm f / D = (1 + C₂) * (c3Norm f / D) := by ring
  have e2 : C₂ * c3Norm f / D = C₂ * (c3Norm f / D) := by ring
  have hs := abs_dirichletInverse_le hd hD f hf z
  have hg := norm_fderiv_le_of_abs_le_of_norm_iteratedFDeriv_two_le
    ((dirichletInverse_spec hd D hD f hf).1 2) (M₀ := c3Norm f / D / 8)
    (M₂ := C₂ * c3Norm f / D) (fun w => abs_dirichletInverse_le hd hD f hf w)
    (fun w => hH D hD f hf w) z
  have hh := hH D hD f hf z
  rw [e1]
  rw [e2] at hg hh
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end LatticeProb.Analysis.Schauder

end
