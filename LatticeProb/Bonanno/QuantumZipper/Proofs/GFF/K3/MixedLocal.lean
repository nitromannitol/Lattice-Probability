/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.MixedLocal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.RealDeriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Local admissibility for the mixed space (GFF-K3 node M4)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M4).

Route (a direct energy bound, no Riesz vectors of `bind` measures):

1. *Pointwise bound* (from M1, `s → 0`): for `z ∈ Hbar` and `0 < s' ≤ ρ`,
   `|f z − ∫ f d fold_{z,s'}| ≤ (2π)⁻¹ ∫_H ‖∇f‖ · 2 k_ρ(· − z)`, with `k_ρ(u) = ‖u‖⁻¹ 1{‖u‖<ρ}`.
2. *Averaging* over `s' ∈ (R, 2R)` with weight `s'` (polar coordinates) turns the circle
   term into `(2π)⁻¹ · 2 ∫_D |f|`, provided `H ∩ B(z, 2R) ⊆ D`.
3. Integrate against `μ`; the gradient term is handled by Tonelli, Cauchy–Schwarz and the
   kernel bound `∫ k(y−a) k(y−b) dy ≤ C (1 + log⁻ ‖a − b‖)` (admissibility of `μ`); the `L¹`
   term by Cauchy–Schwarz and the Poincaré inequality M3.

Sources. Step 1 is the localized first-order representation formula
`f(x) = ω₁⁻¹ ∫ ∇f(y)·(x−y)/|x−y|² dy` (D. R. Adams, L. I. Hedberg, *Function Spaces and Potential
Theory*, Springer 1996, eq. (1.2.4), p. 8), in the form of the annulus identity M1; Steps 1–2
follow the classical potential estimate `|u(x) − u_B| ≤ C ∫_B |∇u(y)| |x−y|^{1−n} dy`
(D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, 2001 ed.,
Lemma 7.16, eq. (7.41), p. 162; `literature/GilbargTrudinger_EllipticPDE_2001.pdf`, PDF p. 175):
the same radial fundamental theorem of calculus followed by averaging, but with the average over a
folded annulus (weight `s'` on `s' ∈ (R, 2R)`) in place of the average over a convex set, and the
radial integration packaged as the annulus identity M1. Step 3 is Fubini for the
mutual energy (Adams–Hedberg, §2.3, eq. (2.3.3), p. 24) together with the planar composition
bound `∫ |y−a|⁻¹ |y−b|⁻¹ dy ≲ 1 + log⁻|a−b|` for truncated Riesz kernels (the critical case of the
composition law of Riesz kernels, N. S. Landkof, *Foundations of Modern Potential Theory*, Ch. I;
proved here directly by splitting at `|y − a| = |a − b|/2`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal

namespace QuantumZipper.K3

/-! ## Local discs -/

/-! ## Elementary geometry -/

/-! ## Step 1: the pointwise bound -/

theorem tendsto_integral_circleUnif_zero {g : ℂ → ℝ} (hg : Continuous g) (w : ℂ) :
    Tendsto (fun r => ∫ x, g x ∂(circleUnif w r)) (𝓝[>] 0) (𝓝 (g w)) := by
  simp_rw [integral_circleUnif_eq hg]
  have hvol : ∫ θ in Ioo (-π) π, g (circleMap w 0 θ) = 2 * π * g w := by
    simp only [circleMap_zero_radius, Function.const_apply, setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    ring
  have hgw : g w = (2 * π)⁻¹ * ∫ θ in Ioo (-π) π, g (circleMap w 0 θ) := by
    rw [hvol]; field_simp
  rw [hgw]
  refine Tendsto.const_mul _ ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall w 1).exists_bound_of_continuousOn hg.continuousOn
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun r => (hg.comp (continuous_circleMap w r)).aestronglyMeasurable)
    ?_ (integrable_const C) (Eventually.of_forall fun θ => ?_)
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
    refine Eventually.of_forall fun θ => hC _ ?_
    rw [mem_closedBall, dist_eq_norm, norm_circleMap_sub_center, abs_of_pos hr.1]
    exact hr.2.le
  · have hcont : Continuous fun r : ℝ => g (circleMap w r θ) :=
      hg.comp ((continuous_circleMap_uncurry w).comp (continuous_id.prodMk continuous_const))
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-! ## Step 2: averaging in polar coordinates -/

/-! ## Step 3: the kernel bound -/

/-! ## Step 4: assembly -/

end QuantumZipper.K3
