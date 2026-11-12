/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.Bilip at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA

/-!
(task P2-M2A, WP-M2a, row 2 of `blueprint/M2.md`)

GM (arXiv:1905.00383v3, `uniqueness-final.tex`) Prop 2.2, l. 890–896: for a whole-plane GFF `h`
and weak γ-LQG metrics `D`, `D̃` with the same `𝔠_r`, there is a deterministic `C > 0` with a.s.
`C⁻¹ D_h ≤ D̃_h ≤ C D_h` on `ℂ × ℂ`. GM's proof (l. 927–936), followed step by step:

1. `D_h`, `D̃_h` are jointly local and ξ-additive (GM S2.3, `gm_S2_3`, from LM Lemma 1.4).
2. By Axioms IV′ and V ("for any `p ∈ (0,1)` we can find `C_p`", l. 928–933; here the tightness
   facts `Blueprint.GMS2_4a` (i) with `K = ∂B_{1/2}(0)`, `U = B_1(0)` and `Blueprint.GMS2_4c` with
   `K = ∂B_1(0)`, `U = A_{1/2,2}(0)`), with probability `≥ p` both
   `sup_{u,v ∈ ∂B_r(z)} D̃_h(u,v; A_{r/2,2r}(z)) ≤ S 𝔠_r e^{ξh_r(z)}` and
   `D_h(∂B_{r/2}(z), ∂B_r(z)) ≥ s 𝔠_r e^{ξh_r(z)}`; so LM (1.6) holds with `C = S/s`
   (`C_p²` in GM) for `(D, D̃)` and for `(D̃, D)`.
3. LM Theorem 1.6 (`Blueprint.LMThm1_6`, = GM Thm 2.5) gives `D̃_h ≤ C D_h` a.s.

LM Thm 1.6 is for the normalized field `h − h_1(0)`; GM applies it to `h` directly. We apply it to
`h − h_1(0)` on one reference probability space and transfer the (measurable) conclusion to every
whole-plane GFF by the uniqueness of the law of `h − h_1(0)` (`Tight.map_normalize_eq`) and Weyl
scaling by the constant `h_1(0)` (`IsWeakLQGMetric.ae_dist_addConst`); this is what makes `C`
deterministic, i.e. independent of the probability space (reading BP-M2-6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

namespace Bilip

/-! ## Elementary geometry of `scaleSet` -/

lemma scaleSet_eq_preimage {r : ℝ} (hr : r ≠ 0) (z : ℂ) (A : Set ℂ) :
    scaleSet r z A = (fun x => (x - z) / r) ⁻¹' A := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ((r : ℂ) * y + z - z) / r ∈ A
    rwa [add_sub_cancel_right, mul_div_cancel_left₀ _ hr']
  · intro hx
    refine ⟨(x - z) / r, hx, ?_⟩
    change (r : ℂ) * ((x - z) / r) + z = x
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hr', sub_add_cancel]

lemma norm_div_ofReal {r : ℝ} (hr : 0 < r) (x : ℂ) : ‖x / (r : ℂ)‖ = ‖x‖ / r := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

lemma scaleSet_sphere {r : ℝ} (hr : 0 < r) (z : ℂ) (ρ : ℝ) :
    scaleSet r z (Metric.sphere 0 ρ) = Metric.sphere z (r * ρ) := by
  rw [scaleSet_eq_preimage hr.ne']
  ext x
  simp only [mem_preimage, mem_sphere_iff_norm, sub_zero, norm_div_ofReal hr]
  rw [div_eq_iff hr.ne', mul_comm]

lemma scaleSet_annulus {r : ℝ} (hr : 0 < r) (z : ℂ) (a b : ℝ) :
    scaleSet r z (annulus 0 a b : Set ℂ) = (annulus z (r * a) (r * b) : Set ℂ) := by
  rw [scaleSet_eq_preimage hr.ne']
  ext x
  change (a < ‖(x - z) / r - 0‖ ∧ ‖(x - z) / r - 0‖ < b) ↔ (r * a < ‖x - z‖ ∧ ‖x - z‖ < r * b)
  rw [sub_zero, norm_div_ofReal hr, lt_div_iff₀ hr, div_lt_iff₀ hr, mul_comm a, mul_comm b]

lemma isPreconnected_annulus_zero {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected (annulus 0 a b : Set ℂ) := by
  have e : (annulus 0 a b : Set ℂ) =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Ioo a b ×ˢ univ) := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      rw [sub_zero] at h1 h2
      exact ⟨(‖w‖, Complex.arg w), ⟨⟨h1, h2⟩, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I w⟩
    · rintro ⟨⟨t, θ⟩, ⟨⟨h1, h2⟩, -⟩, rfl⟩
      have ht : 0 < t := ha.trans_lt h1
      have hn : ‖(t : ℂ) * Complex.exp (θ * Complex.I) - 0‖ = t := by
        rw [sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ht]
      exact ⟨hn.symm ▸ h1, hn.symm ▸ h2⟩
  rw [e]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)).continuousOn

lemma isBounded_annulus_zero (a b : ℝ) : Bornology.IsBounded (annulus 0 a b : Set ℂ) :=
  Metric.isBounded_ball.subset fun w hw => by
    rw [mem_ball_zero_iff]; simpa using hw.2

/-! ## Probability bookkeeping -/

/-! ## One direction on a fixed probability space (GM l. 927–936) -/

variable {γ : ℝ} {D₁ D₂ : DistC → ContMetric} {c : ℝ → ℝ}

/-! ## GM Proposition 2.2 -/

end Bilip

end LQGMetric.GM
