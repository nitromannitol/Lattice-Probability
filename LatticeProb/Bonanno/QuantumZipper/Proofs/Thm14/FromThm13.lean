/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm14.FromThm13 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue

/-!
Sheffield, *Conformal weldings of random surfaces*, §1.4. For almost every `ω`:

1. the reverse SLE hull `revHull W T` is a simple curve hull: `revHull W T` is the forward hull
   of the time-reversed increment `s ↦ W(T-s) - W(T)` (A1(c)), which is `√κ` times the
   time-reversed Brownian motion `revBM B T` (proved here to be a Brownian motion), so
   Rohde–Schramm (`RohdeSchrammSimple`) applies;
2. the doubled hull is removable (`RohdeSchrammHolder` + `JonesSmirnovRemovable`);
3. the second clause of Theorem 1.3, together with the Carathéodory boundary correspondence
   (`RevMapCaratheodory`) and the regularity of `ν_h` (`RevCouplingBoundaryMeasureRegular`),
   gives `weldingHom W T = weldR (√κ) h` on `[0₋, 0]`;
4. deterministic welding uniqueness (`revHull_eq_of_welding_eq`, A3) concludes.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14FromThm13

/-! ### Locality of the forward hull and simple chords -/

/-! ### Time reversal of Brownian motion -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The time-reversed Brownian motion on `[0,τ]`, continued by `-B` afterwards:
`revBM B τ t = B(τ - t) - B(τ)` for `t ≤ τ`, and `B(0) - B(t)` for `t ≥ τ`. -/
def revBM (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B (τ - min t τ) ω - B (max t τ) ω

theorem revBM_cov_arith (τ s t : ℝ≥0) (hst : s ≤ t) :
    ((min (τ - min s τ) (τ - min t τ) : ℝ≥0) : ℝ) - (min (τ - min s τ) (max t τ) : ℝ≥0)
      - ((min (max s τ) (τ - min t τ) : ℝ≥0) - (min (max s τ) (max t τ) : ℝ≥0)) = s := by
  rcases le_total t τ with ht | ht
  · have hs : s ≤ τ := hst.trans ht
    rw [min_eq_left hs, min_eq_left ht, max_eq_right hs, max_eq_right ht,
      min_eq_right (tsub_le_tsub_left hst τ), min_eq_left (tsub_le_self : τ - s ≤ τ),
      min_eq_right (tsub_le_self : τ - t ≤ τ), min_self, NNReal.coe_sub hs, NNReal.coe_sub ht]
    ring
  · rcases le_total s τ with hs | hs
    · rw [min_eq_left hs, min_eq_right ht, max_eq_right hs, max_eq_left ht, tsub_self,
        min_eq_right zero_le, min_eq_left ((tsub_le_self : τ - s ≤ τ).trans ht),
        min_eq_right zero_le, min_eq_left ht, NNReal.coe_sub hs]
      push_cast
      ring
    · rw [min_eq_right hs, min_eq_right ht, max_eq_left hs, max_eq_left ht, tsub_self,
        min_self, min_eq_left zero_le, min_eq_right zero_le, min_eq_left hst]
      push_cast
      ring

/-- The time-reversed Brownian motion is a Brownian motion. -/
theorem isBrownianReal_revBM {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (τ : ℝ≥0) : IsBrownianReal (revBM B τ) P where
  toIsPreBrownianReal := by
    have hG : IsGaussianProcess (revBM B τ) P := by
      classical
      exact hB.isGaussianProcess.of_isGaussianProcess fun t ↦ ⟨{τ - min t τ, max t τ},
        { toFun x := x ⟨τ - min t τ, by simp⟩ - x ⟨max t τ, by simp⟩
          map_add' x y := by simp only [Pi.add_apply]; ring
          map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
        by simp [revBM]⟩
    refine hG.isPreBrownianReal_of_covariance (fun t ↦ ?_) (fun s t hst ↦ ?_)
    · simp only [revBM]
      rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
      all_goals exact hB.integrable_eval _
    · have := hB.isGaussianProcess.isProbabilityMeasure
      unfold revBM
      rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
        hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval]
      · exact revBM_cov_arith τ s t hst
      any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
      exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  cont := by
    filter_upwards [hB.cont] with ω h
    simp only [revBM]
    fun_prop

/-! ### Measure-theoretic lemmas for the welding identification -/

section MeasureLemmas

variable {ν : Measure ℝ} (hatom : ∀ x, ν {x} = 0) (hpos : ∀ u v, u < v → 0 < ν (Ioo u v))
  (hfin : ∀ u v, ν (Icc u v) < ⊤)
include hpos hfin

end MeasureLemmas

/-! ### Step (iii): the welding homeomorphism is `weldR` -/

/-! ### The main implication -/

end Thm14FromThm13

end QuantumZipper
