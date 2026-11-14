/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLFPPMetricMeas at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BMom
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

theorem laneC_measurable_lfppD
    {Ω : Type*} [MeasurableSpace Ω] (Y : ℂ → Ω → ℝ)
    (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hYm : ∀ z, Measurable (Y z)) (ξ : ℝ) (z w : ℂ) :
    Measurable fun ω => lfppD ξ (fun x => Y x ω) z w := by
  letI : Countable gaussRat := gaussRat_countable.to_subtype
  have hcost (N : ℕ) (q : Fin N → gaussRat) :
      Measurable fun ω => chainCost ξ (fun x => Y x ω) z w N q := by
    change Measurable fun ω =>
      ∑ i ∈ Finset.range (N + 1),
        segCost ξ (fun x => Y x ω) (chainV z w N q i) (chainV z w N q (i + 1))
    apply Finset.measurable_sum
    intro i hi
    exact LQGMetric.DDDF.measurable_lfppLen hYc hYm
      (isPiecewiseC1Path_segPath _ _).continuousOn
  have hchain : Measurable fun ω =>
      ⨅ (N : ℕ) (q : Fin N → gaussRat),
        chainCost ξ (fun x => Y x ω) z w N q :=
    Measurable.iInf fun N => Measurable.iInf fun q => hcost N q
  convert hchain using 1
  funext ω
  exact lfppDOn_eq_iInf_chain (ξ := ξ) (φ := fun x => Y x ω)
    (S := Set.univ) (hYc ω) convex_univ (subset_univ _)
    (fun x _ ρ hρ => gaussRat_dense x hρ) (mem_univ _) (mem_univ _)

theorem laneC_measurable_lfppContMetric
    {Ω : Type*} [MeasurableSpace Ω] (Y : ℂ → Ω → ℝ)
    (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hYm : ∀ z, Measurable (Y z)) (ξ : ℝ) :
    Measurable fun ω => lfppContMetric ξ (fun z => Y z ω) (hYc ω) := by
  apply Measurable.subtype_mk
  apply ContinuousMap.measurable_iff_eval.2
  intro p
  change Measurable fun ω => (lfppD ξ (fun z => Y z ω) p.1 p.2).toReal
  exact ENNReal.measurable_toReal.comp
    (laneC_measurable_lfppD Y hYc hYm ξ p.1 p.2)

end SupercriticalLQGUniqueness.B2.DG20Conc
