import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.Topology.PlaneTopology
import LatticeProb.LQG.LQGMeasureInputs
import LatticeProb.LQG.LQGMeasureNonatomic
import LatticeProb.LQG.LQGMeasureNonatomicMassRescaled
import LatticeProb.LQG.LQGMeasureNonatomicMassTail
import LatticeProb.LQG.LQGMeasureFullSupport3

/-!
# Square positivity of the LQG measure

Status: the LP form of the frozen statement is defined, and its proof from the three LP input binders of the HB derivation
(`hDG`, `hCC`, `hE`, as in `LatticeProb/LQG/LQGMeasureInputs.lean`) is `lqgMeasureSquarePositiveLP_of_inputs`, through the LP
full-support statement `LQGMeasureFullSupportStmtLP` (`LQGMeasureFullSupport3.lean`).

* `LatticeProb.Topology.exists_isOpen_nonempty_subset_closedDyadicSquare`: LP port of
  `HarmonicBalls.exists_isOpen_nonempty_subset_closedDyadicSquare` (`SquarePositiveDerived.lean:24`).
* `LatticeProb.LQG.LQGMeasureSquarePositiveLP`: LP form of `LQGMeasureSquarePositiveFrozen` (`FirstPass/Frozen/S11c.lean:130`);
  a definition only.
* `LatticeProb.LQG.ae_pos_closedDyadicSquare_of_charges`: the elementary step of `SquarePositiveDerived.lean:40`: if almost
  surely `μ` charges every nonempty open set, then almost surely `μ(S) > 0` for every closed dyadic square `S`. No LQG input.
-/

open MeasureTheory Set Filter Topology Metric

universe u

namespace LatticeProb.Topology

/-- A closed dyadic square contains a nonempty open rectangle: the open product of the open intervals
`(j 2^{-n}, (j+1) 2^{-n})` and `(k 2^{-n}, (k+1) 2^{-n})`. -/
theorem exists_isOpen_nonempty_subset_closedDyadicSquare (n j k : ℤ) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ closedDyadicSquare n j k := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have h1 : (j : ℝ) * 2 ^ (-n) < ((j : ℝ) + 1) * 2 ^ (-n) := by nlinarith
  have h2 : (k : ℝ) * 2 ^ (-n) < ((k : ℝ) + 1) * 2 ^ (-n) := by nlinarith
  refine ⟨Ioo ((j : ℝ) * 2 ^ (-n)) (((j : ℝ) + 1) * 2 ^ (-n)) ×ℂ
    Ioo ((k : ℝ) * 2 ^ (-n)) (((k : ℝ) + 1) * 2 ^ (-n)), ?_, ?_, ?_⟩
  · exact isOpen_Ioo.reProdIm isOpen_Ioo
  · exact Complex.reProdIm_nonempty.2 ⟨nonempty_Ioo.2 h1, nonempty_Ioo.2 h2⟩
  · exact (Complex.reProdIm_subset_iff).2
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)

end LatticeProb.Topology

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.Topology

/-- **LP form of `LQGMeasureSquarePositiveFrozen`** (`FirstPass/Frozen/S11c.lean:130`): for `0 < γ < 2` and `α₀ < Q`, on every
whole-plane GFF space in `Type u` and for every LQG measure `μ` of the field, almost surely every closed dyadic square has
positive mass. Proved from the LP inputs by `lqgMeasureSquarePositiveLP_of_inputs` (below). -/
def LQGMeasureSquarePositiveLP : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ S : Set ℂ, LatticeProb.Topology.IsClosedDyadicSquare S → ∀ᵐ ω ∂P, 0 < μ ω S

/-- Elementary step of the HB derivation (`SquarePositiveDerived.lean:40`): if almost surely `μ` charges every nonempty
open set, then almost surely `μ(closedDyadicSquare n j k) > 0`. The closed square contains a nonempty open rectangle, and
the measure is monotone. No LQG input is used. -/
theorem ae_pos_closedDyadicSquare_of_charges {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (h : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U) (n j k : ℤ) :
    ∀ᵐ ω ∂P, 0 < μ ω (closedDyadicSquare n j k) := by
  obtain ⟨U, hUo, hUne, hUS⟩ := exists_isOpen_nonempty_subset_closedDyadicSquare n j k
  filter_upwards [h] with ω hω
  exact lt_of_lt_of_le (hω U hUo hUne) (measure_mono hUS)

/-- The elementary step for a set `S` that is a closed dyadic square (`LatticeProb.Topology.IsClosedDyadicSquare`). -/
theorem ae_pos_isClosedDyadicSquare_of_charges {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (h : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U) {S : Set ℂ}
    (hS : LatticeProb.Topology.IsClosedDyadicSquare S) : ∀ᵐ ω ∂P, 0 < μ ω S := by
  obtain ⟨n, j, k, rfl⟩ := hS
  exact ae_pos_closedDyadicSquare_of_charges h n j k

open LatticeProb.LQG.LQGMeasureNonatomicMass in
/-- **Square positivity from the LP inputs** (LP copy of `HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived`,
`FirstPass/Phase2/SquarePositiveDerived.lean:40`, with the same three binders `hDG`, `hCC`, `hE`). The scaled
multiscale step `WholePlaneScaledBallMassStepLP` and the non-atomicity `LQGMeasureNonatomicLP` are derived from the
binders by the proved LP lemmas `rescaledBallMassUniformStep_lp`, `wholePlaneScaledBallMassStep_of_uniform_lp`,
`circleAverageDyadicTailStep_lp` and `lqgMeasureNonatomic_lp`; the full-support statement `LQGMeasureFullSupportStmtLP` is `lqgMeasureFullSupportStmt_of_scaled_lp`; square positivity is the elementary step
`ae_pos_isClosedDyadicSquare_of_charges`. No hypothesis beyond the three binders. -/
theorem lqgMeasureSquarePositiveLP_of_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistenceLP P γ α hC hcirc) :
    LQGMeasureSquarePositiveLP.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hG hμ S hS
  have hS' : WholePlaneScaledBallMassStepLP.{u} :=
    wholePlaneScaledBallMassStep_of_uniform_lp (rescaledBallMassUniformStep_lp hDG hCC)
      circleAverageDyadicTailStep_lp
  have hFull : LQGMeasureFullSupportStmtLP.{u} :=
    lqgMeasureFullSupportStmt_of_scaled_lp hS' (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
      (lqgMeasureNonatomic_lp hDG hCC hE)
  exact ae_pos_isClosedDyadicSquare_of_charges (hFull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hμ) hS

end LatticeProb.LQG
