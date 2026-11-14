import LatticeProb.Prob.BrownianParentBlockClockInitialBound
import LatticeProb.Prob.BrownianSkeletonAlmostSure

/-!
# Active Brownian parent-block clock bounds

Almost-sure finiteness removes the finite-clock condition from the active clock estimate.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

private theorem bounded_closedSquare (c : ℂ) (s : ℝ) :
    Bornology.IsBounded (LatticeProb.ParentBlock.closedSquare c s) := by
  refine ((Metric.isBounded_Icc (c.re - s / 2) (c.re + s / 2)).reProdIm
    (Metric.isBounded_Icc (c.im - s / 2) (c.im + s / 2))).subset ?_
  intro z hz
  change |z.re - c.re| ≤ s / 2 ∧ |z.im - c.im| ≤ s / 2 at hz
  change z.re ∈ Icc _ _ ∧ z.im ∈ Icc _ _
  obtain ⟨h1, h2⟩ := abs_le.mp hz.1
  obtain ⟨h3, h4⟩ := abs_le.mp hz.2
  constructor <;> constructor <;> linarith

/-- The active parent-block clock has a scale-normalized probability bound. -/
theorem measure_active_parentBlock_clock_le_without_finiteness
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → Euc 2), LatticeProb.IsBrownianSpace 2 0 B P →
      ∀ (path : Ω → BrownianPath 2), (∀ t ω, path ω t = B t ω) →
      ∀ {J : Type*} [Countable J] [MeasurableSpace (Option J)]
        [MeasurableSingletonClass (Option J)] (centres : J → ℂ)
        (z : Euc 2) (c : ℂ) (S s : ℝ≥0), 0 < S → 0 < s → s ≤ S →
      Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.closedSquare c S →
      ∀ (j₀ : J),
      Complex.orthonormalBasisOneI.repr.symm z ∈
        LatticeProb.ParentBlock.closedSquare (centres j₀) s →
      ∀ (selector : ℕ → Euc 2 → Option J),
      (∀ n x j, selector n x = some j →
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.closedSquare (centres j) s) →
      ∀ K : ℕ, ⌊((s / (18 * S) : ℝ≥0) : ℝ) ^ (-(2 + ζ))⌋₊ ≤ K + 1 →
      P {ω | let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
        let clock := brownianSkeletonClock U z j₀ selector
        (clock K (path ω)).1 = false} ≤
        ENNReal.ofReal (C * (((s / (18 * S) : ℝ≥0) : ℝ) ^ p)) := by
  obtain ⟨C, hC⟩ := measure_active_parentBlock_clock_le_of_initial_square.{u} hζ0 hζ1 p
  refine ⟨C, ?_⟩
  intro Ω _ P _ B hB path hpath J _ _ _ centres z c S s hS hs hsS hz j₀ hz₀ selector hselector K hK
  let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  have hU : ∀ j, Bornology.IsBounded (U j) := by
    intro j
    apply (Complex.orthonormalBasisOneI.repr.symm.isometry.antilipschitzWith.isBounded_preimage ?_).subset
      (preimage_mono interior_subset)
    rw [LatticeProb.ParentBlock.parentBlock_eq (by exact_mod_cast hs.le)]
    exact bounded_closedSquare _ _
  have hfinite := ae_brownianSkeletonClock_finite (by decide) hB path hpath U hU z j₀ selector
  apply le_trans (measure_mono_ae ?_)
    (hC Ω P B hB path hpath centres z c S s hS hs hsS hz j₀ hz₀ selector hselector K hK)
  filter_upwards [hfinite] with ω hω hactive
  exact ⟨hactive, hω K⟩

end BouRabeeGwynne
