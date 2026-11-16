import LatticeProb.LQG.RecentredSquareFiniteCenterTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Eventual finite-center bounds for recentred square approximations -/

open MeasureTheory Filter
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- Summable finite-center maximal tails give an almost-sure eventual bound along the scales. -/
theorem exists_ae_eventually_finset_sup_iSup_normalized_recentred_square_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (S : ℕ → Finset ℂ) (t : ℕ → ℝ),
      (∀ m, 0 < t m) →
      (∑' m, (S m).card * C / ENNReal.ofReal (t m ^ p)) ≠ ⊤ →
      ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
        (S m).sup (fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) <
          ENNReal.ofReal (t m) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_measure_finset_sup_iSup_normalized_recentred_square_le hH hHm hγ hγ2 hp hpq hq
  refine ⟨C, hC, fun S t ht hsum => ?_⟩
  let E : ℕ → Set Ω := fun m => {ω | ENNReal.ofReal (t m) ≤
    (S m).sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω}
  have hfin : (∑' m, P (E m)) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun m => (htail (S m) m (t m) (ht m)).2)
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with m hm
  exact lt_of_not_ge hm

end LatticeProb.LQG
