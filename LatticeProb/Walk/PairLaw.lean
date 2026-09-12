/-
The law of a PAIR of independent simple random walks.

`walkPairLaw d x y` is the product of the law of the walk started at `x` with
the law of the walk started at `y`.  Its Fubini theorems turn every double
expectation `E_x E_y` of the sandpile papers into one integral against a
single measure.
-/
import LatticeProb.Walk.Markov
open MeasureTheory LatticeProb
noncomputable section
/-- The law of two independent walks started at `x` and `y`. -/
noncomputable def walkPairLaw (d : ℕ) [NeZero d] (x y : Site d) :
    Measure ((ℕ → Site d) × (ℕ → Site d)) :=
  (siteWalkLaw d x).prod (siteWalkLaw d y)

instance walkPairLaw_isProbabilityMeasure (d : ℕ) [NeZero d] (x y : Site d) :
    IsProbabilityMeasure (walkPairLaw d x y) := by
  unfold walkPairLaw; infer_instance

theorem lintegral_walkPairLaw {d : ℕ} [NeZero d] (x y : Site d)
    {f : (ℕ → Site d) → (ℕ → Site d) → ENNReal}
    (hf : AEMeasurable (fun p => f p.1 p.2) (walkPairLaw d x y)) :
    ∫⁻ p, f p.1 p.2 ∂(walkPairLaw d x y)
      = ∫⁻ X, (∫⁻ Y, f X Y ∂(siteWalkLaw d y)) ∂(siteWalkLaw d x) := by
  rw [walkPairLaw]
  exact lintegral_prod _ hf
end
