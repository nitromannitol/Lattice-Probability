import Mathlib

/-!
# Kingman's subadditive ergodic theorem: comparator challenge

Mathlib-only comparator challenge for Kingman's subadditive ergodic theorem as
the library proves it: `LatticeProb.ae_tendsto_div` (the almost sure half) and
`LatticeProb.tendsto_integral_div` (the half about the means), both in
`LatticeProb/Prob/Kingman.lean`.

Content: let `T` preserve a finite measure `μ`, and let `g n` be measurable,
integrable, subadditive along `T`, that is `g (m + n) x ≤ g m x + g n (T^m x)`,
and bounded below by `c n`.  Then almost everywhere `g n x / n` converges to a
finite limit, and the means `(∫ g n) / n` converge to their infimum over
`n ≥ 1`.

Only Mathlib is imported, and no definition is needed: subadditivity along `T`
is written out as a hypothesis.  The sole intentional `sorry` is the proof of
the final theorem.

## Presentation deltas

The library states the two halves separately and names the limit of the means
with Mathlib's `Subadditive.lim`, which is by definition the infimum displayed
here.  The library's almost sure half needs only `g 1` integrable; the
challenge assumes every `g n` integrable, which the half about the means uses.
-/

namespace LatticeProbAudit

open MeasureTheory Filter Topology

universe u

/-- Kingman's subadditive ergodic theorem, for a family bounded below linearly. -/
theorem kingman {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ (m n : ℕ) (x : Ω), g (m + n) x ≤ g m x + g n (T^[m] x))
    (hgm : ∀ n, Measurable (g n)) (hint : ∀ n, Integrable (g n) μ)
    {c : ℝ} (hlow : ∀ (n : ℕ) (x : Ω), 1 ≤ n → c * n ≤ g n x) :
    (∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / n) atTop (𝓝 L)) ∧
      Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop
        (𝓝 (sInf ((fun n : ℕ => (∫ x, g n x ∂μ) / n) '' Set.Ici 1))) := by
  sorry

end LatticeProbAudit
