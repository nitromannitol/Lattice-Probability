/-
Kingman's subadditive ergodic theorem: the part that is reachable, and what is
missing.

A family `g n` is subadditive along `T` when `g (m + n) x ≤ g m x + g n (T^m x)`.
Kingman's theorem says that if `T` preserves a probability measure and the means
are bounded below then `g n / n` converges almost everywhere and in `L¹` to a
`T`-invariant limit whose mean is `inf_n (∫ g n) / n`.

What is proved here is the statement about the means: they form a subadditive
sequence, because `T` preserves the measure, so Fekete's lemma applies and
`(∫ g n) / n` converges to its infimum.  That is the deterministic half, and it
is what identifies the limit once the almost sure convergence is known.

The almost sure half is not proved here, and the obstruction is named: Mathlib
4.32 has no pointwise (Birkhoff) ergodic theorem.  The first step of the chain
that leads to one is `LatticeProb.maximal_ergodic`, proved in
`LatticeProb/Prob/MaximalErgodic.lean`; from it Birkhoff follows by the standard
argument on the invariant sets where the lower limit is below `α` and the upper
limit above `β`, and Kingman follows from Birkhoff by Steele's argument.  Until
those land, the full statement is `LatticeProb.External.KingmanSubadditive`.
-/
import Mathlib
import LatticeProb.Prob.MaximalErgodic

noncomputable section

namespace LatticeProb

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- A family subadditive along `T`. -/
def SubadditiveAlong (T : Ω → Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∀ (m n : ℕ) (x : Ω), g (m + n) x ≤ g m x + g n (T^[m] x)

theorem integrable_comp_iterate (hT : MeasurePreserving T μ μ) {h : Ω → ℝ}
    (hh : Integrable h μ) (m : ℕ) : Integrable (fun x => h (T^[m] x)) μ := by
  have hcopy := hh
  rw [← (hT.iterate m).map_eq] at hcopy
  exact (integrable_map_measure hcopy.aestronglyMeasurable
    (hT.measurable.iterate m).aemeasurable).mp hcopy

theorem integral_comp_iterate (hT : MeasurePreserving T μ μ) {h : Ω → ℝ}
    (hh : Integrable h μ) (m : ℕ) : ∫ x, h (T^[m] x) ∂μ = ∫ x, h x ∂μ := by
  conv_rhs => rw [← (hT.iterate m).map_eq]
  rw [integral_map (hT.measurable.iterate m).aemeasurable
    (by rw [(hT.iterate m).map_eq]; exact hh.aestronglyMeasurable)]

/-- The means of a family subadditive along a measure-preserving transformation
form a subadditive sequence. -/
theorem subadditive_integral (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : SubadditiveAlong T g) (hint : ∀ n, Integrable (g n) μ) :
    Subadditive fun n => ∫ x, g n x ∂μ := by
  intro m n
  have h1 : Integrable (fun x => g m x + g n (T^[m] x)) μ :=
    (hint m).add (integrable_comp_iterate hT (hint n) m)
  calc ∫ x, g (m + n) x ∂μ
      ≤ ∫ x, (g m x + g n (T^[m] x)) ∂μ :=
        integral_mono (hint (m + n)) h1 fun x => hsub m n x
    _ = (∫ x, g m x ∂μ) + ∫ x, g n (T^[m] x) ∂μ :=
        integral_add (hint m) (integrable_comp_iterate hT (hint n) m)
    _ = (∫ x, g m x ∂μ) + ∫ x, g n x ∂μ := by
        rw [integral_comp_iterate hT (hint n) m]

/-- **The mean half of Kingman's theorem.**  For a family subadditive along a
measure-preserving transformation whose means divided by `n` are bounded below,
`(∫ g n) / n` converges to its infimum. -/
theorem tendsto_integral_div (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : SubadditiveAlong T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g n x ∂μ) / n)) :
    Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop
      (nhds (subadditive_integral hT hsub hint).lim) :=
  (subadditive_integral hT hsub hint).tendsto_lim hbdd

/-- The limit of the means is at most every one of them. -/
theorem lim_integral_le (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : SubadditiveAlong T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g n x ∂μ) / n)) {n : ℕ} (hn : n ≠ 0) :
    (subadditive_integral hT hsub hint).lim ≤ (∫ x, g n x ∂μ) / n :=
  (subadditive_integral hT hsub hint).lim_le_div hbdd hn

omit [MeasurableSpace Ω] in
/-- The Birkhoff sums of an integrable function are subadditive along `T`, with
equality; so Kingman's theorem contains Birkhoff's. -/
theorem subadditiveAlong_birkhoffSum (T : Ω → Ω) (f : Ω → ℝ) :
    SubadditiveAlong T fun n => birkhoffSum T f n := by
  intro m n x
  show birkhoffSum T f (m + n) x ≤ birkhoffSum T f m x + birkhoffSum T f n (T^[m] x)
  rw [birkhoffSum_add]

end LatticeProb

end
