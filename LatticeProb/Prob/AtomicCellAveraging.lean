import Mathlib
import LatticeProb.Prob.AtomicPairingReplacement

/-!
# Averaging over cells: from a measure decomposed over cells to the atomic measure

Let `μ` be a measure on `ℂ`, let `(H x)_{x ∈ s}` be a finite family of pairwise disjoint measurable
cells of finite `μ`-mass, and let `p x` be a marked point attached to the cell `H x` (for a
mated-CRT map, `H x = η([x - ε, x])` is the space-filling SLE cell of the vertex `x`, `p x = η(x)`
and `μ` is the `γ`-LQG measure, so `μ(H x) = ε`). The atomic measure
`ν = Σ_{x ∈ s} μ(H x) δ_{p x}` carries the `μ`-mass of each cell at its marked point.

For a test function `φ`, splitting `∫_{⋃ H x} φ dμ` over the disjoint cells and comparing each cell
integral with `μ(H x) φ(p x)` gives
`|∫ φ dν - ∫_{⋃ H x} φ dμ| ≤ Σ_{x ∈ s} μ(H x) ω x`, where `ω x` bounds the oscillation
`|φ z - φ(p x)|` over `z ∈ H x`. If every point of `H x` lies within distance `δ` of `p x` and the
modulus of continuity of `φ` at scale `δ` is at most `m δ`, the bound is `m δ · μ(⋃ H x)`.

Only the `μ`-measurability of `φ` is assumed: the oscillation bound makes `φ` bounded on each cell.

## Main statements

* `LatticeProb.abs_integral_atomic_sub_integral_restrict_le`: the cell-by-cell oscillation bound.
* `LatticeProb.abs_integral_atomic_sub_integral_restrict_le_of_dist_le`: the uniform bound in
  terms of the modulus of continuity of `φ` at the scale of the cell diameters.
* `LatticeProb.atomicMeasure_cellMass_eq`: the atomic measure of the cell masses written with
  `LatticeProb.atomicMeasure`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {ι : Type*}

/-- **The atomic measure of the cell masses.** If every cell `H x` has finite `μ`-mass, the measure
`Σ_{x ∈ s} μ(H x) δ_{p x}` is the atomic measure `atomicMeasure s (fun x => μ(H x)) p`. -/
theorem atomicMeasure_cellMass_eq (s : Finset ι) {μ : Measure ℂ} {H : ι → Set ℂ}
    (hfin : ∀ x ∈ s, μ (H x) < ∞) (p : ι → ℂ) :
    atomicMeasure s (fun x => (μ (H x)).toReal) p = ∑ x ∈ s, μ (H x) • Measure.dirac (p x) := by
  unfold atomicMeasure
  exact Finset.sum_congr rfl fun x hx => by rw [ENNReal.ofReal_toReal (hfin x hx).ne]

/-- **Atomic replacement of a measure decomposed over cells.** Let `(H x)_{x ∈ s}` be pairwise
disjoint measurable cells of finite `μ`-mass with marked points `p x`, and let `φ` be
`μ`-measurable with oscillation `|φ z - φ(p x)| ≤ ω x` for `z ∈ H x`. Then the integral of `φ`
against the atomic measure `ν = Σ_{x ∈ s} μ(H x) δ_{p x}` differs from `∫_{⋃ H x} φ dμ` by at most
`Σ_{x ∈ s} μ(H x) ω x`. -/
theorem abs_integral_atomic_sub_integral_restrict_le (s : Finset ι) {μ : Measure ℂ}
    {H : ι → Set ℂ} (hHm : ∀ x ∈ s, MeasurableSet (H x)) (hHd : (s : Set ι).PairwiseDisjoint H)
    (hfin : ∀ x ∈ s, μ (H x) < ∞) (p : ι → ℂ) {φ : ℂ → ℝ} (hφ : AEStronglyMeasurable φ μ)
    (ω : ι → ℝ) (hω : ∀ x ∈ s, ∀ z ∈ H x, |φ z - φ (p x)| ≤ ω x) :
    |∫ z, φ z ∂(∑ x ∈ s, μ (H x) • Measure.dirac (p x)) - ∫ z in ⋃ x ∈ s, H x, φ z ∂μ| ≤
      ∑ x ∈ s, (μ (H x)).toReal * ω x := by
  -- `φ` is integrable on each cell: there `|φ z| ≤ |φ (p x)| + ω x`
  have hint : ∀ x ∈ s, IntegrableOn φ (H x) μ := by
    intro x hx
    refine Measure.integrableOn_of_bounded (M := |φ (p x)| + ω x) (hfin x hx).ne hφ ?_
    refine ae_restrict_of_forall_mem (hHm x hx) fun z hz => ?_
    rw [Real.norm_eq_abs]
    have h1 := abs_sub_abs_le_abs_sub (φ z) (φ (p x))
    have h2 := hω x hx z hz
    linarith
  rw [← atomicMeasure_cellMass_eq s hfin p,
    integral_atomicMeasure s (c := fun x => (μ (H x)).toReal) (fun _ => ENNReal.toReal_nonneg) p φ,
    integral_biUnion_finset s hHm hHd hint, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  show |(μ (H x)).toReal * φ (p x) - ∫ z in H x, φ z ∂μ| ≤ (μ (H x)).toReal * ω x
  -- compare the cell integral with `μ(H x) φ(p x)`
  have hconst : IntegrableOn (fun _ : ℂ => φ (p x)) (H x) μ := integrableOn_const (hfin x hx).ne
  have he : (μ (H x)).toReal * φ (p x) - ∫ z in H x, φ z ∂μ =
      ∫ z in H x, (φ (p x) - φ z) ∂μ := by
    rw [integral_sub hconst (hint x hx), setIntegral_const, smul_eq_mul, measureReal_def]
  rw [he, ← Real.norm_eq_abs]
  have h := norm_setIntegral_le_of_norm_le_const (s := H x) (μ := μ)
    (f := fun z => φ (p x) - φ z) (hfin x hx) (fun z hz => by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hω x hx z hz)
  rw [measureReal_def] at h
  exact h.trans_eq (mul_comm _ _)

/-- **Atomic replacement, uniform form.** If every point of the cell `H x` lies within distance
`δ` of its marked point `p x` and `|φ z - φ w| ≤ m δ` whenever `dist z w ≤ δ` (the modulus of
continuity of `φ` at scale `δ`), then
`|∫ φ dν - ∫_{⋃ H x} φ dμ| ≤ m δ · μ(⋃_{x ∈ s} H x)` for `ν = Σ_{x ∈ s} μ(H x) δ_{p x}`. -/
theorem abs_integral_atomic_sub_integral_restrict_le_of_dist_le (s : Finset ι) {μ : Measure ℂ}
    {H : ι → Set ℂ} (hHm : ∀ x ∈ s, MeasurableSet (H x)) (hHd : (s : Set ι).PairwiseDisjoint H)
    (hfin : ∀ x ∈ s, μ (H x) < ∞) (p : ι → ℂ) {φ : ℂ → ℝ} (hφ : AEStronglyMeasurable φ μ)
    {δ : ℝ} (hdiam : ∀ x ∈ s, ∀ z ∈ H x, dist z (p x) ≤ δ)
    (m : ℝ → ℝ) (hm : ∀ z w, dist z w ≤ δ → |φ z - φ w| ≤ m δ) :
    |∫ z, φ z ∂(∑ x ∈ s, μ (H x) • Measure.dirac (p x)) - ∫ z in ⋃ x ∈ s, H x, φ z ∂μ| ≤
      m δ * (μ (⋃ x ∈ s, H x)).toReal := by
  refine (abs_integral_atomic_sub_integral_restrict_le s hHm hHd hfin p hφ (fun _ => m δ)
    fun x hx z hz => hm z (p x) (hdiam x hx z hz)).trans_eq ?_
  rw [measure_biUnion_finset hHd hHm, ENNReal.toReal_sum fun x hx => (hfin x hx).ne,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

end LatticeProb
