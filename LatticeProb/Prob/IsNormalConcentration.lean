/-
# Isonormal concentration: Lipschitz preservation and the Fatou limit

The frozen `Sandpile.External.GaussianLipschitzConcentration` is stated for an arbitrary index
type `ι` with the ℓ²/Cameron–Martin condition on `LatticeProb.gaussLaw ι`.  The library
closes the finite-`ι` case (`LatticeProb.gaussian_lipschitz_concentration_l2_fin`) and the
infinite-to-finite reduction (`LatticeProb.tendsto_partialInt`).  This file takes one of the
two remaining pieces.

**Part 1 — Lipschitz preservation.**  For a finite set `S` of coordinates the partial integral
`partialInt (fun _ => gaussianReal 0 1) S F` — the conditional expectation on the coordinates in
`S` — is again ℓ²-Lipschitz with the same constant: `abs_partialInt_sub_le`.  It rests on
`hasSum_sq_comb_sub`: splicing `ω` and `ω'` along a finite `S` differs on `S`, so the ℓ² sum
of the difference is the finite sum over `S`.

**Still open (named).**  (i) The two slice-integrability hypotheses of `abs_partialInt_sub_le`; for
an ℓ²-Lipschitz `F` they follow from linear growth under the Gaussian law, but that bridge is not
formalised here.  (ii) The **Fatou limit**: from `E[F | 𝓕_{S n}] → F` a.e. and a uniform bound
the tails of the approximations, derive the tail bound for `F` (the a.e. convergence plus the
open-set argument, taking the liminf of the measures along the exhaustion).  (iii) The finite
theorem at the frozen constant `L` rather than the library's sup-metric `L √n`.

No `sorry`, no `axiom`.
-/
import LatticeProb.Prob.EfronSteinCountable
import LatticeProb.Prob.GaussianConcentrationL2

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

variable {ι : Type*}

/-- **The spliced difference is supported on a finite set.**  For a finite set `S` the
configuration `comb S ω η` differs from `comb S ω' η` only on `S`.
hence the `ℓ²` sum of the difference is the finite sum over `S`. -/
theorem hasSum_sq_comb_sub {S : Set ι} [DecidablePred (· ∈ S)] (hS : S.Finite)
    (ω ω' η : ι → ℝ) :
    HasSum (fun i : ι => (comb S ω η i - comb S ω' η i) ^ 2)
      (∑ i ∈ hS.toFinset, (ω i - ω' i) ^ 2) := by
  classical
  have h := hasSum_sum_of_ne_finset_zero (α := ℝ) (β := ι)
    (L := SummationFilter.unconditional ι) (s := hS.toFinset)
    (f := fun i : ι => (comb S ω η i - comb S ω' η i) ^ 2) fun i hi => by
      rw [comb_apply_of_notMem (fun h => hi (hS.mem_toFinset.mpr h)),
        comb_apply_of_notMem (fun h => hi (hS.mem_toFinset.mpr h))]
      simp
  have hsum : (∑ i ∈ hS.toFinset, (comb S ω η i - comb S ω' η i) ^ 2)
      = ∑ i ∈ hS.toFinset, (ω i - ω' i) ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      rw [comb_apply_of_mem (hS.mem_toFinset.mp hi),
        comb_apply_of_mem (hS.mem_toFinset.mp hi)]
  rw [hsum] at h
  exact h

/-- **Lipschitz preservation under the conditional expectation.**  If `F` is ℓ²-Lipschitz with
constant `L` and both slices `η ↦ F (comb S ω η)`, `η ↦ F (comb S ω' η)` are integrable,
then `partialInt (fun _ => gaussianReal 0 1) S F` is ℓ²-Lipschitz with the same constant on the
finite coordinate set `S`. -/
theorem abs_partialInt_sub_le {S : Set ι} [DecidablePred (· ∈ S)] (hS : S.Finite)
    {F : (ι → ℝ) → ℝ} {L : ℝ}
    (hLip : ∀ (ω η : ι → ℝ) (M : ℝ), HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * Real.sqrt M)
    (ω ω' : ι → ℝ)
    (h1 : Integrable (fun η => F (comb S ω η)) (gaussLaw ι))
    (h2 : Integrable (fun η => F (comb S ω' η)) (gaussLaw ι)) :
    |partialInt (fun _ : ι => gaussianReal 0 1) S F ω
        - partialInt (fun _ : ι => gaussianReal 0 1) S F ω'|
      ≤ L * Real.sqrt (∑ i ∈ hS.toFinset, (ω i - ω' i) ^ 2) := by
  have hpartial : ∀ (ω : ι → ℝ) (h : Integrable (fun η => F (comb S ω η)) (gaussLaw ι)),
      partialInt (fun _ : ι => gaussianReal 0 1) S F ω
        = ∫ η, F (comb S ω η) ∂(gaussLaw ι) := fun _ _ => rfl
  rw [hpartial ω h1, hpartial ω' h2]
  calc |∫ η, F (comb S ω η) ∂(gaussLaw ι) - ∫ η, F (comb S ω' η) ∂(gaussLaw ι)|
      = |∫ η, (F (comb S ω η) - F (comb S ω' η)) ∂(gaussLaw ι)| := by
        rw [integral_sub h1 h2]
    _ ≤ ∫ η, |F (comb S ω η) - F (comb S ω' η)| ∂(gaussLaw ι) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, L * Real.sqrt (∑ i ∈ hS.toFinset, (ω i - ω' i) ^ 2) ∂(gaussLaw ι) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun η => ?_)
        exact hLip (comb S ω η) (comb S ω' η) _ (hasSum_sq_comb_sub hS ω ω' η)
    _ = L * Real.sqrt (∑ i ∈ hS.toFinset, (ω i - ω' i) ^ 2) := by
        simp [integral_const, Measure.real, measure_univ]

end LatticeProb
