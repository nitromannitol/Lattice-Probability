/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.QuenchedPathLimitReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.PathLawFiniteDimensionalConvergence
import LatticeProb.Bonanno.ReflectedGMS.Limit.HalfLinePathTightness

/-!
# The quenched path limit reduced to window tails and finite-dimensional convergence

This file composes the two halves proved in
`ReflectedGMS/Limit/HalfLinePathTightness.lean` (tightness on the non-compact
time half-line from per-window estimates) and
`ReflectedGMS/Limit/PathLawFiniteDimensionalConvergence.lean` (Prokhorov plus
uniqueness of the cluster point) into the exact convergence assertion
`ReflectedGMS.StatementIngredients.QuenchedWeakLimitAtFixedStart` required by the
`hlimit` input of `ReflectedGMS/InvarianceAssembly.lean`.

**This is a conditional reduction and certifies neither the quenched invariance
principle nor either of its two inputs.**  What it does certify is that the
convergence half of `hlimit` follows from exactly three named, atomic
probabilistic inputs about the diffusively rescaled interpolation laws, taken
uniformly over a set `T` of scales which is a neighbourhood of `0` within the
positive scales:

* `hsize` — a uniform tail for the maximal displacement on each bounded time
  window `[0, m]`;
* `hmod` — a uniform tail for the modulus of continuity on each bounded time
  window `[0, m]`;
* `hfdd` — convergence of every finite-dimensional distribution to the
  corresponding finite-dimensional distribution of the anisotropic Brownian
  target.

No estimate is assumed at, or uniformly up to, scale `0`, and nothing is assumed
about the limiting process beyond `hfdd`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

open StatementIngredients

variable {Environment Vertex : Type*}

/-- **The quenched weak limit at a fixed start from per-window tails and
convergence of the finite-dimensional distributions.**  A conditional
reduction: none of `hsize`, `hmod`, `hfdd` is proved here. -/
theorem quenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict
    (law : Environment → Vertex → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) (environment : Environment) (start : Vertex)
    (e₀ : BouRabeeGwynne.Euc 2) (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Ioi 0))
    (hsize : ∀ (m : ℕ) (η : ℝ≥0∞), 0 < η → ∃ R : ℝ, ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (law environment start) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineSizeFailure e₀ m R) ≤ η)
    (hmod : ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (law environment start) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineModulusFailure m c d) ≤ η)
    (hfdd : ∀ I : Finset ℝ≥0,
      Tendsto (fun ε => (diffusivelyRescaledPathLaw (law environment start) ε).map
          (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f)))
        (nhdsWithin (0 : ℝ≥0) (Ioi 0))
        (𝓝 (target.pathLaw.map
          (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f))))) :
    QuenchedWeakLimitAtFixedStart law target environment start := by
  refine quenchedWeakLimitAtFixedStart_of_isTightMeasureSet_of_tendsto_map_finsetRestrict
    law target environment start
    ((fun ε => diffusivelyRescaledPathLaw (law environment start) ε) '' T) ?_ ?_ hfdd
  · filter_upwards [hT] with ε hε using ⟨ε, hε, rfl⟩
  · refine isTightMeasureSet_halfLine_of_size_and_modulus e₀ _ ?_ ?_
    · intro m η hη
      obtain ⟨Rm, hRm⟩ := hsize m η hη
      refine ⟨Rm, ?_⟩
      rintro ν ⟨ρ, ⟨ε, hε, rfl⟩, rfl⟩
      exact hRm ε hε
    · intro m c hc η hη
      obtain ⟨d, hd, hdm⟩ := hmod m c hc η hη
      refine ⟨d, hd, ?_⟩
      rintro ν ⟨ρ, ⟨ε, hε, rfl⟩, rfl⟩
      exact hdm ε hε

/-- The two-clock form of the previous reduction, i.e. exactly the convergence
content of `ReflectedGMS.InvarianceMainStatement.InterpolatedTwoClockLimit`. -/
theorem twoClockQuenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict
    (expLaw exactLaw :
      Environment → Vertex → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) (environment : Environment) (start : Vertex)
    (e₀ : BouRabeeGwynne.Euc 2) (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Ioi 0))
    (hsizeExp : ∀ (m : ℕ) (η : ℝ≥0∞), 0 < η → ∃ R : ℝ, ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (expLaw environment start) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineSizeFailure e₀ m R) ≤ η)
    (hmodExp : ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (expLaw environment start) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineModulusFailure m c d) ≤ η)
    (hfddExp : ∀ I : Finset ℝ≥0,
      Tendsto (fun ε => (diffusivelyRescaledPathLaw (expLaw environment start) ε).map
          (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f)))
        (nhdsWithin (0 : ℝ≥0) (Ioi 0))
        (𝓝 (target.pathLaw.map
          (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f)))))
    (hsizeExact : ∀ (m : ℕ) (η : ℝ≥0∞), 0 < η → ∃ R : ℝ, ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (exactLaw environment start) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineSizeFailure e₀ m R) ≤ η)
    (hmodExact : ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (exactLaw environment start) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineModulusFailure m c d) ≤ η)
    (hfddExact : ∀ I : Finset ℝ≥0,
      Tendsto (fun ε => (diffusivelyRescaledPathLaw (exactLaw environment start) ε).map
          (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f)))
        (nhdsWithin (0 : ℝ≥0) (Ioi 0))
        (𝓝 (target.pathLaw.map
          (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f))))) :
    TwoClockQuenchedWeakLimitAtFixedStart expLaw exactLaw target environment start :=
  ⟨quenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict
      expLaw target environment start e₀ T hT hsizeExp hmodExp hfddExp,
    quenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict
      exactLaw target environment start e₀ T hT hsizeExact hmodExact hfddExact⟩

end ReflectedGMS.MartingaleLimit
