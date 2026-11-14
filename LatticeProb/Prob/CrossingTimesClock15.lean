/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesClock13
import LatticeProb.Prob.CrossingTimesClock14

/-!
# One functional determines the inverse crossing clock of a time-changed Brownian motion family

Let `K` be a continuous family of path laws on `ℝ ^ d` satisfying the Markov property at
deterministic times, such that for every starting point `z` the law `K z` is the law of a
time-changed Brownian motion `X = B ∘ τ` started at `z` (the time change `τ` being almost surely
continuous, strictly increasing, unbounded and vanishing at `0`).  There is a threshold `m`, depending
only on `d`, such that for every `s ≥ 0` the inverse crossing clock `A_s` of the path is, under
every `K z`, one fixed measurable functional of the path read in its crossing clock, and the
increments of `t ↦ A_t` are produced by the same functional on the shifted clock-read path.

* `exists_clockFunctional_timeChangedBM`: the packaging theorem; every hypothesis of
  `exists_clockFunctional_of_attained` (start, good clock, shift identity, attainment, continuity
  of the inverse clock) is supplied from the coupling data.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

universe u

/-- **The inverse crossing clock of a Markov family of time-changed Brownian motions.**  There is
`m ∈ (0, ∞)`, depending only on `d`, such that for every continuous family `K` of path laws with the
Markov property at deterministic times whose members `K z` are the laws of time-changed Brownian
motions `X = B ∘ τ` started at `z`, and every `s ≥ 0`, there is a measurable functional `F` of a
path on `ℝ≥0` with `A_s = F (clock-read path)` almost surely under every `K z`, and
`A_{t+s} = A_t + F (clock-read shifted path)` almost surely under every `K z`, for all `t ≥ 0`. -/
theorem exists_clockFunctional_timeChangedBM (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧
      ∀ {K : EuclideanSpace ℝ (Fin d) → ProbabilityMeasure C(ℝ≥0, EuclideanSpace ℝ (Fin d))},
        Continuous K → (∀ z t, MarkovAt K z t) →
        (∀ z, ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
            (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (τ : Ω → ℝ≥0 → ℝ≥0)
            (X : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
          IsBrownianSpace d z B Q ∧ (∀ t, StronglyMeasurable (B t)) ∧
          (∀ ω, Continuous fun t => B t ω) ∧ AEMeasurable X Q ∧
          (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
            Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B (τ ω u) ω) ∧
          (K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))) = Q.map X) →
        ∀ s : ℝ≥0, ∃ F : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ, Measurable F ∧
          (∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
            (pathClockInv m x s).toReal = F fun t => clockPath m (fun u => x u) t) ∧
          ∀ z (t : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
            (pathClockInv m x (t + s)).toReal = (pathClockInv m x t).toReal +
              F fun q => clockPath m (fun u => x u) (t + q) := by
  obtain ⟨m, hm0, hmt, hm⟩ := exists_ae_crossClock_eq_self_shift.{u} d hd
  refine ⟨m, hm0, hmt, fun {K} hK hM hcoup s => ?_⟩
  have key : ∀ z, (∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))), x 0 = z) ∧
      (∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
        GoodClock (crossClock m fun u => x u)) ∧
      (∀ t s : ℝ≥0, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
        ShiftIdentity m t s x) ∧
      (∀ t : ℝ≥0, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
        (t : ℝ≥0∞) ≤ crossClock m (fun w => x w) (pathClockInv m x t).toNNReal) := by
    intro z
    obtain ⟨Ω, mΩ, Q, hQ, B, τ, X, hBM, hmeas, hcont, hX, hτ, hKz⟩ := hcoup z
    obtain ⟨hB, hBt⟩ := hm Ω Q z B hBM hmeas hcont
    rw [hKz]
    refine ⟨?_, ae_map_goodClock (B := fun ω t => B t ω) hX hτ hB,
      fun t s => ae_map_shiftIdentity (B := fun ω t => B t ω) hX hτ hB t s (hBt t),
      fun t => ae_map_attained (B := fun ω t => B t ω) hX hτ hB t⟩
    rw [ae_map_iff hX (isClosed_eq (continuous_eval_const (0 : ℝ≥0)) continuous_const).measurableSet]
    filter_upwards [hτ, hBM.start] with ω hω hs
    obtain ⟨-, -, h0, -, hx⟩ := hω
    rw [hx 0, h0]
    exact hs
  exact exists_clockFunctional_of_attained hK hM m (fun z => (key z).1) (fun z => (key z).2.1)
    (fun z t s => (key z).2.2.1 t s) (fun z t => (key z).2.2.2 t)
    (fun z => ae_continuous_pathClockInv_of_good m (key z).2.1) s

end LatticeProb

end
