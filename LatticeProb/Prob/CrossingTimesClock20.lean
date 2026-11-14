/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesClock15
import LatticeProb.Prob.CrossingTimesClock18
import LatticeProb.Prob.CrossingTimesStrictInverse

/-!
# The inverse crossing clock of a time-changed Brownian motion is an adapted functional of the Brownian path

Let `K` be a continuous family of path laws on `ℝ ^ d` satisfying the Markov property at deterministic
times, such that for every starting point `z` the law `K z` is the law of a time-changed Brownian motion
`X = B ∘ τ` started at `z`.  For the threshold `m` of `exists_clockFunctional_timeChangedBM` and every
`s ≥ 0`, the inverse crossing clock `A_s` of the path is the functional `F_s` of the path read in its
crossing clock, and this functional is almost surely equal, for the law of the clock-read path, to a
function measurable for the past of the clock-read path up to time `s`.

* `exists_goodAdaptedClockFunctional_timeChangedBM`: the packaging theorem, with the same threshold `m` as in
  the identification of the crossing clock of Brownian motion.  It adds to the adaptedness statement that,
  almost surely under every `K z`, the crossing clock of the path is a good clock, so that the inverse
  crossing clock is nondecreasing and continuous.  Its first conclusion, which does
  not involve `K`, identifies the law of the clock-read path of any such coupling `X = B ∘ τ` with the law
  of the Brownian motion `B`; the second conclusion adds the adaptedness of `F_s` to the conclusion of
  `exists_clockFunctional_timeChangedBM`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

universe u

/-- **The inverse crossing clock of a Markov family of time-changed Brownian motions is adapted.**
There is `m ∈ (0, ∞)`, depending only on `d`, such that

* for every coupling `X = B ∘ τ` of a Brownian motion `B` and a time change `τ` (continuous, strictly
  increasing, from `0` and unbounded), the clock-read path of `X` has the law of `B`;
* for every continuous Markov family `K` of laws of such time-changed Brownian motions, and every
  `s ≥ 0`, there is a measurable functional `F` with `A_s = F (clock-read path)` almost surely under every
  `K z`, the shift identity `A_{t+s} = A_t + F (clock-read shifted path)`, and, for every `z`, a version of
  `F` that is measurable for the past of the clock-read path up to time `s`;
* for every `z`, almost surely under `K z`, the crossing clock of the path is a good clock, and the inverse
  crossing clock of the path is strictly increasing and unbounded along the nonnegative rationals
  (`InvClockStrict`). -/
theorem exists_goodAdaptedClockFunctional_timeChangedBM (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
          (z : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (τ : Ω → ℝ≥0 → ℝ≥0)
          (X : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
        IsBrownianSpace d z B Q → (∀ t, StronglyMeasurable (B t)) →
        (∀ ω, Continuous fun t => B t ω) → AEMeasurable X Q →
        (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
          Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B (τ ω u) ω) →
        (Q.map X).map (clockRead m) = Q.map fun ω t => B t ω) ∧
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
        (∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
          GoodClock (crossClock m fun u => x u)) ∧
        (∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))), InvClockStrict m x) ∧
        ∀ s : ℝ≥0, ∃ F : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ, Measurable F ∧
          (∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
            (pathClockInv m x s).toReal = F fun t => clockPath m (fun u => x u) t) ∧
          (∀ z (t : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
            (pathClockInv m x (t + s)).toReal = (pathClockInv m x t).toReal +
              F fun q => clockPath m (fun u => x u) (t + q)) ∧
          ∀ z, ∃ h : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ≥0,
            Measurable[coordPast (EuclideanSpace ℝ (Fin d)) s] h ∧
            (fun f => Real.toNNReal (F f)) =ᵐ[(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))).map
              (clockRead m)] h := by
  obtain ⟨m, hm0, hmt, hm⟩ := exists_ae_crossClock_eq_self_shift.{u} d hd
  refine ⟨m, hm0, hmt, ?_, ?_⟩
  · intro Ω _ Q _ z B τ X hBM hmeas hcont hX hτ
    exact map_clockPath_eq (B := fun ω t => B t ω) hX hτ (hm Ω Q z B hBM hmeas hcont).1
  · intro K hK hM hcoup
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
    have hstrict : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
        InvClockStrict m x := by
      intro z
      obtain ⟨Ω, mΩ, Q, hQ, B, τ, X, hBM, hmeas, hcont, hX, hτ, hKz⟩ := hcoup z
      obtain ⟨hB, -⟩ := hm Ω Q z B hBM hmeas hcont
      rw [hKz]
      exact ae_map_invClockStrict (B := fun ω t => B t ω) hX hτ hB
    have hcont : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))),
        Continuous fun u : ℝ≥0 => (pathClockInv m x u).toReal := fun z =>
      ae_continuous_pathClockInv_of_good m (key z).2.1
    refine ⟨fun z => (key z).2.1, hstrict, fun s => ?_⟩
    obtain ⟨F, hF, hFA, hFshift⟩ := exists_clockFunctional_of_attained hK hM m
      (fun z => (key z).1) (fun z => (key z).2.1) (fun z t s => (key z).2.2.1 t s)
      (fun z t => (key z).2.2.2 t) hcont s
    exact ⟨F, hF, hFA, hFshift, fun z =>
      exists_measurable_coordPast_ae_eq_map_clockRead hK (hM z) m
        (fun t s => (key z).2.2.1 t s) (fun t => (key z).2.2.2 t) (hcont z) s hF (hFA z)⟩

end LatticeProb

end
