import LatticeProb.Prob.ExcursionCountLevy
import LatticeProb.Analysis.ExcursionCountShift
import LatticeProb.Analysis.ExcursionCountReflect
import LatticeProb.Prob.CorrelatedBMRationalDescent

/-!
# Lévy's excursion-count formula for the coordinates of a correlated Brownian pair

Let `(L, R)` be a two-sided correlated Brownian pair (`IsCorrelatedBM2 γ μ`) and let `X` be one of its coordinates.
For a fixed time `q`, almost surely, simultaneously for every `t ≥ q`,

  `√(π ε / 2) · #{excursions of X above its running infimum from q, inside [q, t], of length > ε}
      → X q - inf_{[q, t]} X`   as `ε → 0⁺`,

and the same holds backward in time: for every `t ≤ q`, the normalized number of excursions of `X` above its
running infimum read backward from `q`, inside `[t, q]`, tends to `X q - inf_{[t, q]} X`.

The proof transports the one-sided formula for a standard Brownian motion started at `0`
(`ae_tendsto_sqrt_pi_mul_pathExcursionCount`, `ae_exists_nnExtend_lt_sub`) to the restarted increments
`u ↦ X (q + u) - X q` and `u ↦ X (q - u) - X q`, which are standard Brownian motions; the excursion counts of the
restarted path are those of `X` from `q` (`excursionCount_shift`), and the deterministic sandwiches
`tendsto_excursionCount_forwardLadderSet` and `tendsto_excursionCount_backwardLadderSet` pass from first-passage
levels to all times.

## Main results

* `LatticeProb.LadderSet.tendsto_excursionCount_firstPassageBelow_of_restart`: the deterministic transfer of the
  first-passage limits from a restarted path to the original path.
* `LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord`: the two-sided excursion-count formula at every fixed
  rational time, for both coordinates.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

section Restart

variable {X : ℝ → ℝ} {a : ℝ} {f : ℝ≥0 → ℝ}

/-- The extension of the restarted path `f u = X (a + u) - X a` agrees with `u ↦ X (a + u) - X a` on `[0, ∞)`. -/
theorem nnExtend_eq_of_restart (hf : ∀ u : ℝ≥0, f u = X (a + u) - X a) :
    ∀ u : ℝ, 0 ≤ u → nnExtend f u = X (a + u) + -X a := by
  intro u hu
  rw [nnExtend, hf, Real.coe_toNNReal u hu, sub_eq_add_neg]

/-- If the restarted path `f u = X (a + u) - X a` is unbounded below, then `X` is unbounded below on `[a, ∞)`. -/
theorem forall_exists_lt_sub_of_restart (hf : ∀ u : ℝ≥0, f u = X (a + u) - X a)
    (hunb : ∀ b : ℝ, ∃ s, (0 : ℝ) ≤ s ∧ nnExtend f s < nnExtend f 0 - b) :
    ∀ b : ℝ, ∃ s, a ≤ s ∧ X s < X a - b := by
  intro b
  obtain ⟨s, hs, hlt⟩ := hunb b
  have h1 := nnExtend_eq_of_restart hf s hs
  have h0 := nnExtend_eq_of_restart hf 0 le_rfl
  rw [add_zero] at h0
  exact ⟨a + s, by linarith, by linarith⟩

/-- **Transfer of the first-passage limits from a restarted path.** If the restarted path `f u = X (a + u) - X a`
is unbounded below and its normalized excursion counts `√(π ε / 2) J_ε(b)` up to its first passage below `-b`
converge to `b` for every rational `b > 0`, then the normalized excursion counts of `X` above its running minimum
from `a`, up to the first passage of `X` below `X a - b`, converge to `b` as well. -/
theorem tendsto_excursionCount_firstPassageBelow_of_restart (hf : ∀ u : ℝ≥0, f u = X (a + u) - X a)
    (hunb : ∀ b : ℝ, ∃ s, (0 : ℝ) ≤ s ∧ nnExtend f s < nnExtend f 0 - b)
    (hlev : ∀ b : ℚ, 0 < b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (pathExcursionCount f b ε : ℝ)) (𝓝[>] 0) (𝓝 (b : ℝ))) :
    ∀ b : ℚ, 0 < b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a (firstPassageBelow X a b) ε : ℝ)) (𝓝[>] 0) (𝓝 (b : ℝ)) := by
  intro b hb
  refine (hlev b hb).congr fun ε => ?_
  rw [pathExcursionCount,
    excursionCount_shift (nnExtend_eq_of_restart hf) (forall_exists_lt_sub_of_restart hf hunb b) ε]

end Restart

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Lévy's formula at all rational levels.** For a standard real Brownian motion with continuous paths, almost
surely `√(π ε / 2) J_ε(b) → b` as `ε → 0⁺`, simultaneously for every rational `b > 0`. -/
theorem ae_forall_rat_tendsto_sqrt_pi_mul_pathExcursionCount [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ ω ∂P, ∀ b : ℚ, 0 < b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (pathExcursionCount (fun t => B t ω) b ε : ℝ)) (𝓝[>] 0) (𝓝 (b : ℝ)) := by
  rw [ae_all_iff]
  intro b
  by_cases hb : 0 < b
  · filter_upwards [ae_tendsto_sqrt_pi_mul_pathExcursionCount hB hm hcont (Rat.cast_pos.2 hb)] with ω hω
    exact fun _ => hω
  · exact Eventually.of_forall fun _ h => absurd h hb

end LatticeProb.LadderSet

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT LatticeProb.LadderSet

variable {γ : ℝ} {μ : Measure Path2}

/-- **Lévy's excursion-count formula for a correlated Brownian pair.** For each coordinate `X` of a correlated
Brownian pair and each rational time `q`, almost surely: for every `t ≥ q`, the number of excursions of `X` above its
running minimum from `q` inside `[q, t]` of length larger than `ε`, multiplied by `√(π ε / 2)`, tends to
`X q - min_{[q, t]} X` as `ε → 0⁺`; and for every `t ≤ q`, the same holds for the excursions above the running
minimum read backward from `q`, inside `[t, q]`, with limit `X q - min_{[t, q]} X`. -/
theorem ae_excursionCount_lrCoord (hμ : IsCorrelatedBM2 γ μ) :
    ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (forwardLadderSet (fun s => lrCoord i s ω) q) q t ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc (q : ℝ) t)))) ∧
      ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (backwardLadderSet (fun s => lrCoord i s ω) q) t q ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc t (q : ℝ)))) := by
  intro i q
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hcX : ∀ ω : Path2, Continuous fun s => lrCoord i s ω := by
    intro ω
    by_cases hi : i = 0
    · subst hi
      simp only [lrCoord, ↓reduceIte]
      exact continuous_fst.comp ω.continuous
    · simp only [lrCoord, hi, ↓reduceIte]
      exact continuous_snd.comp ω.continuous
  have hWB := shiftedCoordinate_isBrownianReal hμ i (q : ℝ)
  have hWm : ∀ t, Measurable (shiftedCoordinate i q t) := fun t =>
    (measurable_lrCoord (i, (q : ℝ) + (t : ℝ))).sub (measurable_lrCoord (i, (q : ℝ)))
  have hWc : ∀ ω, Continuous fun t => shiftedCoordinate i q t ω := fun ω => by
    change Continuous (fun t : ℝ≥0 => lrCoord i ((q : ℝ) + (t : ℝ)) ω - lrCoord i q ω)
    exact ((hcX ω).comp (continuous_const.add continuous_subtype_val)).sub continuous_const
  have hVB := reversedCoordinate_isBrownianReal hμ i (q : ℝ)
  have hVm : ∀ t, Measurable (reversedCoordinate i q t) := fun t =>
    (measurable_lrCoord (i, (q : ℝ) - (t : ℝ))).sub (measurable_lrCoord (i, (q : ℝ)))
  have hVc : ∀ ω, Continuous fun t => reversedCoordinate i q t ω := fun ω => by
    change Continuous (fun t : ℝ≥0 => lrCoord i ((q : ℝ) - (t : ℝ)) ω - lrCoord i q ω)
    exact ((hcX ω).comp (continuous_const.sub continuous_subtype_val)).sub continuous_const
  filter_upwards [ae_forall_rat_tendsto_sqrt_pi_mul_pathExcursionCount hWB hWm hWc,
    ae_exists_nnExtend_lt_sub hWB hWm, ae_forall_rat_tendsto_sqrt_pi_mul_pathExcursionCount hVB hVm hVc,
    ae_exists_nnExtend_lt_sub hVB hVm] with ω hlW huW hlV huV
  have hfW : ∀ u : ℝ≥0, shiftedCoordinate i q u ω =
      (fun s => lrCoord i s ω) ((q : ℝ) + u) - (fun s => lrCoord i s ω) (q : ℝ) := fun _ => rfl
  have hfV : ∀ u : ℝ≥0, reversedCoordinate i q u ω =
      (fun s => lrCoord i (-s) ω) (-(q : ℝ) + u) - (fun s => lrCoord i (-s) ω) (-(q : ℝ)) := fun u => by
    simp only [neg_neg, show -(-(q : ℝ) + (u : ℝ)) = q - u by ring]
    rfl
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact tendsto_excursionCount_forwardLadderSet (hcX ω)
      (forall_exists_lt_sub_of_restart (X := fun s => lrCoord i s ω) (a := (q : ℝ))
        (f := fun u => shiftedCoordinate i q u ω) hfW huW)
      (tendsto_excursionCount_firstPassageBelow_of_restart (X := fun s => lrCoord i s ω) (a := (q : ℝ))
        (f := fun u => shiftedCoordinate i q u ω) hfW huW hlW) ht
  · refine tendsto_excursionCount_backwardLadderSet (a := (q : ℝ)) (hcX ω) (fun b => ?_)
      (tendsto_excursionCount_firstPassageBelow_of_restart (X := fun s => lrCoord i (-s) ω) (a := -(q : ℝ))
        (f := fun u => reversedCoordinate i q u ω) hfV huV hlV) ht
    obtain ⟨s, hs, hlt⟩ := forall_exists_lt_sub_of_restart (X := fun s => lrCoord i (-s) ω) (a := -(q : ℝ))
      (f := fun u => reversedCoordinate i q u ω) hfV huV b
    refine ⟨-s, by linarith, ?_⟩
    simpa only [neg_neg] using hlt

end LatticeProb.CorrelatedBM
