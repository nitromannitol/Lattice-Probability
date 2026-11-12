/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedLimit
import LatticeProb.Prob.WeakLimitSubalgebra
import LatticeProb.Prob.WeakLimitCylinder
import LatticeProb.Topology.PolishContinuousMap

/-!
# Weak limit of the Brownian motion with drift conditioned to stay above `-δ`

Let `B` be a real Brownian motion with continuous paths and `c > 0`.  The laws on `C(ℝ≥0, ℝ)`
of `B` under `P (· | B t + c t > -δ for all t)` form a tight family as `δ → 0+`, and the
conditional averages of bounded Lipschitz cylinder functionals converge.  Hence the laws converge
weakly along `δ → 0+` to a probability measure.

* `LatticeProb.exists_tendsto_stayAboveAvg_of_isLipCylinder`: convergence of the conditional
  averages of a bounded Lipschitz cylinder functional (values in `[-M, M]`).
* `LatticeProb.exists_weakLimit_stayAbove`: the weak limit as `δ → 0+` of the conditioned laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Affine change of the integrand: the conditional average of `(Ψ + M)/N` is
`(avg Ψ + M)/N`, provided `Ψ` is bounded and measurable and the event has positive mass. -/
theorem stayAboveAvg_affine [IsProbabilityMeasure P] {c l : ℝ} (hpos : 0 < P (stayAboveSet B c l))
    {Ψ : Ω → ℝ} (hΨ : Measurable Ψ) {M N : ℝ} (hM : ∀ ω, |Ψ ω| ≤ M) (hN : 0 < N) :
    stayAboveAvg P B c l (fun ω => (Ψ ω + M) / N) =
      (stayAboveAvg P B c l Ψ + M) / N := by
  have hint : Integrable Ψ (P.restrict (stayAboveSet B c l)) :=
    Integrable.mono' (integrable_const M) hΨ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hM ω)
  have hm : 0 < (P (stayAboveSet B c l)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  unfold stayAboveAvg
  rw [integral_div, integral_add hint (integrable_const M), setIntegral_const]
  have : (P.real (stayAboveSet B c l)) = (P (stayAboveSet B c l)).toReal := rfl
  rw [smul_eq_mul, this]
  field_simp

/-- **Convergence of the conditional averages of a bounded Lipschitz cylinder functional.** -/
theorem exists_tendsto_stayAboveAvg_of_isLipCylinder [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {Φ : (ℝ≥0 → ℝ) → ℝ}
    (hΦ : IsLipCylinder Φ) :
    ∃ a : ℝ, Tendsto (fun δ : ℝ => stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω)))
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  obtain ⟨hmΦ, I, K, M, hK, hM, hlip⟩ := hΦ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM fun _ => 0)
  set N : ℝ := 2 * M + 1 with hNdef
  have hN : 0 < N := by positivity
  set Φ' : (ℝ≥0 → ℝ) → ℝ := fun g => (Φ g + M) / N with hΦ'
  have hΦ'm : Measurable Φ' := (hmΦ.add_const M).div_const N
  have h0 : ∀ g, 0 ≤ Φ' g := fun g => by
    have := (abs_le.1 (hM g)).1
    exact div_nonneg (by linarith) hN.le
  have h1 : ∀ g, Φ' g ≤ 1 := fun g => by
    have := (abs_le.1 (hM g)).2
    rw [hΦ', div_le_one hN]
    linarith
  obtain ⟨a', ha'⟩ := exists_tendsto_stayAboveAvg hB hm hcont hc hΦ'm h0 h1
    (I := (I : Set ℝ≥0)) (T := I.sup id) (fun t ht => Finset.le_sup (f := id) ht)
    (div_nonneg hK hN.le) (K := K / N) (fun g g' r hr h => by
      have e : Φ' g - Φ' g' = (Φ g - Φ g') / N := by simp only [hΦ']; ring
      rw [e, abs_div, abs_of_pos hN, div_le_iff₀ hN]
      calc |Φ g - Φ g'| ≤ K * r := hlip g g' r hr fun t ht => h t (by exact_mod_cast ht)
        _ = K / N * r * N := by field_simp)
  refine ⟨N * a' - M, ?_⟩
  have hlim : Tendsto (fun δ : ℝ => N * stayAboveAvg P B c δ (fun ω => Φ' (fun t => B t ω)) - M)
      (𝓝[>] (0 : ℝ)) (𝓝 (N * a' - M)) := (ha'.const_mul N).sub_const M
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hpos := measure_stayAbove_pos hB hm hcont hc (Set.mem_Ioi.1 hδ)
  have hΨ : Measurable fun ω => Φ (fun t => B t ω) := hmΦ.comp (measurable_pi_iff.2 hm)
  have := stayAboveAvg_affine (B := B) (c := c) (l := δ) hpos hΨ (fun ω => hM _) hN
  have e : (fun ω => Φ' (fun t => B t ω)) = fun ω => (Φ (fun t => B t ω) + M) / N := rfl
  rw [e, this]
  field_simp
  ring

/-- **Weak limit of the conditioned laws.**  For a real Brownian motion `B` with continuous paths
and `c > 0`, the laws on `C(ℝ≥0, ℝ)` of `B` under `P (· | B t + c t > -δ for all t)` converge
weakly as `δ → 0+` to a probability measure. -/
theorem exists_weakLimit_stayAbove [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) :
    ∃ ν : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure ν ∧
      ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto (fun δ : ℝ => ∫ x, f x ∂((ProbabilityTheory.cond P
        (stayAboveSet B c δ)).map (pathMap B hcont))) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂ν)) := by
  have := polishSpace_continuousMap ℝ≥0 ℝ
  have hpm : Measurable (pathMap B hcont) := measurable_pathMap _ hm hcont
  refine exists_tendsto_of_isTightMeasureSet_subalgebra (E := C(ℝ≥0, ℝ)) (l := 𝓝[>] (0 : ℝ))
    (s := Set.Ioi 0) self_mem_nhdsWithin
    (μ := fun δ : ℝ => (ProbabilityTheory.cond P (stayAboveSet B c δ)).map (pathMap B hcont))
    (fun δ hδ => ?_) (isTightMeasureSet_stayAbove_law_base hB hm hcont hc)
    (lipCylinderSubalgebra ℝ≥0) (separatesPoints_lipCylinderSubalgebra ℝ≥0) ?_
  · have hpos := measure_stayAbove_pos hB hm hcont hc (Set.mem_Ioi.1 hδ)
    have : IsProbabilityMeasure (ProbabilityTheory.cond P (stayAboveSet B c δ)) :=
      cond_isProbabilityMeasure_of_finite hpos.ne' (measure_ne_top _ _)
    infer_instance
  · intro g hg
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg
    obtain ⟨a, ha⟩ := exists_tendsto_stayAboveAvg_of_isLipCylinder hB hm hcont hc hΦ
    refine ⟨a, ha.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hpos := measure_stayAbove_pos hB hm hcont hc (Set.mem_Ioi.1 hδ)
    rw [integral_map hpm.aemeasurable g.continuous.aestronglyMeasurable]
    unfold ProbabilityTheory.cond stayAboveAvg
    rw [integral_smul_measure]
    simp only [hgΦ]
    rw [ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]
    rfl

end LatticeProb
