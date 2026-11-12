/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_18 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_22Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.18 (`Blueprint.DFGPSProp3_18`) (task P2-DFA7)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Proposition 3.18
(`prop-holder-uniform`, T:2247–2254), proof T:2383–2385: "Combine Lemmas 3.20 and 3.22."
The upper bound comes from the first display of Lemma 3.20 since
`D_h(u,v) ≤ D_h(u,v; B_{2|u−v|}(u))` (the case `u = v` is trivial), the lower bound is
Lemma 3.22; the two polynomial rates combine with the smaller exponent.

Main results: `dfgpsLem3_20Ball_of` (= `L320.lem3_20_ball_of`), `L322.dfgpsLem3_22_of`, and
`dfgpsProp3_18_of`, all from the cited lemmas 3.19 (ball part) and 3.21 in their
constants-first forms `Lem3_19U`, `Lem3_21U`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint

/-- two polynomially-high-probability events hold simultaneously with polynomially high
probability -/
theorem PolyHighProbU.inter {E₁ E₂ : ℝ → ℝ → Set DistC} (H₁ : PolyHighProbU E₁)
    (H₂ : PolyHighProbU E₂) : PolyHighProbU fun ε 𝕣 => E₁ ε 𝕣 ∩ E₂ ε 𝕣 := by
  obtain ⟨p₁, hp₁, C₁, ε₁, hε₁, H₁⟩ := H₁
  obtain ⟨p₂, hp₂, C₂, ε₂, hε₂, H₂⟩ := H₂
  refine ⟨min p₁ p₂, lt_min hp₁ hp₂, max C₁ 0 + max C₂ 0, min (min ε₁ ε₂) 1,
    lt_min (lt_min hε₁ hε₂) one_pos, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣
  have hε0 : 0 < ε := hε.1
  have hεa : ε < ε₁ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεb : ε < ε₂ := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := (hε.2.trans_le (min_le_right _ _)).le
  have key : ∀ (C p : ℝ), min p₁ p₂ ≤ p →
      ENNReal.ofReal (C * ε ^ p) ≤ ENNReal.ofReal (max C 0 * ε ^ min p₁ p₂) := by
    intro C p hp
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ε ^ p ≤ ε ^ min p₁ p₂ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hp
    have h2 : 0 ≤ ε ^ p := (Real.rpow_pos_of_pos hε0 _).le
    calc C * ε ^ p ≤ max C 0 * ε ^ p := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
      _ ≤ max C 0 * ε ^ min p₁ p₂ := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  rw [preimage_inter, compl_inter]
  refine (measure_union_le _ _).trans ?_
  calc P (h ⁻¹' E₁ ε 𝕣)ᶜ + P (h ⁻¹' E₂ ε 𝕣)ᶜ
      ≤ ENNReal.ofReal (max C₁ 0 * ε ^ min p₁ p₂) + ENNReal.ofReal (max C₂ 0 * ε ^ min p₁ p₂) :=
        add_le_add ((H₁ P h hh ε ⟨hε0, hεa⟩ 𝕣 h𝕣).trans (key C₁ p₁ (min_le_left _ _)))
          ((H₂ P h hh ε ⟨hε0, hεb⟩ 𝕣 h𝕣).trans (key C₂ p₂ (min_le_right _ _)))
    _ = ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * ε ^ min p₁ p₂) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

/-- monotonicity of `PolyHighProbU` in the events -/
theorem PolyHighProbU.mono_aux {E E' : ℝ → ℝ → Set DistC} (H : PolyHighProbU E)
    (hEE' : ∀ ε 𝕣, ∀ g ∈ E ε 𝕣, g ∈ E' ε 𝕣) : PolyHighProbU E' := by
  obtain ⟨p, hp, C, ε₀, hε₀, H⟩ := H
  refine ⟨p, hp, C, ε₀, hε₀, fun P _ h hh ε hε 𝕣 h𝕣 => ?_⟩
  refine (measure_mono ?_).trans (H P h hh ε hε 𝕣 h𝕣)
  exact compl_subset_compl.2 (preimage_mono (hEE' ε 𝕣))

/-- **DFGPS Proposition 3.18** from Lemmas 3.19 (ball part) and 3.21, via Lemmas 3.20 (first
display) and 3.22 -/
theorem dfgpsProp3_18_of (h19 : Lem3_19U) (h21 : Lem3_21U) : DFGPSProp3_18 := by
  intro γ hγ hγ2 D c hD K hK χ χ' hχ hχQ hχ'
  refine PolyHighProbU.mono_aux (PolyHighProbU.inter
    (L320.lem3_20_ball_of h19 γ hγ hγ2 D c hD K hK χ hχ hχQ)
    (L322.dfgpsLem3_22_of h21 γ hγ hγ2 D c hD K hK χ' hχ')) ?_
  intro ε 𝕣 g ⟨hup, hlow⟩ u hu v hv hd
  refine ⟨hlow u hu v hv hd, ?_⟩
  set a := (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0)
  have hx0 : 0 ≤ ‖(u - v) / 𝕣‖ ^ χ := Real.rpow_nonneg (norm_nonneg _) _
  rcases eq_or_ne u v with rfl | huv
  · rw [show (D g).1 (u, u) = 0 from (D g).2.self_eq_zero u, mul_zero]; exact hx0
  rcases lt_or_ge a 0 with ha | ha
  · exact (mul_nonpos_of_nonpos_of_nonneg ha.le (ContMetric.nonneg _ _ _)).trans hx0
  have h1 := hup u hu v hv huv hd
  have h2 : ENNReal.ofReal ((D g).1 (u, v)) ≤
      (D g).internal (Metric.ball u (2 * ‖u - v‖)) u v := by
    rw [← ContMetric.edist_pt]; exact MetricGeometry.edist_le_internalEDist _ _ _
  have h3 : ENNReal.ofReal (a * (D g).1 (u, v)) ≤ ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ) := by
    rw [ENNReal.ofReal_mul ha]
    exact (mul_le_mul_right h2 _).trans h1
  exact (ENNReal.ofReal_le_ofReal_iff hx0).1 h3

end LQGMetric.DFGPS
