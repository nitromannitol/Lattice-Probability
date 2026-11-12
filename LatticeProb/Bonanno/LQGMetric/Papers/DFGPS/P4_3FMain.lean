/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3FMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3FDet
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Prob
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimatesF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3 for filled balls (task P2-DFA10b, decision D68)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Proposition 4.3
(`prop-geo-bdy`, T:2593–2600) and its proof (T:2683–2744), for filled balls
(`Blueprint.DFGPSProp4_3F`):
* Step 1 (T:2685–2697): the event `G^ε_𝕣` with `M̃ = max(M, p) + 1`, `ζ = min(1/2, 1/(4M))`
  (`P43.prob_regG`, from Lemmas 4.4 and 4.5);
* Steps 2–3 (T:2699–2741): on `G^ε_𝕣` the area is `≤ 2 nB π (5ε^{1−ζ}𝕣)²` (`P43.det_bound`);
* conclusion (T:2742–2744): `nB = O(log ε⁻¹)`, so the bound is `≤ ε^{2 − 1/M} 𝕣²` for small `ε`
  (`P43.eventually_area`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint L45

/-- (T:2742–2744) `nB = O(log ε⁻¹)` and `2 nB π (5 ε^{1−ζ})² ≤ ε^{2 − 1/M}` for small `ε` -/
theorem eventually_area {C A M ζ : ℝ} (hC : 1 < C) (hA : 0 < A) (hM : 0 < M)
    (hζ : 2 * ζ ≤ 1 / (2 * M)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ((2 * nB C ε A : ℕ) : ℝ) * (Real.pi * (5 * ε ^ (1 - ζ)) ^ 2) ≤ ε ^ (2 - 1 / M) := by
  set a := 1 / (2 * M) with ha
  have ha0 : 0 < a := by positivity
  set b := Real.log (1 + C⁻¹) with hb
  have hb0 : 0 < b := Real.log_pos (by have := inv_pos.2 (by linarith : (0 : ℝ) < C); linarith)
  have hlC : 0 < Real.log C := Real.log_pos hC
  set c₁ := 50 * Real.pi * (3 + Real.log C / b)
  set c₂ := 50 * Real.pi * A / b
  set g : ℝ → ℝ := fun ε => c₁ * ε ^ a - c₂ * (Real.log ε * ε ^ a)
  have h1 : Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 a (Or.inr ha0.le)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [Real.zero_rpow ha0.ne'] at this
  have hg : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have := (h1.const_mul c₁).sub ((tendsto_log_mul_rpow_nhdsGT_zero ha0).const_mul c₂)
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), g ε < 1 := hg.eventually (gt_mem_nhds one_pos)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, Hδ⟩ := hev
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun ε hε hεδ => ?_⟩
  have hε1 : ε < 1 := hεδ.trans_le (min_le_right _ _)
  have hdε : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ.trans_le (min_le_left _ _)
  have hgε : g ε < 1 := Hδ hdε hε
  have hlε : Real.log ε < 0 := Real.log_neg hε hε1
  -- `nB ≤ 3 + (log C − A log ε)/b`
  have hX : Real.log (C * ε ^ (-A)) / b = (Real.log C - A * Real.log ε) / b := by
    rw [Real.log_mul (by linarith) (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε]; ring
  have hX0 : 0 ≤ (Real.log C - A * Real.log ε) / b := div_nonneg (by nlinarith) hb0.le
  have hnB : ((nB C ε A : ℕ) : ℝ) ≤ 3 + (Real.log C - A * Real.log ε) / b := by
    have := Nat.floor_le (hX ▸ hX0 : 0 ≤ Real.log (C * ε ^ (-A)) / b)
    show ((⌊Real.log (C * ε ^ (-A)) / b⌋₊ + 3 : ℕ) : ℝ) ≤ _
    push_cast
    rw [hX] at this ⊢
    linarith
  -- `(5 ε^{1−ζ})² ≤ 25 ε^a ε^{2−1/M}`
  have hpow : (ε ^ (1 - ζ)) ^ 2 = ε ^ (2 - 1 / M) * ε ^ (1 / M - 2 * ζ) := by
    rw [← Real.rpow_mul_natCast hε.le, ← Real.rpow_add hε]; congr 1; push_cast; ring
  have hle : ε ^ (1 / M - 2 * ζ) ≤ ε ^ a :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by
      have : 1 / M = 2 * a := by rw [ha]; field_simp
      linarith)
  have hE : 0 < ε ^ (2 - 1 / M) := Real.rpow_pos_of_pos hε _
  have hEa : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have key : ((2 * nB C ε A : ℕ) : ℝ) * (Real.pi * (5 * ε ^ (1 - ζ)) ^ 2) ≤
      g ε * ε ^ (2 - 1 / M) := by
    have e1 : ((2 * nB C ε A : ℕ) : ℝ) * (Real.pi * (5 * ε ^ (1 - ζ)) ^ 2) =
        50 * Real.pi * (nB C ε A : ℝ) * (ε ^ (2 - 1 / M) * ε ^ (1 / M - 2 * ζ)) := by
      rw [← hpow]; push_cast; ring
    have e2 : g ε * ε ^ (2 - 1 / M) =
        50 * Real.pi * (3 + (Real.log C - A * Real.log ε) / b) * (ε ^ (2 - 1 / M) * ε ^ a) := by
      simp only [g, c₁, c₂]; field_simp; ring
    rw [e1, e2]
    have hnB0 : (0 : ℝ) ≤ nB C ε A := Nat.cast_nonneg _
    have hp : 0 ≤ 50 * Real.pi := by positivity
    calc 50 * Real.pi * (nB C ε A : ℝ) * (ε ^ (2 - 1 / M) * ε ^ (1 / M - 2 * ζ))
        ≤ 50 * Real.pi * (nB C ε A : ℝ) * (ε ^ (2 - 1 / M) * ε ^ a) := by gcongr
      _ ≤ _ := by gcongr
  calc _ ≤ g ε * ε ^ (2 - 1 / M) := key
    _ ≤ 1 * ε ^ (2 - 1 / M) := by gcongr
    _ = _ := one_mul _

end P43

open P43 Blueprint in
/-- **DFGPS Proposition 4.3 for filled balls** (T:2593–2600, proof T:2683–2744; D68) -/
theorem dfgpsProp4_3F_of (h31a : LMLem3_1a) (hS : DFGPSScaling) : DFGPSProp4_3F := by
  intro γ hγ hγ2 D c hD M hM p hp
  set ζ := min (1 / 2 : ℝ) (1 / (4 * M)) with hζ
  have hζ0 : 0 < ζ := lt_min (by norm_num) (by positivity)
  have hζ1 : ζ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hζ2 : 2 * ζ ≤ 1 / (2 * M) := by
    have := min_le_right (1 / 2 : ℝ) (1 / (4 * M))
    have e : 1 / (2 * M) = 2 * (1 / (4 * M)) := by field_simp; ring
    rw [e]; linarith
  set M' := max M p + 1 with hM'
  have hM'0 : 0 < M' := by have := le_max_left M p; linarith
  obtain ⟨C, A, hC, hA, K, ε₁, hε₁, H⟩ := prob_regG h31a hS hγ hγ2 hD hζ0 hζ1 hM'0
  obtain ⟨δ, hδ, hδ1, Hδ⟩ := eventually_area hC hA hM hζ2
  refine ⟨|K|, min ε₁ (min δ (1 / 2)), lt_min hε₁ (lt_min hδ (by norm_num)),
    fun P _ h hh ε hε 𝕣 h𝕣 => ?_⟩
  obtain ⟨hε0, hεm⟩ := hε
  have hεε₁ : ε < ε₁ := hεm.trans_le (min_le_left _ _)
  have hεδ : ε < δ := hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε2 : ε < 1 / 2 := hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by linarith
  -- the event `G^ε_𝕣` and the length property imply the event of the proposition
  have hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLength := hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh.1)
  have hR : ε ^ (-M) * 𝕣 + 2 * ε * 𝕣 ≤ ε ^ (-M') * 𝕣 := by
    have e : ε ^ (-M') = ε ^ (-M) * ε ^ (-(max M p - M + 1)) := by
      rw [← Real.rpow_add hε0]; congr 1; rw [hM']; ring
    have h1 : 2 ≤ ε ^ (-(max M p - M + 1)) := by
      have hge : ε ^ (-(max M p - M + 1)) ≥ ε ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by have := le_max_left M p; linarith)
      rw [Real.rpow_neg_one] at hge
      have : 2 ≤ ε⁻¹ := by rw [le_inv_comm₀ (by norm_num) hε0]; linarith
      linarith
    have h2 : 1 ≤ ε ^ (-M) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1 (by linarith)
    rw [e]
    have : ε ^ (-M) + 2 * ε ≤ ε ^ (-M) * ε ^ (-(max M p - M + 1)) := by nlinarith
    nlinarith
  have hεζ : ε ≤ ε ^ (1 - ζ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith : 1 - ζ ≤ 1)
    rwa [Real.rpow_one] at this
  have hsub : (h ⁻¹' {g : DistC | ∀ s : ℝ, 0 < s →
      filledBall (D g) 0 s ⊆ Metric.ball 0 (ε ^ (-M) * 𝕣) →
        ∀ w : ℂ, w ∉ filledBall (D g) 0 s → ∀ (G : ℝ → ℂ) (L : ℝ),
          IsGeodesicL (D g) G L 0 w →
          volume (Metric.thickening (ε * 𝕣) (G '' Icc 0 L) ∩
              Metric.thickening (ε * 𝕣) (frontier (filledBall (D g) 0 s))) ≤
            ENNReal.ofReal (ε ^ (2 - 1 / M) * 𝕣 ^ 2)})ᶜ ⊆
      (h ⁻¹' regG D C A ζ M' ε 𝕣)ᶜ ∪ {ω | ¬ (D (h ω)).IsLength} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_compl_iff, mem_preimage, mem_ofPred_eq, not_or, not_not] at hn hω
    apply hω
    intro s hs hF w _ G L hG
    obtain ⟨⟨hcov, hev⟩, hl⟩ := hn
    refine (det_bound hl (by linarith) hε0 h𝕣 hεζ hcov hev hR hs hF hG).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have := Hδ ε hε0 hεδ
    have e : ((2 * nB C ε A : ℕ) : ℝ) * (Real.pi * (5 * (ε ^ (1 - ζ) * 𝕣)) ^ 2) =
        ((2 * nB C ε A : ℕ) : ℝ) * (Real.pi * (5 * ε ^ (1 - ζ)) ^ 2) * 𝕣 ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hnull : P {ω | ¬ (D (h ω)).IsLength} = 0 := ae_iff.1 hlen
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  refine (H P h hh ε ⟨hε0, hεε₁⟩ 𝕣 h𝕣).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : ε ^ M' ≤ ε ^ p :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by have := le_max_right M p; linarith)
  have := mul_le_mul_of_nonneg_left hpow (abs_nonneg K)
  have := mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_pos_of_pos hε0 M').le
  linarith

end LQGMetric.DFGPS
