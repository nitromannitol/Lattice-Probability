/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L6Eta at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5

/-!
# DZZ Lemma 2.5, `η` part (task P2-DZZPRE, WP-112) — modulo the bridge shell bound

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 455, 459–461: "The bound on
`Var(η_δ(u) − η_δ(v))` follows from a similar argument." Following the `h̃` argument (l. 466–514):

* the cross term: `⟪K^η_u, K^η_v⟫ ≥ ∫_I p_{E(s)}(s; u, v) ds`, `E(s) = 𝕍 ∩ B(u, r(s)) ∩ B(v, r(s))`
  (monotonicity of `p` in the domain + Chapman–Kolmogorov for `E(s)`);
* the bridge estimate: `q_{𝕍∩B(u,r)}(t; u, u) − q_E(t; u, v) ≤ P(τ' ≤ t, τ > t) + P(shell)`,
  where the `𝕍` part is DZZ's (`measureReal_square_diff_le`) and the ball part is the event that
  the bridge `B_s − (s/t)B_t` reaches `|·| ≥ r − |u − v|` but stays in `B(0, r)`.

DZZ's "similar argument" does not say how the ball part is bounded; the reflection principle only
handles half-planes. We isolate the needed fact as the hypothesis `BridgeShellBound C`
(`P(r − d ≤ max_{s≤t} |B_s − (s/t)B_t| < r) ≤ C d/√t`, a bounded-density statement for the radial
maximum of the planar Brownian bridge; open, see handoff/P2-DZZPRE.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- **Open input** (needed for DZZ Lemma 2.5's `η` part): the radial maximum of the planar
Brownian bridge of length `t` puts mass `≤ C d/√t` on every shell `[r − d, r)`. -/
def BridgeShellBound (C : ℝ) : Prop :=
  ∀ t : ℝ≥0, t ≠ 0 → ∀ r d : ℝ, 0 ≤ d →
    P2.real ({ω | ∃ s : ℝ≥0, s ≤ t ∧ r - d ≤ ‖stdBridge t s ω‖} ∩
      {ω | ∀ s : ℝ≥0, s ≤ t → ‖stdBridge t s ω‖ < r}) ≤ C * d / Real.sqrt t

/-- The bridge part of DZZ L2.5 for `η`:
`q_{𝕍∩B(u,r)}(t; u, u) − q_{𝕍∩B(u,r)∩B(v,r)}(t; u, v) ≤ (12 + C)|u − v|/√t`. -/
theorem bridgeStay_eta_sub_le {C : ℝ} (hC0 : 0 ≤ C) (hC : BridgeShellBound C) {t : ℝ≥0}
    (ht : t ≠ 0) (u v : ℂ) (r : ℝ) :
    bridgeStay (openSquare ∩ Metric.ball u r) t u u -
      bridgeStay (openSquare ∩ Metric.ball u r ∩ Metric.ball v r) t u v ≤
        (12 + C) * ‖u - v‖ / Real.sqrt t := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hpos : 0 ≤ (12 + C) * ‖u - v‖ / Real.sqrt t := by positivity
  by_cases hu : u ∉ openSquare
  · rw [bridgeStay_eq_zero_of_not_mem ht (fun h => hu h.1)]
    linarith [bridgeStay_nonneg (openSquare ∩ Metric.ball u r ∩ Metric.ball v r) t u v]
  rw [not_not] at hu
  set X := stdBridge t
  haveI := (isPlanarBridge_stdBridge ht).gauss.isProbabilityMeasure
  set Eu := bridgeEvent (openSquare ∩ Metric.ball u r) t u u X
  set Ev := bridgeEvent (openSquare ∩ Metric.ball u r ∩ Metric.ball v r) t u v X
  set Fu := bridgeEvent openSquare t u u X
  set Fv := bridgeEvent openSquare t u v X
  set S := {ω | ∃ s : ℝ≥0, s ≤ t ∧ r - ‖u - v‖ ≤ ‖X s ω‖} ∩
      {ω | ∀ s : ℝ≥0, s ≤ t → ‖X s ω‖ < r}
  have hsub : Eu \ Ev ⊆ (Fu \ Fv) ∪ S := by
    rintro ω ⟨hEu, hEv⟩
    simp only [Eu, Ev, bridgeEvent, mem_setOf_eq, not_forall] at hEu hEv
    obtain ⟨s, hs, hns⟩ := hEv
    have huu : ∀ s' : ℝ≥0, bridgePath t u u X s' ω = u + X s' ω := fun s' => by
      simp [bridgePath]
    by_cases hV : bridgePath t u v X s ω ∈ openSquare
    · right
      refine ⟨⟨s, hs, ?_⟩, fun s' hs' => ?_⟩
      · set θ : ℝ := (s : ℝ) / t
        have hθ0 : 0 ≤ θ := by positivity
        have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hs) ht'.le
        have hp : bridgePath t u v X s ω = u + (θ : ℂ) * (v - u) + X s ω := rfl
        have hb : ¬ (bridgePath t u v X s ω ∈ Metric.ball u r ∧
            bridgePath t u v X s ω ∈ Metric.ball v r) := fun h => hns ⟨⟨hV, h.1⟩, h.2⟩
        rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, hp] at hb
        have n1 : ‖(θ : ℂ) * (v - u)‖ ≤ ‖u - v‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0, norm_sub_rev]
          exact mul_le_of_le_one_left (norm_nonneg _) hθ1
        have n2 : ‖((θ : ℂ) - 1) * (v - u)‖ ≤ ‖u - v‖ := by
          rw [norm_mul, show (θ : ℂ) - 1 = ((θ - 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), norm_sub_rev]
          exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
        by_contra hlt
        push_neg at hlt
        apply hb
        constructor
        · rw [show u + (θ : ℂ) * (v - u) + X s ω - u = (θ : ℂ) * (v - u) + X s ω by ring]
          linarith [norm_add_le ((θ : ℂ) * (v - u)) (X s ω)]
        · rw [show u + (θ : ℂ) * (v - u) + X s ω - v = ((θ : ℂ) - 1) * (v - u) + X s ω by ring]
          linarith [norm_add_le (((θ : ℂ) - 1) * (v - u)) (X s ω)]
      · have h := (hEu s' hs').2
        rw [huu, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] at h
        exact h
    · left
      exact ⟨fun s' hs' => (hEu s' hs').1, fun h => hV (h s hs)⟩
  have h1 := measureReal_le_diff_add P2 Eu Ev
  have h2 : P2.real (Eu \ Ev) ≤ P2.real (Fu \ Fv) + P2.real S :=
    (measureReal_mono hsub (measure_ne_top P2 _)).trans (measureReal_union_le _ _)
  have h3 := measureReal_square_diff_le ht hu v
  have h4 := hC t ht r ‖u - v‖ (norm_nonneg _)
  show P2.real Eu - P2.real Ev ≤ _
  have : (12 + C) * ‖u - v‖ / Real.sqrt t =
      12 * ‖u - v‖ / Real.sqrt t + C * ‖u - v‖ / Real.sqrt t := by ring
  linarith

/-- Heat-kernel form: if `q_A(t; u, u) − q_B(t; u, v) ≤ M|u − v|/√t` then
`π(p_A(t; u, u) − p_B(t; u, v)) ≤ (M + 1)|u − v| t^{−3/2}` (DZZ l. 469–475). -/
theorem pi_killedHeat_sub_le_of_bridge {A B : Set ℂ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (u v : ℂ)
    (hq : bridgeStay A t.toNNReal u u - bridgeStay B t.toNNReal u v ≤
      M * ‖u - v‖ / Real.sqrt t) :
    Real.pi * (killedHeat A t.toNNReal u u - killedHeat B t.toNNReal u v) ≤
      (M + 1) * ‖u - v‖ * t ^ (-(3 / 2 : ℝ)) := by
  have hc : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht.le
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set D := ‖u - v‖ with hD
  set q1 := bridgeStay A t.toNNReal u u
  set q2 := bridgeStay B t.toNNReal u v
  have hq2 : q2 ≤ 1 := bridgeStay_le_one _ _ _ _
  have hq20 : 0 ≤ q2 := bridgeStay_nonneg _ _ _ _
  set e := Real.exp (-D ^ 2 / (2 * t)) with he_def
  have he : 1 - e ≤ D / Real.sqrt t := by
    have h := one_sub_exp_neg_le_sqrt (x := D ^ 2 / (2 * t)) (by positivity)
    rw [← neg_div] at h
    refine h.trans ?_
    calc Real.sqrt (D ^ 2 / (2 * t)) ≤ Real.sqrt (D ^ 2 / t) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (sq_nonneg _) ht (by linarith))
      _ = D / Real.sqrt t := by
          rw [Real.sqrt_div' _ ht.le, Real.sqrt_sq (norm_nonneg _)]
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ D ^ 2 / (2 * t) := by positivity
    rw [neg_div]; linarith)
  have hkey : q1 - e * q2 ≤ (M + 1) * D / Real.sqrt t := by
    have : (1 - e) * q2 ≤ D / Real.sqrt t := by
      calc (1 - e) * q2 ≤ (1 - e) * 1 := mul_le_mul_of_nonneg_left hq2 (by linarith)
        _ ≤ D / Real.sqrt t := by linarith
    have h13 : (M + 1) * D / Real.sqrt t = M * D / Real.sqrt t + D / Real.sqrt t := by ring
    nlinarith
  have hpow : t ^ (-(3 / 2 : ℝ)) = (t * Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hL : Real.pi * (killedHeat A t.toNNReal u u - killedHeat B t.toNNReal u v) =
      (q1 - e * q2) / (2 * t) := by
    simp only [killedHeat, heatKernel, hc, sub_self, norm_zero]
    rw [← hD]
    have hpi := Real.pi_pos
    field_simp
    rw [he_def, neg_div]
    simp
    rfl
  rw [hL, hpow]
  have hD0 : 0 ≤ D := norm_nonneg _
  calc (q1 - e * q2) / (2 * t) ≤ ((M + 1) * D / Real.sqrt t) / (2 * t) := by gcongr
    _ = (M + 1) / 2 * D * (t * Real.sqrt t)⁻¹ := by field_simp
    _ ≤ (M + 1) * D * (t * Real.sqrt t)⁻¹ := by
        have hM' : 0 ≤ (M + 1) * D * (t * Real.sqrt t)⁻¹ := by positivity
        linarith

end DZZ
end LQGMetric
