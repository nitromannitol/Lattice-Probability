/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.T1_4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.T1_4Det
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412b440

/-!
# CONF Theorem 1.4 (`thm-finite-geo0`; GM Theorem 2.15)

Source: CONF = Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for
γ ∈ (0,2)*, arXiv:1905.00381, `confluence-final.tex`, Theorem 1.4 (l. 380–382) and its proof
assuming Theorem 3.1 (l. 1046–1062).

* `t14_rat_finite`: CONF Theorem 3.1 (l. 1038–1040) at `τ = τ_𝕣` in the qualitative form used at
  l. 1048 ("a.s. `X_{τ, τ + t𝔠_𝕣e^{ξh_𝕣(0)}}` is finite"), from Theorem 3.9 and Lemma 3.8 as CONF
  says at l. 1503 ("Theorem 3.1 is an immediate consequence of Theorem 3.9 and Lemma 3.8"): for
  `q < 1`, Lemma 3.8 gives `a` with `P[𝓔_𝕣(a)ᶜ] ≤ 1 − q`; Theorem 3.9 with `N` so large that
  `N^{−β} ≤ b` bounds the probability that `𝓔_𝕣(a)` occurs and `X_{τ, τ + N^{−β}…}` has more than
  `N` points; and `X_{τ, τ + b…} ⊆ X_{τ, τ + N^{−β}…}` (S-left-restr, `p412_hitSetDD_mono`).
* `confThm1_4`: CONF l. 1055–1062: countable intersection over rational `𝕣, b`, then
  `t14_tauR_btwn` and `t14_core`.

The centre: CONF assumes `z = 0` by translation invariance (l. 1047); the Blueprint statements of
§3 (`CONFSection3`) are already at a general centre `z₀`, so no translation step is needed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- `N ↦ N^{−β}` and `N ↦ b₀ e^{−b₁N^β}` are eventually small -/
theorem t14_eventually_N {β b b₀ b₁ ε : ℝ} (hβ : 0 < β) (hb : 0 < b) (hb₁ : 0 < b₁)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ (N : ℝ) ^ (-β) ≤ b ∧ b₀ * Real.exp (-b₁ * (N : ℝ) ^ β) ≤ ε := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-β)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => b₀ * Real.exp (-b₁ * (N : ℝ) ^ β)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun N : ℕ => b₁ * (N : ℝ) ^ β) atTop atTop :=
      ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul_atTop hb₁
    have h4 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h3).const_mul b₀
    simp only [mul_zero] at h4
    refine h4.congr fun N => ?_
    simp [Function.comp, neg_mul]
  filter_upwards [eventually_ge_atTop 1, h1.eventually (ge_mem_nhds hb),
    h2.eventually (ge_mem_nhds hε)] with N hN h1 h2
  exact ⟨hN, h1, h2⟩

/-- **CONF Theorem 3.1 at `τ = τ_𝕣`, qualitative form** (l. 1038–1040, 1048, 1503): a.s.
`X_{τ_𝕣, τ_𝕣 + b𝔠_𝕣e^{ξh_𝕣(z₀)}}` is finite (when `τ_𝕣 > 0`) -/
theorem t14_rat_finite (h38 : DFGPSLem3_8) (hC3 : CONFSection3) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) {R b : ℝ} (hR : 0 < R) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < tauR D h z₀ R ω → (hitSetLM (D (h ω)) z₀ (tauR D h z₀ R ω)
      (tauR D h z₀ R ω + b * scaleFac (xiGamma γ) c (h ω) R z₀)).Finite := by
  obtain ⟨p, -, -, -, h3⟩ := hC3 γ hγ hγ2 D c hD
  have hQ2 : 0 < Q γ - 2 := by
    unfold Q
    have e : 2 / γ + γ / 2 - 2 = (2 - γ) ^ 2 / (2 * γ) := by field_simp; ring
    rw [e]
    have : 0 < 2 - γ := by linarith
    positivity
  have hξQ : 0 < xiGamma γ * (Q γ - 2) := mul_pos (GM.xiGamma_pos hγ) hQ2
  obtain ⟨hL38, hT39⟩ := h3 (xiGamma γ * (Q γ - 2) / 2) ⟨by linarith, by linarith⟩
  obtain ⟨b₁, β, hb₁, hβ, hT⟩ := hT39
  set τ := tauR D h z₀ R
  set sf : Ω → ℝ := fun ω => scaleFac (xiGamma γ) c (h ω) R z₀
  have hsf : ∀ ω, 0 ≤ sf ω := fun ω =>
    mul_nonneg (hD.tightness.1 R hR).le (Real.exp_pos _).le
  rw [ae_iff]
  set Bad := {ω | ¬(0 < τ ω → (hitSetLM (D (h ω)) z₀ (τ ω) (τ ω + b * sf ω)).Finite)}
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := hε
  set q : ℝ := 1 - min (ε : ℝ) 1 / 2
  have hq : q ∈ Ioo (0 : ℝ) 1 := by
    have := min_le_right (ε : ℝ) 1
    have := lt_min hε' one_pos
    constructor <;> simp only [q] <;> linarith
  obtain ⟨a, ha, hE⟩ := hL38 q hq
  obtain ⟨b₀, -, hT'⟩ := hT a ha
  obtain ⟨N, hN1, hNb, hNe⟩ := (t14_eventually_N (b₀ := b₀) (ε := (ε : ℝ) / 2) hβ hb hb₁
    (by positivity)).exists
  -- D130: `𝓑^•_{τ_R}` is local modulo additive constants (`p412b_isLocalSetDet0_tauMin` at
  -- `k = 0`, `ℓ = 1`, `𝕣 = R`, where `s_0 ∧ τ_{2R} = τ_R`)
  have hloc0 : IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) := by
    have H := GM.p412b_isLocalSetDet0_tauMin (ℓ := 1) (𝕣 := R) (ε := 1) (β := 1) h38 hγ hγ2
      hD hh z₀ (by linarith) one_pos 0
    have e : ∀ ω, min (GM.s4S D h z₀ 1 R 1 1 0 ω) (tauR D h z₀ (2 * (1 * R)) ω) = τ ω :=
      fun ω => by
        have hm : tauR D h z₀ R ω ≤ tauR D h z₀ (2 * R) ω :=
          GM.p412b_tauR_mono D h z₀ (by linarith) ω
        simp only [GM.s4S, GM.s4Unit, Nat.cast_zero, zero_mul, add_zero, mul_one, one_mul]
        exact min_eq_left hm
    simp only [e] at H
    exact H
  have hmain := hT' P h hh z₀ R hR N hN1 τ (GM.gm_tauR_isStop D h z₀ R) hloc0
    (Eventually.of_forall fun ω => ⟨le_rfl, GM.p412b_tauR_mono D h z₀ (by linarith) ω⟩)
  have hsub : Bad ≤ᵐ[P] (confReg (xiGamma γ) c D P h p (xiGamma γ * (Q γ - 2) / 2) z₀ R a)ᶜ ∪
      {ω | ω ∈ confReg (xiGamma γ) c D P h p (xiGamma γ * (Q γ - 2) / 2) z₀ R a ∧
        ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
          (τ ω + (N : ℝ) ^ (-β) * scaleFac (xiGamma γ) c (h ω) R z₀)).encard} := by
    filter_upwards [GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh] with ω hc hω
    simp only [Bad, not_imp, mem_ofPred_eq] at hω
    obtain ⟨hτ0, hinf⟩ := hω
    by_cases hE' : ω ∈ confReg (xiGamma γ) c D P h p (xiGamma γ * (Q γ - 2) / 2) z₀ R a
    · refine Or.inr ⟨hE', ?_⟩
      have hS : 0 ≤ (N : ℝ) ^ (-β) * sf ω :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hsf ω)
      have hmono := GM.p412_hitSetDD_mono hτ0 (le_add_of_nonneg_right hS)
        (add_le_add_right (mul_le_mul_of_nonneg_right hNb (hsf ω)) (τ ω))
        (isBounded_ballM_of_bc hc z₀ (τ ω))
      have hI : (hitSetLM (D (h ω)) z₀ (τ ω) (τ ω + (N : ℝ) ^ (-β) * sf ω)).Infinite :=
        Set.Infinite.mono hmono hinf
      rw [hI.encard_eq]
      exact ENat.natCast_lt_top N
    · exact Or.inl hE'
  calc P Bad ≤ P ((confReg (xiGamma γ) c D P h p (xiGamma γ * (Q γ - 2) / 2) z₀ R a)ᶜ ∪
      {ω | ω ∈ confReg (xiGamma γ) c D P h p (xiGamma γ * (Q γ - 2) / 2) z₀ R a ∧
        ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
          (τ ω + (N : ℝ) ^ (-β) * scaleFac (xiGamma γ) c (h ω) R z₀)).encard}) :=
        measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (1 - q) + ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ β)) :=
        (measure_union_le _ _).trans (add_le_add (hE P h hh z₀ R hR) hmain)
    _ ≤ ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2) := by
        gcongr
        simp only [q]
        have := min_le_left (ε : ℝ) 1
        linarith
    _ = ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
          ENNReal.ofReal_coe_nnreal]

/-- **CONF Theorem 1.4** (`thm-finite-geo0`, l. 380–382; GM Theorem 2.15, l. 1142–1144), from
the CONF §3 package (Theorem 3.9, Lemma 3.8) and CONF Lemmas 2.2–2.4; proof CONF l. 1046–1062 -/
theorem confThm1_4 (h38 : DFGPSLem3_8) (hC3 : CONFSection3) : CONFThm1_4 := by
  intro γ hγ hγ2 D c hD Ω _ P _ h hh z₀
  have hrat : ∀ᵐ ω ∂P, ∀ R b : ℚ, 0 < (R : ℝ) → 0 < (b : ℝ) → 0 < tauR D h z₀ R ω →
      (hitSetLM (D (h ω)) z₀ (tauR D h z₀ R ω)
        (tauR D h z₀ R ω + b * scaleFac (xiGamma γ) c (h ω) R z₀)).Finite := by
    rw [ae_all_iff]; intro R; rw [ae_all_iff]; intro b
    by_cases hR : 0 < (R : ℝ)
    · by_cases hb : 0 < (b : ℝ)
      · filter_upwards [t14_rat_finite h38 hC3 hγ hγ2 hD P h hh z₀ hR hb] with ω hω _ _
        exact hω
      · exact Eventually.of_forall fun ω _ hb' => absurd hb' hb
    · exact Eventually.of_forall fun ω hR' => absurd hR' hR
  filter_upwards [hrat, GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh,
    confLem2_2 h38 γ hγ hγ2 D c hD P h hh z₀, confLem2_4 h38 γ hγ hγ2 D c hD P h hh z₀]
    with ω hr hc hq h24 t s ht hts
  have hbd : ∀ u : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ u) := isBounded_ballM_of_bc hc z₀
  obtain ⟨R, hR, htR, hRs⟩ := t14_tauR_btwn hbd ht hts
  set τ := tauR D h z₀ R ω
  set sf := scaleFac (xiGamma γ) c (h ω) R z₀
  have hsfp : 0 < sf := mul_pos (hD.tightness.1 R hR) (Real.exp_pos _)
  have hsf : 0 ≤ sf := hsfp.le
  obtain ⟨b, hb0, hb1⟩ := exists_rat_btwn (show (0 : ℝ) < (s - τ) / (sf + 1) from
    div_pos (by linarith) (by linarith))
  have hbsf : (b : ℝ) * sf < s - τ := by
    have h1 : (b : ℝ) * (sf + 1) < s - τ := (lt_div_iff₀ (by linarith)).1 hb1
    nlinarith
  exact t14_core hc hq (fun y Q hQ => (h24 s (ht.trans hts) y hQ.1 true).2.2 Q hQ) ht htR
    (by have := mul_pos hb0 hsfp; linarith) (by linarith) (hr R b hR hb0 (ht.trans htR))

end LQGMetric.CONF
