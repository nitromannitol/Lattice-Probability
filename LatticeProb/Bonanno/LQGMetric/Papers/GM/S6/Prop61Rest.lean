/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.Prop61Rest at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Prop61RestDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Prop61Step1

/-!
# GM Proposition 6.1 from Step 1 (task P2-M2O2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 6.1, l. 3576–3650.

`gm_P6_1_of_step1`: `P6_1` from GM's display (6.1) (`P6_1Step1`), following GM Steps 1b–4:
* Step 1b (l. 3601–3610): the geodesic confinement (`GMS2_4e` via `conf_prob`, `U = B_{2R₂}(0)`)
  and the Hölder bounds (6.3) by DFGPS Proposition 3.18 (= GM Lemma 2.8) with `K = B̄_{2R₂}(0)`,
  `χ = ξ(Q−2)/2`, `χ' = ξ(Q+2)+1`, at scale `ε'' = 2ρ⁻¹ε^{1+ν}` (which dominates both
  `(ε^q ∨ bε^{1+ν})ρ⁻¹`); DFGPS's normalization `h_1(0) = 0` is removed as in `gm_regC3_prob`
  (Axiom III, `(h + C)_𝕣(0) = h_𝕣(0) + C`);
* Steps 2–3 (l. 3611–3638): `p61_det` (`away_sep`, `away_transfer`), with `q = ((1+ν)χ' + χ)/χ`
  so that `qχ > (1+ν)χ'` as GM require (l. 3634); `D̃ ≤ K D` by GM Proposition 2.2;
* Step 4 (l. 3640–3650): the bound `D_h(z,w) ≤ S𝔠_𝕣e^{ξh_𝕣(0)}` on `B_𝕣(0)` from `GMS2_4c`
  (`U = B_2(0)`, `K = B̄_1(0)`) in place of GM's `𝔠_𝕣e^{ξh_𝕣(0)}ε^{-χ'}` (handoff/P2-M2O.md);
  `ε` is fixed (small enough that each of the four failure probabilities is `≤ η/4`) and
  `δ₀ = (C_* − c₂')(bε^{1+ν}ρ⁻¹)^{χ'}/(2S)`; GM's "choose `ε` with `aε^{(2+ν)χ'} = δ`" is the same
  argument read as "for each `η` there is `δ₀`".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `K ε^r < c` for all small `ε > 0` -/
theorem p61_ev_small {r K c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), K * ε ^ r < c := by
  have ht : Tendsto (fun ε : ℝ => K * ε ^ r) (𝓝 0) (𝓝 (K * (0 : ℝ) ^ r)) :=
    (continuous_const.mul (Real.continuous_rpow_const hr.le)).tendsto 0
  rw [Real.zero_rpow hr.ne', mul_zero] at ht
  exact (ht.eventually (eventually_lt_nhds hc)).filter_mono nhdsWithin_le_nhds

/-- the exponent algebra of GM (6.5)–(6.6) (`qχ = (1+ν)χ' + χ`) -/
theorem p61_herr_of {ε q ρ bb ν χ χ' L M : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hbb : 0 < bb)
    (hq : q * χ = (1 + ν) * χ' + χ) (h : L * ρ⁻¹ ^ χ * ε ^ χ ≤ M * (bb * ρ⁻¹) ^ χ') :
    L * (ε ^ q * ρ⁻¹) ^ χ ≤ M * (bb * ε ^ (1 + ν) * ρ⁻¹) ^ χ' := by
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have e1 : (ε ^ q * ρ⁻¹) ^ χ = ε ^ ((1 + ν) * χ') * (ρ⁻¹ ^ χ * ε ^ χ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hε.le _) hρi, ← Real.rpow_mul hε.le, hq,
      Real.rpow_add hε]
    ring
  have e2 : (bb * ε ^ (1 + ν) * ρ⁻¹) ^ χ' = ε ^ ((1 + ν) * χ') * (bb * ρ⁻¹) ^ χ' := by
    rw [show bb * ε ^ (1 + ν) * ρ⁻¹ = ε ^ (1 + ν) * (bb * ρ⁻¹) by ring,
      Real.mul_rpow (Real.rpow_nonneg hε.le _) (mul_nonneg hbb.le hρi), ← Real.rpow_mul hε.le]
  rw [e1, e2]
  have hE : 0 ≤ ε ^ ((1 + ν) * χ') := Real.rpow_nonneg hε.le _
  calc L * (ε ^ ((1 + ν) * χ') * (ρ⁻¹ ^ χ * ε ^ χ))
      = ε ^ ((1 + ν) * χ') * (L * ρ⁻¹ ^ χ * ε ^ χ) := by ring
    _ ≤ ε ^ ((1 + ν) * χ') * (M * (bb * ρ⁻¹) ^ χ') := mul_le_mul_of_nonneg_left h hE
    _ = M * (ε ^ ((1 + ν) * χ') * (bb * ρ⁻¹) ^ χ') := by ring

/-- a union bound over four events -/
theorem p61_measure_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {G B1 B2 B3 B4 : Set Ω}
    {x : ℝ} (hx : 0 ≤ x) (h1 : P B1 ≤ ENNReal.ofReal x) (h2 : P B2 ≤ ENNReal.ofReal x)
    (h3 : P B3 ≤ ENNReal.ofReal x) (h4 : P B4 ≤ ENNReal.ofReal x)
    (hsub : ∀ᵐ ω ∂P, ω ∈ G → ω ∈ B1 ∨ ω ∈ B2 ∨ ω ∈ B3 ∨ ω ∈ B4) :
    P G ≤ ENNReal.ofReal (4 * x) := by
  have hs : G ≤ᵐ[P] (B1 ∪ (B2 ∪ (B3 ∪ B4)) : Set Ω) := by
    filter_upwards [hsub] with ω hω
    exact hω
  calc P G ≤ P (B1 ∪ (B2 ∪ (B3 ∪ B4))) := measure_mono_ae hs
    _ ≤ P B1 + (P B2 + (P B3 + P B4)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl
          ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))))
    _ ≤ ENNReal.ofReal x + (ENNReal.ofReal x + (ENNReal.ofReal x + ENNReal.ofReal x)) := by
        gcongr
    _ = ENNReal.ofReal (4 * x) := by
        rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add hx (by positivity),
          ← ENNReal.ofReal_add hx (by positivity)]
        congr 1; ring

/-- **GM Proposition 6.1** (l. 3570–3574) from its Step 1 (display (6.1), `P6_1Step1`), DFGPS
Proposition 3.18, GM.S2.4e, GM.S2.4c and GM Proposition 2.2, following GM's proof l. 3601–3650. -/
theorem gm_P6_1_of_step1 (hS : P6_1Step1) (h318 : DFGPSProp3_18) (h24e : GMS2_4e)
    (h24c : GMS2_4c) (h22 : P2_2) : P6_1 := by
  intro γ D D' c cs Cs hPS hRat hlt
  have hγ := hPS.1; have hγ2 := hPS.2.1; have hD := hPS.2.2.1
  obtain ⟨c'', c₂, bb, ρ, ν, hc'', hc₂, hbb, hρ, hν, H1⟩ := hS hPS hRat hlt
  refine ⟨c'', hc'', ?_⟩
  intro β hβ βb hβb η hη
  obtain ⟨Kb, hKb, hBL⟩ := h22 hPS
  have hξ := xiGamma_pos hγ
  have hQ2 : 0 < Q γ - 2 := by
    have : Q γ - 2 = (2 - γ) ^ 2 / (2 * γ) := by unfold Q; field_simp; ring
    rw [this]; exact div_pos (by nlinarith) (by positivity)
  have hξQ : 0 < xiGamma γ * (Q γ - 2) := mul_pos hξ hQ2
  set χ : ℝ := xiGamma γ * (Q γ - 2) / 2 with hχdef
  set χ' : ℝ := xiGamma γ * (Q γ + 2) + 1 with hχ'def
  have hχ : 0 < χ := by rw [hχdef]; linarith
  have hχQ : χ < xiGamma γ * (Q γ - 2) := by rw [hχdef]; linarith
  have hχ'Q : xiGamma γ * (Q γ + 2) < χ' := by rw [hχ'def]; linarith
  have hχχ' : χ < χ' := by
    have : xiGamma γ * (Q γ + 2) = xiGamma γ * (Q γ - 2) + 4 * xiGamma γ := by ring
    linarith
  set q : ℝ := ((1 + ν) * χ' + χ) / χ with hqdef
  have hqχ : q * χ = (1 + ν) * χ' + χ := by rw [hqdef]; field_simp
  have hq1 : 1 + ν ≤ q := by
    rw [hqdef, le_div_iff₀ hχ]; nlinarith
  have hq : 0 < q := by linarith
  have hη4 : 0 < η / 4 := by positivity
  have hβb2 : βb / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hβb.1], by linarith [hβb.2]⟩
  obtain ⟨ε₁, hε₁, H1'⟩ := H1 β hβ (βb / 2) hβb2 q hq (η / 4) hη4
  obtain ⟨R₂, hR₂, H3⟩ := conf_prob h24e hγ hγ2 hD (β := min (η / 4) (1 / 2))
    (lt_min hη4 (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨p, hp, C, ε₀, hε₀, H2⟩ := h318 γ hγ hγ2 D c hD (closedBall 0 (2 * R₂))
    (isCompact_closedBall _ _) χ χ' hχ hχQ hχ'Q
  obtain ⟨a₀, ha₀, ha₀ε, hA0⟩ := gm_exists_small_rpow (C := C) hp hε₀ hη4
  obtain ⟨S, hS0, H4⟩ := h24c γ hγ hγ2 D c hD (ball 0 2) (closedBall 0 1) isOpen_ball
    isBounded_ball (convex_ball _ _).isPreconnected (isCompact_closedBall _ _)
    (closedBall_subset_ball (by norm_num)) (1 - η / 4) (by linarith)
  have hρ0 : 0 < ρ := hρ.1
  have hbb0 : 0 < bb := hbb.1
  have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ0
  have hMc0 : 0 < (Cs - c₂) / 2 * (bb * ρ⁻¹) ^ χ' :=
    mul_pos (by linarith) (Real.rpow_pos_of_pos (mul_pos hbb0 hρi) _)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 ∧ ε < ε₁ ∧
      2 * ρ⁻¹ * ε ^ (1 + ν) < a₀ ∧ 2 * ρ⁻¹ * ε ^ q < βb / 2 ∧
      (Cs + Kb) * 2 * ρ⁻¹ ^ χ * ε ^ χ < (Cs - c₂) / 2 * (bb * ρ⁻¹) ^ χ' := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hε₁).filter_mono nhdsWithin_le_nhds,
      p61_ev_small (K := 2 * ρ⁻¹) (r := 1 + ν) (by linarith) ha₀,
      p61_ev_small (K := 2 * ρ⁻¹) (r := q) hq (by linarith [hβb.1] : (0 : ℝ) < βb / 2),
      p61_ev_small (K := (Cs + Kb) * 2 * ρ⁻¹ ^ χ) hχ hMc0] with ε e0 e1 e2 e3 e4 e5
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  obtain ⟨ε, hε0, hε1, hεε₁, hεa, hεg, hεe⟩ := hev.exists
  set ε'' : ℝ := 2 * ρ⁻¹ * ε ^ (1 + ν) with hε''def
  have hε''0 : 0 < ε'' := by rw [hε''def]; exact mul_pos (by linarith) (Real.rpow_pos_of_pos hε0 _)
  have hXpos : 0 < bb * ε ^ (1 + ν) * ρ⁻¹ :=
    mul_pos (mul_pos hbb0 (Real.rpow_pos_of_pos hε0 _)) hρi
  have hδ₀ : 0 < (Cs - c₂) * (bb * ε ^ (1 + ν) * ρ⁻¹) ^ χ' / (2 * S) :=
    div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hXpos _)) (by linarith)
  refine ⟨_, hδ₀, ?_⟩
  intro R hR Ω _ P _ h hh hG δ hδ
  -- the four events
  have hB1 := H1' R hR P h hh hG ε ⟨hε0, hεε₁⟩
  have hB3 := (H3 P h hh (2 * R) (by linarith)).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hB4 := (H4 P h hh 0 R hR).trans (le_of_eq (by rw [sub_sub_cancel]))
  -- the normalized field `h − h_1(0)` (as in `gm_regC3_prob`)
  have hN : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) with hh'def
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh.addConst hN, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    simp only [h', hω, add_neg_cancel]
  have hB2 := (H2 P h' hh' ε'' ⟨hε''0, lt_of_le_of_lt hεa.le ha₀ε⟩ R hR).trans
    (ENNReal.ofReal_le_ofReal (hA0 ε'' ⟨hε''0, hεa.le⟩))
  refine (p61_measure_le hη4.le hB1 hB2 hB3 hB4 ?_).trans (le_of_eq (by congr 1; ring))
  filter_upwards [hBL P h hh, hRat P h hh, hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
    CircleAvg.ae_circleAvg_addConst hh 0 hR] with ω hB hRω hA hC
  intro hω
  by_contra hcon
  simp only [not_or, mem_compl_iff, not_not, mem_preimage, mem_ofPred_eq] at hcon
  obtain ⟨g1, g2, g3, g4⟩ := hcon
  obtain ⟨z, hz, w, hw, hzw, hle⟩ := hω
  set A := circleAvg (h ω) 1 0
  have hdist : ∀ u v, (D (h' ω)).1 (u, v) = Real.exp (-(xiGamma γ * A)) * (D (h ω)).1 (u, v) :=
    fun u v => (hA (-A) u v).trans (by rw [mul_neg])
  have hcirc : circleAvg (h' ω) R 0 = circleAvg (h ω) R 0 + -A := hC _
  have hkey : (c R)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h' ω) R 0) *
      Real.exp (-(xiGamma γ * A)) = (scaleFac (xiGamma γ) c (h ω) R 0)⁻¹ := by
    rw [gm_scaleFac_inv, hcirc, mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hsf : 0 < scaleFac (xiGamma γ) c (h ω) R 0 :=
    mul_pos (hD.tightness.1 R hR) (Real.exp_pos _)
  have hhol : ∀ u ∈ scaleSet R 0 (closedBall 0 (2 * R₂)),
      ∀ v ∈ scaleSet R 0 (closedBall 0 (2 * R₂)), ‖u - v‖ ≤ ε'' * R →
        ‖(u - v) / R‖ ^ χ' ≤ (scaleFac (xiGamma γ) c (h ω) R 0)⁻¹ * (D (h ω)).1 (u, v) ∧
        (scaleFac (xiGamma γ) c (h ω) R 0)⁻¹ * (D (h ω)).1 (u, v) ≤ ‖(u - v) / R‖ ^ χ := by
    intro u hu v hv huv
    have := g2 u hu v hv huv
    rwa [hdist, ← mul_assoc, hkey] at this
  have hup : ∀ u v, (D' (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v) := fun u v => by
    have := le_upperRatio_mul hB u v; rwa [hRω.2] at this
  have hYε : ε ^ q * ρ⁻¹ ≤ ε'' := by
    have h1 := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hq1) hρi.le
    have h2 := mul_pos (Real.rpow_pos_of_pos hε0 (1 + ν)) hρi
    rw [hε''def]; linarith
  have hXε : bb * ε ^ (1 + ν) * ρ⁻¹ ≤ ε'' := by
    have h2 := mul_pos (Real.rpow_pos_of_pos hε0 (1 + ν)) hρi
    have h1 := mul_le_mul_of_nonneg_right hbb.2.le h2.le
    rw [hε''def]; linarith
  have herr := p61_herr_of hε0 hρ0 hbb0 hqχ hεe.le
  have hlt' := p61_det (d := D (h ω)) (d' := D' (h ω)) hup (fun u v => (hB u v).2) hR hR₂ hsf hS0
    hc₂ hβb.2 hχ hXpos.le (mul_pos (Real.rpow_pos_of_pos hε0 _) hρi) g1 g3 hhol g4 hXε hYε
    (by linarith) (le_of_le_of_eq herr (by ring)) hδ.2 z hz w hw hzw
  linarith

/-- **GM Proposition 6.1** (l. 3570–3574) from GM Theorem 4.2 and Proposition 4.3 (via Step 1,
`gm_P6_1Step1`, with MQ Theorem 1.2 for the geodesic selector), DFGPS Proposition 3.18, GM.S2.4e,
GM.S2.4c and GM Proposition 2.2. -/
theorem gm_P6_1 (hT : T4_2) (hP43 : P4_3) (hMQ : MQThm1_2Weak) (h318 : DFGPSProp3_18)
    (h24e : GMS2_4e) (h24c : GMS2_4c) (h22 : P2_2) : P6_1 :=
  gm_P6_1_of_step1 (gm_P6_1Step1 hT hP43 hMQ) h318 h24e h24c h22

end LQGMetric.GM
