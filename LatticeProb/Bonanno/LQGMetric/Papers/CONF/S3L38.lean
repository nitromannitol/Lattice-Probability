/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L38 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L38Conds
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond3
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFGPSM2Asm2

/-!
# CONF Lemma 3.8 (`lem-finite-geo-reg`): `P[𝓔^𝕫_𝕣(a)] ≥ p` uniformly in `𝕣` and `𝕫`

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, l. 1482–1500 (event `𝓔_𝕣(a)`, Lemma 3.8 and its
proof); at centre `𝕫` as GM S2.7 (arXiv:1905.00383, l. 1153–1160). Condition 2 is read with
`e^{+ξh_𝕣(𝕫)}` (`Blueprint.confReg`).

The proof follows CONF l. 1497–1500: each of the conditions fails with probability `≤ (1−p)/3`
for `a` small, uniformly in `𝕣` (and `𝕫`):
* conditions 1, 2: Axiom V (`conf38_c12_prob`, `S3L38Conds.lean`);
* condition 3: DFGPS Proposition 3.18 (`conf38_c3_prob`). DFGPS Prop 3.18 is stated at centre `0`
  for a field normalized by `h_1(0) = 0`; condition 3 at centre `𝕫` is an event of the rescaled
  metric `scaledField 𝕣 𝕫 h = 𝔠_𝕣⁻¹e^{−ξh_𝕣(𝕫)} D_h(𝕣· + 𝕫, 𝕣· + 𝕫)` (a closed set `S` of
  `C(ℂ × ℂ, ℝ)`), whose law does not depend on the centre or the additive constant
  (`GM.Tight.map_scaledField_eq`: Axioms III, IV′ and translation invariance of the GFF). CONF
  leaves this transfer implicit.
* condition 4: Lemma 3.5 and a union bound over dyadic `ε ∈ (0, a]` (`conf38_c4_prob`).

Main results: `confLem3_8At_of` (from `DFGPSProp3_18`) and `confLem3_8At_cited` (from the cited
inputs `LMLem3_1a`, `DGThm1_5KU`, `DGProp3_21` of `DFGPS.dfgpsProp3_18_cited`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- the closed set of `C(ℂ × ℂ, ℝ)` behind condition 3 at scale `1`, centre `0` -/
def c38S (χ a : ℝ) : Set C(ℂ × ℂ, ℝ) :=
  {f | ∀ x ∈ ball (0 : ℂ) 4, ∀ y ∈ ball (0 : ℂ) 4, ‖x - y‖ ≤ a → f (x, y) ≤ ‖x - y‖ ^ χ}

theorem isClosed_c38S (χ a : ℝ) : IsClosed (c38S χ a) := by
  have : c38S χ a = ⋂ x ∈ ball (0 : ℂ) 4, ⋂ y ∈ ball (0 : ℂ) 4, ⋂ (_ : ‖x - y‖ ≤ a),
      {f : C(ℂ × ℂ, ℝ) | f (x, y) ≤ ‖x - y‖ ^ χ} := by
    ext f; simp [c38S]
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_iInter fun _ =>
    isClosed_le (continuous_eval_const _) continuous_const

/-- condition 3 at centre `𝕫` holds as soon as the rescaled metric lies in `c38S` -/
theorem c38C3_of_mem {Ω : Type} {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {h : Ω → DistC}
    {χ : ℝ} {z₀ : ℂ} {R a : ℝ} (hR : 0 < R) {ω : Ω}
    (hω : GM.Tight.scaledField ξ D cc R z₀ (h ω) ∈ c38S χ a) :
    ω ∈ c38C3 ξ cc D h χ z₀ R a := by
  intro u hu v hv huv
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hn : ∀ w : ℂ, ‖w / R‖ = ‖w‖ / R := fun w => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hx : (R : ℂ) * ((u - z₀) / R) + z₀ = u := by field_simp; ring
  have hy : (R : ℂ) * ((v - z₀) / R) + z₀ = v := by field_simp; ring
  have hxy : (u - z₀) / R - (v - z₀) / R = (u - v) / R := by field_simp; ring
  have hb : ∀ w ∈ ball z₀ (4 * R), (w - z₀) / R ∈ ball (0 : ℂ) 4 := fun w hw => by
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball_zero_iff, hn, div_lt_iff₀ hR]; linarith
  have := hω _ (hb u hu) _ (hb v hv) (by rw [hxy, hn]; exact huv)
  rw [GM.Tight.scaledField_apply, hx, hy, hxy, hn, ← GM.gm_scaleFac_inv] at this
  exact this

/-- **CONF Lemma 3.8, condition 3** (l. 1498, DFGPS Proposition 3.18): uniformly in `𝕣` and `𝕫`. -/
theorem conf38_c3_prob (h318 : DFGPSProp3_18) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {χ : ℝ} (hχ : 0 < χ)
    (hχQ : χ < xiGamma γ * (Q γ - 2)) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ),
      0 < R → ∀ a ∈ Ioc 0 a₀,
        P (c38C3 (xiGamma γ) c D h χ z₀ R a)ᶜ ≤ ENNReal.ofReal (1 - q) := by
  obtain ⟨p₁, hp₁, C₁, ε₁, hε₁, H1⟩ := h318 γ hγ hγ2 D c hD (closedBall 0 4)
    (isCompact_closedBall _ _) χ (xiGamma γ * (Q γ + 2) + 1) hχ hχQ (by linarith)
  intro q hq
  obtain ⟨b₁, hb₁, hb₁ε, hB1⟩ := GM.gm_exists_small_rpow (C := C₁) hp₁ hε₁
    (show 0 < 1 - q by linarith)
  refine ⟨b₁, hb₁, ?_⟩
  intro Ω _ P _ h hh z₀ R hR a ⟨ha0, ha⟩
  -- the normalized field `h − h_1(0)`
  have hN : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) with hh'def
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh.addConst hN, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    simp only [h', hω, add_neg_cancel]
  set F : Ω → C(ℂ × ℂ, ℝ) := fun ω => GM.Tight.scaledField (xiGamma γ) D c R z₀ (h ω) with hF
  set F' : Ω → C(ℂ × ℂ, ℝ) := fun ω => GM.Tight.scaledField (xiGamma γ) D c R 0 (h' ω)
    with hF'
  have hFm : Measurable F :=
    (GM.Tight.measurable_scaledField hD.measurable c R z₀).comp hh.measurable
  have hF'm : Measurable F' :=
    (GM.Tight.measurable_scaledField hD.measurable c R 0).comp hh'.1.measurable
  have hlaw : P.map F = P.map F' := GM.Tight.map_scaledField_eq hD hh hh'.1 hR z₀
  have hSm : MeasurableSet (c38S χ a)ᶜ := (isClosed_c38S χ a).measurableSet.compl
  set E1 := h' ⁻¹' {g : DistC | ∀ u ∈ scaleSet R 0 (closedBall 0 4),
      ∀ v ∈ scaleSet R 0 (closedBall 0 4), ‖u - v‖ ≤ a * R →
        ‖(u - v) / R‖ ^ (xiGamma γ * (Q γ + 2) + 1) ≤
          (c R)⁻¹ * Real.exp (-xiGamma γ * circleAvg g R 0) * (D g).1 (u, v) ∧
        (c R)⁻¹ * Real.exp (-xiGamma γ * circleAvg g R 0) * (D g).1 (u, v) ≤
          ‖(u - v) / R‖ ^ χ} with hE1
  have hP1 : P E1ᶜ ≤ ENNReal.ofReal (C₁ * a ^ p₁) :=
    H1 P h' hh' a ⟨ha0, lt_of_le_of_lt ha hb₁ε⟩ R hR
  have hsub1 : (c38C3 (xiGamma γ) c D h χ z₀ R a)ᶜ ⊆ F ⁻¹' (c38S χ a)ᶜ := by
    intro ω hω hS
    exact hω (c38C3_of_mem hR hS)
  have hsub2 : F' ⁻¹' (c38S χ a)ᶜ ⊆ E1ᶜ := by
    intro ω hω hE
    apply hω
    intro x hx y hy hxy
    have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
    have hmem : ∀ w ∈ ball (0 : ℂ) 4, (R : ℂ) * w + 0 ∈ scaleSet R 0 (closedBall 0 4) :=
      fun w hw => ⟨w, ball_subset_closedBall hw, rfl⟩
    have hd : ((R : ℂ) * x + 0 - ((R : ℂ) * y + 0)) / R = x - y := by field_simp; ring
    have hnorm : ‖(R : ℂ) * x + 0 - ((R : ℂ) * y + 0)‖ ≤ a * R := by
      rw [show (R : ℂ) * x + 0 - ((R : ℂ) * y + 0) = (R : ℂ) * (x - y) by ring, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, mul_comm]
      exact mul_le_mul_of_nonneg_right hxy hR.le
    have := (hE _ (hmem x hx) _ (hmem y hy) hnorm).2
    rw [hd] at this
    show GM.Tight.scaledField (xiGamma γ) D c R 0 (h' ω) (x, y) ≤ ‖x - y‖ ^ χ
    rw [GM.Tight.scaledField_apply]
    exact this
  calc P (c38C3 (xiGamma γ) c D h χ z₀ R a)ᶜ ≤ P (F ⁻¹' (c38S χ a)ᶜ) := measure_mono hsub1
    _ = P.map F (c38S χ a)ᶜ := (Measure.map_apply hFm hSm).symm
    _ = P.map F' (c38S χ a)ᶜ := by rw [hlaw]
    _ = P (F' ⁻¹' (c38S χ a)ᶜ) := Measure.map_apply hF'm hSm
    _ ≤ P E1ᶜ := measure_mono hsub2
    _ ≤ ENNReal.ofReal (C₁ * a ^ p₁) := hP1
    _ ≤ ENNReal.ofReal (1 - q) := ENNReal.ofReal_le_ofReal (hB1 a ⟨ha0, ha⟩)

/-- **CONF Lemma 3.8** (`lem-finite-geo-reg`, l. 1493–1500), at centre `𝕫` (GM S2.7), for every
valid parameter choice satisfying Lemma 3.5 and every Hölder exponent `χ ∈ (0, ξ(Q−2))`, from
DFGPS Proposition 3.18. -/
theorem confLem3_8At_of (h318 : DFGPSProp3_18) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) :
    ∀ p : CONFParams, p.Valid → CONFLem3_5At γ D c p →
      ∀ χ ∈ Ioo (0 : ℝ) (xiGamma γ * (Q γ - 2)), CONFLem3_8At γ D c p χ := by
  intro p _ h35 χ hχ q hq
  have hq3 : 1 - (1 - q) / 3 < 1 := by linarith [hq.2]
  obtain ⟨a₁, ha₁, H12⟩ := conf38_c12_prob hγ hγ2 hD _ hq3
  obtain ⟨a₃, ha₃, H3⟩ := conf38_c3_prob h318 hγ hγ2 hD hχ.1 hχ.2 _ hq3
  obtain ⟨a₄, ha₄, H4⟩ := conf38_c4_prob h35 _ hq3
  set a := min (min a₁ a₃) (min a₄ (1 / 2)) with ha
  have ha0 : 0 < a := lt_min (lt_min ha₁ ha₃) (lt_min ha₄ (by norm_num))
  have ha1 : a < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  refine ⟨a, ⟨ha0, ha1⟩, ?_⟩
  intro Ω _ P _ h hh z₀ R hR
  have e : 1 - (1 - (1 - q) / 3) = (1 - q) / 3 := by ring
  have b12 := H12 P h hh z₀ R hR a ⟨ha0, (min_le_left _ _).trans (min_le_left _ _)⟩
  have b3 := H3 P h hh z₀ R hR a ⟨ha0, (min_le_left _ _).trans (min_le_right _ _)⟩
  have b4 := H4 P h hh z₀ R hR a ⟨ha0, (min_le_right _ _).trans (min_le_left _ _)⟩
  rw [e] at b12 b3 b4
  have hq0 : 0 ≤ (1 - q) / 3 := by linarith [hq.2]
  calc P (confReg (xiGamma γ) c D P h p χ z₀ R a)ᶜ
      ≤ P ((c38C12 (xiGamma γ) c D h z₀ R a)ᶜ ∪ (c38C3 (xiGamma γ) c D h χ z₀ R a)ᶜ ∪
          (c38C4 (xiGamma γ) c D P h p z₀ R a)ᶜ) := measure_mono confReg_compl_subset
    _ ≤ P (c38C12 (xiGamma γ) c D h z₀ R a)ᶜ + P (c38C3 (xiGamma γ) c D h χ z₀ R a)ᶜ +
          P (c38C4 (xiGamma γ) c D P h p z₀ R a)ᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((1 - q) / 3) + ENNReal.ofReal ((1 - q) / 3) +
          ENNReal.ofReal ((1 - q) / 3) := by gcongr
    _ = ENNReal.ofReal (1 - q) := by
        rw [← ENNReal.ofReal_add hq0 hq0, ← ENNReal.ofReal_add (by positivity) hq0]
        congr 1; ring

/-- **CONF Lemma 3.8** from the cited inputs of DFGPS Proposition 3.18 (LM Lemma 3.1 and the DG
results behind DFGPS Theorem 1.5, `DFGPS.dfgpsProp3_18_cited`). -/
theorem confLem3_8At_cited (h31a : LMLem3_1a) (hKU : DGThm1_5KU) (hP : DGProp3_21) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) :
    ∀ p : CONFParams, p.Valid → CONFLem3_5At γ D c p →
      ∀ χ ∈ Ioo (0 : ℝ) (xiGamma γ * (Q γ - 2)), CONFLem3_8At γ D c p χ :=
  confLem3_8At_of (DFGPS.dfgpsProp3_18_cited h31a hKU hP) hγ hγ2 hD

end LQGMetric.CONF
