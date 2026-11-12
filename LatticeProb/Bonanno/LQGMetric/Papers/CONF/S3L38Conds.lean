/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L38Conds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond2Prob
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityProb

/-!
# CONF Lemma 3.8: conditions 1, 2 and 4 of `𝓔^𝕫_𝕣(a)`

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, the event `𝓔_𝕣(a)` (l. 1484–1491) and the proof of
Lemma 3.8 (`lem-finite-geo-reg`, l. 1496–1500):

* conditions 1 and 2 (l. 1497: "By Axiom V, if `a` is chosen sufficiently small then the
  probability of each of conditions 1 and 2 is at least `1 − (1−p)/4`"): `conf38_c12_prob`, from
  the Axiom V tightness facts `GMS2_4a` (i) (distances across the annuli `A_{𝕣/4,3𝕣/4}(𝕫)`,
  `A_{5𝕣/4,7𝕣/4}(𝕫)`, `A_{9𝕣/4,11𝕣/4}(𝕫)`) and `GMS2_4b` (diameter of `B_{𝕣/2}(𝕫)`), proved in
  `GM.Tight`, uniform in the centre `𝕫`; the deterministic step is GM's `gm_c2_good`
  (`Papers/GM/S4/RegularityCond2.lean`) at the single centre `z = w = 𝕫`. CONF gives no details;
  this is the same (own) argument as GM Lemma 4.11 condition 2 (l. 1984), recorded there.
* condition 4 (l. 1499: "By Lemma 3.5 and a union bound over dyadic values of `ε ∈ (0,a]`"):
  `conf38_c4_prob`, Lemma 3.5 (`CONFLem3_5At`) with `K = cl B_4(0)` and `Σ_{2^{-n} ≤ a} C₀ 4^{-n}
  ≤ 2C₀a` (as `GM.gm_regC6_prob`, at centre `𝕫`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

section Events
variable {Ω : Type} [MeasurableSpace Ω]

/-- conditions 1 and 2 of `𝓔^𝕫_𝕣(a)` (CONF l. 1486–1487, `+ξ h_𝕣(𝕫)`, D-typo) -/
def c38C12 (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (R a : ℝ) :
    Set Ω :=
  {ω | ball z₀ (a * R) ⊆ filledBall (D (h ω)) z₀ (tauR D h z₀ R ω) ∧
    a * scaleFac ξ cc (h ω) R z₀ ≤ tauR D h z₀ (3 * R) ω - tauR D h z₀ (2 * R) ω}

/-- condition 3 of `𝓔^𝕫_𝕣(a)` (CONF l. 1488) -/
def c38C3 (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (h : Ω → DistC) (χ : ℝ) (z₀ : ℂ)
    (R a : ℝ) : Set Ω :=
  {ω | ∀ u ∈ ball z₀ (4 * R), ∀ v ∈ ball z₀ (4 * R), ‖u - v‖ / R ≤ a →
      (scaleFac ξ cc (h ω) R z₀)⁻¹ * (D (h ω)).1 (u, v) ≤ (‖u - v‖ / R) ^ χ}

/-- condition 4 of `𝓔^𝕫_𝕣(a)` (CONF l. 1489) -/
def c38C4 (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (z₀ : ℂ) (R a : ℝ) : Set Ω :=
  {ω | ∀ (j : ℕ), (2 : ℝ)⁻¹ ^ j ≤ a → ∀ z ∈ gridPts ((2 : ℝ)⁻¹ ^ j * R / 4) ∩ ball z₀ (4 * R),
      confRho ξ cc D P h p ((2 : ℝ)⁻¹ ^ j * R) z (confN p ((2 : ℝ)⁻¹ ^ j)) ω ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ (1 / 2 : ℝ) * R)}

/-- `𝓔^𝕫_𝕣(a)ᶜ ⊆ (1 ∧ 2)ᶜ ∪ 3ᶜ ∪ 4ᶜ` -/
theorem confReg_compl_subset {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {p : CONFParams} {χ : ℝ} {z₀ : ℂ} {R a : ℝ} :
    (confReg ξ cc D P h p χ z₀ R a)ᶜ ⊆
      (c38C12 ξ cc D h z₀ R a)ᶜ ∪ (c38C3 ξ cc D h χ z₀ R a)ᶜ ∪ (c38C4 ξ cc D P h p z₀ R a)ᶜ := by
  intro ω hω
  by_contra hn
  simp only [mem_union, mem_compl_iff, not_or, not_not] at hn
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hn
  exact hω ⟨h1, h2, h3, h4⟩

end Events

/-- **CONF Lemma 3.8, conditions 1 and 2** (l. 1497, Axiom V): uniformly in `𝕣` and `𝕫`. -/
theorem conf38_c12_prob {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ),
      0 < R → ∀ a ∈ Ioc 0 a₀, P (c38C12 (xiGamma γ) c D h z₀ R a)ᶜ ≤ ENNReal.ofReal (1 - q) := by
  intro q hq
  set η₀ := (1 - q) / 5 with hη₀
  have hη₀0 : 0 < η₀ := by rw [hη₀]; linarith
  have hp₀ : 1 - η₀ < 1 := by linarith
  have h4a := (GM.Tight.blueprint_GMS2_4a γ hγ hγ2 D c hD).1
  have h4b := GM.Tight.blueprint_GMS2_4b γ hγ hγ2 D c hD
  obtain ⟨s₁, hs₁, HS₁⟩ := h4a (ball 0 (3 / 4)) (closedBall 0 (1 / 4)) isOpen_ball
    isBounded_ball (isCompact_closedBall _ _) (closedBall_subset_ball (by norm_num)) (1 - η₀) hp₀
  obtain ⟨s₃, hs₃, HS₃⟩ := h4a (ball 0 (7 / 4)) (closedBall 0 (5 / 4)) isOpen_ball
    isBounded_ball (isCompact_closedBall _ _) (closedBall_subset_ball (by norm_num)) (1 - η₀) hp₀
  obtain ⟨s₅, hs₅, HS₅⟩ := h4a (ball 0 (11 / 4)) (closedBall 0 (9 / 4)) isOpen_ball
    isBounded_ball (isCompact_closedBall _ _) (closedBall_subset_ball (by norm_num)) (1 - η₀) hp₀
  obtain ⟨b, hb, HB⟩ := h4b (closedBall 0 (1 / 2)) (isCompact_closedBall _ _) (s₁ / 2)
    (by positivity) (1 - η₀) hp₀
  set S := min s₃ s₅ with hS
  have hS0 : 0 < S := lt_min hs₃ hs₅
  refine ⟨min (min (1 / 4) b) S, lt_min (lt_min (by norm_num) hb) hS0, ?_⟩
  intro Ω _ P _ h hh z₀ R hR a ⟨ha0, ha⟩
  have ha4 : a ≤ 1 / 4 := ha.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hab : a ≤ b := ha.trans ((min_le_left _ _).trans (min_le_right _ _))
  have haS : a ≤ S := ha.trans (min_le_right _ _)
  have hcpos : ∀ r, 0 < r → 0 < c r := hD.tightness.1
  set ξ := xiGamma γ with hξ
  set E1 : Set Ω := {ω | ENNReal.ofReal (s₁ * scaleFac ξ c (h ω) R z₀) ≤ setDist (D (h ω))
    (scaleSet R z₀ (closedBall 0 (1 / 4))) (scaleSet R z₀ (frontier (ball 0 (3 / 4))))} with hE1
  set E3 : Set Ω := {ω | ENNReal.ofReal (s₃ * scaleFac ξ c (h ω) R z₀) ≤ setDist (D (h ω))
    (scaleSet R z₀ (closedBall 0 (5 / 4))) (scaleSet R z₀ (frontier (ball 0 (7 / 4))))} with hE3
  set E5 : Set Ω := {ω | ENNReal.ofReal (s₅ * scaleFac ξ c (h ω) R z₀) ≤ setDist (D (h ω))
    (scaleSet R z₀ (closedBall 0 (9 / 4))) (scaleSet R z₀ (frontier (ball 0 (11 / 4))))}
    with hE5
  set E2 : Set Ω := {ω | ∀ u ∈ scaleSet R z₀ (closedBall 0 (1 / 2)),
    ∀ v ∈ scaleSet R z₀ (closedBall 0 (1 / 2)), ‖u - v‖ ≤ b * R →
      (D (h ω)).1 (u, v) ≤ s₁ / 2 * scaleFac ξ c (h ω) R z₀} with hE2
  set Nlen : Set Ω := {ω | ¬ (D (h ω)).IsLength} with hNlen
  have hNlenP : P Nlen = 0 :=
    ae_iff.1 (hD.length P h (GM.isGFFPlusCont_of_isWholePlaneGFF hh))
  have b1 : P E1ᶜ ≤ ENNReal.ofReal (1 - (1 - η₀)) := HS₁ P h hh z₀ R hR
  have b3 : P E3ᶜ ≤ ENNReal.ofReal (1 - (1 - η₀)) := HS₃ P h hh z₀ R hR
  have b5 : P E5ᶜ ≤ ENNReal.ofReal (1 - (1 - η₀)) := HS₅ P h hh z₀ R hR
  have b2 : P E2ᶜ ≤ ENNReal.ofReal (1 - (1 - η₀)) := HB P h hh z₀ R hR
  have hsub : (c38C12 ξ c D h z₀ R a)ᶜ ⊆ Nlen ∪ E1ᶜ ∪ E2ᶜ ∪ E3ᶜ ∪ E5ᶜ := by
    intro ω hω
    by_contra hn
    apply hω
    simp only [mem_union, not_or, mem_compl_iff, not_not] at hn
    obtain ⟨⟨⟨⟨hlen, e1⟩, e2⟩, e3⟩, e5⟩ := hn
    simp only [hNlen, mem_ofPred_eq, not_not] at hlen
    set X := scaleFac ξ c (h ω) R z₀ with hX
    have hX0 : 0 < X := mul_pos (hcpos R hR) (Real.exp_pos _)
    have C1 := GM.gm_c2_cross hR (by norm_num) e1
    have C3 := GM.gm_c2_cross hR (by norm_num) e3
    have C5 := GM.gm_c2_cross hR (by norm_num) e5
    have E3' : ∀ u ∈ sphere z₀ (R * (5 / 4)), ∀ v ∈ sphere z₀ (R * (7 / 4)),
        S * X ≤ (D (h ω)).1 (u, v) := fun u hu v hv =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hX0.le) (C3 u hu v hv)
    have E5' : ∀ u ∈ sphere z₀ (R * (9 / 4)), ∀ v ∈ sphere z₀ (R * (11 / 4)),
        S * X ≤ (D (h ω)).1 (u, v) := fun u hu v hv =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hX0.le) (C5 u hu v hv)
    obtain ⟨hball, hincr⟩ := GM.gm_c2_good hlen (z := z₀) (w := z₀) (a := a * R) (b := b) hR
      (by rw [sub_self, norm_zero]; positivity) (by nlinarith) (by nlinarith) hX0 hs₁ C1 e2
      E3' E5'
    refine ⟨hball, le_trans ?_ (hincr.trans (min_le_right _ _))⟩
    exact mul_le_mul_of_nonneg_right haS hX0.le
  have e : 1 - (1 - η₀) = η₀ := by ring
  rw [e] at b1 b2 b3 b5
  calc P (c38C12 ξ c D h z₀ R a)ᶜ ≤ P (Nlen ∪ E1ᶜ ∪ E2ᶜ ∪ E3ᶜ ∪ E5ᶜ) := measure_mono hsub
    _ ≤ P Nlen + P E1ᶜ + P E2ᶜ + P E3ᶜ + P E5ᶜ := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal η₀ + ENNReal.ofReal η₀ + ENNReal.ofReal η₀ + ENNReal.ofReal η₀ := by
        rw [hNlenP]; gcongr
    _ = ENNReal.ofReal (4 * η₀) := by
        rw [zero_add, ← ENNReal.ofReal_add hη₀0.le hη₀0.le,
          ← ENNReal.ofReal_add (by positivity) hη₀0.le,
          ← ENNReal.ofReal_add (by positivity) hη₀0.le]
        congr 1; ring
    _ ≤ ENNReal.ofReal (1 - q) := ENNReal.ofReal_le_ofReal (by rw [hη₀]; linarith)

/-- `B_{4𝕣}(𝕫) ⊆ 𝕣 cl B_4(0) + 𝕫` -/
theorem conf38_ball_subset_scale {z₀ : ℂ} {R : ℝ} (hR : 0 < R) :
    ball z₀ (4 * R) ⊆ (fun x : ℂ => (R : ℂ) * x + z₀) '' closedBall 0 4 := by
  intro u hu
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  refine ⟨(u - z₀) / R, ?_, by field_simp; ring⟩
  rw [mem_ball, dist_eq_norm] at hu
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    div_le_iff₀ hR]
  linarith

/-- **CONF Lemma 3.8, condition 4** (l. 1499): by Lemma 3.5 and a union bound over dyadic
`ε ∈ (0,a]`, uniformly in `𝕣` and `𝕫`. -/
theorem conf38_c4_prob {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (h35 : CONFLem3_5At γ D c p) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ),
      0 < R → ∀ a ∈ Ioc 0 a₀,
        P (c38C4 (xiGamma γ) c D P h p z₀ R a)ᶜ ≤ ENNReal.ofReal (1 - q) := by
  obtain ⟨C₀, ε₀, hC₀, hε₀, H⟩ := h35 (closedBall 0 4) (isCompact_closedBall _ _)
  intro q hq
  have hq' : 0 < 1 - q := by linarith
  refine ⟨min (ε₀ / 2) ((1 - q) / (2 * C₀)), lt_min (by linarith) (by positivity), ?_⟩
  intro Ω _ P _ h hh z₀ R hR a ⟨ha0, ha⟩
  have haε : a < ε₀ := lt_of_le_of_lt (ha.trans (min_le_left _ _)) (by linarith)
  have haq : 2 * C₀ * a ≤ 1 - q := by
    have := ha.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set B : ℕ → Set Ω := fun n => {ω | ∃ z ∈ gridPts ((2 : ℝ)⁻¹ ^ n * R / 4) ∩
      thickening ((2 : ℝ)⁻¹ ^ n * R) ((fun x : ℂ => (R : ℂ) * x + z₀) '' closedBall 0 4),
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ (1 / 2 : ℝ) * R) <
        confRho (xiGamma γ) c D P h p ((2 : ℝ)⁻¹ ^ n * R) z (confN p ((2 : ℝ)⁻¹ ^ n)) ω}
    with hB
  have hsub : (c38C4 (xiGamma γ) c D P h p z₀ R a)ᶜ ⊆
      ⋃ n, ⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n := by
    intro ω hω
    simp only [c38C4, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨n, hn, z, hz, hlt⟩ := hω
    refine mem_iUnion₂.2 ⟨n, hn, z, ⟨hz.1, ?_⟩, hlt⟩
    exact self_subset_thickening (by positivity) _ (conf38_ball_subset_scale hR hz.2)
  have hterm : ∀ n, P (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) ≤
      ENNReal.ofReal (C₀ * a * (2 : ℝ)⁻¹ ^ n) := by
    intro n
    by_cases hn : (2 : ℝ)⁻¹ ^ n ≤ a
    · refine (measure_mono (iUnion_subset fun _ => subset_rfl)).trans ?_
      have hpos : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
      refine (H P h hh z₀ R hR _ ⟨hpos, lt_of_le_of_lt hn haε⟩).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have : ((2 : ℝ)⁻¹ ^ n) ^ 2 ≤ a * (2 : ℝ)⁻¹ ^ n := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hn hpos.le
      nlinarith
    · have : (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) = ∅ :=
        eq_empty_of_subset_empty (iUnion_subset fun h' => (hn h').elim)
      rw [this, measure_empty]; exact bot_le
  have hsum : HasSum (fun n : ℕ => C₀ * a * (2 : ℝ)⁻¹ ^ n) (C₀ * a * 2) := by
    have := (hasSum_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
      (C₀ * a)
    have e : (1 - (2 : ℝ)⁻¹)⁻¹ = 2 := by norm_num
    rwa [e] at this
  calc P (c38C4 (xiGamma γ) c D P h p z₀ R a)ᶜ
        ≤ P (⋃ n, ⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) := measure_mono hsub
    _ ≤ ∑' n, P (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (C₀ * a * (2 : ℝ)⁻¹ ^ n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₀ * a * 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq]
    _ ≤ ENNReal.ofReal (1 - q) := ENNReal.ofReal_le_ofReal (by linarith)

end LQGMetric.CONF
