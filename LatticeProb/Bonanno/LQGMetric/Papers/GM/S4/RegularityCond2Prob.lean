/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond2Prob at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond2

/-!
# GM Lemma 4.11, condition 2: the probability bound

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11, l. 1984 ("Again
using Axiom V …"). Own covering argument (see `RegularityCond2.lean`): union bound over the
`≤ (16ρ₁/ℓ + 1)²` points `w` of `(ℓ𝕣/8)ℤ² ∩ cl B_{𝕣ρ₁}(0)` of the Axiom V events
`GMS2_4a` (four annuli crossings at the scales `𝕣`, `ℓ𝕣` and one for `τ_{ℓ𝕣}`) and `GMS2_4b`
(diameter of `B_{ℓ𝕣/2}(w)`), the a.s. identities `H_r(w) = h_r(w)` at the countably many grid
points, the length property (Axiom I), and condition 4 at the scales `𝕣` and `ℓ𝕣`
(`gm_regC4_prob`) for the comparison `h_r(z)` vs `h_r(w)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

theorem gm_c2_exp_le {C ξ x y K : ℝ} (hC : 0 ≤ C) (hd : |x - y| ≤ K) :
    C * Real.exp (ξ * x) ≤ Real.exp (|ξ| * K) * (C * Real.exp (ξ * y)) := by
  rw [mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
  have h1 := le_abs_self (ξ * (x - y))
  rw [abs_mul] at h1
  have h2 := mul_le_mul_of_nonneg_left hd (abs_nonneg ξ)
  nlinarith

theorem gm_mem_rScale_ball {𝕣 ρ : ℝ} (h𝕣 : 0 < 𝕣) {x : ℂ} (hx : ‖x‖ < 𝕣 * ρ) :
    x ∈ rScale 𝕣 (ball 0 ρ) := by
  have hc : (𝕣 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h𝕣.ne'
  refine ⟨x / 𝕣, ?_, by field_simp⟩
  rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣,
    div_lt_iff₀ h𝕣]
  linarith

theorem gm_measure_union8_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {s₁ s₂ s₃ s₄ s₅ s₆ n₁ n₂ : Set Ω} {x : ℝ} (hx : 0 ≤ x) (h1 : P s₁ ≤ ENNReal.ofReal x)
    (h2 : P s₂ ≤ ENNReal.ofReal x) (h3 : P s₃ ≤ ENNReal.ofReal x) (h4 : P s₄ ≤ ENNReal.ofReal x)
    (h5 : P s₅ ≤ ENNReal.ofReal x) (h6 : P s₆ ≤ ENNReal.ofReal x) (hn1 : P n₁ = 0)
    (hn2 : P n₂ = 0) :
    P (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ n₁ ∪ n₂) ≤ ENNReal.ofReal (6 * x) := by
  have e : ENNReal.ofReal (6 * x) = ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x +
      ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x + 0 + 0 := by
    rw [add_zero, add_zero, ← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) hx,
      ← ENNReal.ofReal_add (by positivity) hx, ← ENNReal.ofReal_add (by positivity) hx,
      ← ENNReal.ofReal_add (by positivity) hx]
    congr 1; ring
  rw [e]
  refine (measure_union_le _ _).trans (add_le_add ?_ (le_of_eq hn2))
  refine (measure_union_le _ _).trans (add_le_add ?_ (le_of_eq hn1))
  refine (measure_union_le _ _).trans (add_le_add ?_ h6)
  refine (measure_union_le _ _).trans (add_le_add ?_ h5)
  refine (measure_union_le _ _).trans (add_le_add ?_ h4)
  refine (measure_union_le _ _).trans (add_le_add ?_ h3)
  exact (measure_union_le _ _).trans (add_le_add h1 h2)

/-- **GM Lemma 4.11, condition 2** (l. 1984, own covering argument): condition 2 of `ℰ_𝕣` holds
with probability `→ 1` as `a → 0`, uniformly in `𝕣`. -/
theorem gm_regC2_prob {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {V : Set ℂ} {ℓ : ℝ} (hV : Bornology.IsBounded V) (hℓ : 0 < ℓ) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ), IsWholePlaneGFF h P →
      DFGPS.IsCircleAvgVersion h P H → ∀ R : RegPar, R.ξ = xiGamma γ → R.c = c → R.V = V →
      R.ℓ = ℓ → RegCondAt P (regC2 D h H R) q a₀ := by
  obtain ⟨ρ₀, hρ₀⟩ := hV.subset_ball (0 : ℂ)
  set ρ' : ℝ := max (ρ₀ + 4 * ℓ) 0 with hρ'
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  set ρ₁ : ℝ := ρ' + ℓ with hρ₁
  have hρ₁0 : 0 < ρ₁ := by positivity
  set ξ := xiGamma γ with hξdef
  have hcpos : ∀ r, 0 < r → 0 < c r := hD.tightness.1
  intro q hq
  set η := 1 - q with hη
  have hη0 : 0 < η := by linarith
  -- condition 4 at the scales `𝕣` and `ℓ𝕣`
  obtain ⟨a₁, ha₁, H₁⟩ := gm_regC4_prob (V := ball 0 (ρ₁ + 1)) isBounded_ball (1 - η / 4)
    (by linarith)
  obtain ⟨a₂, ha₂, H₂⟩ := gm_regC4_prob (V := ball 0 ((ρ₁ + 1) / ℓ)) isBounded_ball
    (1 - η / 4) (by linarith)
  set A := min a₁ a₂ with hAdef
  have hA : 0 < A := lt_min ha₁ ha₂
  set M := A⁻¹ with hM
  -- the grid count and the per-event failure probability
  set N : ℝ := (16 * ρ₁ / ℓ + 1) ^ 2 with hN
  have hN0 : 0 < N := by positivity
  set η₀ : ℝ := η / (12 * N) with hη₀
  have hη₀0 : 0 < η₀ := by positivity
  have hp₀ : 1 - η₀ < 1 := by linarith
  have h4a := (Tight.blueprint_GMS2_4a γ hγ hγ2 D c hD).1
  have h4b := Tight.blueprint_GMS2_4b γ hγ hγ2 D c hD
  have hKU : ∀ κ κ' : ℝ, κ < κ' → closedBall (0 : ℂ) κ ⊆ ball 0 κ' := fun κ κ' hk =>
    closedBall_subset_ball hk
  obtain ⟨s₁, hs₁, HS₁⟩ := h4a (ball 0 (3 / 4)) (closedBall 0 (1 / 4)) isOpen_ball isBounded_ball
    (isCompact_closedBall _ _) (hKU _ _ (by norm_num)) (1 - η₀) hp₀
  obtain ⟨s₃, hs₃, HS₃⟩ := h4a (ball 0 (7 / 4)) (closedBall 0 (5 / 4)) isOpen_ball isBounded_ball
    (isCompact_closedBall _ _) (hKU _ _ (by norm_num)) (1 - η₀) hp₀
  obtain ⟨s₄, hs₄, HS₄⟩ := h4a (ball 0 (7 * ℓ / 4)) (closedBall 0 (5 * ℓ / 4)) isOpen_ball
    isBounded_ball (isCompact_closedBall _ _) (hKU _ _ (by linarith)) (1 - η₀) hp₀
  obtain ⟨s₅, hs₅, HS₅⟩ := h4a (ball 0 (11 / 4)) (closedBall 0 (9 / 4)) isOpen_ball
    isBounded_ball (isCompact_closedBall _ _) (hKU _ _ (by norm_num)) (1 - η₀) hp₀
  obtain ⟨s₆, hs₆, HS₆⟩ := h4a (ball 0 (11 * ℓ / 4)) (closedBall 0 (9 * ℓ / 4)) isOpen_ball
    isBounded_ball (isCompact_closedBall _ _) (hKU _ _ (by linarith)) (1 - η₀) hp₀
  obtain ⟨b, hb, HB⟩ := h4b (closedBall 0 (1 / 2)) (isCompact_closedBall _ _) (s₁ / 2)
    (by positivity) (1 - η₀) hp₀
  set S := min (min s₃ s₄) (min s₅ s₆) with hS
  have hS0 : 0 < S := lt_min (lt_min hs₃ hs₄) (lt_min hs₅ hs₆)
  refine ⟨min (min (ℓ / 4) (b * ℓ)) (S * Real.exp (-(|ξ| * (2 * M)))),
    lt_min (lt_min (by positivity) (by positivity)) (by positivity), ?_⟩
  intro Ω _ P _ h H hh hH R hξ hc hRV hRℓ
  subst hRV hRℓ
  set R₁ : RegPar := { R with V := ball 0 (ρ₁ + 1) } with hR₁
  set R₂ : RegPar := { R with V := ball 0 ((ρ₁ + 1) / R.ℓ) } with hR₂
  rintro a ⟨ha0, ha⟩ 𝕣 h𝕣
  have haℓ : a ≤ R.ℓ / 4 := ha.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hab : a ≤ b * R.ℓ := ha.trans ((min_le_left _ _).trans (min_le_right _ _))
  have haS : a * Real.exp (|ξ| * (2 * M)) ≤ S := by
    have := ha.trans (min_le_right _ _)
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)] at this
    exact this
  set L := R.ℓ * 𝕣 with hL
  have hL0 : 0 < L := by positivity
  set σ := L / 8 with hσ
  have hσ0 : 0 < σ := by positivity
  -- the bad event at a grid point `w`
  set Bw : ℂ → Set Ω := fun w =>
    {ω | ENNReal.ofReal (s₁ * scaleFac ξ c (h ω) L w) ≤ setDist (D (h ω))
        (scaleSet L w (closedBall 0 (1 / 4))) (scaleSet L w (frontier (ball 0 (3 / 4))))}ᶜ ∪
    {ω | ∀ u ∈ scaleSet L w (closedBall 0 (1 / 2)), ∀ v ∈ scaleSet L w (closedBall 0 (1 / 2)),
        ‖u - v‖ ≤ b * L → (D (h ω)).1 (u, v) ≤ s₁ / 2 * scaleFac ξ c (h ω) L w}ᶜ ∪
    {ω | ENNReal.ofReal (s₃ * scaleFac ξ c (h ω) L w) ≤ setDist (D (h ω))
        (scaleSet L w (closedBall 0 (5 / 4))) (scaleSet L w (frontier (ball 0 (7 / 4))))}ᶜ ∪
    {ω | ENNReal.ofReal (s₄ * scaleFac ξ c (h ω) 𝕣 w) ≤ setDist (D (h ω))
        (scaleSet 𝕣 w (closedBall 0 (5 * R.ℓ / 4)))
        (scaleSet 𝕣 w (frontier (ball 0 (7 * R.ℓ / 4))))}ᶜ ∪
    {ω | ENNReal.ofReal (s₅ * scaleFac ξ c (h ω) L w) ≤ setDist (D (h ω))
        (scaleSet L w (closedBall 0 (9 / 4))) (scaleSet L w (frontier (ball 0 (11 / 4))))}ᶜ ∪
    {ω | ENNReal.ofReal (s₆ * scaleFac ξ c (h ω) 𝕣 w) ≤ setDist (D (h ω))
        (scaleSet 𝕣 w (closedBall 0 (9 * R.ℓ / 4)))
        (scaleSet 𝕣 w (frontier (ball 0 (11 * R.ℓ / 4))))}ᶜ ∪
    {ω | ¬ H 𝕣 w ω = circleAvg (h ω) 𝕣 w} ∪ {ω | ¬ H L w ω = circleAvg (h ω) L w} with hBw
  have hη₀e : 1 - (1 - η₀) = η₀ := by ring
  have hBwP : ∀ w, P (Bw w) ≤ ENNReal.ofReal (6 * η₀) := by
    intro w
    have e1 := HS₁ P h hh w L hL0
    have e2 := HB P h hh w L hL0
    have e3 := HS₃ P h hh w L hL0
    have e4 := HS₄ P h hh w 𝕣 h𝕣
    have e5 := HS₅ P h hh w L hL0
    have e6 := HS₆ P h hh w 𝕣 h𝕣
    rw [hη₀e] at e1 e2 e3 e4 e5 e6
    exact gm_measure_union8_le hη₀0.le e1 e2 e3 e4 e5 e6 (ae_iff.1 (hH.ae_eq 𝕣 h𝕣 w))
      (ae_iff.1 (hH.ae_eq L hL0 w))
  set G : Set Ω := ⋃ w ∈ gridPts σ ∩ closedBall 0 (𝕣 * ρ₁), Bw w with hG
  have hGP : P G ≤ ENNReal.ofReal (η / 2) := by
    refine (gm_grid_union_le P hσ0 (by positivity) (by positivity) Bw hBwP).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have e : 2 * (𝕣 * ρ₁) / σ = 16 * ρ₁ / R.ℓ := by
      rw [hσ, hL]; field_simp; ring
    rw [e, ← hN, hη₀]
    field_simp
    ring
  set Nlen : Set Ω := {ω | ¬ (D (h ω)).IsLength} with hNlen
  have hNlenP : P Nlen = 0 := ae_iff.1 (hD.length P h (isGFFPlusCont_of_isWholePlaneGFF hh))
  have hM1 := H₁ P h H hh hH R₁ rfl A ⟨hA, min_le_left _ _⟩ 𝕣 h𝕣
  have hM2 := H₂ P h H hh hH R₂ rfl A ⟨hA, min_le_right _ _⟩ L hL0
  have hsub : (regC2 D h H R 𝕣 a)ᶜ ⊆
      Nlen ∪ (regC4 H R₁ 𝕣 A)ᶜ ∪ (regC4 H R₂ L A)ᶜ ∪ G := by
    intro ω hω
    by_contra hn
    apply hω
    simp only [mem_union, not_or, mem_compl_iff, not_not] at hn
    obtain ⟨⟨⟨hlen, hm1⟩, hm2⟩, hGω⟩ := hn
    simp only [hNlen, mem_ofPred_eq, not_not] at hlen
    intro z hz
    show ball z (a * 𝕣) ⊆ filledBall (D (h ω)) z (tauR D h z L ω) ∧
      a * max (R.c 𝕣 * Real.exp (R.ξ * H 𝕣 z ω)) (R.c L * Real.exp (R.ξ * H L z ω)) ≤
        min (tauR D h z (2 * L) ω - tauR D h z L ω) (tauR D h z (3 * L) ω - tauR D h z (2 * L) ω)
    have hz' : ‖z‖ ≤ 𝕣 * ρ' := by
      obtain ⟨x, hx, rfl⟩ := gm_regRegion_subset h𝕣 hρ₀ hz
      show ‖(𝕣 : ℂ) * x + 0‖ ≤ 𝕣 * ρ'
      rw [add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
      exact mul_le_mul_of_nonneg_left ((mem_closedBall_zero_iff.1 hx).trans (le_max_left _ _))
        h𝕣.le
    obtain ⟨w, hwg, hzw⟩ := gm_exists_gridPt_near hσ0 z
    have hzw' : ‖z - w‖ < L / 4 := by rw [hσ] at hzw; linarith
    have hw' : ‖w‖ ≤ 𝕣 * ρ₁ := by
      have := norm_sub_le z (z - w)
      rw [sub_sub_cancel] at this
      have : L / 4 ≤ 𝕣 * R.ℓ := by rw [hL]; have := mul_pos h𝕣 hℓ; linarith
      rw [hρ₁, mul_add]; linarith
    have hwG : ω ∉ Bw w := fun hB => hGω (mem_iUnion₂.2 ⟨w, ⟨hwg, mem_closedBall_zero_iff.2 hw'⟩,
      hB⟩)
    simp only [hBw, mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hwG
    obtain ⟨⟨⟨⟨⟨⟨⟨E1, E2⟩, E3⟩, E4⟩, E5⟩, E6⟩, Hw1⟩, Hw2⟩ := hwG
    -- the normalizations at `w`
    set X𝕣 := scaleFac ξ c (h ω) 𝕣 w with hX𝕣
    set XL := scaleFac ξ c (h ω) L w with hXL
    have hX𝕣0 : 0 < X𝕣 := mul_pos (hcpos 𝕣 h𝕣) (Real.exp_pos _)
    have hXL0 : 0 < XL := mul_pos (hcpos L hL0) (Real.exp_pos _)
    have C1 := gm_c2_cross hL0 (by norm_num) E1
    have C3 := gm_c2_cross hL0 (by norm_num) E3
    have C4 := gm_c2_cross h𝕣 (by positivity) E4
    have C5 := gm_c2_cross hL0 (by norm_num) E5
    have C6 := gm_c2_cross h𝕣 (by positivity) E6
    have r1 : 𝕣 * (5 * R.ℓ / 4) = L * (5 / 4) := by rw [hL]; ring
    have r2 : 𝕣 * (7 * R.ℓ / 4) = L * (7 / 4) := by rw [hL]; ring
    have r3 : 𝕣 * (9 * R.ℓ / 4) = L * (9 / 4) := by rw [hL]; ring
    have r4 : 𝕣 * (11 * R.ℓ / 4) = L * (11 / 4) := by rw [hL]; ring
    rw [r1, r2] at C4
    rw [r3, r4] at C6
    set Y := S * max X𝕣 XL with hY
    have hYle : ∀ {t₁ t₂ : ℝ}, S ≤ t₁ → S ≤ t₂ → ∀ d : ℝ,
        t₂ * X𝕣 ≤ d → t₁ * XL ≤ d → Y ≤ d := by
      intro t₁ t₂ h1 h2 d hd1 hd2
      rw [hY, mul_max_of_nonneg _ _ hS0.le]
      exact max_le (le_trans (mul_le_mul_of_nonneg_right h2 hX𝕣0.le) hd1)
        (le_trans (mul_le_mul_of_nonneg_right h1 hXL0.le) hd2)
    have E3' : ∀ u ∈ sphere w (L * (5 / 4)), ∀ v ∈ sphere w (L * (7 / 4)),
        Y ≤ (D (h ω)).1 (u, v) := fun u hu v hv =>
      hYle ((min_le_left _ _).trans (min_le_left _ _))
        ((min_le_left _ _).trans (min_le_right _ _)) _ (C4 u hu v hv) (C3 u hu v hv)
    have E5' : ∀ u ∈ sphere w (L * (9 / 4)), ∀ v ∈ sphere w (L * (11 / 4)),
        Y ≤ (D (h ω)).1 (u, v) := fun u hu v hv =>
      hYle ((min_le_right _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_right _ _)) _ (C6 u hu v hv) (C5 u hu v hv)
    obtain ⟨hball, hincr⟩ := gm_c2_good hlen (z := z) (w := w) (a := a * 𝕣) (b := b) hL0 hzw'
      (by rw [hL]; have := mul_le_mul_of_nonneg_right haℓ h𝕣.le; linarith)
      (by rw [hL]; have := mul_le_mul_of_nonneg_right hab h𝕣.le; linarith) hXL0 hs₁ C1 E2 E3' E5'
    refine ⟨hball, ?_⟩
    refine le_trans ?_ hincr
    -- `h_r(z)` vs `h_r(w)` for `r ∈ {𝕣, ℓ𝕣}`
    have hρ'1 : 𝕣 * ρ' < 𝕣 * (ρ₁ + 1) := mul_lt_mul_of_pos_left (by linarith) h𝕣
    have hρ₁1 : 𝕣 * ρ₁ < 𝕣 * (ρ₁ + 1) := mul_lt_mul_of_pos_left (by linarith) h𝕣
    have hmod1 : |H 𝕣 z ω - H 𝕣 w ω| ≤ 2 * M := by
      have h1 := hm1 z (gm_mem_rScale_ball h𝕣 (by linarith))
      have h2 := hm1 w (gm_mem_rScale_ball h𝕣 (by linarith))
      have := abs_sub_le (H 𝕣 z ω) (H 𝕣 0 ω) (H 𝕣 w ω)
      rw [abs_sub_comm (H 𝕣 0 ω)] at this
      linarith
    have hLρ : L * ((ρ₁ + 1) / R.ℓ) = 𝕣 * (ρ₁ + 1) := by rw [hL]; field_simp
    have hmod2 : |H L z ω - H L w ω| ≤ 2 * M := by
      have h1 := hm2 z (gm_mem_rScale_ball hL0 (by rw [hLρ]; linarith))
      have h2 := hm2 w (gm_mem_rScale_ball hL0 (by rw [hLρ]; linarith))
      have := abs_sub_le (H L z ω) (H L 0 ω) (H L w ω)
      rw [abs_sub_comm (H L 0 ω)] at this
      linarith
    have b1 := gm_c2_exp_le (ξ := ξ) (hcpos 𝕣 h𝕣).le hmod1
    have b2 := gm_c2_exp_le (ξ := ξ) (hcpos L hL0).le hmod2
    rw [Hw1] at b1
    rw [Hw2] at b2
    rw [hξ, hc]
    calc a * max (c 𝕣 * Real.exp (ξ * H 𝕣 z ω)) (c L * Real.exp (ξ * H L z ω))
        ≤ a * (Real.exp (|ξ| * (2 * M)) * max X𝕣 XL) := by
          refine mul_le_mul_of_nonneg_left ?_ ha0.le
          rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
          exact max_le_max b1 b2
      _ = (a * Real.exp (|ξ| * (2 * M))) * max X𝕣 XL := by ring
      _ ≤ Y := mul_le_mul_of_nonneg_right haS (le_max_of_le_left hX𝕣0.le)
  calc P (regC2 D h H R 𝕣 a)ᶜ ≤ P (Nlen ∪ (regC4 H R₁ 𝕣 A)ᶜ ∪ (regC4 H R₂ L A)ᶜ ∪ G) :=
        measure_mono hsub
    _ ≤ P Nlen + P (regC4 H R₁ 𝕣 A)ᶜ + P (regC4 H R₂ L A)ᶜ + P G := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (1 - (1 - η / 4)) + ENNReal.ofReal (1 - (1 - η / 4)) +
        ENNReal.ofReal (η / 2) := by
        rw [hNlenP]; gcongr
    _ = ENNReal.ofReal (1 - q) := by
        rw [zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; rw [hη]; ring

end LQGMetric.GM
