/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedP36 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36Conf
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusL38
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedCount
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedSwap

/-!
# GM Proposition 3.6 (task P2-M2F2, WP-M2f, row 8 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Proposition 3.6 (`prop-attained-bad`, l. 1288–1297), proof l. 1418–1499.

* `p36_ratio_le`: deterministic form of Steps 2–3 for all pairs: on the events of Step 1
  (confinement, the cover of Lemma 3.9), the tightness bounds of (3.18) and the a.s. facts
  (geodesics exist, are unique between points of `ℚ²`, `D̃ ≤ C_* D`), every
  `𝕫, 𝕨 ∈ B_𝕣(0)` with `|𝕫 − 𝕨| ≥ β𝕣` has `D̃(𝕫,𝕨) ≤ C₂ D(𝕫,𝕨)`. Rational pairs by `p36_pair`,
  all pairs by continuity (GM's last sentence, l. 1497–1499).
* `gm_P3_6_of`: GM Prop 3.6 from Lemma 3.9, GM.S2.4e (confinement), GM.S1.1, GM.S1.2, Prop 2.2.
* `gm_P3_6`: the same with Lemma 3.9 from Lemma 3.8 (`gm_L3_9`, `gm_L3_8`).

The end estimate (3.18) (GM: "By (3.11), Axiom V (tightness across scales) for `D` and `D̃`, and
the triangle inequality", no further proof) is derived from GM.S2.4a, separated points
(`Tight.gm_S2_4a_sep`: `D(𝕫,𝕨) ≥ s 𝔠_𝕣 e^{ξh_𝕣(0)}` for `|𝕫−𝕨| ≥ β𝕣/2`) and GM.S2.4b
(`Tight.gm_S2_4b`: `D(x,y) ≤ s' 𝔠_𝕣 e^{ξh_𝕣(0)}` for `|x − y| ≤ 4ε𝕣`), with
`3C_* s' = (C₂ − K)s`; we bound `D̃` of the end pieces by `C_* D` instead of comparing `D̃` with
its own tightness (GM's "for `D` and `D̃`"), which is the same estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM Prop 3.6, Steps 2–3**, deterministic, for all pairs (GM l. 1440–1499) -/
theorem p36_ratio_le {D D' : DistC → ContMetric} {g : DistC}
    (hex : ∀ a b : ℂ, ∃ η, (D g).IsGeod01 a b η)
    (hun : ∀ a b : ℚ × ℚ, UniqueGeod (D g) (ratPt a) (ratPt b))
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hC0 : 0 ≤ C')
    (hCC : C' ≤ Cs) (hratio : ∀ x y, (D' g).1 (x, y) ≤ Cs * (D g).1 (x, y))
    {r R ε ν β s s' C₂ X : ℝ} (hr : 0 < r) (hR : 1 < R) (hβ : 0 < β) (hε : 0 < ε)
    (hεβ : 8 * ε < β) (hs's : 3 * Cs * s' = (C₂ - (C' + A / (A + 1) * (Cs - C'))) * s)
    (hKC₂ : C' + A / (A + 1) * (Cs - C') ≤ C₂)
    (hconf : D g ∈ confSet r R)
    (hcov : ∀ x ∈ ball (0 : ℂ) ((R + 1) * r), ∃ v ρ, (ε ^ (1 + ν) * r ≤ ρ ∧ ρ ≤ ε * r ∧
      g ∈ goodAnnulus D D' α A C' ρ v) ∧ x ∈ ball v (ρ / 2))
    (hsep : ∀ x ∈ ball (0 : ℂ) r, ∀ y ∈ ball (0 : ℂ) r, β * r / 2 ≤ ‖x - y‖ → s * X < (D g).1 (x, y))
    (hmod : ∀ x ∈ ball (0 : ℂ) ((R + 1) * r), ∀ y ∈ ball (0 : ℂ) ((R + 1) * r),
      ‖x - y‖ ≤ 4 * (ε * r) → (D g).1 (x, y) ≤ s' * X) :
    ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, β * r ≤ ‖z - w‖ →
      (D' g).1 (z, w) ≤ C₂ * (D g).1 (z, w) := by
  set K := C' + A / (A + 1) * (Cs - C') with hK
  have hCs0 : 0 ≤ Cs := hC0.trans hCC
  -- rational pairs
  have hrat : ∀ a b : ℚ × ℚ, ratPt a ∈ ball (0 : ℂ) r → ratPt b ∈ ball (0 : ℂ) r →
      β * r / 2 < ‖ratPt a - ratPt b‖ →
      (D' g).1 (ratPt a, ratPt b) ≤ C₂ * (D g).1 (ratPt a, ratPt b) := by
    intro a b ha hb hab
    have hrmin : 0 < ε ^ (1 + ν) * r := mul_pos (Real.rpow_pos_of_pos hε _) hr
    have hball : ball (0 : ℂ) r ⊆ ball 0 ((R + 1) * r) := ball_subset_ball (by nlinarith)
    have h1 := p36_pair (D := D) (D' := D') hex hα hα1 hA hC0 hCC hratio (hun a b) hrmin
      (e := ε * r) (ρ := (R + 1) * r) (ω := s' * X) (by nlinarith)
      (fun η hη => (range_subset_of_confSet hR hconf ha hb hη).trans
        (closedBall_subset_ball (by nlinarith))) hcov hmod
    have h2 := hsep _ ha _ hb hab.le
    have h3 : 3 * Cs * (s' * X) ≤ (C₂ - K) * (D g).1 (ratPt a, ratPt b) := by
      rw [← mul_assoc, hs's, mul_assoc]
      exact mul_le_mul_of_nonneg_left h2.le (by linarith)
    linarith
  -- all pairs, by continuity
  set V : Set (ℂ × ℂ) := {p | p.1 ∈ ball (0 : ℂ) r ∧ p.2 ∈ ball (0 : ℂ) r ∧
    β * r / 2 < ‖p.1 - p.2‖} with hV
  have hVo : IsOpen V :=
    (isOpen_ball.preimage continuous_fst).inter ((isOpen_ball.preimage continuous_snd).inter
      (isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm))
  set F : Set (ℂ × ℂ) := {p | (D' g).1 p ≤ C₂ * (D g).1 p} with hF
  have hFc : IsClosed F := isClosed_le (D' g).1.continuous (continuous_const.mul (D g).1.continuous)
  have hd : DenseRange (Prod.map ratPt ratPt) := denseRange_ratPt.prodMap denseRange_ratPt
  have hsub : V ⊆ F := by
    refine (hd.open_subset_closure_inter hVo).trans (closure_minimal ?_ hFc)
    rintro _ ⟨hpV, ⟨a, b⟩, rfl⟩
    exact hrat a b hpV.1 hpV.2.1 hpV.2.2
  intro z hz w hw hzw
  exact hsub ⟨hz, hw, by nlinarith⟩

/-- **GM Proposition 3.6** (l. 1288–1499) from GM Lemma 3.9, GM.S2.4e (Blueprint), GM.S1.1
(`DFGPSLem3_8`), GM.S1.2 (`MQThm1_2Weak`) and GM Prop 2.2. -/
theorem gm_P3_6_of (h39 : L3_9) (h22 : P2_2) (h38 : DFGPSLem3_8) (h24e : GMS2_4e)
    (hMQ : MQThm1_2Weak) : P3_6 := by
  intro γ D D' c cs Cs hS hRat μ ν hμ hμν hν1
  obtain ⟨hγ, hγ2, hD, hD'⟩ := id hS
  obtain ⟨α₀, p, hα₀, hp, H⟩ := h39 hS hμ hμν hν1
  refine ⟨α₀, p, hα₀, hp, fun α hα C' hC' => ?_⟩
  obtain ⟨A, hA, H2⟩ := H α hα
  have hα' : 1 / 2 < α := hα₀.1.trans_le hα.1
  set q := A / (A + 1) with hq
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hq1 : q < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set K := C' + q * (Cs - C') with hK
  have hd0 : 0 < Cs - C' := by linarith [hC'.2]
  have hKC' : C' < K := by nlinarith
  have hKCs : K < Cs := by nlinarith
  refine ⟨(K + Cs) / 2, ⟨by linarith, by linarith⟩, fun β hβ => ?_⟩
  set C'' := (K + Cs) / 2 with hC''
  set C₂ := (K + C'') / 2 with hC₂
  have hCs0 : 0 < Cs := hC'.1.trans hC'.2
  have hβ8 : 0 < β / 8 := by linarith [hβ.1]
  obtain ⟨R, hR, Hconf⟩ := conf_prob h24e hγ hγ2 hD hβ8 (by linarith [hβ.2])
  obtain ⟨ε₁, hε₁, Hcov⟩ := H2 C' (ball (0 : ℂ) (R + 1)) isOpen_ball isBounded_ball (β / 8) hβ8
  obtain ⟨s, hs, Hsep⟩ := Tight.gm_S2_4a_sep hD (isCompact_closedBall (0 : ℂ) (R + 1))
    (b := β / 2) (by linarith [hβ.1]) (ε := ENNReal.ofReal (β / 8)) (ENNReal.ofReal_pos.2 hβ8)
  set s' := (C₂ - K) * s / (3 * Cs) with hs'
  have hs'0 : 0 < s' := div_pos (mul_pos (by linarith) hs) (by linarith)
  obtain ⟨b, hb, Hmod⟩ := Tight.gm_S2_4b hD (isCompact_closedBall (0 : ℂ) (R + 1)) hs'0
    (ε := ENNReal.ofReal (β / 8)) (ENNReal.ofReal_pos.2 hβ8)
  refine ⟨min (ε₁ / 2) (min (b / 4) (β / 16)), lt_min (by linarith) (lt_min (by linarith)
    (by linarith [hβ.1])), ?_⟩
  intro Ω _ P _ h hh r hr ε hε hBad
  have hε0 : 0 < ε := hε.1
  have hεe : ε < ε₁ := by linarith [hε.2.trans (min_le_left _ _)]
  have hεb : 4 * ε ≤ b := by linarith [(hε.2.trans (min_le_right _ _)).trans (min_le_left _ _)]
  have hεβ : 8 * ε < β := by
    linarith [(hε.2.trans (min_le_right _ _)).trans (min_le_right _ _), hβ.1]
  -- the four exceptional events
  set A1 : Set Ω := {ω | ∀ x ∈ (fun u => (r : ℂ) * u) '' ball (0 : ℂ) (R + 1), ∃ k : ℕ,
        ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧ ∃ m : ℤ × ℤ,
          ‖x - gridPt (ε ^ (1 + ν) * r / 100) m‖ ≤ ε ^ (1 + ν) * r / 100 ∧
          ‖x - gridPt (ε ^ (1 + ν) * r / 100) m‖ < (8 : ℝ)⁻¹ ^ k * r / 2 ∧
          h ω ∈ goodAnnulus D D' α A C' ((8 : ℝ)⁻¹ ^ k * r)
            (gridPt (ε ^ (1 + ν) * r / 100) m)}ᶜ with hA1
  have hP1 : P A1 ≤ ENNReal.ofReal (β / 8) := Hcov P h hh r hr ε ⟨hε0, hεe⟩ hBad
  set A2 : Set Ω := h ⁻¹' (D ⁻¹' confSet r R)ᶜ with hA2
  have hP2 : P A2 ≤ ENNReal.ofReal (β / 8) := Hconf P h hh r hr
  set A3 : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) (R + 1), ∀ v ∈ closedBall (0 : ℂ) (R + 1),
    β / 2 ≤ ‖u - v‖ → s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0) <
      (D (h ω)).1 ((r : ℂ) * u + 0, (r : ℂ) * v + 0)} with hA3
  have hP3 : P A3 ≤ ENNReal.ofReal (β / 8) := (Hsep P h hh r hr 0).le
  set A4 : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) (R + 1), ∀ v ∈ closedBall (0 : ℂ) (R + 1),
    ‖u - v‖ ≤ b → (D (h ω)).1 ((r : ℂ) * u + 0, (r : ℂ) * v + 0) <
      s' * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0)} with hA4
  have hP4 : P A4 ≤ ENNReal.ofReal (β / 8) := (Hmod P h hh r hr 0).le
  -- the almost sure facts
  obtain ⟨Cb, hCb, hbl⟩ := h22 hS
  have hae : ∀ᵐ ω ∂P, (∀ a b : ℂ, ∃ η, (D (h ω)).IsGeod01 a b η) ∧
      (∀ a b : ℚ × ℚ, UniqueGeod (D (h ω)) (ratPt a) (ratPt b)) ∧
      ∀ x y, (D' (h ω)).1 (x, y) ≤ Cs * (D (h ω)).1 (x, y) := by
    filter_upwards [gm_S1_1 h38 hγ hγ2 hD P h hh, gm_S1_2_rat hMQ hγ hγ2 hD P h hh,
      hbl P h hh, hRat P h hh] with ω h1 h2 h3 h4
    refine ⟨fun a b => h1 a b, h2, fun x y => ?_⟩
    by_cases hxy : x = y
    · subst hxy; rw [(D' (h ω)).2.self_eq_zero, (D (h ω)).2.self_eq_zero, mul_zero]
    · have hm := ratio_mem_of_bilip h3
      have ha : BddAbove (range fun p : {p : ℂ × ℂ // p.1 ≠ p.2} =>
          (D' (h ω)).1 p.1 / (D (h ω)).1 p.1) := ⟨Cb, by rintro _ ⟨p, rfl⟩; exact (hm p).2⟩
      have := le_ciSup ha ⟨(x, y), hxy⟩
      rw [← upperRatio, h4.2] at this
      exact (div_le_iff₀ (dist_pos_of_ne _ hxy)).1 this
  -- scaling `x = r u`
  have hsc : ∀ x : ℂ, (r : ℂ) * (x / r) + 0 = x := fun x => by
    rw [add_zero, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr.ne')]
  have hnsc : ∀ x : ℂ, ‖x / r‖ = ‖x‖ / r := fun x => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hball : ∀ x : ℂ, ∀ ρ : ℝ, x ∈ ball (0 : ℂ) (ρ * r) → x / r ∈ closedBall (0 : ℂ) ρ :=
    fun x ρ hx => by
      rw [mem_closedBall_zero_iff, hnsc, div_le_iff₀ hr]
      exact (mem_ball_zero_iff.1 hx).le
  have hdsc : ∀ x y : ℂ, ‖x / r - y / r‖ = ‖x - y‖ / r := fun x y => by rw [← sub_div, hnsc]
  calc P (h ⁻¹' GUp D D' r C'' β) ≤ P (A1 ∪ A2 ∪ A3 ∪ A4) := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with ω ⟨hex, hun, hratio⟩ hω
        by_contra hn
        simp only [mem_union, not_or] at hn
        obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hn
        rw [hA1, mem_compl_iff, not_not, mem_ofPred_eq] at n1
        rw [hA2, mem_preimage, mem_compl_iff, not_not, mem_preimage] at n2
        rw [hA3, mem_ofPred_eq, not_not] at n3
        rw [hA4, mem_ofPred_eq, not_not] at n4
        set X := c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0)
        have key := p36_ratio_le (D := D) (D' := D') (g := h ω) (A := A) hex hun hα' hα.2 (by linarith)
          hC'.1.le hC'.2.le hratio (ν := ν) (C₂ := C₂) (s := s) (s' := s') (X := X) hr hR hβ.1
          hε0 hεβ (by rw [hs']; field_simp; rw [hK, hq]; field_simp) (by linarith) n2
          (fun x hx => by
            obtain ⟨k, hk1, hk2, m, -, hlt, hg⟩ := n1 x ⟨x / r, by
              rw [mem_ball_zero_iff, hnsc, div_lt_iff₀ hr]; exact mem_ball_zero_iff.1 hx,
              by simp only; rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr.ne')]⟩
            exact ⟨_, _, ⟨mul_le_mul_of_nonneg_right hk1 hr.le,
              mul_le_mul_of_nonneg_right hk2 hr.le, hg⟩, by rw [mem_ball, dist_eq_norm]; exact hlt⟩)
          (fun x hx y hy hxy => by
            have := n3 (x / r) (hball x (R + 1) (ball_subset_ball (by nlinarith) hx))
              (y / r) (hball y (R + 1) (ball_subset_ball (by nlinarith) hy)) (by rw [hdsc, le_div_iff₀ hr]; linarith)
            rw [hsc, hsc, mul_assoc] at this
            exact this)
          (fun x hx y hy hxy => by
            have := n4 (x / r) (hball x _ hx) (y / r) (hball y _ hy)
              (by rw [hdsc, div_le_iff₀ hr]; nlinarith)
            rw [hsc, hsc, mul_assoc] at this
            exact this.le)
        obtain ⟨z, hz, w, hw, hzw, hge⟩ := hω
        have hk := key z hz w hw hzw
        have hzw0 : z ≠ w := by
          intro e; rw [e, sub_self, norm_zero] at hzw; nlinarith [hβ.1]
        have hpos := dist_pos_of_ne (D (h ω)) hzw0
        nlinarith
    _ ≤ P A1 + P A2 + P A3 + P A4 := by
        calc P (A1 ∪ A2 ∪ A3 ∪ A4) ≤ P (A1 ∪ A2 ∪ A3) + P A4 := measure_union_le _ _
          _ ≤ P (A1 ∪ A2) + P A3 + P A4 := by gcongr; exact measure_union_le _ _
          _ ≤ P A1 + P A2 + P A3 + P A4 := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (β / 8) + ENNReal.ofReal (β / 8) + ENNReal.ofReal (β / 8) +
          ENNReal.ofReal (β / 8) := by gcongr
    _ < ENNReal.ofReal β := by
        rw [← ENNReal.ofReal_add hβ8.le hβ8.le, ← ENNReal.ofReal_add (by positivity) hβ8.le,
          ← ENNReal.ofReal_add (by positivity) hβ8.le]
        exact (ENNReal.ofReal_lt_ofReal_iff hβ.1).2 (by linarith [hβ.1])

/-- **GM Proposition 3.6** with GM Lemma 3.9 from Lemma 3.8 (`gm_L3_9`, `gm_L3_8`): hypotheses
GM Lemma 3.7, GM Prop 2.2, GM Lemma 2.11 (closed form) and the Blueprint items `LMLem3_1a`,
`DFGPSLem3_8`, `GMS2_4e`, `MQThm1_2Weak`. -/
theorem gm_P3_6 (h37 : L3_7) (h31a : LMLem3_1a) (h22 : P2_2) (h211 : L2_11c)
    (h38 : DFGPSLem3_8) (h24e : GMS2_4e) (hMQ : MQThm1_2Weak) : P3_6 :=
  gm_P3_6_of (gm_L3_9 (gm_L3_8 h37 h31a h22 h211 h38)) h22 h38 h24e hMQ

/-- **GM Proposition 3.4** from the same inputs -/
theorem gm_P3_4_of_nodes (h37 : L3_7) (h31a : LMLem3_1a) (h22 : P2_2) (h211 : L2_11c)
    (h38 : DFGPSLem3_8) (h24e : GMS2_4e) (hMQ : MQThm1_2Weak) : P3_4 :=
  gm_P3_4 (gm_P3_6 h37 h31a h22 h211 h38 h24e hMQ)

end LQGMetric.GM
