/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond2Prob
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond3

/-!
# GM Lemma 4.11, condition 7 (DV-B4): `ℰ^𝕫_{ℓ𝕣}(a)` for every `𝕫 ∈ 𝕣U`

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, Remark 4.10 (l. 1975–1977: "Due to
conditions 2, 3, and 6, and since `ℓ ∈ (0,1)`, for each `𝕫 ∈ 𝕣U` the event `ℰ_𝕣` … is contained
in the event `ℰ^𝕫_{ℓ𝕣}(a)`") and l. 1161. Condition 7 (`regC7`, DV-B4) is the simultaneous event;
following GM's Remark we derive it from the conditions of `ℰ` themselves, applied at the scale
`ℓ𝕣` where the scales differ:
* parts 1–2 of `ℰ^𝕫_{ℓ𝕣}(a)` (ball comparison, `τ_{3ℓ𝕣} − τ_{2ℓ𝕣}`) follow from condition 2 at
  scale `𝕣` (`ℓ ≤ 1`);
* part 3 (Hölder bound normalized by `𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)}`) follows from condition 3 at scale
  `ℓ𝕣` with a slightly larger exponent `χ₂ ∈ (χ, ξ(Q−2))`, normalized at `0`, and condition 4 at
  scale `ℓ𝕣` (`|h_{ℓ𝕣}(𝕫) − h_{ℓ𝕣}(0)| ≤ M`); the factor `e^{|ξ|M}` is absorbed by
  `(|u−v|/ℓ𝕣)^{χ₂−χ} ≤ a^{χ₂−χ}`;
* part 4 (the radii `ρ`) is condition 6 at scale `ℓ𝕣`.
(Own argument for the details: GM's Remark has no proof; the deviation DV-B4 already records that
the Remark is not literally implied by conditions 2, 3, 6 at the same scale.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

theorem gm_mem_rScale_rScale {𝕣 ℓ : ℝ} (hℓ : 0 < ℓ) {U : Set ℂ} {𝕫 : ℂ}
    (h𝕫 : 𝕫 ∈ rScale 𝕣 U) : 𝕫 ∈ rScale (ℓ * 𝕣) (rScale ℓ⁻¹ U) := by
  obtain ⟨x, hx, rfl⟩ := h𝕫
  have : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hℓ.ne'
  refine ⟨(ℓ⁻¹ : ℝ) * x, ⟨x, hx, rfl⟩, ?_⟩
  push_cast
  field_simp

/-- **GM Lemma 4.11, condition 7** (DV-B4; GM Remark 4.10): condition 7 of `ℰ_𝕣` holds with
probability `→ 1` as `a → 0`, uniformly in `𝕣`. -/
theorem gm_regC7_prob (h318 : DFGPSProp3_18) (h320 : DFGPSLem3_20) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {p : CONFParams} (h35 : CONFLem3_5At γ D c p) {χ χ' : ℝ} (hχ : 0 < χ)
    (hχQ : χ < xiGamma γ * (Q γ - 2)) (hχ' : xiGamma γ * (Q γ + 2) < χ')
    {U V : Set ℂ} {ℓ : ℝ} (hV : Bornology.IsBounded V) (hUV : U ⊆ V) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ), IsWholePlaneGFF h P →
      DFGPS.IsCircleAvgVersion h P H → ∀ R : RegPar, R.ξ = xiGamma γ → R.c = c → R.p = p →
      R.χ = χ → R.χ' = χ' → R.U = U → R.V = V → R.ℓ = ℓ →
      RegCondAt P (regC7 D P h H R) q a₀ := by
  obtain ⟨ρ₀, hρ₀⟩ := hV.subset_ball (0 : ℂ)
  set ξ := xiGamma γ with hξdef
  set χ₂ : ℝ := (χ + ξ * (Q γ - 2)) / 2 with hχ₂
  have hχχ₂ : χ < χ₂ := by rw [hχ₂]; linarith
  have hχ₂Q : χ₂ < ξ * (Q γ - 2) := by rw [hχ₂]; linarith
  set V' : Set ℂ := rScale ℓ⁻¹ U with hV'
  have hV'b : Bornology.IsBounded V' :=
    isBounded_ball.subset (gm_rScale_subset_ball (inv_pos.2 hℓ) (hUV.trans hρ₀))
  have hcpos : ∀ r, 0 < r → 0 < c r := hD.tightness.1
  intro q hq
  set η := 1 - q with hη
  have hη0 : 0 < η := by linarith
  obtain ⟨a₂, ha₂, H2⟩ := gm_regC2_prob hγ hγ2 hD hV hℓ (1 - η / 4) (by linarith)
  obtain ⟨a₃, ha₃, H3⟩ := gm_regC3_prob h318 h320 hγ hγ2 hD (χ := χ₂)
    (by show 0 < χ₂; linarith) hχ₂Q hχ' (ℓ := 1) hV'b (1 - η / 4) (by linarith)
  obtain ⟨A, hA, H4⟩ := gm_regC4_prob hV'b (1 - η / 4) (by linarith)
  obtain ⟨a₆, ha₆, H6⟩ := gm_regC6_prob h35 (ℓ := 1) hV'b (1 - η / 4) (by linarith)
  set M := A⁻¹ with hM
  have hd : 0 < χ₂ - χ := by linarith
  set aS : ℝ := Real.exp (-(|ξ| * M) / (χ₂ - χ)) with haS
  refine ⟨min (min a₂ a₃) (min a₆ aS), lt_min (lt_min ha₂ ha₃) (lt_min ha₆ (Real.exp_pos _)), ?_⟩
  intro Ω _ P _ h H hh hH R hξ hc hp hRχ hRχ' hRU hRV hRℓ
  subst hRχ hRχ' hRU hRV hRℓ
  set R' : RegPar := { R with χ := χ₂, ℓ := 1, V := V' } with hR'
  rintro a ⟨ha0, ha⟩ 𝕣 h𝕣
  have ha₂' : a ≤ a₂ := ha.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ha₃' : a ≤ a₃ := ha.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ha₆' : a ≤ a₆ := ha.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haS' : a ≤ aS := ha.trans ((min_le_right _ _).trans (min_le_right _ _))
  set L := R.ℓ * 𝕣 with hL
  have hL0 : 0 < L := by positivity
  have hpow : a ^ (χ₂ - R.χ) * Real.exp (|ξ| * M) ≤ 1 := by
    have h1 : a ^ (χ₂ - R.χ) ≤ aS ^ (χ₂ - R.χ) := Real.rpow_le_rpow ha0.le haS' hd.le
    rw [haS, ← Real.exp_mul, div_mul_cancel₀ _ hd.ne'] at h1
    calc a ^ (χ₂ - R.χ) * Real.exp (|ξ| * M) ≤ Real.exp (-(|ξ| * M)) * Real.exp (|ξ| * M) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  set N0 : Set Ω := {ω | ¬ H L 0 ω = circleAvg (h ω) L 0} with hN0
  have hN0P : P N0 = 0 := ae_iff.1 (hH.ae_eq L hL0 0)
  have hsub : (regC7 D P h H R 𝕣 a)ᶜ ⊆ (regC2 D h H R 𝕣 a)ᶜ ∪ (regC3 D h R' L a)ᶜ ∪
      (regC4 H R' L A)ᶜ ∪ (regC6 D P h R' L a)ᶜ ∪ N0 := by
    intro ω hω
    by_contra hn
    apply hω
    simp only [mem_union, not_or, mem_compl_iff, not_not] at hn
    obtain ⟨⟨⟨⟨h2, h3⟩, h4⟩, h6⟩, hn0⟩ := hn
    simp only [hN0, mem_ofPred_eq, not_not] at hn0
    refine mem_iInter₂.2 fun 𝕫 h𝕫 => ?_
    have h𝕫R : 𝕫 ∈ regRegion R 𝕣 :=
      Metric.self_subset_thickening (by positivity) _ (image_mono hUV h𝕫)
    have h𝕫' : 𝕫 ∈ rScale L V' := gm_mem_rScale_rScale hℓ h𝕫
    have hreg : ∀ u ∈ ball 𝕫 (4 * L), u ∈ regRegion R' L := fun u hu =>
      Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫', by
        rw [mem_ball] at hu; show dist u 𝕫 < 4 * (1 * L); linarith⟩
    obtain ⟨hball, hincr⟩ := h2 𝕫 h𝕫R
    set sfz := R.c L * Real.exp (R.ξ * H L 𝕫 ω) with hsfz
    have hsfz0 : 0 < sfz := by rw [hsfz, hc]; exact mul_pos (hcpos L hL0) (Real.exp_pos _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- part 1
      refine (ball_subset_ball ?_).trans hball
      have := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left h𝕣.le hℓ1) ha0.le
      linarith
    · -- part 2
      refine le_trans ?_ (hincr.trans (min_le_right _ _))
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) ha0.le
    · -- part 3
      intro u hu v hv huv
      have huvL : ‖u - v‖ ≤ a * L := by rwa [div_le_iff₀ hL0] at huv
      have H3uv := h3 u (hreg u hu) v (hreg v hv) huvL
      by_cases heq : u = v
      · subst heq
        rw [(D (h ω)).2.self_eq_zero, mul_zero, sub_self, norm_zero, zero_div,
          Real.zero_rpow hχ.ne']
      have hx0 : 0 < ‖u - v‖ / L := div_pos (norm_pos_iff.2 (sub_ne_zero.2 heq)) hL0
      have hup := H3uv.2 heq
      -- the normalization at `0`
      set sf0 := scaleFac R'.ξ R'.c (h ω) L 0 with hsf0
      have hsf00 : 0 < sf0 := by
        rw [hsf0]; show 0 < R.c L * _; rw [hc]; exact mul_pos (hcpos L hL0) (Real.exp_pos _)
      have hD0 : 0 ≤ (D (h ω)).1 (u, v) := dist_nonneg (x := (D (h ω)).pt u) (y := (D (h ω)).pt v)
      have hint : ENNReal.ofReal ((D (h ω)).1 (u, v)) ≤
          (D (h ω)).internal (ball u (2 * ‖u - v‖)) u v :=
        (le_of_eq (edist_dist ((D (h ω)).pt u) ((D (h ω)).pt v)).symm).trans
          (MetricGeometry.edist_le_internalEDist _ _ _)
      have hreal : sf0⁻¹ * (D (h ω)).1 (u, v) ≤ ‖(u - v) / L‖ ^ R'.χ := by
        have := (mul_le_mul_of_nonneg_left hint (by positivity)).trans hup
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hsf00.le)] at this
        exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (norm_nonneg _) _)).1 this
      have hnorm : ‖(u - v) / L‖ = ‖u - v‖ / L := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
      rw [hnorm] at hreal
      -- `sf0 ≤ e^{|ξ|M} sfz`
      have hmod : |H L 0 ω - H L 𝕫 ω| ≤ M := by
        have := h4 𝕫 h𝕫'
        rw [abs_sub_comm]; exact this
      have hcmp := gm_c2_exp_le (ξ := R.ξ) (hcpos L hL0).le hmod
      have hsf0eq : sf0 = c L * Real.exp (R.ξ * H L 0 ω) := by
        rw [hsf0, hn0]; show R.c L * _ = _; rw [hc]
      rw [← hsf0eq, hξ] at hcmp
      have hcmp' : sf0 ≤ Real.exp (|ξ| * M) * sfz := by
        have e1 : sfz = c L * Real.exp (ξ * H L 𝕫 ω) := by rw [hsfz, hc, hξ]
        rw [e1]; exact hcmp
      -- conclude
      have hsplit : (‖u - v‖ / L) ^ χ₂ = (‖u - v‖ / L) ^ (χ₂ - R.χ) * (‖u - v‖ / L) ^ R.χ := by
        rw [← Real.rpow_add hx0]; ring_nf
      have hxa : (‖u - v‖ / L) ^ (χ₂ - R.χ) ≤ a ^ (χ₂ - R.χ) :=
        Real.rpow_le_rpow hx0.le huv hd.le
      have hxχ : 0 ≤ (‖u - v‖ / L) ^ R.χ := Real.rpow_nonneg hx0.le _
      have hDle : (D (h ω)).1 (u, v) ≤ sf0 * (‖u - v‖ / L) ^ χ₂ := by
        rw [inv_mul_le_iff₀ hsf00] at hreal; exact hreal
      rw [inv_mul_le_iff₀ hsfz0]
      calc (D (h ω)).1 (u, v) ≤ sf0 * (‖u - v‖ / L) ^ χ₂ := hDle
        _ ≤ (Real.exp (|ξ| * M) * sfz) * ((‖u - v‖ / L) ^ (χ₂ - R.χ) * (‖u - v‖ / L) ^ R.χ) := by
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right hcmp' (by positivity)
        _ ≤ (Real.exp (|ξ| * M) * sfz) * (a ^ (χ₂ - R.χ) * (‖u - v‖ / L) ^ R.χ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxa hxχ) (by positivity)
        _ = sfz * (‖u - v‖ / L) ^ R.χ * (a ^ (χ₂ - R.χ) * Real.exp (|ξ| * M)) := by ring
        _ ≤ sfz * (‖u - v‖ / L) ^ R.χ * 1 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = sfz * (‖u - v‖ / L) ^ R.χ := mul_one _
    · -- part 4
      intro j hj z hz
      exact h6 j hj z ⟨hz.1, hreg z hz.2⟩
  calc P (regC7 D P h H R 𝕣 a)ᶜ ≤ P ((regC2 D h H R 𝕣 a)ᶜ ∪ (regC3 D h R' L a)ᶜ ∪
        (regC4 H R' L A)ᶜ ∪ (regC6 D P h R' L a)ᶜ ∪ N0) := measure_mono hsub
    _ ≤ P (regC2 D h H R 𝕣 a)ᶜ + P (regC3 D h R' L a)ᶜ + P (regC4 H R' L A)ᶜ +
        P (regC6 D P h R' L a)ᶜ + P N0 := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 - (1 - η / 4)) + ENNReal.ofReal (1 - (1 - η / 4)) +
        ENNReal.ofReal (1 - (1 - η / 4)) + ENNReal.ofReal (1 - (1 - η / 4)) + 0 := by
        rw [hN0P]
        gcongr
        · exact H2 P h H hh hH R hξ hc rfl rfl a ⟨ha0, ha₂'⟩ 𝕣 h𝕣
        · exact H3 P h hh R' hξ hc rfl rfl rfl rfl a ⟨ha0, ha₃'⟩ L hL0
        · exact H4 P h H hh hH R' rfl A ⟨hA, le_rfl⟩ L hL0
        · exact H6 P h hh R' hξ hc hp rfl rfl a ⟨ha0, ha₆'⟩ L hL0
    _ = ENNReal.ofReal (1 - q) := by
        rw [add_zero, ← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; rw [hη]; ring

end LQGMetric.GM
