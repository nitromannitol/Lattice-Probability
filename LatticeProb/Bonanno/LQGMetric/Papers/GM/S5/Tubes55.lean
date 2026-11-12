/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes55 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes55Det
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulusClosed
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightC
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# GM Lemma 5.5 (`lem-endpoint-geodesic`) (task P2-M2L)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, Lemma 5.5, l. 2890–2912. GM's proof,
step by step:
* "By Axioms IV and V we can find `S > s > 0` … with probability at least `1 − p_0/2`" (l. 2900–2906):
  `Tight.gm_S2_4a_sep` (separated points of `cl 𝔸_{3r/4,r}(z)`, see deviation P2-M2L-3 in
  `Tubes55Det`), `Tight.gm_S2_4a` (`𝔸_{3r/4,r}(z)` to `∂B_{2r}(z)`), `Tight.gm_S2_4c` (upper bound),
  each with failure probability `< p_0/8`;
* "Lemma 2.11 applied with the above choice of `s` and `S` gives an `α`" (l. 2907–2910): `L2_11c`
  (GM Lemma 2.11 for the closed annulus, proved as `gm_L2_11_closed`), failure `≤ p_0/8`;
* "Combining this with translation invariance (Axiom IV) and the definition of `𝓡_0`" (l. 2911):
  `r ∈ 𝓡_0` applied to the whole-plane GFF `h(· + z)`, and Axiom IV′ for `D` and `D̃`;
* "This random quarter annulus is a.s. contained in one of four possible deterministic
  half-annuli, so must be contained in one of these four half-annuli with probability at least
  `p_0/8`" (l. 2912): pigeonhole over `Fin 4` (`endpoint_core`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

lemma scale_back {r : ℝ} (hr : 0 < r) (x z : ℂ) : (r : ℂ) * ((x - z) / r) + z = x := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp; ring

lemma norm_scale_back {r : ℝ} (hr : 0 < r) (x z : ℂ) : ‖(x - z) / (r : ℂ)‖ = ‖x - z‖ / r := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]

lemma norm_scale_back_sub {r : ℝ} (hr : 0 < r) (x y z : ℂ) :
    ‖(x - z) / (r : ℂ) - (y - z) / r‖ = ‖x - y‖ / r := by
  rw [← sub_div, sub_sub_sub_cancel_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]

/-- **GM Lemma 5.5** (`lem-endpoint-geodesic`, l. 2890–2912), from GM Lemma 2.11 (closed-annulus
form). -/
theorem gm_L5_5 (h211 : L2_11c) : L5_5 := by
  intro γ D D' c cs Cs hset hcs hCs α₀ p₀ hα₀ hp₀ hp₀1
  obtain ⟨hγ, hγ2, hD, hD'⟩ := hset
  set ε : ℝ≥0∞ := ENNReal.ofReal (p₀ / 8) with hεdef
  have hε : 0 < ε := ENNReal.ofReal_pos.2 (by linarith)
  set K : Set ℂ := Metric.closedBall 0 1 \ Metric.ball 0 (3 / 4) with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hKmem : ∀ w : ℂ, w ∈ K ↔ ‖w‖ ≤ 1 ∧ 3 / 4 ≤ ‖w‖ := by
    intro w; simp [hKdef, not_lt]
  have hdisj : Disjoint K (Metric.sphere (0 : ℂ) 2) := by
    rw [Set.disjoint_left]
    intro w hw hs
    rw [hKmem] at hw
    rw [mem_sphere_zero_iff_norm] at hs
    linarith [hw.1]
  obtain ⟨s₁, hs₁, H1⟩ := Tight.gm_S2_4a_sep hD' hK (b := 1 / 4) (by norm_num) hε
  obtain ⟨s₂, hs₂, H2⟩ := Tight.gm_S2_4a hD' hK (isCompact_sphere 0 2) hdisj hε
  obtain ⟨S₀, hS₀, H3⟩ := Tight.gm_S2_4c hD' (U := Metric.ball 0 2) Metric.isOpen_ball
    (Metric.isConnected_ball (by norm_num)) Metric.isBounded_ball (isCompact_closedBall (0 : ℂ) 1)
    (Metric.closedBall_subset_ball (by norm_num)) hε
  set κ : ℝ := (cs / Cs) ^ 2 with hκdef
  have hκ : 0 < κ := by positivity
  set s : ℝ := min s₁ (κ * s₂) with hsdef
  have hs : 0 < s := lt_min hs₁ (by positivity)
  set S : ℝ := S₀ + s with hSdef
  obtain ⟨α₁, -, hα₁1, H4⟩ := h211 hγ hγ2 hD' (s := s) (S := S) (p := 1 - p₀ / 8) hs
    (by rw [hSdef]; linarith) (by linarith) (by linarith)
  set α : ℝ := max (max α₀ α₁) (3 / 4) with hαdef
  have hα1 : α < 1 := max_lt (max_lt hα₀ hα₁1) (by norm_num)
  have hα34 : 3 / 4 ≤ α := le_max_right _ _
  refine ⟨α, ⟨(le_max_left _ _).trans (le_max_left _ _), hα1⟩, hα34, ?_⟩
  intro c₁ r hr z Ω _ P _ h hh
  have hr0 : 0 < r := hr.1
  have hGz := hr.2 P (fun ω => affineComp 1 z (h ω)) (hh.affineComp one_pos z)
  have hT := hD.translation P h (Tight.isGFFPlusCont_of_wp hh) z
  have hT' := hD'.translation P h (Tight.isGFFPlusCont_of_wp hh) z
  have hB1 := H1 P h hh r hr0 z
  have hB2 := H2 P h hh r hr0 z
  have hB3 := H3 P h hh r hr0 z
  have hB4 := H4 α ⟨(le_max_right _ _).trans (le_max_left _ _), hα1⟩ z r hr0 P h hh
  rw [show (1 : ℝ) - (1 - p₀ / 8) = p₀ / 8 by ring] at hB4
  set Good : Fin 4 → Set Ω := fun k =>
    h ⁻¹' endpointEvent D D' cs Cs α c₁ r z (halfAnn z (α * r) r k) with hGood
  -- the deterministic inclusion
  have hincl : (fun ω => affineComp 1 z (h ω)) ⁻¹' attainedLow D D' α r c₁ ⊆
      (⋃ k, Good k) ∪ {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, 1 / 4 ≤ ‖u - v‖ →
          s₁ * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
            (D' (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ Metric.sphere (0 : ℂ) 2,
          s₂ * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
            (D' (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)} ∪
        {ω | ¬ ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ∀ v ∈ Metric.closedBall (0 : ℂ) 1,
          (D' (h ω)).internal ((fun w => (r : ℂ) * w + z) '' Metric.ball 0 2)
            ((r : ℂ) * u + z) ((r : ℂ) * v + z) ≤
              ENNReal.ofReal (S₀ * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z))} ∪
        {ω | ∀ u ∈ closure (annulus z (α * r) r : Set ℂ),
          ∀ v ∈ closure (annulus z (α * r) r : Set ℂ),
            s * scaleFac (xiGamma γ) c (h ω) r z ≤ (D' (h ω)).1 (u, v) →
              ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z) ≤
                (D' (h ω)).internal (closure (annulus z (α * r) r : Set ℂ)) u v}ᶜ ∪
        {ω | ¬ ∀ u v : ℂ, (D (affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)} ∪
        {ω | ¬ ∀ u v : ℂ, (D' (affineComp 1 z (h ω))).1 (u, v) = (D' (h ω)).1 (u + z, v + z)} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, not_or, not_not] at hnot
    obtain ⟨⟨⟨⟨⟨⟨hG, h1⟩, h2⟩, h3⟩, h4⟩, ht⟩, ht'⟩ := hnot
    apply hG
    set σ : ℝ := scaleFac (xiGamma γ) c (h ω) r z with hσdef
    have hσ : 0 < σ := mul_pos (hD.tightness.1 r hr0) (Real.exp_pos _)
    have hσe : ∀ a : ℝ, a * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) = a * σ := by
      intro a; rw [hσdef, scaleFac]; ring
    obtain ⟨u, hu, v, hv, hc, hgeo⟩ := hω
    beta_reduce at hc
    rw [ht', ht] at hc
    have hgeo' := uniqueGeodIn_mono (uniqueGeodIn_translate ht' hgeo)
      (image_closure_annulus_subset z (α * r) r)
    have hu' : u + z ∈ Metric.sphere z (α * r) := by
      rw [mem_sphere_iff_norm, add_sub_cancel_right]; exact mem_sphere_zero_iff_norm.1 hu
    have hv' : v + z ∈ Metric.sphere z r := by
      rw [mem_sphere_iff_norm, add_sub_cancel_right]; exact mem_sphere_zero_iff_norm.1 hv
    have hA1 : ∀ x y : ℂ, 3 / 4 * r ≤ ‖x - z‖ → ‖x - z‖ ≤ r → 3 / 4 * r ≤ ‖y - z‖ →
        ‖y - z‖ ≤ r → r / 4 ≤ ‖x - y‖ → s₁ * σ < (D' (h ω)).1 (x, y) := by
      intro x y hx1 hx2 hy1 hy2 hxy
      have := h1 ((x - z) / r)
        ((hKmem _).2 ⟨by rw [norm_scale_back hr0, div_le_one hr0]; exact hx2,
          by rw [norm_scale_back hr0, le_div_iff₀ hr0]; exact hx1⟩) ((y - z) / r)
        ((hKmem _).2 ⟨by rw [norm_scale_back hr0, div_le_one hr0]; exact hy2,
          by rw [norm_scale_back hr0, le_div_iff₀ hr0]; exact hy1⟩)
        (by rw [norm_scale_back_sub hr0, le_div_iff₀ hr0]; linarith)
      rwa [scale_back hr0, scale_back hr0, hσe] at this
    have hA2 : ∀ x : ℂ, 3 / 4 * r ≤ ‖x - z‖ → ‖x - z‖ ≤ r → ∀ y ∈ Metric.sphere z (2 * r),
        s₂ * σ < (D' (h ω)).1 (x, y) := by
      intro x hx1 hx2 y hy
      have hy' : ‖y - z‖ = 2 * r := mem_sphere_iff_norm.1 hy
      have := h2 ((x - z) / r)
        ((hKmem _).2 ⟨by rw [norm_scale_back hr0, div_le_one hr0]; exact hx2,
          by rw [norm_scale_back hr0, le_div_iff₀ hr0]; exact hx1⟩) ((y - z) / r)
        (by rw [mem_sphere_zero_iff_norm, norm_scale_back hr0, hy']; field_simp)
      rwa [scale_back hr0, scale_back hr0, hσe] at this
    have hA3 : ∀ x y : ℂ, ‖x - z‖ ≤ r → ‖y - z‖ ≤ r → (D' (h ω)).1 (x, y) ≤ S₀ * σ := by
      intro x y hx hy
      have := h3 ((x - z) / r)
        (by rw [mem_closedBall_zero_iff, norm_scale_back hr0, div_le_one hr0]; exact hx)
        ((y - z) / r)
        (by rw [mem_closedBall_zero_iff, norm_scale_back hr0, div_le_one hr0]; exact hy)
      rw [scale_back hr0, scale_back hr0, hσe] at this
      have he := edist_le_internalEDist ((D' (h ω)).pt '' ((fun w => (r : ℂ) * w + z) ''
        Metric.ball 0 2)) ((D' (h ω)).pt x) ((D' (h ω)).pt y)
      have h5 : ENNReal.ofReal ((D' (h ω)).1 (x, y)) ≤ ENNReal.ofReal (S₀ * σ) := by
        have e1 : edist ((D' (h ω)).pt x) ((D' (h ω)).pt y) = ENNReal.ofReal ((D' (h ω)).1 (x, y)) :=
          edist_dist _ _
        rw [← e1]; exact he.trans this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h5
    obtain ⟨k, hk1, hk2⟩ := endpoint_core (κ := κ) hr0 hα34 hσ (min_le_left _ _)
      (min_le_right _ _) hκ.le hS₀.le (by rw [hSdef]; linarith) hA1 hA2 hA3 h4 hu' hv' hgeo'
    simp only [mem_iUnion]
    exact ⟨k, u + z, hu', v + z, hv', hc, hk1, hk2⟩
  -- probabilities
  have hnull : P {ω | ¬ ∀ u v : ℂ, (D (affineComp 1 z (h ω))).1 (u, v) =
      (D (h ω)).1 (u + z, v + z)} = 0 := ae_iff.1 hT
  have hnull' : P {ω | ¬ ∀ u v : ℂ, (D' (affineComp 1 z (h ω))).1 (u, v) =
      (D' (h ω)).1 (u + z, v + z)} = 0 := ae_iff.1 hT'
  have hsum : ENNReal.ofReal p₀ ≤ (∑ k, P (Good k)) + 4 * ε := by
    calc ENNReal.ofReal p₀ ≤ _ := hGz
      _ ≤ _ := measure_mono hincl
      _ ≤ P (⋃ k, Good k) + ε + ε + ε + ε + 0 + 0 := by
        refine (measure_union_le _ _).trans (add_le_add ?_ hnull'.le)
        refine (measure_union_le _ _).trans (add_le_add ?_ hnull.le)
        refine (measure_union_le _ _).trans (add_le_add ?_ hB4)
        refine (measure_union_le _ _).trans (add_le_add ?_ hB3.le)
        refine (measure_union_le _ _).trans (add_le_add ?_ hB2.le)
        exact (measure_union_le _ _).trans (add_le_add le_rfl hB1.le)
      _ = P (⋃ k, Good k) + 4 * ε := by ring
      _ ≤ (∑ k, P (Good k)) + 4 * ε := by gcongr; exact measure_iUnion_fintype_le _ _
  by_contra hne
  push Not at hne
  have hlt : ∑ k, P (Good k) < ∑ _k : Fin 4, ε :=
    ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ => by
      have := hne (halfAnn z (α * r) r k) (isHalfAnnulus_halfAnn _ _ _ k)
      simpa [hGood, hεdef] using this
  have hε4 : ∑ _k : Fin 4, ε = 4 * ε := by simp [Finset.sum_const]
  have h8 : ENNReal.ofReal p₀ = 4 * ε + 4 * ε := by
    have : p₀ = 8 * (p₀ / 8) := by ring
    rw [this, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← hεdef]
    ring
  rw [hε4] at hlt
  have hfin : 4 * ε ≠ ∞ := ENNReal.mul_ne_top (by simp) (by simp [hεdef])
  have := ENNReal.add_lt_add_right hfin hlt
  rw [← h8] at this
  exact absurd hsum (not_le.2 this)

end LQGMetric.GM
