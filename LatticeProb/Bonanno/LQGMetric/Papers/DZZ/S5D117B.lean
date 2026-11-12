/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B9
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward

/-!
# D117 packet P-SIM (b): walled LGDs of two chaos limits related by a similarity (P2-DZZSIM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) use lem-scaling-coupling (l. 611–624) together with
Lemma 3.8 (`lem-LGD-compare`, l. 1218–1233) for boxes related by `θ v = a v + b`
(l. 2318–2322, 2538–2548, Remark 5.2 l. 2281–2284): the chaos `M^{(2)}` on `θ 𝕍₁` pulled back by
`θ` is (up to the Jacobian `|a|²`) the chaos of `ζ⁽²⁾ ∘ θ`, so a uniform comparison of the
exponents `γ ζ⁽¹⁾_{2^{-n}}(v) − γ²/2 Var` and `γ ζ⁽²⁾_{a 2^{-n}}(θ v) − γ²/2 Var` on `𝕍₁` gives
the comparison of the LGDs as in the proof of Lemma 3.8 (l. 1229–1232).

This file is the deterministic part, for walled measures (`dzzWall`, DEC-117 §1):

* `chaos_sim_ball_le`, `chaos_sim_ball_ge`: mass comparison `M⁽¹⁾(B)` vs `|a|^{∓2} M⁽²⁾(θB)` for
  balls `B ⊆ K` with rational centre, from the two chaos limits (tested on rational balls only:
  `θ B` is approximated by rational balls from inside, DZZ's (eq-def-M-eta) holds for every ball);
* `lgd_sim_sandwich`: for closed `K ⊆ 𝕍` with `θ K ⊆ 𝕍` and `|F₁ − F₂ ∘ θ| ≤ c` on `K`,
  `D^{θK}_{|a| δ e^{c/2}}(θx, θy)[M⁽²⁾] ≤ D^K_δ(x, y)[M⁽¹⁾] ≤ D^{θK}_{|a| δ e^{−c/2}}(θx, θy)[M⁽²⁾]`
  for the walled measures `dzzWall K (dzzWall 𝕍 M)` (the form of `dzzMuIn`).

The change of variables is `QuantumZipper.lintegral_comp_holo` (Jacobian `|a|²`), the LGD
transport is `lgdDZZ_map_similarity`, the core of Lemma 3.8 is `lgdDZZ_le_of_ball_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma simMap_surjective {a : ℂ} (ha : a ≠ 0) (b : ℂ) : Function.Surjective (simMap a b) :=
  fun w => ⟨(w - b) / a, by simp only [simMap]; field_simp; ring⟩

lemma simMap_injective {a : ℂ} (ha : a ≠ 0) (b : ℂ) : Function.Injective (simMap a b) :=
  fun z w h => by simp only [simMap] at h; exact mul_left_cancel₀ ha (add_right_cancel h)

lemma simMap_image_ball {a : ℂ} (ha : a ≠ 0) (b p : ℂ) (r : ℝ) :
    simMap a b '' ball p r = ball (simMap a b p) (‖a‖ * r) := by
  rw [← simMap_preimage_ball ha b p r, image_preimage_eq _ (simMap_surjective ha b)]

lemma simMap_left_inv {a : ℂ} (ha : a ≠ 0) (b z : ℂ) :
    simMap a⁻¹ (-(a⁻¹ * b)) (simMap a b z) = z := by
  simp only [simMap]; field_simp; ring

lemma simMap_right_inv {a : ℂ} (ha : a ≠ 0) (b z : ℂ) :
    simMap a b (simMap a⁻¹ (-(a⁻¹ * b)) z) = z := by
  simp only [simMap]; field_simp; ring

lemma simMap_image_eq_preimage {a : ℂ} (ha : a ≠ 0) (b : ℂ) (S : Set ℂ) :
    simMap a b '' S = simMap a⁻¹ (-(a⁻¹ * b)) ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse (simMap_left_inv ha b) (simMap_right_inv ha b)) S

lemma isClosed_simMap_image {a : ℂ} (ha : a ≠ 0) (b : ℂ) {K : Set ℂ} (hK : IsClosed K) :
    IsClosed (simMap a b '' K) := by
  rw [simMap_image_eq_preimage ha b]; exact hK.preimage (continuous_simMap _ _)

/-- change of variables under `z ↦ a z + b`: Jacobian `|a|²` -/
lemma lintegral_simMap_image {a : ℂ} (ha : a ≠ 0) (b : ℂ) {S : Set ℂ} (hS : MeasurableSet S)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ w in simMap a b '' S, g w = ENNReal.ofReal (‖a‖ ^ 2) * ∫⁻ z in S, g (simMap a b z) := by
  have hd : ∀ z, HasDerivAt (simMap a b) a z := fun z => by
    exact (((hasDerivAt_id z).const_mul a).add_const b).congr_deriv (mul_one a)
  rw [QuantumZipper.lintegral_comp_holo isOpen_univ
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    (simMap_injective ha b).injOn (fun z _ => by rw [(hd z).deriv]; exact ha) hS
    (subset_univ _) g]
  simp_rw [(hd _).deriv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- a rational ball between two concentric balls -/
lemma exists_ratBall_between {w : ℂ} {R R' : ℝ} (h0 : 0 ≤ R) (h : R < R') :
    ∃ (x : ℚ × ℚ) (q : ℚ), 0 < (q : ℝ) ∧ ball w R ⊆ ball (ratPt x) q ∧
      ball (ratPt x) q ⊆ ball w R' := by
  set ε := (R' - R) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨x, hx⟩ := denseRange_ratPt'.exists_dist_lt w hε0
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show R + ε < R' - ε by rw [hε]; linarith)
  refine ⟨x, q, by linarith, fun z hz => ?_, fun z hz => ?_⟩
  · rw [mem_ball] at hz ⊢
    have := dist_triangle z w (ratPt x)
    linarith
  · rw [mem_ball] at hz ⊢
    have := dist_triangle z (ratPt x) w
    rw [dist_comm (ratPt x) w] at this
    linarith

/-- continuity from below for concentric balls -/
lemma measure_ball_le_of_forall_lt {μ : Measure ℂ} {w : ℂ} {R : ℝ} {X : ℝ≥0∞}
    (h : ∀ R' : ℝ, 0 < R' → R' < R → μ (ball w R') ≤ X) : μ (ball w R) ≤ X := by
  have hU : ball w R = ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R}, ball w (q : ℝ) := by
    ext z
    simp only [mem_iUnion, mem_ball]
    constructor
    · intro hz
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hz
      exact ⟨⟨q, by exact_mod_cast (dist_nonneg.trans_lt hq1), hq2⟩, hq1⟩
    · rintro ⟨q, hq⟩
      exact hq.trans q.2.2
  have hd : Directed (· ⊆ ·) (fun q : {q : ℚ // 0 < q ∧ (q : ℝ) < R} => ball w (q : ℝ)) :=
    Monotone.directed_le fun a b hab =>
      ball_subset_ball (by exact_mod_cast (show (a : ℚ) ≤ b from hab))
  rw [hU, hd.measure_iUnion]
  exact iSup_le fun q => h q (by exact_mod_cast q.2.1) q.2.2

variable {γ c : ℝ} {ζ₁ ζ₂ V₁ V₂ : ℝ → ℂ → ℝ} {s₁ s₂ : ℕ → ℝ} {μ₁ μ₂ : Measure ℂ}

/-- **Mass comparison, `M⁽¹⁾ ≤ e^c |a|^{−2} M⁽²⁾ ∘ θ`** on balls `B ⊆ K` with rational centre
(DZZ l. 1229–1231, through the similarity `θ`). -/
theorem chaos_sim_ball_le (h₁ : IsChaosLimit γ ζ₁ V₁ s₁ μ₁) (h₂ : IsChaosLimit γ ζ₂ V₂ s₂ μ₂)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) {K : Set ℂ}
    (hθK : simMap a b '' K ⊆ dzzV)
    (hpt : ∀ n : ℕ, ∀ z ∈ K, γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z ≤
      c + (γ * ζ₂ (s₂ n) (simMap a b z) - γ ^ 2 / 2 * V₂ (s₂ n) (simMap a b z)))
    (x : ℚ × ℚ) (r : ℝ) (hB : ball (ratPt x) r ⊆ K) :
    μ₁ (ball (ratPt x) r) ≤
      ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (‖a‖ ^ 2))⁻¹ *
        μ₂ (simMap a b '' ball (ratPt x) r) := by
  set θ := simMap a b
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hJ0 : ENNReal.ofReal (‖a‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine measure_ball_le_of_forall_lt fun q' hq'0 hq'r => ?_
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hq'r
  have hq0 : (0 : ℝ) < q := hq'0.trans hq1
  refine (measure_mono (ball_subset_ball hq1.le)).trans ?_
  have hBq : ball (ratPt x) q ⊆ K := (ball_subset_ball hq2.le).trans hB
  obtain ⟨x'', q'', hq''0, hsub1, hsub2⟩ := exists_ratBall_between
    (w := θ (ratPt x)) (mul_pos hna hq0).le (mul_lt_mul_of_pos_left hq2 hna)
  have himq : θ '' ball (ratPt x) q = ball (θ (ratPt x)) (‖a‖ * q) :=
    simMap_image_ball ha b _ _
  have hB'' : ball (ratPt x'') q'' ⊆ θ '' ball (ratPt x) r := by
    rw [simMap_image_ball ha b]; exact hsub2
  refine (le_of_tendsto_of_tendsto' (h₁ x q (by exact_mod_cast hq0))
    (ENNReal.Tendsto.const_mul (h₂ x'' q'' (by exact_mod_cast hq''0))
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 hJ0))))
    fun n => ?_).trans (mul_le_mul_of_nonneg_left (measure_mono hB'') zero_le)
  set G₁ : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z))
  set G₂ : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (γ * ζ₂ (s₂ n) z - γ ^ 2 / 2 * V₂ (s₂ n) z))
  have hm : MeasurableSet (ball (ratPt x) (q : ℝ)) := measurableSet_ball
  calc ∫⁻ z in ball (ratPt x) q ∩ dzzV, G₁ z ≤ ∫⁻ z in ball (ratPt x) q, G₁ z :=
        lintegral_mono_set inter_subset_left
    _ ≤ ∫⁻ z in ball (ratPt x) q, ENNReal.ofReal (Real.exp c) * G₂ (θ z) := by
        refine setLIntegral_mono' hm fun z hz => ?_
        simp only [G₁, G₂]
        rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpt n z (hBq hz)))
    _ = ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (‖a‖ ^ 2))⁻¹ *
          ∫⁻ w in θ '' ball (ratPt x) q, G₂ w := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_simMap_image ha b hm,
          mul_assoc, ← mul_assoc _ (ENNReal.ofReal _), ENNReal.inv_mul_cancel hJ0
            ENNReal.ofReal_ne_top, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (‖a‖ ^ 2))⁻¹ *
          ∫⁻ w in ball (ratPt x'') q'' ∩ dzzV, G₂ w := by
        refine mul_le_mul_of_nonneg_left (lintegral_mono_set fun w hw => ⟨?_, ?_⟩) zero_le
        · rw [himq] at hw; exact hsub1 hw
        · exact hθK (image_mono hBq hw)

/-- **Mass comparison, `M⁽²⁾ ∘ θ ≤ e^c |a|² M⁽¹⁾`** on balls `B ⊆ K` with rational centre. -/
theorem chaos_sim_ball_ge (h₁ : IsChaosLimit γ ζ₁ V₁ s₁ μ₁) (h₂ : IsChaosLimit γ ζ₂ V₂ s₂ μ₂)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) {K : Set ℂ} (hKV : K ⊆ dzzV)
    (hpt : ∀ n : ℕ, ∀ z ∈ K,
      γ * ζ₂ (s₂ n) (simMap a b z) - γ ^ 2 / 2 * V₂ (s₂ n) (simMap a b z) ≤
        c + (γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z))
    (x : ℚ × ℚ) (r : ℝ) (hB : ball (ratPt x) r ⊆ K) :
    μ₂ (simMap a b '' ball (ratPt x) r) ≤
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) * μ₁ (ball (ratPt x) r) := by
  set θ := simMap a b
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [simMap_image_ball ha b]
  refine measure_ball_le_of_forall_lt fun R' hR'0 hR'r => ?_
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show R' / ‖a‖ < r by
    rwa [div_lt_iff₀ hna, mul_comm])
  have hq0 : (0 : ℝ) < q := (div_pos hR'0 hna).trans hq1
  have hBq : ball (ratPt x) q ⊆ K := (ball_subset_ball hq2.le).trans hB
  obtain ⟨x'', q'', hq''0, hsub1, hsub2⟩ := exists_ratBall_between
    (w := θ (ratPt x)) hR'0.le (show R' < ‖a‖ * q by rwa [div_lt_iff₀ hna, mul_comm] at hq1)
  have himq : θ '' ball (ratPt x) q = ball (θ (ratPt x)) (‖a‖ * q) :=
    simMap_image_ball ha b _ _
  refine (measure_mono hsub1).trans ?_
  refine (le_of_tendsto_of_tendsto' (h₂ x'' q'' (by exact_mod_cast hq''0))
    (ENNReal.Tendsto.const_mul (h₁ x q (by exact_mod_cast hq0))
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)))
    fun n => ?_).trans (mul_le_mul_of_nonneg_left (measure_mono (ball_subset_ball hq2.le)) zero_le)
  set G₁ : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z))
  set G₂ : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (γ * ζ₂ (s₂ n) z - γ ^ 2 / 2 * V₂ (s₂ n) z))
  have hm : MeasurableSet (ball (ratPt x) (q : ℝ)) := measurableSet_ball
  calc ∫⁻ w in ball (ratPt x'') q'' ∩ dzzV, G₂ w ≤ ∫⁻ w in θ '' ball (ratPt x) q, G₂ w := by
        refine lintegral_mono_set fun w hw => ?_
        rw [himq]; exact hsub2 hw.1
    _ = ENNReal.ofReal (‖a‖ ^ 2) * ∫⁻ z in ball (ratPt x) q, G₂ (θ z) :=
        lintegral_simMap_image ha b hm _
    _ ≤ ENNReal.ofReal (‖a‖ ^ 2) * ∫⁻ z in ball (ratPt x) q,
          ENNReal.ofReal (Real.exp c) * G₁ z := by
        refine mul_le_mul_of_nonneg_left (setLIntegral_mono' hm fun z hz => ?_) zero_le
        simp only [G₁, G₂]
        rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpt n z (hBq hz)))
    _ = ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) *
          ∫⁻ z in ball (ratPt x) q ∩ dzzV, G₁ z := by
        rw [inter_eq_left.2 (hBq.trans hKV), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring

lemma dzzWall_eq_of_subset {K B : Set ℂ} (μ : Measure ℂ) (hB : B ⊆ K) (hBm : MeasurableSet B) :
    dzzWall K μ B = μ B := by
  simp only [dzzWall, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hBm]
  rw [show B ∩ Kᶜ = ∅ from eq_empty_of_forall_notMem fun z hz => hz.2 (hB hz.1),
    measure_empty, mul_zero, add_zero]

lemma dzzWall_eq_top_of_not_subset {K B : Set ℂ} (hK : IsClosed K) (μ : Measure ℂ)
    (hBo : IsOpen B) (h : ¬ B ⊆ K) : dzzWall K μ B = ⊤ := by
  simp only [dzzWall, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hBo.measurableSet]
  obtain ⟨z, hz, hzK⟩ := not_subset.1 h
  have hpos : 0 < volume (B ∩ Kᶜ) :=
    (hBo.inter hK.isOpen_compl).measure_pos volume ⟨z, hz, hzK⟩
  rw [ENNReal.top_mul hpos.ne', add_top]

/-- **DZZ Lemma 3.8 through a similarity, walled form** (l. 1229–1232 with lem-scaling-coupling,
l. 611–624): if `|F₁ − F₂ ∘ θ| ≤ c` on the closed box `K ⊆ 𝕍` (`θ K ⊆ 𝕍`) for the exponents of two
chaos limits, then for all `x, y` and `δ`
`D^{θK}_{|a|δe^{c/2}}(θx, θy)[M⁽²⁾] ≤ D^K_δ(x, y)[M⁽¹⁾] ≤ D^{θK}_{|a|δe^{−c/2}}(θx, θy)[M⁽²⁾]`. -/
theorem lgd_sim_sandwich (h₁ : IsChaosLimit γ ζ₁ V₁ s₁ μ₁) (h₂ : IsChaosLimit γ ζ₂ V₂ s₂ μ₂)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) {K : Set ℂ} (hK : IsClosed K) (hKV : K ⊆ dzzV)
    (hθK : simMap a b '' K ⊆ dzzV)
    (hc : ∀ n : ℕ, ∀ z ∈ K, |(γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z) -
      (γ * ζ₂ (s₂ n) (simMap a b z) - γ ^ 2 / 2 * V₂ (s₂ n) (simMap a b z))| ≤ c)
    (δ : ℝ) (x y : ℂ) :
    lgdDZZ (dzzWall (simMap a b '' K) (dzzWall dzzV μ₂)) (‖a‖ * δ * Real.exp (c / 2))
        (simMap a b x) (simMap a b y) ≤ lgdDZZ (dzzWall K (dzzWall dzzV μ₁)) δ x y ∧
      lgdDZZ (dzzWall K (dzzWall dzzV μ₁)) δ x y ≤
        lgdDZZ (dzzWall (simMap a b '' K) (dzzWall dzzV μ₂)) (‖a‖ * δ * Real.exp (-c / 2))
          (simMap a b x) (simMap a b y) := by
  set θ := simMap a b
  set θi := simMap a⁻¹ (-(a⁻¹ * b))
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  set μA := dzzWall K (dzzWall dzzV μ₁)
  set μB := dzzWall (θ '' K) (dzzWall dzzV μ₂)
  set ν := μB.map θi
  have hνθ : ν.map θ = μB := by
    rw [Measure.map_map (continuous_simMap _ _).measurable (continuous_simMap _ _).measurable]
    conv_rhs => rw [← Measure.map_id (μ := μB)]
    congr 1; funext z; exact simMap_right_inv ha b z
  have hν : ∀ S : Set ℂ, MeasurableSet S → ν S = μB (θ '' S) := fun S hS => by
    rw [Measure.map_apply (continuous_simMap _ _).measurable hS, simMap_image_eq_preimage ha b]
  have hball : ∀ (x : ℚ × ℚ) (r : ℝ),
      (μA (ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (‖a‖ ^ 2))⁻¹ *
        ν (ball (ratPt x) r)) ∧
      ν (ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) *
        μA (ball (ratPt x) r) := by
    intro x r
    have hJ0 : ENNReal.ofReal (‖a‖ ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have he0 : ENNReal.ofReal (Real.exp c) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos c
    have himB : θ '' ball (ratPt x) r = ball (θ (ratPt x)) (‖a‖ * r) := simMap_image_ball ha b _ _
    rw [hν _ measurableSet_ball]
    by_cases hBK : ball (ratPt x) r ⊆ K
    · have hθB : θ '' ball (ratPt x) r ⊆ θ '' K := image_mono hBK
      have hmB : MeasurableSet (θ '' ball (ratPt x) r) := by rw [himB]; exact measurableSet_ball
      simp only [μA, μB]
      rw [dzzWall_eq_of_subset _ hBK measurableSet_ball,
        dzzWall_eq_of_subset _ (hBK.trans hKV) measurableSet_ball,
        dzzWall_eq_of_subset _ hθB hmB, dzzWall_eq_of_subset _ (hθB.trans hθK) hmB]
      exact ⟨chaos_sim_ball_le h₁ h₂ ha b hθK
          (fun n z hz => by linarith [(abs_le.1 (hc n z hz)).2]) x r hBK,
        chaos_sim_ball_ge h₁ h₂ ha b hKV
          (fun n z hz => by linarith [(abs_le.1 (hc n z hz)).1]) x r hBK⟩
    · have hθB : ¬ θ '' ball (ratPt x) r ⊆ θ '' K := fun h =>
        hBK ((image_subset_image_iff (simMap_injective ha b)).1 h)
      simp only [μA, μB]
      rw [dzzWall_eq_top_of_not_subset hK _ isOpen_ball hBK,
        dzzWall_eq_top_of_not_subset (isClosed_simMap_image ha b hK) _
          (by rw [himB]; exact isOpen_ball) hθB]
      exact ⟨le_of_eq (ENNReal.mul_top (mul_ne_zero he0 (ENNReal.inv_ne_zero.2
          ENNReal.ofReal_ne_top))).symm,
        le_of_eq (ENNReal.mul_top (mul_ne_zero he0 hJ0)).symm⟩
  set L := Real.log ‖a‖
  have hL : Real.exp L = ‖a‖ := Real.exp_log hna
  have e3 : ENNReal.ofReal (Real.exp (c - 2 * L)) =
      ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (‖a‖ ^ 2))⁻¹ := by
    rw [show c - 2 * L = c + -L + -L by ring, Real.exp_add, Real.exp_add, Real.exp_neg, hL,
      mul_assoc, ← mul_inv, ← sq, ENNReal.ofReal_mul (Real.exp_pos c).le,
      ENNReal.ofReal_inv_of_pos (by positivity)]
  have e4 : ENNReal.ofReal (Real.exp (c + 2 * L)) =
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [show c + 2 * L = c + L + L by ring, Real.exp_add, Real.exp_add, hL, mul_assoc, ← sq,
      ENNReal.ofReal_mul (Real.exp_pos c).le]
  have hA := lgdDZZ_le_of_ball_le (c := c - 2 * L) (fun x r => by rw [e3]; exact (hball x r).1)
    δ x y
  have hB := lgdDZZ_le_of_ball_le (c := c + 2 * L) (fun x r => by rw [e4]; exact (hball x r).2)
    (‖a‖ * δ * Real.exp (c / 2)) x y
  have hθν : ∀ δ' : ℝ, lgdDZZ μB δ' (θ x) (θ y) = lgdDZZ ν δ' x y := fun δ' => by
    rw [← hνθ]; exact lgdDZZ_map_similarity ha b ν δ' x y
  have f1 : δ * Real.exp (-(c - 2 * L) / 2) = ‖a‖ * δ * Real.exp (-c / 2) := by
    rw [show -(c - 2 * L) / 2 = L + -c / 2 by ring, Real.exp_add, hL]; ring
  have f2 : ‖a‖ * δ * Real.exp (c / 2) * Real.exp (-(c + 2 * L) / 2) = δ := by
    rw [show -(c + 2 * L) / 2 = -L + -(c / 2) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg,
      hL, show ‖a‖ * δ * Real.exp (c / 2) * (‖a‖⁻¹ * (Real.exp (c / 2))⁻¹) =
        (‖a‖ * ‖a‖⁻¹) * δ * (Real.exp (c / 2) * (Real.exp (c / 2))⁻¹) by ring,
      mul_inv_cancel₀ hna.ne', mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul, mul_one]
  rw [f1] at hA
  rw [f2] at hB
  rw [hθν, hθν]
  exact ⟨hB, hA⟩

end DZZ
end LQGMetric
