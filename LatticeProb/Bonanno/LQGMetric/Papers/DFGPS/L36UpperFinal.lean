/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperFinal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperOne
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.6, upper half at `𝕣 = 1`, from DG Proposition 3.21

DFGPS Lemma 3.6 (arXiv:1905.00380, T:1628–1650), upper inequality of (eqn-lfpp-dist-show): w.p.
→ 1 as `δ → 0`, `D̃^δ_h(∂_L 𝕊, ∂_R 𝕊; 𝕊) ≤ δ^{−ξQ−ζ} e^{ξ h_1(0)}`.

Decision D52 (DECISIONS.md): DFGPS derive this from "[DG, Theorem 1.5]"; the path has to reach
within `δ` of `∂𝕊`, so we use the quantitative upper bound DG Proposition 3.21
(`Blueprint.DGProp3_21`, DG:1603–1610) on `N + 1 ≈ (1−a) log₂ δ⁻¹` dyadic boxes towards the
corners `0` and `1` (whole-plane GFF scale/translation invariance, DFGPS T:1638), straight walks
for the last `δ^{1−a}` (fractional moments), and the oscillation bound of LQGDimension
`Osc37.osc_tendsto` for the passage continuum path → graph path. Own arguments: DEVIATIONS
DV-DFC2-1 (boundary layer), DV-DFC2-2 (continuum → graph path).

Parameters: `ζ₁ = ζ/4`, `θ = min(1, Q/ξ)`, `a = θζ₁/2`, `u = θξQ − (θξ)²/2 > 0`,
`m = a min(p_L, p_R, 1)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint
open LQGDimension (IsGFFCircleAverage)
open LQGDimension.Blueprint.Draft (osc)

/-- **The per-`δ` bound**: `P[failure] ≤ P[osc failure] + K δ^m`. -/
theorem prob_bad_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {H : ℝ → ℂ → Ω → ℝ}
    (hH : IsGFFCircleAverage H P)
    {ξ s ζ₁ θ a u m lam pL CL ρL pR CR ρR δ : ℝ} (hξ : 0 < ξ) (hs : 0 ≤ s) (hζ₁ : 0 < ζ₁)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ha : 2 * a = θ * ζ₁) (ha0 : 0 < a)
    (hudef : u = θ * s - (θ * ξ) ^ 2 / 2) (hu : 0 < u) (hlam : lam = (1 - s) - ζ₁)
    (hma : m ≤ a) (hpL : 0 < pL) (hpR : 0 < pR) (hmpL : m ≤ a * pL) (hmpR : m ≤ a * pR)
    (hbL : ∀ r : ℝ, 0 < r → ∀ c : ℂ, ∀ δ : ℝ, 0 < δ → δ / r < ρL →
      P {ω | ¬ ∃ q : ℝ → ℂ, DG.IsDGPath ((fun x => (r : ℂ) * x + c) '' Metric.closedBall aL (3/4))
        ((r : ℂ) * bL + c) ((r : ℂ) * aL + c) q ∧
        LQGDimension.lfppLength ξ (fun x => H δ x ω) q ≤
          2 * r * Real.exp (ξ * H r c ω) * (δ / r) ^ lam} ≤ ENNReal.ofReal (CL * (δ / r) ^ pL))
    (hbR : ∀ r : ℝ, 0 < r → ∀ c : ℂ, ∀ δ : ℝ, 0 < δ → δ / r < ρR →
      P {ω | ¬ ∃ q : ℝ → ℂ, DG.IsDGPath ((fun x => (r : ℂ) * x + c) '' Metric.closedBall aR (3/4))
        ((r : ℂ) * bR + c) ((r : ℂ) * aR + c) q ∧
        LQGDimension.lfppLength ξ (fun x => H δ x ω) q ≤
          2 * r * Real.exp (ξ * H r c ω) * (δ / r) ^ lam} ≤ ENNReal.ofReal (CR * (δ / r) ^ pR))
    (hnull : P (nullBad h H δ) = 0)
    (hδ : 0 < δ) (hδ64 : δ ≤ 1/64) (hc2 : δ ^ (1 - a) ≤ 1/4) (hc3 : δ ^ a ≤ 1/64)
    (hc4L : δ ^ a < ρL) (hc4R : δ ^ a < ρR) (hc5 : 18 ≤ δ ^ (-ζ₁)) :
    P {ω | ¬ graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1)
        (rS 1) ≤ δ ^ (-s - 4 * ζ₁) * Real.exp (ξ * circleAvg (h ω) 1 0)} ≤
      P (oscBad H (ζ₁ / ξ) δ) + ENNReal.ofReal ((max CL 0 * (2 ^ pL / (2 ^ pL - 1)) +
        max CR 0 * (2 ^ pR / (2 ^ pR - 1)) +
        2 * (Real.exp (Real.log 4 * (θ * ξ) ^ 2) / (2 ^ u - 1)) +
        12 * Real.exp (Real.log 4 * (θ * ξ) ^ 2)) * δ ^ m) := by
  subst hlam
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨N, hN1, hN2⟩ := exists_scale hδ hc2
  have h64 := sixtyfour_le hδ N hN1 hc3
  have hrL := ratio_lt hδ N hN1 hc4L
  have hrR := ratio_lt hδ N hN1 hc4R
  have hsub : {ω | ¬ graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1)
      (rightVerts δ 1) (rS 1) ≤ δ ^ (-s - 4 * ζ₁) * Real.exp (ξ * circleAvg (h ω) 1 0)} ⊆
      oscBad H (ζ₁ / ξ) δ ∪ (⋃ k ∈ Finset.range (N + 1), boxBad H ξ ((1 - s) - ζ₁) δ 0 aL bL k) ∪
        (⋃ k ∈ Finset.range (N + 1), boxBad H ξ ((1 - s) - ζ₁) δ 1 aR bR k) ∪
        momBad H ξ s ζ₁ δ 0 N ∪ momBad H ξ s ζ₁ δ 1 N ∪
        walkBad H ξ s ζ₁ δ (1, 1) (rnd δ (xL (N + 1))) ∪
        walkBad H ξ s ζ₁ δ (rnd δ (xR (N + 1))) (mR δ, 1) ∪ nullBad h H δ := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or, mem_iUnion, not_exists, Finset.mem_range] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hO, hL⟩, hR⟩, hmL⟩, hmR⟩, hwL⟩, hwR⟩, hn⟩ := hc
    exact hω (graphLFPP_le_of_good (fun δ hδ ω => hH.continuous δ hδ ω) hδ hδ64 hξ hs hζ₁.le
      N h64 hc5 ω hO (fun k hk hk' => hL k hk hk') (fun k hk hk' => hR k hk hk') hmL hmR hwL hwR hn)
  set E4 := Real.exp (Real.log 4 * (θ * ξ) ^ 2) with hE4
  have hE40 : 0 < E4 := Real.exp_pos _
  have h2u : 1 < (2:ℝ) ^ u := Real.one_lt_rpow (by norm_num) hu
  have hPL : P (⋃ k ∈ Finset.range (N + 1), boxBad H ξ ((1 - s) - ζ₁) δ 0 aL bL k) ≤
      ENNReal.ofReal (max CL 0 * (2 ^ pL / (2 ^ pL - 1)) * δ ^ m) :=
    (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun k hk =>
      hbL (rk k) (rk_pos k) 0 δ hδ (hrL k (Finset.mem_range.1 hk))).trans
      (box_sum_le hδ hδ1 hpL hmpL N hN1))
  have hPR : P (⋃ k ∈ Finset.range (N + 1), boxBad H ξ ((1 - s) - ζ₁) δ 1 aR bR k) ≤
      ENNReal.ofReal (max CR 0 * (2 ^ pR / (2 ^ pR - 1)) * δ ^ m) :=
    (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun k hk =>
      hbR (rk k) (rk_pos k) 1 δ hδ (hrR k (Finset.mem_range.1 hk))).trans
      (box_sum_le hδ hδ1 hpR hmpR N hN1))
  have hmom : ∀ c : ℂ, ‖c‖ ≤ 3 → P (momBad H ξ s ζ₁ δ c N) ≤
      ENNReal.ofReal (E4 / (2 ^ u - 1) * δ ^ m) := fun c hc =>
    (prob_scale_sum_le hH (N + 1) hc hs hθ0 hθ1 (hudef ▸ hu) (Real.rpow_pos_of_pos hδ _)).trans
      (ENNReal.ofReal_le_ofReal (by
        rw [← hudef]; exact moment_real_le hδ hδ1 ha hma ha0 hE40.le h2u))
  have hwalk : ∀ k k' : ℤ × ℤ, gpt δ k ∈ rS 1 → gpt δ k' ∈ rS 1 →
      ((wlen k k' + 1 : ℕ) : ℝ) ≤ rk (N + 1) / δ + 4 →
      P (walkBad H ξ s ζ₁ δ k k') ≤ ENNReal.ofReal (6 * E4 * δ ^ m) := fun k k' hk hk' hlen =>
    (prob_walk_le hH hδ hδ1 hk hk' ξ hθ0 hθ1 (Real.rpow_pos_of_pos hδ _)).trans
      (ENNReal.ofReal_le_ofReal (walk_real_le hδ hδ1 ha hudef hu hma ha0 hE40.le hN2
        (Nat.cast_nonneg _) hlen))
  have hρ2 := rk_le_half (N + 1)
  have hWL : P (walkBad H ξ s ζ₁ δ (1, 1) (rnd δ (xL (N + 1)))) ≤
      ENNReal.ofReal (6 * E4 * δ ^ m) :=
    hwalk _ _ (gpt_one_one_mem_leftVerts hδ (by linarith)).1.1
      (gpt_rnd_mem_rS hδ (by simp [xL, aL]; linarith) (by simp [xL, aL]; linarith)
        (by simp [xL, aL]; linarith) (by simp [xL, aL]; linarith))
      (by have := wlen_walkL_le hδ N; linarith)
  have hWR : P (walkBad H ξ s ζ₁ δ (rnd δ (xR (N + 1))) (mR δ, 1)) ≤
      ENNReal.ofReal (6 * E4 * δ ^ m) :=
    hwalk _ _ (gpt_rnd_mem_rS hδ (by simp [xR, aR]; linarith) (by simp [xR, aR]; linarith)
        (by simp [xR, aR]; linarith) (by simp [xR, aR]; linarith))
      (gpt_mR_mem_rightVerts hδ (by linarith)).1.1 (wlen_walkR_le hδ N)
  have hML := hmom 0 (by simp)
  have hMR := hmom 1 (by simp)
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [hnull, add_zero]
  have u7 : ∀ A B C D E F G : Set Ω,
      P (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ≤ P A + P B + P C + P D + P E + P F + P G := by
    intro A B C D E F G
    refine (measure_union_le (μ := P) _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le (μ := P) _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le (μ := P) _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le (μ := P) _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le (μ := P) _ _).trans (add_le_add ?_ le_rfl)
    exact measure_union_le (μ := P) _ _
  refine (u7 _ _ _ _ _ _ _).trans ?_
  have hdm : 0 ≤ δ ^ m := Real.rpow_nonneg hδ.le _
  have hK1 : 0 ≤ max CL 0 * (2 ^ pL / (2 ^ pL - 1)) * δ ^ m := by
    have : 1 < (2:ℝ) ^ pL := Real.one_lt_rpow (by norm_num) hpL
    have := le_max_right CL 0
    have : 0 ≤ (2:ℝ) ^ pL / (2 ^ pL - 1) := div_nonneg (by positivity) (by linarith)
    positivity
  have hK2 : 0 ≤ max CR 0 * (2 ^ pR / (2 ^ pR - 1)) * δ ^ m := by
    have : 1 < (2:ℝ) ^ pR := Real.one_lt_rpow (by norm_num) hpR
    have := le_max_right CR 0
    have : 0 ≤ (2:ℝ) ^ pR / (2 ^ pR - 1) := div_nonneg (by positivity) (by linarith)
    positivity
  have hK3 : 0 ≤ E4 / (2 ^ u - 1) * δ ^ m :=
    mul_nonneg (div_nonneg hE40.le (by linarith)) hdm
  have hK4 : 0 ≤ 6 * E4 * δ ^ m := by positivity
  have hfin : ENNReal.ofReal (max CL 0 * (2 ^ pL / (2 ^ pL - 1)) * δ ^ m) +
      ENNReal.ofReal (max CR 0 * (2 ^ pR / (2 ^ pR - 1)) * δ ^ m) +
      ENNReal.ofReal (E4 / (2 ^ u - 1) * δ ^ m) + ENNReal.ofReal (E4 / (2 ^ u - 1) * δ ^ m) +
      ENNReal.ofReal (6 * E4 * δ ^ m) + ENNReal.ofReal (6 * E4 * δ ^ m) =
      ENNReal.ofReal ((max CL 0 * (2 ^ pL / (2 ^ pL - 1)) +
        max CR 0 * (2 ^ pR / (2 ^ pR - 1)) + 2 * (E4 / (2 ^ u - 1)) + 12 * E4) * δ ^ m) := by
    rw [← ENNReal.ofReal_add hK1 hK2, ← ENNReal.ofReal_add (by positivity) hK3,
      ← ENNReal.ofReal_add (by positivity) hK3, ← ENNReal.ofReal_add (by positivity) hK4,
      ← ENNReal.ofReal_add (by positivity) hK4]
    congr 1; ring
  rw [← hfin]
  have := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hPL hPR) hML) hMR) hWL) hWR
  calc _ = P (oscBad H (ζ₁ / ξ) δ) +
        (P (⋃ k ∈ Finset.range (N + 1), boxBad H ξ ((1 - s) - ζ₁) δ 0 aL bL k) +
        P (⋃ k ∈ Finset.range (N + 1), boxBad H ξ ((1 - s) - ζ₁) δ 1 aR bR k) +
        P (momBad H ξ s ζ₁ δ 0 N) + P (momBad H ξ s ζ₁ δ 1 N) +
        P (walkBad H ξ s ζ₁ δ (1, 1) (rnd δ (xL (N + 1)))) +
        P (walkBad H ξ s ζ₁ δ (rnd δ (xR (N + 1))) (mR δ, 1))) := by simp only [add_assoc]
    _ ≤ _ := add_le_add le_rfl this

/-- **DFGPS Lemma 3.6, upper half at `𝕣 = 1`**, from DG Proposition 3.21 (D52). -/
theorem lem3_6_upperOne (hP : DGProp3_21) : Lem3_6UpperOne := by
  intro γ hγ0 hγ2 Ω _ P _ h hh ζ hζ η hη
  obtain ⟨H, hH, -, hHae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh
  have hξ : 0 < xiGamma γ := DG.xiGamma_pos hγ0
  have hQ : 0 < Q γ := by unfold Q; positivity
  have hs : 0 ≤ xiGamma γ * Q γ := by positivity
  have hζ₁ : ζ / 4 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = min 1 (Q γ / xiGamma γ) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := hθdef ▸ lt_min one_pos (div_pos hQ hξ)
  have hθ1 : θ ≤ 1 := hθdef ▸ min_le_left _ _
  have hθξ : θ * xiGamma γ ≤ Q γ := by
    have := min_le_right 1 (Q γ / xiGamma γ); rw [← hθdef, le_div_iff₀ hξ] at this; exact this
  obtain ⟨a, hadef⟩ : ∃ a, a = θ * (ζ / 4) / 2 := ⟨_, rfl⟩
  have ha : 2 * a = θ * (ζ / 4) := by rw [hadef]; ring
  have ha0 : 0 < a := by rw [hadef]; have := hζ₁.1; positivity
  have ha1 : a < 1 := by
    have : θ * (ζ / 4) ≤ 1 * 1 := mul_le_mul hθ1 hζ₁.2.le hζ₁.1.le zero_le_one
    linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = θ * (xiGamma γ * Q γ) - (θ * xiGamma γ) ^ 2 / 2 := ⟨_, rfl⟩
  have hu : 0 < u := by
    have h1 : 0 < θ * xiGamma γ := by positivity
    have : (θ * xiGamma γ) ^ 2 ≤ θ * xiGamma γ * Q γ := by nlinarith
    have : 0 < θ * xiGamma γ * Q γ := by positivity
    rw [hudef]; nlinarith
  obtain ⟨pL, CL, ρL, hpL, hρL, hbL⟩ := box_bound hP hγ0 hγ2 aL bL (R := 3/4)
    (by rw [norm_sub_rev]; exact norm_aL_sub_bL) hζ₁
  obtain ⟨pR, CR, ρR, hpR, hρR, hbR⟩ := box_bound hP hγ0 hγ2 aR bR (R := 3/4)
    (by rw [norm_sub_rev]; exact norm_aR_sub_bR) hζ₁
  obtain ⟨m, hmdef⟩ : ∃ m, m = a * min (min pL pR) 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := hmdef ▸ mul_pos ha0 (lt_min (lt_min hpL hpR) one_pos)
  have hma : m ≤ a := by
    have : min (min pL pR) 1 ≤ 1 := min_le_right _ _
    rw [hmdef]; nlinarith
  have hmpL : m ≤ a * pL := hmdef ▸ mul_le_mul_of_nonneg_left
    ((min_le_left _ _).trans (min_le_left _ _)) ha0.le
  have hmpR : m ≤ a * pR := hmdef ▸ mul_le_mul_of_nonneg_left
    ((min_le_left _ _).trans (min_le_right _ _)) ha0.le
  have hlam : DG.dgLambda γ - ζ / 4 = (1 - xiGamma γ * Q γ) - ζ / 4 := by
    rw [dgLambda_eq hγ0]
  obtain ⟨K, -⟩ : ∃ K, K = (max CL 0 * (2 ^ pL / (2 ^ pL - 1)) +
      max CR 0 * (2 ^ pR / (2 ^ pR - 1)) +
      2 * (Real.exp (Real.log 4 * (θ * xiGamma γ) ^ 2) / (2 ^ u - 1)) +
      12 * Real.exp (Real.log 4 * (θ * xiGamma γ) ^ 2)) := ⟨_, rfl⟩
  have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have hT1 := LQGDimension.Osc37.osc_tendsto hH (div_pos hζ₁.1 hξ)
  have hT2 : Tendsto (fun δ : ℝ => (max CL 0 * (2 ^ pL / (2 ^ pL - 1)) +
      max CR 0 * (2 ^ pR / (2 ^ pR - 1)) +
      2 * (Real.exp (Real.log 4 * (θ * xiGamma γ) ^ 2) / (2 ^ u - 1)) +
      12 * Real.exp (Real.log 4 * (θ * xiGamma γ) ^ 2)) * δ ^ m) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_rpow_nhdsGT hm0).const_mul (max CL 0 * (2 ^ pL / (2 ^ pL - 1)) +
      max CR 0 * (2 ^ pR / (2 ^ pR - 1)) +
      2 * (Real.exp (Real.log 4 * (θ * xiGamma γ) ^ 2) / (2 ^ u - 1)) +
      12 * Real.exp (Real.log 4 * (θ * xiGamma γ) ^ 2))
  have hT3 := tendsto_rpow_nhdsGT (show 0 < 1 - a by linarith)
  have hT4 := tendsto_rpow_nhdsGT ha0
  have hT5 := tendsto_rpow_nhdsGT hζ₁.1
  have hev := (((hT1.eventually (gt_mem_nhds hη2)).and (hT2.eventually (gt_mem_nhds
    (show (0:ℝ) < η / 2 by positivity)))).and ((hT3.eventually (gt_mem_nhds
    (show (0:ℝ) < 1/4 by norm_num))).and (hT4.eventually (gt_mem_nhds
    (show (0:ℝ) < min (1/64) (min ρL ρR) by positivity))))).and
    ((hT5.eventually (gt_mem_nhds (show (0:ℝ) < 1/18 by norm_num))).and
      (Ioo_mem_nhdsGT (show (0:ℝ) < 1/64 by norm_num)))
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨δ₀, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨⟨⟨hA, hB⟩, hC, hD⟩, hE, hF⟩ := hsub hδ
  have hδ0 : 0 < δ := hδ.1
  have h18 : 18 ≤ δ ^ (-(ζ / 4)) := by
    rw [Real.rpow_neg hδ0.le, le_inv_comm₀ (by norm_num) (Real.rpow_pos_of_pos hδ0 _)]
    linarith
  have hnull : P (nullBad h H δ) = 0 := by
    have hall : ∀ᵐ ω ∂P, ∀ ab : ℤ × ℤ,
        H δ ⟨ab.1 * δ, ab.2 * δ⟩ ω = circleAvg (h ω) δ ⟨ab.1 * δ, ab.2 * δ⟩ :=
      ae_all_iff.2 fun ab => hHae δ hδ0 _
    have := hh.2.and hall
    rw [ae_iff] at this
    exact this
  have hb := prob_bad_le (P := P) hh hH (θ := θ) (a := a) (u := u) (m := m)
    (lam := DG.dgLambda γ - ζ / 4) hξ hs hζ₁.1 hθ0 hθ1 ha ha0 hudef hu hlam hma hpL hpR hmpL hmpR
    (fun r hr c δ hδ hρ => hbL P h hh H hH hHae r hr c δ hδ hρ)
    (fun r hr c δ hδ hρ => hbR P h hh H hH hHae r hr c δ hδ hρ) hnull hδ0 hF.2.le hC.le
    (hD.le.trans (min_le_left _ _)) (hD.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    (hD.trans_le ((min_le_right _ _).trans (min_le_right _ _))) h18
  rw [show -xiGamma γ * Q γ - ζ = -(xiGamma γ * Q γ) - 4 * (ζ / 4) by ring]
  refine hb.trans ?_
  calc _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add hA.le (ENNReal.ofReal_le_ofReal hB.le)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- **DFGPS Lemma 3.6** from DG Thm 1.5 (1.5b, second half) and DG Prop 3.21 (D52). -/
theorem lem3_6_of_DG (hKU : DGThm1_5KU) (hP : DGProp3_21) : DFGPS.Lem3_6 :=
  lem3_6_of_upperOne hKU (lem3_6_upperOne hP)

end LQGMetric.DFGPS.L36
