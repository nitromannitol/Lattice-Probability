/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas

/-!
# DZZ Lemma 6.1, lower half: the union-bound reduction to segments (P2-DZZ61L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 6.1, l. 2598–2603:
"By Proposition 3.17, it suffices to show that for any fixed `ι > 0` and any segment
`L_δ ⊆ ∂𝕍̄_{u,α}` with length in `[δ^{2ι}/2, δ^{2ι}]` we have
`E log min_{x ∈ L_δ, y ∈ ∂𝕍̄_u} D_{γ,δ,η}(x,y) ≥ (χ − 2ι) log δ⁻¹`."
The reduction is the one written out at the end of the proof of Lemma 5.4 (l. 2573–2578):
`∂𝕍̄_{u,α}` is the union of `4n ≤ δ^{−2ι}` segments; by Proposition 3.17 at deviation `ι'` (DZZ's
`Cι^{1/2}`) each segment distance is within `ι' log δ⁻¹` of its mean outside an event of
probability `δ^{cι'²}`, and `δ^{−2ι} δ^{cι'²} → 0`.

* `DZZL61SegBound P μ α χ u ι`: the segment bound (DZZ l. 2601–2603). DZZ's "any segment
  `L_δ`" is read for families `δ ↦ L_δ` with the bound for all small `δ` (as for the
  `ξ`-admissible pairs of Proposition 3.17).
* `dzzLem61Lower_of_segBound`: `DZZLem61Lower P μ α χ` from DZZ Proposition 3.17 and the segment
  bound (for all small `ι`).

Formal side hypotheses: `P` is a probability measure, and the ball masses `μ ω (B(c,r))` are
a.e.-measurable (so that `log min D_δ` is a.e.-measurable, `LGDMeas.lean`; DZZ take expectations
without comment). Proved for the LQG measure in `LGDMeasQ.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The segment bound of DZZ Lemma 6.1** (l. 2601–2603) at `ι`, with segment length `δ^κ`
(DEC-117 §2(c): DZZ's `δ^{2ι}` needs `χ ≥ 1/2`; the consumer uses `κ = 2ι/χ`): for every family
of segments `L_δ ⊆ ∂𝕍̄_{u,α}` of length in `[δ^κ/2, δ^κ]` (for small `δ`),
`E log min_{x ∈ L_δ, y ∈ ∂𝕍̄_u} D_δ(x,y) ≥ (χ − 2ι) log δ⁻¹` for small `δ`. -/
def DZZL61SegBound (P : Measure Ω) (μ : Ω → Measure ℂ) (α χ : ℝ) (u : ℂ) (ι κ : ℝ) : Prop :=
  ∀ L : ℝ → Set ℂ, (∀ᶠ δ in 𝓝[>] (0 : ℝ), IsBdrySeg u (α / 20) (δ ^ κ) (L δ)) →
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (χ - 2 * ι) * Real.log δ⁻¹ ≤
      ∫ ω, logMinLGD (μ ω) δ (L δ) (frontier (sqBox u (1 / 20))) ∂P

lemma eventually_rpow_le {e b : ℝ} (he : 0 < e) (hb : 0 < b) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ e ≤ b := by
  have h : Tendsto (fun δ : ℝ => δ ^ e) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow he.ne'] using (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto
  exact (tendsto_nhdsWithin_of_tendsto_nhds h).eventually (Iic_mem_nhds hb)

/-- The minimum over a finite union of sets is attained on one of them. -/
lemma exists_logMinLGD_eq_of_cover {I : Type*} [Finite I] [Nonempty I] (μ : Measure ℂ) (δ : ℝ)
    {F G : Set ℂ} {S : I → Set ℂ} (hS : ∀ i, S i ⊆ F) (hF : ∀ x ∈ F, ∃ i, x ∈ S i) :
    ∃ j, logMinLGD μ δ F G = logMinLGD μ δ (S j) G := by
  obtain ⟨j, hj⟩ := Finite.exists_min fun i => lgdMinSet μ δ (S i) G
  refine ⟨j, ?_⟩
  have h1 : lgdMinSet μ δ F G ≤ lgdMinSet μ δ (S j) G :=
    biInf_mono fun x hx => hS j hx
  have h2 : lgdMinSet μ δ (S j) G ≤ lgdMinSet μ δ F G := by
    refine le_iInf₂ fun x hx => ?_
    obtain ⟨i, hi⟩ := hF x hx
    exact (hj i).trans (iInf₂_le x hi)
  rw [logMinLGD, logMinLGD, le_antisymm h1 h2]

/-- Expectation lower bound from a good event: if `Y` is pointwise one of the `X i ≥ 0`
(integrable), and all `X i ≥ K` off `bad`, then `E Y ≥ K (1 − P(bad))`. -/
lemma integral_ge_of_good {P : Measure Ω} [IsProbabilityMeasure P] {I : Type*} [Fintype I]
    {Y : Ω → ℝ} {X : I → Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hYX : ∀ ω, ∃ j, Y ω = X j ω)
    (hX0 : ∀ i ω, 0 ≤ X i ω) (hXi : ∀ i, Integrable (X i) P) (hYm : AEStronglyMeasurable Y P)
    {bad : Set Ω} (hgood : ∀ ω ∉ bad, ∀ i, K ≤ X i ω) :
    K * (1 - P.real bad) ≤ ∫ ω, Y ω ∂P := by
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => by obtain ⟨j, hj⟩ := hYX ω; rw [hj]; exact hX0 j ω
  have hYint : Integrable Y P := by
    refine Integrable.mono' (integrable_finset_sum Finset.univ fun i _ => hXi i) hYm
      (ae_of_all _ fun ω => ?_)
    obtain ⟨j, hj⟩ := hYX ω
    rw [Real.norm_of_nonneg (hY0 ω), hj]
    exact Finset.single_le_sum (fun i _ => hX0 i ω) (Finset.mem_univ j)
  set T := toMeasurable P bad
  have hT : MeasurableSet T := measurableSet_toMeasurable P bad
  have hle : Tᶜ.indicator (fun _ => K) ≤ Y := fun ω => by
    by_cases hω : ω ∈ Tᶜ
    · rw [indicator_of_mem hω]
      obtain ⟨j, hj⟩ := hYX ω
      rw [hj]
      exact hgood ω (fun h => hω (subset_toMeasurable P bad h)) j
    · rw [indicator_of_notMem hω]; exact hY0 ω
  have := integral_mono ((integrable_const K).indicator hT.compl) hYint hle
  rw [integral_indicator_const K hT.compl, probReal_compl_eq_one_sub hT, smul_eq_mul] at this
  have hTb : P.real T = P.real bad := by
    rw [measureReal_def, measureReal_def, measure_toMeasurable]
  rw [hTb] at this; linarith

/-- **DZZ Lemma 6.1, lower half, from the segment bound** (DZZ l. 2598–2603 with the union bound
of l. 2573–2578): DZZ Proposition 3.17 (`0 < ξ < ξ₀`) and the segment bound `DZZL61SegBound` for
all small `ι`, at the segment length `δ^{2ι/χ}` (DEC-117 §2(c)), give
`liminf E log min_{∂𝕍̄_{u,α} × ∂𝕍̄_u} D_δ / log δ⁻¹ ≥ χ`. The union is over `≈ δ^{−2ι/χ}`
segments, so the deviation `ι'` must satisfy `c ι'² > 2ι/χ` (DZZ's `Cι^{1/2}`). -/
theorem dzzLem61Lower_of_segBound {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure ℂ}
    {α χ ξ₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hξ₀ : 0 < ξ₀)
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P)
    (h317 : ∀ ξ, 0 < ξ → ξ < ξ₀ → DZZProp317 P μ ξ)
    (hseg : ∀ u ∈ dzzVbar, ∃ ι₀ > 0, ∀ ι ∈ Ioo (0 : ℝ) ι₀,
      DZZL61SegBound P μ α χ u ι (2 * ι / χ)) :
    DZZLem61Lower P μ α χ := by
  classical
  intro u hu ε hε
  by_cases hχ : χ ≤ ε / 2
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ.1).mpr hδ.2)
    have : 0 ≤ (∫ ω, logMinLGD (μ ω) δ (frontier (sqBox u (α / 20)))
        (frontier (sqBox u (1 / 20))) ∂P) / Real.log δ⁻¹ :=
      div_nonneg (integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _) hL.le
    linarith
  push_neg at hχ
  have hχ0 : 0 < χ := by linarith
  -- the parameters `ξ`, `ι'` (DZZ's `Cι^{1/2}`), `ι` and the segment exponent `κ = 2ι/χ`
  set ξ := min (ξ₀ / 2) ((1 - α) / 40) with hξdef
  have hξ : 0 < ξ := lt_min (by linarith) (by linarith)
  have hξ₀' : ξ < ξ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hξα : ξ ≤ (1 - α) / 40 := min_le_right _ _
  have hξ9 : ξ ≤ 9 / 20 := by linarith
  obtain ⟨c, hc, hconc⟩ := h317 ξ hξ hξ₀'
  set ι' : ℝ := min (ε / 8) (1 / 2) with hι'def
  have hι'0 : 0 < ι' := lt_min (by linarith) (by norm_num)
  have hι'1 : ι' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hι'ε : ι' ≤ ε / 8 := min_le_left _ _
  obtain ⟨ι₀, hι₀, hsegu⟩ := hseg u hu
  have hcι : 0 < c * ι' ^ 2 / 4 := by positivity
  set ι : ℝ := min (min (ι₀ / 2) (ε / 16)) (min (ξ * χ / 4) (c * ι' ^ 2 * χ / 4)) with hιdef
  have hι0 : 0 < ι := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by positivity) (by positivity))
  have hιι₀ : ι < ι₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hιε : ι ≤ ε / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have hιξ : ι ≤ ξ * χ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hιc : ι ≤ c * ι' ^ 2 * χ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set κ : ℝ := 2 * ι / χ with hκdef
  have hκ0 : 0 < κ := by positivity
  have hκξ : κ ≤ ξ / 2 := by
    rw [hκdef, div_le_iff₀ hχ0]; nlinarith
  have hκc : κ ≤ c * ι' ^ 2 / 2 := by
    rw [hκdef, div_le_iff₀ hχ0]; nlinarith
  set a : ℝ := α / 20 with hadef
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 20 := by rw [hadef]; linarith
  set G := frontier (sqBox u (1 / 20)) with hGdef
  set F := frontier (sqBox u a) with hFdef
  -- the segments
  set ℓ : ℝ → ℝ := fun δ => δ ^ κ with hℓdef
  set n : ℝ → ℕ := fun δ => ⌈a / ℓ δ⌉₊ with hndef
  set good : ℝ → Prop := fun δ => δ ∈ Ioo (0 : ℝ) 1 ∧ ℓ δ ≤ a ∧ δ ^ ξ ≤ ℓ δ / 2 with hgooddef
  have hgood : ∀ᶠ δ in 𝓝[>] (0 : ℝ), good δ := by
    filter_upwards [Ioo_mem_nhdsGT one_pos, eventually_rpow_le hκ0 ha0,
      eventually_rpow_le (by linarith : 0 < ξ - κ) (by norm_num : (0 : ℝ) < 1 / 2)]
      with δ hδ h1 h2
    refine ⟨hδ, h1, ?_⟩
    have : δ ^ ξ = δ ^ (ξ - κ) * δ ^ κ := by
      rw [← Real.rpow_add hδ.1]; ring_nf
    rw [this]
    have := Real.rpow_pos_of_pos hδ.1 κ
    show δ ^ (ξ - κ) * δ ^ κ ≤ δ ^ κ / 2
    nlinarith
  have hℓpos : ∀ δ, good δ → 0 < ℓ δ := fun δ h => Real.rpow_pos_of_pos h.1.1 _
  have hn0 : ∀ δ, good δ → 0 < n δ := fun δ h =>
    Nat.ceil_pos.mpr (div_pos ha0 (hℓpos δ h))
  have hnge : ∀ δ, good δ → a / ℓ δ ≤ n δ := fun δ _ => Nat.le_ceil _
  have hnle : ∀ δ, good δ → (n δ : ℝ) ≤ 2 * a / ℓ δ := fun δ h => by
    have h1 := Nat.ceil_lt_add_one (div_nonneg ha0.le (hℓpos δ h).le)
    have h2 : 1 ≤ a / ℓ δ := (one_le_div (hℓpos δ h)).mpr h.2.1
    have : 2 * a / ℓ δ = 2 * (a / ℓ δ) := by ring
    show (⌈a / ℓ δ⌉₊ : ℝ) ≤ _
    linarith
  have hn1 : ∀ δ, good δ → a / n δ ≤ ℓ δ := fun δ h => by
    have hnp : (0 : ℝ) < n δ := by exact_mod_cast hn0 δ h
    rw [div_le_iff₀ hnp]
    have := hnge δ h
    rw [div_le_iff₀ (hℓpos δ h)] at this
    linarith
  have hn2 : ∀ δ, good δ → ℓ δ / 2 ≤ a / n δ := fun δ h => by
    have hnp : (0 : ℝ) < n δ := by exact_mod_cast hn0 δ h
    rw [le_div_iff₀ hnp]
    have := hnle δ h
    rw [le_div_iff₀ (hℓpos δ h)] at this
    linarith
  set S : (δ : ℝ) → Fin 4 × Fin (n δ) → Set ℂ := fun δ i => bdrySeg u a (n δ) i.1 i.2 with hSdef
  have hSseg : ∀ δ (h : good δ) i, IsBdrySeg u a (ℓ δ) (S δ i) := fun δ h i =>
    isBdrySeg_bdrySeg u ha0 (hn0 δ h) (hn2 δ h) (hn1 δ h) i.1 i.2.isLt
  have hcover : ∀ δ, good δ → ∀ x ∈ F, ∃ i, x ∈ S δ i := fun δ h x hx => by
    have := frontier_sqBox_subset_iUnion_bdrySeg u ha0 (hn0 δ h) hx
    simp only [mem_iUnion] at this
    obtain ⟨j, k, hk⟩ := this
    exact ⟨(j, k), hk⟩
  have hne : ∀ δ, good δ → Nonempty (Fin 4 × Fin (n δ)) := fun δ h => ⟨(0, ⟨0, hn0 δ h⟩)⟩
  -- the worst segment for the concentration events, the best one for the means
  set conc : (δ : ℝ) → Fin 4 × Fin (n δ) → Set Ω := fun δ i => conc1Event μ P δ ι' (S δ i) G
  have hexW : ∀ δ, good δ → ∃ i : Fin 4 × Fin (n δ), ∀ i', P (conc δ i')ᶜ ≤ P (conc δ i)ᶜ :=
    fun δ h => by haveI := hne δ h; exact Finite.exists_max _
  have hexB : ∀ δ, good δ → ∃ i : Fin 4 × Fin (n δ), ∀ i',
      ∫ ω, logMinLGD (μ ω) δ (S δ i) G ∂P ≤ ∫ ω, logMinLGD (μ ω) δ (S δ i') G ∂P :=
    fun δ h => by haveI := hne δ h; exact Finite.exists_min _
  choose worst hworst using hexW
  choose best hbest using hexB
  -- the `ξ`-admissible family of the worst segments
  set a₀ : ℂ := u + ((α / 40 : ℝ) : ℂ)
  set b₀ : ℂ := u + ((1 / 40 : ℝ) : ℂ)
  have ha₀ : a₀ ∈ sqBox u (α / 20) := by
    constructor
    · show |(u + ((α / 40 : ℝ) : ℂ)).re - u.re| ≤ α / 20 / 2
      rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith
    · show |(u + ((α / 40 : ℝ) : ℂ)).im - u.im| ≤ α / 20 / 2
      rw [Complex.add_im, Complex.ofReal_im, add_zero, sub_self, abs_zero]; positivity
  have hb₀ : b₀ ∈ sqBox u (1 / 20) := by
    constructor
    · show |(u + ((1 / 40 : ℝ) : ℂ)).re - u.re| ≤ 1 / 20 / 2
      rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith
    · show |(u + ((1 / 40 : ℝ) : ℂ)).im - u.im| ≤ 1 / 20 / 2
      rw [Complex.add_im, Complex.ofReal_im, add_zero, sub_self, abs_zero]; positivity
  have hb₀e : |b₀.re - u.re| = 1 / 40 ∨ |b₀.im - u.im| = 1 / 40 := by
    left; show |(u + ((1 / 40 : ℝ) : ℂ)).re - u.re| = 1 / 40
    rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
  let A : ℝ → Set ℂ := fun δ => if h : good δ then S δ (worst δ h) else {a₀}
  let B : ℝ → Set ℂ := fun δ => if good δ then G else {b₀}
  have hAsub : ∀ δ, A δ ⊆ sqBox u (α / 20) := fun δ => by
    simp only [A]; split_ifs with h
    · exact (hSseg δ h _).subset_sqBox
    · exact singleton_subset_iff.mpr ha₀
  have hBsub : ∀ δ, B δ ⊆ sqBox u (1 / 20) := fun δ => by
    simp only [B]; split_ifs
    · exact (isClosed_sqBox _ _).frontier_subset
    · exact singleton_subset_iff.mpr hb₀
  have hBe : ∀ δ, ∀ b ∈ B δ, |b.re - u.re| = 1 / 40 ∨ |b.im - u.im| = 1 / 40 := fun δ b hb => by
    simp only [B] at hb; split_ifs at hb
    · have := edge_of_mem_frontier_sqBox (by norm_num : (0 : ℝ) < 1 / 20) hb
      norm_num at this ⊢; exact this
    · rw [mem_singleton_iff.mp hb]; exact hb₀e
  have hAB : IsXiAdmissible ξ A B :=
    { subset_left := fun δ _ z hz =>
        mem_dzzVXi_of_mem_sqBox hu (hAsub δ hz) (by linarith) hξ.le hξ9
      subset_right := fun δ _ z hz => mem_dzzVXi_of_mem_sqBox hu (hBsub δ hz) le_rfl hξ.le hξ9
      adm_left := fun δ _ => by
        simp only [A]; split_ifs with h
        · exact Or.inr ⟨(hSseg δ h _).isConnected (hℓpos δ h).le,
            h.2.2.trans ((hSseg δ h _).diam_ge ha0.le (hℓpos δ h).le)⟩
        · exact Or.inl ⟨a₀, rfl⟩
      adm_right := fun δ _ => by
        simp only [B]; split_ifs with h
        · refine Or.inr ⟨isConnected_frontier_sqBox u (by positivity),
            le_trans ?_ (side_le_diam_frontier_sqBox u (by positivity))⟩
          have := h.2.2; have := h.2.1; linarith
        · exact Or.inl ⟨b₀, rfl⟩
      dist_ge := fun δ _ a ha b hb => hξα.trans (dist_ge_of_edge (hAsub δ ha) (hBe δ b hb)) }
  obtain ⟨δ₀, hδ₀, hP⟩ := (hconc A B hAB).1 ι' ⟨hι'0, hι'1⟩
  -- the segment bound for the best segments
  have hE := hsegu ι ⟨hι0, hιι₀⟩ (fun δ => if h : good δ then S δ (best δ h) else ∅)
    (by filter_upwards [hgood] with δ hδ; simp only [dif_pos hδ]; exact hSseg δ hδ _)
  set e : ℝ := c * ι' ^ 2 - κ
  have he : 0 < e := by have := hcι; simp only [e]; linarith
  set η : ℝ := ε / (2 * (|χ| + ε + 1)) with hηdef
  have hη0 : 0 < η := by positivity
  filter_upwards [hgood, hE, eventually_Ioo_nhdsGT hδ₀, eventually_rpow_le he hη0]
    with δ hg hEδ hδ hηδ
  have hδpos : 0 < δ := hδ.1
  have hL : 0 < Real.log δ⁻¹ := log_inv_pos_of_mem hδ
  simp only [dif_pos hg] at hEδ
  haveI := hne δ hg
  set X : Fin 4 × Fin (n δ) → Ω → ℝ := fun i ω => logMinLGD (μ ω) δ (S δ i) G with hXdef
  have hEi : ∀ i, (χ - 2 * ι) * Real.log δ⁻¹ ≤ ∫ ω, X i ω ∂P := fun i =>
    hEδ.trans (hbest δ hg i)
  have hpos : 0 < (χ - 2 * ι) * Real.log δ⁻¹ := mul_pos (by linarith) hL
  have hint : ∀ i, Integrable (X i) P := fun i => by
    by_contra h
    have := hEi i
    rw [integral_undef h] at this
    linarith
  have hYX : ∀ ω, ∃ j, logMinLGD (μ ω) δ F G = X j ω := fun ω =>
    exists_logMinLGD_eq_of_cover (μ ω) δ (fun i => (hSseg δ hg i).1) (hcover δ hg)
  set bad : Set Ω := ⋃ i, (conc δ i)ᶜ with hbaddef
  set K := (χ - 2 * ι - ι') * Real.log δ⁻¹ with hKdef
  have hK : 0 ≤ K := mul_nonneg (by linarith) hL.le
  have hgd : ∀ ω ∉ bad, ∀ i, K ≤ X i ω := fun ω hω i => by
    simp only [bad, mem_iUnion, mem_compl_iff, not_exists, not_not] at hω
    have h1 := hω i
    simp only [conc, conc1Event, mem_setOf_eq] at h1
    have h2 := (abs_le.mp h1).1
    have h3 := hEi i
    have h4 : K = (χ - 2 * ι) * Real.log δ⁻¹ - ι' * Real.log δ⁻¹ := by rw [hKdef]; ring
    rw [h4]
    show _ ≤ logMinLGD (μ ω) δ (S δ i) G
    linarith
  have hmain := integral_ge_of_good (Y := fun ω => logMinLGD (μ ω) δ F G) hK hYX
    (fun i ω => logMinLGD_nonneg _ _ _ _) hint
    ((aemeasurable_log_lgdMinSet hμ δ F G).aestronglyMeasurable) hgd
  have hbad : P.real bad ≤ (4 * n δ : ℝ) * δ ^ (c * ι' ^ 2) := by
    have h1 : P bad ≤ ∑ i, P (conc δ i)ᶜ := measure_iUnion_fintype_le P _
    have h2 : ∀ i, P (conc δ i)ᶜ ≤ ENNReal.ofReal (δ ^ (c * ι' ^ 2)) := fun i => by
      refine (hworst δ hg i).trans ?_
      have := hP δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
      simp only [A, B, dif_pos hg, if_pos hg] at this
      exact this
    have h3 : P bad ≤ ((4 * n δ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (δ ^ (c * ι' ^ 2)) := by
      refine h1.trans ((Finset.sum_le_sum fun i _ => h2 i).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
    rw [measureReal_def]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top) h3).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
    push_cast; ring
  have hcount : (4 * n δ : ℝ) * δ ^ (c * ι' ^ 2) ≤ δ ^ e := by
    have h0 : 8 * a / ℓ δ = 4 * (2 * a / ℓ δ) := by ring
    have h1 : (4 * n δ : ℝ) ≤ 8 * a / ℓ δ := by have := hnle δ hg; rw [h0]; linarith
    have h2 : 8 * a / ℓ δ ≤ 1 / ℓ δ :=
      div_le_div_of_nonneg_right (by linarith) (hℓpos δ hg).le
    have h3 : δ ^ e = δ ^ (c * ι' ^ 2) / ℓ δ := Real.rpow_sub hδpos _ _
    rw [h3, div_eq_mul_one_div, mul_comm (δ ^ (c * ι' ^ 2))]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
  rw [lt_div_iff₀ hL]
  have hPb : P.real bad ≤ η := (hbad.trans hcount).trans hηδ
  set q := χ - 2 * ι - ι' with hqdef
  have hq1 : χ - ε / 4 ≤ q := by rw [hqdef]; linarith
  have hq2 : q ≤ |χ| := by have := le_abs_self χ; rw [hqdef]; linarith
  have hηe : η * (2 * (|χ| + ε + 1)) = ε := by
    rw [hηdef]; field_simp
  have hqη : q * η ≤ ε / 2 := by
    have h1 : q * η ≤ |χ| * η := mul_le_mul_of_nonneg_right hq2 hη0.le
    have h2 : (|χ| + ε + 1) * η = |χ| * η + (ε + 1) * η := by ring
    have h3 : 0 ≤ (ε + 1) * η := by positivity
    have h4 : η * (2 * (|χ| + ε + 1)) = 2 * ((|χ| + ε + 1) * η) := by ring
    linarith
  have hq3 : χ - 3 * ε / 4 ≤ q * (1 - P.real bad) := by
    have hq0 : 0 ≤ q := by linarith
    have h1 : q * P.real bad ≤ q * η := mul_le_mul_of_nonneg_left hPb hq0
    have h2 : q * (1 - P.real bad) = q - q * P.real bad := by ring
    linarith
  have hfin : (χ - 3 * ε / 4) * Real.log δ⁻¹ ≤ K * (1 - P.real bad) := by
    calc (χ - 3 * ε / 4) * Real.log δ⁻¹ ≤ q * (1 - P.real bad) * Real.log δ⁻¹ :=
          mul_le_mul_of_nonneg_right hq3 hL.le
      _ = K * (1 - P.real bad) := by rw [hKdef]; ring
  have : (χ - ε) * Real.log δ⁻¹ < (χ - 3 * ε / 4) * Real.log δ⁻¹ :=
    mul_lt_mul_of_pos_right (by linarith) hL
  exact this.trans_le (hfin.trans hmain)

end DZZ
end LQGMetric
