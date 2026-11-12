/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_9Neg at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10Neg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.9 for `p ≤ 0`

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.9 (`prop-diam-moment`) assuming Proposition 3.10, first sentence (T:1766):
"For `p < 0`, the bound (eqn-diam-moment) follows from the lower bound of Proposition 3.1."

We take two points `z ≠ w` of `K` and apply the lower bound of Proposition 3.1 (centre `0`) to
`K₁ = B̄_ε(z)`, `K₂ = B̄_ε(w)` (`ε = |z-w|/3`) in the open connected set `ℂ`:
`D_h(𝕣K₁, 𝕣K₂; ℂ) ≤ D_h(𝕣z, 𝕣w; ℂ) ≤ D_h(𝕣z, 𝕣w; 𝕣U) ≤ sup_{u,v ∈ 𝕣K} D_h(u, v; 𝕣U)`.
(Using `ℂ` as the open set of Prop 3.1 avoids assuming `U` connected, which Prop 3.9 does not.)
Uniformity over realizations: canonical space and `prob_le_canonical`, as in `P3_10Neg`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

lemma scaleSet_univ {r : ℝ} (hr : 0 < r) (z : ℂ) : scaleSet r z univ = univ := by
  refine eq_univ_of_forall fun w => (mem_scaleSet_iff hr z w univ).2 (mem_univ _)

lemma mem_scaleSet_of_mem (r : ℝ) (z : ℂ) {K : Set ℂ} {x : ℂ} (hx : x ∈ K) :
    (r : ℂ) * x + z ∈ scaleSet r z K := ⟨x, hx, rfl⟩

lemma not_subsingleton_closedBall (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ¬ (closedBall z ε).Subsingleton := by
  intro hs
  have h := @hs (z + ε) (mem_closedBall.2 (by rw [dist_eq_norm, add_sub_cancel_left,
    Complex.norm_real, Real.norm_of_nonneg hε.le])) z (mem_closedBall_self hε.le)
  have := congrArg Complex.re h
  simp at this
  linarith

/-- **Lower tail of `sup_{u,v∈𝕣K} D_h(u, v; 𝕣U)`** (Prop 3.1, lower bound), canonical space -/
theorem diam_K_lower_tail (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {U K : Set ℂ}
    (hK1 : ¬ K.Subsingleton)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 →
      μ {g | internalDiam (D g) (scaleSet 𝕣 0 K) (scaleSet 𝕣 0 U) <
        ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c g 𝕣 0)} ≤ ENNReal.ofReal (C * A ^ (-p)) := by
  intro p hp
  obtain ⟨z, hz, w, hw, hzw⟩ := Set.not_subsingleton_iff.1 hK1
  set ε := dist z w / 3 with hε
  have hε0 : 0 < ε := by have := dist_pos.2 hzw; rw [hε]; linarith
  have hdisj : Disjoint (closedBall z ε) (closedBall w ε) := by
    refine closedBall_disjoint_closedBall ?_
    rw [hε]; have := dist_pos.2 hzw; linarith
  obtain ⟨C, A₀, hC⟩ := h31 γ hγ0 hγ2 D c hD univ (closedBall z ε) (closedBall w ε) isOpen_univ
    isConnected_univ (isCompact_closedBall z ε) (isCompact_closedBall w ε)
    ((convex_closedBall z ε).isConnected ⟨z, mem_closedBall_self hε0.le⟩)
    ((convex_closedBall w ε).isConnected ⟨w, mem_closedBall_self hε0.le⟩) (subset_univ _)
    (subset_univ _) hdisj (not_subsingleton_closedBall z hε0) (not_subsingleton_closedBall w hε0)
    μ id hμ p hp
  refine ⟨C, A₀, fun A hA 𝕣 h𝕣 => le_trans (measure_mono fun g hg => ?_) (hC A hA 𝕣 h𝕣)⟩
  simp only [mem_ofPred_eq, mem_compl_iff, id] at hg ⊢
  rintro ⟨h1, -⟩
  refine absurd (h1.trans ?_) (not_le.2 hg)
  rw [scaleSet_univ h𝕣]
  have hz' := mem_scaleSet_of_mem 𝕣 0 (mem_closedBall_self hε0.le : z ∈ closedBall z ε)
  have hw' := mem_scaleSet_of_mem 𝕣 0 (mem_closedBall_self hε0.le : w ∈ closedBall w ε)
  refine (iInf₂_le_of_le _ hz' (iInf₂_le_of_le _ hw' le_rfl)).trans ?_
  refine le_trans ?_ (le_iSup₂_of_le _ (mem_scaleSet_of_mem 𝕣 0 hz)
    (le_iSup₂_of_le _ (mem_scaleSet_of_mem 𝕣 0 hw) le_rfl))
  exact MetricGeometry.internalEDist_anti (image_mono (subset_univ _)) _ _

/-- **DFGPS Prop 3.9 for `p ≤ 0`** (T:1766) -/
theorem prop3_9_nonpos (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {U K : Set ℂ}
    (hK1 : ¬ K.Subsingleton) {p : ℝ} (hp : p ≤ 0) :
    ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) 𝕣 0)⁻¹ *
          internalDiam (D (h ω)) (scaleSet 𝕣 0 K) (scaleSet 𝕣 0 U)) ^ p ∂P ≤
        ENNReal.ofReal Cp := by
  rcases hp.eq_or_lt with rfl | hp
  · refine ⟨1, fun P _ h _ 𝕣 _ => ?_⟩
    simp
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  obtain ⟨C, A₀, hC⟩ := diam_K_lower_tail h31 hγ0 hγ2 hD (U := U) hK1 hμ (1 - p) (by linarith)
  set t₀ := max 1 (A₀ + 1)
  refine ⟨momBd (-p) (1 - p) (max C 0) t₀, fun P _ h hh 𝕣 h𝕣 => ?_⟩
  refine lintegral_rpow_neg_le_of_tail P _ hp (by linarith) (le_max_right _ _) (le_max_left _ _)
    fun t ht => ?_
  have hA : A₀ < t := by have := le_max_right 1 (A₀ + 1); linarith
  have ht0 : 0 < t := by have := le_max_left 1 (A₀ + 1); linarith
  refine le_trans ?_ ((hC t hA 𝕣 h𝕣).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0.le _))))
  refine le_trans (measure_mono fun ω hω => ?_) (prob_le_canonical hμ P h hh _)
  simp only [mem_ofPred_eq] at hω ⊢
  set s := scaleFac (xiGamma γ) c (h ω) 𝕣 0
  have hs : 0 < s := mul_pos (hD.tightness.1 𝕣 h𝕣) (Real.exp_pos _)
  by_contra hcon
  rw [not_lt] at hcon
  refine absurd hω (not_lt.2 ?_)
  calc ENNReal.ofReal t⁻¹ = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t⁻¹ * s) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ _ := by
        rw [ENNReal.ofReal_inv_of_pos hs]
        exact mul_le_mul_right hcon _

end LQGMetric.DFGPS
