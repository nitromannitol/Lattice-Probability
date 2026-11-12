/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54I1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54H3

/-!
# D117 P-54T (1): moving a boundary segment of `𝕍_{u,1/20}` to the configuration (P2-DZZ54C)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, (eq-translation-invariant) l. 2271 and "by symmetry"
l. 2555, realised (DEC-117 §2(a)(ii), §4 P-54T) by the isometry
`θ_j(z) = c₅₄ + ā_j (z − m_j)`, `m_j = u + (λ/2) e_j` the midpoint of the `j`-th side,
`ā_j = conj e_j`: it maps `u ↦ u₅₄`, the `j`-th side onto `{1/2} × [19/40, 21/40]` and the leg wall
`legSq u λ j` onto `K₅₄`. Own elementary geometry.

* `seg_side`: a boundary segment of positive length lies on one side `j`, its leg wall is
  `legSq u λ j`, and `θ_j(L) ⊆ vSeg s' t'` with `t' − s'` the length of `L`;
* `ae_legSq_lt_top`: a.s. finiteness of the leg distances;
* `prob_lgdMinSet_wall_eq`: the law of a walled `min D` does not depend on the white noise
  (`prob_lgdWall_eq`, S6L61G1, for sets).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- the rotation part `conj e_j` -/
def aJ : Fin 4 → ℂ := ![Complex.I, -1, -Complex.I, 1]

/-- the midpoint of the `j`-th side of `𝕍_{u,1/20}` -/
def legC (u : ℂ) (j : Fin 4) : ℂ := u + (((1 / 20 : ℝ) / 2 : ℝ) : ℂ) * legDir j

/-- the isometry to the configuration -/
def thJ (u : ℂ) (j : Fin 4) (z : ℂ) : ℂ := c₅₄ + aJ j * (z - legC u j)

lemma legSq_eq (u : ℂ) (j : Fin 4) : legSq u (1 / 20) j = sqBox (legC u j) (2 * (1 / 20)) := rfl

lemma thJ_eq_simMap (u : ℂ) (j : Fin 4) :
    thJ u j = simMap (aJ j) (c₅₄ - aJ j * legC u j) := by
  funext z; simp only [thJ, simMap]; ring

lemma norm_aJ (j : Fin 4) : ‖aJ j‖ = 1 := by
  fin_cases j <;> simp [aJ]

lemma aJ_ne_zero (j : Fin 4) : aJ j ≠ 0 := by
  intro h; have := norm_aJ j; rw [h, norm_zero] at this; norm_num at this

lemma thJ_u (u : ℂ) (j : Fin 4) : thJ u j u = u₅₄ := by
  fin_cases j <;> apply Complex.ext <;>
    simp [thJ, aJ, legC, legDir, c₅₄, u₅₄] <;> norm_num

lemma thJ_legSq (u : ℂ) (j : Fin 4) : thJ u j '' legSq u (1 / 20) j ⊆ K₅₄ := by
  rintro _ ⟨w, ⟨h1, h2⟩, rfl⟩
  have e : u + (((1 / 20 : ℝ) / 2 : ℝ) : ℂ) * legDir j = legC u j := rfl
  rw [e] at h1 h2
  rw [abs_le] at h1 h2
  refine ⟨?_, ?_⟩ <;> rw [abs_le] <;>
  fin_cases j <;> simp [thJ, aJ, c₅₄] at h1 h2 ⊢ <;> constructor <;> linarith

lemma legSq_subset_dzzVXi {u : ℂ} (hu : u ∈ dzzVbar) (j : Fin 4) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / 80) : legSq u (1 / 20) j ⊆ dzzVXi ξ := by
  obtain ⟨hr, hi⟩ := near_of_mem_dzzVbar hu
  intro z ⟨h1, h2⟩
  have e : u + (((1 / 20 : ℝ) / 2 : ℝ) : ℂ) * legDir j = legC u j := rfl
  rw [e] at h1 h2
  have hc : |(legC u j).re - u.re| ≤ 1 / 40 ∧ |(legC u j).im - u.im| ≤ 1 / 40 := by
    fin_cases j <;> simp [legC, legDir] <;> norm_num
  refine mem_dzzVXi_of_near (a := 1 / 10) ?_ ?_ (by linarith) hξ0
  · have := abs_sub_le z.re (legC u j).re (1 / 2)
    have := abs_sub_le (legC u j).re u.re (1 / 2)
    linarith [hc.1]
  · have := abs_sub_le z.im (legC u j).im (1 / 2)
    have := abs_sub_le (legC u j).im u.im (1 / 2)
    linarith [hc.2]

lemma norm_lt_of_re_im {z : ℂ} (h1 : |z.re| ≤ 1 / 40) (h2 : |z.im| ≤ 1 / 40) : ‖z‖ < 1 / 20 := by
  have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have a1 : z.re ^ 2 ≤ (1 / 40) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 : z.im ^ 2 ≤ (1 / 40) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith [norm_nonneg z]

/-- **a.s. finiteness of the leg distances** (pattern of `ae_lgd_tilde_lt_top`) -/
theorem ae_legSq_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) {u : ℂ} (hu : u ∈ dzzVbar) {j : Fin 4}
    {x : ℂ} (hx : x ∈ sqSide u (1 / 20) j) :
    ∀ᵐ ω ∂P, lgdDZZ (dzzWall (legSq u (1 / 20) j) (dzzMuIn γ W ω)) δ u x < ⊤ := by
  filter_upwards [ae_wickQArea_reg hW hγ hγ2] with ω hω
  obtain ⟨hK, hat⟩ := hω
  obtain ⟨hr, hi⟩ := near_of_mem_dzzVbar hu
  set m := legC u j
  have hc : |m.re - u.re| ≤ 1 / 40 ∧ |m.im - u.im| ≤ 1 / 40 := by
    fin_cases j <;> simp [m, legC, legDir] <;> norm_num
  have hBT : Metric.ball m (1 / 20) ⊆ legSq u (1 / 20) j := fun z hz => by
    rw [legSq_eq]
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - m)
    have h2 := Complex.abs_im_le_norm (z - m)
    rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
    exact ⟨by linarith, by linarith⟩
  have hBS : Metric.ball m (1 / 20) ⊆ openSquare := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - m)
    have h2 := Complex.abs_im_le_norm (z - m)
    rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
    rw [abs_le] at h1 h2 hr hi
    have := abs_le.1 hc.1
    have := abs_le.1 hc.2
    show 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hBV : Metric.ball m (1 / 20) ⊆ dzzV := hBS.trans fun z hz =>
    ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hw : ∀ K ⊆ Metric.ball m (1 / 20),
      dzzWall (legSq u (1 / 20) j) (dzzMuIn γ W ω) K = wickQArea γ W ω K := fun K hKB => by
    have hT := hKB.trans hBT
    rw [legSq_eq] at hT ⊢
    rw [dzzWall_apply_of_subset (isClosed_sqBox _ _).measurableSet hT,
      dzzMuIn, dzzWall_apply_of_subset isClosed_dzzV.measurableSet (hKB.trans hBV)]
  have hum : u ∈ Metric.ball m (1 / 20) := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine norm_lt_of_re_im ?_ ?_
    · rw [Complex.sub_re, abs_sub_comm]; exact hc.1
    · rw [Complex.sub_im, abs_sub_comm]; exact hc.2
  have hxm : x ∈ Metric.ball m (1 / 20) := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine norm_lt_of_re_im ?_ ?_ <;>
    fin_cases j <;> simp [sqSide, m, legC, legDir, Complex.mem_reProdIm] at hx ⊢ <;>
      rw [abs_le] <;> constructor <;> norm_num <;> linarith
  exact lgdDZZ_lt_top_of_convex Metric.isOpen_ball (convex_ball _ _)
    (fun K hKc hKB => by rw [hw K hKB]; exact hK K hKc (hKB.trans hBS))
    (fun x hx => by rw [hw {x} (singleton_subset_iff.mpr hx)]; exact hat x (hBS hx))
    hδ hum hxm

/-- **the law of a walled `min D_δ(A, B)` does not depend on the white noise** -/
theorem prob_lgdMinSet_wall_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (K : Set ℂ) (δ : ℝ) (A B : Set ℂ) (T : Set ℕ∞) :
    P {ω | lgdMinSet (dzzWall K (dzzMuIn γ W ω)) δ A B ∈ T} =
      P' {ω | lgdMinSet (dzzWall K (dzzMuIn γ W' ω)) δ A B ∈ T} := by
  have hev : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => m c q :=
    fun c q => (measurable_pi_apply q).comp (measurable_pi_apply c)
  have hmeas : Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => lgdRat (wallMass K m) δ A B :=
    measurable_lgdRat (m := fun m => wallMass K m) (fun c q => (hev c q).add measurable_const)
      δ A B
  have h := prob_ballMassQ_dzzMuIn_eq hW hW' hγ hγ2 (hmeas (T.to_countable.measurableSet))
  simp only [mem_preimage] at h
  simp_rw [lgdMinSet_eq_lgdRat, ballMassQ_dzzWall]
  exact h

end DZZ
end LQGMetric
