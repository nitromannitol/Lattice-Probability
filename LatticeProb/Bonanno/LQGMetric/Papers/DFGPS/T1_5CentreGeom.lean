/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5CentreGeom at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Centre
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.5: the configurations to which Proposition 3.1 is applied

DFGPS (arXiv:1905.00380, "T"), proof of Theorem 1.5 (T:1659–1723) applies Proposition 3.1
(T:1414–1420) to squares/annuli around the grid points (Step 1) and, through Axiom V, to the
distance between the sides of `𝕣𝕊` (Steps 2–3). We use closed boxes `[a,b] ×ℂ [c,d]` as `K₁, K₂`
inside an open box `U`, and the annulus `B̄_{3/4}(0) → ∂B_{3/2}(0)` in `B_2(0)`. Here we check the
hypotheses of Proposition 3.1 for these sets and describe the scaled sets `scaleSet r z K`.
-/

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint

lemma mem_scaleSet_iff {r : ℝ} (hr : 0 < r) (z w : ℂ) (K : Set ℂ) :
    w ∈ scaleSet r z K ↔ (w - z) / (r : ℂ) ∈ K := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold scaleSet
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [add_sub_cancel_right, mul_div_cancel_left₀ _ hr']
  · intro h
    exact ⟨_, h, by show (r : ℂ) * ((w - z) / r) + z = w; rw [mul_div_cancel₀ _ hr', sub_add_cancel]⟩

lemma mem_scaleSet_Icc {r : ℝ} (hr : 0 < r) (z w : ℂ) (a b c d : ℝ) :
    w ∈ scaleSet r z (Icc a b ×ℂ Icc c d) ↔
      (z.re + r * a ≤ w.re ∧ w.re ≤ z.re + r * b) ∧ (z.im + r * c ≤ w.im ∧ w.im ≤ z.im + r * d) := by
  rw [mem_scaleSet_iff hr, mem_reProdIm, div_ofReal_re, div_ofReal_im, mem_Icc, mem_Icc,
    le_div_iff₀ hr, div_le_iff₀ hr, le_div_iff₀ hr, div_le_iff₀ hr, sub_re, sub_im]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma mem_scaleSet_Ioo {r : ℝ} (hr : 0 < r) (z w : ℂ) (a b c d : ℝ) :
    w ∈ scaleSet r z (Ioo a b ×ℂ Ioo c d) ↔
      (z.re + r * a < w.re ∧ w.re < z.re + r * b) ∧ (z.im + r * c < w.im ∧ w.im < z.im + r * d) := by
  rw [mem_scaleSet_iff hr, mem_reProdIm, div_ofReal_re, div_ofReal_im, mem_Ioo, mem_Ioo,
    lt_div_iff₀ hr, div_lt_iff₀ hr, lt_div_iff₀ hr, div_lt_iff₀ hr, sub_re, sub_im]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma scaleSet_closedBall {r : ℝ} (hr : 0 < r) (z : ℂ) (ρ : ℝ) :
    scaleSet r z (closedBall 0 ρ) = closedBall z (ρ * r) := by
  ext w
  rw [mem_scaleSet_iff hr, mem_closedBall, mem_closedBall, dist_zero_right, dist_eq_norm,
    norm_div, norm_real, Real.norm_of_nonneg hr.le, div_le_iff₀ hr]

lemma scaleSet_ball {r : ℝ} (hr : 0 < r) (z : ℂ) (ρ : ℝ) :
    scaleSet r z (ball 0 ρ) = ball z (ρ * r) := by
  ext w
  rw [mem_scaleSet_iff hr, mem_ball, mem_ball, dist_zero_right, dist_eq_norm,
    norm_div, norm_real, Real.norm_of_nonneg hr.le, div_lt_iff₀ hr]

lemma scaleSet_sphere {r : ℝ} (hr : 0 < r) (z : ℂ) (ρ : ℝ) :
    scaleSet r z (sphere 0 ρ) = sphere z (ρ * r) := by
  ext w
  rw [mem_scaleSet_iff hr, mem_sphere, mem_sphere, dist_zero_right, dist_eq_norm,
    norm_div, norm_real, Real.norm_of_nonneg hr.le, div_eq_iff hr.ne']

lemma isConnected_box {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IsConnected (Icc a b ×ℂ Icc c d) := by
  have hc : Convex ℝ (Icc a b ×ℂ Icc c d) :=
    ((convex_Icc a b).linear_preimage reLm).inter ((convex_Icc c d).linear_preimage imLm)
  exact hc.isConnected (reProdIm_nonempty.2 ⟨nonempty_Icc.2 hab, nonempty_Icc.2 hcd⟩)

lemma not_subsingleton_box {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hn : a < b ∨ c < d) :
    ¬ (Icc a b ×ℂ Icc c d).Subsingleton := by
  intro hs
  rcases hn with h | h
  · have := hs (x := ⟨a, c⟩) (mem_reProdIm.2 ⟨⟨le_rfl, hab⟩, le_rfl, hcd⟩)
      (y := ⟨b, c⟩) (mem_reProdIm.2 ⟨⟨hab, le_rfl⟩, le_rfl, hcd⟩)
    have := congrArg Complex.re this
    simp only at this; linarith
  · have := hs (x := ⟨a, c⟩) (mem_reProdIm.2 ⟨⟨le_rfl, hab⟩, le_rfl, hcd⟩)
      (y := ⟨a, d⟩) (mem_reProdIm.2 ⟨⟨le_rfl, hab⟩, hcd, le_rfl⟩)
    have := congrArg Complex.im this
    simp only at this; linarith

/-- **Prop 3.1 at every centre** for boxes `K_i = [a_i,b_i] ×ℂ [c_i,d_i]` in `U = (X₀,X₁) ×ℂ (Y₀,Y₁)` -/
theorem prop3_1_centre_box (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ X₀ X₁ Y₀ Y₁ : ℝ} (h₁ : a₁ ≤ b₁) (h₁' : c₁ ≤ d₁) (h₂ : a₂ ≤ b₂)
    (h₂' : c₂ ≤ d₂) (hn₁ : a₁ < b₁ ∨ c₁ < d₁) (hn₂ : a₂ < b₂ ∨ c₂ < d₂)
    (hdis : b₁ < a₂ ∨ d₁ < c₂) (hX : X₀ < a₁ ∧ b₁ < X₁ ∧ X₀ < a₂ ∧ b₂ < X₁)
    (hY : Y₀ < c₁ ∧ d₁ < Y₁ ∧ Y₀ < c₂ ∧ d₂ < Y₁)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : ℂ,
      μ {g | ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c g 𝕣 z) ≤
            setDistIn (D g) (scaleSet 𝕣 z (Icc a₁ b₁ ×ℂ Icc c₁ d₁))
              (scaleSet 𝕣 z (Icc a₂ b₂ ×ℂ Icc c₂ d₂)) (scaleSet 𝕣 z (Ioo X₀ X₁ ×ℂ Ioo Y₀ Y₁)) ∧
          setDistIn (D g) (scaleSet 𝕣 z (Icc a₁ b₁ ×ℂ Icc c₁ d₁))
              (scaleSet 𝕣 z (Icc a₂ b₂ ×ℂ Icc c₂ d₂)) (scaleSet 𝕣 z (Ioo X₀ X₁ ×ℂ Ioo Y₀ Y₁)) ≤
            ENNReal.ofReal (A * scaleFac (xiGamma γ) c g 𝕣 z)}ᶜ ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  have hUc : IsConnected (Ioo X₀ X₁ ×ℂ Ioo Y₀ Y₁) :=
    (((convex_Ioo X₀ X₁).linear_preimage reLm).inter
      ((convex_Ioo Y₀ Y₁).linear_preimage imLm)).isConnected
      (reProdIm_nonempty.2 ⟨nonempty_Ioo.2 (by linarith), nonempty_Ioo.2 (by linarith)⟩)
  refine prop3_1_centre h31 hγ0 hγ2 hD (isOpen_Ioo.reProdIm isOpen_Ioo) hUc
    (isCompact_Icc.reProdIm isCompact_Icc) (isCompact_Icc.reProdIm isCompact_Icc)
    (isConnected_box h₁ h₁') (isConnected_box h₂ h₂') ?_ ?_ ?_
    (not_subsingleton_box h₁ h₁' hn₁) (not_subsingleton_box h₂ h₂' hn₂) hμ
  · intro w hw
    rw [mem_reProdIm] at hw ⊢
    exact ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  · intro w hw
    rw [mem_reProdIm] at hw ⊢
    exact ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  · rw [Set.disjoint_left]
    intro w hw1 hw2
    rw [mem_reProdIm] at hw1 hw2
    rcases hdis with h | h
    · linarith [hw1.1.2, hw2.1.1]
    · linarith [hw1.2.2, hw2.2.1]

/-- **Prop 3.1 at every centre** for the annulus `B̄_{3/4}(0) → ∂B_{3/2}(0)` in `B_2(0)` -/
theorem prop3_1_centre_ann (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : ℂ,
      μ {g | ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c g 𝕣 z) ≤
            setDistIn (D g) (closedBall z (3 / 4 * 𝕣)) (sphere z (3 / 2 * 𝕣)) (ball z (2 * 𝕣))}ᶜ ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hdis : Disjoint (closedBall (0 : ℂ) (3 / 4)) (sphere 0 (3 / 2)) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    rw [mem_closedBall] at hw1
    rw [mem_sphere] at hw2
    linarith
  have hn₁ : ¬ (closedBall (0 : ℂ) (3 / 4)).Subsingleton := by
    intro hs
    have := hs (x := (3 / 4 : ℂ)) (by norm_num) (y := (-3 / 4 : ℂ))
      (by norm_num)
    norm_num at this
  have hn₂ : ¬ (sphere (0 : ℂ) (3 / 2)).Subsingleton := by
    intro hs
    have := hs (x := (3 / 2 : ℂ)) (by norm_num) (y := (-3 / 2 : ℂ))
      (by norm_num)
    norm_num at this
  intro p hp
  obtain ⟨C, A₀, h⟩ := prop3_1_centre h31 hγ0 hγ2 hD isOpen_ball
    (isConnected_ball (x := (0 : ℂ)) (r := 2) (by norm_num)) (isCompact_closedBall 0 (3 / 4))
    (isCompact_sphere 0 (3 / 2)) (isConnected_closedBall (by norm_num))
    (isConnected_sphere hrank 0 (by norm_num))
    (closedBall_subset_ball (by norm_num : (3 / 4 : ℝ) < 2))
    (sphere_subset_ball (by norm_num : (3 / 2 : ℝ) < 2)) hdis hn₁ hn₂ hμ p hp
  refine ⟨C, A₀, fun A hA r hr z => le_trans (measure_mono ?_) (h A hA r hr z)⟩
  intro g hg hE
  apply hg
  rw [scaleSet_closedBall hr, scaleSet_sphere hr, scaleSet_ball hr] at hE
  exact hE.1

end LQGMetric.DFGPS
