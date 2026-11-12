/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcH at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcG

/-!
# Splitting the good set: DZZ's core and the path regularity of `𝒳_δ` (P2-DZZCONC)

`DZZGoodSet` (S3ConcG) bundles DZZ's set `𝒜` (DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`,
l. 1572–1594, 1631–1645) with a finite-net property used only to pass from the continuum to
finitely many Gaussian coordinates (`gauss_far_le`). The two are independent:

* `DZZGoodCore`: `𝒜 ⊆ 𝒜_δ`, `P(𝒳_δ ∉ 𝒜) ≤ ε`, (eq-distance-Lip) on `𝒜` (DZZ's statement);
* `CoarseNet`: a set `ℛ` of coarse paths, `P(𝒳_δ ∉ ℛ) ≤ ε`, with a finite `1`-net (sample-path
  regularity of `(v, ε) ↦ η_ε(v)`, implicit in DZZ);
* `goodSet_of_core_net`: intersect (`𝒜 ∩ ℛ`).

OPEN nodes after this file: `DZZDistLip1Core`, `DZZDistLip2Core` (DZZ's argument) and
`DZZCoarseReg` (for every `δ ∈ (0,1)` and `ε > 0`, `CoarseNet` holds; a regularity statement
about the white-noise field). **`dzzDistLip1C_of_core`**, **`dzzDistLip2C_of_core`**,
**`dzzProp317_dzzMuIn_of_core`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DZZ's good set `𝒜 ⊆ 𝒜_δ` with (eq-distance-Lip) (DZZ l. 1572–1594). -/
def DZZGoodCore (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ)
    (ℓ τ ε : ℝ) : Prop :=
  ∃ 𝒜 : Set (CoarseIdx (dzzCmc γ) δ → ℝ), 𝒜 ⊆ CoarseGood γ (dzzCmc γ) δ ∧
    P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ≤ ε ∧
    ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) →
      |coarseLogD γ (dzzCmc γ) δ A B x - coarseLogD γ (dzzCmc γ) δ A B x'| ≤ τ

/-- A high-probability set of coarse paths with a finite `1`-net. -/
def CoarseNet (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ ε : ℝ) : Prop :=
  ∃ ℛ : Set (CoarseIdx (dzzCmc γ) δ → ℝ),
    P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ ℛ} ≤ ε ∧
    ∃ (n : ℕ) (t : Fin n → CoarseIdx (dzzCmc γ) δ),
      ∀ x ∈ ℛ, ∀ x' ∈ ℛ, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + 1

/-- **Path regularity of `𝒳_δ`** (OPEN). -/
def DZZCoarseReg (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) : Prop :=
  ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → CoarseNet P γ W δ ε

/-- **DZZ l. 1572–1594** (OPEN). -/
def DZZDistLip1Core (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZGoodCore P γ W δ (A δ) (B δ) (a * ι * Real.log δ⁻¹) (ι * Real.log δ⁻¹) (δ ^ (a * ι))

/-- **DZZ l. 1631–1645** (OPEN). -/
def DZZDistLip2Core (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZGoodCore P γ W δ (A δ) (B δ) (Real.log δ⁻¹ ^ (0.9 : ℝ)) (Real.log δ⁻¹ ^ (0.93 : ℝ))
        (δ ^ a)

theorem goodSet_of_core_net [IsFiniteMeasure P] {γ δ : ℝ} {A B : Set ℂ} {ℓ ℓ' τ ε₁ ε₂ ε : ℝ}
    (hc : DZZGoodCore P γ W δ A B ℓ τ ε₁) (hr : CoarseNet P γ W δ ε₂) (hℓ : ℓ' ≤ ℓ)
    (hε : ε₁ + ε₂ ≤ ε) : DZZGoodSet P γ W δ A B ℓ' τ ε := by
  obtain ⟨𝒜, hsub, h𝒜, hlip⟩ := hc
  obtain ⟨ℛ, hℛ, n, t, hnet⟩ := hr
  refine ⟨𝒜 ∩ ℛ, fun x hx => hsub hx.1, ?_, fun x hx x' hx' hxx =>
    hlip x hx.1 x' hx'.1 fun s => (hxx s).trans hℓ, n, t, fun x hx x' hx' => hnet x hx.2 x' hx'.2⟩
  have h1 := measureReal_mono (μ := P)
    (s₁ := {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜 ∩ ℛ})
    (s₂ := {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ∪
      {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ ℛ})
    (fun ω hω => by
      simp only [mem_setOf_eq, mem_inter_iff, not_and_or] at hω
      exact hω) (measure_ne_top P _)
  have h2 := measureReal_union_le (μ := P)
    {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜}
    {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ ℛ}
  linarith

/-- `2 δ^{x} ≤ δ^{x/2}` for small `δ` -/
lemma two_rpow_le {x : ℝ} (hx : 0 < x) : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    δ ^ x + δ ^ x ≤ δ ^ (x / 2) := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_delta_of_eventually
    (ev_exp_neg_le (k := x / 2) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨δ₀, hδ₀, fun δ hδ => ?_⟩
  have h1 := h δ hδ
  rw [rpow_eq_exp_log_inv hδ.1, rpow_eq_exp_log_inv hδ.1]
  have e : Real.exp (-(x * Real.log δ⁻¹)) =
      Real.exp (-(x / 2 * Real.log δ⁻¹)) * Real.exp (-(x / 2 * Real.log δ⁻¹)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have := Real.exp_pos (-(x / 2 * Real.log δ⁻¹))
  nlinarith

theorem dzzDistLip1C_of_core (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hreg : DZZCoarseReg P γ W)
    (h : DZZDistLip1Core P γ W ξ) : DZZDistLip1C P γ W ξ := by
  have := hW.isProbabilityMeasure
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a / 2, by positivity, fun A B hAB ι hι => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := h A B hAB ι hι
  obtain ⟨δ₂, hδ₂, h2⟩ := two_rpow_le (x := a * ι) (mul_pos ha hι.1)
  refine ⟨min δ₀ (min δ₂ 1), lt_min hδ₀ (lt_min hδ₂ one_pos), fun δ hδ => ?_⟩
  have hδa : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL : 0 ≤ Real.log δ⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_neg hδ.1 hδ1]
  refine goodSet_of_core_net (hD δ ⟨hδ.1, hδa⟩)
    (hreg δ ⟨hδ.1, hδ1⟩ (δ ^ (a * ι)) (Real.rpow_pos_of_pos hδ.1 _)) ?_ ?_
  · have : a / 2 * ι ≤ a * ι := by nlinarith [hι.1]
    exact mul_le_mul_of_nonneg_right this hL
  · have e : a / 2 * ι = a * ι / 2 := by ring
    rw [e]; exact h2 δ ⟨hδ.1, hδb⟩

theorem dzzDistLip2C_of_core (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hreg : DZZCoarseReg P γ W)
    (h : DZZDistLip2Core P γ W ξ) : DZZDistLip2C P γ W ξ := by
  have := hW.isProbabilityMeasure
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a / 2, by positivity, fun A B hAB => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := h A B hAB
  obtain ⟨δ₂, hδ₂, h2⟩ := two_rpow_le ha
  refine ⟨min δ₀ (min δ₂ 1), lt_min hδ₀ (lt_min hδ₂ one_pos), fun δ hδ => ?_⟩
  have hδa : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  exact goodSet_of_core_net (hD δ ⟨hδ.1, hδa⟩)
    (hreg δ ⟨hδ.1, hδ1⟩ (δ ^ a) (Real.rpow_pos_of_pos hδ.1 _)) le_rfl (h2 δ ⟨hδ.1, hδb⟩)

end DZZ
end LQGMetric
