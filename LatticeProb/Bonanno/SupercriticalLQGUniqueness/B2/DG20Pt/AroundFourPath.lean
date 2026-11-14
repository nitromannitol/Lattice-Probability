/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundConcat
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.Inputs

 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem around_loop_of_four_admPaths
    (A : EuclideanAnnulus) (ξ : ℝ) (φ : ℂ → ℝ)
    (f₀ f₁ f₂ f₃ : ℝ → ℂ) (L : ℝ≥0∞)
    (h₀ : AdmPath (Strong.cfgOpens A 0 : Set ℂ) (Strong.cfgSet₁ A 0)
      (Strong.cfgSet₂ A 0) f₀)
    (h₁ : AdmPath (Strong.cfgOpens A 1 : Set ℂ) (Strong.cfgSet₁ A 1)
      (Strong.cfgSet₂ A 1) f₁)
    (h₂ : AdmPath (Strong.cfgOpens A 2 : Set ℂ) (Strong.cfgSet₁ A 2)
      (Strong.cfgSet₂ A 2) f₂)
    (h₃ : AdmPath (Strong.cfgOpens A 3 : Set ℂ) (Strong.cfgSet₁ A 3)
      (Strong.cfgSet₂ A 3) f₃)
    (hcost : lfppLen ξ φ f₀ + lfppLen ξ φ f₁ + lfppLen ξ φ f₂ +
      lfppLen ξ φ f₃ < L) :
    ∃ (γ : ℝ → ℂ) (a b : ℂ), IsPiecewiseC1Path γ a b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ A.toSet) ∧
      LQGMetric.Disconnects (γ '' Icc (0 : ℝ) 1) A.innerBoundary A.outerBoundary ∧
      lfppLen ξ φ γ < L := by
  rcases h₀ with ⟨a₀, ha₀, b₀, hb₀, hf₀, hU₀⟩
  rcases h₁ with ⟨a₁, ha₁, b₁, hb₁, hf₁, hU₁⟩
  rcases h₂ with ⟨a₂, ha₂, b₂, hb₂, hf₂, hU₂⟩
  rcases h₃ with ⟨a₃, ha₃, b₃, hb₃, hf₃, hU₃⟩
  have hp₀ : Strong.PathIn A.center (Strong.cfgU (Strong.annL A) (Strong.annΔ A) 0)
      (Strong.cfgK₁ (Strong.annL A) (Strong.annΔ A) 0)
      (Strong.cfgK₂ (Strong.annL A) (Strong.annΔ A) 0) f₀ 0 1 :=
    ⟨zero_le_one, hf₀.continuousOn, hU₀, hf₀.source ▸ ha₀,
      hf₀.target ▸ hb₀⟩
  have hp₁ : Strong.PathIn A.center (Strong.cfgU (Strong.annL A) (Strong.annΔ A) 1)
      (Strong.cfgK₁ (Strong.annL A) (Strong.annΔ A) 1)
      (Strong.cfgK₂ (Strong.annL A) (Strong.annΔ A) 1) f₁ 0 1 :=
    ⟨zero_le_one, hf₁.continuousOn, hU₁, hf₁.source ▸ ha₁,
      hf₁.target ▸ hb₁⟩
  have hp₂ : Strong.PathIn A.center (Strong.cfgU (Strong.annL A) (Strong.annΔ A) 2)
      (Strong.cfgK₁ (Strong.annL A) (Strong.annΔ A) 2)
      (Strong.cfgK₂ (Strong.annL A) (Strong.annΔ A) 2) f₂ 0 1 :=
    ⟨zero_le_one, hf₂.continuousOn, hU₂, hf₂.source ▸ ha₂,
      hf₂.target ▸ hb₂⟩
  have hp₃ : Strong.PathIn A.center (Strong.cfgU (Strong.annL A) (Strong.annΔ A) 3)
      (Strong.cfgK₁ (Strong.annL A) (Strong.annΔ A) 3)
      (Strong.cfgK₂ (Strong.annL A) (Strong.annΔ A) 3) f₃ 0 1 :=
    ⟨zero_le_one, hf₃.continuousOn, hU₃, hf₃.source ▸ ha₃,
      hf₃.target ▸ hb₃⟩
  obtain ⟨s₀, hs₀, t₀, ht₀, s₁, hs₁, t₁, ht₁, s₂, hs₂, t₂, ht₂,
    s₃, hs₃, t₃, ht₃, z₁, z₂, z₃, hdisc⟩ :=
    Strong.exists_around_loop A.center (Strong.annΔ_pos A) hp₀ hp₁ hp₂ hp₃
  let P₀ := Strong.seg f₀ s₀ t₀
  let P₁ := Strong.seg f₁ s₁ t₁
  let P₂ := Strong.seg f₂ s₂ t₂
  let P₃ := Strong.seg f₃ s₃ t₃
  let γ := concatPath (concatPath (concatPath P₀ P₁) P₂) P₃
  have hP₀ : IsPiecewiseC1Path P₀ (f₀ s₀) (f₀ t₀) :=
    isPiecewiseC1Path_aroundSeg hf₀ hs₀ ht₀
  have hP₁ : IsPiecewiseC1Path P₁ (f₁ s₁) (f₁ t₁) :=
    isPiecewiseC1Path_aroundSeg hf₁ hs₁ ht₁
  have hP₂ : IsPiecewiseC1Path P₂ (f₂ s₂) (f₂ t₂) :=
    isPiecewiseC1Path_aroundSeg hf₂ hs₂ ht₂
  have hP₃ : IsPiecewiseC1Path P₃ (f₃ s₃) (f₃ t₃) :=
    isPiecewiseC1Path_aroundSeg hf₃ hs₃ ht₃
  have h01 : P₀ 1 = P₁ 0 := by simpa only [P₀, P₁, Strong.seg_one, Strong.seg_zero] using z₁
  have h12 : P₁ 1 = P₂ 0 := by simpa only [P₁, P₂, Strong.seg_one, Strong.seg_zero] using z₂
  have h23 : P₂ 1 = P₃ 0 := by simpa only [P₂, P₃, Strong.seg_one, Strong.seg_zero] using z₃
  have hP₁' : IsPiecewiseC1Path P₁ (f₀ t₀) (f₁ t₁) := by
    simpa only [z₁] using hP₁
  have h01p : IsPiecewiseC1Path (concatPath P₀ P₁) (f₀ s₀) (f₁ t₁) := by
    exact isPiecewiseC1Path_concatPath hP₀ hP₁'
  have concat_one (P R : ℝ → ℂ) : concatPath P R 1 = R 1 := by
    rw [concatPath, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
    norm_num
  have h012 : (concatPath P₀ P₁) 1 = P₂ 0 := by
    rw [concat_one]
    exact h12
  have h012p : IsPiecewiseC1Path (concatPath (concatPath P₀ P₁) P₂)
      (f₀ s₀) (f₂ t₂) := by
    have hP₂' : IsPiecewiseC1Path P₂ (f₁ t₁) (f₂ t₂) := by
      simpa only [z₂] using hP₂
    exact isPiecewiseC1Path_concatPath h01p hP₂'
  have h0123 : (concatPath (concatPath P₀ P₁) P₂) 1 = P₃ 0 := by
    rw [concat_one]
    exact h23
  have hγ : IsPiecewiseC1Path γ (f₀ s₀) (f₃ t₃) := by
    have hP₃' : IsPiecewiseC1Path P₃ (f₂ t₂) (f₃ t₃) := by
      simpa only [z₃] using hP₃
    exact isPiecewiseC1Path_concatPath h012p hP₃'
  have htrace : γ '' Icc (0 : ℝ) 1 =
      P₀ '' Icc (0 : ℝ) 1 ∪ P₁ '' Icc (0 : ℝ) 1 ∪
        P₂ '' Icc (0 : ℝ) 1 ∪ P₃ '' Icc (0 : ℝ) 1 := by
    dsimp [γ]
    rw [concatPath_image_Icc _ _ h0123, concatPath_image_Icc _ _ h012,
      concatPath_image_Icc _ _ h01]
  have hQsub : Strong.glue4 P₀ P₁ P₂ P₃ '' Icc (0 : ℝ) 4 ⊆
      γ '' Icc (0 : ℝ) 1 := by
    rw [htrace]
    exact glue4_image_subset _ _ _ _
  have hA₀ : ∀ u ∈ Icc (0 : ℝ) 1, P₀ u ∈ A.toSet := fun u hu =>
    Strong.cfgOpens_subset_toSet A 0 (hU₀ _ (Strong.seg_param_mem hs₀ ht₀ hu))
  have hA₁ : ∀ u ∈ Icc (0 : ℝ) 1, P₁ u ∈ A.toSet := fun u hu =>
    Strong.cfgOpens_subset_toSet A 1 (hU₁ _ (Strong.seg_param_mem hs₁ ht₁ hu))
  have hA₂ : ∀ u ∈ Icc (0 : ℝ) 1, P₂ u ∈ A.toSet := fun u hu =>
    Strong.cfgOpens_subset_toSet A 2 (hU₂ _ (Strong.seg_param_mem hs₂ ht₂ hu))
  have hA₃ : ∀ u ∈ Icc (0 : ℝ) 1, P₃ u ∈ A.toSet := fun u hu =>
    Strong.cfgOpens_subset_toSet A 3 (hU₃ _ (Strong.seg_param_mem hs₃ ht₃ hu))
  have hγA : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ A.toSet := by
    intro u hu
    have hmem : γ u ∈ γ '' Icc (0 : ℝ) 1 := ⟨u, hu, rfl⟩
    rw [htrace] at hmem
    rcases hmem with (((h | h) | h) | h)
    · rcases h with ⟨v, hv, hev⟩
      rw [← hev]
      exact hA₀ v hv
    · rcases h with ⟨v, hv, hev⟩
      rw [← hev]
      exact hA₁ v hv
    · rcases h with ⟨v, hv, hev⟩
      rw [← hev]
      exact hA₂ v hv
    · rcases h with ⟨v, hv, hev⟩
      rw [← hev]
      exact hA₃ v hv
  have hdisc' : LQGMetric.Disconnects (γ '' Icc (0 : ℝ) 1)
      A.innerBoundary A.outerBoundary := by
    rw [Strong.exp_annL, Strong.exp_annL_add] at hdisc
    exact LQGMetric.Disconnects.mono hdisc hQsub subset_rfl subset_rfl
  have hlen : lfppLen ξ φ γ =
      lfppLen ξ φ P₀ + lfppLen ξ φ P₁ + lfppLen ξ φ P₂ +
        lfppLen ξ φ P₃ := by
    dsimp [γ]
    rw [lfppLen_concatPath h0123, lfppLen_concatPath h012,
      lfppLen_concatPath h01]
  have hcost' : lfppLen ξ φ γ < L := by
    rw [hlen]
    exact (add_le_add (add_le_add (add_le_add
      (lfppLen_aroundSeg_le ξ φ f₀ hs₀ ht₀)
      (lfppLen_aroundSeg_le ξ φ f₁ hs₁ ht₁))
      (lfppLen_aroundSeg_le ξ φ f₂ hs₂ ht₂))
      (lfppLen_aroundSeg_le ξ φ f₃ hs₃ ht₃)).trans_lt hcost
  exact ⟨γ, f₀ s₀, f₃ t₃, hγ, hγA, hdisc', hcost'⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
