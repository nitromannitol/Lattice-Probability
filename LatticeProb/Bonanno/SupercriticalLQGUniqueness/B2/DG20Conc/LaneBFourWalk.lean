/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFourWalk at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBMeetDetour

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

 



theorem laneB_four_crossings_walk {ξ : ℝ} {f : ℂ → ℝ}
    {P₀ P₁ P₂ P₃ : ℝ → ℂ} {a b c₁ d₁ c₂ d₂ c₃ d₃ : ℂ}
    {U : Set ℂ}
    (h₀ : IsPiecewiseC1Path P₀ a b)
    (h₁ : IsPiecewiseC1Path P₁ c₁ d₁)
    (h₂ : IsPiecewiseC1Path P₂ c₂ d₂)
    (h₃ : IsPiecewiseC1Path P₃ c₃ d₃)
    (hU₀ : MapsTo P₀ (Icc (0 : ℝ) 1) U)
    (hU₁ : MapsTo P₁ (Icc (0 : ℝ) 1) U)
    (hU₂ : MapsTo P₂ (Icc (0 : ℝ) 1) U)
    (hU₃ : MapsTo P₃ (Icc (0 : ℝ) 1) U)
    (h₀₁ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P₀ s = P₁ t)
    (h₁₂ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P₁ s = P₂ t)
    (h₀₃ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P₀ s = P₃ t) :
    ∃ W : ℝ → ℂ,
      IsPiecewiseC1Path W a b ∧
      MapsTo W (Icc (0 : ℝ) 1) U ∧
      (P₀ '' Icc (0 : ℝ) 1 ∪ P₁ '' Icc (0 : ℝ) 1 ∪
        P₂ '' Icc (0 : ℝ) 1 ∪ P₃ '' Icc (0 : ℝ) 1 ⊆
        W '' Icc (0 : ℝ) 1) ∧
      lfppLen ξ f W ≤ lfppLen ξ f P₀ +
        3 * (lfppLen ξ f P₁ + lfppLen ξ f P₂ + lfppLen ξ f P₃) := by
  obtain ⟨s₀₁, hs₀₁, t₀₁, ht₀₁, e₀₁⟩ := h₀₁
  obtain ⟨s₁₂, hs₁₂, t₁₂, ht₁₂, e₁₂⟩ := h₁₂
  obtain ⟨s₀₃, hs₀₃, t₀₃, ht₀₃, e₀₃⟩ := h₀₃
  let W₁ := laneBMeetDetour P₀ P₁ s₀₁ t₀₁
  have hW₁ : IsPiecewiseC1Path W₁ a b :=
    laneB_meetDetour_piecewise h₀ h₁ hs₀₁ ht₀₁ e₀₁
  have hW₁U : MapsTo W₁ (Icc (0 : ℝ) 1) U :=
    laneB_meetDetour_mapsTo hs₀₁ ht₀₁ e₀₁ hU₀ hU₁
  have hP₀W₁ : P₀ '' Icc (0 : ℝ) 1 ⊆ W₁ '' Icc (0 : ℝ) 1 :=
    laneB_meetDetour_contains_base hs₀₁ e₀₁
  have hP₁W₁ : P₁ '' Icc (0 : ℝ) 1 ⊆ W₁ '' Icc (0 : ℝ) 1 :=
    laneB_meetDetour_contains_crossing e₀₁
  obtain ⟨u₁₂, hu₁₂, eu₁₂⟩ := hP₁W₁ ⟨s₁₂, hs₁₂, rfl⟩
  let W₂ := laneBMeetDetour W₁ P₂ u₁₂ t₁₂
  have eW₁₂ : W₁ u₁₂ = P₂ t₁₂ := eu₁₂.trans e₁₂
  have hW₂ : IsPiecewiseC1Path W₂ a b :=
    laneB_meetDetour_piecewise hW₁ h₂ hu₁₂ ht₁₂ eW₁₂
  have hW₂U : MapsTo W₂ (Icc (0 : ℝ) 1) U :=
    laneB_meetDetour_mapsTo hu₁₂ ht₁₂ eW₁₂ hW₁U hU₂
  have hW₁W₂ : W₁ '' Icc (0 : ℝ) 1 ⊆ W₂ '' Icc (0 : ℝ) 1 :=
    laneB_meetDetour_contains_base hu₁₂ eW₁₂
  have hP₂W₂ : P₂ '' Icc (0 : ℝ) 1 ⊆ W₂ '' Icc (0 : ℝ) 1 :=
    laneB_meetDetour_contains_crossing eW₁₂
  obtain ⟨u₀₃, hu₀₃, eu₀₃⟩ := hW₁W₂ (hP₀W₁ ⟨s₀₃, hs₀₃, rfl⟩)
  let W₃ := laneBMeetDetour W₂ P₃ u₀₃ t₀₃
  have eW₂₃ : W₂ u₀₃ = P₃ t₀₃ := eu₀₃.trans e₀₃
  have hW₃ : IsPiecewiseC1Path W₃ a b :=
    laneB_meetDetour_piecewise hW₂ h₃ hu₀₃ ht₀₃ eW₂₃
  have hW₃U : MapsTo W₃ (Icc (0 : ℝ) 1) U :=
    laneB_meetDetour_mapsTo hu₀₃ ht₀₃ eW₂₃ hW₂U hU₃
  have hW₂W₃ : W₂ '' Icc (0 : ℝ) 1 ⊆ W₃ '' Icc (0 : ℝ) 1 :=
    laneB_meetDetour_contains_base hu₀₃ eW₂₃
  have hP₃W₃ : P₃ '' Icc (0 : ℝ) 1 ⊆ W₃ '' Icc (0 : ℝ) 1 :=
    laneB_meetDetour_contains_crossing eW₂₃
  refine ⟨W₃, hW₃, hW₃U, ?_, ?_⟩
  · exact union_subset (union_subset (union_subset
      (hP₀W₁.trans (hW₁W₂.trans hW₂W₃))
      (hP₁W₁.trans (hW₁W₂.trans hW₂W₃)))
      (hP₂W₂.trans hW₂W₃)) hP₃W₃
  · have hc₁ := laneB_meetDetour_len_le_add
      (ξ := ξ) (f := f) hs₀₁ ht₀₁ e₀₁
    have hc₂ := laneB_meetDetour_len_le_add
      (ξ := ξ) (f := f) hu₁₂ ht₁₂ eW₁₂
    have hc₃ := laneB_meetDetour_len_le_add
      (ξ := ξ) (f := f) hu₀₃ ht₀₃ eW₂₃
    calc
      lfppLen ξ f W₃ ≤ lfppLen ξ f W₂ + 3 * lfppLen ξ f P₃ := hc₃
      _ ≤ (lfppLen ξ f W₁ + 3 * lfppLen ξ f P₂) +
          3 * lfppLen ξ f P₃ := by gcongr
      _ ≤ ((lfppLen ξ f P₀ + 3 * lfppLen ξ f P₁) +
          3 * lfppLen ξ f P₂) + 3 * lfppLen ξ f P₃ := by gcongr
      _ = lfppLen ξ f P₀ +
          3 * (lfppLen ξ f P₁ + lfppLen ξ f P₂ + lfppLen ξ f P₃) := by
        simp only [mul_add]
        ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
