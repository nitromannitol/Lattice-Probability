import LatticeProb.Topology.FirstExitTraceTimeChange
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Dilation of first-exit ball witnesses -/

set_option autoImplicit false

open Set Metric
open scoped Pointwise

namespace LatticeProb

/-- Positive dilation preserves ball containment and scales the center constraint. -/
theorem exists_ball_subset_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set E) {c : ℝ} (hc : 0 < c) (ρ δ : ℝ) :
    (∃ z ∈ ball (0 : E) (c * ρ), ball z (c * δ) ⊆ c • A) ↔
      ∃ z ∈ ball (0 : E) ρ, ball z δ ⊆ A := by
  have hn : c ≠ 0 := ne_of_gt hc
  have hb (z : E) (r : ℝ) : c • ball z r = ball (c • z) (c * r) := by
    simpa [Real.norm_eq_abs, abs_of_pos hc] using (smul_ball hn z r)
  constructor
  · rintro ⟨z, hz, hsub⟩
    refine ⟨c⁻¹ • z, ?_, ?_⟩
    · have hz' : c • (c⁻¹ • z) ∈ c • ball (0 : E) ρ := by
        simpa [hb, hn] using hz
      exact (Set.smul_mem_smul_set_iff₀ hn _ _).mp hz'
    · apply (Set.smul_set_subset_smul_set_iff₀ hn).mp
      simpa [hb, hn] using hsub
  · rintro ⟨z, hz, hsub⟩
    refine ⟨c • z, ?_, ?_⟩
    · simpa [hb] using (Set.smul_mem_smul_set (a := c) hz)
    · rw [← hb]
      exact (Set.smul_set_subset_smul_set_iff₀ hn).mpr hsub

/-- Scaling a path scales both rooted first-exit traces. -/
theorem rooted_exit_traces_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ → E) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    ((fun t => c • η t) '' Icc
      (sSup {t : ℝ | t ≤ 0 ∧ c • η t ∉ ball 0 (c * R)}) 0 =
      c • (η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 R}) 0)) ∧
    ((fun t => c • η t) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ c • η t ∉ ball 0 (c * R)}) =
      c • (η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 R}))) := by
  have hn : c ≠ 0 := ne_of_gt hc
  have hb : c • ball (0 : E) R = ball 0 (c * R) := by
    simpa [Real.norm_eq_abs, abs_of_pos hc] using (smul_ball hn (0 : E) R)
  have hm (x : E) : c • x ∈ ball 0 (c * R) ↔ x ∈ ball 0 R := by
    rw [← hb, Set.smul_mem_smul_set_iff₀ hn]
  simp only [hm]
  constructor <;> change ((fun x => c • x) ∘ η) '' _ = _ <;>
    rw [Set.image_comp, Set.image_smul]

/-- Both directional ball witnesses transport under positive dilation and a
root-preserving increasing reparametrization. -/
theorem rooted_exit_ball_witnesses_smul_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ → E) (e : ℝ ≃o ℝ) (he : e 0 = 0) {c : ℝ} (hc : 0 < c)
    (R ρ δ : ℝ) :
    let f := fun t => c • η (e t)
    ((∃ z ∈ ball (0 : E) (c * ρ), ball z (c * δ) ⊆
        f '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f t ∉ ball 0 (c * R)}) 0) ∧
      (∃ z ∈ ball (0 : E) (c * ρ), ball z (c * δ) ⊆
        f '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f t ∉ ball 0 (c * R)}))) ↔
    ((∃ z ∈ ball (0 : E) ρ, ball z δ ⊆
        η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 R}) 0) ∧
      (∃ z ∈ ball (0 : E) ρ, ball z δ ⊆
        η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 R}))) := by
  dsimp only
  obtain ⟨hl, hr⟩ := rooted_exit_traces_comp_orderIso (fun t => c • η t)
    (ball 0 (c * R)) e he
  obtain ⟨hl', hr'⟩ := rooted_exit_traces_smul η hc R
  simp only [Function.comp_apply] at hl hr
  rw [hl, hr, hl', hr', exists_ball_subset_smul_iff _ hc, exists_ball_subset_smul_iff _ hc]

end LatticeProb
