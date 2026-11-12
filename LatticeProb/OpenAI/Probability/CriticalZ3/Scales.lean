/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalZ3/Scales.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalZ3.Scales in place of OAI.Probability.CriticalZ3.Scales, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.CriticalZ3.Extension (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.CriticalZ3.Conditioning;
   the declarations of the namespace OAI.CriticalZ3 of this file (the law and scale data of a percolation model,
   which need modules not copied here) are omitted, and `_root_.OAI.MeasureTheory`, a namespace of those modules,
   is removed from an `open` command; statements and proofs of the declarations kept are unchanged. -/
import LatticeProb.OpenAI.Probability.CriticalZ3.Conditioning

namespace OAI

open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

noncomputable def contourError : ℝ := (1/100 : ℝ)^7/2

theorem contourError_pos : 0 < contourError := by norm_num [contourError]
theorem contourError_lt_half : contourError < 1/2 := by norm_num [contourError]

theorem contour_power (n : ℕ) :
    (2*contourError)^((n : ℝ)/7) = (1/100 : ℝ)^n := by
  have he : 2*contourError = (1/100 : ℝ)^7 := by unfold contourError; ring
  rw [he,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1/100)]
  have hn : (7 : ℝ)*((n : ℝ)/7) = n := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hn,Real.rpow_natCast]

theorem contour_budget :
    (∑' n : ℕ, 2*(n : ℝ)*3^n*(2*contourError)^((n : ℝ)/7)) < 1 := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(3/100 : ℝ)‖ < 1)).mul_left 2
  have he (n : ℕ) : 2*(n : ℝ)*3^n*(2*contourError)^((n : ℝ)/7) =
      2*((n : ℝ)*(3/100 : ℝ)^n) := by
    rw [contour_power]
    have hb : (3/100 : ℝ)^n = 3^n*(1/100 : ℝ)^n := by rw [←mul_pow]; congr 1; ring
    rw [hb]
    ring
  simp_rw [he]
  rw [h.tsum_eq]
  norm_num

theorem error_budgets {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    ∃ δ η τ γ : ℝ,
      δ ∈ Set.Ioo 0 1 ∧ η ∈ Set.Ioo 0 1 ∧ τ ∈ Set.Ioo 0 1 ∧ γ ∈ Set.Ioo 0 1 ∧
      δ+52*η/δ < f ∧ τ < η/4 ∧ γ < δ ∧ 2*γ/τ < η/4 := by
  let δ := f/2
  let η := δ*f/208
  let τ := η/8
  let γ := min (δ/2) (τ*η/16)
  have hd0 : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ < 1 := by dsimp [δ]; linarith
  have he0 : 0 < η := by dsimp [η]; positivity
  have he1 : η < 1 := by dsimp [η]; nlinarith
  have ht0 : 0 < τ := by dsimp [τ]; positivity
  have ht1 : τ < 1 := by dsimp [τ]; linarith
  have hg0 : 0 < γ := lt_min (by positivity) (by positivity)
  have hgd : γ ≤ δ/2 := min_le_left _ _
  have hge : γ ≤ τ*η/16 := min_le_right _ _
  refine ⟨δ,η,τ,γ,⟨hd0,hd1⟩,⟨he0,he1⟩,⟨ht0,ht1⟩,⟨hg0,by linarith⟩,?_,?_,?_,?_⟩
  · have heq : 52*η/δ = f/4 := by dsimp [η]; field_simp; ring
    rw [heq]
    dsimp [δ]
    linarith
  · dsimp [τ]; linarith
  · linarith
  · apply (div_lt_iff₀ ht0).mpr
    nlinarith

end CriticalScales

end OAI
