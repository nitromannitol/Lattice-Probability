import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqKer

/-! # Translation and local comparison of killed heat kernels -/

set_option autoImplicit false

open Set
open scoped NNReal
open LQGMetric.HeatSq

namespace LQGMetric.KilledHeat

/-- Translating a domain and both endpoints leaves the bridge survival probability unchanged. -/
theorem bridgeStay_translate (A : Set ℂ) (t : ℝ≥0) (c z w : ℂ) :
    bridgeStay {v | v - c ∈ A} t (z + c) (w + c) = bridgeStay A t z w := by
  unfold bridgeStay
  congr 2
  ext ω
  simp only [bridgeEvent, bridgePath, Set.mem_ofPred_eq]
  refine forall₂_congr fun s _ => ?_
  have heq : (z + c) + (((s : ℝ) / t : ℝ) : ℂ) * ((w + c) - (z + c)) +
      stdBridge t s ω - c = z + (((s : ℝ) / t : ℝ) : ℂ) * (w - z) +
      stdBridge t s ω := by ring
  rw [heq]

/-- Translating a domain and both endpoints leaves its killed heat kernel unchanged. -/
theorem killedHeat_translate (A : Set ℂ) (t : ℝ≥0) (c z w : ℂ) :
    killedHeat {v | v - c ∈ A} t (z + c) (w + c) = killedHeat A t z w := by
  rw [killedHeat, bridgeStay_translate, killedHeat]
  congr 1
  simp only [LQGMetric.heatKernel, add_sub_add_right_eq_sub]

/-- An explicit square Dirichlet kernel bounds the killed kernel of any containing domain. -/
theorem sqDirKernel_le_killedHeat_of_translate_subset {a L : ℝ} (hL : 0 < L)
    {t : ℝ≥0} (ht : t ≠ 0) (c z w : ℂ) (hz : z ∈ sqOpen a L)
    (hw : w ∈ sqOpen a L) {U : Set ℂ} (hU : {v | v - c ∈ sqOpen a L} ⊆ U) :
    sqDirKernel a L t z w ≤ killedHeat U t (z + c) (w + c) := by
  rw [← LQGMetric.KilledHeatSq.killedHeat_sqOpen hL t ht z w hz hw,
    ← killedHeat_translate (sqOpen a L) t c z w]
  exact killedHeat_mono hU t (z + c) (w + c)

end LQGMetric.KilledHeat
