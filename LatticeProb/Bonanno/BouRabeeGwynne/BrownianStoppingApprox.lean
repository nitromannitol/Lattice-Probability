/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppingApprox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DyadicExitApprox
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Explicit finite dyadic approximations of bounded stopping times

These are concrete ceiling approximations. The finite range is the image of
an explicitly bounded set of natural numbers, and convergence follows from
the checked upper-approximation inequalities.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

noncomputable def dyadicStoppingTime {Ω : Type*} (σ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ / (2 : ℝ≥0) ^ n

lemma nnrealApproxSeq_coe_eq_dyadicStoppingTime {Ω : Type*}
    (σ : Ω → ℝ≥0) (n : ℕ) :
    nnrealApproxSeq (fun ω ↦ (σ ω : WithTop ℝ≥0)) n =
      fun ω ↦ (dyadicStoppingTime σ n ω : WithTop ℝ≥0) := rfl

lemma isStoppingTime_dyadicStoppingTime {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime F (fun ω ↦ (σ ω : ℝ≥0∞))) (n : ℕ) :
    IsStoppingTime F (fun ω ↦ (dyadicStoppingTime σ n ω : ℝ≥0∞)) := by
  change IsStoppingTime F (fun ω ↦ (dyadicStoppingTime σ n ω : WithTop ℝ≥0))
  rw [← nnrealApproxSeq_coe_eq_dyadicStoppingTime]
  exact nnrealApproxSeq_isStoppingTime F hσ n

lemma le_dyadicStoppingTime {Ω : Type*} (σ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    σ ω ≤ dyadicStoppingTime σ n ω := by
  have h := nnrealApproxSeq_le (fun ω ↦ (σ ω : WithTop ℝ≥0)) n ω
  rw [nnrealApproxSeq_coe_eq_dyadicStoppingTime] at h
  exact WithTop.coe_le_coe.mp h

lemma tendsto_dyadicStoppingTime {Ω : Type*} (σ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ dyadicStoppingTime σ n ω) atTop (𝓝 (σ ω)) := by
  have h := nnrealApproxSeq_tendsto (fun ω ↦ (σ ω : WithTop ℝ≥0)) ω
  simp only [nnrealApproxSeq_coe_eq_dyadicStoppingTime] at h
  have h' : Tendsto (fun n ↦ (dyadicStoppingTime σ n ω : ℝ≥0∞))
      atTop (𝓝 (σ ω : ℝ≥0∞)) := h
  simpa only [Function.comp_def, ENNReal.toNNReal_coe] using
    (ENNReal.tendsto_toNNReal ENNReal.coe_ne_top).comp h'

noncomputable def dyadicStoppingRange (N : ℝ≥0) (n : ℕ) : Finset ℝ≥0 := by
  classical
  exact (Finset.range (⌈N * (2 : ℝ≥0) ^ n⌉₊ + 1)).image
    (fun k : ℕ ↦ (k : ℝ≥0) / (2 : ℝ≥0) ^ n)

lemma dyadicStoppingTime_mem_range {Ω : Type*} {σ : Ω → ℝ≥0} {N : ℝ≥0}
    (hN : ∀ ω, σ ω ≤ N) (n : ℕ) (ω : Ω) :
    dyadicStoppingTime σ n ω ∈ dyadicStoppingRange N n := by
  classical
  refine Finset.mem_image.mpr ⟨⌈σ ω * (2 : ℝ≥0) ^ n⌉₊, ?_, rfl⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.ceil_mono (mul_le_mul_of_nonneg_right (hN ω) (by positivity)))

end BouRabeeGwynne
