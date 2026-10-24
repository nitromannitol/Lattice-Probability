import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# The positive epsilon filter

Convergence through epsilon values in `(0,1)` is equivalent to convergence along
all sequences of such values tending to zero.
-/

open Filter Set
open scoped Topology

namespace LatticeProb

/-- The carrier of epsilon values strictly between zero and one. -/
abbrev Eps := {ε : ℝ // ε ∈ Ioo 0 1}

/-- Approach zero through epsilon values strictly between zero and one. -/
def epsFilter : Filter Eps := comap Subtype.val (𝓝[Ioo (0 : ℝ) 1] 0)

/-- The epsilon filter inherits a countable basis from the real neighborhood filter. -/
instance : epsFilter.IsCountablyGenerated := by
  unfold epsFilter
  infer_instance

/-- Positive epsilon values accumulate at zero, so the epsilon filter is nontrivial. -/
instance : epsFilter.NeBot := by
  unfold epsFilter
  have : (𝓝[Ioo (0 : ℝ) 1] 0).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    infer_instance
  exact Filter.comap_coe_neBot_of_le_principal inf_le_right

/-- Convergence to the epsilon filter means convergence of the real values to zero. -/
theorem tendsto_epsFilter_iff {α : Type*} {l : Filter α} {x : α → Eps} :
    Tendsto x l epsFilter ↔ Tendsto (fun a ↦ (x a).val) l (𝓝 0) := by
  rw [epsFilter, tendsto_comap_iff, tendsto_nhdsWithin_iff]
  simp only [Function.comp_def, Eventually.of_forall (fun a ↦ (x a).property), and_true]

/-- A function converges along epsilon precisely when it converges on every null sequence. -/
theorem tendsto_epsFilter_iff_seq {Y : Type*} [TopologicalSpace Y]
    {f : Eps → Y} {y : Y} :
    Tendsto f epsFilter (𝓝 y) ↔ ∀ x : ℕ → Eps,
      Tendsto (fun n ↦ (x n).val) atTop (𝓝 0) → Tendsto (f ∘ x) atTop (𝓝 y) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  simp only [tendsto_epsFilter_iff]

end LatticeProb
