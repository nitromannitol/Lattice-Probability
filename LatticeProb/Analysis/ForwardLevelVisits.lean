import LatticeProb.Analysis.LocalMinCountable

/-! # Level visits followed by a positive interval above the level -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- If distinct local minima have distinct values, visits to a fixed level that
are followed by a fixed positive interval above that level are countable. -/
theorem countable_forward_level_visits (f : ℝ → ℝ) (v δ : ℝ) (hδ : 0 < δ)
    (hdist : ∀ a b, a ≠ b → IsLocalMin f a → IsLocalMin f b → f a ≠ f b) :
    {x : ℝ | f x = v ∧ ∀ y ∈ Icc x (x + δ), v ≤ f y}.Countable := by
  let A : Set ℝ := {x : ℝ | f x = v ∧ ∀ y ∈ Icc x (x + δ), v ≤ f y}
  have hloc := countable_localMin_of_distinct_values f hdist
  have hiso : {x ∈ A | 𝓝[A ∩ Iio x] x = ⊥}.Countable :=
    countable_setOfPred_isolated_left_within
  have hcover : A ⊆ {x | IsLocalMin f x} ∪ {x ∈ A | 𝓝[A ∩ Iio x] x = ⊥} := by
    intro x hx
    by_cases hmin : IsLocalMin f x
    · exact Or.inl hmin
    · right
      refine ⟨hx, ?_⟩
      have hempty : Ioo (x - δ) (x + δ) ∩ (A ∩ Iio x) = ∅ := by
        apply Set.Subset.antisymm ?_ (empty_subset _)
        intro y hy
        have hxy : y < x := hy.2.2
        have hxs : x < y + δ := by linarith [hy.1.1]
        have hlocal : IsLocalMin f x := by
          apply IsMinOn.isLocalMin _ (Icc_mem_nhds hxy hxs)
          intro z hz
          rw [hx.1]
          exact hy.2.1.2 z hz
        exact (hmin hlocal).elim
      rw [← empty_mem_iff_bot, mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Ioo (x - δ) (x + δ), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      rw [hempty]
  exact (hloc.union hiso).mono hcover

/-- Visits to a fixed level preceded by a fixed positive interval above that
level are countable when distinct local minima have distinct values. -/
theorem countable_backward_level_visits (f : ℝ → ℝ) (v δ : ℝ) (hδ : 0 < δ)
    (hdist : ∀ a b, a ≠ b → IsLocalMin f a → IsLocalMin f b → f a ≠ f b) :
    {x : ℝ | f x = v ∧ ∀ y ∈ Icc (x - δ) x, v ≤ f y}.Countable := by
  let g : ℝ → ℝ := fun x => f (-x)
  have hmin : ∀ a, IsLocalMin g a → IsLocalMin f (-a) := by
    intro a ha
    have ha' : IsLocalMin g (- -a) := by simpa using ha
    have h := ha'.comp_continuous
      (continuous_neg.continuousAt : ContinuousAt (fun x : ℝ => -x) (-a))
    simpa [g, Function.comp_def] using h
  have hdistg : ∀ a b, a ≠ b → IsLocalMin g a → IsLocalMin g b → g a ≠ g b := by
    intro a b hab ha hb
    exact hdist (-a) (-b) (fun h => hab (neg_injective h)) (hmin a ha) (hmin b hb)
  have hc := countable_forward_level_visits g v δ hδ hdistg
  have hp := hc.preimage (neg_injective : Function.Injective (fun x : ℝ => -x))
  apply hp.mono
  intro x hx
  refine ⟨by simpa [g] using hx.1, ?_⟩
  intro y hy
  have hmem : -y ∈ Icc (x - δ) x := by
    constructor <;> linarith [hy.1, hy.2]
  simpa [g] using hx.2 (-y) hmem

end LatticeProb
