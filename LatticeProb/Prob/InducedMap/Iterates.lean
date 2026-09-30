import LatticeProb.Prob.InducedMap.Ergodicity

/-!
# Iterates of the induced map

The `j`-th iterate of `inducedMap T A` is the `T`-iterate along the Birkhoff sum of the return
time (used by `LatticeProb.Prob.KingmanLinear`); pulling `ae_retTime_pos` back along the
quasi-measure-preserving iterates of `inducedMap T A` shows every iterate lands back in `A` at a
positive return time, for a.e. starting point in `A`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `(inducedMap T A)^[j] x = T^[R] x` where `R` is the Birkhoff sum of `retTime T A` along
`inducedMap T A` up to time `j`. -/
theorem inducedMap_iterate (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) :
    (inducedMap T A)^[j] x = T^[birkhoffSum (inducedMap T A) (retTime T A) j x] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, birkhoffSum_succ, ih, inducedMap,
      ← Function.iterate_add_apply, Nat.add_comm]

/-- For `μ`-a.e. `x ∈ A`, every iterate `(inducedMap T A)^[i] x` has a positive return time,
by pulling `ae_retTime_pos` back along the quasi-measure-preserving iterates of
`inducedMap T A`. -/
theorem inducedMap_ae_retTime_pos {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x) := by
  have h1 : ∀ᵐ x ∂(μ.restrict A), 0 < retTime T A x :=
    (ae_restrict_iff' hA).2 (ae_retTime_pos hT hA)
  have hS : MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) :=
    measurePreserving_inducedMap hT hA
  rw [ae_all_iff]
  intro i
  exact ((hS.iterate i).quasiMeasurePreserving).ae h1

end LatticeProb
