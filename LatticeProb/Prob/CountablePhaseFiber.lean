import LatticeProb.Prob.CountablePhaseMap
import Mathlib.MeasureTheory.Measure.Restrict

/-! Fixed-count fibers of measures on a countable phase space. -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The inclusion of a fixed coordinate count is a measurable embedding. -/
theorem measurableEmbedding_countablePhase_inject {E : Type*} [MeasurableSpace E] (n : ℕ) :
    MeasurableEmbedding (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) where
  injective := sigma_mk_injective
  measurable := by
    intro s hs
    change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
      (Sigma.mk i)] s at hs
    exact (MeasurableSpace.measurableSet_iInf.mp hs) n
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
      (Sigma.mk i)] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro i
    change MeasurableSet ((@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) i) ⁻¹'
      ((@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) '' s))
    by_cases h : i = n
    · subst i
      simpa only [sigma_mk_injective.preimage_image] using hs
    · have he : (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) i) ⁻¹'
          ((@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) '' s) = ∅ := by
        ext x
        simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false]
        rintro ⟨y, _, hy⟩
        exact h (congrArg Sigma.fst hy).symm
      rw [he]
      exact MeasurableSet.empty

/-- Fixed-count vectors and the corresponding count fiber are measurably equivalent. -/
noncomputable def countablePhaseFiberEquiv (E : Type*) [MeasurableSpace E] (n : ℕ) :
    (E × (Fin n → ℝ)) ≃ᵐ
      range (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) :=
  (measurableEmbedding_countablePhase_inject (E := E) n).equivRange

/-- A measure restricted to a count fiber is the pushforward of its comap. -/
theorem countablePhase_map_comap (E : Type*) [MeasurableSpace E]
    (μ : Measure (CountablePhaseSpace E)) (n : ℕ) :
    (μ.comap (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)).map
        (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) =
      μ.restrict {x | x.1 = n} := by
  rw [(measurableEmbedding_countablePhase_inject (E := E) n).map_comap]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    cases x with
    | mk i y =>
      change i = n at hx
      subst i
      exact ⟨y, rfl⟩

end LatticeProb
