import LatticeProb.LQG.HullObservationCollar

/-! # Local hull phases observed from collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Metric TopologicalSpace LQGMetric
open LQGMetric.Blueprint LQGMetric.LocalEvent LQGMetric.CONF SmallGammaGeodesics

namespace LatticeProb.LQG

/-- A unit-integral test supported in every hull has observable phase when the
hulls are contained in the collar. -/
theorem measurable_phase_of_hull_subset_collar {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k n : ℕ) (a : TestC)
    (ha : ∫ z, a z = 1)
    (hsupp : ∀ ω, tsupport (a : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ)))
    (hsub : ∀ ω, dyadicHull n (K ω : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (fun ω => toIcoMod hp 0 (h ω a)) := by
  classical
  let A : Ω → Set ℂ := fun ω => K ω
  let m : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  let : MeasurableSpace Ω := m
  have hset : setSigma A ≤ m := setSigma_le_collarFieldCode h K ψ hp k
  have hE (S : Set ℂ) : MeasurableSet {ω | dyadicHull n (A ω) = S} :=
    hset _ (measurableSet_hull_eq (fun ω => (K ω).isCompact.isClosed) n S)
  intro B hB
  have hpiece (S : Set ℂ) : MeasurableSet
      ({ω | dyadicHull n (A ω) = S} ∩ (fun ω => toIcoMod hp 0 (h ω a)) ⁻¹' B) := by
    by_cases hs : tsupport (a : ℂ → ℝ) ⊆ interior S
    · have hm := measurable_indicator_phase_of_collarFieldCode h K ψ hp k
        ⟨interior S, isOpen_interior⟩ {ω | dyadicHull n (A ω) = S} (hE S)
        (fun ω hω => by
          change dyadicHull n (K ω : Set ℂ) = S at hω
          rw [← hω]
          exact interior_subset.trans (hsub ω)) a hs ha
      have heq : {ω | dyadicHull n (A ω) = S} ∩
          (fun ω => toIcoMod hp 0 (h ω a)) ⁻¹' B =
          {ω | dyadicHull n (A ω) = S} ∩
          ({ω | dyadicHull n (A ω) = S}.indicator
            (fun ω => toIcoMod hp 0 (h ω a))) ⁻¹' B := by
        ext ω
        simp only [mem_inter_iff, mem_preimage]
        constructor <;> rintro ⟨hω, hωB⟩
        · exact ⟨hω, by simpa only [indicator_of_mem hω] using hωB⟩
        · exact ⟨hω, by simpa only [indicator_of_mem hω] using hωB⟩
      rw [heq]
      exact (hE S).inter (hm hB)
    · have hempty : {ω | dyadicHull n (A ω) = S} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro ω hω
        apply hs
        change dyadicHull n (K ω : Set ℂ) = S at hω
        rw [← hω]
        exact hsupp ω
      rw [hempty, empty_inter]
      exact MeasurableSet.empty
  have heq : (fun ω => toIcoMod hp 0 (h ω a)) ⁻¹' B =
      ⋃ S ∈ conf36HullShapes n,
        ({ω | dyadicHull n (A ω) = S} ∩ (fun ω => toIcoMod hp 0 (h ω a)) ⁻¹' B) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    constructor
    · intro hω
      exact ⟨_, conf36_hull_mem_shapes (Or.inl (K ω).isCompact.isBounded) n, rfl, hω⟩
    · rintro ⟨S, hS, hEq, hω⟩
      exact hω
  rw [heq]
  exact MeasurableSet.biUnion (conf36HullShapes_countable n) (fun S _ => hpiece S)

/-- The local hull field sigma-field is contained in the collar code when a
unit-integral anchor is supported in every hull and the hulls fit in the collar. -/
theorem localHullFieldSigma_le_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k n : ℕ) (a : TestC)
    (ha : ∫ z, a z = 1)
    (hsupp : ∀ ω, tsupport (a : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ)))
    (hsub : ∀ ω, dyadicHull n (K ω : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n a hp ≤
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance := by
  apply sup_le (hullSigma0_le_collarFieldCode h K ψ hp k n hsub)
  apply Measurable.comap_le
  have hm := measurable_phase_of_hull_subset_collar h K ψ hp k n a ha hsupp hsub
  convert hm using 1
  funext ω
  exact indicator_of_mem (hsupp ω) _

end LatticeProb.LQG
