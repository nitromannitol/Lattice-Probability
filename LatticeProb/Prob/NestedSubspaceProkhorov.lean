import LatticeProb.Prob.LevyProkhorovIsometricEmbedding

/-! # Lévy–Prokhorov distance on nested measurable subspaces -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Inclusion of one measurable subspace into another preserves the extended
Lévy–Prokhorov distance for their inherited metrics. -/
theorem levyProkhorovEDist_map_nestedSubtype
    {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T)
    (μ ν : Measure S) :
    levyProkhorovEDist (μ.map (fun x : S => (⟨x.1, hST x.2⟩ : T)))
        (ν.map (fun x : S => (⟨x.1, hST x.2⟩ : T))) = levyProkhorovEDist μ ν := by
  let i : S → T := fun x => ⟨x.1, hST x.2⟩
  have hi : Measurable i := measurable_subtype_coe.subtype_mk
  have hTcoe : Measurable ((↑) : T → X) := measurable_subtype_coe
  have houter := levyProkhorovEDist_map_eq_of_isometry
    (isometry_subtype_coe : Isometry ((↑) : T → X)) (MeasurableEmbedding.subtype_coe hT)
    (μ.map i) (ν.map i)
  have hinner := levyProkhorovEDist_map_eq_of_isometry
    (isometry_subtype_coe : Isometry ((↑) : S → X)) (MeasurableEmbedding.subtype_coe hS) μ ν
  rw [Measure.map_map hTcoe hi, Measure.map_map hTcoe hi] at houter
  exact houter.symm.trans hinner

/-- The real-valued Lévy–Prokhorov distance is preserved by a nested subspace inclusion. -/
theorem levyProkhorovDist_map_nestedSubtype
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T)
    (μ ν : Measure S) :
    levyProkhorovDist (μ.map (fun x : S => (⟨x.1, hST x.2⟩ : T)))
        (ν.map (fun x : S => (⟨x.1, hST x.2⟩ : T))) = levyProkhorovDist μ ν := by
  unfold levyProkhorovDist
  rw [levyProkhorovEDist_map_nestedSubtype hS hT hST]

end LatticeProb
