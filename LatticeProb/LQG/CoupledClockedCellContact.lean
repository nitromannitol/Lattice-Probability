import LatticeProb.LQG.CoupledClockedEmbeddingCells

/-! # Geometry of cells under the coupled area clock -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT LatticeProb.CorrelatedBM
open scoped NNReal

namespace LatticeProb

/-- For one positive mesh, the coupled area-clock cells form compact connected
sets with nonempty interior, distinct cells have zero-area overlap, and adjacent
vertices of the common contour graph have intersecting cells. -/
theorem exists_coupled_clocked_cell_contact
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∃ G : Ω → Path2, Measurable G ∧
      ∀ᵐ p ∂P.prod Q, 0 ≤ p.2 → p.2 ≤ 1 →
        let c := CellScaling.JointScalingO.clock γ
          (coneField (X p.1) (coneRadial γ γ (fun u => B u p.1) (fun u => B' u p.1)))
          (η₀ p.1)
        let C : ℤ → Set ℂ := fun j => η p.1 '' Icc
          (c (ε * ((j : ℝ) - 1 + p.2))) (c (ε * ((j : ℝ) + p.2)))
        let w : Path2 := ⟨fun t => G p.1 (t + ε * p.2),
          (G p.1).continuous.comp (by fun_prop)⟩
        ∃ hlf : IsLocallyFinite ε w,
          (∀ j, IsCompact (C j) ∧ IsConnected (C j) ∧ (interior (C j)).Nonempty) ∧
          (∀ i j, i ≠ j → volume (C i ∩ C j) = 0) ∧
          (∀ i j, (MatedCRT.graph ε w hlf).adj.Adj i j → (C i ∩ C j).Nonempty) := by
  obtain ⟨G, hG, _, hevent⟩ := exists_coupled_clocked_embedding_area_cells hC hγ hf ε hε Q hQ
  refine ⟨G, hG, ?_⟩
  filter_upwards [hevent] with p hp
  intro hθ0 hθ1
  obtain ⟨hlf, H, hH⟩ := hp.1 hθ0 hθ1
  refine ⟨hlf, ?_, ?_, ?_⟩
  · intro j
    have hc : IsCompact (H.cell j) ∧ IsConnected (H.cell j) ∧
        (interior (H.cell j)).Nonempty :=
      ⟨H.isCompact_cell j, H.isConnected_cell j, H.interior_cell_nonempty j⟩
    simpa only [hH] using hc
  · intro i j hij
    simpa only [hH] using H.volume_inter_cell i j hij
  · intro i j hij
    simpa only [hH] using H.inter_of_adj i j hij

end LatticeProb
