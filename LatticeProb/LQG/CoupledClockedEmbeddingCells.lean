import LatticeProb.LQG.CoupledClockedCellEmbedding
import LatticeProb.LQG.CoupledAreaClockStrictWindows

/-! # Coupled shifted embeddings and area-clock cells -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT LatticeProb.CorrelatedBM
open scoped NNReal

namespace LatticeProb

/-- The reference-clock shifted embedding has precisely the cone-curve cells
between the corresponding signed area-clock endpoints. On the same product-full
event, weak contour-window comparisons imply strict comparisons. -/
theorem exists_coupled_clocked_embedding_area_cells
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∃ G : Ω → Path2, Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, G ω t = bm ω (ψ t)) ∧
        (∀ t, CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t = ψ t) ∧ RouteM.Peanosphere (G ω) (η₀ ω)) ∧
      ∀ᵐ p ∂P.prod Q,
        let c := CellScaling.JointScalingO.clock γ
          (coneField (X p.1) (coneRadial γ γ (fun u => B u p.1) (fun u => B' u p.1)))
          (η₀ p.1)
        (0 ≤ p.2 → p.2 ≤ 1 →
          let w : Path2 := ⟨fun t => G p.1 (t + ε * p.2),
            (G p.1).continuous.comp (by fun_prop)⟩
          ∃ (hlf : IsLocallyFinite ε w)
            (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
            ∀ j : ℤ, H.cell j = η p.1 '' Icc
              (c (ε * ((j : ℝ) - 1 + p.2))) (c (ε * ((j : ℝ) + p.2)))) ∧
        ∀ (k : Fin 2) (i j : ℤ), i + 1 < j →
          let a := ε * ((i : ℝ) - 1 + p.2)
          let b := ε * ((i : ℝ) + p.2)
          let d := ε * ((j : ℝ) - 1 + p.2)
          let e := ε * ((j : ℝ) + p.2)
          let f := fun t => lrCoord k t (bm p.1)
          max (sInf (f '' Icc (c a) (c b))) (sInf (f '' Icc (c d) (c e))) ≤
            sInf (f '' Icc (c b) (c d)) →
          max (sInf (f '' Icc (c a) (c b))) (sInf (f '' Icc (c d) (c e))) <
            sInf (f '' Icc (c b) (c d)) := by
  obtain ⟨G, hG, hclock, hemb⟩ :=
    exists_coupled_clocked_cellularEmbedding hC hγ hf ε hε Q hQ
  refine ⟨G, hG, hclock, ?_⟩
  filter_upwards [hemb, ae_prod_coupled_area_clock_strict_windows hC hγ hf ε hε Q hQ] with p hemb hwin
  obtain ⟨hcells, hstrict⟩ := hwin
  refine ⟨?_, hstrict⟩
  intro hθ0 hθ1
  obtain ⟨hlf, H, hH⟩ := hemb hθ0 hθ1
  refine ⟨hlf, H, ?_⟩
  intro j
  rw [hH, ← hcells j, coe_shiftedCompactCell]
  have hle : ε * ((j : ℝ) - 1 + p.2) ≤ ε * ((j : ℝ) + p.2) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  rw [uIcc_of_le hle]
  ext z
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t + ε * p.2, ⟨?_, ?_⟩, rfl⟩ <;> nlinarith
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t - ε * p.2, ⟨?_, ?_⟩, ?_⟩
    · nlinarith
    · nlinarith
    · congr 1; ring

end LatticeProb
