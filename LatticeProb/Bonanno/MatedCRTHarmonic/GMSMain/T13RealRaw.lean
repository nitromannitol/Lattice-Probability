/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13RealRaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13RealMain

/-!
# [18] Theorems 1.3, 1.4 and 3.2 at every real mesh, in the single-embedding raw shape

The named inputs `MainResults.Theorem32Input`, `MainResults.Theorem14GreenInput` (`GMSMain/MainResultsInputs.lean`) use the events
`MainResults.RawEnergyGood`, `MainResults.RawGreenGood`: "`MatedCRT.graph ε b` is locally finite and has A cellular embedding with
the curve cells, and the bound holds for it". The stronger events `T13RealEnergyGood`, `T13RealGreenGood` are stronger (an
embedding exists AND the bound holds for EVERY such embedding). This file restates the real-mesh theorems with the
single-embedding events written out (literally the bodies of the corresponding definitions, without importing them), so that

`MainResults.Theorem32Input` is `fun γ hγ Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D => t13_theorem32_real_raw D hstd hγ`

and likewise `MainResults.Theorem14GreenInput` with `t13_theorem14_green_real_raw`.

* `T13RealEnergyGood.exists_raw`, `T13RealGreenGood.exists_raw` — the strong events imply the single-embedding ones;
* **`t13_theorem32_real_raw`**, **`t13_theorem13_real_raw`**, **`t13_theorem14_green_real_raw`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3
theorem T13RealEnergyGood.exists_raw {ε : ℝ} {b : MatedCRT.Path2} {c : C(ℝ, ℂ)} {Dom : Set ℂ} {f : ℂ → ℝ}
    {A t : ℝ} (h : T13RealEnergyGood ε b c Dom f A t) :
    ∃ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        ∀ fε : ℤ → ℝ, IsGMSDirichletSolution H Dom f fε →
          ENNReal.ofReal (energy (MatedCRT.graph ε b h) (vFin H Dom) fε) ≤
            ENNReal.ofReal A * eucEnergy f Dom + ENNReal.ofReal t := by
  obtain ⟨hlf, H, hcell⟩ := h.1
  exact ⟨hlf, H, hcell, h.2 hlf H hcell⟩

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Theorem 3.2 at every real mesh, single-embedding raw event** (the body of `MainResults.Theorem32RawBody`). -/
theorem t13_theorem32_real_raw (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
      ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ →
        (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier Dom)) ≤ ENNReal.ofReal (C * r)) →
        BoundedConvexityWith C Dom →
        ∀ f : ℂ → ℝ, DifferentiableOn ℝ f Dom →
          (∀ z ∈ Dom, ∀ w ∈ Dom, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
          (∀ z ∈ Dom, |f z| ≤ ε ^ (-β)) → (∀ z ∈ Dom, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
          ContinuousOn f (closure Dom) →
            P {ω | ¬ ∃ (h : MatedCRT.IsLocallyFinite ε (bm ω))
                (H : CellularEmbedding (MatedCRT.graph ε (bm ω) h) 0),
                (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
                  ∀ fε : ℤ → ℝ, IsGMSDirichletSolution H Dom f fε →
                    ENNReal.ofReal (energy (MatedCRT.graph ε (bm ω) h) (vFin H Dom) fε) ≤
                      ENNReal.ofReal A * eucEnergy f Dom + ENNReal.ofReal (ε ^ α)} ≤
              ENNReal.ofReal (Cr * ε ^ α) := by
  obtain ⟨α, hα, β, hβ, h⟩ := t13_theorem32_real D hstd hγ
  refine ⟨α, hα, β, hβ, fun ρ hρ0 hρ1 C hC1 => ?_⟩
  obtain ⟨A, hA, Cr, hCr⟩ := h ρ hρ0 hρ1 C hC1
  refine ⟨A, hA, Cr, fun ε hε hε1 Dom hDo hDsub hbdry hbc f hf hLip hfb hGf hfc => ?_⟩
  refine (measure_mono ?_).trans (hCr ε hε hε1 Dom hDo hDsub hbdry hbc f hf hLip hfb hGf hfc)
  intro ω hω hgood
  exact hω hgood.exists_raw

end Coupling

end MatedCRTHarmonic.GMSMain
