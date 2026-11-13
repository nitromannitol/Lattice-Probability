/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.MeshFamily at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# The dyadic cellular family, on a full-measure standard-Borel subspace
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The full-measure event on which every dyadic mesh has its curve-cell embedding. -/
def MeshEmbeddingGood (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ω : Ω) : Prop :=
  (∃ h : IsLocallyFinite 1 (bm ω),
    ∃ H : CellularEmbedding (MatedCRT.graph 1 (bm ω) h) 0,
      H.cell = fun x : ℤ => η ω '' Icc ((x : ℝ) - 1) x) ∧
  ∀ k, ∃ h : IsLocallyFinite (CellFamily.mesh k) (bm ω),
    ∃ H : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) (bm ω) h) 0,
      H.cell = fun x : ℤ => η ω '' Icc
        (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)

/-- A measurable subset of the full-measure geometric event, used as the probability space for
the total random-cell family. -/
noncomputable def meshGoodSetData
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    {S : Set Ω // MeasurableSet S ∧ (∀ ω, ω ∈ S → MeshEmbeddingGood D ω) ∧
      ∀ᵐ ω ∂P, ω ∈ S} := by
  classical
  let A : Set Ω := {ω | MeshEmbeddingGood D ω}
  have hA : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [ae_unitCellularEmbedding D, ae_meshCellularEmbeddings D] with ω hunit hmesh
    exact ⟨hunit, hmesh⟩
  have hbad : P Aᶜ = 0 := by
    have hset : {ω | ¬ ω ∈ A} = Aᶜ := by ext ω; simp
    rw [← hset]
    exact ae_iff.mp hA
  let N := Classical.choose (exists_measurable_superset_of_null hbad)
  have hN := Classical.choose_spec (exists_measurable_superset_of_null hbad)
  have hbadN : Aᶜ ⊆ N := hN.1
  have hNmeas : MeasurableSet N := hN.2.1
  have hNzero : P N = 0 := hN.2.2
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · intro ω hω
    have hnotbad : ω ∉ Aᶜ := fun h => hω (hbadN h)
    simpa [A] using hnotbad
  · rw [ae_iff]
    have hset : {ω | ¬ ω ∈ Nᶜ} = N := by ext ω; simp
    rw [hset]
    exact hNzero

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)

end MatedCRTHarmonic.MoTInput
