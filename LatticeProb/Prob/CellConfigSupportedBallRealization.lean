import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Measurable realizations from cell configuration ball tests -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open ReflectedGMS.GMS

namespace LatticeProb

/-- A configuration-valued map has a measurable version if its values on a
measurable conull set lie in a second-countable family and all generating
cell-configuration ball tests are measurable on that set. -/
theorem exists_measurable_ae_eq_of_cellConfig_ball_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (H : Ω → GMSSpace)
    (A : Set Ω) (hA : MeasurableSet A) (hfull : ∀ᵐ ω ∂μ, ω ∈ A)
    (T : Set GMSSpace) [SecondCountableTopology T] (H₀ : T)
    (hT : ∀ ω ∈ A, H ω ∈ T)
    (hball : ∀ (K : GMSSpace) (ε : ℝ≥0∞), 0 < ε →
      MeasurableSet (A ∩ {ω | CellConfig.dCC K.1 (H ω).1 < ε})) :
    ∃ F : Ω → GMSSpace, Measurable F ∧ F =ᵐ[μ] H := by
  classical
  let G : Ω → T := fun ω => if h : ω ∈ A then ⟨H ω, hT ω h⟩ else H₀
  let S : Set (Set GMSSpace) := {U | ∃ (K : GMSSpace) (ε : ℝ≥0∞),
    0 < ε ∧ U = {K' | CellConfig.dCC K.1 K'.1 < ε}}
  have htop : (inferInstance : TopologicalSpace T) =
      TopologicalSpace.generateFrom ((fun U : Set GMSSpace => (Subtype.val : T → GMSSpace) ⁻¹' U) '' S) := by
    change TopologicalSpace.induced Subtype.val (TopologicalSpace.generateFrom S) = _
    exact induced_generateFrom_eq
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  have hG : Measurable G := by
    have hgen : (borel T) = MeasurableSpace.generateFrom
        ((fun U : Set GMSSpace => (Subtype.val : T → GMSSpace) ⁻¹' U) '' S) :=
      borel_eq_generateFrom_of_subbasis htop
    refine (measurable_generateFrom ?_).mono le_rfl hgen.le
    rintro _ ⟨U, ⟨K, ε, hε, rfl⟩, rfl⟩
    by_cases h₀ : CellConfig.dCC K.1 H₀.1.1 < ε
    · have heq : G ⁻¹' (Subtype.val ⁻¹' {K' : GMSSpace | CellConfig.dCC K.1 K'.1 < ε}) =
          (A ∩ {ω | CellConfig.dCC K.1 (H ω).1 < ε}) ∪ Aᶜ := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [G, hω, h₀]
      rw [heq]
      exact (hball K ε hε).union hA.compl
    · have heq : G ⁻¹' (Subtype.val ⁻¹' {K' : GMSSpace | CellConfig.dCC K.1 K'.1 < ε}) =
          A ∩ {ω | CellConfig.dCC K.1 (H ω).1 < ε} := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [G, hω, h₀]
      rw [heq]
      exact hball K ε hε
  refine ⟨fun ω => (G ω).1, ?_, ?_⟩
  · exact continuous_subtype_val.measurable.comp hG
  · filter_upwards [hfull] with ω hω
    simp [G, hω]

end LatticeProb
