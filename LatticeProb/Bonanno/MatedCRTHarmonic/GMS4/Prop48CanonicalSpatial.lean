/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalSpatial at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalRegularity

/-!
# Spatial almost-sure transfer for Proposition 4.8

The source uses an a.s. identity at each fixed centre inside a spatial
integral. For jointly measurable versions, Fubini turns those pointwise
identities into a single a.s. identity for Lebesgue-a.e. centre. This is the
correct strength for the integral in (4.29); it does not claim equality of
events quantified over all centres.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.GMS4.Canonical

/-- A versioned all-centres good event has a measurable good subset with
The same failure outer measure. On that subset, fixed-centre a.s. local
implications hold at Lebesgue-a.e. centre on a single a.s. sample set. -/
theorem prop48_exists_measurable_good_spatial
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Set Ω) (L : Ω → ℂ → Prop)
    (hL : MeasurableSet {p : Ω × ℂ | L p.1 p.2})
    (hfixed : ∀ z : ℂ, ∀ᵐ ω ∂P, ω ∈ G → L ω z) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ G ∧ P Eᶜ = P Gᶜ ∧
      ∀ᵐ ω ∂P, ω ∈ E → ∀ᵐ z ∂volume, L ω z := by
  obtain ⟨M, hGM, hMm, hMeq⟩ := exists_measurable_superset P Gᶜ
  let E : Set Ω := Mᶜ
  have hE : MeasurableSet E := hMm.compl
  have hEG : E ⊆ G := by
    intro ω hω
    by_contra hnot
    exact hω (hGM hnot)
  have hset : MeasurableSet {p : Ω × ℂ | p.1 ∈ E → L p.1 p.2} := by
    have heq : {p : Ω × ℂ | p.1 ∈ E → L p.1 p.2} =
        (M ×ˢ (Set.univ : Set ℂ)) ∪ {p : Ω × ℂ | L p.1 p.2} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, Set.mem_univ,
        and_true, E, Set.mem_compl_iff]
      tauto
    rw [heq]
    exact (hMm.prod MeasurableSet.univ).union hL
  have hpoint : ∀ z : ℂ, ∀ᵐ ω ∂P, ω ∈ E → L ω z := by
    intro z
    filter_upwards [hfixed z] with ω hω hωE
    exact hω (hEG hωE)
  have hspatial : ∀ᵐ ω ∂P, ∀ᵐ z ∂volume, ω ∈ E → L ω z :=
    (Measure.ae_ae_comm hset).2 (Filter.Eventually.of_forall hpoint)
  refine ⟨E, hE, hEG, ?_, ?_⟩
  · simpa only [E, compl_compl] using hMeq
  · filter_upwards [hspatial] with ω hω hωE
    exact hω.mono fun z hz => hz hωE

end MatedCRTHarmonic.GMS4.Canonical

