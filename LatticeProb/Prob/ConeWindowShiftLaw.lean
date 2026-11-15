import LatticeProb.Prob.ConeWindowShift
import LatticeProb.Prob.ConeWindowFixedTime

/-! # Equal-law shifts of cone-window coverage -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Equality in law of a shifted path pair transfers almost-sure cone-window
coverage. Coordinate offsets may depend on the sample. -/
theorem ae_coneWindowCoverage_shift_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z Y : Ω → C(ℝ, ℝ) × C(ℝ, ℝ)) (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : P.map Y = P.map Z) (l r t d : ℝ)
    (hpaths : ∀ᵐ ω ∂P, ∃ c₁ c₂ : ℝ,
      (∀ s, (Z ω).1 (s + d) = (Y ω).1 s + c₁) ∧
      (∀ s, (Z ω).2 (s + d) = (Y ω).2 s + c₂))
    (h : ∀ᵐ ω ∂P, (Z ω, t) ∈ Prod.fst '' coneWindowWitness l r) :
    ∀ᵐ ω ∂P, (Z ω, t + d) ∈ Prod.fst '' coneWindowWitness (l + d) (r + d) := by
  let E : Set (C(ℝ, ℝ) × C(ℝ, ℝ)) :=
    {z | (z, t) ∈ Prod.fst '' coneWindowWitness l r}
  have : IsFiniteMeasure (P.map Z) := P.isFiniteMeasure_map Z
  have hE : NullMeasurableSet E (P.map Z) := by
    exact nullMeasurableSet_preimage_coneWindowCoverage (P.map Z)
      (fun z => (z, t)) (measurable_id.prodMk measurable_const) l r
  obtain ⟨F, hFE, hFm, hFae⟩ := hE.exists_measurable_subset_ae_eq
  have hFZ : ∀ᵐ ω ∂P, Z ω ∈ F := by
    have hEq : ∀ᵐ ω ∂P, (Z ω ∈ F ↔ Z ω ∈ E) :=
      (Measure.tendsto_ae_map hZ.aemeasurable).eventually hFae.mem_iff
    filter_upwards [hEq, h] with ω he hh
    exact he.mpr hh
  have hFY : ∀ᵐ ω ∂P, Y ω ∈ F := by
    have hF : ∀ᵐ z ∂P.map Z, z ∈ F := (ae_map_iff hZ.aemeasurable hFm).2 hFZ
    rw [← hlaw] at hF
    exact (ae_map_iff hY.aemeasurable hFm).1 hF
  filter_upwards [hFY, hpaths] with ω hf ⟨c₁, c₂, h₁, h₂⟩
  exact (mem_coneWindowCoverage_shift_iff (Y ω) (Z ω) l r t d c₁ c₂ h₁ h₂).2
    (hFE hf)

/-- Almost-every-time coverage yields fixed-time coverage when every shifted
path pair has the same law and has the stated pathwise translation relation. -/
theorem ae_coneWindowCoverage_fixedTime_of_shift_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → C(ℝ, ℝ) × C(ℝ, ℝ)) (hZ : Measurable Z)
    (Y : ℝ → Ω → C(ℝ, ℝ) × C(ℝ, ℝ))
    (hY : ∀ d, Measurable (Y d)) (hlaw : ∀ d, P.map (Y d) = P.map Z)
    (hpaths : ∀ d, ∀ᵐ ω ∂P, ∃ c₁ c₂ : ℝ,
      (∀ s, (Z ω).1 (s + d) = (Y d ω).1 s + c₁) ∧
      (∀ s, (Z ω).2 (s + d) = (Y d ω).2 s + c₂))
    (hcoverage : ∀ l r : ℝ, l < r → ∀ᵐ ω ∂P,
      ∀ᵐ t ∂volume.restrict (Ioo l r), (Z ω, t) ∈ Prod.fst '' coneWindowWitness l r)
    {a u b : ℝ} (hau : a < u) (hub : u < b) :
    ∀ᵐ ω ∂P, (Z ω, u) ∈ Prod.fst '' coneWindowWitness a b := by
  apply ae_coneWindowCoverage_fixedTime P Z hZ hcoverage
  · intro l r t d h
    exact ae_coneWindowCoverage_shift_of_map_eq P Z (Y d) hZ (hY d) (hlaw d)
      l r t d (hpaths d) h
  · exact hau
  · exact hub

end LatticeProb
