import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.PushArea
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Topology.AreaCurveRegularClosed

/-! # Regular closed segments of coupled curves -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- All nondegenerate segments of the Lebesgue and the two area-parametrized
curves of a coupling are regular closed on one common event. -/
theorem ae_regularClosed_segments_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      closure (interior (ηL ω '' Icc a b)) = ηL ω '' Icc a b ∧
      closure (interior (η ω '' Icc a b)) = η ω '' Icc a b ∧
      closure (interior (η₀ ω '' Icc a b)) = η₀ ω '' Icc a b := by
  filter_upwards [D.spaceFilling, D.areaParam, D.areaParam₀] with ω hs ha ha₀
  obtain ⟨φ, -, hφ⟩ := ha.1
  obtain ⟨ψ, -, hψ⟩ := ha₀.1
  have hp : IsProperMap (ηL ω) := isProperMap_iff_tendsto_cocompact.2
    ⟨(ηL ω).continuous, hs.2.1⟩
  have hm : Measure.map (ηL ω) volume = volume :=
    (MatedCRTHarmonic.GMS4cM.eq_map_volume (ηL ω).continuous hs.1 hs.2.2.2).symm
  have hr : ∀ a b : ℝ, a < b →
      closure (interior (ηL ω '' Icc a b)) = ηL ω '' Icc a b := by
    intro a b hab
    exact LatticeProb.closure_interior_image_Icc_of_proper_area_curve
      (ηL ω) volume (ηL ω).continuous hp hs.1 hm
      (fun a b hab => hs.2.2.2 a b hab.le) hab
  have hi (χ : ℝ ≃o ℝ) (f : C(ℝ, ℂ)) (hf : ∀ t, f t = ηL ω (χ t))
      (a b : ℝ) : f '' Icc a b = ηL ω '' Icc (χ a) (χ b) := by
    rw [show (f : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ χ from funext hf,
      Set.image_comp, χ.image_Icc]
  intro a b hab
  refine ⟨hr a b hab, ?_, ?_⟩
  · rw [hi φ (η ω) hφ a b]
    exact hr (φ a) (φ b) (φ.strictMono hab)
  · rw [hi ψ (η₀ ω) hψ a b]
    exact hr (ψ a) (ψ b) (ψ.strictMono hab)

end MatedCRTHarmonic.MoTInput
