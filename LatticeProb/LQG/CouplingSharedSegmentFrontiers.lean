import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.PushArea
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Topology.AreaCurveSharedFrontier

/-! # Shared segment frontiers of coupled curves -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- On one event, ordered nondegenerate segments of each of the three coupled curves
meet precisely on their shared frontiers. -/
theorem ae_shared_frontiers_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      (ηL ω '' Icc a b ∩ ηL ω '' Icc c d =
        frontier (ηL ω '' Icc a b) ∩ frontier (ηL ω '' Icc c d)) ∧
      (η ω '' Icc a b ∩ η ω '' Icc c d =
        frontier (η ω '' Icc a b) ∩ frontier (η ω '' Icc c d)) ∧
      (η₀ ω '' Icc a b ∩ η₀ ω '' Icc c d =
        frontier (η₀ ω '' Icc a b) ∩ frontier (η₀ ω '' Icc c d)) := by
  filter_upwards [D.spaceFilling, D.areaParam, D.areaParam₀] with ω hs ha ha₀
  obtain ⟨φ, -, hφ⟩ := ha.1
  obtain ⟨ψ, -, hψ⟩ := ha₀.1
  have hp : IsProperMap (ηL ω) := isProperMap_iff_tendsto_cocompact.2
    ⟨(ηL ω).continuous, hs.2.1⟩
  have hm : Measure.map (ηL ω) volume = volume :=
    (MatedCRTHarmonic.GMS4cM.eq_map_volume (ηL ω).continuous hs.1 hs.2.2.2).symm
  have hr : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      ηL ω '' Icc a b ∩ ηL ω '' Icc c d =
        frontier (ηL ω '' Icc a b) ∩ frontier (ηL ω '' Icc c d) := by
    intro a b c d hab hbc hcd
    exact LatticeProb.proper_area_curve_inter_eq_shared_frontier
      (ηL ω) volume (ηL ω).continuous hp hs.1 hm
      (fun a b hab => hs.2.2.2 a b hab.le) hab hbc hcd
  have hi (χ : ℝ ≃o ℝ) (f : C(ℝ, ℂ)) (hf : ∀ t, f t = ηL ω (χ t))
      (a b : ℝ) : f '' Icc a b = ηL ω '' Icc (χ a) (χ b) := by
    rw [show (f : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ χ from funext hf,
      Set.image_comp, χ.image_Icc]
  intro a b c d hab hbc hcd
  refine ⟨hr a b c d hab hbc hcd, ?_, ?_⟩
  · rw [hi φ (η ω) hφ a b, hi φ (η ω) hφ c d]
    exact hr (φ a) (φ b) (φ c) (φ d) (φ.strictMono hab) (φ.monotone hbc)
      (φ.strictMono hcd)
  · rw [hi ψ (η₀ ω) hψ a b, hi ψ (η₀ ω) hψ c d]
    exact hr (ψ a) (ψ b) (ψ c) (ψ d) (ψ.strictMono hab) (ψ.monotone hbc)
      (ψ.strictMono hcd)

end MatedCRTHarmonic.MoTInput
