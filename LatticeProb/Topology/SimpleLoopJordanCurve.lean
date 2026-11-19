import LatticeProb.Topology.BoundaryAccessRay
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

/-!
# Simple loops and Jordan curves

Two descriptions of a simple closed curve in the plane agree:

* `IsSimpleLoop Γ`: `Γ` is the image of a continuous injective map from the unit circle `Circle`;
* `LQGMetric.JordanMap.IsJordanCurve Γ`: `Γ` is the image of the circle `sphere 0 1 ⊆ ℂ` under a map
  `ℂ → ℂ` that is continuous and injective on that circle.

`isSimpleLoop_iff_isJordanCurve` is the bridge. With it, the Jordan curve and Schoenflies theorems stated for
`IsJordanCurve` apply to the simple loops produced by Torhorst's theorem: the frontier of each complementary
component of a nondegenerate locally connected plane continuum without cut points is a Jordan curve
(`isJordanCurve_frontier_of_torhorst`).
-/

open Set Metric

namespace LatticeProb.Topology

/-- A plane set is a simple loop (the image of a continuous injective map from `Circle`) iff it is a Jordan curve
(the image of `sphere 0 1` under a map continuous and injective on that circle). -/
theorem isSimpleLoop_iff_isJordanCurve {Γ : Set ℂ} :
    IsSimpleLoop Γ ↔ LQGMetric.JordanMap.IsJordanCurve Γ := by
  classical
  constructor
  · rintro ⟨φ, hφc, hφi, rfl⟩
    let γ : ℂ → ℂ := fun z => if h : z ∈ sphere (0 : ℂ) 1 then φ ⟨z, h⟩ else 0
    have hγ : ∀ z (hz : z ∈ sphere (0 : ℂ) 1), γ z = φ ⟨z, hz⟩ := by
      intro z hz
      simp only [γ]
      split_ifs
      rfl
    refine ⟨γ, ?_, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have hres : (sphere (0 : ℂ) 1).domRestrict γ = fun x : sphere (0 : ℂ) 1 => φ ⟨x, x.2⟩ := by
        funext x
        exact hγ x x.2
      rw [hres]
      exact hφc.comp (continuous_subtype_val.subtype_mk _)
    · intro a ha b hb hab
      rw [hγ a ha, hγ b hb] at hab
      exact congrArg Subtype.val (hφi hab)
    · ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, (hγ z hz).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, z.2, hγ z z.2⟩
  · rintro ⟨γ, hγc, hγi, rfl⟩
    refine ⟨fun z : Circle => γ z, hγc.comp_continuous continuous_subtype_val fun z => z.2,
      fun a b hab => Subtype.ext (hγi a.2 b.2 hab), ?_⟩
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

/-- **Torhorst's theorem, Jordan curve form.** The frontier of every complementary component of a nondegenerate
locally connected continuum `K ⊆ ℂ` without cut points is a Jordan curve. -/
theorem isJordanCurve_frontier_of_torhorst {K : Set ℂ} (hKc : IsCompact K) (hK : IsConnected K)
    (hKn : K.Nontrivial) (hKlc : IsLocallyConnectedSet K) (hcut : ∀ a : ℂ, ¬ IsCutPoint K a)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn Kᶜ) :
    LQGMetric.JordanMap.IsJordanCurve (frontier C) :=
  isSimpleLoop_iff_isJordanCurve.1 (torhorstSimpleLoop K hKc hK hKn hKlc hcut C hC)

end LatticeProb.Topology
