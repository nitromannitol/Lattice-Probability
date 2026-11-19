import LatticeProb.Topology.BoundaryAccessRay
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Schoenflies.Disc

/-!
# Simple loops and Jordan curves

Two descriptions of a simple closed curve in the plane agree:

* `IsSimpleLoop Γ`: `Γ` is the image of a continuous injective map from the unit circle `Circle`;
* `LQGMetric.JordanMap.IsJordanCurve Γ`: `Γ` is the image of the circle `sphere 0 1 ⊆ ℂ` under a map
  `ℂ → ℂ` that is continuous and injective on that circle.

`isSimpleLoop_iff_isJordanCurve` is the bridge. With it, the Jordan curve and Schoenflies theorems stated for
`IsJordanCurve` apply to the simple loops produced by Torhorst's theorem: the frontier of each complementary
component of a nondegenerate locally connected plane continuum without cut points is a Jordan curve
(`isJordanCurve_frontier_of_torhorst`). Combined with the Jordan curve and Schoenflies theorems this gives a
characterization of the closed disk: a nondegenerate locally connected plane continuum without cut points whose
complement is connected is homeomorphic to the closed unit disk (`nonempty_homeomorph_closedBall_of_torhorst`).
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

/-- **Closed disk characterization.** A nondegenerate locally connected continuum `K ⊆ ℂ` without cut points whose
complement is connected is homeomorphic to the closed unit disk. By Torhorst's theorem the frontier `J` of `K` is a
Jordan curve; `ℂ \ K` is the unbounded complementary domain of `J`, so `K` is the closure of the bounded one, a
closed disk by the Schoenflies theorem. -/
theorem nonempty_homeomorph_closedBall_of_torhorst {K : Set ℂ} (hKc : IsCompact K) (hK : IsConnected K)
    (hKn : K.Nontrivial) (hKlc : IsLocallyConnectedSet K) (hcut : ∀ a : ℂ, ¬ IsCutPoint K a)
    (hKcc : IsPreconnected Kᶜ) : Nonempty (closedBall (0 : ℂ) 1 ≃ₜ K) := by
  have hKcl : IsClosed K := hKc.isClosed
  have hKb : Bornology.IsBounded K := hKc.isBounded
  have hKcu : ¬ Bornology.IsBounded Kᶜ := fun h =>
    NormedSpace.unbounded_univ ℝ ℂ (by rw [← union_compl_self K]; exact hKb.union h)
  obtain ⟨q, hq⟩ : Kᶜ.Nonempty :=
    nonempty_iff_ne_empty.2 fun h => hKcu (h ▸ Bornology.isBounded_empty)
  have hC : connectedComponentIn Kᶜ q ∈ connectedComponentsIn Kᶜ := ⟨q, hq, rfl⟩
  have hJ := isJordanCurve_frontier_of_torhorst hKc hK hKn hKlc hcut hC
  rw [hKcc.connectedComponentIn hq, frontier_compl] at hJ
  have hJK : frontier K ⊆ K := hKcl.frontier_subset
  obtain ⟨x₁, hx₁, x₀, -, hb₁, hu₀, hd, hun, hf₁, -⟩ :=
    MatedCRTHarmonic.Planar.Jordan.jordan_curve_components_complex hJ
  set U := connectedComponentIn (frontier K)ᶜ x₁ with hU
  set V := connectedComponentIn (frontier K)ᶜ x₀ with hV
  have hJo : IsOpen (frontier K)ᶜ := isClosed_frontier.isOpen_compl
  have hKV : Kᶜ ⊆ V := by
    have hsub : Kᶜ ⊆ U ∪ V := by
      rw [← hun]
      exact compl_subset_compl.2 hJK
    rcases hKcc.subset_or_subset hJo.connectedComponentIn hJo.connectedComponentIn hd hsub with h | h
    · exact absurd (hb₁.subset h) hKcu
    · exact h
  have hVK : V ⊆ Kᶜ := by
    have hsub : V ⊆ interior K ∪ Kᶜ := by
      intro z hz
      have hzJ : z ∉ frontier K := connectedComponentIn_subset _ _ hz
      by_cases hzK : z ∈ K
      · left
        by_contra hzi
        exact hzJ ⟨subset_closure hzK, hzi⟩
      · exact Or.inr hzK
    rcases (isPreconnected_connectedComponentIn : IsPreconnected V).subset_or_subset isOpen_interior
        hKcl.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hsub with h | h
    · exact absurd (hKb.subset (h.trans interior_subset)) hu₀
    · exact h
  have hKU : K = closure U := by
    rw [closure_eq_self_union_frontier, hf₁]
    apply Subset.antisymm
    · intro z hzK
      by_cases hzJ : z ∈ frontier K
      · exact Or.inr hzJ
      · have hz : z ∈ U ∪ V := by
          rw [← hun]
          exact hzJ
        rcases hz with h | h
        · exact Or.inl h
        · exact absurd hzK (hVK h)
    · rintro z (hz | hz)
      · by_contra hzK
        exact disjoint_left.1 hd hz (hKV hzK)
      · exact hJK hz
  obtain ⟨e, -, -⟩ := MatedCRTHarmonic.Planar.Schoenflies.schoenflies_closedDisc hJ hx₁ hb₁
  exact ⟨e.trans (Homeomorph.setCongr hKU.symm)⟩

end LatticeProb.Topology
