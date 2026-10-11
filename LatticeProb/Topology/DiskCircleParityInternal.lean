/-
# Parity on complementary original circle intervals

If a finite closed edge chain meets the unit circle only at the first and
third boundary points, its parity is constant on each of the two complementary
angular intervals. Continuity of `(cos θ, sin θ)` supplies preconnected arc
images, while strict angular windows exclude both endpoint points, including
the wraparound interval. An actual finite disk crosscut and its produced outside
completion supply the circle-incidence prerequisite in the consumer below.

The complementary interval constants are obtained from continuity and
preconnectedness of the corresponding circle images.
-/
import LatticeProb.Topology.DiskCrosscutParityInternal



open Set
namespace LatticeProb.Topology.PolygonalParity

/-- Circle parity is constant on an angular interval whose actual circle
image avoids the closed edge chain. This is local constancy consumed on a
preconnected continuous image, with no assumption about a side label. -/
theorem parity_eq_on_circle_interval {u : Plane} {L : List Piece}
    (hu : Plane.IsDirection u) (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {α β : ℝ}
    (havoid : ∀ θ ∈ Ioo α β, coordinateEquiv (Real.cos θ, Real.sin θ) ∉ cover L)
    {θ φ : ℝ} (hθ : θ ∈ Ioo α β) (hφ : φ ∈ Ioo α β) :
    parity u L (coordinateEquiv (Real.cos θ, Real.sin θ)) =
      parity u L (coordinateEquiv (Real.cos φ, Real.sin φ)) := by
  have hcontinuous : Continuous (fun t : ℝ => coordinateEquiv (Real.cos t, Real.sin t)) :=
    continuous_coordinateEquiv.comp (Real.continuous_cos.prodMk Real.continuous_sin)
  exact parity_eq_of_isPreconnected hu hL hC
    (isPreconnected_Ioo.image _ hcontinuous.continuousOn)
    (by rintro _ ⟨t, ht, rfl⟩; exact havoid t ht)
    ⟨θ, hθ, rfl⟩ ⟨φ, hφ, rfl⟩

/-- Exact circle incidence at two endpoints implies parity constancy on each
complementary original angle interval. The final interval retains the literal
wraparound endpoint `θ₁ + 2π`. -/
theorem parity_constant_on_complementary_circle_intervals_internal
    (θ₁ θ₃ : ℝ) (h13 : θ₁ < θ₃) (h31 : θ₃ < θ₁ + 2 * Real.pi)
    {u : Plane} {L : List Piece} (hu : Plane.IsDirection u)
    (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    (hcircle : ∀ θ : ℝ, coordinateEquiv (Real.cos θ, Real.sin θ) ∈ cover L →
      (Real.cos θ, Real.sin θ) = (Real.cos θ₁, Real.sin θ₁) ∨
      (Real.cos θ, Real.sin θ) = (Real.cos θ₃, Real.sin θ₃)) :
    (∀ θ ∈ Ioo θ₁ θ₃, ∀ φ ∈ Ioo θ₁ θ₃,
      parity u L (coordinateEquiv (Real.cos θ, Real.sin θ)) =
        parity u L (coordinateEquiv (Real.cos φ, Real.sin φ))) ∧
    (∀ θ ∈ Ioo θ₃ (θ₁ + 2 * Real.pi), ∀ φ ∈ Ioo θ₃ (θ₁ + 2 * Real.pi),
      parity u L (coordinateEquiv (Real.cos θ, Real.sin θ)) =
        parity u L (coordinateEquiv (Real.cos φ, Real.sin φ))) := by
  have hfirst : ∀ θ ∈ Ioo θ₁ θ₃,
      coordinateEquiv (Real.cos θ, Real.sin θ) ∉ cover L := by
    intro θ hθ hmem
    rcases hcircle θ hmem with heq | heq
    · exact (circle_point_ne_of_lt_lt_add_two_pi hθ.1 (hθ.2.trans h31)) heq.symm
    · have hbound : θ₃ < θ + 2 * Real.pi :=
        h31.trans (by simpa only [add_comm] using add_lt_add_right hθ.1 (2 * Real.pi))
      exact (circle_point_ne_of_lt_lt_add_two_pi hθ.2 hbound) heq
  have hsecond : ∀ θ ∈ Ioo θ₃ (θ₁ + 2 * Real.pi),
      coordinateEquiv (Real.cos θ, Real.sin θ) ∉ cover L := by
    intro θ hθ hmem
    rcases hcircle θ hmem with heq | heq
    · exact (circle_point_ne_of_lt_lt_add_two_pi (h13.trans hθ.1) hθ.2) heq.symm
    · have hbound : θ < θ₃ + 2 * Real.pi :=
        hθ.2.trans (by simpa only [add_comm] using add_lt_add_right h13 (2 * Real.pi))
      exact (circle_point_ne_of_lt_lt_add_two_pi hθ.1 hbound) heq.symm
  exact ⟨fun _ hθ _ hφ => parity_eq_on_circle_interval hu hL hC hfirst hθ hφ,
    fun _ hθ _ hφ => parity_eq_on_circle_interval hu hL hC hsecond hθ hφ⟩

/-- **Complementary original circle interval consumer (internal).** An actual
simple finite crosscut whose nonendpoint trace is strictly inside the coordinate
disk, together with an avoiding second disk path, produces a closed generic-ray
chain whose parity is constant on both original complementary circle intervals
and equal at the original second and fourth endpoints. All circle-incidence
and closed-chain prerequisites are derived from the supplied genuine traces.
This does not assert that the two interval constants are different. -/
theorem exists_original_circle_interval_parity_internal (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (vs : List (ℝ × ℝ)) (hv : vs ≠ []) (hvs : IsSimplePolygonalChain vs)
    (hvhead : vs.head hv = (Real.cos θ₁, Real.sin θ₁))
    (hvlast : vs.getLast hv = (Real.cos θ₃, Real.sin θ₃))
    (hvD : polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hvI : polygonalChain vs \ {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ⊆
      {z | z.1 ^ 2 + z.2 ^ 2 < 1})
    (r : Path (Real.cos θ₂, Real.sin θ₂) (Real.cos θ₄, Real.sin θ₄))
    (hrD : range r ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hvr : Disjoint (polygonalChain vs) (range r)) :
    ∃ us : List (ℝ × ℝ), ∃ u : Plane, Plane.IsDirection u ∧
      IsClosedChain (coordinateEdges (chainEdges vs ++ chainEdges us)) ∧
      (∀ P ∈ coordinateEdges (chainEdges vs ++ chainEdges us), hgt u P.1 ≠ hgt u P.2) ∧
      parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
          (coordinateEquiv (Real.cos θ₂, Real.sin θ₂)) =
        parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
          (coordinateEquiv (Real.cos θ₄, Real.sin θ₄)) ∧
      (∀ θ ∈ Ioo θ₁ θ₃, ∀ φ ∈ Ioo θ₁ θ₃,
        parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
            (coordinateEquiv (Real.cos θ, Real.sin θ)) =
          parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
            (coordinateEquiv (Real.cos φ, Real.sin φ))) ∧
      (∀ θ ∈ Ioo θ₃ (θ₁ + 2 * Real.pi), ∀ φ ∈ Ioo θ₃ (θ₁ + 2 * Real.pi),
        parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
            (coordinateEquiv (Real.cos θ, Real.sin θ)) =
          parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
            (coordinateEquiv (Real.cos φ, Real.sin φ))) := by
  obtain ⟨us, _, _, _, _, hout, u, hu, hC, hL, hcover, _, _, heq⟩ :=
    exists_original_endpoint_parity_chain_internal θ₁ θ₂ θ₃ θ₄ h₁₂ h₂₃ h₃₄ h₄₁
      vs hv hvs hvhead hvlast hvD r hrD hvr
  have hcircle : ∀ θ : ℝ, coordinateEquiv (Real.cos θ, Real.sin θ) ∈
      cover (coordinateEdges (chainEdges vs ++ chainEdges us)) →
      (Real.cos θ, Real.sin θ) = (Real.cos θ₁, Real.sin θ₁) ∨
      (Real.cos θ, Real.sin θ) = (Real.cos θ₃, Real.sin θ₃) := by
    intro θ hmem
    by_contra hne
    have hnotends : (Real.cos θ, Real.sin θ) ∉
        ({(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} : Set (ℝ × ℝ)) := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hne
    rw [hcover] at hmem
    obtain ⟨z, hz, heqz⟩ := hmem
    have hzeq : z = (Real.cos θ, Real.sin θ) := coordinateEquiv.injective heqz
    rw [hzeq] at hz
    rcases hz with hz | hz
    · have hlt := hvI ⟨hz, hnotends⟩
      change Real.cos θ ^ 2 + Real.sin θ ^ 2 < 1 at hlt
      rw [Real.cos_sq_add_sin_sq] at hlt
      exact lt_irrefl 1 hlt
    · have hgt := hout ⟨hz, hnotends⟩
      change 1 < Real.cos θ ^ 2 + Real.sin θ ^ 2 at hgt
      rw [Real.cos_sq_add_sin_sq] at hgt
      exact lt_irrefl 1 hgt
  obtain ⟨hfirst, hsecond⟩ := parity_constant_on_complementary_circle_intervals_internal
    θ₁ θ₃ (h₁₂.trans h₂₃) (h₃₄.trans h₄₁) hu hL hC hcircle
  exact ⟨us, u, hu, hC, hL, heq, hfirst, hsecond⟩

end LatticeProb.Topology.PolygonalParity
