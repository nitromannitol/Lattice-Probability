module

/-
# Alternation of original circle endpoints for polygonal crosscuts

Close the first simple disk chain by a produced outside radial completion.
The finite endpoint crossing jump puts the two original complementary circle
intervals at opposite parities. Constancy along an avoiding second disk path
then contradicts its alternating original endpoints. The wraparound interval
is retained using the literal period `2π`.
-/
public import LatticeProb.Topology.DiskRadialCrosscut

@[expose] public section



open Set
namespace LatticeProb.Topology.PolygonalParity

/-- **Polygonal disk alternation (internal).** A simple finite chain whose
nonendpoint trace is strictly in the round coordinate disk cannot avoid a
second disk path between alternating original unit-circle endpoints. All
outside completion, generic direction, crossing, and separation prerequisites
are derived from the actual traces. -/
theorem disk_polygonal_alternation_impossible_internal (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (vs : List (ℝ × ℝ)) (hv : vs ≠ []) (hs : IsSimplePolygonalChain vs)
    (hhead : vs.head hv = (Real.cos θ₁, Real.sin θ₁))
    (hlast : vs.getLast hv = (Real.cos θ₃, Real.sin θ₃))
    (hD : polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hI : polygonalChain vs \ {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ⊆
      {z | z.1 ^ 2 + z.2 ^ 2 < 1})
    (r : Path (Real.cos θ₂, Real.sin θ₂) (Real.cos θ₄, Real.sin θ₄))
    (hrD : range r ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hvr : Disjoint (polygonalChain vs) (range r)) : False := by
  have h13 := circle_point_ne_of_lt_lt_add_two_pi (h₁₂.trans h₂₃) (h₃₄.trans h₄₁)
  cases vs with
  | nil => exact (hv rfl).elim
  | cons a rest =>
    cases rest with
    | nil =>
      have heq : (Real.cos θ₁, Real.sin θ₁) = (Real.cos θ₃, Real.sin θ₃) :=
        hhead.symm.trans hlast
      exact h13 heq
    | cons b rest =>
      change a = (Real.cos θ₁, Real.sin θ₁) at hhead
      subst a
      let a : ℝ × ℝ := (Real.cos θ₁, Real.sin θ₁)
      let d : ℝ × ℝ := (Real.cos θ₃, Real.sin θ₃)
      obtain ⟨tail, ulast, uout, utanot, und⟩ :=
        exists_radial_polygonal_outside_completion θ₁ θ₃ h13
      let us := a :: (2 : ℝ) • a :: tail
      let V := a :: b :: rest
      let E := coordinateEdges (chainEdges V ++ chainEdges us)
      let R := coordinateEdges (chainEdges (b :: rest) ++ chainEdges ((2 : ℝ) • a :: tail))
      have hRnot : coordinateEquiv a ∉ cover R := by
        rw [← coordinateEquiv_image_edgeTrace]
        rintro ⟨z, hz, heq⟩
        have hza : z = a := coordinateEquiv.injective heq
        rw [hza, coordinateEdgeTrace_append] at hz
        rcases hz with hz | hz
        · exact hs.head_not_mem_tail (coordinateEdgeTrace_chainEdges_subset _ hz)
        · exact utanot (coordinateEdgeTrace_chainEdges_subset _ hz)
      have hRnd : ∀ P ∈ R, P.Nondeg := by
        intro P hP
        obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
        intro heq
        have hneq : Q.1 ≠ Q.2 := by
          rcases List.mem_append.mp hQ with hQ | hQ
          · exact nondeg_chainEdges_of_simple hs.2.1 Q hQ
          · exact und Q (List.mem_cons_of_mem _ hQ)
        exact hneq (coordinateEquiv.injective heq)
      have hbin : inner ℝ (coordinateEquiv b - coordinateEquiv a) (coordinateEquiv a) < 0 := by
        rw [inner_displacement_coordinateEquiv]
        exact hs.head_radial_neg (Real.cos_sq_add_sin_sq θ₁) hD
      have hcout : 0 < inner ℝ (coordinateEquiv ((2 : ℝ) • a) - coordinateEquiv a)
          (coordinateEquiv a) := by
        rw [inner_displacement_coordinateEquiv]
        exact coordinateRadial_smul_pos (Real.cos_sq_add_sin_sq θ₁) (by norm_num)
      obtain ⟨u, hu, hout, hab, hac, hR, hheight⟩ :=
        exists_generic_endpoint_direction (isDirection_coordinate_circle θ₁) hbin hcout hRnd hRnot
      have hE : E = ((coordinateEquiv a, coordinateEquiv b) ::
          coordinateEdges (chainEdges (b :: rest))) ++
          ((coordinateEquiv a, coordinateEquiv ((2 : ℝ) • a)) ::
            coordinateEdges (chainEdges ((2 : ℝ) • a :: tail))) := by
        change coordinateEdges (chainEdges V ++ chainEdges us) = _
        rw [coordinateEdges, List.map_append]
        rfl
      have hRsplit : R = coordinateEdges (chainEdges (b :: rest)) ++
          coordinateEdges (chainEdges ((2 : ℝ) • a :: tail)) := by
        change coordinateEdges (_ ++ _) = _
        rw [coordinateEdges, List.map_append]
        rfl
      have hL : ∀ P ∈ E, hgt u P.1 ≠ hgt u P.2 := by
        intro P hP
        rw [hE] at hP
        rcases List.mem_append.mp hP with hP | hP
        · rcases List.mem_cons.mp hP with rfl | hP
          · exact hab
          · exact hR P (hRsplit.symm ▸ List.mem_append_left _ hP)
        · rcases List.mem_cons.mp hP with rfl | hP
          · exact hac
          · exact hR P (hRsplit.symm ▸ List.mem_append_right _ hP)
      have hpar : ∀ q : Plane, parity u E q =
          parity u ((coordinateEquiv a, coordinateEquiv b) ::
            (coordinateEquiv a, coordinateEquiv ((2 : ℝ) • a)) :: R) q := by
        intro q
        rw [hE, parity_append, parity_cons, parity_cons, parity_cons, parity_cons,
          hRsplit, parity_append]
        abel
      have huws : us ≠ [] := List.cons_ne_nil _ _
      have hvws : V ≠ [] := List.cons_ne_nil _ _
      have hC : IsClosedChain E := isClosedChain_coordinateEdges_append hvws huws rfl
        (hlast.trans ulast.symm)
      have hune : us.head huws ≠ us.getLast huws := by
        change a ≠ us.getLast huws
        rw [ulast]
        exact h13
      have hvne : V.head hvws ≠ V.getLast hvws := by
        change a ≠ V.getLast hvws
        rw [hlast]
        exact h13
      have hcover : cover E = coordinateEquiv '' (polygonalChain V ∪ polygonalChain us) := by
        rw [← coordinateEquiv_image_edgeTrace, coordinateEdgeTrace_append,
          coordinateEdgeTrace_chainEdges hvws hvne, coordinateEdgeTrace_chainEdges huws hune]
      have hcircle : ∀ θ : ℝ, coordinateEquiv (Real.cos θ, Real.sin θ) ∈ cover E →
          (Real.cos θ, Real.sin θ) = a ∨ (Real.cos θ, Real.sin θ) = d := by
        intro θ hmem
        by_contra hne
        have hn : (Real.cos θ, Real.sin θ) ∉ ({a, d} : Set (ℝ × ℝ)) := by
          simpa only [mem_insert_iff, mem_singleton_iff] using hne
        rw [hcover] at hmem
        obtain ⟨z, hz, heq⟩ := hmem
        have hzeq := coordinateEquiv.injective heq
        rw [hzeq] at hz
        rcases hz with hz | hz
        · have hlt := hI ⟨hz, hn⟩
          change Real.cos θ ^ 2 + Real.sin θ ^ 2 < 1 at hlt
          rw [Real.cos_sq_add_sin_sq] at hlt
          exact lt_irrefl 1 hlt
        · have hgt := uout ⟨hz, hn⟩
          change 1 < Real.cos θ ^ 2 + Real.sin θ ^ 2 at hgt
          rw [Real.cos_sq_add_sin_sq] at hgt
          exact lt_irrefl 1 hgt
      obtain ⟨hfirst, hsecond⟩ := parity_constant_on_complementary_circle_intervals_internal
        θ₁ θ₃ (h₁₂.trans h₂₃) (h₃₄.trans h₄₁) hu hL hC hcircle
      have hends : ({a, d} : Set (ℝ × ℝ)) ⊆ polygonalChain V := by
        intro z hz
        rcases mem_insert_iff.mp hz with rfl | hz
        · exact head_mem_polygonal_chain hvws
        · rw [mem_singleton_iff] at hz
          rw [hz]
          change (Real.cos θ₃, Real.sin θ₃) ∈ polygonalChain V
          rw [← hlast]
          exact getLast_mem_polygonal_chain hvws
      have havoid : ∀ z ∈ range r, coordinateEquiv z ∉ cover E := by
        intro z hzr hzc
        rw [hcover] at hzc
        obtain ⟨w, hw, heq⟩ := hzc
        have hwz : w = z := coordinateEquiv.injective heq
        rw [hwz] at hw
        rcases hw with hw | hw
        · exact disjoint_left.mp hvr hw hzr
        · by_cases hzends : z ∈ ({a, d} : Set (ℝ × ℝ))
          · exact disjoint_left.mp hvr (hends hzends) hzr
          · exact (not_lt_of_ge (show z.1 ^ 2 + z.2 ^ 2 ≤ 1 from hrD hzr))
              (show 1 < z.1 ^ 2 + z.2 ^ 2 from uout ⟨hw, hzends⟩)
      have heq : parity u E (coordinateEquiv (Real.cos θ₂, Real.sin θ₂)) =
          parity u E (coordinateEquiv (Real.cos θ₄, Real.sin θ₄)) := by
        exact parity_eq_of_isPreconnected hu hL hC
          ((isConnected_range r.continuous).isPreconnected.image _ continuous_coordinateEquiv.continuousOn)
          (by rintro _ ⟨z, hz, rfl⟩; exact havoid z hz)
          (mem_image_of_mem coordinateEquiv r.source_mem_range)
          (mem_image_of_mem coordinateEquiv r.target_mem_range)
      obtain ⟨δ, hδ, hjump⟩ := exists_circle_endpoint_jump_internal θ₁ hu hout hab hac
        hbin hcout hR hRnot hheight
      let t := min δ (min (θ₃ - θ₁) (θ₁ + 2 * Real.pi - θ₃)) / 2
      have ht : 0 < t := half_pos (lt_min hδ
        (lt_min (sub_pos.mpr (h₁₂.trans h₂₃)) (sub_pos.mpr (h₃₄.trans h₄₁))))
      have htbound : t < min δ (min (θ₃ - θ₁) (θ₁ + 2 * Real.pi - θ₃)) :=
        half_lt_self (lt_min hδ
          (lt_min (sub_pos.mpr (h₁₂.trans h₂₃)) (sub_pos.mpr (h₃₄.trans h₄₁))))
      have htδ : t < δ := htbound.trans_le (min_le_left _ _)
      have ht13 : t < θ₃ - θ₁ :=
        htbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have ht31 : t < θ₁ + 2 * Real.pi - θ₃ :=
        htbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hpint : θ₁ + t ∈ Ioo θ₁ θ₃ :=
        ⟨lt_add_of_pos_right _ ht, by linarith only [ht13]⟩
      have hmint : θ₁ - t + 2 * Real.pi ∈ Ioo θ₃ (θ₁ + 2 * Real.pi) :=
        ⟨by linarith only [ht31], by linarith only [ht]⟩
      have hpval := hfirst _ hpint _ ⟨h₁₂, h₂₃⟩
      have hmval := hsecond _ hmint _ ⟨h₃₄, h₄₁⟩
      rw [Real.cos_add_two_pi, Real.sin_add_two_pi] at hmval
      have hj := hjump t ht htδ
      rw [← hpar, ← hpar, hmval, hpval, heq] at hj
      have hone : (1 : ZMod 2) = 0 :=
        add_left_cancel (hj.symm.trans (add_zero _).symm)
      exact one_ne_zero hone

end LatticeProb.Topology.PolygonalParity
