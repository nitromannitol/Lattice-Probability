/-
Janiszewski's theorem at a point, for compact plane sets, and hence the frozen
polygonal statement `LatticeProb.PolygonalJaniszewski`.

The proof transports Janiszewski's theorem for compact subsets of `ℂ`
(`QuantumZipper.CA.Topo.janiszewski`, adapted from Leonardo Bonanno's
formalizations; Burckel, *Classical Analysis in the Complex Plane*, Exercise
4.37(ii)) to `Plane = Fin 2 → ℝ` along the linear homeomorphism `Plane ≃ ℂ`.
A point is not separated from infinity by a compact set exactly when its
component lies in the unbounded component, which contains the exterior of a
large disk; so the two-point form of Janiszewski's theorem applied to `p` and a
far point gives the statement at a point.
-/
import LatticeProb.External.PolygonalTopology
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep

noncomputable section

open Set Bornology

namespace LatticeProb

namespace Janiszewski

/-- The exterior `{z | R < ‖z‖}` of a disk in `ℂ` is unbounded. -/
theorem not_isBounded_setOf_lt_norm (R : ℝ) : ¬ IsBounded {z : ℂ | R < ‖z‖} := by
  intro h
  obtain ⟨C, hC⟩ := h.exists_norm_le
  have h1 : max R C + 1 ≤ ‖((max R C + 1 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  have := hC _ (show R < ‖((max R C + 1 : ℝ) : ℂ)‖ by linarith [le_max_left R C])
  linarith [le_max_right R C]

/-- **Janiszewski's theorem at a point, in `ℂ`.** If neither of two compact sets with
preconnected intersection separates `p ∉ A ∪ B` from infinity, then neither does their union. -/
theorem not_isBounded_connectedComponentIn_compl_union {A B : Set ℂ} (hA : IsCompact A)
    (hB : IsCompact B) (hAB : IsPreconnected (A ∩ B)) {p : ℂ} (hp : p ∉ A ∪ B)
    (hAp : ¬ IsBounded (connectedComponentIn Aᶜ p))
    (hBp : ¬ IsBounded (connectedComponentIn Bᶜ p)) :
    ¬ IsBounded (connectedComponentIn (A ∪ B)ᶜ p) := by
  obtain ⟨R, hR⟩ := (hA.union hB).isBounded.subset_ball (0 : ℂ)
  set b : ℂ := ((|R| + 1 : ℝ) : ℂ)
  have hb : R < ‖b‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (le_abs_self R).trans_lt ((lt_add_one _).trans_le (le_abs_self _))
  have hbS : b ∉ A ∪ B := fun h => by
    have := hR h
    rw [Metric.mem_ball, dist_zero_right] at this
    exact lt_asymm this hb
  have far : ∀ {S : Set ℂ}, S ⊆ Metric.ball 0 R → p ∉ S →
      ¬ IsBounded (connectedComponentIn Sᶜ p) → b ∈ connectedComponentIn Sᶜ p := by
    intro S hS hpS hSp
    have hsub := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hS
      isPreconnected_connectedComponentIn hSp
      (Set.disjoint_left.2 fun _ hx hxS => connectedComponentIn_subset _ _ hx hxS) hb
    have hpb : p ∈ connectedComponentIn Sᶜ b := hsub (mem_connectedComponentIn hpS)
    rw [← connectedComponentIn_eq hpb]
    exact mem_connectedComponentIn fun h => (lt_asymm (by
      simpa [Metric.mem_ball, dist_zero_right] using hS h) hb)
  have hbA := far (subset_union_left.trans hR) (fun h => hp (Or.inl h)) hAp
  have hbB := far (subset_union_right.trans hR) (fun h => hp (Or.inr h)) hBp
  have hbU := QuantumZipper.CA.Topo.janiszewski hA hB hAB hp hbS hbA hbB
  rw [connectedComponentIn_eq hbU]
  intro hbdd
  refine not_isBounded_setOf_lt_norm R (hbdd.subset ?_)
  refine (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R).subset_connectedComponentIn hb ?_
  exact QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR

/-- The linear homeomorphism `Plane ≃ ℂ`, `x ↦ x 0 + x 1 * I`. -/
def planeEquiv : Plane ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm

/-- A set of the plane is bounded exactly when its image in `ℂ` is. -/
theorem isBounded_image_planeEquiv_iff {S : Set Plane} :
    IsBounded (planeEquiv '' S) ↔ IsBounded S := by
  refine ⟨fun h => ?_, fun h => planeEquiv.lipschitzWith.isBounded_image h⟩
  have := planeEquiv.symm.lipschitzWith.isBounded_image h
  rwa [ContinuousLinearEquiv.symm_image_image] at this

/-- Separation from infinity is invariant under `planeEquiv`. -/
theorem separates_iff {S : Set Plane} {p : Plane} (hp : p ∉ S) :
    Separates S p ↔ IsBounded (connectedComponentIn (planeEquiv '' S)ᶜ (planeEquiv p)) := by
  have h := planeEquiv.toHomeomorph.image_connectedComponentIn (s := Sᶜ) (x := p) hp
  rw [image_compl_eq planeEquiv.toHomeomorph.bijective] at h
  rw [Separates, ← isBounded_image_planeEquiv_iff]
  exact iff_of_eq (congrArg IsBounded h)

end Janiszewski

open Janiszewski

/-- **Janiszewski's theorem at a point.** If two compact plane sets have preconnected
intersection and neither separates `p ∉ A ∪ B` from infinity, then their union does not
separate `p` from infinity either. -/
theorem not_separates_union {A B : Set Plane} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : IsPreconnected (A ∩ B)) {p : Plane} (hp : p ∉ A ∪ B)
    (hAp : ¬ Separates A p) (hBp : ¬ Separates B p) : ¬ Separates (A ∪ B) p := by
  have hpA : p ∉ A := fun h => hp (Or.inl h)
  have hpB : p ∉ B := fun h => hp (Or.inr h)
  rw [separates_iff hp, image_union]
  rw [separates_iff hpA] at hAp
  rw [separates_iff hpB] at hBp
  refine not_isBounded_connectedComponentIn_compl_union (hA.image planeEquiv.continuous)
    (hB.image planeEquiv.continuous) ?_ (by rwa [← image_union, planeEquiv.injective.mem_set_image])
    hAp hBp
  rw [← image_inter planeEquiv.injective]
  exact hAB.image _ planeEquiv.continuous.continuousOn

/-- The frozen polygonal form of Janiszewski's theorem holds; the polygonality hypotheses are
not needed. -/
theorem polygonalJaniszewski : PolygonalJaniszewski := by
  intro A B _ _ hA hB v hv p hp hAp hBp
  exact not_separates_union hA hB ((subsingleton_singleton.anti hv).isPreconnected) hp hAp hBp

end LatticeProb
