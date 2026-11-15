import LatticeProb.Topology.JordanExteriorRetraction
import LatticeProb.Topology.PuncturedDiskRetraction

/-! Retraction of a punctured plane onto the boundary of a Jordan disk. -/

set_option autoImplicit false

noncomputable section

open Set Metric
open LQGMetric

namespace LatticeProb

/-- A Jordan disk admits a retraction of the plane punctured at its centre
onto its boundary. -/
theorem exists_punctured_plane_jordan_retraction {K : Set ℂ} {p : ℂ}
    (hK : IsCompact K) (hp : p ∈ interior K) (hKc : IsPreconnected Kᶜ)
    (hJ : JordanMap.IsJordanCurve (frontier K))
    (e : closedBall (0 : ℂ) 1 ≃ₜ K)
    (he : (e ⟨0, mem_closedBall_self (by norm_num)⟩ : ℂ) = p)
    (heB : (fun z => (e z : ℂ)) '' {z | (z : ℂ) ∈ sphere 0 1} = frontier K) :
    ∃ r : {z : ℂ // z ≠ p} → ℂ, Continuous r ∧
      (∀ x, r x ∈ frontier K) ∧
      (∀ x : {z : ℂ // z ≠ p}, (x : ℂ) ∈ frontier K → r x = x) := by
  classical
  obtain ⟨ri, hri, hriB, hrifix⟩ := exists_punctured_disk_boundary_retraction e
  obtain ⟨ro, hro, hroB, hrofix⟩ := exists_jordan_exterior_boundary_retraction hK hp hKc hJ
  let X := {z : ℂ // z ≠ p}
  let A : Set X := {x | (x : ℂ) ∈ K}
  let B : Set X := {x | (x : ℂ) ∈ closure Kᶜ}
  let gi : A → {x : K // x ≠ e ⟨0, mem_closedBall_self (by norm_num)⟩} :=
    fun x => ⟨⟨x.1, x.2⟩, fun h => x.1.2 (by simpa [he] using congrArg Subtype.val h)⟩
  let go : B → closure Kᶜ := fun x => ⟨x.1, x.2⟩
  have hgi : Continuous gi := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_val.subtype_mk _
  have hgo : Continuous go := continuous_subtype_val.subtype_val.subtype_mk _
  let r : X → ℂ := fun x =>
    if hx : x ∈ A then ri (gi ⟨x, hx⟩) else ro (go ⟨x, subset_closure hx⟩)
  have hA : IsClosed A := hK.isClosed.preimage continuous_subtype_val
  have hB : IsClosed B := isClosed_closure.preimage continuous_subtype_val
  have hcover : A ∪ B = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    by_cases hx : x ∈ A
    · exact Or.inl hx
    · exact Or.inr (subset_closure hx)
  have hriA : ContinuousOn r A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert (continuous_subtype_val.comp (hri.comp hgi)) using 1
    funext x
    simp [Set.domRestrict, r, x.2]
  have hrBcont : ContinuousOn r B := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hro.comp hgo using 1
    funext x
    by_cases hx : x.1 ∈ A
    · have hfront : (x.1 : ℂ) ∈ frontier K := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hx, x.2⟩
      simp only [Set.domRestrict, Function.comp_apply, r, dite_eq_left hx]
      change (ri (gi ⟨x.1, hx⟩) : ℂ) = ro (go x)
      rw [hrifix _ (heB.symm ▸ hfront), hrofix _ hfront]
    · simp [Set.domRestrict, r, hx]
  have hr : Continuous r := by
    apply continuousOn_univ.mp
    rw [← hcover]
    exact hriA.union_of_isClosed hrBcont hA hB
  refine ⟨r, hr, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ A
    · simpa only [r, dite_eq_left hx, heB] using hriB (gi ⟨x, hx⟩)
    · simpa only [r, dite_eq_right hx] using hroB (go ⟨x, subset_closure hx⟩)
  · intro x hx
    have hxA : x ∈ A := by
      change (x : ℂ) ∈ K
      rw [← hK.isClosed.closure_eq]
      exact frontier_subset_closure hx
    simpa only [r, dite_eq_left hxA] using congrArg Subtype.val (hrifix (gi ⟨x, hxA⟩) (heB.symm ▸ hx))

end LatticeProb
