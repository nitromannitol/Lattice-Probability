module

/-
Component indicators in the left kernel of literal copied incidence matrices.
-/

public import LatticeProb.Graph.CopiedGraph.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section



namespace LatticeProb.Graph.CopiedGraph

open scoped Classical BigOperators Matrix
noncomputable section
variable {V E A : Type*}

/-- The indicator of the actual copied-walk component containing a vertex. -/
def componentIndicator (K : Type*) [Zero K] [One K] (J : CopiedGraph V E)
    (F : Finset E) (x : V) : V → K :=
  fun v => if J.reaches F x v then 1 else 0

/-- Both endpoints of each selected original copy lie in the same component. -/
theorem componentIndicator_left_eq_right (K : Type*) [Zero K] [One K]
    (J : CopiedGraph V E) (F : Finset E) (x : V) {e : E} (he : e ∈ F) :
    J.componentIndicator K F x (J.left e) = J.componentIndicator K F x (J.right e) := by
  have hiff : J.reaches F x (J.left e) ↔ J.reaches F x (J.right e) :=
    ⟨fun h => h.tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩,
      fun h => h.tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩⟩
  simp only [componentIndicator, hiff]

/-- Testing a literal incidence column returns the difference of endpoint values. -/
theorem sum_mul_endpoint_difference {K : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (w : V → K) (l r : V) :
    (∑ v, w v * ((if v = l then 1 else 0) - (if v = r then 1 else 0))) =
      w l - w r := by
  simp [mul_sub, mul_ite, Finset.sum_sub_distrib]

/-- A function vanishing on the roots has the same sum on the nonroot carrier. -/
theorem sum_nonroots_eq_sum {K : Type*} [AddCommMonoid K] [Fintype V]
    (R : Finset V) (g : V → K) (hg : ∀ r ∈ R, g r = 0) :
    (∑ v : {v : V // v ∉ R}, g v.val) = ∑ v, g v := by
  rw [← Finset.sum_subtype Rᶜ (fun _ => Finset.mem_compl)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  exact hg v (by simpa only [Finset.mem_compl, not_not] using hv)

/-- The restricted indicator of a component missing the roots annihilates the actual
nonroot incidence columns. -/
theorem componentIndicator_vecMul_nonroot_incidence_eq_zero {K : Type*} [CommRing K]
    [Fintype V] [Fintype A] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {v : V // v ∉ R}) (b : A → F) (x : V)
    (hmiss : ∀ r ∈ R, ¬J.reaches F x r) :
    (fun i => J.componentIndicator K F x (a i).val) ᵥ*
      Matrix.of (fun i j : A =>
        (if (a i).val = J.left (b j).val then (1 : K) else 0) -
          (if (a i).val = J.right (b j).val then 1 else 0)) = 0 := by
  let w := J.componentIndicator K F x
  have hwroot : ∀ r ∈ R, w r = 0 := fun r hr => if_neg (hmiss r hr)
  ext j
  rw [Matrix.vecMul_apply_eq_sum, Pi.zero_apply]
  calc
    (∑ i, w (a i).val *
      ((if (a i).val = J.left (b j).val then (1 : K) else 0) -
        (if (a i).val = J.right (b j).val then 1 else 0))) =
        ∑ v : {v : V // v ∉ R}, w v.val *
          ((if v.val = J.left (b j).val then (1 : K) else 0) -
            (if v.val = J.right (b j).val then 1 else 0)) :=
      Fintype.sum_equiv a _ _ (fun _ => rfl)
    _ = ∑ v : V, w v *
          ((if v = J.left (b j).val then (1 : K) else 0) -
            (if v = J.right (b j).val then 1 else 0)) :=
      sum_nonroots_eq_sum R
        (fun v => w v * ((if v = J.left (b j).val then (1 : K) else 0) -
          (if v = J.right (b j).val then 1 else 0)))
        (fun r hr => by rw [hwroot r hr, zero_mul])
    _ = w (J.left (b j).val) - w (J.right (b j).val) :=
      sum_mul_endpoint_difference w _ _
    _ = 0 := sub_eq_zero.mpr (J.componentIndicator_left_eq_right K F x (b j).property)


/-- A root-free component gives a nonzero left kernel of every square nonroot minor.
Only membership of the selected columns is needed; ambient copy finiteness is unnecessary. -/
theorem det_nonroot_incidence_eq_zero_of_missing_root {K : Type*} [CommRing K] [IsDomain K]
    [Fintype V] [Fintype A] [DecidableEq A] (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V) (a : A ≃ {v : V // v ∉ R})
    (b : A → F) (x : V) (hmiss : ∀ r ∈ R, ¬J.reaches F x r) :
    (Matrix.of (fun i j : A =>
      (if (a i).val = J.left (b j).val then (1 : K) else 0) -
        (if (a i).val = J.right (b j).val then 1 else 0))).det = 0 := by
  let w := J.componentIndicator K F x
  have hxx : J.reaches F x x := .refl
  have hx : x ∉ R := fun hx => hmiss x hx hxx
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨fun i => w (a i).val, ?_, ?_⟩
  · intro hz
    have hz' := congrFun hz (a.symm ⟨x, hx⟩)
    change w (a (a.symm ⟨x, hx⟩)).val = 0 at hz'
    rw [a.apply_symm_apply] at hz'
    exact one_ne_zero ((if_pos hxx).symm.trans hz')
  · exact J.componentIndicator_vecMul_nonroot_incidence_eq_zero F R a b x hmiss

/-- A component missing every root annihilates both the copy columns and root unit columns. -/
theorem componentIndicator_vecMul_augmented_incidence_eq_zero {K : Type*} [CommRing K]
    [Fintype V] [DecidableEq V] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (e : V ≃ F ⊕ R) (x : V) (hmiss : ∀ r ∈ R, ¬J.reaches F x r) :
    J.componentIndicator K F x ᵥ* Matrix.of (fun v j : V => Sum.elim
      (fun f : F => (if v = J.left f.val then (1 : K) else 0) -
        (if v = J.right f.val then 1 else 0))
      (fun r : R => if v = r.val then (1 : K) else 0) (e j)) = 0 := by
  let w := J.componentIndicator K F x
  ext j
  rw [Matrix.vecMul_apply_eq_sum, Pi.zero_apply]
  simp only [Matrix.of_apply]
  cases e j with
  | inl f =>
    simp only [Sum.elim_inl]
    rw [sum_mul_endpoint_difference]
    exact sub_eq_zero.mpr (J.componentIndicator_left_eq_right K F x f.property)
  | inr r =>
    simp only [Sum.elim_inr]
    have hwr : w r.val = 0 := if_neg (hmiss r.val r.property)
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] using hwr

/-- **Component indicator kernel.** The same component indicator kills the original copy columns and all root unit columns. -/
theorem det_augmented_incidence_eq_zero_of_missing_root {K : Type*} [CommRing K] [IsDomain K]
    [Fintype V] [DecidableEq V] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (e : V ≃ F ⊕ R) (x : V) (hmiss : ∀ r ∈ R, ¬J.reaches F x r) :
    (Matrix.of (fun v j : V => Sum.elim
      (fun f : F => (if v = J.left f.val then (1 : K) else 0) -
        (if v = J.right f.val then 1 else 0))
      (fun r : R => if v = r.val then (1 : K) else 0) (e j))).det = 0 := by
  let w := J.componentIndicator K F x
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨w, ?_, ?_⟩
  · intro hz
    have hz' := congrFun hz x
    exact one_ne_zero ((if_pos (show J.reaches F x x from .refl)).symm.trans hz')
  · exact J.componentIndicator_vecMul_augmented_incidence_eq_zero F R e x hmiss

end
end LatticeProb.Graph.CopiedGraph
