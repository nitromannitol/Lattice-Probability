module

/-
# Transport of finite-set event probabilities

A ground-set equivalence transports insertion-closed events and finite sums.
Pulling a coordinate frame back to the original carrier identifies the actual
atoms with ordered determinant coefficients without transporting inclusion sums.
-/
public import LatticeProb.Prob.DPP.OrderedAtoms

@[expose] public section


namespace LatticeProb.DPP
open scoped BigOperators Classical
noncomputable section

/-- Finite-set transport along an equivalence preserves insertion. -/
theorem finsetCongr_insert {E F : Type*} [DecidableEq E] [DecidableEq F]
    (e : E ≃ F) (i : E) (S : Finset E) :
    e.finsetCongr (insert i S) = insert (e i) (e.finsetCongr S) :=
  Finset.map_insert e.toEmbedding i S

/-- The pullback of an insertion-closed event is insertion-closed. -/
theorem insertion_closed_preimage_finsetCongr {E F : Type*}
    [DecidableEq E] [DecidableEq F] (e : E ≃ F) (ev : Set (Finset F))
    (hev : ∀ S ∈ ev, ∀ i : F, insert i S ∈ ev) :
    ∀ S ∈ e.finsetCongr ⁻¹' ev, ∀ i : E, insert i S ∈ e.finsetCongr ⁻¹' ev := by
  intro S hS i
  change e.finsetCongr (insert i S) ∈ ev
  rw [finsetCongr_insert]
  exact hev (e.finsetCongr S) hS (e i)

/-- Event masses are unchanged by a bijection of the ground set. -/
theorem sum_indicator_finsetCongr {E F : Type*}
    [Fintype E] [Fintype F] (e : E ≃ F) (p : Finset F → ℝ) (ev : Set (Finset F)) :
    (∑ S, Set.indicator (e.finsetCongr ⁻¹' ev) (p ∘ e.finsetCongr) S) =
      ∑ T, Set.indicator ev p T := by
  have he : Set.indicator (e.finsetCongr ⁻¹' ev) (p ∘ e.finsetCongr) =
      (Set.indicator ev p) ∘ e.finsetCongr := by
    ext S
    change Set.indicator (e.finsetCongr ⁻¹' ev) (p ∘ e.finsetCongr) S =
      Set.indicator ev p (e.finsetCongr S)
    by_cases hS : e.finsetCongr S ∈ ev
    · rw [Set.indicator_of_mem (show S ∈ e.finsetCongr ⁻¹' ev from hS),
        Set.indicator_of_mem hS]
      rfl
    · rw [Set.indicator_of_notMem (show S ∉ e.finsetCongr ⁻¹' ev from hS),
        Set.indicator_of_notMem hS]
  rw [he]
  exact e.finsetCongr.sum_comp (Set.indicator ev p)

/-- A selected coordinate subset is equivalent to its transported original subset. -/
def finsetMapEquiv {E F : Type*} (e : E ≃ F) (S : Finset E) :
    S ≃ e.finsetCongr S where
  toFun i := ⟨e i.val, (Finset.mem_map' e.toEmbedding).mpr i.property⟩
  invFun i := ⟨e.symm i.val, (Finset.mem_map_equiv).mp i.property⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv i := Subtype.ext (e.apply_symm_apply i.val)

/-- **Original-carrier ordered atoms.** The literal inclusion law for a frame
pulled back along a ground-set equivalence has the coordinate frame's squared
ordered determinant coefficients, at every subset including off-degree subsets. -/
theorem atom_finsetCongr_eq_determinantCoeff_sq
    {E : Type*} [Fintype E] [DecidableEq E] {n k : ℕ}
    (e : Fin n ≃ E) (V : Matrix (Fin n) (Fin k) ℝ) (hV : V.transpose * V = 1)
    (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      (((V * V.transpose).submatrix e.symm e.symm).submatrix
        (fun a : A => (a : E)) (fun a : A => (a : E))).det)
    (S : Finset (Fin n)) :
    p (e.finsetCongr S) = LatticeProb.SubsetContraction.determinantCoeff V S ^ 2 := by
  let W : Matrix E (Fin k) ℝ := V.submatrix e.symm id
  have hW : W.transpose * W = 1 := by
    change V.transpose.submatrix id e.symm * V.submatrix e.symm id = 1
    rw [Matrix.submatrix_mul_equiv V.transpose V id e.symm id, hV,
      Matrix.submatrix_id_id]
  have hdetW : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((W * W.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det := hdet
  have hcard : (e.finsetCongr S).card = S.card := Finset.card_map e.toEmbedding
  by_cases hS : S.card = k
  · rw [LatticeProb.SubsetContraction.determinantCoeff_of_card_eq V S hS]
    let q : Fin k ≃ e.finsetCongr S :=
      (S.orderIsoOfFin hS).toEquiv.trans (finsetMapEquiv e S)
    have hatom := atom_eq_sq_of_enumeration W p hp hdetW
      (e.finsetCongr S) (hcard.trans hS) q
    have he : W.submatrix (fun i => (q i).val) id =
        V.submatrix (fun i => ((S.orderIsoOfFin hS) i).val) id := by
      ext i j
      change V (e.symm (e _)) j = _
      rw [e.symm_apply_apply]
      rfl
    exact hatom.trans (congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M.det ^ 2) he)
  · rw [LatticeProb.SubsetContraction.determinantCoeff_of_card_ne V S hS,
      zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact atom_eq_zero_of_card_ne W hW p hp hdetW (e.finsetCongr S)
      (fun h => hS (hcard.symm.trans h))

end
end LatticeProb.DPP
