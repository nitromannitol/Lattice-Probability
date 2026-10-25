module

/-
All complementary minors of a copied-graph Laplacian count component-matching
forests. Cauchy–Binet separates the selections; integer incidence vanishing
removes nonforests, paired incidence signs evaluate forests, and the unique
root matching partitions the selections into exact permutation fibers.
-/
public import LatticeProb.LinearAlgebra.Matrix.CauchyBinet
public import LatticeProb.Graph.CopiedGraph.IncidenceConverse
public import LatticeProb.Graph.CopiedGraph.PairedIncidenceSign
public import LatticeProb.Graph.CopiedGraph.RootedForestCounting

@[expose] public section

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical BigOperators
noncomputable section

private def nonrootEquiv {d k : ℕ} (I : Finset (Fin (d + k))) (hI : I.card = k) :
    Fin d ≃ {v : Fin (d + k) // v ∉ I} :=
  (Iᶜ.orderIsoOfFin (show Iᶜ.card = d by
    rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel])).toEquiv.trans
    { toFun := fun v => ⟨v.val, Finset.mem_compl.mp v.property⟩
      invFun := fun v => ⟨v.val, Finset.mem_compl.mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Integer all-minors matrix-tree theorem.** The ordered complementary
Laplacian minor is the root-label parity times the signed number of copied
forests pairing each increasing I-root with its permuted increasing J-root.
Empty minors, overlapping roots, loops, parallel copies and disconnected
ambient graphs are included. -/
theorem det_laplacian_minor_int {d k : ℕ} {E : Type*} [Fintype E]
    (G : CopiedGraph (Fin (d + k)) E) (I J : Finset (Fin (d + k)))
    (hI : I.card = k) (hJ : J.card = k) :
    ((Matrix.of fun x y => ∑ e : E, G.incidenceColumn e x * G.incidenceColumn e y).submatrix
      (Iᶜ.orderEmbOfFin (show Iᶜ.card = d by
        rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]))
      (Jᶜ.orderEmbOfFin (show Jᶜ.card = d by
        rw [Finset.card_compl, Fintype.card_fin, hJ, Nat.add_sub_cancel]))).det =
      (-1 : ℤ) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ J, (y : ℕ))) *
        ∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π : ℤ) *
          (Nat.card {F : Finset E // G.IsRootedForest (I : Set (Fin (d + k))) F ∧
            ∀ r : Fin k, G.reaches F (I.orderEmbOfFin hI r)
              (J.orderEmbOfFin hJ (π r))} : ℤ) := by
  let irow := Iᶜ.orderEmbOfFin (show Iᶜ.card = d by
    rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel])
  let jrow := Jᶜ.orderEmbOfFin (show Jᶜ.card = d by
    rw [Finset.card_compl, Fintype.card_fin, hJ, Nat.add_sub_cancel])
  let q (F : {F : Finset E // F.card = d}) : Fin d ≃ F.val :=
    (F.val.equivFinOfCardEq F.property).symm
  let A : Matrix (Fin d) E ℤ := fun a e => G.incidenceColumn e (irow a)
  let B : Matrix E (Fin d) ℤ := fun e b => G.incidenceColumn e (jrow b)
  let eSize : {F : Finset E // F.card = Fintype.card (Fin d)} ≃
      {F : Finset E // F.card = d} :=
    Equiv.subtypeEquivRight (fun _ => by rw [Fintype.card_fin])
  have hCB : (A * B).det = ∑ F : {F : Finset E // F.card = d},
      (Matrix.of fun a b => G.incidenceColumn (q F b).val (irow a)).det *
        (Matrix.of fun a b => G.incidenceColumn (q F a).val (jrow b)).det := by
    refine (Matrix.det_mul_eq_sum_subsets A B (fun F => q (eSize F))).trans ?_
    exact Fintype.sum_equiv eSize _ _ (fun _ => rfl)
  change (A * B).det = _
  rw [hCB]
  let i := (I.orderIsoOfFin hI).toEquiv
  let j := (J.orderIsoOfFin hJ).toEquiv
  let s : ℤ := (-1 : ℤ) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ J, (y : ℕ)))
  calc
    _ = ∑ F : {F : Finset E // F.card = d},
        s * (if h : G.IsRootedForest (I : Set (Fin (d + k))) F.val ∧
            G.IsRootedForest (J : Set (Fin (d + k))) F.val then
          (Equiv.Perm.sign (rootMatchingPerm i j h.1 h.2) : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro F _
      let MI : Matrix (Fin d) (Fin d) ℤ :=
        fun a b => G.incidenceColumn (q F b).val (irow a)
      let MJ : Matrix (Fin d) (Fin d) ℤ :=
        fun a b => G.incidenceColumn (q F b).val (jrow a)
      change MI.det * MJ.transpose.det = _
      rw [Matrix.det_transpose]
      by_cases h : G.IsRootedForest (I : Set (Fin (d + k))) F.val ∧
        G.IsRootedForest (J : Set (Fin (d + k))) F.val
      · rw [dif_pos h]
        exact G.paired_incidence_minor_sign F.val (q F) I J hI hJ h.1
          (rootMatchingPerm i j h.1 h.2) (rootMatchingPerm_reaches i j h.1 h.2)
      · rw [dif_neg h, mul_zero]
        by_cases hR : G.IsRootedForest (I : Set (Fin (d + k))) F.val
        · have hS : ¬G.IsRootedForest (J : Set (Fin (d + k))) F.val :=
            fun hS => h ⟨hR, hS⟩
          have hz : MJ.det = 0 := G.det_nonrootIncidence_eq_zero_of_not_isRootedForest
            F.val J (nonrootEquiv J hJ) (q F) hS
          rw [hz, mul_zero]
        · have hz : MI.det = 0 := G.det_nonrootIncidence_eq_zero_of_not_isRootedForest
            F.val I (nonrootEquiv I hI) (q F) hR
          rw [hz, zero_mul]
    _ = _ := by
      rw [← Finset.mul_sum]
      exact congrArg (fun z : ℤ => s * z)
        (sum_rootMatchingPerm_of_card_eq G I (J : Set (Fin (d + k))) i j
          (fun π => (Equiv.Perm.sign π : ℤ)) d
          (by rw [Fintype.card_fin, hI, Nat.add_sub_cancel]))

/-- **All-minors matrix-tree theorem over a commutative ring.** The Laplacian
built from literal endpoint differences has each ordered complementary minor
equal to root-label parity times the signed cardinality of its exact copied
forest matching fibers. Every copy retains its own identifier and orientation. -/
theorem det_laplacian_minor {R : Type*} [CommRing R] {d k : ℕ} {E : Type*} [Fintype E]
    (G : CopiedGraph (Fin (d + k)) E) (I J : Finset (Fin (d + k)))
    (hI : I.card = k) (hJ : J.card = k) :
    ((Matrix.of fun x y => ∑ e : E,
      ((if x = G.left e then (1 : R) else 0) - (if x = G.right e then 1 else 0)) *
      ((if y = G.left e then (1 : R) else 0) - (if y = G.right e then 1 else 0))).submatrix
      (Iᶜ.orderEmbOfFin (show Iᶜ.card = d by
        rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]))
      (Jᶜ.orderEmbOfFin (show Jᶜ.card = d by
        rw [Finset.card_compl, Fintype.card_fin, hJ, Nat.add_sub_cancel]))).det =
      (-1 : R) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ J, (y : ℕ))) *
        ∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : R) *
          (Nat.card {F : Finset E // G.IsRootedForest (I : Set (Fin (d + k))) F ∧
            ∀ r : Fin k, G.reaches F (I.orderEmbOfFin hI r)
              (J.orderEmbOfFin hJ (π r))} : R) := by
  let L : Matrix (Fin (d + k)) (Fin (d + k)) ℤ :=
    Matrix.of fun x y => ∑ e : E, G.incidenceColumn e x * G.incidenceColumn e y
  have hcast : L.map (fun z : ℤ => (z : R)) = Matrix.of (fun x y => ∑ e : E,
      ((if x = G.left e then (1 : R) else 0) - (if x = G.right e then 1 else 0)) *
      ((if y = G.left e then (1 : R) else 0) - (if y = G.right e then 1 else 0))) := by
    ext x y
    simp only [L, Matrix.map_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul,
      incidenceColumn, Int.cast_sub]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp only [Int.cast_one, Int.cast_zero]
  have heq := congrArg (fun z : ℤ => (z : R)) (det_laplacian_minor_int G I J hI hJ)
  rw [Int.cast_det] at heq
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_sum, Int.cast_natCast] at heq
  change ((L.map (fun z : ℤ => (z : R))).submatrix _ _).det = _ at heq
  rw [hcast] at heq
  exact heq

end
end LatticeProb.Graph.CopiedGraph
