module

/-
# Creation and contraction of ordered determinant coefficients

The added vector is the first column. First-column Laplace expansion therefore
has exactly the signed deletion coefficients of left exterior multiplication.
-/

public import LatticeProb.LinearAlgebra.OrderedMinorInsertion
public import LatticeProb.LinearAlgebra.DeterminantContraction

@[expose] public section



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical Matrix
noncomputable section

/-- Add `u` as the first column of a frame. -/
def prependColumn {n k : ℕ} (u : Fin n → ℝ) (V : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin (k + 1)) ℝ := fun i => Fin.cons (u i) (V i)

/-- Removing a sorted row position enumerates exactly the erased subset. -/
theorem orderEmb_erase_succAbove {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k + 1) (p : Fin (k + 1)) :
    let i := S.orderEmbOfFin hS p
    let hT : (S.erase i).card = k := by
      rw [Finset.card_erase_of_mem (S.orderEmbOfFin_mem hS p), hS,
        Nat.add_sub_cancel]
    (fun j => S.orderEmbOfFin hS (p.succAbove j)) = (S.erase i).orderEmbOfFin hT := by
  dsimp only
  apply Finset.orderEmbOfFin_unique
  · intro j
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact Fin.succAbove_ne p j ((S.orderEmbOfFin hS).injective he)
    · exact S.orderEmbOfFin_mem hS (p.succAbove j)
  · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove p)

/-- The first-column Laplace sign is the literal finset insertion sign. -/
theorem insertionSign_orderEmb {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k + 1) (p : Fin (k + 1)) :
    insertionSign S (S.orderEmbOfFin hS p) = (-1 : ℝ) ^ (p : ℕ) := by
  let i := S.orderEmbOfFin hS p
  have hi : i ∈ S := S.orderEmbOfFin_mem hS p
  have hT : (S.erase i).card = k := by
    rw [Finset.card_erase_of_mem hi, hS, Nat.add_sub_cancel]
  have hpos := insertion_position_eq_card_filter (S.erase i) hT i
    (Finset.notMem_erase i S)
  let hI : (insert i (S.erase i)).card = k + 1 :=
    (Finset.card_insert_of_notMem (Finset.notMem_erase i S)).trans
      (congrArg Nat.succ hT)
  let q := (insert i (S.erase i)).orderIsoOfFin hI
  let pI := q.symm ⟨i, Finset.mem_insert_self i (S.erase i)⟩
  have henum : ((insert i (S.erase i)).orderEmbOfFin hI : Fin (k + 1) → Fin n) =
      S.orderEmbOfFin hS := by
    apply Finset.orderEmbOfFin_unique hS
    · intro j
      have hj := (insert i (S.erase i)).orderEmbOfFin_mem hI j
      rcases Finset.mem_insert.mp hj with he | he
      · exact he.symm ▸ hi
      · exact (Finset.mem_erase.mp he).2
    · exact ((insert i (S.erase i)).orderEmbOfFin hI).strictMono
  have hpi : (insert i (S.erase i)).orderEmbOfFin hI pI = i :=
    congrArg Subtype.val (q.apply_symm_apply ⟨i, Finset.mem_insert_self i (S.erase i)⟩)
  have hpI : pI = p := by
    apply (S.orderEmbOfFin hS).injective
    exact (congrFun henum pI).symm.trans hpi
  have hpos' : (p : ℕ) = ((S.erase i).filter (fun j => j < i)).card := by
    change (pI : ℕ) = _ at hpos
    rwa [hpI] at hpos
  have hf : (S.erase i).filter (fun j => j < i) = S.filter (fun j => j < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hj⟩, hlt⟩; exact ⟨hj, hlt⟩
    · rintro ⟨hj, hlt⟩; exact ⟨⟨hlt.ne, hj⟩, hlt⟩
  rw [insertionSign_eq_pow_card_filter, ← hf, ← hpos']

/-- **Ordered determinant creation.** Adding a first column is exactly the
CAR creator on all finsets, including the zero terms outside degree `k+1`. -/
theorem determinantCoeff_prependColumn {n k : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) (S : Finset (Fin n)) :
    determinantCoeff (prependColumn u V) S =
      ∑ i : Fin n, if i ∈ S then
        insertionSign S i * u i * determinantCoeff V (S.erase i) else 0 := by
  by_cases hS : S.card = k + 1
  · rw [determinantCoeff_of_card_eq _ _ hS, Matrix.det_succ_column_zero]
    have hsum (f : Fin n → ℝ) : (∑ i : Fin n, if i ∈ S then f i else 0) =
        ∑ p : Fin (k + 1), f (S.orderEmbOfFin hS p) := by
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun i : Fin n => i ∈ S) = S := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hf]
      calc
        (∑ i ∈ S, f i) = ∑ i ∈ Finset.univ.image (S.orderEmbOfFin hS), f i :=
          congrArg (fun T : Finset (Fin n) => ∑ i ∈ T, f i)
            (S.image_orderEmbOfFin_univ hS).symm
        _ = _ := Finset.sum_image (S.orderEmbOfFin hS).injective.injOn
    rw [hsum]
    apply Finset.sum_congr rfl
    intro p _
    rw [insertionSign_orderEmb S hS p]
    congr 1
    rw [determinantCoeff_erase V S hS _ (S.orderEmbOfFin_mem hS p)]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, prependColumn, id_eq, Fin.cons_succ]
    exact congrArg (fun f : Fin k → Fin n => V (f a) b)
      (orderEmb_erase_succAbove S hS p)
  · rw [determinantCoeff_of_card_ne _ _ hS]
    symm
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · have hT : (S.erase i).card ≠ k := by
        rw [Finset.card_erase_of_mem hi]
        intro he
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      rw [determinantCoeff_of_card_ne V _ hT, mul_zero]
    · rfl

end
end LatticeProb.SubsetContraction
