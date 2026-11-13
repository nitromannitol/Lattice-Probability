/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.CodeMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurableLocal
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalSimilarityMeasurable

/-!
# Measurability of the labelled coding of GMS cell configurations

`measurable_codeMap`: the coding `codeMap : GMSSpace → Code.RawCode` is measurable from GMS's
`d^CC`-Borel σ-algebra to the product σ-algebra of `Code.RawCode`.

Route (all local facts about `d^CC` are in `GMS/CodeMeasurableLocal.lean`):

* `interiorSet p`, the configurations having a cell with `p` in its interior, is `d^CC`-open, and on
  it the cell `interiorCell p H` containing `p` in its interior moves continuously for the Hausdorff
  metric (`isOpen_interiorSet_inter_preimage`): near `H` an admissible homeomorphism `f` of small
  displacement carries it to the corresponding cell of `H'`, at Hausdorff distance at most the
  displacement.
* The conductance `c_H(K_p(H), K_{p'}(H))` is continuous on `interiorSet p ∩ interiorSet p'`
  (`isOpen_inter_preimage_pairCond`): adjacent pairs are carried to adjacent pairs with small change
  of conductance, and non-adjacent pairs stay non-adjacent because `f⁻¹` preserves adjacency.
* The label event `labelSet n` (a cell with least rational interior label `n`) is a finite Boolean
  combination of the open sets `commonInteriorSet`, and `slot n`, `codeCond n m` are piecewise
  combinations of the continuous pieces on these Borel events.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS

/-! ### A measurability criterion -/

/-- A map which is continuous on an open set `A` (in the sense that `A ∩ g⁻¹ V` is open for open
`V`) and constant off `A` is Borel measurable. -/
theorem measurable_of_isOpen_inter_preimage {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {A : Set GMSSpace} (hA : IsOpen A) {g : GMSSpace → Y} {y₀ : Y}
    (hg : ∀ V : Set Y, IsOpen V → IsOpen (A ∩ g ⁻¹' V)) (hoff : ∀ H ∉ A, g H = y₀) :
    Measurable g := by
  refine measurable_of_isOpen fun V hV => ?_
  rw [← inter_union_compl (g ⁻¹' V) A]
  refine MeasurableSet.union ?_ ?_
  · rw [inter_comm]
    exact (hg V hV).measurableSet
  · by_cases hy : y₀ ∈ V
    · convert hA.measurableSet.compl using 1
      ext H
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
      exact ⟨fun h => h.2, fun h => ⟨by rw [hoff H h]; exact hy, h⟩⟩
    · convert MeasurableSet.empty using 1
      ext H
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hH hHA
      exact hy (by rw [← hoff H hHA]; exact hH)

/-! ### The cell containing a point in its interior -/

/-- The reference cell `{0}`, used as the value off `interiorSet p`. -/
noncomputable def refCell : Cell := {(0 : Plane)}

/-- The cell of `H` containing `p` in its interior (unique when it exists), `refCell` otherwise. -/
noncomputable def interiorCell (p : Plane) (H : GMSSpace) : Cell :=
  open Classical in
  if h : ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) then h.choose else refCell

theorem interiorCell_spec {p : Plane} {H : GMSSpace} (hH : H ∈ interiorSet p) :
    interiorCell p H ∈ H.1.cells ∧ p ∈ interior (interiorCell p H : Set Plane) := by
  have h : ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) := hH
  unfold interiorCell
  rw [dif_pos h]
  exact h.choose_spec

theorem interiorCell_eq {p : Plane} {H : GMSSpace} {K : Cell} (hK : K ∈ H.1.cells)
    (hp : p ∈ interior (K : Set Plane)) : interiorCell p H = K := by
  obtain ⟨h1, h2⟩ := interiorCell_spec (p := p) (H := H) ⟨K, hK, hp⟩
  exact CellConfig.eq_of_interior_mem H.2 h1 hK h2 hp

theorem interiorCell_of_notMem {p : Plane} {H : GMSSpace} (hH : H ∉ interiorSet p) :
    interiorCell p H = refCell := by
  have h : ¬ ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) := hH
  unfold interiorCell
  rw [dif_neg h]

/-- **Continuity of the interior cell** on `interiorSet p`, for the Hausdorff metric. -/
theorem isOpen_interiorSet_inter_preimage (p : Plane) {V : Set Cell} (hV : IsOpen V) :
    IsOpen (interiorSet p ∩ interiorCell p ⁻¹' V) := by
  refine isOpen_of_forall_dCC fun H hH => ?_
  obtain ⟨hHp, hHV⟩ := hH
  obtain ⟨hKc, hKi⟩ := interiorCell_spec hHp
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV _ hHV
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.1 isOpen_interior p hKi
  have hn := norm_nonneg p
  have hη : 0 < min (δ / 2) (ρ / 2) := lt_min (half_pos hδ) (half_pos hρ)
  obtain ⟨ε, hε, hspec⟩ := CellConfig.exists_admissible_of_dCC_lt
    (R := ‖p‖ + δ + 1) (η := min (δ / 2) (ρ / 2)) (by linarith) hη
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨r, hRr, f, hf, hdist⟩ := hspec H.1 H'.1 hH'
  have hfη := CellConfig.dist_lt_of_distortion_lt hdist
  obtain ⟨-, hc, hi⟩ := CellConfig.transfer H.2 H'.2 hf hfη (δ := δ) (min_le_left _ _) hKc
    (hb.trans interior_subset) (by linarith)
  have hK' : interiorCell p H' = CellConfig.mapCell f (interiorCell p H) := interiorCell_eq hc hi
  refine ⟨⟨_, hc, hi⟩, ?_⟩
  show interiorCell p H' ∈ V
  rw [hK']
  refine hρV ?_
  rw [mem_ball, TopologicalSpace.NonemptyCompacts.dist_eq, CellConfig.coe_mapCell_eq_image]
  have hle : hausdorffDist (f '' (interiorCell p H : Set Plane)) (interiorCell p H : Set Plane) ≤
      min (δ / 2) (ρ / 2) := by
    refine hausdorffDist_le_of_mem_dist hη.le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, by rw [dist_comm]; exact (hfη y).le⟩
    · intro y hy
      exact ⟨f y, mem_image_of_mem f hy, (hfη y).le⟩
  calc _ ≤ min (δ / 2) (ρ / 2) := hle
    _ ≤ ρ / 2 := min_le_right _ _
    _ < ρ := half_lt_self hρ

theorem measurable_interiorCell (p : Plane) : Measurable (interiorCell p) :=
  measurable_of_isOpen_inter_preimage (isOpen_interiorSet p)
    (fun _ hV => isOpen_interiorSet_inter_preimage p hV) (fun _ hH => interiorCell_of_notMem hH)

/-! ### The conductance between two interior cells -/

/-- The conductance between the cells containing `p₁` and `p₂` in their interiors (`0` when one of
them does not exist). -/
noncomputable def pairCond (p₁ p₂ : Plane) (H : GMSSpace) : ℝ :=
  open Classical in
  if H ∈ interiorSet p₁ ∩ interiorSet p₂ then H.1.c (interiorCell p₁ H) (interiorCell p₂ H)
  else 0

/-- **Continuity of the conductance** on `interiorSet p₁ ∩ interiorSet p₂`. -/
theorem isOpen_inter_preimage_pairCond (p₁ p₂ : Plane) {V : Set ℝ} (hV : IsOpen V) :
    IsOpen ((interiorSet p₁ ∩ interiorSet p₂) ∩ pairCond p₁ p₂ ⁻¹' V) := by
  refine isOpen_of_forall_dCC fun H hH => ?_
  obtain ⟨⟨hH₁, hH₂⟩, hHV⟩ := hH
  obtain ⟨hK₁c, hK₁i⟩ := interiorCell_spec hH₁
  obtain ⟨hK₂c, hK₂i⟩ := interiorCell_spec hH₂
  have hval : pairCond p₁ p₂ H = H.1.c (interiorCell p₁ H) (interiorCell p₂ H) := by
    unfold pairCond
    rw [if_pos ⟨hH₁, hH₂⟩]
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV _ hHV
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 isOpen_interior p₁ hK₁i
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.isOpen_iff.1 isOpen_interior p₂ hK₂i
  have hn₁ := norm_nonneg p₁
  have hn₂ := norm_nonneg p₂
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hη : 0 < min (min δ₁ δ₂ / 2) ρ := lt_min (half_pos hδ) hρ
  obtain ⟨ε, hε, hspec⟩ := CellConfig.exists_admissible_of_dCC_lt
    (R := ‖p₁‖ + ‖p₂‖ + min δ₁ δ₂ + 1) (η := min (min δ₁ δ₂ / 2) ρ) (by linarith) hη
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨r, hRr, f, hf, hdist⟩ := hspec H.1 H'.1 hH'
  have hfη := CellConfig.dist_lt_of_distortion_lt hdist
  obtain ⟨hK₁r, hc₁, hi₁⟩ := CellConfig.transfer H.2 H'.2 hf hfη (δ := min δ₁ δ₂)
    (min_le_left _ _) hK₁c
    ((ball_subset_ball (min_le_left _ _)).trans (hb₁.trans interior_subset)) (by linarith)
  obtain ⟨hK₂r, hc₂, hi₂⟩ := CellConfig.transfer H.2 H'.2 hf hfη (δ := min δ₁ δ₂)
    (min_le_left _ _) hK₂c
    ((ball_subset_ball (min_le_right _ _)).trans (hb₂.trans interior_subset)) (by linarith)
  have hH'₁ : H' ∈ interiorSet p₁ := ⟨_, hc₁, hi₁⟩
  have hH'₂ : H' ∈ interiorSet p₂ := ⟨_, hc₂, hi₂⟩
  have hval' : pairCond p₁ p₂ H' = H'.1.c (CellConfig.mapCell f (interiorCell p₁ H))
      (CellConfig.mapCell f (interiorCell p₂ H)) := by
    unfold pairCond
    rw [if_pos ⟨hH'₁, hH'₂⟩, interiorCell_eq hc₁ hi₁, interiorCell_eq hc₂ hi₂]
  refine ⟨⟨hH'₁, hH'₂⟩, ?_⟩
  show pairCond p₁ p₂ H' ∈ V
  apply hρV
  rw [mem_ball, hval', hval, Real.dist_eq]
  by_cases hadj : H.1.Adj (interiorCell p₁ H) (interiorCell p₂ H)
  · rw [abs_sub_comm]
    exact (CellConfig.abs_sub_lt_of_distortion_lt hη hdist hK₁r hK₂r hadj).trans_le
      (min_le_right _ _)
  · have h0 : H.1.c (interiorCell p₁ H) (interiorCell p₂ H) = 0 :=
      le_antisymm (not_lt.1 hadj) (H.2.c_nonneg _ _)
    have h0' : H'.1.c (CellConfig.mapCell f (interiorCell p₁ H))
        (CellConfig.mapCell f (interiorCell p₂ H)) = 0 := by
      refine le_antisymm (not_lt.1 ?_) (H'.2.c_nonneg _ _)
      intro hadj'
      apply hadj
      have h := hf.2.2.2 _ (hf.1 _ hK₁r) _ (hf.1 _ hK₂r) hadj'
      rwa [CellConfig.mapCell_symm_mapCell, CellConfig.mapCell_symm_mapCell] at h
    rw [h0, h0', sub_zero, abs_zero]
    exact hρ

theorem measurable_pairCond (p₁ p₂ : Plane) : Measurable (pairCond p₁ p₂) := by
  refine measurable_of_isOpen_inter_preimage
    ((isOpen_interiorSet p₁).inter (isOpen_interiorSet p₂))
    (fun _ hV => isOpen_inter_preimage_pairCond p₁ p₂ hV) (y₀ := 0) fun H hH => ?_
  unfold pairCond
  rw [if_neg hH]

/-! ### The label events -/

/-- The configurations having a cell whose least rational interior label is `n`. -/
def labelSet (n : ℕ) : Set GMSSpace := {H | ∃ K ∈ H.1.cells, Code.LeastInteriorLabel K n}

theorem labelSet_subset (n : ℕ) : labelSet n ⊆ interiorSet (Code.rationalPoint n) :=
  fun _ ⟨K, hK, hn, _⟩ => ⟨K, hK, hn⟩

theorem labelSet_eq (n : ℕ) :
    labelSet n = interiorSet (Code.rationalPoint n) ∩
      ⋂ m : Fin n, (commonInteriorSet (Code.rationalPoint n) (Code.rationalPoint m))ᶜ := by
  ext H
  simp only [mem_inter_iff, mem_iInter, mem_compl_iff]
  constructor
  · rintro ⟨K, hK, hn, hlt⟩
    refine ⟨⟨K, hK, hn⟩, fun m hm => ?_⟩
    obtain ⟨K', hK', hn', hm'⟩ := hm
    have hKK' : K' = K := CellConfig.eq_of_interior_mem H.2 hK' hK hn' hn
    rw [hKK'] at hm'
    exact hlt m m.2 hm'
  · rintro ⟨⟨K, hK, hn⟩, hnot⟩
    exact ⟨K, hK, hn, fun m hm hmK => hnot ⟨m, hm⟩ ⟨K, hK, hn, hmK⟩⟩

theorem measurableSet_labelSet (n : ℕ) : MeasurableSet (labelSet n) := by
  rw [labelSet_eq]
  exact (isOpen_interiorSet _).measurableSet.inter
    (MeasurableSet.iInter fun _ => (isOpen_commonInteriorSet _ _).measurableSet.compl)

/-! ### The coordinates of the code -/

open Classical in
theorem slot_eq (H : GMSSpace) (n : ℕ) :
    H.1.slot n =
      if H ∈ labelSet n then some (interiorCell (Code.rationalPoint n) H) else none := by
  unfold CellConfig.slot
  by_cases h : ∃ K ∈ H.1.cells, Code.LeastInteriorLabel K n
  · have hH : H ∈ labelSet n := h
    rw [dif_pos h, if_pos hH]
    exact congrArg some (interiorCell_eq h.choose_spec.1 h.choose_spec.2.1).symm
  · have hH : H ∉ labelSet n := h
    rw [dif_neg h, if_neg hH]

open Classical in
theorem codeCond_eq (H : GMSSpace) (n m : ℕ) :
    H.1.codeCond n m =
      if H ∈ labelSet n ∧ H ∈ labelSet m then
        pairCond (Code.rationalPoint n) (Code.rationalPoint m) H
      else 0 := by
  unfold CellConfig.codeCond
  rw [slot_eq H n, slot_eq H m]
  by_cases h₁ : H ∈ labelSet n <;> by_cases h₂ : H ∈ labelSet m
  · rw [if_pos h₁, if_pos h₂, if_pos ⟨h₁, h₂⟩]
    unfold pairCond
    rw [if_pos ⟨labelSet_subset n h₁, labelSet_subset m h₂⟩]
  · rw [if_pos h₁, if_neg h₂, if_neg fun h => h₂ h.2]
  · rw [if_neg h₁, if_pos h₂, if_neg fun h => h₁ h.1]
  · rw [if_neg h₁, if_neg h₂, if_neg fun h => h₁ h.1]

theorem measurable_slot (n : ℕ) : Measurable fun H : GMSSpace => H.1.slot n := by
  classical
  have h : (fun H : GMSSpace => H.1.slot n) = fun H =>
      if H ∈ labelSet n then some (interiorCell (Code.rationalPoint n) H) else none :=
    funext fun H => slot_eq H n
  rw [h]
  exact Measurable.ite (measurableSet_labelSet n)
    (CanonicalSimilarity.measurable_someCell.comp (measurable_interiorCell _)) measurable_const

theorem measurable_codeCond (n m : ℕ) : Measurable fun H : GMSSpace => H.1.codeCond n m := by
  classical
  have h : (fun H : GMSSpace => H.1.codeCond n m) = fun H =>
      if H ∈ labelSet n ∧ H ∈ labelSet m then
        pairCond (Code.rationalPoint n) (Code.rationalPoint m) H
      else 0 :=
    funext fun H => codeCond_eq H n m
  rw [h]
  exact Measurable.ite ((measurableSet_labelSet n).inter (measurableSet_labelSet m))
    (measurable_pairCond _ _) measurable_const

/-- **The labelled coding is measurable** from GMS's `d^CC`-Borel σ-algebra to the product
σ-algebra of `Code.RawCode`. -/
theorem measurable_codeMap : Measurable codeMap := by
  show Measurable fun H : GMSSpace => ((fun n => H.1.slot n), fun n m => H.1.codeCond n m)
  exact (Measurable.of_eval fun n => measurable_slot n).prodMk
    (Measurable.of_eval fun n => Measurable.of_eval fun m => measurable_codeCond n m)

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.measurable_interiorCell
assert_no_sorry ReflectedGMS.GMS.measurable_pairCond
assert_no_sorry ReflectedGMS.GMS.measurableSet_labelSet
assert_no_sorry ReflectedGMS.GMS.measurable_slot
assert_no_sorry ReflectedGMS.GMS.measurable_codeCond
assert_no_sorry ReflectedGMS.GMS.measurable_codeMap

#print axioms ReflectedGMS.GMS.measurable_slot
#print axioms ReflectedGMS.GMS.measurable_codeCond
#print axioms ReflectedGMS.GMS.measurable_codeMap
