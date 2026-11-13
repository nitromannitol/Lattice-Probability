/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.CodingValid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingDef
import LatticeProb.Bonanno.ReflectedGMS.Environment.CodeGeneralValid
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralGMSSpecialization
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalRelabel
import Mathlib.Util.AssertNoSorry

/-!
# Validity of the labelled coding of a GMS cell configuration

For a GMS cell configuration `H` (`CellConfig.IsCellConfiguration`, GMS Definition 1.15) this file
proves that its labelled code `H.code` (`GMS/CodingDef.lean`) is a legitimate code of the
reflected-walk development:

* `slot_eq_some_iff` — slot `n` holds exactly the cell whose least rational interior label is `n`
  (at most one cell has a given rational point in its interior, since distinct cells meet in a
  Lebesgue-null set; every cell has a label, since its interior is nonempty);
* `rawAdmissible_code`, `finiteRows_code`, `canonicalLabels_code` — admissible conductances, finite
  rows (spatial local finiteness plus "adjacent cells intersect"), canonical labels;
* `cellEquiv` — the active labels are in bijection with the cells, with `coe_cellEquiv` and
  `code_cond` identifying cells and conductances;
* `gmsGeometry_code` — with GMS's connectedness along (nondegenerate) lines, the decoded
  configuration satisfies `GMSGeometry`; degenerate (one-point) segments are handled by the
  manuscript's argument (`work/general/manuscript-text.txt`, lines 70–73): a short nondegenerate
  segment through the point meets exactly the cells containing the point;
* `validGMS_code`, `validGeneral_code`, `valid_code`;
* the similarity compatibility `isCellConfiguration_similarity`, `lineConnected_similarity`,
  `exists_relabel_code` and its two corollaries `GeneralLaws.IsSimilarity`/`EnvironmentLaws.IsSimilarity`.

The converse "general validity of the code ⇒ GMS line connectivity" is **not** proved: `ValidGeneral`
only gives (LCS) off *some* closed `H¹`-null set, and removing that set requires a genuine argument.
-/

set_option autoImplicit false

open MeasureTheory Set Topology

namespace ReflectedGMS.GMS

namespace CellConfig

variable {H : CellConfig}

/-! ## Labels -/

/-- The conductance of a cell with itself vanishes. -/
theorem c_self_eq_zero (hH : H.IsCellConfiguration) (K : Cell) : H.c K K = 0 :=
  le_antisymm (not_lt.mp fun h => hH.adj_ne K K h rfl) (hH.c_nonneg K K)

/-- Two cells of a configuration sharing an interior point coincide. -/
theorem eq_of_mem_interior (hH : H.IsCellConfiguration) {K K' : Cell} (hK : K ∈ H.cells)
    (hK' : K' ∈ H.cells) {z : Plane} (hz : z ∈ interior (K : Set Plane))
    (hz' : z ∈ interior (K' : Set Plane)) : K = K' := by
  by_contra hne
  have hpos : 0 < volume (interior (K : Set Plane) ∩ interior (K' : Set Plane)) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨z, hz, hz'⟩
  have hle : volume (interior (K : Set Plane) ∩ interior (K' : Set Plane)) ≤
      volume ((K : Set Plane) ∩ K') :=
    measure_mono (inter_subset_inter interior_subset interior_subset)
  rw [hH.volume_inter K hK K' hK' hne] at hle
  exact (not_le.mpr hpos) hle

/-- At most one cell carries a given least rational interior label. -/
theorem eq_of_leastInteriorLabel (hH : H.IsCellConfiguration) {K K' : Cell} (hK : K ∈ H.cells)
    (hK' : K' ∈ H.cells) {n : ℕ} (h : Code.LeastInteriorLabel K n)
    (h' : Code.LeastInteriorLabel K' n) : K = K' :=
  eq_of_mem_interior hH hK hK' h.1 h'.1

/-- **Slot `n` holds exactly the cell whose least rational interior label is `n`.** -/
theorem slot_eq_some_iff (hH : H.IsCellConfiguration) {n : ℕ} {K : Cell} :
    H.slot n = some K ↔ K ∈ H.cells ∧ Code.LeastInteriorLabel K n := by
  unfold slot
  constructor
  · intro hs
    by_cases h : ∃ K ∈ H.cells, Code.LeastInteriorLabel K n
    · rw [dif_pos h] at hs
      obtain rfl := Option.some_inj.mp hs
      exact h.choose_spec
    · rw [dif_neg h] at hs
      cases hs
  · rintro ⟨hK, hl⟩
    have h : ∃ K ∈ H.cells, Code.LeastInteriorLabel K n := ⟨K, hK, hl⟩
    rw [dif_pos h]
    exact congrArg some (eq_of_leastInteriorLabel hH h.choose_spec.1 hK h.choose_spec.2 hl)

/-- A slot is empty exactly when no cell has that least label. -/
theorem slot_eq_none_iff (hH : H.IsCellConfiguration) {n : ℕ} :
    H.slot n = none ↔ ∀ K ∈ H.cells, ¬ Code.LeastInteriorLabel K n := by
  constructor
  · intro hs K hK hl
    rw [(slot_eq_some_iff hH).2 ⟨hK, hl⟩] at hs
    cases hs
  · intro h
    cases hs : H.slot n with
    | none => rfl
    | some K => exact absurd ((slot_eq_some_iff hH).1 hs).2 (h K ((slot_eq_some_iff hH).1 hs).1)

/-- The label of a cell: its least rational interior-hit index. -/
noncomputable def label (hH : H.IsCellConfiguration) (K : H.cells) : ℕ :=
  Code.leastInteriorLabel K (hH.interior_nonempty K K.2)

theorem leastInteriorLabel_label (hH : H.IsCellConfiguration) (K : H.cells) :
    Code.LeastInteriorLabel K (label hH K) :=
  Code.leastInteriorLabel_spec _ _

theorem slot_label (hH : H.IsCellConfiguration) (K : H.cells) :
    H.slot (label hH K) = some (K : Cell) :=
  (slot_eq_some_iff hH).2 ⟨K.2, leastInteriorLabel_label hH K⟩

/-- The slot of an active label holds its decoded cell. -/
theorem slot_val (v : Code.Vertex H.code) : H.slot v.val = some (Code.cell H.code v) :=
  (Option.some_get v.property).symm

theorem cell_mem_cells (hH : H.IsCellConfiguration) (v : Code.Vertex H.code) :
    Code.cell H.code v ∈ H.cells :=
  ((slot_eq_some_iff hH).1 (slot_val v)).1

/-! ## The conductance array -/

theorem codeCond_of_some {n m : ℕ} {K K' : Cell} (hn : H.slot n = some K)
    (hm : H.slot m = some K') : H.codeCond n m = H.c K K' := by
  unfold codeCond
  rw [hn, hm]

theorem codeCond_of_none_left {n m : ℕ} (hn : H.slot n = none) : H.codeCond n m = 0 := by
  unfold codeCond
  rw [hn]

theorem codeCond_of_none_right {n m : ℕ} (hm : H.slot m = none) : H.codeCond n m = 0 := by
  unfold codeCond
  rw [hm]
  cases H.slot n <;> rfl

/-- **The code's conductances are admissible.** -/
theorem rawAdmissible_code (hH : H.IsCellConfiguration) : Code.RawAdmissible H.code where
  symm n m := by
    show H.codeCond n m = H.codeCond m n
    unfold codeCond
    cases H.slot n with
    | none => cases H.slot m <;> rfl
    | some K =>
      cases H.slot m with
      | none => rfl
      | some K' => exact hH.c_symm K K'
  nonneg n m := by
    show 0 ≤ H.codeCond n m
    unfold codeCond
    cases H.slot n with
    | none => cases H.slot m <;> exact le_rfl
    | some K =>
      cases H.slot m with
      | none => exact le_rfl
      | some K' => exact hH.c_nonneg K K'
  self n := by
    show H.codeCond n n = 0
    unfold codeCond
    cases H.slot n with
    | none => rfl
    | some K => exact c_self_eq_zero hH K
  absent n m h := by
    show H.codeCond n m = 0
    rcases h with h | h
    · exact codeCond_of_none_left h
    · exact codeCond_of_none_right h

/-- The family of cells, indexed by the cells, is locally finite. -/
theorem locallyFinite_cells (hH : H.IsCellConfiguration) :
    LocallyFinite (fun K : H.cells => ((K : Cell) : Set Plane)) := by
  intro z
  obtain ⟨U, hU, hfin⟩ := hH.locallyFinite z
  exact ⟨U, hU, (hfin.preimage Subtype.val_injective.injOn).subset fun K hK => ⟨K.2, hK⟩⟩

/-- A compact set meets only finitely many cells. -/
theorem finite_restrict_of_isCompact (hH : H.IsCellConfiguration) {A : Set Plane}
    (hA : IsCompact A) : (H.restrict A).Finite := by
  refine (((locallyFinite_cells hH).finite_nonempty_inter_compact hA).image Subtype.val).subset ?_
  rintro K ⟨hK, hKA⟩
  exact ⟨⟨K, hK⟩, hKA, rfl⟩

/-- The labels whose slot holds a given cell form a subsingleton. -/
theorem subsingleton_slot_eq (hH : H.IsCellConfiguration) (K : Cell) :
    {m : ℕ | H.slot m = some K}.Subsingleton := by
  intro m hm m' hm'
  exact Code.LeastInteriorLabel.unique ((slot_eq_some_iff hH).1 hm).2
    ((slot_eq_some_iff hH).1 hm').2

/-- **The code has finite rows**: a cell has finitely many neighbours, since its neighbours meet it
and only finitely many cells meet a compact set. -/
theorem finiteRows_code (hH : H.IsCellConfiguration) : Code.FiniteRows H.code := by
  intro n
  show (Function.support (H.codeCond n)).Finite
  cases hn : H.slot n with
  | none =>
    refine Set.finite_empty.subset ?_
    intro m hm
    exact hm (codeCond_of_none_left hn)
  | some K =>
    refine ((finite_restrict_of_isCompact hH K.isCompact).biUnion
      fun K' _ => (subsingleton_slot_eq hH K').finite).subset ?_
    intro m hm0
    have hm : H.codeCond n m ≠ 0 := hm0
    cases hm' : H.slot m with
    | none => exact absurd (codeCond_of_none_right hm') hm
    | some K' =>
      rw [codeCond_of_some hn hm'] at hm
      have hpos : H.Adj K K' := lt_of_le_of_ne (hH.c_nonneg K K') (Ne.symm hm)
      refine Set.mem_biUnion (x := K') ⟨(hH.adj_mem K K' hpos).2, ?_⟩ hm'
      rw [Set.inter_comm]
      exact hH.adj_inter K K' hpos

/-- **The code's labels are canonical.** -/
theorem canonicalLabels_code (hH : H.IsCellConfiguration) : Code.CanonicalLabels H.code :=
  fun v => ((slot_eq_some_iff hH).1 (slot_val v)).2

/-! ## Active labels and cells -/

/-- **The active labels of the code are in bijection with the cells.** -/
noncomputable def cellEquiv (hH : H.IsCellConfiguration) : Code.Vertex H.code ≃ H.cells where
  toFun v := ⟨Code.cell H.code v, cell_mem_cells hH v⟩
  invFun K := ⟨label hH K, by
    show (H.slot (label hH K)).isSome
    rw [slot_label hH K]
    rfl⟩
  left_inv v := Subtype.ext (Code.LeastInteriorLabel.unique
    (leastInteriorLabel_label hH ⟨Code.cell H.code v, cell_mem_cells hH v⟩)
    (canonicalLabels_code hH v))
  right_inv K := Subtype.ext (Option.some_inj.mp ((slot_val _).symm.trans (slot_label hH K)))

@[simp] theorem coe_cellEquiv (hH : H.IsCellConfiguration) (v : Code.Vertex H.code) :
    ((cellEquiv hH v : H.cells) : Cell) = Code.cell H.code v := rfl

@[simp] theorem cellEquiv_symm_val (hH : H.IsCellConfiguration) (K : H.cells) :
    ((cellEquiv hH).symm K).val = label hH K := rfl

theorem cell_cellEquiv_symm (hH : H.IsCellConfiguration) (K : H.cells) :
    Code.cell H.code ((cellEquiv hH).symm K) = K := by
  rw [← coe_cellEquiv hH, Equiv.apply_symm_apply]

/-- **The conductances of the code are those of the configuration.** -/
theorem code_cond (hH : H.IsCellConfiguration) (v w : Code.Vertex H.code) :
    H.code.2 v.val w.val = H.c (cellEquiv hH v) (cellEquiv hH w) :=
  codeCond_of_some (slot_val v) (slot_val w)

/-- The raw configuration of the code. -/
theorem rawConfig_c (hH : H.IsCellConfiguration) (v w : Code.Vertex H.code) :
    (Code.rawConfig H.code (rawAdmissible_code hH)).c v w =
      H.c (cellEquiv hH v) (cellEquiv hH w) :=
  code_cond hH v w

theorem rawConfig_cell (hH : H.IsCellConfiguration) (v : Code.Vertex H.code) :
    (Code.rawConfig H.code (rawAdmissible_code hH)).cell v = (cellEquiv hH v : Cell) := rfl

/-! ## Geometry of the decoded configuration -/

/-- **Transfer of induced connectivity**: if the cells meeting `A` are exactly those meeting `B` and
GMS's induced graph on `B` is preconnected, then the decoded configuration's induced graph on `A`
is preconnected. -/
theorem inducedConnected_rawConfig (hH : H.IsCellConfiguration) {A B : Set Plane}
    (hAB : ∀ K ∈ H.cells, ((K : Set Plane) ∩ A).Nonempty ↔ ((K : Set Plane) ∩ B).Nonempty)
    (hB : (H.inducedGraph B).Preconnected) :
    (Code.rawConfig H.code (rawAdmissible_code hH)).InducedConnected A := by
  let C := Code.rawConfig H.code (rawAdmissible_code hH)
  let f : H.inducedGraph B →g C.graph.induce {v | C.Hits A v} :=
    { toFun := fun K => ⟨(cellEquiv hH).symm K.1, by
        show (((Code.cell H.code ((cellEquiv hH).symm K.1)) : Set Plane) ∩ A).Nonempty
        rw [cell_cellEquiv_symm]
        exact (hAB _ K.1.2).2 K.2⟩
      map_rel' := fun {K K'} h => by
        have h' : H.graph.Adj K.1 K'.1 := h
        show 0 < H.code.2 ((cellEquiv hH).symm K.1).val ((cellEquiv hH).symm K'.1).val
        rw [code_cond hH]
        simp only [Equiv.apply_symm_apply]
        exact h'.2.1 }
  refine hB.map f ?_
  rintro ⟨v, hv⟩
  exact ⟨⟨cellEquiv hH v, (hAB _ (cell_mem_cells hH v)).1 hv⟩,
    Subtype.ext ((cellEquiv hH).symm_apply_apply v)⟩

/-- Near any point `z`, only the cells containing `z` are met: some closed ball around `z` meets no
cell avoiding `z` (spatial local finiteness plus compactness of the cells). -/
theorem exists_pos_mem_of_inter_closedBall (hH : H.IsCellConfiguration) (z : Plane) :
    ∃ δ > 0, ∀ K ∈ H.cells, ((K : Set Plane) ∩ Metric.closedBall z δ).Nonempty →
      z ∈ (K : Set Plane) := by
  obtain ⟨U, hU, hfin⟩ := hH.locallyFinite z
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hFfin : {K ∈ H.restrict U | z ∉ (K : Set Plane)}.Finite := hfin.subset fun K hK => hK.1
  have hclosed : IsClosed (⋃ K ∈ {K ∈ H.restrict U | z ∉ (K : Set Plane)}, (K : Set Plane)) :=
    hFfin.isClosed_biUnion fun K _ => K.isCompact.isClosed
  have hzn : z ∉ ⋃ K ∈ {K ∈ H.restrict U | z ∉ (K : Set Plane)}, (K : Set Plane) := by
    simp only [Set.mem_iUnion]
    rintro ⟨K, hK, hzK⟩
    exact hK.2 hzK
  obtain ⟨δ', hδ', hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hzn
  refine ⟨min ε δ' / 2, half_pos (lt_min hε hδ'), ?_⟩
  rintro K hK ⟨w, hwK, hw⟩
  by_contra hzK
  have hwz : dist w z ≤ min ε δ' / 2 := Metric.mem_closedBall.mp hw
  have hmin : min ε δ' / 2 < min ε δ' := half_lt_self (lt_min hε hδ')
  have hwε : w ∈ Metric.ball z ε := Metric.mem_ball.mpr
    (lt_of_le_of_lt hwz (lt_of_lt_of_le hmin (min_le_left _ _)))
  have hwδ : w ∈ Metric.ball z δ' := Metric.mem_ball.mpr
    (lt_of_le_of_lt hwz (lt_of_lt_of_le hmin (min_le_right _ _)))
  have hKU : K ∈ H.restrict U := ⟨hK, w, hwK, hεU hwε⟩
  exact hball hwδ (Set.mem_biUnion (x := K) ⟨hKU, hzK⟩ hwK)

/-- A one-point set and a set around it inside a small closed ball are met by the same cells. -/
theorem hits_iff_of_point {z : Plane} {δ : ℝ}
    (hball : ∀ K ∈ H.cells, ((K : Set Plane) ∩ Metric.closedBall z δ).Nonempty →
      z ∈ (K : Set Plane))
    {A B : Set Plane} (hA : ∀ w ∈ A, w = z) (hzA : z ∈ A) (hzB : z ∈ B)
    (hB : B ⊆ Metric.closedBall z δ) :
    ∀ K ∈ H.cells, ((K : Set Plane) ∩ A).Nonempty ↔ ((K : Set Plane) ∩ B).Nonempty := by
  intro K hK
  constructor
  · rintro ⟨w, hwK, hw⟩
    obtain rfl := hA w hw
    exact ⟨w, hwK, hzB⟩
  · rintro ⟨w, hwK, hw⟩
    exact ⟨z, hball K hK ⟨w, hwK, hB hw⟩, hzA⟩

theorem dist_le_abs_add_abs (w z : Plane) : dist w z ≤ |w 0 - z 0| + |w 1 - z 1| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg (w 0 - z 0)) (abs_nonneg (w 1 - z 1)),
    sq_abs (w 0 - z 0), sq_abs (w 1 - z 1)]

theorem eq_toLp_of_coord {w : Plane} {p q : ℝ} (h0 : w 0 = p) (h1 : w 1 = q) :
    w = (WithLp.toLp 2 ![p, q] : Plane) := by
  ext i
  fin_cases i <;> simp [h0, h1]

theorem toLp_coord_zero (p q : ℝ) : (WithLp.toLp 2 ![p, q] : Plane) 0 = p := by simp

theorem toLp_coord_one (p q : ℝ) : (WithLp.toLp 2 ![p, q] : Plane) 1 = q := by simp

/-- **Segment condition, horizontal**: GMS's condition for nondegenerate segments gives it for all
real endpoints (`a > b`: empty; `a = b`: a point, through a short nondegenerate segment). -/
theorem inducedConnected_horizontal (hH : H.IsCellConfiguration) (hL : H.LineConnected)
    (a b y : ℝ) :
    (Code.rawConfig H.code (rawAdmissible_code hH)).InducedConnected (horizontal a b y) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact inducedConnected_rawConfig hH (fun _ _ => Iff.rfl) (hL.1 a b y hab).preconnected
  · obtain ⟨δ, hδ, hball⟩ := exists_pos_mem_of_inter_closedBall hH (WithLp.toLp 2 ![a, y])
    refine inducedConnected_rawConfig hH (B := horizontal (a - δ) (a + δ) y)
      (hits_iff_of_point hball ?_ ?_ ?_ ?_) (hL.1 _ _ y (by linarith)).preconnected
    · rintro w ⟨h1, h2, h3⟩
      exact eq_toLp_of_coord (le_antisymm h2 h1) h3
    · exact ⟨(toLp_coord_zero a y).ge, (toLp_coord_zero a y).le, toLp_coord_one a y⟩
    · refine ⟨?_, ?_, toLp_coord_one a y⟩ <;> rw [toLp_coord_zero] <;> linarith
    · rintro w ⟨h1, h2, h3⟩
      rw [Metric.mem_closedBall]
      refine (dist_le_abs_add_abs _ _).trans ?_
      rw [toLp_coord_zero, toLp_coord_one, h3, sub_self, abs_zero, add_zero, abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
  · intro v
    exfalso
    obtain ⟨w, -, h1, h2, -⟩ := v.2
    linarith

/-- **Segment condition, vertical.** -/
theorem inducedConnected_vertical (hH : H.IsCellConfiguration) (hL : H.LineConnected)
    (x a b : ℝ) :
    (Code.rawConfig H.code (rawAdmissible_code hH)).InducedConnected (vertical x a b) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact inducedConnected_rawConfig hH (fun _ _ => Iff.rfl) (hL.2 x a b hab).preconnected
  · obtain ⟨δ, hδ, hball⟩ := exists_pos_mem_of_inter_closedBall hH (WithLp.toLp 2 ![x, a])
    refine inducedConnected_rawConfig hH (B := vertical x (a - δ) (a + δ))
      (hits_iff_of_point hball ?_ ?_ ?_ ?_) (hL.2 x _ _ (by linarith)).preconnected
    · rintro w ⟨h1, h2, h3⟩
      exact eq_toLp_of_coord h1 (le_antisymm h3 h2)
    · exact ⟨toLp_coord_zero x a, (toLp_coord_one x a).ge, (toLp_coord_one x a).le⟩
    · refine ⟨toLp_coord_zero x a, ?_, ?_⟩ <;> rw [toLp_coord_one] <;> linarith
    · rintro w ⟨h1, h2, h3⟩
      rw [Metric.mem_closedBall]
      refine (dist_le_abs_add_abs _ _).trans ?_
      rw [toLp_coord_zero, toLp_coord_one, h1, sub_self, abs_zero, zero_add, abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
  · intro v
    exfalso
    obtain ⟨w, -, -, h1, h2⟩ := v.2
    linarith

/-- **The decoded configuration of a line-connected GMS configuration satisfies `GMSGeometry`.** -/
theorem gmsGeometry_code (hH : H.IsCellConfiguration) (hL : H.LineConnected) :
    GMSGeometry (Code.rawConfig H.code (rawAdmissible_code hH)) := by
  refine ⟨fun v => hH.isConnected _ (cell_mem_cells hH v),
    fun v => hH.interior_nonempty _ (cell_mem_cells hH v), ?_, ?_, ?_, ?_,
    ⟨inducedConnected_horizontal hH hL, inducedConnected_vertical hH hL⟩⟩
  · intro v w hvw
    exact hH.volume_inter _ (cell_mem_cells hH v) _ (cell_mem_cells hH w)
      fun h => hvw ((cellEquiv hH).injective (Subtype.ext h))
  · refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.mp (Set.eq_univ_iff_forall.mp hH.iUnion_eq_univ z)
    refine Set.mem_iUnion.mpr ⟨(cellEquiv hH).symm ⟨K, hK⟩, ?_⟩
    show z ∈ (Code.cell H.code ((cellEquiv hH).symm ⟨K, hK⟩) : Set Plane)
    rw [cell_cellEquiv_symm]
    exact hzK
  · exact (locallyFinite_cells hH).comp_injective (cellEquiv hH).injective
  · intro v w hvw
    have hpos : 0 < H.code.2 v.val w.val := hvw
    rw [code_cond hH] at hpos
    exact hH.adj_inter _ _ hpos

/-- **The code of a line-connected GMS configuration is a GMS code.** -/
theorem validGMS_code (hH : H.IsCellConfiguration) (hL : H.LineConnected) :
    Code.ValidGMS H.code :=
  ⟨rawAdmissible_code hH, gmsGeometry_code hH hL, canonicalLabels_code hH⟩

/-- **The code of a line-connected GMS configuration is a code of the general manuscript.** -/
theorem validGeneral_code (hH : H.IsCellConfiguration) (hL : H.LineConnected) :
    Code.ValidGeneral H.code :=
  Code.validGeneral_of_validGMS (validGMS_code hH hL)

/-- **The code of a line-connected GMS configuration is a valid code of the corpus.** -/
theorem valid_code (hH : H.IsCellConfiguration) (hL : H.LineConnected) : Code.Valid H.code :=
  Code.valid_of_validGeneral (validGeneral_code hH hL) (finiteRows_code hH)

/-! ## Similarities -/

section Similarity

variable (s : ℝ) (u : Plane) (hs : 0 < s)

theorem transformCell_eq_mapCell (K : Cell) :
    transformCell s u hs K = mapCell (positiveSimilarityHomeomorph s u hs) K := rfl

theorem coe_mapCell (f : Plane ≃ₜ Plane) (K : Cell) : ((mapCell f K : Cell) : Set Plane) = f '' K :=
  rfl

theorem mapCell_symm_transformCell (K : Cell) :
    mapCell (positiveSimilarityHomeomorph s u hs).symm (transformCell s u hs K) = K := by
  apply SetLike.coe_injective
  exact (positiveSimilarityHomeomorph s u hs).toEquiv.symm_image_image (K : Set Plane)

theorem transformCell_mapCell_symm (K : Cell) :
    transformCell s u hs (mapCell (positiveSimilarityHomeomorph s u hs).symm K) = K := by
  apply SetLike.coe_injective
  exact (positiveSimilarityHomeomorph s u hs).toEquiv.image_symm_image (K : Set Plane)

theorem mem_similarity_cells {K : Cell} :
    K ∈ (H.similarity s u hs).cells ↔
      mapCell (positiveSimilarityHomeomorph s u hs).symm K ∈ H.cells := by
  constructor
  · rintro ⟨K0, hK0, rfl⟩
    rw [mapCell_symm_transformCell]
    exact hK0
  · intro h
    exact ⟨_, h, transformCell_mapCell_symm s u hs K⟩

theorem transformCell_mem_similarity_cells {K : Cell} (hK : K ∈ H.cells) :
    transformCell s u hs K ∈ (H.similarity s u hs).cells :=
  ⟨K, hK, rfl⟩

theorem similarity_c_transformCell (K K' : Cell) :
    (H.similarity s u hs).c (transformCell s u hs K) (transformCell s u hs K') = H.c K K' := by
  show H.c (mapCell _ (transformCell s u hs K)) (mapCell _ (transformCell s u hs K')) = H.c K K'
  rw [mapCell_symm_transformCell, mapCell_symm_transformCell]

theorem transformCell_injective : Function.Injective (transformCell s u hs) := fun K K' h => by
  rw [← mapCell_symm_transformCell s u hs K, h, mapCell_symm_transformCell]

/-- **`C(H − z)` is again a cell configuration.** -/
theorem isCellConfiguration_similarity (hH : H.IsCellConfiguration) :
    (H.similarity s u hs).IsCellConfiguration where
  locallyFinite z := by
    obtain ⟨U, hU, hfin⟩ := hH.locallyFinite ((positiveSimilarityHomeomorph s u hs).symm z)
    refine ⟨(positiveSimilarityHomeomorph s u hs).symm ⁻¹' U,
      (positiveSimilarityHomeomorph s u hs).symm.continuous.continuousAt.preimage_mem_nhds hU,
      (hfin.image (transformCell s u hs)).subset ?_⟩
    rintro K ⟨⟨K0, hK0, rfl⟩, w, hwK, hwU⟩
    refine ⟨K0, ⟨hK0, ?_⟩, rfl⟩
    rw [coe_transformCell] at hwK
    obtain ⟨w0, hw0, rfl⟩ := hwK
    refine ⟨w0, hw0, ?_⟩
    have h := (positiveSimilarityHomeomorph s u hs).symm_apply_apply w0
    rw [Set.mem_preimage, ← coe_positiveSimilarityHomeomorph s u hs, h] at hwU
    exact hwU
  isConnected K hK := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [coe_transformCell]
    exact (hH.isConnected K0 hK0).image _
      (positiveSimilarityHomeomorph s u hs).continuous.continuousOn
  interior_nonempty K hK := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [interior_coe_transformCell]
    exact (hH.interior_nonempty K0 hK0).image _
  iUnion_eq_univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨K0, hK0, hz0⟩ := Set.mem_iUnion₂.mp
      (Set.eq_univ_iff_forall.mp hH.iUnion_eq_univ ((positiveSimilarityHomeomorph s u hs).symm z))
    refine Set.mem_iUnion₂.mpr ⟨transformCell s u hs K0, ⟨K0, hK0, rfl⟩, ?_⟩
    rw [coe_transformCell]
    exact ⟨_, hz0, positiveSimilarity_inverse_right s u z hs⟩
  volume_inter K hK K' hK' hne := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    obtain ⟨K0', hK0', rfl⟩ := hK'
    rw [coe_transformCell, coe_transformCell,
      ← Set.image_inter (f := positiveSimilarity s u) (positiveSimilarityHomeomorph s u hs).injective]
    exact volume_positiveSimilarity_image_eq_zero s u hs
      (hH.volume_inter K0 hK0 K0' hK0' fun h => hne (congrArg _ h))
  c_nonneg K K' := hH.c_nonneg _ _
  c_symm K K' := hH.c_symm _ _
  adj_mem K K' h := ⟨(mem_similarity_cells s u hs).2 (hH.adj_mem _ _ h).1,
    (mem_similarity_cells s u hs).2 (hH.adj_mem _ _ h).2⟩
  adj_ne K K' h hKK := hH.adj_ne _ _ h (congrArg _ hKK)
  adj_inter K K' h := by
    have h' := hH.adj_inter _ _ h
    rw [coe_mapCell, coe_mapCell,
      ← Set.image_inter (positiveSimilarityHomeomorph s u hs).symm.injective,
      Set.image_nonempty] at h'
    exact h'

/-- Connectivity of `H(C⁻¹ A)` gives connectivity of `C(H − z)(A)`. -/
theorem inducedGraph_connected_similarity {A : Set Plane}
    (h : (H.inducedGraph (positiveSimilarity s u ⁻¹' A)).Connected) :
    ((H.similarity s u hs).inducedGraph A).Connected := by
  let f : H.inducedGraph (positiveSimilarity s u ⁻¹' A) →g (H.similarity s u hs).inducedGraph A :=
    { toFun := fun K => ⟨⟨transformCell s u hs K.1.1, K.1.1, K.1.2, rfl⟩, by
          show ((transformCell s u hs K.1.1 : Set Plane) ∩ A).Nonempty
          rw [coe_transformCell, ← Set.image_inter_preimage, Set.image_nonempty]
          exact K.2⟩
      map_rel' := fun {K K'} hKK' => by
        have h' : H.graph.Adj K.1 K'.1 := hKK'
        refine ⟨fun heq => h'.1 (Subtype.ext (transformCell_injective s u hs
          (congrArg Subtype.val heq))), ?_, ?_⟩
        · show 0 < (H.similarity s u hs).c (transformCell s u hs K.1.1)
            (transformCell s u hs K'.1.1)
          rw [similarity_c_transformCell]
          exact h'.2.1
        · show 0 < (H.similarity s u hs).c (transformCell s u hs K'.1.1)
            (transformCell s u hs K.1.1)
          rw [similarity_c_transformCell]
          exact h'.2.2 }
  refine h.map f ?_
  rintro ⟨⟨K, ⟨K0, hK0, rfl⟩⟩, hKA⟩
  refine ⟨⟨⟨K0, hK0⟩, ?_⟩, rfl⟩
  show ((K0 : Set Plane) ∩ positiveSimilarity s u ⁻¹' A).Nonempty
  have hKA' : ((transformCell s u hs K0 : Set Plane) ∩ A).Nonempty := hKA
  rwa [coe_transformCell, ← Set.image_inter_preimage, Set.image_nonempty] at hKA'

/-- **Connectedness along lines is preserved by `H ↦ C(H − z)`**: a positive similarity maps
horizontal (vertical) segments to horizontal (vertical) segments. -/
theorem lineConnected_similarity (hL : H.LineConnected) :
    (H.similarity s u hs).LineConnected := by
  have hinv : 0 < s⁻¹ := inv_pos.mpr hs
  refine ⟨fun a b y hab => ?_, fun x a b hab => ?_⟩
  · apply inducedGraph_connected_similarity s u hs
    rw [preimage_positiveSimilarity_horizontal s u hs]
    exact hL.1 _ _ _ (by have := mul_lt_mul_of_pos_left hab hinv; linarith)
  · apply inducedGraph_connected_similarity s u hs
    rw [preimage_positiveSimilarity_vertical s u hs]
    exact hL.2 _ _ _ (by have := mul_lt_mul_of_pos_left hab hinv; linarith)

/-- The cells of `H` and of `C(H − z)` correspond through the similarity. -/
noncomputable def similarityCellEquiv : H.cells ≃ (H.similarity s u hs).cells where
  toFun K := ⟨transformCell s u hs K, K, K.2, rfl⟩
  invFun K := ⟨mapCell (positiveSimilarityHomeomorph s u hs).symm K,
    (mem_similarity_cells s u hs).1 K.2⟩
  left_inv K := Subtype.ext (mapCell_symm_transformCell s u hs K)
  right_inv K := Subtype.ext (transformCell_mapCell_symm s u hs K)

@[simp] theorem coe_similarityCellEquiv (K : H.cells) :
    ((similarityCellEquiv s u hs K : (H.similarity s u hs).cells) : Cell) =
      transformCell s u hs K := rfl

/-- **The codes of `H` and `C(H − z)` are related by a relabelling**: cells are transformed by
`z ↦ s(z − u)` and conductances are unchanged. -/
theorem exists_relabel_code (hH : H.IsCellConfiguration) :
    ∃ relabel : Code.Vertex H.code ≃ Code.Vertex (H.similarity s u hs).code,
      (∀ v, Code.cell (H.similarity s u hs).code (relabel v) =
          transformCell s u hs (Code.cell H.code v)) ∧
        ∀ v w, (H.similarity s u hs).code.2 (relabel v).val (relabel w).val =
          H.code.2 v.val w.val := by
  have hH' := isCellConfiguration_similarity s u hs hH
  refine ⟨((cellEquiv hH).trans (similarityCellEquiv s u hs)).trans (cellEquiv hH').symm,
    fun v => ?_, fun v w => ?_⟩
  · simp only [Equiv.trans_apply]
    rw [cell_cellEquiv_symm hH']
    rfl
  · simp only [Equiv.trans_apply]
    rw [code_cond hH', code_cond hH]
    simp only [Equiv.apply_symm_apply]
    exact similarity_c_transformCell s u hs _ _

/-- The similarity relation of the general manuscript holds between the codes of `H` and
`C(H − z)`. -/
theorem generalLaws_isSimilarity (hH : H.IsCellConfiguration) {e e' : Code.EnvGeneral}
    (he : e.val = H.code) (he' : e'.val = (H.similarity s u hs).code) :
    GeneralLaws.IsSimilarity s u hs e e' := by
  obtain ⟨r, hr⟩ := e
  obtain ⟨r', hr'⟩ := e'
  have he2 : r = H.code := he
  have he2' : r' = (H.similarity s u hs).code := he'
  subst he2 he2'
  obtain ⟨relabel, hcell, hc⟩ := exists_relabel_code s u hs hH
  exact ⟨relabel, hcell, hc⟩

/-- The similarity relation of the corpus holds between the codes of `H` and `C(H − z)`. -/
theorem environmentLaws_isSimilarity (hH : H.IsCellConfiguration) {e e' : Code.Env}
    (he : e.val = H.code) (he' : e'.val = (H.similarity s u hs).code) :
    EnvironmentLaws.IsSimilarity s u hs e e' := by
  obtain ⟨r, hr⟩ := e
  obtain ⟨r', hr'⟩ := e'
  have he2 : r = H.code := he
  have he2' : r' = (H.similarity s u hs).code := he'
  subst he2 he2'
  obtain ⟨relabel, hcell, hc⟩ := exists_relabel_code s u hs hH
  exact ⟨relabel, hcell, hc⟩

end Similarity

/-! ## The (FE) and walk quantities -/

section Quantities

variable (hH : H.IsCellConfiguration)

theorem diam_cellEquiv (v : Code.Vertex H.code) :
    Metric.diam ((cellEquiv hH v : Cell) : Set Plane) =
      Metric.diam ((Code.cell H.code v : Cell) : Set Plane) := rfl

theorem area_cellEquiv (v : Code.Vertex H.code) :
    area (cellEquiv hH v : Cell) =
      StatementIngredients.cellArea (Code.rawConfig H.code (rawAdmissible_code hH)).cellsOnly v :=
  rfl

theorem centroid_cellEquiv (v : Code.Vertex H.code) :
    centroid (cellEquiv hH v : Cell) =
      StatementIngredients.cellCentroid (Code.rawConfig H.code (rawAdmissible_code hH)).cellsOnly v :=
  rfl

theorem area_cellEquiv_decodeRaw (h : Code.AdmissibleConductance H.code) (v : Code.Vertex H.code) :
    area (cellEquiv hH v : Cell) = StatementIngredients.cellArea (Code.decodeRaw H.code h) v :=
  rfl

theorem centroid_cellEquiv_decodeRaw (h : Code.AdmissibleConductance H.code)
    (v : Code.Vertex H.code) :
    centroid (cellEquiv hH v : Cell) =
      StatementIngredients.cellCentroid (Code.decodeRaw H.code h) v :=
  rfl

/-- `π(H)` as a sum over the active labels. -/
theorem pi_cellEquiv (v : Code.Vertex H.code) :
    H.pi (cellEquiv hH v) = ∑' w : Code.Vertex H.code, H.code.2 v.val w.val := by
  unfold pi
  rw [← (cellEquiv hH).tsum_eq]
  simp only [code_cond hH]

/-- `π*(H)` as a sum over the active labels. -/
theorem piStar_cellEquiv (v : Code.Vertex H.code) :
    H.piStar (cellEquiv hH v) = ∑' w : Code.Vertex H.code, (H.code.2 v.val w.val)⁻¹ := by
  unfold piStar
  rw [← (cellEquiv hH).tsum_eq]
  simp only [code_cond hH]

theorem pi_cellEquiv_decodeRaw (h : Code.AdmissibleConductance H.code) (v : Code.Vertex H.code) :
    H.pi (cellEquiv hH v) = RootDensities.pi (Code.decodeRaw H.code h) v :=
  pi_cellEquiv hH v

theorem piStar_cellEquiv_decodeRaw (h : Code.AdmissibleConductance H.code)
    (v : Code.Vertex H.code) :
    H.piStar (cellEquiv hH v) = RootDensities.piStar (Code.decodeRaw H.code h) v :=
  piStar_cellEquiv hH v

include hH in
theorem finite_support_code_row (v : Code.Vertex H.code) :
    (Function.support fun w : Code.Vertex H.code => H.code.2 v.val w.val).Finite :=
  Code.locallyFiniteGraph_rawConfig (rawAdmissible_code hH) (finiteRows_code hH) v

/-- The extended sum `Σ c(H,H')` of the general manuscript's (FE) is `π(H)`. -/
theorem ofReal_pi_cellEquiv (v : Code.Vertex H.code) :
    ENNReal.ofReal (H.pi (cellEquiv hH v)) =
      ∑' w, ENNReal.ofReal ((Code.rawConfig H.code (rawAdmissible_code hH)).c v w) := by
  rw [pi_cellEquiv hH v]
  exact ENNReal.ofReal_tsum_of_nonneg (fun w => (rawAdmissible_code hH).nonneg _ _)
    (summable_of_hasFiniteSupport (finite_support_code_row hH v))

/-- The extended sum `Σ c(H,H')⁻¹` of the general manuscript's (FE) is `π*(H)`. -/
theorem ofReal_piStar_cellEquiv (v : Code.Vertex H.code) :
    ENNReal.ofReal (H.piStar (cellEquiv hH v)) =
      ∑' w, ENNReal.ofReal ((Code.rawConfig H.code (rawAdmissible_code hH)).c v w)⁻¹ := by
  rw [piStar_cellEquiv hH v]
  refine ENNReal.ofReal_tsum_of_nonneg (fun w => inv_nonneg.mpr ((rawAdmissible_code hH).nonneg _ _))
    (summable_of_hasFiniteSupport ((finite_support_code_row hH v).subset fun w hw => ?_))
  exact fun h0 => Function.mem_support.mp hw
    (show (H.code.2 v.val w.val)⁻¹ = 0 by rw [show H.code.2 v.val w.val = 0 from h0, inv_zero])

/-- **The (FE) integrand of the general manuscript at a label is GMS's integrand at its cell.** -/
theorem finiteEnergyDensity_rawConfig (v : Code.Vertex H.code) :
    GeneralLaws.finiteEnergyDensity (Code.rawConfig H.code (rawAdmissible_code hH)) v =
      ENNReal.ofReal (Metric.diam ((cellEquiv hH v : Cell) : Set Plane) ^ 2) /
          ENNReal.ofReal (area (cellEquiv hH v : Cell)) *
        (ENNReal.ofReal (H.pi (cellEquiv hH v)) + ENNReal.ofReal (H.piStar (cellEquiv hH v))) := by
  rw [ofReal_pi_cellEquiv hH v, ofReal_piStar_cellEquiv hH v]
  rfl

/-- **The (FE) integrand of the corpus at a label is GMS's integrand at its cell.** -/
theorem finiteEnergyDensity_decodeRaw (h : Code.AdmissibleConductance H.code)
    (v : Code.Vertex H.code) :
    RootDensities.finiteEnergyDensity (Code.decodeRaw H.code h) v =
      ENNReal.ofReal (Metric.diam ((cellEquiv hH v : Cell) : Set Plane) ^ 2) /
          ENNReal.ofReal (area (cellEquiv hH v : Cell)) *
        (ENNReal.ofReal (H.pi (cellEquiv hH v)) + ENNReal.ofReal (H.piStar (cellEquiv hH v))) := by
  rw [pi_cellEquiv_decodeRaw hH h v, piStar_cellEquiv_decodeRaw hH h v]
  rfl

end Quantities

end CellConfig

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.CellConfig.slot_eq_some_iff
assert_no_sorry ReflectedGMS.GMS.CellConfig.rawAdmissible_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.finiteRows_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.canonicalLabels_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.cellEquiv
assert_no_sorry ReflectedGMS.GMS.CellConfig.coe_cellEquiv
assert_no_sorry ReflectedGMS.GMS.CellConfig.code_cond
assert_no_sorry ReflectedGMS.GMS.CellConfig.gmsGeometry_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.validGMS_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.validGeneral_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.valid_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.isCellConfiguration_similarity
assert_no_sorry ReflectedGMS.GMS.CellConfig.lineConnected_similarity
assert_no_sorry ReflectedGMS.GMS.CellConfig.exists_relabel_code
assert_no_sorry ReflectedGMS.GMS.CellConfig.generalLaws_isSimilarity
assert_no_sorry ReflectedGMS.GMS.CellConfig.environmentLaws_isSimilarity
assert_no_sorry ReflectedGMS.GMS.CellConfig.finiteEnergyDensity_rawConfig
assert_no_sorry ReflectedGMS.GMS.CellConfig.finiteEnergyDensity_decodeRaw

#print axioms ReflectedGMS.GMS.CellConfig.slot_eq_some_iff
#print axioms ReflectedGMS.GMS.CellConfig.rawAdmissible_code
#print axioms ReflectedGMS.GMS.CellConfig.finiteRows_code
#print axioms ReflectedGMS.GMS.CellConfig.canonicalLabels_code
#print axioms ReflectedGMS.GMS.CellConfig.cellEquiv
#print axioms ReflectedGMS.GMS.CellConfig.code_cond
#print axioms ReflectedGMS.GMS.CellConfig.gmsGeometry_code
#print axioms ReflectedGMS.GMS.CellConfig.valid_code
#print axioms ReflectedGMS.GMS.CellConfig.validGeneral_code
#print axioms ReflectedGMS.GMS.CellConfig.isCellConfiguration_similarity
#print axioms ReflectedGMS.GMS.CellConfig.lineConnected_similarity
#print axioms ReflectedGMS.GMS.CellConfig.exists_relabel_code
#print axioms ReflectedGMS.GMS.CellConfig.generalLaws_isSimilarity
#print axioms ReflectedGMS.GMS.CellConfig.environmentLaws_isSimilarity
#print axioms ReflectedGMS.GMS.CellConfig.finiteEnergyDensity_rawConfig
#print axioms ReflectedGMS.GMS.CellConfig.finiteEnergyDensity_decodeRaw
