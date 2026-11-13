/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.CodingSing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.Statement
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint
import LatticeProb.Bonanno.ReflectedGMS.Environment.SingularWitnessFacts
import Mathlib.Util.AssertNoSorry

/-!
# The labelled coding of a configuration of the singular class `C_sing`

For an unmarked configuration `H` satisfying Definition 1.1 (i)–(iii) of the geometric-topology
revision (`GeomTop.IsSingConfiguration`), this file proves that its rational-label coding `H.code`
(`GMS/CodingDef.lean`) is a legitimate code of the general-cell development.  It is the
singular-class analogue of `GMS/CodingValid.lean`, whose label and similarity arguments use only
null intersections, nonempty interiors and the adjacency clauses, and so transfer verbatim; full
coverage and spatial local finiteness are replaced by a singular witness.

* **Labels** — `slot_eq_some_iff_sing`, `rawAdmissible_code_sing`, `canonicalLabels_code_sing`,
  `cellEquivSing` (active labels ≃ cells) with `coe_cellEquivSing` and `code_cond_sing`.
* **Validity** — `validGeneral_code_of_witness`: a singular witness `w` of `H` with (LCS) off
  `w.sing` makes `H.code` a code of the general manuscript (`Code.ValidGeneral`); conversely
  `exists_witness_of_validGeneral_code`.  The witness is transported with the *same* singular set;
  the induced graphs of the code and of `H` are isomorphic (`inducedIsoSing`).
* **Similarities** — `isSingConfiguration_similarity` (the witness is moved by the similarity, a
  Lipschitz map preserving `H¹`-nullity), `exists_relabel_code_sing`,
  `generalLaws_isSimilarity_sing` and `validGeneral_code_iff_similarity`.
* **(FE)** — `rootedFiniteEnergyDensity_config_sing`: at a general environment with `e.val = H.code`
  the general manuscript's rooted (FE) integrand at `0` **equals** `rootedFEDensity H`.
-/

set_option autoImplicit false

open MeasureTheory Set Topology
open scoped ENNReal

namespace ReflectedGMS.GeomTop

open GMS

variable {H : CellConfig}

/-! ## Labels -/

/-- The conductance of a cell with itself vanishes. -/
theorem c_self_eq_zero_sing (hH : IsSingConfiguration H) (K : Cell) : H.c K K = 0 :=
  le_antisymm (not_lt.mp fun h => hH.adj_ne K K h rfl) (hH.c_nonneg K K)

/-- Two cells of a configuration sharing an interior point coincide. -/
theorem eq_of_mem_interior_sing (hH : IsSingConfiguration H) {K K' : Cell} (hK : K ∈ H.cells)
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
theorem eq_of_leastInteriorLabel_sing (hH : IsSingConfiguration H) {K K' : Cell}
    (hK : K ∈ H.cells) (hK' : K' ∈ H.cells) {n : ℕ} (h : Code.LeastInteriorLabel K n)
    (h' : Code.LeastInteriorLabel K' n) : K = K' :=
  eq_of_mem_interior_sing hH hK hK' h.1 h'.1

/-- **Slot `n` holds exactly the cell whose least rational interior label is `n`.** -/
theorem slot_eq_some_iff_sing (hH : IsSingConfiguration H) {n : ℕ} {K : Cell} :
    H.slot n = some K ↔ K ∈ H.cells ∧ Code.LeastInteriorLabel K n := by
  unfold CellConfig.slot
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
    exact congrArg some
      (eq_of_leastInteriorLabel_sing hH h.choose_spec.1 hK h.choose_spec.2 hl)

/-- The label of a cell: its least rational interior-hit index. -/
noncomputable def labelSing (hH : IsSingConfiguration H) (K : H.cells) : ℕ :=
  Code.leastInteriorLabel K (hH.interior_nonempty K K.2)

theorem leastInteriorLabel_labelSing (hH : IsSingConfiguration H) (K : H.cells) :
    Code.LeastInteriorLabel K (labelSing hH K) :=
  Code.leastInteriorLabel_spec _ _

theorem slot_labelSing (hH : IsSingConfiguration H) (K : H.cells) :
    H.slot (labelSing hH K) = some (K : Cell) :=
  (slot_eq_some_iff_sing hH).2 ⟨K.2, leastInteriorLabel_labelSing hH K⟩

theorem cell_mem_cells_sing (hH : IsSingConfiguration H) (v : Code.Vertex H.code) :
    Code.cell H.code v ∈ H.cells :=
  ((slot_eq_some_iff_sing hH).1 (GMS.CellConfig.slot_val v)).1

/-- **The code's conductances are admissible** (no finite-row clause). -/
theorem rawAdmissible_code_sing (hH : IsSingConfiguration H) : Code.RawAdmissible H.code where
  symm n m := by
    show H.codeCond n m = H.codeCond m n
    unfold CellConfig.codeCond
    cases H.slot n with
    | none => cases H.slot m <;> rfl
    | some K =>
      cases H.slot m with
      | none => rfl
      | some K' => exact hH.c_symm K K'
  nonneg n m := by
    show 0 ≤ H.codeCond n m
    unfold CellConfig.codeCond
    cases H.slot n with
    | none => cases H.slot m <;> exact le_rfl
    | some K =>
      cases H.slot m with
      | none => exact le_rfl
      | some K' => exact hH.c_nonneg K K'
  self n := by
    show H.codeCond n n = 0
    unfold CellConfig.codeCond
    cases H.slot n with
    | none => rfl
    | some K => exact c_self_eq_zero_sing hH K
  absent n m h := by
    show H.codeCond n m = 0
    rcases h with h | h
    · exact GMS.CellConfig.codeCond_of_none_left h
    · exact GMS.CellConfig.codeCond_of_none_right h

/-- **The code's labels are canonical.** -/
theorem canonicalLabels_code_sing (hH : IsSingConfiguration H) : Code.CanonicalLabels H.code :=
  fun v => ((slot_eq_some_iff_sing hH).1 (GMS.CellConfig.slot_val v)).2

/-- **The active labels of the code are in bijection with the cells.** -/
noncomputable def cellEquivSing (hH : IsSingConfiguration H) : Code.Vertex H.code ≃ H.cells where
  toFun v := ⟨Code.cell H.code v, cell_mem_cells_sing hH v⟩
  invFun K := ⟨labelSing hH K, by
    show (H.slot (labelSing hH K)).isSome
    rw [slot_labelSing hH K]
    rfl⟩
  left_inv v := Subtype.ext (Code.LeastInteriorLabel.unique
    (leastInteriorLabel_labelSing hH ⟨Code.cell H.code v, cell_mem_cells_sing hH v⟩)
    (canonicalLabels_code_sing hH v))
  right_inv K := Subtype.ext
    (Option.some_inj.mp ((GMS.CellConfig.slot_val _).symm.trans (slot_labelSing hH K)))

@[simp] theorem coe_cellEquivSing (hH : IsSingConfiguration H) (v : Code.Vertex H.code) :
    ((cellEquivSing hH v : H.cells) : Cell) = Code.cell H.code v := rfl

@[simp] theorem cellEquivSing_symm_val (hH : IsSingConfiguration H) (K : H.cells) :
    ((cellEquivSing hH).symm K).val = labelSing hH K := rfl

theorem cell_cellEquivSing_symm (hH : IsSingConfiguration H) (K : H.cells) :
    Code.cell H.code ((cellEquivSing hH).symm K) = K := by
  rw [← coe_cellEquivSing hH, Equiv.apply_symm_apply]

/-- **The conductances of the code are those of the configuration.** -/
theorem code_cond_sing (hH : IsSingConfiguration H) (v w : Code.Vertex H.code) :
    H.code.2 v.val w.val = H.c (cellEquivSing hH v) (cellEquivSing hH w) :=
  GMS.CellConfig.codeCond_of_some (GMS.CellConfig.slot_val v) (GMS.CellConfig.slot_val w)


/-! ## Validity of the code -/

/-- Unions over active labels are unions over cells. -/
theorem iUnion_comp_cell_sing (hH : IsSingConfiguration H) (g : Cell → Set Plane) :
    (⋃ v : Code.Vertex H.code, g (Code.cell H.code v)) = ⋃ K ∈ H.cells, g K := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨v, hz⟩
    exact ⟨_, cell_mem_cells_sing hH v, hz⟩
  · rintro ⟨K, hK, hz⟩
    refine ⟨(cellEquivSing hH).symm ⟨K, hK⟩, ?_⟩
    rw [cell_cellEquivSing_symm]
    exact hz

/-- **The induced graphs of the decoded configuration and of `H` on a set are isomorphic.** -/
noncomputable def inducedIsoSing (hH : IsSingConfiguration H) (h : Code.RawAdmissible H.code)
    (A : Set Plane) :
    (Code.rawConfig H.code h).graph.induce {v | (Code.rawConfig H.code h).Hits A v} ≃g
      H.inducedGraph A where
  toFun v := ⟨cellEquivSing hH v.1, v.2⟩
  invFun K := ⟨(cellEquivSing hH).symm K.1, by
    show ((Code.cell H.code ((cellEquivSing hH).symm K.1) : Set Plane) ∩ A).Nonempty
    rw [cell_cellEquivSing_symm]
    exact K.2⟩
  left_inv v := Subtype.ext ((cellEquivSing hH).symm_apply_apply v.1)
  right_inv K := Subtype.ext ((cellEquivSing hH).apply_symm_apply K.1)
  map_rel_iff' {v w} := by
    change ((cellEquivSing hH v.1 : H.cells) ≠ cellEquivSing hH w.1 ∧
        0 < H.c (cellEquivSing hH v.1) (cellEquivSing hH w.1) ∧
        0 < H.c (cellEquivSing hH w.1) (cellEquivSing hH v.1)) ↔ 0 < H.code.2 v.1.val w.1.val
    rw [code_cond_sing hH]
    constructor
    · exact fun hvw => hvw.2.1
    · intro hvw
      refine ⟨fun heq => hH.adj_ne _ _ hvw (congrArg Subtype.val heq), hvw, ?_⟩
      rw [hH.c_symm]
      exact hvw

/-- Induced connectivity of the decoded configuration is preconnectedness of `H(A)`. -/
theorem inducedConnected_rawConfig_iff_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (A : Set Plane) :
    (Code.rawConfig H.code h).InducedConnected A ↔ (H.inducedGraph A).Preconnected :=
  (inducedIsoSing hH h A).preconnected_iff

/-- **(LCS) of the decoded configuration is (LCS) of `H`**, relative to the same set. -/
theorem lineConnectedOff_rawConfig_iff_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (S : Set Plane) :
    (Code.rawConfig H.code h).LineConnectedOff S ↔ LineConnectedOff H S := by
  unfold CellConfiguration.LineConnectedOff LineConnectedOff
  simp only [inducedConnected_rawConfig_iff_sing hH h]

/-- A singular witness of `H` is a singular set of its decoded configuration (the same `Ssing`). -/
noncomputable def singularSetOfWitness (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (w : SingularWitness H) :
    CellConfiguration.SingularSet (Code.rawConfig H.code h) where
  sing := w.sing
  isClosed_sing := w.isClosed_sing
  hausdorff_sing := w.hausdorff_sing
  cover := by
    intro z hz
    obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.mp (w.cover hz)
    refine Set.mem_iUnion.mpr ⟨(cellEquivSing hH).symm ⟨K, hK⟩, ?_⟩
    show z ∈ ((Code.cell H.code ((cellEquivSing hH).symm ⟨K, hK⟩) : Cell) : Set Plane)
    rw [cell_cellEquivSing_symm]
    exact hzK
  locallyFinite := by
    intro z hz
    obtain ⟨U, hU, hfin⟩ := w.locallyFinite z hz
    refine ⟨U, hU, (hfin.preimage (f := fun v : Code.Vertex H.code => Code.cell H.code v)
      (Subtype.val_injective.comp (cellEquivSing hH).injective).injOn).subset ?_⟩
    intro v hv
    exact ⟨cell_mem_cells_sing hH v, hv⟩

/-- A singular set of the decoded configuration is a singular witness of `H` (the same `Ssing`). -/
noncomputable def witnessOfSingularSet (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (S : CellConfiguration.SingularSet (Code.rawConfig H.code h)) :
    SingularWitness H where
  sing := S.sing
  isClosed_sing := S.isClosed_sing
  hausdorff_sing := S.hausdorff_sing
  cover := by
    intro z hz
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (S.cover hz)
    exact Set.mem_iUnion₂.mpr ⟨Code.cell H.code v, cell_mem_cells_sing hH v, hv⟩
  locallyFinite := by
    intro z hz
    obtain ⟨U, hU, hfin⟩ := S.locallyFinite z hz
    refine ⟨U, hU, (hfin.image fun v : Code.Vertex H.code => Code.cell H.code v).subset ?_⟩
    rintro K ⟨hK, hKU⟩
    refine ⟨(cellEquivSing hH).symm ⟨K, hK⟩, ?_, cell_cellEquivSing_symm hH ⟨K, hK⟩⟩
    show ((Code.cell H.code ((cellEquivSing hH).symm ⟨K, hK⟩) : Set Plane) ∩ U).Nonempty
    rw [cell_cellEquivSing_symm]
    exact hKU

/-- **With a singular witness and (LCS) off it, the decoded configuration satisfies Definition 1.1
and (LCS) of the general manuscript.** -/
theorem generalGeometry_rawConfig_of_witness (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (w : SingularWitness H) (hL : LineConnectedOff H w.sing) :
    GeneralGeometry (Code.rawConfig H.code h) := by
  refine ⟨fun v => hH.isConnected _ (cell_mem_cells_sing hH v),
    fun v => hH.interior_nonempty _ (cell_mem_cells_sing hH v), ?_,
    ⟨singularSetOfWitness hH h w, (lineConnectedOff_rawConfig_iff_sing hH h w.sing).2 hL⟩, ?_⟩
  · intro v v' hvv'
    exact hH.volume_inter _ (cell_mem_cells_sing hH v) _ (cell_mem_cells_sing hH v')
      fun hEq => hvv' ((cellEquivSing hH).injective (Subtype.ext hEq))
  · intro v v' hvv'
    have hpos : 0 < H.code.2 v.val v'.val := hvv'
    rw [code_cond_sing hH] at hpos
    exact hH.adj_inter _ _ hpos

/-- **The code of a singular configuration with a witness satisfying (LCS) is a code of the general
manuscript.** -/
theorem validGeneral_code_of_witness (hH : IsSingConfiguration H) (w : SingularWitness H)
    (hL : LineConnectedOff H w.sing) : Code.ValidGeneral H.code :=
  ⟨rawAdmissible_code_sing hH, generalGeometry_rawConfig_of_witness hH _ w hL,
    canonicalLabels_code_sing hH⟩

/-- **Conversely**, general validity of the code gives a singular witness of `H` with (LCS) off it. -/
theorem exists_witness_of_validGeneral_code (hH : IsSingConfiguration H)
    (hV : Code.ValidGeneral H.code) : ∃ w : SingularWitness H, LineConnectedOff H w.sing := by
  obtain ⟨h, hG, -⟩ := hV
  obtain ⟨S, hS⟩ := hG.exists_singularSet
  exact ⟨witnessOfSingularSet hH h S, (lineConnectedOff_rawConfig_iff_sing hH h S.sing).1 hS⟩

theorem validGeneral_code_iff_exists_witness (hH : IsSingConfiguration H) :
    Code.ValidGeneral H.code ↔ ∃ w : SingularWitness H, LineConnectedOff H w.sing :=
  ⟨exists_witness_of_validGeneral_code hH, fun ⟨w, hL⟩ => validGeneral_code_of_witness hH w hL⟩

/-! ## Similarities -/

section Similarity

variable (s : ℝ) (u : Plane) (hs : 0 < s)

/-- The image of a singular witness under `z ↦ s(z − u)`. -/
noncomputable def SingularWitness.similarity (w : SingularWitness H) :
    SingularWitness (H.similarity s u hs) where
  sing := positiveSimilarity s u '' w.sing
  isClosed_sing := (positiveSimilarityHomeomorph s u hs).isClosedMap _ w.isClosed_sing
  hausdorff_sing := hausdorffMeasure_one_image_positiveSimilarity_eq_zero s u hs w.hausdorff_sing
  cover := by
    intro z hz
    have hz' : (positiveSimilarityHomeomorph s u hs).symm z ∉ w.sing := fun hc =>
      hz ((mem_image_positiveSimilarity_iff s u hs w.sing z).mpr hc)
    obtain ⟨K0, hK0, hz0⟩ := Set.mem_iUnion₂.mp (w.cover ((Set.mem_compl_iff _ _).mpr hz'))
    refine Set.mem_iUnion₂.mpr ⟨transformCell s u hs K0, ⟨K0, hK0, rfl⟩, ?_⟩
    rw [coe_transformCell]
    exact ⟨_, hz0, positiveSimilarity_inverse_right s u z hs⟩
  locallyFinite := by
    intro z hz
    have hz' : (positiveSimilarityHomeomorph s u hs).symm z ∉ w.sing := fun hc =>
      hz ((mem_image_positiveSimilarity_iff s u hs w.sing z).mpr hc)
    obtain ⟨U, hU, hfin⟩ := w.locallyFinite _ hz'
    refine ⟨(positiveSimilarityHomeomorph s u hs).symm ⁻¹' U,
      (positiveSimilarityHomeomorph s u hs).symm.continuous.continuousAt.preimage_mem_nhds hU,
      (hfin.image (transformCell s u hs)).subset ?_⟩
    rintro K ⟨⟨K0, hK0, rfl⟩, p, hpK, hpU⟩
    refine ⟨K0, ⟨hK0, ?_⟩, rfl⟩
    rw [coe_transformCell] at hpK
    obtain ⟨p0, hp0, rfl⟩ := hpK
    refine ⟨p0, hp0, ?_⟩
    have hp := (positiveSimilarityHomeomorph s u hs).symm_apply_apply p0
    rw [Set.mem_preimage, ← coe_positiveSimilarityHomeomorph s u hs, hp] at hpU
    exact hpU

/-- The pull-back of a singular witness of `C(H − u)` to `H`. -/
noncomputable def SingularWitness.ofSimilarity (w : SingularWitness (H.similarity s u hs)) :
    SingularWitness H where
  sing := positiveSimilarity s u ⁻¹' w.sing
  isClosed_sing := w.isClosed_sing.preimage (positiveSimilarityHomeomorph s u hs).continuous
  hausdorff_sing := by
    have hpre : positiveSimilarity s u ⁻¹' w.sing = positiveSimilarity s⁻¹ (-s • u) '' w.sing :=
      (congrFun (Set.image_eq_preimage_of_inverse
        (f := positiveSimilarity s⁻¹ (-s • u)) (g := positiveSimilarity s u)
        (fun z => positiveSimilarity_inverse_right s u z hs)
        (fun z => positiveSimilarity_inverse_left s u z hs)) w.sing).symm
    rw [hpre]
    exact hausdorffMeasure_one_image_positiveSimilarity_eq_zero s⁻¹ (-s • u) (inv_pos.2 hs)
      w.hausdorff_sing
  cover := by
    intro z hz
    have hz' : positiveSimilarity s u z ∈ w.singᶜ := hz
    obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.mp (w.cover hz')
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [coe_transformCell] at hzK
    exact Set.mem_iUnion₂.mpr
      ⟨K0, hK0, (injective_positiveSimilarity s u hs).mem_set_image.mp hzK⟩
  locallyFinite := by
    intro z hz
    obtain ⟨U, hU, hfin⟩ := w.locallyFinite (positiveSimilarity s u z) hz
    refine ⟨positiveSimilarity s u ⁻¹' U,
      (positiveSimilarityHomeomorph s u hs).continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    refine (hfin.preimage (f := transformCell s u hs)
      (GMS.CellConfig.transformCell_injective s u hs).injOn).subset ?_
    rintro K ⟨hK, p, hpK, hpU⟩
    refine ⟨⟨K, hK, rfl⟩, positiveSimilarity s u p, ?_, hpU⟩
    rw [coe_transformCell]
    exact Set.mem_image_of_mem _ hpK

/-- **`C(H − u)` is again a configuration of the singular class.** -/
theorem isSingConfiguration_similarity (hH : IsSingConfiguration H) :
    IsSingConfiguration (H.similarity s u hs) where
  isConnected K hK := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [coe_transformCell]
    exact (hH.isConnected K0 hK0).image _
      (positiveSimilarityHomeomorph s u hs).continuous.continuousOn
  interior_nonempty K hK := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [interior_coe_transformCell]
    exact (hH.interior_nonempty K0 hK0).image _
  volume_inter K hK K' hK' hne := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    obtain ⟨K0', hK0', rfl⟩ := hK'
    rw [coe_transformCell, coe_transformCell,
      ← Set.image_inter (f := positiveSimilarity s u) (positiveSimilarityHomeomorph s u hs).injective]
    exact volume_positiveSimilarity_image_eq_zero s u hs
      (hH.volume_inter K0 hK0 K0' hK0' fun h => hne (congrArg _ h))
  witness := hH.witness.map (SingularWitness.similarity s u hs)
  c_nonneg K K' := hH.c_nonneg _ _
  c_symm K K' := hH.c_symm _ _
  adj_mem K K' h := ⟨(GMS.CellConfig.mem_similarity_cells s u hs).2 (hH.adj_mem _ _ h).1,
    (GMS.CellConfig.mem_similarity_cells s u hs).2 (hH.adj_mem _ _ h).2⟩
  adj_ne K K' h hKK := hH.adj_ne _ _ h (congrArg _ hKK)
  adj_inter K K' h := by
    have h' := hH.adj_inter _ _ h
    rw [GMS.CellConfig.coe_mapCell, GMS.CellConfig.coe_mapCell,
      ← Set.image_inter (positiveSimilarityHomeomorph s u hs).symm.injective,
      Set.image_nonempty] at h'
    exact h'

/-- Preconnectedness of `C(H − u)(A)` is preconnectedness of `H(C⁻¹ A)`. -/
theorem preconnected_inducedGraph_similarity_iff (H : CellConfig) (A : Set Plane) :
    ((H.similarity s u hs).inducedGraph A).Preconnected ↔
      (H.inducedGraph (positiveSimilarity s u ⁻¹' A)).Preconnected := by
  have hA : positiveSimilarity s u '' (positiveSimilarity s u ⁻¹' A) = A :=
    Set.image_preimage_eq A (positiveSimilarityHomeomorph s u hs).surjective
  have key := (GMS.CellConfig.inducedGraphSimilarityIso s u hs H
    (positiveSimilarity s u ⁻¹' A)).preconnected_iff
  rw [hA] at key
  exact key.symm

/-- **(LCS) is carried to `C(H − u)`, relative to the image of the singular set.** -/
theorem lineConnectedOff_similarity {S : Set Plane} (hL : LineConnectedOff H S) :
    LineConnectedOff (H.similarity s u hs) (positiveSimilarity s u '' S) := by
  have hpre : positiveSimilarity s u ⁻¹' (positiveSimilarity s u '' S) = S :=
    Set.preimage_image_eq S (injective_positiveSimilarity s u hs)
  refine ⟨fun a b y hd => ?_, fun x a b hd => ?_⟩
  · rw [preconnected_inducedGraph_similarity_iff s u hs,
      preimage_positiveSimilarity_horizontal s u hs]
    refine hL.1 _ _ _ ?_
    have hd' := hd.preimage (positiveSimilarity s u)
    rwa [hpre, preimage_positiveSimilarity_horizontal s u hs] at hd'
  · rw [preconnected_inducedGraph_similarity_iff s u hs,
      preimage_positiveSimilarity_vertical s u hs]
    refine hL.2 _ _ _ ?_
    have hd' := hd.preimage (positiveSimilarity s u)
    rwa [hpre, preimage_positiveSimilarity_vertical s u hs] at hd'

/-- **(LCS) is pulled back from `C(H − u)` to `H`, relative to the preimage of the singular set.** -/
theorem lineConnectedOff_of_similarity {S : Set Plane}
    (hL : LineConnectedOff (H.similarity s u hs) S) :
    LineConnectedOff H (positiveSimilarity s u ⁻¹' S) := by
  have hinv : 0 < s⁻¹ := inv_pos.2 hs
  have himg : ∀ A : Set Plane,
      positiveSimilarity s u '' A = positiveSimilarity s⁻¹ (-s • u) ⁻¹' A := fun A =>
    congrFun (Set.image_eq_preimage_of_inverse
      (fun z => positiveSimilarity_inverse_left s u z hs)
      (fun z => positiveSimilarity_inverse_right s u z hs)) A
  have hback : ∀ A : Set Plane, positiveSimilarity s u ⁻¹' (positiveSimilarity s u '' A) = A :=
    fun A => Set.preimage_image_eq A (injective_positiveSimilarity s u hs)
  have hdisj : ∀ A : Set Plane, Disjoint A (positiveSimilarity s u ⁻¹' S) →
      Disjoint (positiveSimilarity s u '' A) S := by
    intro A hA
    refine Set.disjoint_left.2 ?_
    rintro p ⟨q, hq, rfl⟩ hpS
    exact Set.disjoint_left.1 hA hq hpS
  refine ⟨fun a b y hd => ?_, fun x a b hd => ?_⟩
  · have hd' := hdisj _ hd
    rw [← hback (horizontal a b y), ← preconnected_inducedGraph_similarity_iff s u hs]
    rw [himg, preimage_positiveSimilarity_horizontal s⁻¹ (-s • u) hinv] at hd' ⊢
    exact hL.1 _ _ _ hd'
  · have hd' := hdisj _ hd
    rw [← hback (vertical x a b), ← preconnected_inducedGraph_similarity_iff s u hs]
    rw [himg, preimage_positiveSimilarity_vertical s⁻¹ (-s • u) hinv] at hd' ⊢
    exact hL.2 _ _ _ hd'

/-- **The codes of `H` and `C(H − u)` are related by a relabelling**: cells are transformed by
`z ↦ s(z − u)` and conductances are unchanged. -/
theorem exists_relabel_code_sing (hH : IsSingConfiguration H) :
    ∃ relabel : Code.Vertex H.code ≃ Code.Vertex (H.similarity s u hs).code,
      (∀ v, Code.cell (H.similarity s u hs).code (relabel v) =
          transformCell s u hs (Code.cell H.code v)) ∧
        ∀ v w, (H.similarity s u hs).code.2 (relabel v).val (relabel w).val =
          H.code.2 v.val w.val := by
  have hH' := isSingConfiguration_similarity s u hs hH
  refine ⟨((cellEquivSing hH).trans (GMS.CellConfig.similarityCellEquiv s u hs)).trans
      (cellEquivSing hH').symm, fun v => ?_, fun v w => ?_⟩
  · simp only [Equiv.trans_apply]
    rw [cell_cellEquivSing_symm hH']
    rfl
  · simp only [Equiv.trans_apply]
    rw [code_cond_sing hH', code_cond_sing hH]
    simp only [Equiv.apply_symm_apply]
    exact GMS.CellConfig.similarity_c_transformCell s u hs _ _

/-- **The similarity relation of the general manuscript holds between the codes of `H` and
`C(H − u)`.** -/
theorem generalLaws_isSimilarity_sing (hH : IsSingConfiguration H) {e e' : Code.EnvGeneral}
    (he : e.val = H.code) (he' : e'.val = (H.similarity s u hs).code) :
    GeneralLaws.IsSimilarity s u hs e e' := by
  obtain ⟨r, hr⟩ := e
  obtain ⟨r', hr'⟩ := e'
  have he2 : r = H.code := he
  have he2' : r' = (H.similarity s u hs).code := he'
  subst he2 he2'
  obtain ⟨relabel, hcell, hc⟩ := exists_relabel_code_sing s u hs hH
  exact ⟨relabel, hcell, hc⟩

/-- **General validity of the code is similarity invariant** on the singular class. -/
theorem validGeneral_code_iff_similarity (hH : IsSingConfiguration H) :
    Code.ValidGeneral H.code ↔ Code.ValidGeneral (H.similarity s u hs).code := by
  have hH' := isSingConfiguration_similarity s u hs hH
  constructor
  · intro hV
    obtain ⟨w, hL⟩ := exists_witness_of_validGeneral_code hH hV
    exact validGeneral_code_of_witness hH' (w.similarity s u hs)
      (lineConnectedOff_similarity s u hs hL)
  · intro hV
    obtain ⟨w, hL⟩ := exists_witness_of_validGeneral_code hH' hV
    exact validGeneral_code_of_witness hH (w.ofSimilarity s u hs)
      (lineConnectedOff_of_similarity s u hs hL)

end Similarity

/-! ## The (FE) integrand -/

theorem iUnion_cell_code_sing (hH : IsSingConfiguration H) :
    (⋃ v : Code.Vertex H.code, ((Code.cell H.code v : Cell) : Set Plane)) =
      ⋃ K ∈ H.cells, (K : Set Plane) :=
  iUnion_comp_cell_sing hH fun K => (K : Set Plane)

theorem iUnion_frontier_cell_code_sing (hH : IsSingConfiguration H) :
    (⋃ v : Code.Vertex H.code, frontier ((Code.cell H.code v : Cell) : Set Plane)) =
      ⋃ K ∈ H.cells, frontier (K : Set Plane) :=
  iUnion_comp_cell_sing hH fun K => frontier (K : Set Plane)

/-- The boundary mask of the decoded configuration is that of `H`. -/
theorem boundaryMask_rawConfig_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) :
    RootDensities.boundaryMask (Code.rawConfig H.code h).cellsOnly = boundaryMask H := by
  show (⋃ v : Code.Vertex H.code, frontier ((Code.cell H.code v : Cell) : Set Plane)) ∪
      (⋃ v : Code.Vertex H.code, ((Code.cell H.code v : Cell) : Set Plane))ᶜ = boundaryMask H
  rw [iUnion_frontier_cell_code_sing hH, iUnion_cell_code_sing hH]
  rfl

/-- `Σ_{H'} c(H,H')` over labels is the sum over cells. -/
theorem tsum_ofReal_rawConfig_c_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (v : Code.Vertex H.code) :
    ∑' w, ENNReal.ofReal ((Code.rawConfig H.code h).c v w) =
      ∑' K' : H.cells, ENNReal.ofReal (H.c (cellEquivSing hH v) K') := by
  rw [← (cellEquivSing hH).tsum_eq]
  exact tsum_congr fun w => congrArg ENNReal.ofReal (code_cond_sing hH v w)

/-- `Σ_{H'} c(H,H')⁻¹` over labels is the sum over cells. -/
theorem tsum_ofReal_rawConfig_c_inv_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (v : Code.Vertex H.code) :
    ∑' w, ENNReal.ofReal ((Code.rawConfig H.code h).c v w)⁻¹ =
      ∑' K' : H.cells, ENNReal.ofReal (H.c (cellEquivSing hH v) K')⁻¹ := by
  rw [← (cellEquivSing hH).tsum_eq]
  exact tsum_congr fun w => congrArg (fun x : ℝ => ENNReal.ofReal x⁻¹) (code_cond_sing hH v w)

/-- **The (FE) integrand of the general manuscript at a label is `feDensity` at its cell.** -/
theorem finiteEnergyDensity_rawConfig_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) (v : Code.Vertex H.code) :
    GeneralLaws.finiteEnergyDensity (Code.rawConfig H.code h) v =
      feDensity H (cellEquivSing hH v) := by
  unfold GeneralLaws.finiteEnergyDensity feDensity
  rw [tsum_ofReal_rawConfig_c_sing hH h v, tsum_ofReal_rawConfig_c_inv_sing hH h v]
  rfl

/-- **The rooted (FE) integrand of the decoded configuration at `0` is `rootedFEDensity H`.** -/
theorem rootedFiniteEnergyDensity_rawConfig_sing (hH : IsSingConfiguration H)
    (h : Code.RawAdmissible H.code) :
    GeneralLaws.rootedFiniteEnergyDensity (Code.rawConfig H.code h) 0 = rootedFEDensity H := by
  classical
  have hmask := boundaryMask_rawConfig_sing hH h
  unfold GeneralLaws.rootedFiniteEnergyDensity rootedFEDensity
  by_cases h0 : (0 : Plane) ∈ boundaryMask H
  · have h0' : (0 : Plane) ∈ RootDensities.boundaryMask (Code.rawConfig H.code h).cellsOnly := by
      rw [hmask]
      exact h0
    rw [RootDensities.rootAt_eq_none_of_mem_boundaryMask _ h0', dif_neg fun hc => hc.1 h0]
    rfl
  · have h0' : (0 : Plane) ∉ RootDensities.boundaryMask (Code.rawConfig H.code h).cellsOnly := by
      rw [hmask]
      exact h0
    have hcov : ∃ K ∈ H.cells, (0 : Plane) ∈ (K : Set Plane) := by
      by_contra hc
      apply h0
      show (0 : Plane) ∈ (⋃ K ∈ H.cells, frontier (K : Set Plane)) ∪
        (⋃ K ∈ H.cells, (K : Set Plane))ᶜ
      refine Set.mem_union_right _ fun hz => hc ?_
      obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.mp hz
      exact ⟨K, hK, hzK⟩
    have hc : (0 : Plane) ∉ boundaryMask H ∧ ∃ K ∈ H.cells, (0 : Plane) ∈ (K : Set Plane) :=
      ⟨h0, hcov⟩
    rw [dif_pos hc]
    obtain ⟨hK1, h0K1⟩ := hc.2.choose_spec
    have hint : (0 : Plane) ∈ interior (hc.2.choose : Set Plane) := by
      rw [← self_diff_frontier]
      refine Set.mem_diff_of_mem h0K1 fun hf => h0 ?_
      show (0 : Plane) ∈ (⋃ K ∈ H.cells, frontier (K : Set Plane)) ∪
        (⋃ K ∈ H.cells, (K : Set Plane))ᶜ
      exact Set.mem_union_left _ (Set.mem_iUnion₂.mpr ⟨_, hK1, hf⟩)
    have hint0 : RootDensities.IsInteriorRoot (Code.rawConfig H.code h).cellsOnly 0
        ((cellEquivSing hH).symm ⟨hc.2.choose, hK1⟩) := by
      show (0 : Plane) ∈
        interior ((Code.cell H.code ((cellEquivSing hH).symm ⟨hc.2.choose, hK1⟩) : Cell) :
          Set Plane)
      rw [cell_cellEquivSing_symm]
      exact hint
    have huniq : ∀ v, RootDensities.IsInteriorRoot (Code.rawConfig H.code h).cellsOnly 0 v →
        v = (cellEquivSing hH).symm ⟨hc.2.choose, hK1⟩ := by
      intro v hv
      have hv' : (0 : Plane) ∈ interior ((Code.cell H.code v : Cell) : Set Plane) := hv
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext (eq_of_mem_interior_sing hH (cell_mem_cells_sing hH v) hK1 hv' hint)
    have hex : ∃! v, RootDensities.IsInteriorRoot (Code.rawConfig H.code h).cellsOnly 0 v :=
      ⟨_, hint0, huniq⟩
    have hroot : RootDensities.rootAt (Code.rawConfig H.code h).cellsOnly 0 =
        some ((cellEquivSing hH).symm ⟨hc.2.choose, hK1⟩) := by
      unfold RootDensities.rootAt
      rw [dif_neg h0', dif_pos hex]
      exact congrArg some (huniq _ hex.exists.choose_spec)
    have hfe := finiteEnergyDensity_rawConfig_sing hH h
      ((cellEquivSing hH).symm ⟨hc.2.choose, hK1⟩)
    rw [Equiv.apply_symm_apply] at hfe
    rw [hroot, Option.elim_some]
    exact hfe

/-- **(FE) correspondence**: at a general environment coding `H`, the general manuscript's rooted
(FE) integrand at `0` equals the (FE) integrand `rootedFEDensity H` of the singular class. -/
theorem rootedFiniteEnergyDensity_config_sing (hH : IsSingConfiguration H)
    {e : Code.EnvGeneral} (he : e.val = H.code) :
    GeneralLaws.rootedFiniteEnergyDensity (Code.config e) 0 = rootedFEDensity H := by
  obtain ⟨r, hr⟩ := e
  have he2 : r = H.code := he
  subst he2
  exact rootedFiniteEnergyDensity_rawConfig_sing hH hr.choose

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.slot_eq_some_iff_sing
assert_no_sorry ReflectedGMS.GeomTop.rawAdmissible_code_sing
assert_no_sorry ReflectedGMS.GeomTop.canonicalLabels_code_sing
assert_no_sorry ReflectedGMS.GeomTop.cellEquivSing
assert_no_sorry ReflectedGMS.GeomTop.coe_cellEquivSing
assert_no_sorry ReflectedGMS.GeomTop.cell_cellEquivSing_symm
assert_no_sorry ReflectedGMS.GeomTop.code_cond_sing
assert_no_sorry ReflectedGMS.GeomTop.inducedIsoSing
assert_no_sorry ReflectedGMS.GeomTop.lineConnectedOff_rawConfig_iff_sing
assert_no_sorry ReflectedGMS.GeomTop.validGeneral_code_of_witness
assert_no_sorry ReflectedGMS.GeomTop.exists_witness_of_validGeneral_code
assert_no_sorry ReflectedGMS.GeomTop.validGeneral_code_iff_exists_witness
assert_no_sorry ReflectedGMS.GeomTop.SingularWitness.similarity
assert_no_sorry ReflectedGMS.GeomTop.SingularWitness.ofSimilarity
assert_no_sorry ReflectedGMS.GeomTop.isSingConfiguration_similarity
assert_no_sorry ReflectedGMS.GeomTop.lineConnectedOff_similarity
assert_no_sorry ReflectedGMS.GeomTop.lineConnectedOff_of_similarity
assert_no_sorry ReflectedGMS.GeomTop.exists_relabel_code_sing
assert_no_sorry ReflectedGMS.GeomTop.generalLaws_isSimilarity_sing
assert_no_sorry ReflectedGMS.GeomTop.validGeneral_code_iff_similarity
assert_no_sorry ReflectedGMS.GeomTop.finiteEnergyDensity_rawConfig_sing
assert_no_sorry ReflectedGMS.GeomTop.rootedFiniteEnergyDensity_rawConfig_sing
assert_no_sorry ReflectedGMS.GeomTop.rootedFiniteEnergyDensity_config_sing

#print axioms ReflectedGMS.GeomTop.slot_eq_some_iff_sing
#print axioms ReflectedGMS.GeomTop.rawAdmissible_code_sing
#print axioms ReflectedGMS.GeomTop.canonicalLabels_code_sing
#print axioms ReflectedGMS.GeomTop.cellEquivSing
#print axioms ReflectedGMS.GeomTop.code_cond_sing
#print axioms ReflectedGMS.GeomTop.validGeneral_code_of_witness
#print axioms ReflectedGMS.GeomTop.exists_witness_of_validGeneral_code
#print axioms ReflectedGMS.GeomTop.validGeneral_code_iff_exists_witness
#print axioms ReflectedGMS.GeomTop.isSingConfiguration_similarity
#print axioms ReflectedGMS.GeomTop.exists_relabel_code_sing
#print axioms ReflectedGMS.GeomTop.generalLaws_isSimilarity_sing
#print axioms ReflectedGMS.GeomTop.validGeneral_code_iff_similarity
#print axioms ReflectedGMS.GeomTop.rootedFiniteEnergyDensity_rawConfig_sing
#print axioms ReflectedGMS.GeomTop.rootedFiniteEnergyDensity_config_sing
