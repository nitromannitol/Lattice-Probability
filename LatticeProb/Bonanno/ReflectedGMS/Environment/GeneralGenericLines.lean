/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GeneralGenericLines at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralNullBoundaries
import LatticeProb.Bonanno.ReflectedGMS.Environment.GenericLines
import Mathlib.Util.AssertNoSorry

/-!
# Lemma 2.2 and Proposition 2.3 of the general-cell manuscript

Manuscript: "Reflected scale-free invariance principle — cell configurations with singularities"
(`work/general/manuscript-text.txt`, lines 283–315).

**Lemma 2.2 (Compact sets away from the singular set).**  Every compact `K ⊂ ℂ \ Ssing` meets
finitely many cells and is covered by them; the coordinate projections `pₓ(Ssing)`, `p_y(Ssing)` are
Borel Lebesgue-null subsets of `ℝ`.

**Proposition 2.3 (Generic lines and graph connectedness).**  With `Nh = p_y(Ssing)` and
`Nv = pₓ(Ssing)`, simultaneously for all real `a, b`, the cell graphs of `[a,b] × {y}` (`y ∉ Nh`) and
of `{x} × [a,b]` (`x ∉ Nv`) are finite and connected, and the full cell adjacency graph is connected.

Connectivity of the segment graphs is **(LCS)** itself (`CellConfiguration.LineConnectedOff`); no
face / incidence rule is used anywhere, as in the manuscript ("no implication from intersection to
adjacency is used").  The good-rectangle half of Proposition 2.3 is not formalized here.

Main results:
* `CellConfiguration.SingularSet.finite_hits_of_isCompact`, `subset_iUnion_hits` — Lemma 2.2;
* `CellConfiguration.SingularSet.measurableSet_image_coordProj`, `volume_image_coordProj` —
  Lemma 2.2, projections;
* `CellConfiguration.SingularSet.horizontal_finite_and_connected`, `vertical_finite_and_connected`,
  `GeneralGeometry.exists_generic_lines` — Proposition 2.3, generic lines;
* `GeneralGeometry.graph_connected` — Proposition 2.3, graph connectedness;
* `GeneralGeometry.aeLineConnected_toIndexedCells` — with finite rows, the configuration satisfies
  the corpus' `AELineConnected`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace ReflectedGMS

/-! ### Points of the plane from their coordinates -/

theorem verticalPoint_coord (q : Plane) : verticalPoint (q 0) (q 1) = q := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · simp
  · simp

theorem horizontalPoint_coord (q : Plane) : horizontalPoint (q 1) (q 0) = q := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · simp
  · simp

/-- A nonempty open set of the plane contains a point whose second coordinate avoids a given
Lebesgue-null set of reals. -/
theorem exists_mem_of_isOpen_coord_one_notMem {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty)
    {N : Set ℝ} (hN : volume N = 0) : ∃ p ∈ U, p 1 ∉ N := by
  obtain ⟨q, hq⟩ := hne
  set Y : Set ℝ := verticalPoint (q 0) ⁻¹' U with hYdef
  have hYopen : IsOpen Y := hU.preimage (continuous_verticalPoint (q 0))
  have hYne : Y.Nonempty := ⟨q 1, by rw [hYdef, Set.mem_preimage, verticalPoint_coord]; exact hq⟩
  have hYpos : 0 < volume Y := hYopen.measure_pos volume hYne
  have hYN : ¬ Y ⊆ N := fun hsub => hYpos.ne' (measure_mono_null hsub hN)
  obtain ⟨t, htY, htN⟩ := Set.not_subset.mp hYN
  exact ⟨verticalPoint (q 0) t, htY, by rw [verticalPoint_apply_one]; exact htN⟩

/-- A nonempty open set of the plane contains a point whose first coordinate avoids a given
Lebesgue-null set of reals. -/
theorem exists_mem_of_isOpen_coord_zero_notMem {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty)
    {N : Set ℝ} (hN : volume N = 0) : ∃ p ∈ U, p 0 ∉ N := by
  obtain ⟨q, hq⟩ := hne
  set X : Set ℝ := horizontalPoint (q 1) ⁻¹' U with hXdef
  have hXopen : IsOpen X := hU.preimage (continuous_horizontalPoint (q 1))
  have hXne : X.Nonempty := ⟨q 0, by rw [hXdef, Set.mem_preimage, horizontalPoint_coord]; exact hq⟩
  have hXpos : 0 < volume X := hXopen.measure_pos volume hXne
  have hXN : ¬ X ⊆ N := fun hsub => hXpos.ne' (measure_mono_null hsub hN)
  obtain ⟨t, htX, htN⟩ := Set.not_subset.mp hXN
  exact ⟨horizontalPoint (q 1) t, htX, by rw [horizontalPoint_apply_zero]; exact htN⟩

namespace CellConfiguration

namespace SingularSet

variable {V : Type*} {C : CellConfiguration V}

/-! ### Lemma 2.2 -/

/-- **Lemma 2.2, finiteness.**  A compact set disjoint from `Ssing` meets only finitely many cells:
local finiteness off `Ssing` plus a finite subcover. -/
theorem finite_hits_of_isCompact (S : SingularSet C) {L : Set Plane} (hcomp : IsCompact L)
    (havoid : ∀ z ∈ L, z ∉ S.sing) : {v | C.Hits L v}.Finite := by
  have hne : ∀ z ∈ L, ∃ U : Set Plane, U ∈ 𝓝 z ∧ {v | C.Hits U v}.Finite :=
    fun z hz => S.locallyFinite z (havoid z hz)
  choose! U hUmem hUfin using hne
  obtain ⟨t, htL, htcover⟩ := hcomp.elim_nhds_subcover U hUmem
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet
    (fun z hz => hUfin z (htL z (Finset.mem_coe.mp hz)))) ?_
  rintro v ⟨p, hpc, hpL⟩
  obtain ⟨z, hzt, hpz⟩ := Set.mem_iUnion₂.mp (htcover hpL)
  exact Set.mem_iUnion₂.mpr ⟨z, Finset.mem_coe.mpr hzt, ⟨p, hpc, hpz⟩⟩

/-- **Lemma 2.2, coverage.**  A set disjoint from `Ssing` is covered by the cells meeting it. -/
theorem subset_iUnion_hits (S : SingularSet C) {L : Set Plane} (havoid : ∀ z ∈ L, z ∉ S.sing) :
    L ⊆ ⋃ v ∈ {v | C.Hits L v}, (C.cell v : Set Plane) := by
  intro z hz
  obtain ⟨v, hzv⟩ := Set.mem_iUnion.mp (S.cover (havoid z hz))
  exact Set.mem_iUnion₂.mpr ⟨v, ⟨z, hzv, hz⟩, hzv⟩

/-- The coordinate projections of `Ssing` are σ-compact (a closed subset of the plane is). -/
theorem isSigmaCompact_image_coordProj (S : SingularSet C) (i : Fin 2) :
    IsSigmaCompact (coordProj i '' S.sing) :=
  ((isSigmaCompact_univ (X := Plane)).of_isClosed_subset S.isClosed_sing (Set.subset_univ _)).image
    (lipschitzWith_coordProj i).continuous

/-- **Lemma 2.2, projections.**  The coordinate projections of `Ssing` are Borel. -/
theorem measurableSet_image_coordProj (S : SingularSet C) (i : Fin 2) :
    MeasurableSet (coordProj i '' S.sing) := by
  obtain ⟨K, hK, hKU⟩ := S.isSigmaCompact_image_coordProj i
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

/-- **Lemma 2.2, projections.**  The coordinate projections of `Ssing` are Lebesgue-null. -/
theorem volume_image_coordProj (S : SingularSet C) (i : Fin 2) :
    volume (coordProj i '' S.sing) = 0 :=
  volume_image_coordProj_eq_zero i S.hausdorff_sing

/-! ### Proposition 2.3: generic lines -/

theorem disjoint_horizontal (S : SingularSet C) {y : ℝ} (hy : y ∉ coordProj 1 '' S.sing)
    (a b : ℝ) : Disjoint (horizontal a b y) S.sing := by
  rw [Set.disjoint_left]
  rintro z ⟨-, -, hz1⟩ hzs
  exact hy ⟨z, hzs, hz1⟩

theorem disjoint_vertical (S : SingularSet C) {x : ℝ} (hx : x ∉ coordProj 0 '' S.sing)
    (a b : ℝ) : Disjoint (vertical x a b) S.sing := by
  rw [Set.disjoint_left]
  rintro z ⟨hz0, -, -⟩ hzs
  exact hx ⟨z, hzs, hz0⟩

/-- **Proposition 2.3, horizontal lines.**  For `y ∉ p_y(Ssing)` and all real `a, b`, the cell graph
of `[a,b] × {y}` is finite (Lemma 2.2) and connected ((LCS)). -/
theorem horizontal_finite_and_connected (S : SingularSet C) (hL : C.LineConnectedOff S.sing)
    {y : ℝ} (hy : y ∉ coordProj 1 '' S.sing) (a b : ℝ) :
    {v | C.Hits (horizontal a b y) v}.Finite ∧ C.InducedConnected (horizontal a b y) :=
  ⟨S.finite_hits_of_isCompact (isCompact_horizontal a b y)
      (fun _ hz hzs => Set.disjoint_left.mp (S.disjoint_horizontal hy a b) hz hzs),
    hL.1 a b y (S.disjoint_horizontal hy a b)⟩

/-- **Proposition 2.3, vertical lines.**  For `x ∉ pₓ(Ssing)` and all real `a, b`, the cell graph
of `{x} × [a,b]` is finite (Lemma 2.2) and connected ((LCS)). -/
theorem vertical_finite_and_connected (S : SingularSet C) (hL : C.LineConnectedOff S.sing)
    {x : ℝ} (hx : x ∉ coordProj 0 '' S.sing) (a b : ℝ) :
    {v | C.Hits (vertical x a b) v}.Finite ∧ C.InducedConnected (vertical x a b) :=
  ⟨S.finite_hits_of_isCompact (isCompact_vertical x a b)
      (fun _ hz hzs => Set.disjoint_left.mp (S.disjoint_vertical hx a b) hz hzs),
    hL.2 x a b (S.disjoint_vertical hx a b)⟩

end SingularSet

/-- Reachability inside an induced graph gives reachability in the full graph. -/
theorem reachable_of_inducedConnected {V : Type*} {C : CellConfiguration V} {A : Set Plane}
    (hA : C.InducedConnected A) {v w : V} (hv : C.Hits A v) (hw : C.Hits A w) :
    C.graph.Reachable v w :=
  (hA ⟨v, hv⟩ ⟨w, hw⟩).map (SimpleGraph.Embedding.induce {u | C.Hits A u}).toHom

end CellConfiguration

open CellConfiguration

namespace GeneralGeometry

variable {V : Type*} {C : CellConfiguration V}

/-- **Proposition 2.3, generic lines**, with the manuscript's exceptional sets
`Nh = p_y(Ssing)` and `Nv = pₓ(Ssing)` for a witness `Ssing` satisfying (LCS): these are Borel and
Lebesgue-null, and simultaneously for all real `a, b` the cell graphs of the good segments are finite
and connected. -/
theorem exists_generic_lines (h : GeneralGeometry C) :
    ∃ S : SingularSet C, C.LineConnectedOff S.sing ∧
      MeasurableSet (coordProj 1 '' S.sing) ∧ volume (coordProj 1 '' S.sing) = 0 ∧
      MeasurableSet (coordProj 0 '' S.sing) ∧ volume (coordProj 0 '' S.sing) = 0 ∧
      (∀ y ∉ coordProj 1 '' S.sing, ∀ a b : ℝ,
        {v | C.Hits (horizontal a b y) v}.Finite ∧ C.InducedConnected (horizontal a b y)) ∧
      (∀ x ∉ coordProj 0 '' S.sing, ∀ a b : ℝ,
        {v | C.Hits (vertical x a b) v}.Finite ∧ C.InducedConnected (vertical x a b)) := by
  obtain ⟨S, hL⟩ := h.exists_singularSet
  exact ⟨S, hL, S.measurableSet_image_coordProj 1, S.volume_image_coordProj 1,
    S.measurableSet_image_coordProj 0, S.volume_image_coordProj 0,
    fun y hy a b => S.horizontal_finite_and_connected hL hy a b,
    fun x hx a b => S.vertical_finite_and_connected hL hx a b⟩

/-- **Proposition 2.3, generic lines**, with the exceptional sets packaged as measurable null sets
of offsets. -/
theorem exists_null_sets_segment_finite_and_connected (h : GeneralGeometry C) :
    ∃ Nh Nv : Set ℝ, MeasurableSet Nh ∧ volume Nh = 0 ∧ MeasurableSet Nv ∧ volume Nv = 0 ∧
      (∀ y ∉ Nh, ∀ a b : ℝ,
        {v | C.Hits (horizontal a b y) v}.Finite ∧ C.InducedConnected (horizontal a b y)) ∧
      (∀ x ∉ Nv, ∀ a b : ℝ,
        {v | C.Hits (vertical x a b) v}.Finite ∧ C.InducedConnected (vertical x a b)) := by
  obtain ⟨S, -, h1, h2, h3, h4, h5, h6⟩ := h.exists_generic_lines
  exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩

/-- **Proposition 2.3, graph connectedness.**  The full cell adjacency graph is connected.

Following the manuscript: for cells `H, K` choose `a ∈ H°` on a good horizontal line and
`b ∈ K°` on a good vertical line; their crossing point `p` avoids `Ssing`, so it lies in a cell `J`;
(LCS) on the horizontal segment from `a` to `p` and on the vertical segment from `p` to `b` gives
finite paths `H → J → K`.  Nonemptiness: `Ssing` is Lebesgue-null, so some point is covered. -/
theorem graph_connected (h : GeneralGeometry C) : C.graph.Connected := by
  obtain ⟨S, hL⟩ := h.exists_singularSet
  have hcompl : S.singᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hu
    have hint := S.interior_sing_eq_empty
    rw [hu, interior_univ] at hint
    exact Set.univ_nonempty.ne_empty hint
  obtain ⟨z₀, hz₀⟩ := hcompl
  obtain ⟨v₀, -⟩ := Set.mem_iUnion.mp (S.cover hz₀)
  rw [SimpleGraph.connected_iff]
  refine ⟨fun v w => ?_, ⟨v₀⟩⟩
  obtain ⟨a, hav, hay⟩ := exists_mem_of_isOpen_coord_one_notMem isOpen_interior
    (h.interior_nonempty v) (S.volume_image_coordProj 1)
  obtain ⟨b, hbw, hbx⟩ := exists_mem_of_isOpen_coord_zero_notMem isOpen_interior
    (h.interior_nonempty w) (S.volume_image_coordProj 0)
  set p : Plane := horizontalPoint (a 1) (b 0) with hpdef
  have hp0 : p 0 = b 0 := horizontalPoint_apply_zero _ _
  have hp1 : p 1 = a 1 := horizontalPoint_apply_one _ _
  have hps : p ∉ S.sing := fun hps => hay ⟨p, hps, hp1⟩
  obtain ⟨J, hpJ⟩ := Set.mem_iUnion.mp (S.cover hps)
  -- the horizontal segment from `a` to `p`
  have hvJ : C.graph.Reachable v J := by
    have hconn := (S.horizontal_finite_and_connected hL hay (min (a 0) (b 0))
      (max (a 0) (b 0))).2
    refine reachable_of_inducedConnected hconn ⟨a, interior_subset hav, ?_⟩ ⟨p, hpJ, ?_⟩
    · exact ⟨min_le_left _ _, le_max_left _ _, rfl⟩
    · refine ⟨?_, ?_, hp1⟩
      · rw [hp0]; exact min_le_right _ _
      · rw [hp0]; exact le_max_right _ _
  -- the vertical segment from `p` to `b`
  have hJw : C.graph.Reachable J w := by
    have hconn := (S.vertical_finite_and_connected hL hbx (min (a 1) (b 1))
      (max (a 1) (b 1))).2
    refine reachable_of_inducedConnected hconn ⟨p, hpJ, ?_⟩ ⟨b, interior_subset hbw, ?_⟩
    · refine ⟨hp0, ?_, ?_⟩
      · rw [hp1]; exact min_le_left _ _
      · rw [hp1]; exact le_max_left _ _
    · exact ⟨rfl, min_le_right _ _, le_max_right _ _⟩
  exact hvJ.trans hJw

/-- With locally finite rows, a configuration satisfying Definition 1.1 and (LCS) satisfies the
corpus' almost-everywhere line connectivity `AELineConnected`, with the exceptional offsets
`p_y(Ssing)` and `pₓ(Ssing)`. -/
theorem aeLineConnected_toIndexedCells (h : GeneralGeometry C) (hfin : C.LocallyFiniteGraph) :
    AELineConnected (C.toIndexedCells hfin) := by
  obtain ⟨S, hL⟩ := h.exists_singularSet
  rw [aeLineConnected_iff_exists_measurable_null_sets]
  exact ⟨_, _, S.measurableSet_image_coordProj 1, S.volume_image_coordProj 1,
    S.measurableSet_image_coordProj 0, S.volume_image_coordProj 0,
    fun y hy a b _ => (S.horizontal_finite_and_connected hL hy a b).2,
    fun x hx a b _ => (S.vertical_finite_and_connected hL hx a b).2⟩

end GeneralGeometry

end ReflectedGMS

assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.finite_hits_of_isCompact
assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.measurableSet_image_coordProj
assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.horizontal_finite_and_connected
assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.vertical_finite_and_connected
assert_no_sorry ReflectedGMS.GeneralGeometry.exists_generic_lines
assert_no_sorry ReflectedGMS.GeneralGeometry.exists_null_sets_segment_finite_and_connected
assert_no_sorry ReflectedGMS.GeneralGeometry.graph_connected
assert_no_sorry ReflectedGMS.GeneralGeometry.aeLineConnected_toIndexedCells
#print axioms ReflectedGMS.CellConfiguration.SingularSet.finite_hits_of_isCompact
#print axioms ReflectedGMS.CellConfiguration.SingularSet.measurableSet_image_coordProj
#print axioms ReflectedGMS.CellConfiguration.SingularSet.horizontal_finite_and_connected
#print axioms ReflectedGMS.CellConfiguration.SingularSet.vertical_finite_and_connected
#print axioms ReflectedGMS.GeneralGeometry.exists_generic_lines
#print axioms ReflectedGMS.GeneralGeometry.exists_null_sets_segment_finite_and_connected
#print axioms ReflectedGMS.GeneralGeometry.graph_connected
#print axioms ReflectedGMS.GeneralGeometry.aeLineConnected_toIndexedCells
