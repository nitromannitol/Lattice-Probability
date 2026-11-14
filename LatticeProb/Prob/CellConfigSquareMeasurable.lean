import LatticeProb.Prob.CellConfigCellMassMeasurable

/-!
# Joint measurability of the cell mass of the dyadic squares

The capped square `S_m^w` of a cell configuration `H` (Gwynne, Miller and Sheffield, *An
invariance principle for ergodic scale-free random environments*, arXiv 1807.07515, (2.1)) is
selected among the squares `squareAt q j w` of the uniform dyadic system with coordinates
`q = (s, o¹, o²)` by comparing the mass `m` with the cell masses of consecutive generations. To
integrate over the configuration, the dyadic system and the point (as in the mass transport
argument of Lemma 2.3 of that paper) these cell masses must be measurable jointly in `(H, q, w)`.

The cell mass of a set depending measurably on a parameter (a set with measurable graph) is a
measurable function of the configuration and the parameter: the area of the part of a cell lying
in the section is measurable by Tonelli's theorem, and the cell mass is the sum over the label
slots of the configuration. The corners and the side of the dyadic squares are measurable
functions of `(q, w)`, so the graph of `(q, w) ↦ squareAt q j w` is measurable.

## Main statements

* `LatticeProb.CellConfigCappedSquare.measurable_cellMass_complexCells_section`: for a measurable
  set `E ⊆ α × ℂ`, `(H, x) ↦ cellMass (cells of H) {w | (x, w) ∈ E}` is measurable.
* `LatticeProb.CellConfigCappedSquare.measurableSet_squareAt_graph`: the graph of
  `(q, w) ↦ squareAt q j w` is measurable.
* `LatticeProb.CellConfigCappedSquare.measurable_cellMass_squareAt`: the cell mass of
  `squareAt q j w` is measurable in `(H, q, w)`.
* `LatticeProb.CellConfigCappedSquare.measurableSet_cellMass_squareAt_le_lt`: the event that `m`
  lies between the cell masses of the generations `j` and `j + 1` is measurable.
* `LatticeProb.CellConfigCappedSquare.measurable_setLIntegral_section`: integrals over the
  sections of a measurable set are measurable in the parameter.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass DyadicOffset

variable {α : Type*} [MeasurableSpace α]

/-! ### Cell masses of sets depending on a parameter -/

/-- The area of the part of a cell lying in the section `{z | (x, z) ∈ E}` of a measurable set is
a measurable function of the cell and the parameter (Tonelli's theorem). -/
theorem measurable_volume_inter_section {E : Set (α × Plane)} (hE : MeasurableSet E) :
    Measurable fun p : Code.CompactCell × α =>
      volume ((p.1 : Set Plane) ∩ {z | (p.2, z) ∈ E}) := by
  have hF : MeasurableSet
      {q : (Code.CompactCell × α) × Plane | q.2 ∈ (q.1.1 : Set Plane) ∧ (q.1.2, q.2) ∈ E} :=
    (Spatial.measurableSet_cellMem.preimage (measurable_fst.fst.prodMk measurable_snd)).inter
      (hE.preimage (measurable_fst.snd.prodMk measurable_snd))
  have h : (fun p : Code.CompactCell × α => volume ((p.1 : Set Plane) ∩ {z | (p.2, z) ∈ E})) =
      fun p => ∫⁻ z, {q : (Code.CompactCell × α) × Plane |
        q.2 ∈ (q.1.1 : Set Plane) ∧ (q.1.2, q.2) ∈ E}.indicator (fun _ => (1 : ℝ≥0∞)) (p, z) := by
    funext p
    have hs : MeasurableSet ((p.1 : Set Plane) ∩ {z | (p.2, z) ∈ E}) :=
      p.1.isCompact.isClosed.measurableSet.inter (measurable_prodMk_left hE)
    rw [← lintegral_indicator_one hs]
    rfl
  rw [h]
  exact (measurable_const.indicator hF).lintegral_prod_right' (ν := (volume : Measure Plane))

/-- The fraction of the area of a cell lying in the section of a measurable set is jointly
measurable. -/
theorem measurable_cellFraction_section {E : Set (α × Plane)} (hE : MeasurableSet E) :
    Measurable fun p : Code.CompactCell × α => cellFraction {z | (p.2, z) ∈ E} p.1 :=
  (measurable_volume_inter_section hE).div (Spatial.measurable_cellVolume.comp measurable_fst)

theorem measurable_slotMass_section {E : Set (α × Plane)} (hE : MeasurableSet E) (n : ℕ) :
    Measurable fun p : GMSSpace × α => slotMass {z | (p.2, z) ∈ E} p.1.1 n := by
  have h : (fun p : GMSSpace × α => slotMass {z | (p.2, z) ∈ E} p.1.1 n) =
      (labelSet n ×ˢ (univ : Set α)).indicator
        (fun p => cellFraction {z | (p.2, z) ∈ E} (interiorCell (Code.rationalPoint n) p.1)) := by
    funext p
    rw [slotMass_eq_indicator]
    by_cases hp : p.1 ∈ labelSet n
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem (show p ∈ labelSet n ×ˢ (univ : Set α) from ⟨hp, mem_univ _⟩)]
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ labelSet n ×ˢ (univ : Set α) from fun h => hp h.1)]
  rw [h]
  exact ((measurable_cellFraction_section hE).comp
    (((measurable_interiorCell _).comp measurable_fst).prodMk measurable_snd)).indicator
    ((measurableSet_labelSet n).prod MeasurableSet.univ)

/-- **The cell mass of a set depending measurably on a parameter is jointly measurable** in the
configuration and the parameter. -/
theorem measurable_cellMass_planeCells_section {E : Set (α × Plane)} (hE : MeasurableSet E) :
    Measurable fun p : GMSSpace × α => cellMass volume (planeCells p.1.1) {z | (p.2, z) ∈ E} := by
  have h : (fun p : GMSSpace × α => cellMass volume (planeCells p.1.1) {z | (p.2, z) ∈ E}) =
      fun p => ∑' n, slotMass {z | (p.2, z) ∈ E} p.1.1 n :=
    funext fun p => cellMass_planeCells_eq_tsum_slotMass p.1.2 _
  rw [h]
  exact Measurable.tsum fun n => measurable_slotMass_section hE n

/-- The same for the cells pulled back to `ℂ`. -/
theorem measurable_cellMass_complexCells_section {E : Set (α × ℂ)} (hE : MeasurableSet E) :
    Measurable fun p : GMSSpace × α => cellMass volume (complexCells p.1.1) {w | (p.2, w) ∈ E} := by
  have hE' : MeasurableSet {q : α × Plane | (q.1, planeCoord.symm q.2) ∈ E} :=
    hE.preimage (measurable_fst.prodMk (planeCoord.symm.continuous.measurable.comp measurable_snd))
  have h : (fun p : GMSSpace × α => cellMass volume (complexCells p.1.1) {w | (p.2, w) ∈ E}) =
      fun p => cellMass volume (planeCells p.1.1)
        {z | (p.2, z) ∈ {q : α × Plane | (q.1, planeCoord.symm q.2) ∈ E}} := by
    funext p
    rw [cellMass_complexCells, LinearIsometryEquiv.image_eq_preimage_symm]
    rfl
  rw [h]
  exact measurable_cellMass_planeCells_section hE'

/-- Integrals over the sections of a measurable set are measurable in the parameter. -/
theorem measurable_setLIntegral_section {E : Set (α × ℂ)} (hE : MeasurableSet E)
    {G : α × ℂ → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun x : α => ∫⁻ z in {z | (x, z) ∈ E}, G (x, z) := by
  have h : (fun x : α => ∫⁻ z in {z | (x, z) ∈ E}, G (x, z)) =
      fun x => ∫⁻ z, E.indicator G (x, z) := by
    funext x
    have hs : MeasurableSet {z | (x, z) ∈ E} := measurable_prodMk_left hE
    rw [← lintegral_indicator hs]
    rfl
  rw [h]
  exact (hG.indicator hE).lintegral_prod_right' (ν := (volume : Measure ℂ))

/-! ### The dyadic squares -/

/-- The graph of `(a, b, ℓ) ↦ cornerSquare a b ℓ` is measurable. -/
theorem measurableSet_cornerSquare_graph :
    MeasurableSet {p : (ℝ × ℝ × ℝ) × ℂ | p.2 ∈ cornerSquare p.1.1 p.1.2.1 p.1.2.2} := by
  have h1 : Measurable fun p : (ℝ × ℝ × ℝ) × ℂ => p.2.re := Complex.measurable_re.comp measurable_snd
  have h2 : Measurable fun p : (ℝ × ℝ × ℝ) × ℂ => p.2.im := Complex.measurable_im.comp measurable_snd
  have ha : Measurable fun p : (ℝ × ℝ × ℝ) × ℂ => p.1.1 := measurable_fst.fst
  have hb : Measurable fun p : (ℝ × ℝ × ℝ) × ℂ => p.1.2.1 := measurable_fst.snd.fst
  have hl : Measurable fun p : (ℝ × ℝ × ℝ) × ℂ => p.1.2.2 := measurable_fst.snd.snd
  exact (measurableSet_le ha h1).inter ((measurableSet_le h1 (ha.add hl)).inter
    ((measurableSet_le hb h2).inter (measurableSet_le h2 (hb.add hl))))

theorem measurable_latticeFloor {β : Type*} [MeasurableSpace β] {c p x : β → ℝ}
    (hc : Measurable c) (hp : Measurable p) (hx : Measurable x) :
    Measurable fun b => latticeFloor (c b) (p b) (x b) := by
  unfold latticeFloor
  exact hc.add (((measurable_of_countable (Int.cast : ℤ → ℝ)).comp
    ((hx.sub hc).div hp).floor).mul hp)

/-- The left end of the grid interval of generation `j` containing `x` is measurable in the scale,
the offsets and `x`. -/
theorem measurable_gridFloor {β : Type*} [MeasurableSpace β] (j : ℤ) {s : β → ℝ}
    {o : β → ℕ → ℝ} {x : β → ℝ} (hs : Measurable s) (ho : Measurable o) (hx : Measurable x) :
    Measurable fun b => gridFloor (s b) (o b) j (x b) := by
  unfold gridFloor
  exact measurable_latticeFloor
    ((measurable_const.pow hs).mul ((measurable_pi_apply j.toNat).comp ho)).neg
    (measurable_const.pow (hs.add_const _)) hx

/-- **The graph of `(q, w) ↦ squareAt q j w` is measurable**, for every generation `j`. -/
theorem measurableSet_squareAt_graph (j : ℤ) :
    MeasurableSet {p : ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) × ℂ |
      p.2 ∈ squareAt p.1.1.1 p.1.1.2.1 p.1.1.2.2 j p.1.2} := by
  have hs : Measurable fun p : ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) × ℂ => p.1.1.1 :=
    measurable_fst.fst.fst
  have hw : Measurable fun p : ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) × ℂ => p.1.2 := measurable_fst.snd
  have hf : Measurable fun p : ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) × ℂ =>
      ((gridFloor p.1.1.1 p.1.1.2.1 j p.1.2.re, gridFloor p.1.1.1 p.1.1.2.2 j p.1.2.im,
        (2 : ℝ) ^ (p.1.1.1 + (j : ℝ))), p.2) :=
    ((measurable_gridFloor j hs measurable_fst.fst.snd.fst (Complex.measurable_re.comp hw)).prodMk
      ((measurable_gridFloor j hs measurable_fst.fst.snd.snd (Complex.measurable_im.comp hw)).prodMk
        (measurable_const.pow (hs.add_const _)))).prodMk measurable_snd
  exact measurableSet_cornerSquare_graph.preimage hf

/-- **Joint measurability of the cell mass of the dyadic squares**: for every generation `j`, the
cell mass of `squareAt q j w` for the configuration `H` is a measurable function of `(H, q, w)`. -/
theorem measurable_cellMass_squareAt (j : ℤ) :
    Measurable fun p : GMSSpace × ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) =>
      cellMass volume (complexCells p.1.1) (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2) := by
  have h := measurable_cellMass_complexCells_section (measurableSet_squareAt_graph j)
  exact h

/-- **The selection event of the capped square is measurable**: the event that the mass `m` lies
between the cell masses of the squares of generations `j` and `j + 1` around `w` is a measurable
set of `(H, q, w)`. -/
theorem measurableSet_cellMass_squareAt_le_lt (j : ℤ) (m : ℝ≥0∞) :
    MeasurableSet {p : GMSSpace × ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) |
      cellMass volume (complexCells p.1.1) (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2) ≤ m ∧
      m < cellMass volume (complexCells p.1.1)
        (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 (j + 1) p.2.2)} :=
  (measurableSet_le (measurable_cellMass_squareAt j) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_cellMass_squareAt (j + 1)))

/-- The integral of a measurable function over the square `squareAt q j w` is measurable in the
parameters. -/
theorem measurable_setLIntegral_squareAt (j : ℤ)
    {G : ((ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ) × ℂ → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun x : (ℝ × (ℕ → ℝ) × (ℕ → ℝ)) × ℂ =>
      ∫⁻ z in squareAt x.1.1 x.1.2.1 x.1.2.2 j x.2, G (x, z) := by
  have h := measurable_setLIntegral_section (measurableSet_squareAt_graph j) hG
  exact h

end LatticeProb.CellConfigCappedSquare
