import LatticeProb.Prob.CellConfigCovariantDyadicRelatives
import LatticeProb.Prob.CellConfigNonnegAverage
import LatticeProb.Prob.CellConfigKernelExactCovariance
import LatticeProb.Prob.CellConfigKernelReverse
import LatticeProb.Prob.CellConfigCellMassMeasurable
import LatticeProb.Prob.CondExpJointInvariant
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# The cells of a cell configuration are small compared with the squares around the origin

Let `H` be a random cell configuration with law `μ` satisfying the mass-transport principle and
`D` an independent uniform dyadic system, with `S_k` the square of `D` of generation `k`
containing the origin and `|S_k|` its side length. Gwynne, Miller and Sheffield (*An invariance
principle for ergodic scale-free random environments*, arXiv 1807.07515, Lemma 2.9) prove that
almost surely, for each `ε ∈ (0, 1)` and every large enough `k`, every cell `K ∈ H(S_k)` (a cell
meeting `S_k`) satisfies `diam(K) ≤ ε |S_k|`.

We follow the printed proof, with the conditional form of the ergodic lemma (no ergodicity is
assumed: the limits are conditional expectations given the tail σ-algebra `𝓘`).

* **Cells inside the squares (2.8).** For a mass `m`, the *large-cell density*
  `G_{ε,m}(H, D, w) = Σ_{K ∋ w} diam(K)² / Area(K)`, the sum over the cells `K` containing `w` with
  `ε² |S| < diam(K)²` for every square `S` of `D` around `w` of cell mass at most `m`, is invariant
  under the joint similarity and bounded at the origin by the root ratio
  `Σ_{K ∋ 0} diam(K)² / Area(K)`. Along the squares `S_j` its uniform averages converge to
  `E[G_{ε,m}(H, D, 0) | 𝓘]` (the conditional ergodic lemma), and these conditional expectations
  tend to `0` as `m → ∞` (conditional monotone convergence; the threshold `m` is chosen from them,
  hence `𝓘`-measurably). A cell `K ⊆ S_j` with `diam(K) > ε |S_j|` contributes at least
  `diam(K)² / |S_j|² > ε²` to the average over `S_j` once the cell mass of `S_j` exceeds `m`.
* **Cells meeting the boundary.** A cell `K` meeting `S_k` with `diam(K) < |S_{k'}|` lies in the
  dyadic ancestor of side `4 |S_{k'}|` of `S_{k'}` in which `S_{k'}` occupies the second column and
  row. Given (2.8) for these ancestors (Lemma 2.8 of arXiv 1807.07515 for the similarity-covariant
  event `SmallInnerCells δ`), the minimal `k' ≥ k` with `diam(K) < ε |S_{k'}|` must be `k`.

## Main definitions
* `IsLargeAtMass`, `largeCellDensity`: the large-cell density `G_{ε,m}`.
* `originCellRatioSum`: `Σ_{K ∋ 0} diam(K)² / Area(K)`.
* `SmallInnerCells δ H S`: every cell of `H` contained in `S` has `diam(K)² ≤ δ² Area(S)`.
* `originAncestorSquare q k`: the dyadic ancestor of side `4 |S_k|` of `S_k` described above.

## Main results
* `largeCellDensity_similarity`, `smallInnerCells_similarity`: similarity invariance.
* `ae_ae_eventually_smallInnerCells_squareAt`: (2.8), almost surely for every `δ > 0`, eventually
  every cell contained in `S_k` has `diam(K)² ≤ δ² |S_k|²`.
* `ae_ae_eventually_diam_le`: Lemma 2.9, (2.5).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-! ### Sums over the cells and the label slots -/

/-- A sum over the cells of a cell configuration is the sum over its label slots. -/
theorem tsum_cells_eq_tsum_slot {H : CellConfig} (hH : H.IsCellConfiguration)
    (f : Cell → ℝ≥0∞) : ∑' K : H.cells, f K = ∑' n, (H.slot n).elim 0 f := by
  have hinj : Function.Injective (CellConfig.label hH) := by
    intro K K' h
    have h1 := CellConfig.slot_label hH K
    have h2 := CellConfig.slot_label hH K'
    rw [h] at h1
    exact Subtype.ext (Option.some_inj.mp (h1.symm.trans h2))
  have hsupp : Function.support (fun n => (H.slot n).elim 0 f) ⊆
      Set.range (CellConfig.label hH) := by
    intro n hn
    cases hs : H.slot n with
    | none =>
      exact absurd (by simp only [hs, Option.elim]) hn
    | some K =>
      obtain ⟨hK, hl⟩ := (CellConfig.slot_eq_some_iff hH).1 hs
      exact ⟨⟨K, hK⟩, leastInteriorLabel_unique (CellConfig.leastInteriorLabel_label hH ⟨K, hK⟩) hl⟩
  rw [← hinj.tsum_eq hsupp]
  congr 1
  funext K
  simp only [CellConfig.slot_label hH K, Option.elim]

theorem slot_elim_eq_indicator (H : GMSSpace) (n : ℕ) (f : Cell → ℝ≥0∞) :
    (H.1.slot n).elim 0 f =
      (labelSet n).indicator (fun H => f (interiorCell (Code.rationalPoint n) H)) H := by
  by_cases h : H ∈ labelSet n
  · rw [slot_eq, Set.indicator_of_mem h]
    simp only [h, ↓reduceIte, Option.elim]
  · rw [slot_eq, Set.indicator_of_notMem h]
    simp only [h, ↓reduceIte, Option.elim]

/-- **A sum over the cells of a measurable function of the cell is measurable** in the
configuration and the parameters. -/
theorem measurable_tsum_cells {α : Type*} [MeasurableSpace α] {φ : α → GMSSpace}
    (hφ : Measurable φ) {g : α × Cell → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun a => ∑' K : (φ a).1.cells, g (a, K) := by
  have h : (fun a => ∑' K : (φ a).1.cells, g (a, K)) = fun a =>
      ∑' n, {a | φ a ∈ labelSet n}.indicator
        (fun a => g (a, interiorCell (Code.rationalPoint n) (φ a))) a := by
    funext a
    refine (tsum_cells_eq_tsum_slot (φ a).2 (fun K => g (a, K))).trans (tsum_congr fun n => ?_)
    rw [slot_elim_eq_indicator]
    by_cases h : φ a ∈ labelSet n
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show a ∈ {a | φ a ∈ labelSet n} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show a ∉ {a | φ a ∈ labelSet n} from h)]
  rw [h]
  exact Measurable.tsum fun n =>
    (hg.comp (measurable_id.prodMk ((measurable_interiorCell _).comp hφ))).indicator
      (hφ (measurableSet_labelSet n))

/-! ### The large-cell density -/

/-- The ratio `diam(K)² / Area(K)` of a cell. -/
noncomputable def cellRatio (K : Cell) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2) / volume (K : Set Plane)

theorem measurable_cellRatio : Measurable cellRatio :=
  (ENNReal.measurable_ofReal.comp (Spatial.measurable_cellDiam.pow_const 2)).div
    Spatial.measurable_cellVolume

/-- The cell `K` is **large at mass `m`** for the rooted configuration `p = (H, q, w)`: for every
square `S` of the dyadic system around `w` of cell mass at most `m`, `ε² Area(S) < diam(K)²`. -/
def IsLargeAtMass (ε : ℝ) (m : ℝ≥0∞) (p : GMSSpace × DyadicCoord × ℂ) (K : Cell) : Prop :=
  ∀ j : ℤ, cellMass volume (complexCells p.1.1) (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2) ≤ m →
    ENNReal.ofReal (ε ^ 2) * volume (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2) <
      ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2)

/-- The rooted configurations and cells such that the cell contains the root and is large at mass
`m`. -/
def largeCellSet (ε : ℝ) (m : ℝ≥0∞) : Set ((GMSSpace × DyadicCoord × ℂ) × Cell) :=
  {x | planeCoord x.1.2.2 ∈ (x.2 : Set Plane) ∧ IsLargeAtMass ε m x.1 x.2}

/-- **The large-cell density** `G_{ε,m}(H, D, w) = Σ diam(K)² / Area(K)`, the sum over the cells
`K ∋ w` which are large at mass `m`. -/
noncomputable def largeCellDensity (ε : ℝ) (m : ℝ≥0∞) (p : GMSSpace × DyadicCoord × ℂ) : ℝ≥0∞ :=
  ∑' K : p.1.1.cells, (largeCellSet ε m).indicator (fun x => cellRatio x.2) (p, (K : Cell))

/-- **The root ratio** `Σ_{K ∋ 0} diam(K)² / Area(K)` (for almost every configuration under the
mass-transport principle the origin lies in a single cell `H₀`, and this is
`diam(H₀)² / Area(H₀)`). -/
noncomputable def originCellRatioSum (H : GMSSpace) : ℝ≥0∞ :=
  ∑' K : H.1.cells, {K : Cell | (0 : Plane) ∈ (K : Set Plane)}.indicator cellRatio K

theorem measurableSet_largeCellSet (ε : ℝ) (m : ℝ≥0∞) : MeasurableSet (largeCellSet ε m) := by
  have hmem : MeasurableSet
      {x : (GMSSpace × DyadicCoord × ℂ) × Cell | planeCoord x.1.2.2 ∈ (x.2 : Set Plane)} :=
    Spatial.measurableSet_cellMem.preimage
      (measurable_snd.prodMk (planeCoord.continuous.measurable.comp measurable_fst.snd.snd))
  have hlarge : MeasurableSet
      {x : (GMSSpace × DyadicCoord × ℂ) × Cell | IsLargeAtMass ε m x.1 x.2} := by
    have h : {x : (GMSSpace × DyadicCoord × ℂ) × Cell | IsLargeAtMass ε m x.1 x.2} =
        ⋂ j : ℤ, ({x : (GMSSpace × DyadicCoord × ℂ) × Cell | cellMass volume
          (complexCells x.1.1.1) (squareAt x.1.2.1.1 x.1.2.1.2.1 x.1.2.1.2.2 j x.1.2.2) ≤ m}ᶜ ∪
          {x | ENNReal.ofReal (ε ^ 2) * volume (squareAt x.1.2.1.1 x.1.2.1.2.1 x.1.2.1.2.2 j x.1.2.2) <
            ENNReal.ofReal (Metric.diam (x.2 : Set Plane) ^ 2)}) := by
      ext x
      simp only [IsLargeAtMass, mem_iInter, mem_union, mem_compl_iff, Set.mem_ofPred_eq,
        imp_iff_not_or]
    rw [h]
    refine MeasurableSet.iInter fun j => MeasurableSet.union (MeasurableSet.compl ?_) ?_
    · exact measurableSet_le ((measurable_cellMass_squareAt j).comp measurable_fst) measurable_const
    · exact measurableSet_lt
        (measurable_const.mul ((measurable_volume_squareAt j).comp measurable_fst.snd))
        (ENNReal.measurable_ofReal.comp ((Spatial.measurable_cellDiam.comp measurable_snd).pow_const 2))
  exact hmem.inter hlarge

theorem measurable_largeCellDensity (ε : ℝ) (m : ℝ≥0∞) : Measurable (largeCellDensity ε m) := by
  unfold largeCellDensity
  exact measurable_tsum_cells measurable_fst
    (g := fun x => (largeCellSet ε m).indicator (fun x => cellRatio x.2) x)
    ((measurable_cellRatio.comp measurable_snd).indicator (measurableSet_largeCellSet ε m))

theorem measurable_originCellRatioSum : Measurable originCellRatioSum := by
  have hset : MeasurableSet {K : Cell | (0 : Plane) ∈ (K : Set Plane)} :=
    Spatial.measurableSet_cellMem.preimage (measurable_id.prodMk measurable_const)
  unfold originCellRatioSum
  exact measurable_tsum_cells measurable_id
    (g := fun x : GMSSpace × Cell =>
      {K : Cell | (0 : Plane) ∈ (K : Set Plane)}.indicator cellRatio x.2)
    ((measurable_cellRatio.indicator hset).comp measurable_snd)

/-- The large-cell density decreases as the mass increases. -/
theorem largeCellDensity_anti (ε : ℝ) {m m' : ℝ≥0∞} (hmm' : m ≤ m')
    (p : GMSSpace × DyadicCoord × ℂ) : largeCellDensity ε m' p ≤ largeCellDensity ε m p := by
  have hsub : largeCellSet ε m' ⊆ largeCellSet ε m := fun x hx =>
    ⟨hx.1, fun j hj => hx.2 j (hj.trans hmm')⟩
  exact ENNReal.tsum_le_tsum fun K =>
    Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) _

/-- At the origin, the large-cell density is at most the root ratio. -/
theorem largeCellDensity_origin_le (ε : ℝ) (m : ℝ≥0∞) (H : GMSSpace) (q : DyadicCoord) :
    largeCellDensity ε m (H, q, 0) ≤ originCellRatioSum H := by
  unfold largeCellDensity originCellRatioSum
  refine ENNReal.tsum_le_tsum fun K => ?_
  by_cases h : ((H, q, (0 : ℂ)), (K : Cell)) ∈ largeCellSet ε m
  · have h0 : (0 : Plane) ∈ ((K : Cell) : Set Plane) := by simpa using h.1
    rw [Set.indicator_of_mem h,
      Set.indicator_of_mem (show (K : Cell) ∈ {K : Cell | (0 : Plane) ∈ (K : Set Plane)} from h0)]
  · rw [Set.indicator_of_notMem h]
    exact zero_le

/-- For a uniform dyadic system, the expected large-cell density at the origin is at most the
expected root ratio. -/
theorem lintegral_largeCellDensity_origin_ne_top {μ : Measure GMSSpace}
    (hΦ : ∫⁻ H, originCellRatioSum H ∂μ ≠ ∞) (ε : ℝ) (m : ℝ≥0∞) :
    ∫⁻ p, largeCellDensity ε m (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hle : ∫⁻ p, largeCellDensity ε m (p.1, p.2, 0) ∂μ.prod dyadicLaw ≤
      ∫⁻ H, originCellRatioSum H ∂μ := by
    calc ∫⁻ p, largeCellDensity ε m (p.1, p.2, 0) ∂μ.prod dyadicLaw
        ≤ ∫⁻ p, originCellRatioSum p.1 ∂μ.prod dyadicLaw :=
          lintegral_mono fun p => largeCellDensity_origin_le ε m p.1 p.2
      _ = ∫⁻ H, originCellRatioSum H ∂μ := by
          rw [lintegral_prod (fun p : GMSSpace × DyadicCoord => originCellRatioSum p.1)
            (measurable_originCellRatioSum.comp measurable_fst).aemeasurable]
          simp only [lintegral_const, measure_univ, mul_one]
  exact (hle.trans_lt (lt_top_iff_ne_top.2 hΦ)).ne

/-! ### Similarity invariance -/

theorem ofReal_mul_sq (s d : ℝ) :
    ENNReal.ofReal ((s * d) ^ 2) = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (d ^ 2) := by
  rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg s)]

section Similarity

variable {H : CellConfig} {s : ℝ} (u : Plane) (hs : 0 < s)

theorem planeCoord_mem_similarityCellEquiv_iff (K : H.cells) (w : ℂ) :
    planeCoord (s • w + similarityOffset s u) ∈
        (((CellConfig.similarityCellEquiv s u hs K : (H.similarity s u hs).cells) : Cell) :
          Set Plane) ↔ planeCoord w ∈ ((K : Cell) : Set Plane) := by
  change s • w + similarityOffset s u ∈
      complexCells (H.similarity s u hs) (CellConfig.similarityCellEquiv s u hs K) ↔
    w ∈ complexCells H K
  rw [complexCells_similarity s u hs K]
  exact (injective_smul_add hs.ne' (similarityOffset s u)).mem_set_image

theorem diam_similarityCellEquiv (K : H.cells) :
    Metric.diam (((CellConfig.similarityCellEquiv s u hs K : (H.similarity s u hs).cells) : Cell) :
      Set Plane) = s * Metric.diam ((K : Cell) : Set Plane) := by
  rw [CellConfig.coe_similarityCellEquiv, coe_transformCell,
    Spatial.diam_image_positiveSimilarity s u hs]

theorem volume_similarityCellEquiv (K : H.cells) :
    volume (((CellConfig.similarityCellEquiv s u hs K : (H.similarity s u hs).cells) : Cell) :
      Set Plane) = ENNReal.ofReal (s ^ 2) * volume ((K : Cell) : Set Plane) := by
  rw [← volume_complexCells (CellConfig.similarityCellEquiv s u hs K),
    complexCells_similarity s u hs K, volume_image_smul_add_similarityOffset, volume_complexCells]

end Similarity

/-- **Similarity invariance of the large-cell density**: `G_{ε,m}` is invariant under the joint
similarity of the configuration, the dyadic system and the root. -/
theorem largeCellDensity_similarity (ε : ℝ) (m : ℝ≥0∞) :
    ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        largeCellDensity ε m (H', similarityCoord s u q, s • w + similarityOffset s u) =
          largeCellDensity ε m (H, q, w) := by
  intro s u hs H H' hHH' q h₁ h₂ w
  obtain ⟨H'c, hH'c⟩ := H'
  have e : H'c = H.1.similarity s u hs := hHH'
  subst e
  have hs2 : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  unfold largeCellDensity
  refine ((CellConfig.similarityCellEquiv s u hs).tsum_eq _).symm.trans (tsum_congr fun K => ?_)
  have hcut : IsLargeAtMass ε m (⟨H.1.similarity s u hs, hH'c⟩, similarityCoord s u q,
        s • w + similarityOffset s u)
        ((CellConfig.similarityCellEquiv s u hs K : (H.1.similarity s u hs).cells) : Cell) ↔
      IsLargeAtMass ε m (H, q, w) (K : Cell) := by
    have key : ∀ j : ℤ,
        (cellMass volume (complexCells (H.1.similarity s u hs))
            (squareAt (similarityCoord s u q).1 (similarityCoord s u q).2.1
              (similarityCoord s u q).2.2 (j + ⌊q.1 + Real.logb 2 s⌋)
              (s • w + similarityOffset s u)) ≤ m →
          ENNReal.ofReal (ε ^ 2) * volume (squareAt (similarityCoord s u q).1
              (similarityCoord s u q).2.1 (similarityCoord s u q).2.2 (j + ⌊q.1 + Real.logb 2 s⌋)
              (s • w + similarityOffset s u)) <
            ENNReal.ofReal (Metric.diam
              (((CellConfig.similarityCellEquiv s u hs K : (H.1.similarity s u hs).cells) : Cell) :
                Set Plane) ^ 2)) ↔
        (cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j w) ≤ m →
          ENNReal.ofReal (ε ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 j w) <
            ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2)) := by
      intro j
      rw [squareAt_similarityCoord s u hs q h₁ h₂ j w,
        cellMass_complexCells_similarity_image s u hs, volume_image_smul_add_similarityOffset,
        diam_similarityCellEquiv u hs K, ofReal_mul_sq, mul_left_comm,
        ENNReal.mul_lt_mul_iff_right hs2 ENNReal.ofReal_ne_top]
    constructor
    · intro h j
      exact (key j).1 (h (j + ⌊q.1 + Real.logb 2 s⌋))
    · intro h j
      have hj := (key (j - ⌊q.1 + Real.logb 2 s⌋)).2 (h _)
      rwa [sub_add_cancel] at hj
  have hset : (((⟨H.1.similarity s u hs, hH'c⟩ : GMSSpace), similarityCoord s u q,
        s • w + similarityOffset s u),
        ((CellConfig.similarityCellEquiv s u hs K : (H.1.similarity s u hs).cells) : Cell)) ∈
        largeCellSet ε m ↔ ((H, q, w), (K : Cell)) ∈ largeCellSet ε m :=
    and_congr (planeCoord_mem_similarityCellEquiv_iff u hs K w) hcut
  by_cases h : ((H, q, w), (K : Cell)) ∈ largeCellSet ε m
  · rw [Set.indicator_of_mem (hset.2 h), Set.indicator_of_mem h]
    simp only [cellRatio]
    rw [diam_similarityCellEquiv u hs K, volume_similarityCellEquiv u hs K, ofReal_mul_sq,
      ENNReal.mul_div_mul_left _ _ hs2 ENNReal.ofReal_ne_top]
  · rw [Set.indicator_of_notMem (fun h' => h (hset.1 h')), Set.indicator_of_notMem h]

/-! ### Small cells inside a square: the covariant event -/

/-- The event `E_δ(S, H)`: every cell `K` of `H` contained in `S` has `diam(K)² ≤ δ² Area(S)`
(for a square, `diam(K) ≤ δ |S|`). -/
def SmallInnerCells (δ : ℝ) (H : GMSSpace) (S : Set ℂ) : Prop :=
  ∀ K : H.1.cells, complexCells H.1 K ⊆ S →
    ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) ≤ ENNReal.ofReal (δ ^ 2) * volume S

/-- **The event `E_δ` is similarity covariant**: `E_δ(C(S - u), C(H - u)) ↔ E_δ(S, H)`, the
similarity `z ↦ s (z - u)` reading `z ↦ s • z + b` in the coordinates `ℂ`. -/
theorem smallInnerCells_similarity (δ : ℝ) {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (hHH' : IsSimilar s u hs H H') (S : Set ℂ) :
    SmallInnerCells δ H' ((fun z : ℂ => s • z + similarityOffset s u) '' S) ↔
      SmallInnerCells δ H S := by
  obtain ⟨H'c, hH'c⟩ := H'
  have e : H'c = H.1.similarity s u hs := hHH'
  subst e
  have hinj := injective_smul_add (V := ℂ) hs.ne' (similarityOffset s u)
  have hs2 : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  constructor
  · intro h K hK
    have hK' : complexCells (H.1.similarity s u hs) (CellConfig.similarityCellEquiv s u hs K) ⊆
        (fun z : ℂ => s • z + similarityOffset s u) '' S := by
      rw [complexCells_similarity s u hs K]
      exact image_mono hK
    have h1 := h (CellConfig.similarityCellEquiv s u hs K) hK'
    rw [diam_similarityCellEquiv u hs K, volume_image_smul_add_similarityOffset, ofReal_mul_sq,
      mul_left_comm] at h1
    exact not_lt.1 fun hlt =>
      (not_le.2 ((ENNReal.mul_lt_mul_iff_right hs2 ENNReal.ofReal_ne_top).2 hlt)) h1
  · intro h K' hK'
    obtain ⟨K, rfl⟩ := (CellConfig.similarityCellEquiv s u hs).surjective K'
    have hK : complexCells H.1 K ⊆ S := by
      have hK'' : complexCells (H.1.similarity s u hs) (CellConfig.similarityCellEquiv s u hs K) ⊆
          (fun z : ℂ => s • z + similarityOffset s u) '' S := hK'
      rw [complexCells_similarity s u hs K] at hK''
      exact (image_subset_image_iff hinj).1 hK''
    show ENNReal.ofReal (Metric.diam (((CellConfig.similarityCellEquiv s u hs K :
        (H.1.similarity s u hs).cells) : Cell) : Set Plane) ^ 2) ≤
      ENNReal.ofReal (δ ^ 2) * volume ((fun z : ℂ => s • z + similarityOffset s u) '' S)
    rw [diam_similarityCellEquiv u hs K, volume_image_smul_add_similarityOffset, ofReal_mul_sq,
      mul_left_comm]
    gcongr
    exact h K hK

/-! ### The large-cell density at the origin vanishes for large masses -/

/-- For `ε > 0` and every `x`, some square of generation `t + n` has `x < ε 2^{t + n}`. -/
theorem exists_lt_mul_two_rpow (x : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ n : ℕ, x < ε * (2 : ℝ) ^ (t + (n : ℝ)) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / (ε * (2 : ℝ) ^ t)) one_lt_two
  refine ⟨n, ?_⟩
  have hpos : 0 < ε * (2 : ℝ) ^ t := by positivity
  rw [Real.rpow_add two_pos, Real.rpow_natCast, ← mul_assoc]
  rwa [div_lt_iff₀ hpos, mul_comm] at hn

/-- **For every configuration and every dyadic system, the large-cell density at the origin
vanishes for all large masses**: the finitely many cells containing the origin are not large at the
cell mass of a square around the origin of side at least `diam(K) / ε`. -/
theorem largeCellDensity_origin_eventually_eq_zero {ε : ℝ} (hε : 0 < ε) (H : GMSSpace)
    (q : DyadicCoord) : ∀ᶠ m : ℕ in atTop, largeCellDensity ε (m : ℝ≥0∞) (H, q, 0) = 0 := by
  obtain ⟨U, hU, hfinU⟩ := H.2.locallyFinite (0 : Plane)
  have hT : {K : Cell | K ∈ H.1.cells ∧ (0 : Plane) ∈ (K : Set Plane)}.Finite :=
    hfinU.subset fun K hK => ⟨hK.1, 0, hK.2, mem_of_mem_nhds hU⟩
  have hev : ∀ K ∈ {K : Cell | K ∈ H.1.cells ∧ (0 : Plane) ∈ (K : Set Plane)},
      ∀ᶠ m : ℕ in atTop, ¬ IsLargeAtMass ε (m : ℝ≥0∞) (H, q, 0) K := by
    intro K _
    obtain ⟨n, hn⟩ := exists_lt_mul_two_rpow (Metric.diam (K : Set Plane)) hε q.1
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt (cellMass_squareAt_ne_top H q (n : ℤ))
    filter_upwards [eventually_ge_atTop M] with m hm hlarge
    have h1 := hlarge (n : ℤ) (hM.le.trans (Nat.cast_le.2 hm))
    have hd0 : 0 ≤ Metric.diam (K : Set Plane) := Metric.diam_nonneg
    have hL : 0 ≤ (2 : ℝ) ^ (q.1 + ((n : ℤ) : ℝ)) := by positivity
    have hn' : Metric.diam (K : Set Plane) < ε * (2 : ℝ) ^ (q.1 + ((n : ℤ) : ℝ)) := by
      rwa [Int.cast_natCast]
    have hle : ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2) ≤
        ENNReal.ofReal (ε ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 (n : ℤ) 0) := by
      rw [volume_squareAt, ← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_self_le_mul_self hd0 hn'.le])
    exact (not_lt.2 hle) h1
  filter_upwards [(Filter.eventually_all_finite hT).2 hev] with m hm
  unfold largeCellDensity
  refine ENNReal.tsum_eq_zero.2 fun K => Set.indicator_of_notMem (fun hK => ?_) _
  have h0 : (0 : Plane) ∈ ((K : Cell) : Set Plane) := by simpa using hK.1
  exact hm K ⟨K.2, h0⟩ hK.2

/-! ### The ergodic averages along the squares around the origin -/

section Ergodic

variable {μ : Measure GMSSpace}

/-- **Conditional ergodic lemma along the squares around the origin, in `[0, ∞]`**: under the
hypotheses of `ae_ae_tendsto_squareAt_average_condExp`, the uniform averages over `S_j` converge in
`[0, ∞]` to `E[G(H, D, 0) | 𝓘]`. -/
theorem ae_ae_tendsto_squareAt_average_ofReal_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun j : ℤ => ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z))
        atTop
        (𝓝 (ENNReal.ofReal ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal |
          cappedSquareTailSigma] (H, q)))) := by
  filter_upwards [ae_ae_tendsto_cappedSquareAverage_ofReal_condExp hMT hG hinv hfin] with H hH
  filter_upwards [hH, ae_tendsto_cellMass_squareAt_origin_atTop H,
    ae_cappedSquareAverage_cellMass_squareAt_eq H G] with q hq htop havg
  have hreal := tendsto_toReal_atTop_of_tendsto_top htop fun j => cellMass_squareAt_ne_top H q j
  refine (hq.comp hreal).congr fun j => ?_
  simp only [Function.comp_apply, ENNReal.ofReal_toReal (cellMass_squareAt_ne_top H q j), havg j]

end Ergodic

/-- **A large cell inside a square around the origin weighs on the average**: if the cell mass of
`S = S_j` exceeds `m`, every cell `K ⊆ S` with `ε² Area(S) < diam(K)²` is large at mass `m` at each
off-grid point of `K`, so the uniform average of `G_{ε,m}` over `S` is at least
`diam(K)² / Area(S)`. -/
theorem inv_volume_mul_le_average_largeCellDensity {ε : ℝ} {m : ℝ≥0∞} {H : GMSSpace}
    {q : DyadicCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) {j : ℤ}
    (hm : m < cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0))
    (K : H.1.cells) (hKS : complexCells H.1 K ⊆ squareAt q.1 q.2.1 q.2.2 j 0)
    (hK : ENNReal.ofReal (ε ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 j 0) <
      ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2)) :
    (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) ≤
      ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
          largeCellDensity ε m (H, q, z) := by
  have hKm : MeasurableSet (complexCells H.1 K) := (isCompact_complexCells K).isClosed.measurableSet
  have hvol0 : volume (complexCells H.1 K) ≠ 0 := volume_complexCells_ne_zero H.2 K
  have hvoltop : volume (complexCells H.1 K) ≠ ∞ := (isCompact_complexCells K).measure_lt_top.ne
  have hval : ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        (complexCells H.1 K).indicator (fun _ => cellRatio K) z =
      (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) := by
    rw [lintegral_const_mul _ (measurable_const.indicator hKm), lintegral_indicator_const hKm,
      cellRatio, ← volume_complexCells K, ENNReal.div_mul_cancel hvol0 hvoltop]
  rw [← hval]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with z hz
  by_cases hzK : z ∈ complexCells H.1 K
  · have hzS : z ∈ squareAt q.1 q.2.1 q.2.2 j 0 := hKS hzK
    rw [Set.indicator_of_mem hzK, Set.indicator_of_mem hzS, mul_one]
    have hSz : squareAt q.1 q.2.1 q.2.2 j 0 = squareAt q.1 q.2.1 q.2.2 j z :=
      squareAt_eq_of_mem hz hzS
    have hlarge : ((H, q, z), (K : Cell)) ∈ largeCellSet ε m := by
      show planeCoord z ∈ ((K : Cell) : Set Plane) ∧ IsLargeAtMass ε m (H, q, z) (K : Cell)
      refine ⟨hzK, fun j' hj' => ?_⟩
      have hj'j : j' ≤ j := by
        refine not_lt.1 fun hlt => ?_
        have hsub : squareAt q.1 q.2.1 q.2.2 j 0 ⊆ squareAt q.1 q.2.1 q.2.2 j' z := by
          rw [hSz]
          exact squareAt_mono_of_isCompatible h₁ h₂ z hlt.le
        exact (lt_irrefl m)
          (lt_of_lt_of_le hm ((cellMass_mono volume (complexCells H.1) hsub).trans hj'))
      have hsub : squareAt q.1 q.2.1 q.2.2 j' z ⊆ squareAt q.1 q.2.1 q.2.2 j 0 := by
        rw [hSz]
        exact squareAt_mono_of_isCompatible h₁ h₂ z hj'j
      have hvol := measure_mono (μ := volume) hsub
      calc ENNReal.ofReal (ε ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 j' z)
          ≤ ENNReal.ofReal (ε ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 j 0) := by gcongr
        _ < ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) := hK
    gcongr
    calc cellRatio K
        = (largeCellSet ε m).indicator (fun x => cellRatio x.2) ((H, q, z), (K : Cell)) :=
          (Set.indicator_of_mem hlarge
            (fun x : (GMSSpace × DyadicCoord × ℂ) × Cell => cellRatio x.2)).symm
      _ ≤ largeCellDensity ε m (H, q, z) := ENNReal.le_tsum (f := fun K' : H.1.cells =>
          (largeCellSet ε m).indicator (fun x => cellRatio x.2) ((H, q, z), (K' : Cell))) K
  · rw [Set.indicator_of_notMem hzK, mul_zero]
    exact zero_le

/-! ### Cells inside the squares around the origin: (2.8) -/

section Inner

variable {μ : Measure GMSSpace}

/-- The conditional expectation given `𝓘` of the large-cell density at the origin. -/
noncomputable def largeCellCondExp (μ : Measure GMSSpace) (ε : ℝ) (m : ℝ≥0∞) :
    GMSSpace × DyadicCoord → ℝ :=
  (μ.prod dyadicLaw)[fun p => (largeCellDensity ε m (p.1, p.2, 0)).toReal | cappedSquareTailSigma]

/-- **Cells inside the squares around the origin are small** (arXiv 1807.07515, (2.8), with the
conditional ergodic lemma): under the mass-transport principle and `E[Σ_{K ∋ 0} diam(K)²/Area(K)]
< ∞`, for `μ`-almost every configuration and almost every dyadic system, for every `δ > 0` and every
large enough `k`, every cell contained in `S_k` has `diam(K)² ≤ δ² Area(S_k)`. -/
theorem ae_ae_eventually_smallInnerCells_squareAt [IsFiniteMeasure μ] (hMT : MassTransport μ)
    (hΦ : ∫⁻ H, originCellRatioSum H ∂μ ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℤ in atTop,
      SmallInnerCells δ H (squareAt q.1 q.2.1 q.2.2 k 0) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hmeas0 : ∀ (N : ℕ) (m : ℕ), Measurable fun p : GMSSpace × DyadicCoord =>
      largeCellDensity (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞) (p.1, p.2, 0) := fun N m =>
    (measurable_largeCellDensity _ _).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hfin : ∀ (N : ℕ) (m : ℕ), ∫⁻ p, largeCellDensity (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞)
      (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞ := fun N m =>
    lintegral_largeCellDensity_origin_ne_top hΦ _ _
  -- the conditional ergodic lemma for every `ε = 1/(N+1)` and every integer mass `m`
  have hconv : ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ N m : ℕ, Tendsto (fun j : ℤ =>
      ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
          largeCellDensity (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞) (H, q, z)) atTop
      (𝓝 (ENNReal.ofReal (largeCellCondExp μ (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞) (H, q)))) := by
    have h := fun N m : ℕ => ae_ae_tendsto_squareAt_average_ofReal_condExp hMT
      (measurable_largeCellDensity (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞))
      (largeCellDensity_similarity _ _) (hfin N m)
    filter_upwards [ae_all_iff.2 fun N => ae_all_iff.2 (h N)] with H hH
    filter_upwards [ae_all_iff.2 fun N => ae_all_iff.2 (hH N)] with q hq
    exact hq
  -- conditional monotone convergence as the mass tends to `∞`
  have hCE : ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ N : ℕ,
      Tendsto (fun m : ℕ => largeCellCondExp μ (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞) (H, q)) atTop
        (𝓝 0) := by
    have h : ∀ N : ℕ, ∀ᵐ p ∂μ.prod dyadicLaw, Tendsto
        (fun m : ℕ => largeCellCondExp μ (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞) p) atTop (𝓝 0) := by
      intro N
      have hlt : ∀ᵐ p ∂μ.prod dyadicLaw,
          largeCellDensity (1 / ((N : ℝ) + 1)) ((0 : ℕ) : ℝ≥0∞) (p.1, p.2, 0) < ∞ :=
        ae_lt_top (hmeas0 N 0) (hfin N 0)
      unfold largeCellCondExp
      refine JointInvariant.ae_tendsto_condExp_zero_of_antitone cappedSquareTailSigma_le
        (F := fun m p => (largeCellDensity (1 / ((N : ℝ) + 1)) (m : ℝ≥0∞) (p.1, p.2, 0)).toReal)
        (fun m => (hmeas0 N m).ennreal_toReal.aestronglyMeasurable)
        (integrable_toReal_of_lintegral_ne_top (hmeas0 N 0).aemeasurable (hfin N 0))
        (Eventually.of_forall fun p m => ENNReal.toReal_nonneg) ?_ ?_
      · filter_upwards [hlt] with p hp
        intro m m' hmm'
        exact ENNReal.toReal_mono
          ((largeCellDensity_anti _ (Nat.cast_le.2 (Nat.zero_le m)) _).trans_lt hp).ne
          (largeCellDensity_anti _ (Nat.cast_le.2 hmm') _)
      · refine Eventually.of_forall fun p => ?_
        refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
        filter_upwards [largeCellDensity_origin_eventually_eq_zero
          (ε := 1 / ((N : ℝ) + 1)) (by positivity) p.1 p.2]
          with m hm
        rw [hm, ENNReal.toReal_zero]
    filter_upwards [Measure.ae_ae_of_ae_prod (ae_all_iff.2 h)] with H hH
    filter_upwards [hH] with q hq
    exact hq
  filter_upwards [hconv, hCE] with H hHc hHl
  filter_upwards [hHc, hHl, ae_isCompatible_isOffGrid_system 0,
    ae_tendsto_cellMass_squareAt_origin_atTop H] with q hq hql hcomp htop
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  have hε0 : 0 < 1 / ((N : ℝ) + 1) := by positivity
  have hε2 : 0 < (1 / ((N : ℝ) + 1)) ^ 2 := by positivity
  obtain ⟨m, hm⟩ := ((hql N).eventually (gt_mem_nhds hε2)).exists
  have hev1 := (hq N m).eventually (gt_mem_nhds ((ENNReal.ofReal_lt_ofReal_iff hε2).2 hm))
  have hev2 := htop.eventually (lt_mem_nhds (ENNReal.natCast_ne_top m).lt_top)
  filter_upwards [hev1, hev2] with k hk1 hk2
  intro K hKS
  have hS0 : volume (squareAt q.1 q.2.1 q.2.2 k 0) ≠ 0 := by
    rw [volume_squareAt]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (q.1 + (k : ℝ)) := by positivity
    exact mul_ne_zero (ENNReal.ofReal_pos.2 hp).ne' (ENNReal.ofReal_pos.2 hp).ne'
  have hStop : volume (squareAt q.1 q.2.1 q.2.2 k 0) ≠ ∞ :=
    (isCompact_squareAt k 0).measure_lt_top.ne
  calc ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2)
      ≤ ENNReal.ofReal ((1 / ((N : ℝ) + 1)) ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 k 0) := by
        refine not_lt.1 fun hlt => ?_
        have hlow := inv_volume_mul_le_average_largeCellDensity hcomp.1 hcomp.2.1 hk2 K hKS hlt
        have hgt : ENNReal.ofReal ((1 / ((N : ℝ) + 1)) ^ 2) <
            (volume (squareAt q.1 q.2.1 q.2.2 k 0))⁻¹ *
              ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) := by
          rw [← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (Or.inl hS0) (Or.inl hStop)]
          exact hlt
        exact lt_irrefl _ ((hgt.trans_le hlow).trans hk1)
    _ ≤ ENNReal.ofReal (δ ^ 2) * volume (squareAt q.1 q.2.1 q.2.2 k 0) := by
        gcongr

end Inner

/-! ### Cells meeting the boundary -/

/-- **The dyadic ancestor of side `4 |S_k|` of `S_k`** in which `S_k` occupies the second column
and the second row of the subdivision into `16` squares of side `|S_k|` (one of the `16` dyadic
ancestors of `S_k` of side `4 |S_k|`, arXiv 1807.07515, proof of Lemma 2.9). -/
noncomputable def originAncestorSquare (q : DyadicCoord) (k : ℤ) : Set ℂ :=
  cornerSquare (gridFloor q.1 q.2.1 k (0 : ℂ).re - (2 : ℝ) ^ (q.1 + (k : ℝ)))
    (gridFloor q.1 q.2.2 k (0 : ℂ).im - (2 : ℝ) ^ (q.1 + (k : ℝ))) (4 * (2 : ℝ) ^ (q.1 + (k : ℝ)))

/-- A cell meeting `S_k` with diameter less than `|S_k|` lies in `originAncestorSquare q k`. -/
theorem complexCells_subset_originAncestorSquare {H : CellConfig} (K : H.cells) {q : DyadicCoord}
    {k : ℤ} (hmeet : (complexCells H K ∩ squareAt q.1 q.2.1 q.2.2 k 0).Nonempty)
    (hdiam : Metric.diam ((K : Cell) : Set Plane) < (2 : ℝ) ^ (q.1 + (k : ℝ))) :
    complexCells H K ⊆ originAncestorSquare q k := by
  obtain ⟨z₀, hz₀K, hz₀S⟩ := hmeet
  intro z hz
  have hdist : dist z z₀ < (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
    have h := Metric.dist_le_diam_of_mem (x := planeCoord z) (y := planeCoord z₀)
      (K : Cell).isCompact.isBounded hz hz₀K
    rw [LinearIsometryEquiv.dist_map] at h
    exact h.trans_lt hdiam
  have hre : |z.re - z₀.re| < (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
    have h := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_re, ← dist_eq_norm] at h
    exact h.trans_lt hdist
  have him : |z.im - z₀.im| < (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
    have h := Complex.abs_im_le_norm (z - z₀)
    rw [Complex.sub_im, ← dist_eq_norm] at h
    exact h.trans_lt hdist
  obtain ⟨h1, h2, h3, h4⟩ := hz₀S
  obtain ⟨hre1, hre2⟩ := abs_lt.1 hre
  obtain ⟨him1, him2⟩ := abs_lt.1 him
  have hL : 0 < (2 : ℝ) ^ (q.1 + (k : ℝ)) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Cells meeting the squares around the origin are small, given small cells in the ancestors**:
for compatible offsets, if every cell contained in `originAncestorSquare q k` has
`diam(K)² ≤ δ² Area` for all `k ≥ k₀`, with `8 δ < ε < 1`, then for `k ≥ k₀` every cell meeting
`S_k` has `diam(K) ≤ ε |S_k|`. -/
theorem diam_le_of_smallInnerCells_originAncestorSquare {H : GMSSpace} {q : DyadicCoord}
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 ≤ δ) (hδε : 8 * δ < ε) {k₀ : ℤ}
    (hanc : ∀ k ≥ k₀, SmallInnerCells δ H (originAncestorSquare q k)) {k : ℤ} (hk : k₀ ≤ k)
    (K : H.1.cells) (hmeet : (complexCells H.1 K ∩ squareAt q.1 q.2.1 q.2.2 k 0).Nonempty) :
    Metric.diam ((K : Cell) : Set Plane) ≤ ε * (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
  have hd0 : 0 ≤ Metric.diam ((K : Cell) : Set Plane) := Metric.diam_nonneg
  refine not_lt.1 fun hgt => ?_
  have hex : ∃ i : ℕ, Metric.diam ((K : Cell) : Set Plane) <
      ε * (2 : ℝ) ^ (q.1 + ((k + (i : ℤ) : ℤ) : ℝ)) := by
    obtain ⟨n, hn⟩ := exists_lt_mul_two_rpow (Metric.diam ((K : Cell) : Set Plane)) hε0
      (q.1 + (k : ℝ))
    refine ⟨n, ?_⟩
    have e : q.1 + ((k + (n : ℤ) : ℤ) : ℝ) = q.1 + (k : ℝ) + (n : ℝ) := by push_cast; ring
    rw [e]
    exact hn
  classical
  obtain ⟨i₀, hi₀, hmin⟩ : ∃ i : ℕ, Metric.diam ((K : Cell) : Set Plane) <
      ε * (2 : ℝ) ^ (q.1 + ((k + (i : ℤ) : ℤ) : ℝ)) ∧
      ∀ i' < i, ¬ Metric.diam ((K : Cell) : Set Plane) <
        ε * (2 : ℝ) ^ (q.1 + ((k + (i' : ℤ) : ℤ) : ℝ)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i' hi' => Nat.find_min hex hi'⟩
  rcases i₀ with _ | i₁
  · have e : q.1 + ((k + ((0 : ℕ) : ℤ) : ℤ) : ℝ) = q.1 + (k : ℝ) := by push_cast; ring
    rw [e] at hi₀
    linarith
  · have hprev := not_lt.1 (hmin i₁ (Nat.lt_succ_self i₁))
    have hhalf : (2 : ℝ) ^ (q.1 + ((k + (i₁ : ℤ) : ℤ) : ℝ)) * 2 =
        (2 : ℝ) ^ (q.1 + ((k + ((i₁ + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by
      rw [← Real.rpow_add_one two_ne_zero]
      congr 1
      push_cast
      ring
    have hLpos : 0 < (2 : ℝ) ^ (q.1 + ((k + ((i₁ + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by positivity
    have hmeet' : (complexCells H.1 K ∩
        squareAt q.1 q.2.1 q.2.2 (k + ((i₁ + 1 : ℕ) : ℤ)) 0).Nonempty := by
      obtain ⟨z, hzK, hzS⟩ := hmeet
      exact ⟨z, hzK, squareAt_mono_of_isCompatible h₁ h₂ 0 (by omega) hzS⟩
    have hsub := complexCells_subset_originAncestorSquare K hmeet' (by nlinarith)
    have hsmall := hanc _ (by omega) K hsub
    rw [originAncestorSquare, volume_cornerSquare, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)]
      at hsmall
    have h4 : 4 * δ * (2 : ℝ) ^ (q.1 + ((k + ((i₁ + 1 : ℕ) : ℤ) : ℤ) : ℝ)) <
        Metric.diam ((K : Cell) : Set Plane) := by
      nlinarith
    nlinarith [mul_self_lt_mul_self (by positivity :
      0 ≤ 4 * δ * (2 : ℝ) ^ (q.1 + ((k + ((i₁ + 1 : ℕ) : ℤ) : ℤ) : ℝ))) h4]

/-! ### The root ratio has finite expectation under the hypotheses of Theorem 1.16 -/

section RootRatio

/-- A walk between distinct vertices starts with an edge. -/
theorem exists_adj_of_reachable_of_ne {V : Type*} {G : SimpleGraph V} {u w : V}
    (h : G.Reachable u w) (hne : u ≠ w) : ∃ v, G.Adj u v := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h _ => exact ⟨_, h⟩

theorem one_le_ofReal_add_ofReal_inv {c : ℝ} (hc : 0 < c) :
    1 ≤ ENNReal.ofReal c + ENNReal.ofReal c⁻¹ := by
  rcases le_total 1 c with h | h
  · exact (ENNReal.one_le_ofReal.2 h).trans le_self_add
  · exact (ENNReal.one_le_ofReal.2 ((one_le_inv₀ hc).2 h)).trans le_add_self

/-- **Under connectedness along lines every cell has a neighbour**: the horizontal segment of
length `diam(K) + 1` starting at a point of `K` ends in another cell, and the graph of the cells
meeting the segment is connected. -/
theorem exists_conductance_pos_of_lineConnected {H : GMSSpace} (hL : H.1.LineConnected)
    (K : H.1.cells) : ∃ K' : H.1.cells, 0 < H.1.c K K' := by
  obtain ⟨p, hp⟩ := (K : Cell).nonempty
  obtain ⟨d, hd_eq⟩ : ∃ d : ℝ, d = Metric.diam ((K : Cell) : Set Plane) := ⟨_, rfl⟩
  have hd : 0 ≤ d := hd_eq ▸ Metric.diam_nonneg
  obtain ⟨q, hq_def⟩ : ∃ q : Plane, q = p + (d + 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hq0 : q 0 = p 0 + (d + 1) := by simp [hq_def]
  have hq1 : q 1 = p 1 := by simp [hq_def]
  have hpq : dist p q = d + 1 := by
    rw [dist_comm, dist_eq_norm, hq_def, add_sub_cancel_left, norm_smul,
      PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg (by linarith)]
  have hqK : q ∉ ((K : Cell) : Set Plane) := fun hq => by
    have h := Metric.dist_le_diam_of_mem (K : Cell).isCompact.isBounded hp hq
    rw [← hd_eq, hpq] at h
    linarith
  have hqU : q ∈ ⋃ K ∈ H.1.cells, (K : Set Plane) := by
    rw [H.2.iUnion_eq_univ]
    exact mem_univ q
  obtain ⟨K'', hK''c, hqK''⟩ := mem_iUnion₂.1 hqU
  have hlt : p 0 < p 0 + (d + 1) := by linarith
  have hpL : p ∈ horizontal (p 0) (p 0 + (d + 1)) (p 1) := ⟨le_rfl, hlt.le, rfl⟩
  have hqL : q ∈ horizontal (p 0) (p 0 + (d + 1)) (p 1) :=
    ⟨by rw [hq0]; linarith, by rw [hq0], hq1⟩
  let u : {K : H.1.cells | ((K : Set Plane) ∩ horizontal (p 0) (p 0 + (d + 1)) (p 1)).Nonempty} :=
    ⟨K, p, hp, hpL⟩
  let w : {K : H.1.cells | ((K : Set Plane) ∩ horizontal (p 0) (p 0 + (d + 1)) (p 1)).Nonempty} :=
    ⟨⟨K'', hK''c⟩, q, hqK'', hqL⟩
  have huw : u ≠ w := by
    intro h
    have hKK : (K : Cell) = K'' := congrArg (fun x => ((x.1 : H.1.cells) : Cell)) h
    exact hqK (hKK ▸ hqK'')
  obtain ⟨v, hv⟩ := exists_adj_of_reachable_of_ne
    ((hL.1 (p 0) (p 0 + (d + 1)) (p 1) hlt).preconnected u w) huw
  exact ⟨v.1, (show H.1.graph.Adj u.1 v.1 from hv).2.1⟩

/-- A frontier point of a cell lies in another cell (local finiteness and covering). -/
theorem frontier_subset_biUnion_inter (H : GMSSpace) {K : Cell} (_hK : K ∈ H.1.cells) :
    frontier (K : Set Plane) ⊆ ⋃ K' ∈ {K' | K' ∈ H.1.cells ∧ K' ≠ K}, (K : Set Plane) ∩ K' := by
  intro y hy
  have hy' : y ∈ closure (K : Set Plane) \ interior (K : Set Plane) := hy
  by_contra hno
  have hyK : y ∈ (K : Set Plane) := K.isCompact.isClosed.frontier_subset hy
  obtain ⟨U, hU, hfin⟩ := H.2.locallyFinite y
  have hV : U ∩ ⋂ K' ∈ H.1.restrict U \ {K}, ((K' : Set Plane))ᶜ ∈ 𝓝 y := by
    refine Filter.inter_mem hU ((Filter.biInter_mem (hfin.subset sdiff_subset)).2 fun K' hK' => ?_)
    refine K'.isCompact.isClosed.isOpen_compl.mem_nhds fun hyK' => hno ?_
    exact mem_biUnion (x := K') ⟨hK'.1.1, hK'.2⟩ ⟨hyK, hyK'⟩
  refine hy'.2 (mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hV fun x hx => ?_))
  have hxU : x ∈ ⋃ K ∈ H.1.cells, (K : Set Plane) := by
    rw [H.2.iUnion_eq_univ]
    exact mem_univ x
  obtain ⟨K', hK'c, hxK'⟩ := mem_iUnion₂.1 hxU
  by_contra hxK
  have hKK' : K' ≠ K := fun h => hxK (h ▸ hxK')
  exact mem_iInter₂.1 hx.2 K' ⟨⟨hK'c, x, hxK', hx.1⟩, hKK'⟩ hxK'

/-- **Cell frontiers are Lebesgue-null.** -/
theorem volume_frontier_cell (H : GMSSpace) {K : Cell} (hK : K ∈ H.1.cells) :
    volume (frontier (K : Set Plane)) = 0 :=
  measure_mono_null (frontier_subset_biUnion_inter H hK)
    ((measure_biUnion_null_iff ((Set.countable_coe_iff.1 (countable_cells H.2)).mono fun _ h => h.1)).2
      fun K' hK' => H.2.volume_inter K hK K' hK'.1 (Ne.symm hK'.2))

/-- The rooted configurations `(H, z)` with `z` on the frontier of a cell of `H`. -/
def cellFrontierSet : Set (GMSSpace × ℂ) :=
  {p | ∃ K : Cell, K ∈ p.1.1.cells ∧ planeCoord p.2 ∈ frontier (K : Set Plane)}

/-- The indicator of `cellFrontierSet`. -/
noncomputable def cellFrontierIndicator : GMSSpace × ℂ → ℝ≥0∞ := cellFrontierSet.indicator 1

theorem measurableSet_cellFrontierSet : MeasurableSet cellFrontierSet := by
  have h : cellFrontierSet = ⋃ n : ℕ, (Prod.fst ⁻¹' labelSet n) ∩
      (fun p : GMSSpace × ℂ => (interiorCell (Code.rationalPoint n) p.1, planeCoord p.2)) ⁻¹'
        {x : Cell × Plane | x.2 ∈ frontier (x.1 : Set Plane)} := by
    ext p
    constructor
    · rintro ⟨K, hK, hfr⟩
      have hs := CellConfig.slot_label p.1.2 ⟨K, hK⟩
      rw [slot_eq] at hs
      by_cases hn : p.1 ∈ labelSet (CellConfig.label p.1.2 ⟨K, hK⟩)
      · rw [ite_eq_left hn] at hs
        refine mem_iUnion.2 ⟨_, hn, ?_⟩
        show planeCoord p.2 ∈ frontier ((interiorCell _ p.1 : Cell) : Set Plane)
        rw [Option.some_inj.1 hs]
        exact hfr
      · rw [ite_eq_right hn] at hs
        exact absurd hs (Option.some_ne_none K).symm
    · intro hp
      obtain ⟨n, hn, hfr⟩ := mem_iUnion.1 hp
      have hs : p.1.1.slot n = some (interiorCell (Code.rationalPoint n) p.1) := by
        rw [slot_eq, ite_eq_left (show p.1 ∈ labelSet n from hn)]
      exact ⟨_, ((CellConfig.slot_eq_some_iff p.1.2).1 hs).1, hfr⟩
  rw [h]
  exact MeasurableSet.iUnion fun n => (measurable_fst (measurableSet_labelSet n)).inter
    (Spatial.measurableSet_cellFrontier.preimage
      (((measurable_interiorCell _).comp measurable_fst).prodMk
        (planeCoord.continuous.measurable.comp measurable_snd)))

/-- **The cell frontiers are similarity covariant.** -/
theorem mem_cellFrontierSet_similarity_iff {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (hHH' : IsSimilar s u hs H H') (w : ℂ) :
    (H', s • w + similarityOffset s u) ∈ cellFrontierSet ↔ (H, w) ∈ cellFrontierSet := by
  obtain ⟨H'c, hH'c⟩ := H'
  have e : H'c = H.1.similarity s u hs := hHH'
  subst e
  have key : ∀ K : Cell, positiveSimilarity s u (planeCoord w) ∈
      frontier ((transformCell s u hs K : Cell) : Set Plane) ↔
        planeCoord w ∈ frontier (K : Set Plane) := by
    intro K
    have himg : ((transformCell s u hs K : Cell) : Set Plane) =
        positiveSimilarityHomeomorph s u hs '' (K : Set Plane) := rfl
    rw [himg, ← Homeomorph.image_frontier]
    exact Function.Injective.mem_set_image (positiveSimilarityHomeomorph s u hs).injective
  show (∃ K ∈ transformCell s u hs '' H.1.cells, planeCoord (s • w + similarityOffset s u) ∈
      frontier (K : Set Plane)) ↔ ∃ K ∈ H.1.cells, planeCoord w ∈ frontier (K : Set Plane)
  rw [planeCoord_smul_add_similarityOffset]
  constructor
  · rintro ⟨_, ⟨K, hK, rfl⟩, h⟩
    exact ⟨K, hK, (key K).1 h⟩
  · rintro ⟨K, hK, h⟩
    exact ⟨_, ⟨K, hK, rfl⟩, (key K).2 h⟩

theorem volume_cellFrontierSet_slice (H : GMSSpace) :
    volume {z : ℂ | (H, z) ∈ cellFrontierSet} = 0 := by
  have h : {z : ℂ | (H, z) ∈ cellFrontierSet} =
      planeCoord ⁻¹' ⋃ K ∈ H.1.cells, frontier (K : Set Plane) := by
    ext z
    rw [mem_preimage, mem_iUnion₂]
    constructor
    · rintro ⟨K, hK, hz⟩
      exact ⟨K, hK, hz⟩
    · rintro ⟨K, hK, hz⟩
      exact ⟨K, hK, hz⟩
  rw [h]
  refine (measurePreserving_planeCoordMeas.measure_preimage_equiv _).trans ?_
  rw [measure_biUnion_null_iff (Set.countable_coe_iff.1 (countable_cells H.2))]
  exact fun K hK => volume_frontier_cell H hK

/-- **Almost surely the origin lies on no cell frontier** (mass transport, the frontiers being
Lebesgue-null). -/
theorem ae_zero_notMem_frontier {μ : Measure GMSSpace} (hMT : MassTransport μ) :
    ∀ᵐ H ∂μ, ∀ (K : Cell), K ∈ H.1.cells → (0 : Plane) ∉ frontier (K : Set Plane) := by
  have hG : Measurable cellFrontierIndicator :=
    measurable_one.indicator measurableSet_cellFrontierSet
  have hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ w : ℂ, cellFrontierIndicator (H', s • w + similarityOffset s u) =
        cellFrontierIndicator (H, w) := by
    intro s u hs H H' hHH' w
    unfold cellFrontierIndicator
    by_cases h : (H, w) ∈ cellFrontierSet
    · rw [indicator_of_mem h, indicator_of_mem ((mem_cellFrontierSet_similarity_iff hHH' w).2 h)]
      rfl
    · rw [indicator_of_notMem h,
        indicator_of_notMem fun h' => h ((mem_cellFrontierSet_similarity_iff hHH' w).1 h')]
  have hzero : ∀ (H : GMSSpace) (f : ℂ → ℝ≥0∞),
      ∫⁻ z, f z * cellFrontierIndicator (H, z) = 0 := by
    intro H f
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_cellFrontierSet_slice H)] with z hz
    simp only [cellFrontierIndicator, indicator_of_notMem (show (H, z) ∉ cellFrontierSet from hz),
      mul_zero]
  have h := lintegral_cappedSquare_average_eq hMT one_ne_zero ENNReal.one_ne_top hG hinv
  simp only [hzero, lintegral_zero] at h
  have hmeas0 : Measurable fun H : GMSSpace => cellFrontierIndicator (H, 0) :=
    hG.comp (measurable_id.prodMk measurable_const)
  have h0 := (lintegral_eq_zero_iff hmeas0).1 h.symm
  filter_upwards [h0] with H hH K hK hfr
  have hmem : (H, (0 : ℂ)) ∈ cellFrontierSet := by
    refine ⟨K, hK, ?_⟩
    show planeCoord (0 : ℂ) ∈ frontier (K : Set Plane)
    rw [map_zero]
    exact hfr
  have h1 : cellFrontierIndicator (H, 0) = 1 := indicator_of_mem hmem 1
  have h2 : cellFrontierIndicator (H, 0) = 0 := hH
  rw [h1] at h2
  exact one_ne_zero h2

/-- The extended row sum `Σ_m φ(c(H_n, H_m))` of the conductance array of the coding at the slot
`n`. -/
noncomputable def slotRowMass (φ : ℝ → ℝ) (H : GMSSpace) (n : ℕ) : ℝ≥0∞ :=
  ∑' m, ENNReal.ofReal (φ (H.1.codeCond n m))

theorem measurable_slotRowMass {φ : ℝ → ℝ} (hφ : Measurable φ) (n : ℕ) :
    Measurable fun H : GMSSpace => slotRowMass φ H n :=
  Measurable.tsum fun m => (hφ.comp (measurable_codeCond n m)).ennreal_ofReal

theorem slotRowMass_eq_tsum_vertex {φ : ℝ → ℝ} (hφ0 : φ 0 = 0) (H : GMSSpace) (K : H.1.cells) :
    slotRowMass φ H (CellConfig.label H.2 K) =
      ∑' w : Code.Vertex H.1.code,
        ENNReal.ofReal (φ (H.1.code.2 ((CellConfig.cellEquiv H.2).symm K).val w.val)) := by
  have hsupp : Function.support (fun m =>
      ENNReal.ofReal (φ (H.1.codeCond (CellConfig.label H.2 K) m))) ⊆
        {m | (H.1.code.1 m).isSome} := by
    intro m hm
    by_contra hnone
    apply hm
    have hm' : H.1.slot m = none := Option.not_isSome_iff_eq_none.mp hnone
    show ENNReal.ofReal (φ (H.1.codeCond _ m)) = 0
    rw [CellConfig.codeCond_of_none_right hm', hφ0, ENNReal.ofReal_zero]
  unfold slotRowMass
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

/-- `π(K)` is the slot row sum of the conductances at the label of `K`. -/
theorem ofReal_pi_eq_slotRowMass (H : GMSSpace) (K : H.1.cells) :
    ENNReal.ofReal (H.1.pi K) = slotRowMass id H (CellConfig.label H.2 K) := by
  have h := CellConfig.ofReal_pi_cellEquiv H.2 ((CellConfig.cellEquiv H.2).symm K)
  rw [Equiv.apply_symm_apply] at h
  exact h.trans (slotRowMass_eq_tsum_vertex (φ := id) rfl H K).symm

/-- `π*(K)` is the slot row sum of the inverse conductances at the label of `K`. -/
theorem ofReal_piStar_eq_slotRowMass (H : GMSSpace) (K : H.1.cells) :
    ENNReal.ofReal (H.1.piStar K) = slotRowMass (fun x => x⁻¹) H (CellConfig.label H.2 K) := by
  have h := CellConfig.ofReal_piStar_cellEquiv H.2 ((CellConfig.cellEquiv H.2).symm K)
  rw [Equiv.apply_symm_apply] at h
  exact h.trans (slotRowMass_eq_tsum_vertex (φ := fun x => x⁻¹) inv_zero H K).symm

/-- `diam(K)² / Area(K)` for the cells containing the origin, `0` for the others. -/
noncomputable def originAreaRatio (K : Cell) : ℝ≥0∞ :=
  {K : Cell | (0 : Plane) ∈ (K : Set Plane)}.indicator
    (fun K => ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K)) K

theorem measurable_originAreaRatio : Measurable originAreaRatio :=
  (((Spatial.measurable_cellDiam.pow_const 2).div
    Spatial.measurable_cellVolume.ennreal_toReal).ennreal_ofReal).indicator
    (Spatial.measurableSet_cellMem.preimage (measurable_id.prodMk measurable_const))

/-- **A half of the rooted finite-energy density in the slot form**:
`Σ_n 1(0 ∈ H_n) diam(H_n)² / Area(H_n) · Σ_m φ(c(H_n, H_m))`. -/
noncomputable def originRowSum (φ : ℝ → ℝ) (H : GMSSpace) : ℝ≥0∞ :=
  ∑' n, (H.1.slot n).elim 0 (fun K => originAreaRatio K * slotRowMass φ H n)

theorem measurable_originRowSum {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (originRowSum φ) := by
  unfold originRowSum
  refine Measurable.tsum fun n => ?_
  have h : (fun H : GMSSpace =>
      (H.1.slot n).elim 0 (fun K => originAreaRatio K * slotRowMass φ H n)) =
      (labelSet n).indicator (fun H =>
        originAreaRatio (interiorCell (Code.rationalPoint n) H) * slotRowMass φ H n) := by
    funext H
    by_cases h : H ∈ labelSet n
    · rw [slot_eq, Set.indicator_of_mem h]
      simp only [h, ↓reduceIte, Option.elim]
    · rw [slot_eq, Set.indicator_of_notMem h]
      simp only [h, ↓reduceIte, Option.elim]
  rw [h]
  exact ((measurable_originAreaRatio.comp (measurable_interiorCell _)).mul
    (measurable_slotRowMass hφ n)).indicator (measurableSet_labelSet n)

/-- Off the cell frontiers, the cell containing the origin is unique. -/
theorem eq_of_zero_mem {H : GMSSpace}
    (hH : ∀ (K : Cell), K ∈ H.1.cells → (0 : Plane) ∉ frontier (K : Set Plane)) {K K' : Cell}
    (hK : K ∈ H.1.cells) (hK' : K' ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K : Set Plane))
    (h0' : (0 : Plane) ∈ (K' : Set Plane)) : K = K' := by
  have hint : ∀ {L : Cell}, L ∈ H.1.cells → (0 : Plane) ∈ (L : Set Plane) →
      (0 : Plane) ∈ interior (L : Set Plane) := fun {L} hL h0L =>
    Classical.byContradiction fun hn => hH L hL
      (show (0 : Plane) ∈ closure (L : Set Plane) \ interior (L : Set Plane) from
        ⟨subset_closure h0L, hn⟩)
  exact CellConfig.eq_of_mem_interior H.2 hK hK' (hint hK h0) (hint hK' h0')

theorem originCellRatioSum_eq {H : GMSSpace}
    (hH : ∀ (K : Cell), K ∈ H.1.cells → (0 : Plane) ∉ frontier (K : Set Plane)) {K₀ : Cell}
    (hK₀ : K₀ ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K₀ : Set Plane)) :
    originCellRatioSum H = cellRatio K₀ := by
  unfold originCellRatioSum
  rw [tsum_eq_single (f := fun K : H.1.cells => {K : Cell | (0 : Plane) ∈ (K : Set Plane)}.indicator cellRatio K) ⟨K₀, hK₀⟩ fun K hK => Set.indicator_of_notMem (show (K : Cell) ∉ {L : Cell | (0 : Plane) ∈ (L : Set Plane)} from
    fun h0K => hK (Subtype.ext (eq_of_zero_mem hH K.2 hK₀ h0K h0))) _]
  exact Set.indicator_of_mem (show K₀ ∈ {K : Cell | (0 : Plane) ∈ (K : Set Plane)} from h0) _

theorem originRowSum_eq {φ : ℝ → ℝ} {H : GMSSpace}
    (hH : ∀ (K : Cell), K ∈ H.1.cells → (0 : Plane) ∉ frontier (K : Set Plane)) {K₀ : Cell}
    (hK₀ : K₀ ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K₀ : Set Plane)) :
    originRowSum φ H = ENNReal.ofReal (Metric.diam (K₀ : Set Plane) ^ 2 / CellConfig.area K₀) *
      slotRowMass φ H (CellConfig.label H.2 ⟨K₀, hK₀⟩) := by
  unfold originRowSum
  rw [tsum_eq_single (CellConfig.label H.2 ⟨K₀, hK₀⟩) fun n hn => ?_,
    CellConfig.slot_label H.2 ⟨K₀, hK₀⟩]
  · simp only [Option.elim]
    rw [originAreaRatio,
      Set.indicator_of_mem (show K₀ ∈ {K : Cell | (0 : Plane) ∈ (K : Set Plane)} from h0)]
  · cases hs : H.1.slot n with
    | none => rfl
    | some K =>
      simp only [Option.elim]
      obtain ⟨hK, hl⟩ := (CellConfig.slot_eq_some_iff H.2).1 hs
      have hK0 : (0 : Plane) ∉ (K : Set Plane) := fun h0K => hn (by
        have hKK : K = K₀ := eq_of_zero_mem hH hK hK₀ h0K h0
        subst hKK
        exact (leastInteriorLabel_unique (CellConfig.leastInteriorLabel_label H.2 ⟨K, hK₀⟩)
          hl).symm)
      rw [originAreaRatio,
        Set.indicator_of_notMem (show K ∉ {K : Cell | (0 : Plane) ∈ (K : Set Plane)} from hK0),
        zero_mul]

/-- The two halves of the rooted finite-energy density at the cell `H₀ H` containing the origin. -/
theorem originRowSum_eq_root {φ : ℝ → ℝ} {q : GMSSpace → Cell → ℝ}
    (hq : ∀ (H : GMSSpace) (K : H.1.cells),
      ENNReal.ofReal (q H K) = slotRowMass φ H (CellConfig.label H.2 K))
    {H₀ : GMSSpace → Cell} (hH₀ : ∀ H, H₀ H ∈ H.1.cells ∧ (0 : Plane) ∈ (H₀ H : Set Plane))
    {H : GMSSpace} (hH : ∀ (K : Cell), K ∈ H.1.cells → (0 : Plane) ∉ frontier (K : Set Plane)) :
    originRowSum φ H = ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 /
      CellConfig.area (H₀ H) * q H (H₀ H)) := by
  rw [originRowSum_eq hH (hH₀ H).1 (hH₀ H).2, ← hq H ⟨H₀ H, (hH₀ H).1⟩]
  exact (ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)).symm

theorem cellRatio_eq_ofReal_div_area {H : GMSSpace} {K : Cell} (hK : K ∈ H.1.cells) :
    cellRatio K = ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K) := by
  have hfin : volume (K : Set Plane) ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hpos : 0 < volume (K : Set Plane) :=
    (isOpen_interior.measure_pos volume (H.2.interior_nonempty K hK)).trans_le
      (measure_mono interior_subset)
  rw [cellRatio, CellConfig.area, ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hpos.ne' hfin),
    ENNReal.ofReal_toReal hfin]

/-- Under connectedness along lines, `π(K) + π*(K) ≥ 1` in the slot form. -/
theorem one_le_slotRowMass_add {H : GMSSpace} (hL : H.1.LineConnected) (K : H.1.cells) :
    1 ≤ slotRowMass id H (CellConfig.label H.2 K) +
      slotRowMass (fun x => x⁻¹) H (CellConfig.label H.2 K) := by
  obtain ⟨K', hK'⟩ := exists_conductance_pos_of_lineConnected hL K
  have hc : H.1.codeCond (CellConfig.label H.2 K) (CellConfig.label H.2 K') = H.1.c K K' :=
    CellConfig.codeCond_of_some (CellConfig.slot_label H.2 K) (CellConfig.slot_label H.2 K')
  refine (one_le_ofReal_add_ofReal_inv hK').trans (add_le_add ?_ ?_)
  · rw [← hc]
    exact ENNReal.le_tsum (f := fun m =>
      ENNReal.ofReal (id (H.1.codeCond (CellConfig.label H.2 K) m))) _
  · rw [← hc]
    exact ENNReal.le_tsum (f := fun m =>
      ENNReal.ofReal ((H.1.codeCond (CellConfig.label H.2 K) m)⁻¹)) _

/-- **The root ratio has finite expectation** under the hypotheses of Theorem 1.16 of arXiv
1807.07515: mass transport, connectedness along lines and the finite-expectation hypothesis (1.5).
Almost surely the origin lies on no cell frontier, so the cell `H₀` containing it is unique and the
two halves of (1.5) are the measurable slot sums `originRowSum`; every cell has a neighbour,
whence `π(H₀) + π*(H₀) ≥ 1` and `diam(H₀)² / Area(H₀)` is at most the sum of the two halves. -/
theorem lintegral_originCellRatioSum_ne_top {μ : Measure GMSSpace} (hMT : MassTransport μ)
    (hL : ConnectedAlongLines μ) (hFE : FiniteExpectation μ) :
    ∫⁻ H, originCellRatioSum H ∂μ ≠ ∞ := by
  obtain ⟨H₀, hH₀, hπ, hπs⟩ := hFE
  have hfr := ae_zero_notMem_frontier hMT
  have h1 : ∫⁻ H, originRowSum id H ∂μ = ∫⁻ H, ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 /
      CellConfig.area (H₀ H) * H.1.pi (H₀ H)) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hfr] with H hH
    exact originRowSum_eq_root (q := fun H K => H.1.pi K) ofReal_pi_eq_slotRowMass hH₀ hH
  have h2 : ∫⁻ H, originRowSum (fun x => x⁻¹) H ∂μ = ∫⁻ H, ENNReal.ofReal
      (Metric.diam (H₀ H : Set Plane) ^ 2 / CellConfig.area (H₀ H) * H.1.piStar (H₀ H)) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hfr] with H hH
    exact originRowSum_eq_root (q := fun H K => H.1.piStar K) ofReal_piStar_eq_slotRowMass hH₀ hH
  have hle : ∫⁻ H, originCellRatioSum H ∂μ ≤
      ∫⁻ H, originRowSum id H + originRowSum (fun x => x⁻¹) H ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hfr, (connectedAlongLines_iff μ).1 hL] with H hH hHL
    rw [originCellRatioSum_eq hH (hH₀ H).1 (hH₀ H).2, cellRatio_eq_ofReal_div_area (hH₀ H).1,
      originRowSum_eq hH (hH₀ H).1 (hH₀ H).2, originRowSum_eq hH (hH₀ H).1 (hH₀ H).2, ← mul_add]
    exact le_mul_of_one_le_right zero_le (one_le_slotRowMass_add hHL ⟨H₀ H, (hH₀ H).1⟩)
  rw [lintegral_add_left (measurable_originRowSum measurable_id), h1, h2] at hle
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hπ.ne, hπs.ne⟩) hle

end RootRatio

/-! ### Measurability of the interior-cell event -/

private theorem isClosed_subset_cornerSquare_params (A : Set ℂ) :
    IsClosed {p : ℝ × ℝ × ℝ | A ⊆ cornerSquare p.1 p.2.1 p.2.2} := by
  have heq : {p : ℝ × ℝ × ℝ | A ⊆ cornerSquare p.1 p.2.1 p.2.2} =
      ⋂ z ∈ A, {p : ℝ × ℝ × ℝ | z ∈ cornerSquare p.1 p.2.1 p.2.2} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, Set.subset_def]
  rw [heq]
  refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
  simp only [mem_cornerSquare, Set.ofPred_and]
  exact (isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_const (continuous_fst.add continuous_snd.snd)).inter
      ((isClosed_le continuous_snd.fst continuous_const).inter
        (isClosed_le continuous_const (continuous_snd.fst.add continuous_snd.snd))))

/-- The small-interior-cell event is measurable in the parameters of a closed square. -/
theorem measurableSet_smallInnerCells_cornerSquare (δ : ℝ) (H : GMSSpace) :
    MeasurableSet {p : ℝ × ℝ × ℝ |
      SmallInnerCells δ H (cornerSquare p.1 p.2.1 p.2.2)} := by
  have := countable_cells H.2
  have hm : Measurable fun p : ℝ × ℝ × ℝ => volume (cornerSquare p.1 p.2.1 p.2.2) := by
    simp_rw [volume_cornerSquare]
    exact (ENNReal.measurable_ofReal.comp measurable_snd.snd).mul
      (ENNReal.measurable_ofReal.comp measurable_snd.snd)
  have heq : {p : ℝ × ℝ × ℝ | SmallInnerCells δ H (cornerSquare p.1 p.2.1 p.2.2)} =
      ⋂ K : H.1.cells, {p : ℝ × ℝ × ℝ |
        complexCells H.1 K ⊆ cornerSquare p.1 p.2.1 p.2.2 →
          ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) ≤
            ENNReal.ofReal (δ ^ 2) * volume (cornerSquare p.1 p.2.1 p.2.2)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, SmallInnerCells]
  rw [heq]
  refine MeasurableSet.iInter fun K => ?_
  have hset : {p : ℝ × ℝ × ℝ |
      complexCells H.1 K ⊆ cornerSquare p.1 p.2.1 p.2.2 →
        ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) ≤
          ENNReal.ofReal (δ ^ 2) * volume (cornerSquare p.1 p.2.1 p.2.2)} =
      {p : ℝ × ℝ × ℝ | complexCells H.1 K ⊆ cornerSquare p.1 p.2.1 p.2.2}ᶜ ∪
      {p : ℝ × ℝ × ℝ | ENNReal.ofReal (Metric.diam ((K : Cell) : Set Plane) ^ 2) ≤
        ENNReal.ofReal (δ ^ 2) * volume (cornerSquare p.1 p.2.1 p.2.2)} := by
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [hset]
  exact (isClosed_subset_cornerSquare_params (complexCells H.1 K)).measurableSet.compl.union
    (measurableSet_le measurable_const (measurable_const.mul hm))

/-! ### Lemma 2.9 -/

section Main

variable {μ : Measure GMSSpace}

/-- **The cells meeting the squares around the origin are small** (Gwynne, Miller and Sheffield,
arXiv 1807.07515, Lemma 2.9, (2.5)): under the mass-transport principle and
`E[Σ_{K ∋ 0} diam(K)² / Area(K)] < ∞`, and given Lemma 2.8 for the similarity-covariant events
`SmallInnerCells δ` (`smallInnerCells_similarity`) and the dyadic ancestors `originAncestorSquare`
of side `4 |S_k|` (hypothesis `hL28`), for `μ`-almost every configuration `H` and almost every
dyadic system `D`, for each `ε ∈ (0, 1)` and every large enough `k ∈ ℕ`, every cell `K ∈ H(S_k)`
has `diam(K) ≤ ε |S_k|`, where `|S_k| = 2^{t + k}` is the side length of `S_k`. -/
theorem ae_ae_eventually_diam_le_of_interior [IsFiniteMeasure μ] (hMT : MassTransport μ)
    (hΦ : ∫⁻ H, originCellRatioSum H ∂μ ≠ ∞)
    (hL28 : ∀ δ : ℝ, 0 < δ →
      (∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ k : ℤ in atTop,
        SmallInnerCells δ H (squareAt q.1 q.2.1 q.2.2 k 0)) →
      ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ k : ℤ in atTop,
        SmallInnerCells δ H (originAncestorSquare q k)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᶠ k : ℕ in atTop,
      ∀ K : Cell, K ∈ H.1.restrict (planeCoord '' squareAt q.1 q.2.1 q.2.2 k 0) →
        Metric.diam (K : Set Plane) ≤ ε * (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
  have hint := ae_ae_eventually_smallInnerCells_squareAt hMT hΦ
  have hanc : ∀ N : ℕ, ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ k : ℤ in atTop,
      SmallInnerCells (1 / ((N : ℝ) + 1)) H (originAncestorSquare q k) := fun N =>
    hL28 _ (by positivity) (by
      filter_upwards [hint] with H hH
      filter_upwards [hH] with q hq
      exact hq _ (by positivity))
  filter_upwards [ae_all_iff.2 hanc] with H hH
  filter_upwards [ae_all_iff.2 hH, ae_isCompatible_isOffGrid_system 0] with q hq hcomp
  rintro ε ⟨hε0, hε1⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 8 by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hq N)
  filter_upwards [eventually_ge_atTop k₀.toNat] with k hk K hK
  obtain ⟨hKc, p, hpK, z, hz, hzp⟩ := hK
  have hmeet : (complexCells H.1 ⟨K, hKc⟩ ∩ squareAt q.1 q.2.1 q.2.2 (k : ℤ) 0).Nonempty := by
    refine ⟨z, ?_, hz⟩
    show planeCoord z ∈ (K : Set Plane)
    rw [hzp]
    exact hpK
  have hkk : k₀ ≤ (k : ℤ) := (Int.self_le_toNat k₀).trans (by exact_mod_cast hk)
  have h := diam_le_of_smallInnerCells_originAncestorSquare hcomp.1 hcomp.2.1 hε0 hε1
    (by positivity) (by linarith) hk₀ hkk ⟨K, hKc⟩ hmeet
  rwa [Int.cast_natCast] at h

set_option maxHeartbeats 400000 in
/-- Cells meeting the squares around the origin have sublinear diameter under the
mass-transport, connectedness-along-lines and finite-expectation hypotheses. -/
theorem ae_ae_eventually_diam_le [IsFiniteMeasure μ] (hMT : MassTransport μ)
    (hL : ConnectedAlongLines μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᶠ k : ℕ in atTop,
      ∀ K : Cell, K ∈ H.1.restrict (planeCoord '' squareAt q.1 q.2.1 q.2.2 k 0) →
        Metric.diam (K : Set Plane) ≤ ε * (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
  have hΦ : ∫⁻ H, originCellRatioSum H ∂μ ≠ ∞ :=
    lintegral_originCellRatioSum_ne_top hMT hL hFE
  have hL28 : ∀ δ : ℝ, 0 < δ →
      (∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ k : ℤ in atTop,
        SmallInnerCells δ H (squareAt q.1 q.2.1 q.2.2 k 0)) →
      ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ k : ℤ in atTop,
        SmallInnerCells δ H (originAncestorSquare q k) := by
    intro δ _ hE
    exact ae_ae_eventually_dyadicAncestor_side_four
      (E := fun S H => SmallInnerCells δ H S)
      (Filter.Eventually.of_forall (measurableSet_smallInnerCells_cornerSquare δ)) hE
  exact ae_ae_eventually_diam_le_of_interior hMT hΦ hL28


/-- The diameter estimate along all sufficiently large integer generations. -/
theorem ae_ae_eventually_diam_le_int [IsFiniteMeasure μ] (hMT : MassTransport μ)
    (hL : ConnectedAlongLines μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᶠ k : ℤ in atTop,
      ∀ K : Cell, K ∈ H.1.restrict (planeCoord '' squareAt q.1 q.2.1 q.2.2 k 0) →
        Metric.diam (K : Set Plane) ≤ ε * (2 : ℝ) ^ (q.1 + (k : ℝ)) := by
  filter_upwards [ae_ae_eventually_diam_le hMT hL hFE] with H hH
  filter_upwards [hH] with q hq
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq ε hε)
  filter_upwards [eventually_ge_atTop (N : ℤ)] with k hk
  have hk0 : 0 ≤ k := le_trans (Int.natCast_nonneg N) hk
  have hkN : N ≤ k.toNat := by omega
  have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  have hreal : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hcast
  have h := hN k.toNat hkN
  simpa only [hcast, hreal] using h

/-- Eventually, every cell meeting an origin square has diameter at most half its side. -/
theorem ae_ae_eventually_diam_le_half_side [IsFiniteMeasure μ] (hMT : MassTransport μ)
    (hL : ConnectedAlongLines μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ j : ℤ in atTop, ∀ K : H.1.cells,
      (complexCells H.1 K ∩ squareAt q.1 q.2.1 q.2.2 j 0).Nonempty →
        Metric.diam (K.1 : Set Plane) ≤ (2 : ℝ) ^ (q.1 + (j : ℝ)) / 2 := by
  filter_upwards [ae_ae_eventually_diam_le_int hMT hL hFE] with H hH
  filter_upwards [hH] with q hq
  filter_upwards [hq (1 / 2) (by norm_num)] with j hj K hK
  obtain ⟨z, hzK, hzS⟩ := hK
  have hmem : K.1 ∈ H.1.restrict (planeCoord '' squareAt q.1 q.2.1 q.2.2 j 0) := by
    refine ⟨K.2, planeCoord z, ?_, z, hzS, rfl⟩
    exact hzK
  simpa [div_eq_mul_inv, mul_comm] using hj K.1 hmem

end Main

end LatticeProb.CellConfigCappedSquare
