/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CovarianceRootPropagation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalNondegeneracy

/-!
# From a null rooted cell property to a null property at every cell

`Limit.DirectionalNondegeneracy` proves the deterministic half of
`StatementIngredients.SymmetricPositiveDefinite (meanCovariance ν Φ)` and records
the exact missing probabilistic input: the rooted bracket density
`RootDensities.rootedGamma` only sees the *single* cell rooted at the origin, so
vanishing of its directional form almost surely has to be propagated to *every*
cell of the environment.

This file supplies that propagation for an arbitrary **covariant cell
property** `B` (a degree `0` label-level predicate that is preserved by the
physical similarity relabelings of `EnvironmentLaws.IsSimilarityRelabel` and is
measurable in the environment).  The transport used is

`T(𝓗, w, z) = ∑_H 1_{B(H)} 1_{w ∈ N_r(H)} 1_{z ∈ int H} / a_H`,

where `N_r(H) = {y | infDist y H ≤ r * diam H}` is the neighbourhood of `H` at
`r` times `H`'s own scale.  Both `infDist` and `diam` scale by the same factor
under `positiveSimilarity`, so `N_r(·)` is exactly covariant of degree `0` while
`a_H` scales by `s ^ 2`; the transport is therefore an honest
`EnvironmentLaws.MassTransportKernel` of degree `-2`, exactly as required by
`EnvironmentLaws.MassTransport`.  Nothing here assumes stationarity, an annealed
time law, ergodicity, or a mass-transport identity for this particular kernel.

The two integrals are computed exactly:

* incoming at the origin is `1_{B(H_0)} * volume (N_r(H_0)) / a_{H_0}`, because
  off the boundary mask the interior root `H_0` is unique; it therefore
  **vanishes** as soon as the rooted cell is not bad;
* outgoing from the origin is the *count* `∑_H 1_{B(H)} 1_{0 ∈ N_r(H)}` of bad
  cells that are near the origin at `r` times their own scale, because
  `volume (int H) = a_H` for a null-boundary cell.

Mass transport thus gives, for every fixed `r`, that almost surely no bad cell
sees the origin within `r` of its own diameter.  The scale `r` is free: running
it through `r = k ∈ ℕ` and using **positive cell area** (hence positive cell
diameter) leaves no room for a bad cell at all.  This is the "scaling-weighted"
variant of the naive degree `0` indicator: the indicator itself is scale
invariant, while the normalisation `1 / a_H` carries the required degree `-2`.

The final section specialises `B` to "some incident ordinary edge has nonzero
directional gradient `⟪ξ, Φ(H') - Φ(H)⟫`", whose covariance is exactly
`HarmonicLawIngredients.GradientCovariant`, and concludes the statement the
consumer needs: a vanishing directional mean covariance forces almost surely
vanishing directional gradients on *every* edge, hence — with the geometric
contradiction already proved in `Limit.DirectionalNondegeneracy` — strict
positivity of the directional form of `HarmonicLawIngredients.meanCovariance`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ReflectedGMS.CovarianceRootPropagation

open Code EnvironmentLaws Spatial

/-! ### Neighbourhoods at a multiple of a cell's own scale -/

/-- The neighbourhood of a cell at `r` times its own scale.  For `r = 1` this is
`Spatial.cellNeighborhood`; the free parameter `r` is what upgrades the
mass-transport conclusion from "not near the origin" to "nowhere". -/
def scaledCellNeighborhood (r : ℝ) (K : CompactCell) : Set Plane :=
  {z | Metric.infDist z (K : Set Plane) ≤ r * Metric.diam (K : Set Plane)}

theorem isClosed_scaledCellNeighborhoodMem (r : ℝ) :
    IsClosed {p : CompactCell × Plane | p.2 ∈ scaledCellNeighborhood r p.1} := by
  have hswap : Continuous fun p : CompactCell × Plane => (p.2, p.1) :=
    continuous_snd.prodMk continuous_fst
  have hlip : Continuous fun p : Plane × CompactCell => Metric.infDist p.1 (p.2 : Set Plane) :=
    (NonemptyCompacts.lipschitz_infDist (α := Plane)).continuous
  have hinf : Continuous fun p : CompactCell × Plane =>
      Metric.infDist p.2 (p.1 : Set Plane) := hlip.comp hswap
  have hdiam : Continuous fun p : CompactCell × Plane =>
      r * Metric.diam (p.1 : Set Plane) :=
    continuous_const.mul (continuous_cellDiam.comp continuous_fst)
  exact isClosed_le hinf hdiam

theorem measurableSet_scaledCellNeighborhoodMem (r : ℝ) :
    MeasurableSet {p : CompactCell × Plane | p.2 ∈ scaledCellNeighborhood r p.1} :=
  (isClosed_scaledCellNeighborhoodMem r).measurableSet

theorem isClosed_scaledCellNeighborhood (r : ℝ) (K : CompactCell) :
    IsClosed (scaledCellNeighborhood r K) :=
  isClosed_le (Metric.continuous_infDist_pt _) continuous_const

theorem measurableSet_scaledCellNeighborhood (r : ℝ) (K : CompactCell) :
    MeasurableSet (scaledCellNeighborhood r K) :=
  (isClosed_scaledCellNeighborhood r K).measurableSet

/-- Exact degree `0` covariance of the scaled neighbourhood. -/
theorem mem_scaledCellNeighborhood_transformCell_iff (r s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (z : Plane) :
    positiveSimilarity s u z ∈ scaledCellNeighborhood r (transformCell s u hs K)
      ↔ z ∈ scaledCellNeighborhood r K := by
  have hcoe : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarity s u '' (K : Set Plane) := coe_transformCell s u hs K
  have hrw : r * (s * Metric.diam (K : Set Plane))
      = s * (r * Metric.diam (K : Set Plane)) := by ring
  simp only [scaledCellNeighborhood, mem_setOf_eq, hcoe,
    infDist_image_positiveSimilarity s u hs, diam_image_positiveSimilarity s u hs, hrw]
  exact ⟨fun h => le_of_mul_le_mul_left h hs, fun h => mul_le_mul_of_nonneg_left h hs.le⟩

/-- A cell of positive area has positive diameter, so every point of the plane
lies in some scaled neighbourhood of it. -/
theorem diam_pos_of_volume_pos {K : CompactCell} (hK : 0 < volume (K : Set Plane)) :
    0 < Metric.diam (K : Set Plane) := by
  have hnt : (K : Set Plane).Nontrivial := by
    rcases Set.subsingleton_or_nontrivial (K : Set Plane) with hsub | hnt
    · exact absurd (hsub.measure_zero volume) hK.ne'
    · exact hnt
  exact Metric.diam_pos hnt K.isCompact.isBounded

theorem exists_nat_zero_mem_scaledCellNeighborhood {K : CompactCell}
    (hK : 0 < volume (K : Set Plane)) :
    ∃ k : ℕ, (0 : Plane) ∈ scaledCellNeighborhood (k : ℝ) K := by
  have hdiam := diam_pos_of_volume_pos hK
  obtain ⟨k, hk⟩ := exists_nat_ge (Metric.infDist (0 : Plane) (K : Set Plane) /
    Metric.diam (K : Set Plane))
  exact ⟨k, (div_le_iff₀ hdiam).mp hk⟩

/-! ### Covariant cell properties -/

/-- A degree `0` cell property: a label-level predicate on environments that is
measurable in the environment and is preserved by every physical similarity
relabeling.  Labels of absent slots are irrelevant: the transport below only
ever evaluates `mem` at active labels. -/
structure CovariantCellProperty where
  /-- The predicate, read at a code label. -/
  mem : Env → ℕ → Prop
  /-- Measurability in the environment, at each fixed label. -/
  measurableSet_mem : ∀ n : ℕ, MeasurableSet {e : Env | mem e n}
  /-- Invariance under the physical similarity relabelings of the environment
  law. -/
  covariant : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → ∀ v : Vertex e.val,
      (mem e' (relabel v).val ↔ mem e v.val)

/-- The `ℝ≥0∞`-valued indicator of a cell property at a fixed label. -/
noncomputable def markIndicator (B : CovariantCellProperty) (n : ℕ) : Env → ℝ≥0∞ :=
  Set.indicator {x : Env | B.mem x n} fun _ => (1 : ℝ≥0∞)

theorem measurable_markIndicator (B : CovariantCellProperty) (n : ℕ) :
    Measurable (markIndicator B n) :=
  measurable_const.indicator (B.measurableSet_mem n)

theorem markIndicator_of_mem {B : CovariantCellProperty} {n : ℕ} {e : Env}
    (h : B.mem e n) : markIndicator B n e = 1 := by
  have hmem : e ∈ {x : Env | B.mem x n} := h
  simp [markIndicator, Set.indicator_of_mem hmem]

theorem markIndicator_of_notMem {B : CovariantCellProperty} {n : ℕ} {e : Env}
    (h : ¬ B.mem e n) : markIndicator B n e = 0 := by
  have hmem : e ∉ {x : Env | B.mem x n} := h
  simp [markIndicator, Set.indicator_of_notMem hmem]

theorem markIndicator_ne_top (B : CovariantCellProperty) (n : ℕ) (e : Env) :
    markIndicator B n e ≠ ∞ := by
  by_cases h : B.mem e n
  · simp [markIndicator_of_mem h]
  · simp [markIndicator_of_notMem h]

theorem markIndicator_congr {B : CovariantCellProperty} {n m : ℕ} {e e' : Env}
    (h : B.mem e' m ↔ B.mem e n) : markIndicator B m e' = markIndicator B n e := by
  by_cases hb : B.mem e n
  · rw [markIndicator_of_mem (h.mpr hb), markIndicator_of_mem hb]
  · rw [markIndicator_of_notMem fun hx => hb (h.mp hx), markIndicator_of_notMem hb]

/-! ### The scaled patch transport of a single cell -/

/-- The contribution of one cell to the transport
`T(𝓗, w, z) = ∑_H 1_{w ∈ N_r(H)} 1_{z ∈ int H} / a_H`. -/
noncomputable def cellPatchTransport (r : ℝ) (K : CompactCell) (w z : Plane) : ℝ≥0∞ :=
  Set.indicator (scaledCellNeighborhood r K) (fun _ => (1 : ℝ≥0∞)) w *
      Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z /
    volume (K : Set Plane)

theorem cellPatchTransport_of_mem (r : ℝ) (K : CompactCell) {w z : Plane}
    (hw : w ∈ scaledCellNeighborhood r K) (hz : z ∈ interior (K : Set Plane)) :
    cellPatchTransport r K w z = (volume (K : Set Plane))⁻¹ := by
  simp [cellPatchTransport, Set.indicator_apply, hw, hz]

theorem cellPatchTransport_of_notMem_neighborhood (r : ℝ) (K : CompactCell) {w : Plane}
    (z : Plane) (hw : w ∉ scaledCellNeighborhood r K) :
    cellPatchTransport r K w z = 0 := by
  simp [cellPatchTransport, Set.indicator_apply, hw]

theorem cellPatchTransport_of_notMem_interior (r : ℝ) (K : CompactCell) (w : Plane)
    {z : Plane} (hz : z ∉ interior (K : Set Plane)) :
    cellPatchTransport r K w z = 0 := by
  simp [cellPatchTransport, Set.indicator_apply, hz]

theorem measurable_cellPatchTransport_target (r : ℝ) (K : CompactCell) (w : Plane) :
    Measurable fun z : Plane => cellPatchTransport r K w z := by
  have hEq : (fun z : Plane => cellPatchTransport r K w z)
      = fun z : Plane =>
        Set.indicator (scaledCellNeighborhood r K) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (K : Set Plane))⁻¹ *
          Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z := by
    funext z
    rw [cellPatchTransport, div_eq_mul_inv]
    ring
  rw [hEq]
  exact measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet)

theorem measurable_cellPatchTransport_source (r : ℝ) (K : CompactCell) (z : Plane) :
    Measurable fun w : Plane => cellPatchTransport r K w z := by
  have hEq : (fun w : Plane => cellPatchTransport r K w z)
      = fun w : Plane =>
        Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (K : Set Plane))⁻¹ *
          Set.indicator (scaledCellNeighborhood r K) (fun _ => (1 : ℝ≥0∞)) w := by
    funext w
    rw [cellPatchTransport, div_eq_mul_inv]
    ring
  rw [hEq]
  exact measurable_const.mul
    (measurable_const.indicator (measurableSet_scaledCellNeighborhood r K))

/-- Degree `-2` covariance of the scaled patch transport of one cell. -/
theorem cellPatchTransport_transformCell (r s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (w z : Plane) :
    cellPatchTransport r (transformCell s u hs K) (positiveSimilarity s u w)
        (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * cellPatchTransport r K w z := by
  have hcoe : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarity s u '' (K : Set Plane) := coe_transformCell s u hs K
  have hindNbhd : Set.indicator (scaledCellNeighborhood r (transformCell s u hs K))
        (fun _ => (1 : ℝ≥0∞)) (positiveSimilarity s u w)
      = Set.indicator (scaledCellNeighborhood r K) (fun _ => (1 : ℝ≥0∞)) w :=
    indicator_one_congr_of_iff (mem_scaledCellNeighborhood_transformCell_iff r s u hs K w)
  have hindInt : Set.indicator (interior ((transformCell s u hs K : CompactCell) : Set Plane))
        (fun _ => (1 : ℝ≥0∞)) (positiveSimilarity s u z)
      = Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z :=
    indicator_one_congr_of_iff (mem_interior_transformCell_iff s u hs K z)
  have hvol : volume ((transformCell s u hs K : CompactCell) : Set Plane)
      = ENNReal.ofReal (s ^ 2) * volume (K : Set Plane) := by
    rw [hcoe]
    exact volume_image_positiveSimilarity s u (K : Set Plane)
  have hspos : (0 : ℝ) < s ^ 2 := by positivity
  have hinv : (ENNReal.ofReal (s ^ 2) * volume (K : Set Plane))⁻¹
      = ENNReal.ofReal ((s ^ 2)⁻¹) * (volume (K : Set Plane))⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (by simpa using hspos.ne'))
      (Or.inl (by simp [ENNReal.ofReal_ne_top])), ENNReal.ofReal_inv_of_pos hspos]
  rw [cellPatchTransport, cellPatchTransport, hindNbhd, hindInt, hvol,
    div_eq_mul_inv, div_eq_mul_inv, hinv]
  ring

/-! ### Slot level -/

/-- The scaled patch transport of one code slot; absent slots transport
nothing. -/
noncomputable def slotPatchTransport (r : ℝ) (o : Option CompactCell) (w z : Plane) : ℝ≥0∞ :=
  o.elim 0 fun K => cellPatchTransport r K w z

def slotPatchTransportSupport (r : ℝ) : Set (Option CompactCell × Plane × Plane) :=
  {q | q.1.isSome ∧
    q.2.1 ∈ scaledCellNeighborhood r (q.1.getD referenceCell : CompactCell) ∧
    q.2.2 ∈ interior ((q.1.getD referenceCell : CompactCell) : Set Plane)}

theorem measurableSet_slotPatchTransportSupport (r : ℝ) :
    MeasurableSet (slotPatchTransportSupport r) := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hS0 : MeasurableSet {q : Option CompactCell × Plane × Plane | q.1.isSome} :=
    measurable_fst measurableSet_slotIsSome
  have hS1 : MeasurableSet {q : Option CompactCell × Plane × Plane |
      q.2.1 ∈ scaledCellNeighborhood r (q.1.getD referenceCell : CompactCell)} :=
    (hcellmap.prodMk (measurable_fst.comp measurable_snd))
      (measurableSet_scaledCellNeighborhoodMem r)
  have hS2 : MeasurableSet {q : Option CompactCell × Plane × Plane |
      q.2.2 ∈ interior ((q.1.getD referenceCell : CompactCell) : Set Plane)} :=
    (hcellmap.prodMk (measurable_snd.comp measurable_snd)) measurableSet_cellInterior
  have hEq : slotPatchTransportSupport r
      = {q : Option CompactCell × Plane × Plane | q.1.isSome} ∩
        ({q : Option CompactCell × Plane × Plane |
            q.2.1 ∈ scaledCellNeighborhood r (q.1.getD referenceCell : CompactCell)} ∩
          {q : Option CompactCell × Plane × Plane |
            q.2.2 ∈ interior ((q.1.getD referenceCell : CompactCell) : Set Plane)}) :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact hS0.inter (hS1.inter hS2)

theorem measurable_slotPatchTransport (r : ℝ) :
    Measurable fun q : Option CompactCell × Plane × Plane =>
      slotPatchTransport r q.1 q.2.1 q.2.2 := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hvol : Measurable fun q : Option CompactCell × Plane × Plane =>
      (volume ((q.1.getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
    (measurable_cellVolume.comp hcellmap).inv
  have hEq : (fun q : Option CompactCell × Plane × Plane =>
        slotPatchTransport r q.1 q.2.1 q.2.2)
      = Set.indicator (slotPatchTransportSupport r)
          (fun q => (volume ((q.1.getD referenceCell : CompactCell) : Set Plane))⁻¹) := by
    funext q
    obtain ⟨o, w, z⟩ := q
    cases o with
    | none =>
        have hmem : ((none : Option CompactCell), w, z) ∉ slotPatchTransportSupport r := by
          intro h
          simpa using h.1
        rw [Set.indicator_of_notMem hmem]
        rfl
    | some K =>
        have hiff : ((some K : Option CompactCell), w, z) ∈ slotPatchTransportSupport r
            ↔ w ∈ scaledCellNeighborhood r K ∧ z ∈ interior (K : Set Plane) := by
          simp [slotPatchTransportSupport]
        by_cases hw : w ∈ scaledCellNeighborhood r K
        · by_cases hz : z ∈ interior (K : Set Plane)
          · rw [Set.indicator_of_mem (hiff.mpr ⟨hw, hz⟩)]
            simp only [Option.getD_some]
            exact cellPatchTransport_of_mem r K hw hz
          · rw [Set.indicator_of_notMem fun h => hz (hiff.mp h).2]
            exact cellPatchTransport_of_notMem_interior r K w hz
        · rw [Set.indicator_of_notMem fun h => hw (hiff.mp h).1]
          exact cellPatchTransport_of_notMem_neighborhood r K z hw
  rw [hEq]
  exact hvol.indicator (measurableSet_slotPatchTransportSupport r)

/-! ### The marked transport on the environment space -/

/-- The manuscript-style transport carrying only the cells with the property
`B`: `T(𝓗, w, z) = ∑_H 1_{B(H)} 1_{w ∈ N_r(H)} 1_{z ∈ int H} / a_H`. -/
noncomputable def markedPatchTransport (B : CovariantCellProperty) (r : ℝ)
    (p : Env × Plane × Plane) : ℝ≥0∞ :=
  ∑' n : ℕ, markIndicator B n p.1 * slotPatchTransport r (p.1.val.1 n) p.2.1 p.2.2

theorem measurable_markedPatchTransport (B : CovariantCellProperty) (r : ℝ) :
    Measurable (markedPatchTransport B r) := by
  refine Measurable.ennreal_tsum fun n => ?_
  have h1 : Measurable fun p : Env × Plane × Plane => markIndicator B n p.1 :=
    (measurable_markIndicator B n).comp measurable_fst
  have hmap : Measurable fun p : Env × Plane × Plane => (p.1.val.1 n, p.2) :=
    (((measurable_pi_apply n).comp
      (measurable_fst.comp measurable_inclusion)).comp measurable_fst).prodMk measurable_snd
  exact h1.mul ((measurable_slotPatchTransport r).comp hmap)

theorem markedPatchTransport_eq_tsum_vertex (B : CovariantCellProperty) (r : ℝ)
    (e : Env) (w z : Plane) :
    markedPatchTransport B r (e, w, z)
      = ∑' v : Vertex e.val,
          markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z := by
  have hsupp : Function.support
      (fun n : ℕ => markIndicator B n e * slotPatchTransport r (e.val.1 n) w z)
      ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    cases hcase : e.val.1 n with
    | none =>
        refine absurd (show (fun n : ℕ =>
          markIndicator B n e * slotPatchTransport r (e.val.1 n) w z) n = 0 from ?_) hn
        simp [slotPatchTransport, hcase]
    | some K => simp [mem_setOf_eq, hcase]
  have hterm : ∀ v : Vertex e.val,
      markIndicator B v.val e * slotPatchTransport r (e.val.1 v.val) w z
        = markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z := by
    intro v
    have hv : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
    rw [hv]
    rfl
  calc markedPatchTransport B r (e, w, z)
      = ∑' n : ℕ, markIndicator B n e * slotPatchTransport r (e.val.1 n) w z := rfl
    _ = ∑' n : {n : ℕ | (e.val.1 n).isSome},
          markIndicator B n.val e * slotPatchTransport r (e.val.1 n.val) w z :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' v : Vertex e.val,
          markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z :=
        tsum_congr hterm

theorem markedPatchTransport_covariant (B : CovariantCellProperty) (r : ℝ)
    (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    markedPatchTransport B r (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * markedPatchTransport B r (e, w, z) := by
  obtain ⟨relabel, hrel⟩ := hsim
  rw [markedPatchTransport_eq_tsum_vertex, markedPatchTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq relabel (fun v' : Vertex e'.val => markIndicator B v'.val e' *
      cellPatchTransport r ((decode e').cell v')
        (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [hrel.1 v, cellPatchTransport_transformCell,
    markIndicator_congr (B.covariant s u hs e e' relabel hrel v)]
  ring

/-- The marked scaled patch transport as an actual `MassTransportKernel`. -/
noncomputable def markedPatchTransportKernel (B : CovariantCellProperty) (r : ℝ) :
    MassTransportKernel where
  toFun := markedPatchTransport B r
  measurable_toFun := measurable_markedPatchTransport B r
  covariant := fun s u hs e e' hsim w z =>
    markedPatchTransport_covariant B r s u hs e e' hsim w z

/-! ### The two integrals -/

theorem lintegral_cellPatchTransport_target (r : ℝ) (K : CompactCell) (w : Plane) :
    (∫⁻ z : Plane, cellPatchTransport r K w z ∂volume)
      = Set.indicator (scaledCellNeighborhood r K) (fun _ => (1 : ℝ≥0∞)) w *
          (volume (interior (K : Set Plane)) / volume (K : Set Plane)) := by
  have hI : MeasurableSet (interior (K : Set Plane)) := isOpen_interior.measurableSet
  have hz : ∀ z : Plane, cellPatchTransport r K w z
      = Set.indicator (interior (K : Set Plane)) (fun _ =>
          Set.indicator (scaledCellNeighborhood r K) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (K : Set Plane))⁻¹) z := by
    intro z
    by_cases hzI : z ∈ interior (K : Set Plane) <;>
      simp [cellPatchTransport, Set.indicator_apply, hzI, div_eq_mul_inv]
  simp_rw [hz]
  rw [lintegral_indicator_const hI, div_eq_mul_inv]
  ring

theorem lintegral_cellPatchTransport_source (r : ℝ) (K : CompactCell) (z : Plane) :
    (∫⁻ w : Plane, cellPatchTransport r K w z ∂volume)
      = Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
          (volume (scaledCellNeighborhood r K) / volume (K : Set Plane)) := by
  have hN : MeasurableSet (scaledCellNeighborhood r K) := measurableSet_scaledCellNeighborhood r K
  have hw : ∀ w : Plane, cellPatchTransport r K w z
      = Set.indicator (scaledCellNeighborhood r K) (fun _ =>
          Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (K : Set Plane))⁻¹) w := by
    intro w
    by_cases hwN : w ∈ scaledCellNeighborhood r K <;>
      simp [cellPatchTransport, Set.indicator_apply, hwN, div_eq_mul_inv]
  simp_rw [hw]
  rw [lintegral_indicator_const hN, div_eq_mul_inv]
  ring

/-- Outgoing mass from a source point: each marked cell whose scaled
neighbourhood contains the source contributes its interior-to-area ratio. -/
theorem lintegral_markedPatchTransport_outgoing (B : CovariantCellProperty) (r : ℝ)
    (e : Env) (w : Plane) :
    (∫⁻ z : Plane, markedPatchTransport B r (e, w, z) ∂volume)
      = ∑' v : Vertex e.val, markIndicator B v.val e *
          (Set.indicator (scaledCellNeighborhood r ((decode e).cell v))
              (fun _ => (1 : ℝ≥0∞)) w *
            (volume (interior ((decode e).cell v : Set Plane)) /
              volume ((decode e).cell v : Set Plane))) := by
  have hmeas : ∀ v : Vertex e.val, Measurable fun z : Plane =>
      markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z := fun v =>
    measurable_const.mul (measurable_cellPatchTransport_target r ((decode e).cell v) w)
  calc (∫⁻ z : Plane, markedPatchTransport B r (e, w, z) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val,
          markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z ∂volume :=
        lintegral_congr fun z => markedPatchTransport_eq_tsum_vertex B r e w z
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane,
          markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z ∂volume :=
        lintegral_tsum fun v => (hmeas v).aemeasurable
    _ = ∑' v : Vertex e.val, markIndicator B v.val e *
          (Set.indicator (scaledCellNeighborhood r ((decode e).cell v))
              (fun _ => (1 : ℝ≥0∞)) w *
            (volume (interior ((decode e).cell v : Set Plane)) /
              volume ((decode e).cell v : Set Plane))) := by
        refine tsum_congr fun v => ?_
        rw [lintegral_const_mul' _ _ (markIndicator_ne_top B v.val e),
          lintegral_cellPatchTransport_target]

/-- Incoming mass at a target point: each marked cell whose interior contains
the target contributes its neighbourhood-to-area ratio. -/
theorem lintegral_markedPatchTransport_incoming (B : CovariantCellProperty) (r : ℝ)
    (e : Env) (z : Plane) :
    (∫⁻ w : Plane, markedPatchTransport B r (e, w, z) ∂volume)
      = ∑' v : Vertex e.val, markIndicator B v.val e *
          (Set.indicator (interior ((decode e).cell v : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (scaledCellNeighborhood r ((decode e).cell v)) /
              volume ((decode e).cell v : Set Plane))) := by
  have hmeas : ∀ v : Vertex e.val, Measurable fun w : Plane =>
      markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z := fun v =>
    measurable_const.mul (measurable_cellPatchTransport_source r ((decode e).cell v) z)
  calc (∫⁻ w : Plane, markedPatchTransport B r (e, w, z) ∂volume)
      = ∫⁻ w : Plane, ∑' v : Vertex e.val,
          markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z ∂volume :=
        lintegral_congr fun w => markedPatchTransport_eq_tsum_vertex B r e w z
    _ = ∑' v : Vertex e.val, ∫⁻ w : Plane,
          markIndicator B v.val e * cellPatchTransport r ((decode e).cell v) w z ∂volume :=
        lintegral_tsum fun v => (hmeas v).aemeasurable
    _ = ∑' v : Vertex e.val, markIndicator B v.val e *
          (Set.indicator (interior ((decode e).cell v : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (scaledCellNeighborhood r ((decode e).cell v)) /
              volume ((decode e).cell v : Set Plane))) := by
        refine tsum_congr fun v => ?_
        rw [lintegral_const_mul' _ _ (markIndicator_ne_top B v.val e),
          lintegral_cellPatchTransport_source]

/-- Off the boundary mask the outgoing integral from the origin is exactly the
number of marked cells that see the origin at `r` times their own scale. -/
theorem lintegral_markedPatchTransport_outgoing_zero (B : CovariantCellProperty) (r : ℝ)
    (e : Env) :
    (∫⁻ z : Plane, markedPatchTransport B r (e, 0, z) ∂volume)
      = ∑' v : Vertex e.val, markIndicator B v.val e *
          Set.indicator (scaledCellNeighborhood r ((decode e).cell v))
            (fun _ => (1 : ℝ≥0∞)) 0 := by
  have hgeom := decode_geometry e
  rw [lintegral_markedPatchTransport_outgoing B r e 0]
  refine tsum_congr fun v => ?_
  have hvol := cellVolume_pos_lt_top (decode e) hgeom v
  have hint : volume (interior ((decode e).cell v : Set Plane))
      = volume ((decode e).cell v : Set Plane) :=
    volume_interior_eq_of_frontier_null (hgeom.2.2.1 v)
  rw [hint, ENNReal.div_self hvol.1.ne' hvol.2.ne, mul_one]

/-- If the rooted cell of the origin is unmasked and unmarked, no mass arrives
at the origin. -/
theorem lintegral_markedPatchTransport_incoming_zero (B : CovariantCellProperty) (r : ℝ)
    (e : Env) (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e))
    (hroot : ∀ v : Vertex e.val,
      RootDensities.rootAt (decode e) 0 = some v → ¬ B.mem e v.val) :
    (∫⁻ w : Plane, markedPatchTransport B r (e, w, 0) ∂volume) = 0 := by
  have hgeom := decode_geometry e
  rw [lintegral_markedPatchTransport_incoming B r e 0]
  refine ENNReal.tsum_eq_zero.mpr fun v => ?_
  by_cases hmem : (0 : Plane) ∈ interior ((decode e).cell v : Set Plane)
  · have hv : RootDensities.rootAt (decode e) 0 = some v :=
      (RootDensities.rootAt_eq_some_iff (decode e) hgeom 0 v).mpr ⟨he, hmem⟩
    rw [markIndicator_of_notMem (hroot v hv), zero_mul]
  · rw [Set.indicator_of_notMem hmem, zero_mul, mul_zero]

/-! ### The propagation theorem -/

/-- **One scale.**  Under mass transport, if almost surely the cell rooted at
the origin is unmarked, then almost surely no marked cell sees the origin within
`r` times its own diameter. -/
theorem ae_notMem_scaledCellNeighborhood_of_ae_root_notMem (B : CovariantCellProperty)
    (ν : Measure Env) (hν : MassTransport ν) (r : ℝ)
    (hroot : ∀ᵐ e ∂ν, ∀ v : Vertex e.val,
      RootDensities.rootAt (decode e) 0 = some v → ¬ B.mem e v.val) :
    ∀ᵐ e ∂ν, ∀ v : Vertex e.val, B.mem e v.val →
      (0 : Plane) ∉ scaledCellNeighborhood r ((decode e).cell v) := by
  have hmt : (∫⁻ e : Env, ∫⁻ z : Plane, markedPatchTransport B r (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ z : Plane, markedPatchTransport B r (e, z, 0) ∂volume ∂ν :=
    hν (markedPatchTransportKernel B r)
  have hin : (∫⁻ e : Env, ∫⁻ z : Plane, markedPatchTransport B r (e, z, 0) ∂volume ∂ν) = 0 := by
    rw [lintegral_congr_ae (g := fun _ : Env => (0 : ℝ≥0∞)) ?_]
    · exact lintegral_zero
    · filter_upwards [ae_notMem_boundaryMask_of_massTransport ν hν, hroot] with e he hg
      exact lintegral_markedPatchTransport_incoming_zero B r e he hg
  have hout : (∫⁻ e : Env, ∫⁻ z : Plane, markedPatchTransport B r (e, 0, z) ∂volume ∂ν) = 0 :=
    hmt.trans hin
  have hmeasout : Measurable fun e : Env =>
      ∫⁻ z : Plane, markedPatchTransport B r (e, 0, z) ∂volume :=
    (markedPatchTransportKernel B r).measurable_outgoing.lintegral_prod_right'
  have hae := (lintegral_eq_zero_iff hmeasout).mp hout
  filter_upwards [hae] with e he
  have he0 : (∫⁻ z : Plane, markedPatchTransport B r (e, 0, z) ∂volume) = 0 := he
  rw [lintegral_markedPatchTransport_outgoing_zero B r e] at he0
  intro v hv hmem
  have hterm := ENNReal.tsum_eq_zero.mp he0 v
  rw [markIndicator_of_mem hv, one_mul, Set.indicator_of_mem hmem] at hterm
  exact one_ne_zero hterm

/-- **Root-null covariant cell property propagates to every cell.**  Under the
manuscript mass-transport law, if almost surely the cell rooted at the origin
does not have the covariant property `B`, then almost surely *no* cell of the
environment has it.

The scale `r` of the transport is free, and cells have positive area hence
positive diameter, so the one-scale conclusion at `r = k ∈ ℕ` leaves no marked
cell anywhere. -/
theorem ae_forall_not_mem_of_ae_root_not_mem (B : CovariantCellProperty)
    (ν : Measure Env) (hν : MassTransport ν)
    (hroot : ∀ᵐ e ∂ν, ∀ v : Vertex e.val,
      RootDensities.rootAt (decode e) 0 = some v → ¬ B.mem e v.val) :
    ∀ᵐ e ∂ν, ∀ v : Vertex e.val, ¬ B.mem e v.val := by
  have hscale : ∀ᵐ e ∂ν, ∀ k : ℕ, ∀ v : Vertex e.val, B.mem e v.val →
      (0 : Plane) ∉ scaledCellNeighborhood (k : ℝ) ((decode e).cell v) :=
    ae_all_iff.mpr fun k =>
      ae_notMem_scaledCellNeighborhood_of_ae_root_notMem B ν hν (k : ℝ) hroot
  filter_upwards [hscale] with e he v hv
  have hvol := (cellVolume_pos_lt_top (decode e) (decode_geometry e) v).1
  obtain ⟨k, hk⟩ := exists_nat_zero_mem_scaledCellNeighborhood hvol
  exact he k v hv hk

/-! ### Specialisation: zero rooted directional energy propagates to every edge -/

section DirectionalEnergy

open EnvironmentFields HarmonicLawIngredients RootDensities StatementIngredients
open DirectionalNondegeneracy

/-- Positive conductance forces both endpoints to be active labels: this is the
`absent` clause of `Code.AdmissibleConductance`. -/
theorem isSome_of_conductance_pos (e : Env) {n m : ℕ} (h : 0 < e.val.2 n m) :
    (e.val.1 n).isSome ∧ (e.val.1 m).isSome := by
  have habs := e.property.choose.absent n m
  constructor
  · cases hn : e.val.1 n with
    | none => exact absurd (habs (Or.inl hn)) h.ne'
    | some K => simp [hn]
  · cases hm : e.val.1 m with
    | none => exact absurd (habs (Or.inr hm)) h.ne'
    | some K => simp [hm]

/-- The directional gradient of `Φ` read at code labels.  On active labels this
is definitionally `DirectionalNondegeneracy.directionalGradient` of `Φ.at e`. -/
noncomputable def labelDirectionalGradient (Φ : CellField) (ξ : Fin 2 → ℝ) (e : Env)
    (n m : ℕ) : ℝ :=
  directionalGradient (Φ.value e) ξ n m

theorem measurable_labelDirectionalGradient (Φ : CellField) (ξ : Fin 2 → ℝ) (n m : ℕ) :
    Measurable fun e : Env => labelDirectionalGradient Φ ξ e n m := by
  have hcont : Continuous fun y : Plane => dirPairing ξ y := by
    simp only [dirPairing]
    refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
    first
      | exact PiLp.continuous_apply _ _ i
      | fun_prop
  have h1 : Measurable fun e : Env => dirPairing ξ (Φ.value e m) :=
    hcont.measurable.comp (Φ.measurable_label m)
  have h2 : Measurable fun e : Env => dirPairing ξ (Φ.value e n) :=
    hcont.measurable.comp (Φ.measurable_label n)
  have hEq : (fun e : Env => labelDirectionalGradient Φ ξ e n m)
      = (fun e : Env => dirPairing ξ (Φ.value e m)) -
        fun e : Env => dirPairing ξ (Φ.value e n) := by
    funext e
    simp [labelDirectionalGradient, directionalGradient_eq_sub]
  rw [hEq]
  exact h1.sub h2

/-- The cell property "some incident ordinary edge has nonzero directional
gradient", read at code labels. -/
def DirectionalEnergyMem (Φ : CellField) (ξ : Fin 2 → ℝ) (e : Env) (n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < e.val.2 n m ∧ labelDirectionalGradient Φ ξ e n m ≠ 0

theorem measurableSet_directionalEnergyMem (Φ : CellField) (ξ : Fin 2 → ℝ) (n : ℕ) :
    MeasurableSet {e : Env | DirectionalEnergyMem Φ ξ e n} := by
  have hEq : {e : Env | DirectionalEnergyMem Φ ξ e n}
      = ⋃ m : ℕ, ({e : Env | 0 < e.val.2 n m} ∩
          {e : Env | labelDirectionalGradient Φ ξ e n m ≠ 0}) := by
    ext e
    constructor
    · rintro ⟨m, h1, h2⟩
      exact Set.mem_iUnion.mpr ⟨m, h1, h2⟩
    · intro h
      obtain ⟨m, h1, h2⟩ := Set.mem_iUnion.mp h
      exact ⟨m, h1, h2⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun m => MeasurableSet.inter ?_ ?_
  · have hc : Measurable fun e : Env => e.val.2 n m :=
      (measurable_pi_apply m).comp
        ((measurable_pi_apply n).comp (measurable_snd.comp measurable_inclusion))
    exact measurableSet_lt measurable_const hc
  · have hg := measurable_labelDirectionalGradient Φ ξ n m
    have hset : {e : Env | labelDirectionalGradient Φ ξ e n m ≠ 0}
        = ((fun e : Env => labelDirectionalGradient Φ ξ e n m) ⁻¹' {0})ᶜ := by
      ext e
      simp
    rw [hset]
    exact (hg (measurableSet_singleton 0)).compl

/-- Conductances are unchanged by a physical similarity relabeling. -/
theorem conductance_similarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val}
    (hrel : IsSimilarityRelabel s u hs e e' relabel) (v w : Vertex e.val) :
    e'.val.2 (relabel v).val (relabel w).val = e.val.2 v.val w.val := hrel.2 v w

/-- The directional gradient picks up exactly the factor `s` of the similarity:
this is the `HarmonicLawIngredients.GradientCovariant` law read in coordinates. -/
theorem labelDirectionalGradient_similarity {Φ : CellField} (hcov : GradientCovariant Φ)
    (ξ : Fin 2 → ℝ) {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val}
    (hrel : IsSimilarityRelabel s u hs e e' relabel) (v w : Vertex e.val) :
    labelDirectionalGradient Φ ξ e' (relabel v).val (relabel w).val
      = s * labelDirectionalGradient Φ ξ e v.val w.val := by
  have hco : ∀ i : Fin 2,
      Φ.value e' (relabel w).val i - Φ.value e' (relabel v).val i
        = s * (Φ.value e w.val i - Φ.value e v.val i) := by
    intro i
    have hg := hcov s u hs e e' relabel hrel v w
    have h2 := congrArg (fun y : Plane => y i) hg
    simpa [CellField.gradient, CellField.at, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      using h2
  simp only [labelDirectionalGradient, directionalGradient, hco, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The directional-energy cell property is invariant under every physical
similarity relabeling. -/
theorem directionalEnergyMem_similarity {Φ : CellField} (hcov : GradientCovariant Φ)
    (ξ : Fin 2 → ℝ) (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (relabel : Vertex e.val ≃ Vertex e'.val)
    (hrel : IsSimilarityRelabel s u hs e e' relabel) (v : Vertex e.val) :
    DirectionalEnergyMem Φ ξ e' (relabel v).val ↔ DirectionalEnergyMem Φ ξ e v.val := by
  constructor
  · rintro ⟨m, hpos, hne⟩
    obtain ⟨-, hm⟩ := isSome_of_conductance_pos e' hpos
    obtain ⟨w, hw⟩ : ∃ w : Vertex e.val, (relabel w).val = m :=
      ⟨relabel.symm ⟨m, hm⟩, by rw [Equiv.apply_symm_apply]⟩
    refine ⟨w.val, ?_, ?_⟩
    · rw [← conductance_similarity hrel v w, hw]
      exact hpos
    · intro h0
      have hl := labelDirectionalGradient_similarity hcov ξ hrel v w
      rw [hw, h0, mul_zero] at hl
      exact hne hl
  · rintro ⟨m, hpos, hne⟩
    obtain ⟨-, hm⟩ := isSome_of_conductance_pos e hpos
    refine ⟨(relabel ⟨m, hm⟩).val, ?_, ?_⟩
    · rw [conductance_similarity hrel v ⟨m, hm⟩]
      exact hpos
    · intro h0
      have hl := labelDirectionalGradient_similarity hcov ξ hrel v ⟨m, hm⟩
      rw [h0] at hl
      exact hne ((mul_eq_zero.mp hl.symm).resolve_left (ne_of_gt hs))

/-- The directional-energy property as a `CovariantCellProperty`, using exactly
the `HarmonicLawIngredients.GradientCovariant` law of the cell field. -/
noncomputable def directionalEnergyProperty (Φ : CellField) (hcov : GradientCovariant Φ)
    (ξ : Fin 2 → ℝ) : CovariantCellProperty where
  mem := DirectionalEnergyMem Φ ξ
  measurableSet_mem := measurableSet_directionalEnergyMem Φ ξ
  covariant := fun s u hs e e' relabel hrel v =>
    directionalEnergyMem_similarity hcov ξ s u hs e e' relabel hrel v

theorem directionalEnergyProperty_mem (Φ : CellField) (hcov : GradientCovariant Φ)
    (ξ : Fin 2 → ℝ) (e : Env) (n : ℕ) :
    (directionalEnergyProperty Φ hcov ξ).mem e n ↔ DirectionalEnergyMem Φ ξ e n := Iff.rfl

/-- Zero rooted directional energy at the origin means the rooted cell is not
marked: a marked incident edge would make the rooted quadratic form strictly
positive, by `DirectionalNondegeneracy.quadraticForm_bracketDensity_pos`. -/
theorem not_directionalEnergyMem_of_quadraticForm_rootedGamma_eq_zero
    (Φ : CellField) (ξ : Fin 2 → ℝ) (e : Env) {v : Vertex e.val}
    (hv : rootAt (decode e) 0 = some v)
    (h0 : (∑ i : Fin 2, ∑ j : Fin 2,
      ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) = 0) :
    ¬ DirectionalEnergyMem Φ ξ e v.val := by
  rintro ⟨m, hpos, hne⟩
  obtain ⟨-, hm⟩ := isSome_of_conductance_pos e hpos
  have hgeom := decode_geometry e
  have hfin := hgeom.2.2.2.2.2.2.1 v
  have hcpos : 0 < (decode e).graph.c v ⟨m, hm⟩ := hpos
  have hgrad : directionalGradient (Φ.at e) ξ v ⟨m, hm⟩ ≠ 0 := hne
  have hbpos := quadraticForm_bracketDensity_pos (decode e) hgeom (Φ.at e) v ξ hcpos hgrad
  rw [quadraticForm_bracketDensity (decode e) (Φ.at e) v hfin ξ,
    ← quadraticForm_rootedGamma_eq (decode e) (Φ.at e) 0 hv hfin ξ, h0] at hbpos
  exact lt_irrefl 0 hbpos

/-- **Zero rooted directional energy propagates to every edge.**  Under the
manuscript mass-transport law and the gradient covariance of the cell field, if
the directional form of the rooted bracket density at the origin vanishes almost
surely, then almost surely *every* ordinary edge of the environment has
vanishing directional gradient. -/
theorem ae_forall_directionalGradient_eq_zero_of_ae_rooted_quadraticForm_eq_zero
    (ν : Measure Env) (hν : MassTransport ν) (Φ : CellField) (hcov : GradientCovariant Φ)
    (ξ : Fin 2 → ℝ)
    (hzero : ∀ᵐ e ∂ν, (∑ i : Fin 2, ∑ j : Fin 2,
      ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) = 0) :
    ∀ᵐ e ∂ν, ∀ v w : Vertex e.val, 0 < (decode e).graph.c v w →
      directionalGradient (Φ.at e) ξ v w = 0 := by
  have hroot : ∀ᵐ e ∂ν, ∀ v : Vertex e.val,
      rootAt (decode e) 0 = some v →
        ¬ (directionalEnergyProperty Φ hcov ξ).mem e v.val := by
    filter_upwards [hzero] with e he v hv
    exact not_directionalEnergyMem_of_quadraticForm_rootedGamma_eq_zero Φ ξ e hv he
  filter_upwards [ae_forall_not_mem_of_ae_root_not_mem
    (directionalEnergyProperty Φ hcov ξ) ν hν hroot] with e he v w hc
  by_contra hne
  exact he v ((directionalEnergyProperty_mem Φ hcov ξ e v.val).mpr ⟨w.val, hc, hne⟩)

/-- A vanishing directional form of the deterministic mean covariance forces the
rooted directional energy to vanish almost surely: the rooted form is a
nonnegative integrable function with zero integral. -/
theorem ae_quadraticForm_rootedGamma_eq_zero_of_quadraticForm_meanCovariance_eq_zero
    (ν : Measure Env) (Φ : CellField) (hint : IntegrableBracket ν Φ) (ξ : Fin 2 → ℝ)
    (h0 : (∑ i : Fin 2, ∑ j : Fin 2, ξ i * meanCovariance ν Φ i j * ξ j) = 0) :
    ∀ᵐ e ∂ν, (∑ i : Fin 2, ∑ j : Fin 2,
      ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) = 0 := by
  have hintegrable : Integrable (fun e : Env => ∑ i : Fin 2, ∑ j : Fin 2,
      ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hint i j).const_mul (ξ i)).mul_const (ξ j)
  have hnonneg : (0 : Env → ℝ) ≤ fun e : Env => ∑ i : Fin 2, ∑ j : Fin 2,
      ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j := fun e =>
    quadraticForm_rootedGamma_nonneg (decode e) (decode_geometry e) (Φ.at e) 0 ξ
  rw [quadraticForm_meanCovariance_eq_integral ν Φ hint ξ] at h0
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hintegrable).mp h0
  filter_upwards [hae] with e he
  simpa using he

/-- **Directional positive definiteness of the mean covariance.**  Combining the
propagation above with the deterministic geometric contradiction already proved
in `Limit.DirectionalNondegeneracy`: on a nonzero environment law satisfying the
mass-transport law, with a gradient-covariant cell field that is almost surely a
uniformly sublinear corrector on an environment with almost surely submacroscopic
cell diameters, every nonzero direction has strictly positive mean bracket
form. -/
theorem quadraticForm_meanCovariance_pos (ν : Measure Env) (hνne : ν ≠ 0)
    (hν : MassTransport ν) (Φ : CellField) (hcov : GradientCovariant Φ)
    (hint : IntegrableBracket ν Φ)
    (hsub : ∀ᵐ e ∂ν, UniformlySublinearCorrector (decode e) (Φ.at e))
    (hdiam : ∀ᵐ e ∂ν, SubmacroscopicDiameters (decode e))
    {ξ : Fin 2 → ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ i : Fin 2, ∑ j : Fin 2, ξ i * meanCovariance ν Φ i j * ξ j := by
  refine lt_of_le_of_ne (quadraticForm_meanCovariance_nonneg ν Φ hint ξ) ?_
  intro h0
  have hae := ae_forall_directionalGradient_eq_zero_of_ae_rooted_quadraticForm_eq_zero
    ν hν Φ hcov ξ
    (ae_quadraticForm_rootedGamma_eq_zero_of_quadraticForm_meanCovariance_eq_zero
      ν Φ hint ξ h0.symm)
  have hfalse : ∀ᵐ _e ∂ν, False := by
    filter_upwards [hae, hsub, hdiam] with e h1 h2 h3
    obtain ⟨v, w, hc, hg⟩ :=
      exists_edge_directionalGradient_ne_zero (decode e) (decode_geometry e) (Φ.at e) h2 h3 hξ
    exact hg (h1 v w hc)
  exact (ae_neBot.mpr hνne).ne (Filter.eventually_false_iff_eq_bot.mp hfalse)

end DirectionalEnergy

end ReflectedGMS.CovarianceRootPropagation
