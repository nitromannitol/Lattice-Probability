/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.NullBoundaryRoots at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CellSlotMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Spatial.UncoveredRootTransport
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The origin is almost surely not on a cell boundary

This file carries out the mass-transport argument of the reflected-GMS
manuscript (Section "Null boundaries, large cells, and dyadic blocks"):
apply the mass-transport principle to the actual transport
`T(H, w, z) = ∑_{H ∈ 𝓗} 1_{w ∈ ∂H} 1_{z ∈ H} / a_H`.
Its incoming integral at the origin vanishes, because every cell frontier is
Lebesgue null, while its outgoing integral counts the cell boundaries through
the origin.  Hence that count has expectation zero, so almost surely the origin
lies on no cell boundary.

Nothing here assumes stationarity, a mass-transport identity for this
particular kernel, or null boundary roots: the kernel is *constructed* as an
`EnvironmentLaws.MassTransportKernel` (joint measurability on the full trace
sigma algebra and exact `(s ^ 2)⁻¹` covariance for the existing
`EnvironmentLaws.IsSimilarity` relation), and the existing law
`EnvironmentLaws.MassTransport` is then invoked.

The measurability inputs are proved for the Hausdorff Borel structure on cells:
cell membership is a closed condition, interior membership is a countable
union of countable intersections of closed conditions tested on a countable
dense set of points, and the cell area is measurable because it is the
Lebesgue integral of the membership indicator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Pointwise

namespace ReflectedGMS.Spatial

open Code EnvironmentLaws

/-! ### Joint measurability of membership, interior and frontier of a cell

The cell-membership and code-slot facts moved to `Spatial/CellSlotMeasurable.lean`,
which this file imports; they are unchanged and keep their names. -/

/-- Membership of a fixed point in a varying cell is measurable. -/
theorem measurableSet_mem_cell (y : Plane) :
    MeasurableSet {K : CompactCell | y ∈ (K : Set Plane)} := by
  have hmap : Measurable fun K : CompactCell => (K, y) :=
    measurable_id.prodMk measurable_const
  have h := hmap measurableSet_cellMem
  exact h

/-- Interior membership is measurable: a point is interior to a compact cell
exactly when some rational-radius ball around it is covered, and covering can be
tested on a fixed countable dense set of points. -/
theorem measurableSet_cellInterior :
    MeasurableSet {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} := by
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense Plane
  haveI : Countable D := hDcount.to_subtype
  have key : {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)}
      = ⋃ n : ℕ, ⋂ y : D, {p : CompactCell × Plane |
          dist p.2 (y : Plane) < 1 / (n + 1) → (y : Plane) ∈ (p.1 : Set Plane)} := by
    ext p
    obtain ⟨K, w⟩ := p
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
    constructor
    · intro hw
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine ⟨n, fun y hy => ?_⟩
      have hyball : (y : Plane) ∈ Metric.ball w ε := by
        rw [Metric.mem_ball, dist_comm]
        exact hy.trans hn
      exact interior_subset (hball hyball)
    · rintro ⟨n, hn⟩
      have hρ : (0 : ℝ) < 1 / (n + 1) := by positivity
      have hsub : Metric.ball w (1 / (n + 1)) ⊆ (K : Set Plane) := by
        intro x hx
        have hxw : dist x w < 1 / (n + 1) := Metric.mem_ball.mp hx
        have hclos : x ∈ closure (K : Set Plane) := by
          rw [Metric.mem_closure_iff]
          intro ε hε
          obtain ⟨y, hyD, hyx⟩ :=
            Metric.mem_closure_iff.mp (hDdense x) (min ε (1 / (n + 1) - dist x w))
              (lt_min hε (by linarith))
          refine ⟨y, hn ⟨y, hyD⟩ ?_, lt_of_lt_of_le hyx (min_le_left _ _)⟩
          have hlt : dist x y < 1 / (n + 1) - dist x w :=
            lt_of_lt_of_le hyx (min_le_right _ _)
          have htri : dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
          have hwx : dist w x = dist x w := dist_comm w x
          linarith
        rwa [K.isCompact.isClosed.closure_eq] at hclos
      exact mem_interior.mpr
        ⟨Metric.ball w (1 / (n + 1)), hsub, Metric.isOpen_ball, Metric.mem_ball_self hρ⟩
  rw [key]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun y => ?_
  have h1 : MeasurableSet {p : CompactCell × Plane | dist p.2 (y : Plane) < 1 / (n + 1)} := by
    have hset : {p : CompactCell × Plane | dist p.2 (y : Plane) < 1 / (n + 1)}
        = Prod.snd ⁻¹' Metric.ball (y : Plane) (1 / (n + 1)) := by
      ext p
      simp [Metric.mem_ball]
    rw [hset]
    exact measurable_snd Metric.isOpen_ball.measurableSet
  have h2 : MeasurableSet {p : CompactCell × Plane | (y : Plane) ∈ (p.1 : Set Plane)} :=
    measurable_fst (measurableSet_mem_cell (y : Plane))
  have hunion : {p : CompactCell × Plane |
        dist p.2 (y : Plane) < 1 / (n + 1) → (y : Plane) ∈ (p.1 : Set Plane)}
      = {p : CompactCell × Plane | dist p.2 (y : Plane) < 1 / (n + 1)}ᶜ ∪
        {p : CompactCell × Plane | (y : Plane) ∈ (p.1 : Set Plane)} := by
    ext p
    simp only [mem_setOf_eq, mem_union, mem_compl_iff]
    exact imp_iff_not_or
  rw [hunion]
  exact h1.compl.union h2

/-- Frontier membership is measurable: for a compact cell it is membership
minus interior membership. -/
theorem measurableSet_cellFrontier :
    MeasurableSet {p : CompactCell × Plane | p.2 ∈ frontier (p.1 : Set Plane)} := by
  have hdiff : {p : CompactCell × Plane | p.2 ∈ frontier (p.1 : Set Plane)}
      = {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} \
        {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} := by
    ext p
    obtain ⟨K, w⟩ := p
    simp [K.isCompact.isClosed.frontier_eq]
  rw [hdiff]
  exact measurableSet_cellMem.diff measurableSet_cellInterior

/-- The cell area is measurable in the cell: it is the Lebesgue integral of the
jointly measurable membership indicator. -/
theorem measurable_cellVolume :
    Measurable fun K : CompactCell => volume (K : Set Plane) := by
  have hf : Measurable (Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
      (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator measurableSet_cellMem
  have hint : Measurable fun K : CompactCell =>
      ∫⁻ z : Plane, Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
        (fun _ => (1 : ℝ≥0∞)) (K, z) ∂volume :=
    hf.lintegral_prod_right' (ν := (volume : Measure Plane))
  have hpt : ∀ K : CompactCell,
      (∫⁻ z : Plane, Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
          (fun _ => (1 : ℝ≥0∞)) (K, z) ∂volume) = volume (K : Set Plane) := by
    intro K
    have hz : ∀ z : Plane,
        Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
            (fun _ => (1 : ℝ≥0∞)) (K, z)
          = Set.indicator (K : Set Plane) (fun _ => (1 : ℝ≥0∞)) z := by
      intro z
      by_cases hzK : z ∈ (K : Set Plane)
      · have hmem : (K, z) ∈ {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} := hzK
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzK]
      · have hmem : (K, z) ∉ {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} := hzK
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hzK]
    simp_rw [hz]
    rw [lintegral_indicator_const K.isCompact.isClosed.measurableSet, one_mul]
  have hEq : (fun K : CompactCell => volume (K : Set Plane))
      = fun K : CompactCell =>
        ∫⁻ z : Plane, Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
          (fun _ => (1 : ℝ≥0∞)) (K, z) ∂volume := by
    funext K
    exact (hpt K).symm
  rw [hEq]
  exact hint

/-! ### Lebesgue area under a positive similarity -/

/-- A positive similarity rescales Lebesgue area of any set by `s ^ 2`. -/
theorem volume_image_positiveSimilarity (s : ℝ) (u : Plane) (A : Set Plane) :
    volume (positiveSimilarity s u '' A) = ENNReal.ofReal (s ^ 2) * volume A := by
  have hfun : positiveSimilarity s u
      = (fun y : Plane => -(s • u) + y) ∘ (fun z : Plane => s • z) := by
    funext z
    show s • (z - u) = -(s • u) + s • z
    rw [smul_sub, sub_eq_neg_add]
  have htrans : ∀ (c : Plane) (B : Set Plane),
      volume ((fun y : Plane => c + y) '' B) = volume B := by
    intro c B
    have hpre : (fun y : Plane => c + y) '' B = (fun y : Plane => -c + y) ⁻¹' B := by
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        simpa using hb
      · intro hy
        exact ⟨-c + y, hy, by simp⟩
    rw [hpre]
    exact measure_preimage_add volume (-c) B
  have hsmul : (fun z : Plane => s • z) '' A = s • A := Set.image_smul
  rw [hfun, Set.image_comp, htrans, hsmul, Measure.addHaar_smul volume s A,
    finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg s)]

/-! ### The manuscript's boundary transport kernel -/


/-- The contribution of one cell to the manuscript transport
`T(𝓗, w, z) = ∑_H 1_{w ∈ ∂H} 1_{z ∈ H} / a_H`. -/
noncomputable def cellBoundaryTransport (K : CompactCell) (w z : Plane) : ℝ≥0∞ :=
  Set.indicator (frontier (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
      Set.indicator (K : Set Plane) (fun _ => (1 : ℝ≥0∞)) z /
    volume (K : Set Plane)

theorem cellBoundaryTransport_of_mem (K : CompactCell) {w z : Plane}
    (hw : w ∈ frontier (K : Set Plane)) (hz : z ∈ (K : Set Plane)) :
    cellBoundaryTransport K w z = (volume (K : Set Plane))⁻¹ := by
  simp [cellBoundaryTransport, Set.indicator_apply, hw, hz]

theorem cellBoundaryTransport_of_notMem_frontier (K : CompactCell) {w : Plane} (z : Plane)
    (hw : w ∉ frontier (K : Set Plane)) :
    cellBoundaryTransport K w z = 0 := by
  simp [cellBoundaryTransport, Set.indicator_apply, hw]

theorem cellBoundaryTransport_of_notMem_cell (K : CompactCell) (w : Plane) {z : Plane}
    (hz : z ∉ (K : Set Plane)) :
    cellBoundaryTransport K w z = 0 := by
  simp [cellBoundaryTransport, Set.indicator_apply, hz]

/-- Measurability of the cell transport in the target point alone. -/
theorem measurable_cellBoundaryTransport_target (K : CompactCell) (w : Plane) :
    Measurable fun z : Plane => cellBoundaryTransport K w z := by
  have hEq : (fun z : Plane => cellBoundaryTransport K w z)
      = fun z : Plane =>
        Set.indicator (frontier (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (K : Set Plane))⁻¹ *
          Set.indicator (K : Set Plane) (fun _ => (1 : ℝ≥0∞)) z := by
    funext z
    rw [cellBoundaryTransport, div_eq_mul_inv]
    ring
  rw [hEq]
  exact measurable_const.mul (measurable_const.indicator K.isCompact.isClosed.measurableSet)

/-- Measurability of the cell transport in the source point alone. -/
theorem measurable_cellBoundaryTransport_source (K : CompactCell) (z : Plane) :
    Measurable fun w : Plane => cellBoundaryTransport K w z := by
  have hEq : (fun w : Plane => cellBoundaryTransport K w z)
      = fun w : Plane =>
        Set.indicator (K : Set Plane) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (K : Set Plane))⁻¹ *
          Set.indicator (frontier (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w := by
    funext w
    rw [cellBoundaryTransport, div_eq_mul_inv]
    ring
  rw [hEq]
  exact measurable_const.mul (measurable_const.indicator isClosed_frontier.measurableSet)

/-- Frontier and membership conditions, and the area, transform exactly as they
must for the `(s ^ 2)⁻¹` covariance of the transport. -/
theorem cellBoundaryTransport_transformCell (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (w z : Plane) :
    cellBoundaryTransport (transformCell s u hs K) (positiveSimilarity s u w)
        (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * cellBoundaryTransport K w z := by
  have hcoe : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarity s u '' (K : Set Plane) := coe_transformCell s u hs K
  have hhom : ⇑(positiveSimilarityHomeomorph s u hs) = positiveSimilarity s u := rfl
  have hinj : Function.Injective (positiveSimilarity s u) := by
    rw [← hhom]
    exact (positiveSimilarityHomeomorph s u hs).injective
  have hfront : frontier (positiveSimilarity s u '' (K : Set Plane))
      = positiveSimilarity s u '' frontier (K : Set Plane) := by
    rw [← hhom]
    exact ((positiveSimilarityHomeomorph s u hs).image_frontier (K : Set Plane)).symm
  have hind : ∀ (A : Set Plane) (x : Plane),
      Set.indicator (positiveSimilarity s u '' A) (fun _ => (1 : ℝ≥0∞))
          (positiveSimilarity s u x)
        = Set.indicator A (fun _ => (1 : ℝ≥0∞)) x := by
    intro A x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem (mem_image_of_mem _ hx), Set.indicator_of_mem hx]
    · have hnot : positiveSimilarity s u x ∉ positiveSimilarity s u '' A := by
        intro hmem
        exact hx (hinj.mem_set_image.mp hmem)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hx]
  have hvol : volume (positiveSimilarity s u '' (K : Set Plane))
      = ENNReal.ofReal (s ^ 2) * volume (K : Set Plane) :=
    volume_image_positiveSimilarity s u (K : Set Plane)
  have hspos : (0 : ℝ) < s ^ 2 := by positivity
  have hinv : (ENNReal.ofReal (s ^ 2) * volume (K : Set Plane))⁻¹
      = ENNReal.ofReal ((s ^ 2)⁻¹) * (volume (K : Set Plane))⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (by simpa using hspos.ne'))
      (Or.inl (by simp [ENNReal.ofReal_ne_top])), ENNReal.ofReal_inv_of_pos hspos]
  rw [cellBoundaryTransport, cellBoundaryTransport, hcoe, hfront, hind, hind, hvol,
    div_eq_mul_inv, div_eq_mul_inv, hinv]
  ring

/-- The transport contribution of one code slot; absent slots transport nothing. -/
noncomputable def slotBoundaryTransport (o : Option CompactCell) (w z : Plane) : ℝ≥0∞ :=
  o.elim 0 fun K => cellBoundaryTransport K w z


/-- The support of the slot transport: the slot is present, the source is on its
cell boundary and the target is in its cell. -/
def slotBoundaryTransportSupport : Set (Option CompactCell × Plane × Plane) :=
  {q | q.1.isSome ∧ q.2.1 ∈ frontier ((q.1.getD referenceCell : CompactCell) : Set Plane) ∧
    q.2.2 ∈ ((q.1.getD referenceCell : CompactCell) : Set Plane)}

theorem measurableSet_slotBoundaryTransportSupport :
    MeasurableSet slotBoundaryTransportSupport := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hS0 : MeasurableSet {q : Option CompactCell × Plane × Plane | q.1.isSome} :=
    measurable_fst measurableSet_slotIsSome
  have hS1 : MeasurableSet {q : Option CompactCell × Plane × Plane |
      q.2.1 ∈ frontier ((q.1.getD referenceCell : CompactCell) : Set Plane)} :=
    (hcellmap.prodMk (measurable_fst.comp measurable_snd)) measurableSet_cellFrontier
  have hS2 : MeasurableSet {q : Option CompactCell × Plane × Plane |
      q.2.2 ∈ ((q.1.getD referenceCell : CompactCell) : Set Plane)} :=
    (hcellmap.prodMk (measurable_snd.comp measurable_snd)) measurableSet_cellMem
  have hEq : slotBoundaryTransportSupport
      = {q : Option CompactCell × Plane × Plane | q.1.isSome} ∩
        ({q : Option CompactCell × Plane × Plane |
            q.2.1 ∈ frontier ((q.1.getD referenceCell : CompactCell) : Set Plane)} ∩
          {q : Option CompactCell × Plane × Plane |
            q.2.2 ∈ ((q.1.getD referenceCell : CompactCell) : Set Plane)}) :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact hS0.inter (hS1.inter hS2)

theorem measurable_slotBoundaryTransport :
    Measurable fun q : Option CompactCell × Plane × Plane =>
      slotBoundaryTransport q.1 q.2.1 q.2.2 := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hvol : Measurable fun q : Option CompactCell × Plane × Plane =>
      (volume ((q.1.getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
    (measurable_cellVolume.comp hcellmap).inv
  have hEq : (fun q : Option CompactCell × Plane × Plane =>
        slotBoundaryTransport q.1 q.2.1 q.2.2)
      = Set.indicator slotBoundaryTransportSupport
          (fun q => (volume ((q.1.getD referenceCell : CompactCell) : Set Plane))⁻¹) := by
    funext q
    obtain ⟨o, w, z⟩ := q
    cases o with
    | none =>
        have hmem : ((none : Option CompactCell), w, z) ∉ slotBoundaryTransportSupport := by
          intro h
          simpa using h.1
        rw [Set.indicator_of_notMem hmem]
        rfl
    | some K =>
        have hiff : ((some K : Option CompactCell), w, z) ∈ slotBoundaryTransportSupport
            ↔ w ∈ frontier (K : Set Plane) ∧ z ∈ (K : Set Plane) := by
          simp [slotBoundaryTransportSupport]
        by_cases hw : w ∈ frontier (K : Set Plane)
        · by_cases hz : z ∈ (K : Set Plane)
          · rw [Set.indicator_of_mem (hiff.mpr ⟨hw, hz⟩)]
            simp only [Option.getD_some]
            exact cellBoundaryTransport_of_mem K hw hz
          · rw [Set.indicator_of_notMem fun h => hz (hiff.mp h).2]
            exact cellBoundaryTransport_of_notMem_cell K w hz
        · rw [Set.indicator_of_notMem fun h => hw (hiff.mp h).1]
          exact cellBoundaryTransport_of_notMem_frontier K z hw
  rw [hEq]
  exact hvol.indicator measurableSet_slotBoundaryTransportSupport

/-- The manuscript's boundary transport, as a function on the full trace
environment space: `T(𝓗, w, z) = ∑_H 1_{w ∈ ∂H} 1_{z ∈ H} / a_H`. -/
noncomputable def boundaryTransport (p : Env × Plane × Plane) : ℝ≥0∞ :=
  ∑' n : ℕ, slotBoundaryTransport (p.1.val.1 n) p.2.1 p.2.2

theorem measurable_boundaryTransport : Measurable boundaryTransport := by
  have hslot : ∀ n : ℕ, Measurable fun p : Env × Plane × Plane =>
      slotBoundaryTransport (p.1.val.1 n) p.2.1 p.2.2 := by
    intro n
    have hmap : Measurable fun p : Env × Plane × Plane => (p.1.val.1 n, p.2) :=
      (((measurable_pi_apply n).comp
        (measurable_fst.comp measurable_inclusion)).comp measurable_fst).prodMk measurable_snd
    exact measurable_slotBoundaryTransport.comp hmap
  exact Measurable.ennreal_tsum hslot

/-- The slot sum is exactly the sum over the actual cells of the environment. -/
theorem boundaryTransport_eq_tsum_vertex (e : Env) (w z : Plane) :
    boundaryTransport (e, w, z)
      = ∑' v : Vertex e.val, cellBoundaryTransport ((decode e).cell v) w z := by
  have hsupp : Function.support (fun n : ℕ => slotBoundaryTransport (e.val.1 n) w z)
      ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    cases hcase : e.val.1 n with
    | none =>
        refine absurd (show (fun n : ℕ => slotBoundaryTransport (e.val.1 n) w z) n = 0 from ?_) hn
        simp [slotBoundaryTransport, hcase]
    | some K => simp [mem_setOf_eq, hcase]
  have hterm : ∀ v : Vertex e.val,
      slotBoundaryTransport (e.val.1 v.val) w z
        = cellBoundaryTransport ((decode e).cell v) w z := by
    intro v
    have hv : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
    rw [hv]
    rfl
  calc boundaryTransport (e, w, z)
      = ∑' n : ℕ, slotBoundaryTransport (e.val.1 n) w z := rfl
    _ = ∑' n : {n : ℕ | (e.val.1 n).isSome}, slotBoundaryTransport (e.val.1 n.val) w z :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' v : Vertex e.val, cellBoundaryTransport ((decode e).cell v) w z :=
        tsum_congr hterm

/-- Exact covariance of the boundary transport under the physical similarity
relation of the environment law. -/
theorem boundaryTransport_covariant (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    boundaryTransport (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * boundaryTransport (e, w, z) := by
  obtain ⟨relabel, hcell, -⟩ := hsim
  rw [boundaryTransport_eq_tsum_vertex, boundaryTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq relabel (fun v' : Vertex e'.val => cellBoundaryTransport ((decode e').cell v')
      (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [hcell v, cellBoundaryTransport_transformCell]

/-- The boundary transport as an actual `MassTransportKernel`: jointly
measurable on the full trace sigma algebra and exactly `(s ^ 2)⁻¹`-covariant. -/
noncomputable def boundaryTransportKernel : MassTransportKernel where
  toFun := boundaryTransport
  measurable_toFun := measurable_boundaryTransport
  covariant := fun s u hs e e' hsim w z => boundaryTransport_covariant s u hs e e' hsim w z

/-! ### Outgoing and incoming integrals -/

/-- Outgoing mass from a fixed source point through one cell is exactly the
indicator that the source lies on that cell's boundary. -/
theorem lintegral_cellBoundaryTransport_target (K : CompactCell) (w : Plane)
    (hpos : 0 < volume (K : Set Plane)) (hfin : volume (K : Set Plane) < ∞) :
    (∫⁻ z : Plane, cellBoundaryTransport K w z ∂volume)
      = Set.indicator (frontier (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w := by
  have hK : MeasurableSet (K : Set Plane) := K.isCompact.isClosed.measurableSet
  have hz : ∀ z : Plane, cellBoundaryTransport K w z
      = Set.indicator (K : Set Plane) (fun _ =>
          Set.indicator (frontier (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (K : Set Plane))⁻¹) z := by
    intro z
    by_cases hzK : z ∈ (K : Set Plane) <;>
      simp [cellBoundaryTransport, Set.indicator_apply, hzK, div_eq_mul_inv]
  simp_rw [hz]
  rw [lintegral_indicator_const hK, mul_assoc, ENNReal.inv_mul_cancel hpos.ne' hfin.ne, mul_one]

/-- Incoming mass at a fixed target point through one cell vanishes, because the
cell frontier is Lebesgue null. -/
theorem lintegral_cellBoundaryTransport_source (K : CompactCell) (z : Plane)
    (hfront : volume (frontier (K : Set Plane)) = 0) :
    (∫⁻ w : Plane, cellBoundaryTransport K w z ∂volume) = 0 := by
  have hF : MeasurableSet (frontier (K : Set Plane)) := isClosed_frontier.measurableSet
  have hw : ∀ w : Plane, cellBoundaryTransport K w z
      = Set.indicator (frontier (K : Set Plane)) (fun _ =>
          Set.indicator (K : Set Plane) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (K : Set Plane))⁻¹) w := by
    intro w
    by_cases hwF : w ∈ frontier (K : Set Plane) <;>
      simp [cellBoundaryTransport, Set.indicator_apply, hwF, div_eq_mul_inv]
  simp_rw [hw]
  rw [lintegral_indicator_const hF, hfront, mul_zero]

/-- The outgoing integral from the origin counts the cell boundaries through the
origin. -/
theorem lintegral_boundaryTransport_outgoing (e : Env) :
    (∫⁻ z : Plane, boundaryTransport (e, 0, z) ∂volume)
      = ∑' v : Vertex e.val,
          Set.indicator (frontier ((decode e).cell v : Set Plane))
            (fun _ => (1 : ℝ≥0∞)) 0 := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v : Vertex e.val, Measurable fun z : Plane =>
      cellBoundaryTransport ((decode e).cell v) 0 z := fun v =>
    measurable_cellBoundaryTransport_target ((decode e).cell v) 0
  calc (∫⁻ z : Plane, boundaryTransport (e, 0, z) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val,
          cellBoundaryTransport ((decode e).cell v) 0 z ∂volume :=
        lintegral_congr fun z => boundaryTransport_eq_tsum_vertex e 0 z
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane,
          cellBoundaryTransport ((decode e).cell v) 0 z ∂volume :=
        lintegral_tsum fun v => (hmeas v).aemeasurable
    _ = ∑' v : Vertex e.val, Set.indicator (frontier ((decode e).cell v : Set Plane))
          (fun _ => (1 : ℝ≥0∞)) 0 :=
        tsum_congr fun v => lintegral_cellBoundaryTransport_target _ _
          (cellVolume_pos_lt_top (decode e) hgeom v).1
          (cellVolume_pos_lt_top (decode e) hgeom v).2

/-- The incoming integral at the origin vanishes. -/
theorem lintegral_boundaryTransport_incoming (e : Env) :
    (∫⁻ z : Plane, boundaryTransport (e, z, 0) ∂volume) = 0 := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v : Vertex e.val, Measurable fun z : Plane =>
      cellBoundaryTransport ((decode e).cell v) z 0 := fun v =>
    measurable_cellBoundaryTransport_source ((decode e).cell v) 0
  calc (∫⁻ z : Plane, boundaryTransport (e, z, 0) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val,
          cellBoundaryTransport ((decode e).cell v) z 0 ∂volume :=
        lintegral_congr fun z => boundaryTransport_eq_tsum_vertex e z 0
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane,
          cellBoundaryTransport ((decode e).cell v) z 0 ∂volume :=
        lintegral_tsum fun v => (hmeas v).aemeasurable
    _ = 0 := by
        rw [show (fun v : Vertex e.val => ∫⁻ z : Plane,
            cellBoundaryTransport ((decode e).cell v) z 0 ∂volume) = fun _ => 0 from
          funext fun v => lintegral_cellBoundaryTransport_source _ _ (hgeom.2.2.1 v)]
        exact tsum_zero

/-! ### Almost surely the origin is on no cell boundary -/

/-- Mass transport, applied to the manuscript's boundary transport, forces the
number of cell boundaries through the origin to vanish almost surely. -/
theorem ae_notMem_boundaryMask_of_massTransport (ν : Measure Env) (hν : MassTransport ν) :
    ∀ᵐ e ∂ν, (0 : Plane) ∉ RootDensities.boundaryMask (decode e) := by
  have hkey : (∫⁻ e : Env, ∫⁻ z : Plane, boundaryTransport (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ z : Plane, boundaryTransport (e, z, 0) ∂volume ∂ν :=
    hν boundaryTransportKernel
  have hzero : (∫⁻ e : Env, ∫⁻ z : Plane, boundaryTransport (e, 0, z) ∂volume ∂ν) = 0 := by
    rw [hkey, show (fun e : Env => ∫⁻ z : Plane, boundaryTransport (e, z, 0) ∂volume)
      = fun _ => 0 from funext lintegral_boundaryTransport_incoming]
    exact lintegral_zero
  have hmeasout : Measurable fun e : Env =>
      ∫⁻ z : Plane, boundaryTransport (e, 0, z) ∂volume :=
    boundaryTransportKernel.measurable_outgoing.lintegral_prod_right'
  have hae := (lintegral_eq_zero_iff hmeasout).mp hzero
  -- The mask has two parts.  The frontier part is the transport argument above; the uncovered part
  -- is the manuscript's other transport, `Spatial/UncoveredRootTransport.lean`, whose hypothesis is
  -- supplied pointwise by the covering clause of `Geometry`.
  have hcov : ∀ᵐ e ∂ν, (0 : Plane) ∈ ⋃ v, ((decode e).cell v : Set Plane) :=
    ae_zero_mem_iUnion_cell ν hν
      (Filter.Eventually.of_forall fun e => volume_uncoveredSet (decode_geometry e))
  filter_upwards [hae, hcov] with e he hecov
  have he0 : (∫⁻ z : Plane, boundaryTransport (e, 0, z) ∂volume) = 0 := he
  rw [lintegral_boundaryTransport_outgoing e] at he0
  have hterm := ENNReal.tsum_eq_zero.mp he0
  intro hmem
  rcases hmem with hmemFrontier | hmemUncovered
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmemFrontier
    have hone := hterm v
    rw [Set.indicator_of_mem hv] at hone
    exact one_ne_zero hone
  · exact hmemUncovered hecov

end ReflectedGMS.Spatial
