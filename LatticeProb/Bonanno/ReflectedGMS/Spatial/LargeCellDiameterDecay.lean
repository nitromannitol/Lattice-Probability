/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.LargeCellDiameterDecay at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicApproximation
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts

/-!
# Large cells are sparse: `D_R < ∞` and `D_R / R → 0`

This module proves the manuscript's large-cell lemma (`s:lem:largecells`), the
geometric input of the log cutoff, the corrector and the covariance:
the maximal diameter `D_R` of a cell meeting the ball of radius `R` is finite and
sublinear in `R`.

`ReflectedGMS.Spatial.RootedMassBounds` supplies the mass-transport bound for the
*one-diameter* neighbourhood `N(H) = {z | infDist z H ≤ d_H}`.  One scale is not
enough: sublinearity needs, for every `ε > 0`, the finiteness of the family of
cells `H` with `infDist 0 H ≤ ε⁻¹ d_H`.  So the first half of this file redoes
the transport at the scaled neighbourhood

`N_k(H) = {z | infDist z H ≤ k d_H}`  (`cellScaledNeighborhood`),

which is again exactly similarity covariant (`infDist` and `diam` scale by the
same factor), giving an honest `EnvironmentLaws.MassTransportKernel` for every
`k ≥ 0` and hence

`E[#{H : 0 ∈ N_k(H)}] ≤ (k+1)² |B_1| E[d²_{H_0} / a_{H_0}]`.

The missing conductance factor flagged by `RootedMassBounds` is supplied here:
`Geometry` forces the vertex set to be nontrivial (a single compact cell cannot
cover the plane), so the connected cell graph gives every vertex a neighbour, and
AM–GM gives `π_H + π*_H ≥ c + c⁻¹ ≥ 2 ≥ 1`.  Local finiteness makes `π*` an
honest finite-support sum, so its single-term lower bound is available.  Hence
`d²/a ≤ (d²/a)(π + π*)` pointwise and the near-cell count is bounded by the
manuscript's (FE) moment.

The second half is deterministic.  If for every integer `n` only finitely many
cells satisfy `infDist 0 H ≤ n d_H`, then for every `ε > 0` and every `R`, a cell
meeting `B_R` with `d_H ≥ ε R` lies in that finite family for `n ≥ ε⁻¹`
(`infDist 0 H ≤ R ≤ n ε R ≤ n d_H`).  All other cells meeting `B_R` have
`d_H < ε R`, whence `D_R ≤ M ⊔ ε R` with `M` finite: `D_R < ∞` for each `R` and
`D_R / R → 0`.

The consumer `ReflectedGMS.Geometry.DiameterBlockIndex` uses exactly this decay
through `maxCellDiameter`; `maxCellDiameter_le_maxDiamHittingBall` is the bridge.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Pointwise

namespace ReflectedGMS.Spatial

open Code EnvironmentLaws

variable {V : Type*}

/-! ### The neighbourhood of a cell at `k` times its own scale -/

/-- `N_k(H) = {z | infDist z H ≤ k d_H}`: the points within `k` cell diameters of
the cell.  `k = 1` is `cellNeighborhood`. -/
def cellScaledNeighborhood (k : ℝ) (K : CompactCell) : Set Plane :=
  {z | Metric.infDist z (K : Set Plane) ≤ k * Metric.diam (K : Set Plane)}

theorem isClosed_cellScaledNeighborhoodMem (k : ℝ) :
    IsClosed {p : CompactCell × Plane | p.2 ∈ cellScaledNeighborhood k p.1} := by
  have hswap : Continuous fun p : CompactCell × Plane => (p.2, p.1) :=
    continuous_snd.prodMk continuous_fst
  have hlip : Continuous fun p : Plane × CompactCell => Metric.infDist p.1 (p.2 : Set Plane) :=
    (NonemptyCompacts.lipschitz_infDist (α := Plane)).continuous
  have hinf : Continuous fun p : CompactCell × Plane =>
      Metric.infDist p.2 (p.1 : Set Plane) := hlip.comp hswap
  have hdiam : Continuous fun p : CompactCell × Plane =>
      k * Metric.diam (p.1 : Set Plane) :=
    continuous_const.mul (continuous_cellDiam.comp continuous_fst)
  exact isClosed_le hinf hdiam

theorem measurableSet_cellScaledNeighborhoodMem (k : ℝ) :
    MeasurableSet {p : CompactCell × Plane | p.2 ∈ cellScaledNeighborhood k p.1} :=
  (isClosed_cellScaledNeighborhoodMem k).measurableSet

theorem isClosed_cellScaledNeighborhood (k : ℝ) (K : CompactCell) :
    IsClosed (cellScaledNeighborhood k K) :=
  isClosed_le (Metric.continuous_infDist_pt _) continuous_const

theorem measurableSet_cellScaledNeighborhood (k : ℝ) (K : CompactCell) :
    MeasurableSet (cellScaledNeighborhood k K) :=
  (isClosed_cellScaledNeighborhood k K).measurableSet

/-- A `k`-scaled neighbourhood sits in a ball of radius `(k+1) d_H` around any
point of the cell. -/
theorem cellScaledNeighborhood_subset_closedBall {k : ℝ} (hk : 0 ≤ k) {K : CompactCell}
    {x : Plane} (hx : x ∈ (K : Set Plane)) :
    cellScaledNeighborhood k K ⊆
      Metric.closedBall x ((k + 1) * Metric.diam (K : Set Plane)) := by
  intro z hz
  obtain ⟨y, hy, hdy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty z
  have h1 : dist z y ≤ k * Metric.diam (K : Set Plane) := by
    rw [← hdy]
    exact hz
  have h2 : dist y x ≤ Metric.diam (K : Set Plane) :=
    Metric.dist_le_diam_of_mem K.isCompact.isBounded hy hx
  have htri : dist z x ≤ dist z y + dist y x := dist_triangle z y x
  rw [Metric.mem_closedBall]
  nlinarith [h1, h2, htri]

/-- Lebesgue area of a `k`-scaled neighbourhood is at most `(k+1)² d_H²` times
the area of the unit ball. -/
theorem volume_cellScaledNeighborhood_le {k : ℝ} (hk : 0 ≤ k) (K : CompactCell) :
    volume (cellScaledNeighborhood k K)
      ≤ ENNReal.ofReal ((k + 1) ^ 2 * Metric.diam (K : Set Plane) ^ 2) *
          volume (Metric.ball (0 : Plane) 1) := by
  obtain ⟨x, hx⟩ := K.nonempty
  have hdiam : (0 : ℝ) ≤ Metric.diam (K : Set Plane) := Metric.diam_nonneg
  have hr : (0 : ℝ) ≤ (k + 1) * Metric.diam (K : Set Plane) := by nlinarith
  have hball := Measure.addHaar_closedBall (volume : Measure Plane) x hr
  rw [finrank_euclideanSpace_fin] at hball
  calc volume (cellScaledNeighborhood k K)
      ≤ volume (Metric.closedBall x ((k + 1) * Metric.diam (K : Set Plane))) :=
        measure_mono (cellScaledNeighborhood_subset_closedBall hk hx)
    _ = ENNReal.ofReal (((k + 1) * Metric.diam (K : Set Plane)) ^ 2) *
          volume (Metric.ball (0 : Plane) 1) := hball
    _ = ENNReal.ofReal ((k + 1) ^ 2 * Metric.diam (K : Set Plane) ^ 2) *
          volume (Metric.ball (0 : Plane) 1) := by
        rw [mul_pow]

/-- The scaled cell neighbourhood is exactly similarity covariant. -/
theorem mem_cellScaledNeighborhood_transformCell_iff (k s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (z : Plane) :
    positiveSimilarity s u z ∈ cellScaledNeighborhood k (transformCell s u hs K)
      ↔ z ∈ cellScaledNeighborhood k K := by
  have hcoe : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarity s u '' (K : Set Plane) := coe_transformCell s u hs K
  simp only [cellScaledNeighborhood, mem_setOf_eq, hcoe,
    infDist_image_positiveSimilarity s u hs, diam_image_positiveSimilarity s u hs]
  constructor
  · intro h
    have h' : s * Metric.infDist z (K : Set Plane)
        ≤ s * (k * Metric.diam (K : Set Plane)) := by nlinarith [h]
    exact le_of_mul_le_mul_left h' hs
  · intro h
    have h' : s * Metric.infDist z (K : Set Plane)
        ≤ s * (k * Metric.diam (K : Set Plane)) := mul_le_mul_of_nonneg_left h hs.le
    nlinarith [h']

/-! ### The scaled neighbourhood transport of a single cell -/

/-- The contribution of one cell to the `k`-scaled transport
`T_k(𝓗, w, z) = ∑_H 1_{w ∈ int H} 1_{z ∈ N_k(H)} / a_H`. -/
noncomputable def cellScaledNeighborhoodTransport (k : ℝ) (K : CompactCell) (w z : Plane) :
    ℝ≥0∞ :=
  Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
      Set.indicator (cellScaledNeighborhood k K) (fun _ => (1 : ℝ≥0∞)) z /
    volume (K : Set Plane)

theorem cellScaledNeighborhoodTransport_of_mem (k : ℝ) (K : CompactCell) {w z : Plane}
    (hw : w ∈ interior (K : Set Plane)) (hz : z ∈ cellScaledNeighborhood k K) :
    cellScaledNeighborhoodTransport k K w z = (volume (K : Set Plane))⁻¹ := by
  simp [cellScaledNeighborhoodTransport, Set.indicator_apply, hw, hz]

theorem cellScaledNeighborhoodTransport_of_notMem_interior (k : ℝ) (K : CompactCell)
    {w : Plane} (z : Plane) (hw : w ∉ interior (K : Set Plane)) :
    cellScaledNeighborhoodTransport k K w z = 0 := by
  simp [cellScaledNeighborhoodTransport, Set.indicator_apply, hw]

theorem cellScaledNeighborhoodTransport_of_notMem_neighborhood (k : ℝ) (K : CompactCell)
    (w : Plane) {z : Plane} (hz : z ∉ cellScaledNeighborhood k K) :
    cellScaledNeighborhoodTransport k K w z = 0 := by
  simp [cellScaledNeighborhoodTransport, Set.indicator_apply, hz]

theorem measurable_cellScaledNeighborhoodTransport_target (k : ℝ) (K : CompactCell)
    (w : Plane) :
    Measurable fun z : Plane => cellScaledNeighborhoodTransport k K w z := by
  have hEq : (fun z : Plane => cellScaledNeighborhoodTransport k K w z)
      = fun z : Plane =>
        Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (K : Set Plane))⁻¹ *
          Set.indicator (cellScaledNeighborhood k K) (fun _ => (1 : ℝ≥0∞)) z := by
    funext z
    rw [cellScaledNeighborhoodTransport, div_eq_mul_inv]
    ring
  rw [hEq]
  exact measurable_const.mul
    (measurable_const.indicator (measurableSet_cellScaledNeighborhood k K))

theorem measurable_cellScaledNeighborhoodTransport_source (k : ℝ) (K : CompactCell)
    (z : Plane) :
    Measurable fun w : Plane => cellScaledNeighborhoodTransport k K w z := by
  have hEq : (fun w : Plane => cellScaledNeighborhoodTransport k K w z)
      = fun w : Plane =>
        Set.indicator (cellScaledNeighborhood k K) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (K : Set Plane))⁻¹ *
          Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w := by
    funext w
    rw [cellScaledNeighborhoodTransport, div_eq_mul_inv]
    ring
  rw [hEq]
  exact measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet)

/-- Degree `-2` covariance of the scaled cell transport. -/
theorem cellScaledNeighborhoodTransport_transformCell (k s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (w z : Plane) :
    cellScaledNeighborhoodTransport k (transformCell s u hs K) (positiveSimilarity s u w)
        (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * cellScaledNeighborhoodTransport k K w z := by
  have hcoe : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarity s u '' (K : Set Plane) := coe_transformCell s u hs K
  have hindInt : Set.indicator (interior ((transformCell s u hs K : CompactCell) : Set Plane))
        (fun _ => (1 : ℝ≥0∞)) (positiveSimilarity s u w)
      = Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w :=
    indicator_one_congr_of_iff (mem_interior_transformCell_iff s u hs K w)
  have hindNbhd : Set.indicator (cellScaledNeighborhood k (transformCell s u hs K))
        (fun _ => (1 : ℝ≥0∞)) (positiveSimilarity s u z)
      = Set.indicator (cellScaledNeighborhood k K) (fun _ => (1 : ℝ≥0∞)) z :=
    indicator_one_congr_of_iff (mem_cellScaledNeighborhood_transformCell_iff k s u hs K z)
  have hvol : volume ((transformCell s u hs K : CompactCell) : Set Plane)
      = ENNReal.ofReal (s ^ 2) * volume (K : Set Plane) := by
    rw [hcoe]
    exact volume_image_positiveSimilarity s u (K : Set Plane)
  have hspos : (0 : ℝ) < s ^ 2 := by positivity
  have hinv : (ENNReal.ofReal (s ^ 2) * volume (K : Set Plane))⁻¹
      = ENNReal.ofReal ((s ^ 2)⁻¹) * (volume (K : Set Plane))⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (by simpa using hspos.ne'))
      (Or.inl (by simp [ENNReal.ofReal_ne_top])), ENNReal.ofReal_inv_of_pos hspos]
  rw [cellScaledNeighborhoodTransport, cellScaledNeighborhoodTransport, hindInt, hindNbhd,
    hvol, div_eq_mul_inv, div_eq_mul_inv, hinv]
  ring

/-! ### Slot and environment level scaled transport -/

/-- The scaled transport of one code slot; absent slots transport nothing. -/
noncomputable def slotScaledNeighborhoodTransport (k : ℝ) (o : Option CompactCell)
    (w z : Plane) : ℝ≥0∞ :=
  o.elim 0 fun K => cellScaledNeighborhoodTransport k K w z

def slotScaledNeighborhoodTransportSupport (k : ℝ) :
    Set (Option CompactCell × Plane × Plane) :=
  {q | q.1.isSome ∧ q.2.1 ∈ interior ((q.1.getD referenceCell : CompactCell) : Set Plane) ∧
    q.2.2 ∈ cellScaledNeighborhood k (q.1.getD referenceCell : CompactCell)}

theorem measurableSet_slotScaledNeighborhoodTransportSupport (k : ℝ) :
    MeasurableSet (slotScaledNeighborhoodTransportSupport k) := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hS0 : MeasurableSet {q : Option CompactCell × Plane × Plane | q.1.isSome} :=
    measurable_fst measurableSet_slotIsSome
  have hS1 : MeasurableSet {q : Option CompactCell × Plane × Plane |
      q.2.1 ∈ interior ((q.1.getD referenceCell : CompactCell) : Set Plane)} :=
    (hcellmap.prodMk (measurable_fst.comp measurable_snd)) measurableSet_cellInterior
  have hS2 : MeasurableSet {q : Option CompactCell × Plane × Plane |
      q.2.2 ∈ cellScaledNeighborhood k (q.1.getD referenceCell : CompactCell)} :=
    (hcellmap.prodMk (measurable_snd.comp measurable_snd))
      (measurableSet_cellScaledNeighborhoodMem k)
  have hEq : slotScaledNeighborhoodTransportSupport k
      = {q : Option CompactCell × Plane × Plane | q.1.isSome} ∩
        ({q : Option CompactCell × Plane × Plane |
            q.2.1 ∈ interior ((q.1.getD referenceCell : CompactCell) : Set Plane)} ∩
          {q : Option CompactCell × Plane × Plane |
            q.2.2 ∈ cellScaledNeighborhood k (q.1.getD referenceCell : CompactCell)}) :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact hS0.inter (hS1.inter hS2)

theorem measurable_slotScaledNeighborhoodTransport (k : ℝ) :
    Measurable fun q : Option CompactCell × Plane × Plane =>
      slotScaledNeighborhoodTransport k q.1 q.2.1 q.2.2 := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hvol : Measurable fun q : Option CompactCell × Plane × Plane =>
      (volume ((q.1.getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
    (measurable_cellVolume.comp hcellmap).inv
  have hEq : (fun q : Option CompactCell × Plane × Plane =>
        slotScaledNeighborhoodTransport k q.1 q.2.1 q.2.2)
      = Set.indicator (slotScaledNeighborhoodTransportSupport k)
          (fun q => (volume ((q.1.getD referenceCell : CompactCell) : Set Plane))⁻¹) := by
    funext q
    obtain ⟨o, w, z⟩ := q
    cases o with
    | none =>
        have hmem : ((none : Option CompactCell), w, z)
            ∉ slotScaledNeighborhoodTransportSupport k := by
          intro h
          simpa using h.1
        rw [Set.indicator_of_notMem hmem]
        rfl
    | some K =>
        have hiff : ((some K : Option CompactCell), w, z)
            ∈ slotScaledNeighborhoodTransportSupport k
            ↔ w ∈ interior (K : Set Plane) ∧ z ∈ cellScaledNeighborhood k K := by
          simp [slotScaledNeighborhoodTransportSupport]
        by_cases hw : w ∈ interior (K : Set Plane)
        · by_cases hz : z ∈ cellScaledNeighborhood k K
          · rw [Set.indicator_of_mem (hiff.mpr ⟨hw, hz⟩)]
            simp only [Option.getD_some]
            exact cellScaledNeighborhoodTransport_of_mem k K hw hz
          · rw [Set.indicator_of_notMem fun h => hz (hiff.mp h).2]
            exact cellScaledNeighborhoodTransport_of_notMem_neighborhood k K w hz
        · rw [Set.indicator_of_notMem fun h => hw (hiff.mp h).1]
          exact cellScaledNeighborhoodTransport_of_notMem_interior k K z hw
  rw [hEq]
  exact hvol.indicator (measurableSet_slotScaledNeighborhoodTransportSupport k)

/-- The `k`-scaled neighbourhood transport on the full trace environment space. -/
noncomputable def scaledNeighborhoodTransport (k : ℝ) (p : Env × Plane × Plane) : ℝ≥0∞ :=
  ∑' n : ℕ, slotScaledNeighborhoodTransport k (p.1.val.1 n) p.2.1 p.2.2

theorem measurable_scaledNeighborhoodTransport (k : ℝ) :
    Measurable (scaledNeighborhoodTransport k) := by
  have hslot : ∀ n : ℕ, Measurable fun p : Env × Plane × Plane =>
      slotScaledNeighborhoodTransport k (p.1.val.1 n) p.2.1 p.2.2 := by
    intro n
    have hmap : Measurable fun p : Env × Plane × Plane => (p.1.val.1 n, p.2) :=
      (((measurable_pi_apply n).comp
        (measurable_fst.comp measurable_inclusion)).comp measurable_fst).prodMk measurable_snd
    exact (measurable_slotScaledNeighborhoodTransport k).comp hmap
  exact Measurable.ennreal_tsum hslot

theorem scaledNeighborhoodTransport_eq_tsum_vertex (k : ℝ) (e : Env) (w z : Plane) :
    scaledNeighborhoodTransport k (e, w, z)
      = ∑' v : Vertex e.val, cellScaledNeighborhoodTransport k ((decode e).cell v) w z := by
  have hsupp : Function.support
      (fun n : ℕ => slotScaledNeighborhoodTransport k (e.val.1 n) w z)
      ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    cases hcase : e.val.1 n with
    | none =>
        refine absurd (show (fun n : ℕ => slotScaledNeighborhoodTransport k (e.val.1 n) w z) n
          = 0 from ?_) hn
        simp [slotScaledNeighborhoodTransport, hcase]
    | some K => simp [mem_setOf_eq, hcase]
  have hterm : ∀ v : Vertex e.val,
      slotScaledNeighborhoodTransport k (e.val.1 v.val) w z
        = cellScaledNeighborhoodTransport k ((decode e).cell v) w z := by
    intro v
    have hv : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
    rw [hv]
    rfl
  calc scaledNeighborhoodTransport k (e, w, z)
      = ∑' n : ℕ, slotScaledNeighborhoodTransport k (e.val.1 n) w z := rfl
    _ = ∑' n : {n : ℕ | (e.val.1 n).isSome},
          slotScaledNeighborhoodTransport k (e.val.1 n.val) w z :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' v : Vertex e.val,
          cellScaledNeighborhoodTransport k ((decode e).cell v) w z := tsum_congr hterm

theorem scaledNeighborhoodTransport_covariant (k s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    scaledNeighborhoodTransport k (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * scaledNeighborhoodTransport k (e, w, z) := by
  obtain ⟨relabel, hcell, -⟩ := hsim
  rw [scaledNeighborhoodTransport_eq_tsum_vertex, scaledNeighborhoodTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq relabel (fun v' : Vertex e'.val =>
      cellScaledNeighborhoodTransport k ((decode e').cell v')
        (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [hcell v, cellScaledNeighborhoodTransport_transformCell]

/-- The `k`-scaled neighbourhood transport as an actual `MassTransportKernel`. -/
noncomputable def scaledNeighborhoodTransportKernel (k : ℝ) : MassTransportKernel where
  toFun := scaledNeighborhoodTransport k
  measurable_toFun := measurable_scaledNeighborhoodTransport k
  covariant := fun s u hs e e' hsim w z =>
    scaledNeighborhoodTransport_covariant k s u hs e e' hsim w z

/-! ### Outgoing and incoming integrals of the scaled transport -/

theorem lintegral_cellScaledNeighborhoodTransport_target (k : ℝ) (K : CompactCell) (w : Plane) :
    (∫⁻ z : Plane, cellScaledNeighborhoodTransport k K w z ∂volume)
      = Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
          (volume (cellScaledNeighborhood k K) / volume (K : Set Plane)) := by
  have hN : MeasurableSet (cellScaledNeighborhood k K) := measurableSet_cellScaledNeighborhood k K
  have hz : ∀ z : Plane, cellScaledNeighborhoodTransport k K w z
      = Set.indicator (cellScaledNeighborhood k K) (fun _ =>
          Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (K : Set Plane))⁻¹) z := by
    intro z
    by_cases hzN : z ∈ cellScaledNeighborhood k K <;>
      simp [cellScaledNeighborhoodTransport, Set.indicator_apply, hzN, div_eq_mul_inv]
  simp_rw [hz]
  rw [lintegral_indicator_const hN, div_eq_mul_inv]
  ring

theorem lintegral_cellScaledNeighborhoodTransport_source (k : ℝ) (K : CompactCell) (z : Plane)
    (hfront : volume (frontier (K : Set Plane)) = 0)
    (hpos : 0 < volume (K : Set Plane)) (hfin : volume (K : Set Plane) < ∞) :
    (∫⁻ w : Plane, cellScaledNeighborhoodTransport k K w z ∂volume)
      = Set.indicator (cellScaledNeighborhood k K) (fun _ => (1 : ℝ≥0∞)) z := by
  have hI : MeasurableSet (interior (K : Set Plane)) := isOpen_interior.measurableSet
  have hw : ∀ w : Plane, cellScaledNeighborhoodTransport k K w z
      = Set.indicator (interior (K : Set Plane)) (fun _ =>
          Set.indicator (cellScaledNeighborhood k K) (fun _ => (1 : ℝ≥0∞)) z *
            (volume (K : Set Plane))⁻¹) w := by
    intro w
    by_cases hwI : w ∈ interior (K : Set Plane) <;>
      simp [cellScaledNeighborhoodTransport, Set.indicator_apply, hwI, div_eq_mul_inv]
  simp_rw [hw]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfront, mul_assoc,
    ENNReal.inv_mul_cancel hpos.ne' hfin.ne, mul_one]

theorem lintegral_scaledNeighborhoodTransport_outgoing (k : ℝ) (e : Env) (w : Plane) :
    (∫⁻ z : Plane, scaledNeighborhoodTransport k (e, w, z) ∂volume)
      = ∑' v : Vertex e.val,
          Set.indicator (interior ((decode e).cell v : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (cellScaledNeighborhood k ((decode e).cell v)) /
              volume ((decode e).cell v : Set Plane)) := by
  have hmeas : ∀ v : Vertex e.val, Measurable fun z : Plane =>
      cellScaledNeighborhoodTransport k ((decode e).cell v) w z := fun v =>
    measurable_cellScaledNeighborhoodTransport_target k ((decode e).cell v) w
  calc (∫⁻ z : Plane, scaledNeighborhoodTransport k (e, w, z) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val,
          cellScaledNeighborhoodTransport k ((decode e).cell v) w z ∂volume :=
        lintegral_congr fun z => scaledNeighborhoodTransport_eq_tsum_vertex k e w z
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane,
          cellScaledNeighborhoodTransport k ((decode e).cell v) w z ∂volume :=
        lintegral_tsum fun v => (hmeas v).aemeasurable
    _ = ∑' v : Vertex e.val,
          Set.indicator (interior ((decode e).cell v : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (cellScaledNeighborhood k ((decode e).cell v)) /
              volume ((decode e).cell v : Set Plane)) :=
        tsum_congr fun v => lintegral_cellScaledNeighborhoodTransport_target _ _ _

theorem lintegral_scaledNeighborhoodTransport_incoming (k : ℝ) (e : Env) (z : Plane) :
    (∫⁻ w : Plane, scaledNeighborhoodTransport k (e, w, z) ∂volume)
      = ∑' v : Vertex e.val,
          Set.indicator (cellScaledNeighborhood k ((decode e).cell v))
            (fun _ => (1 : ℝ≥0∞)) z := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v : Vertex e.val, Measurable fun w : Plane =>
      cellScaledNeighborhoodTransport k ((decode e).cell v) w z := fun v =>
    measurable_cellScaledNeighborhoodTransport_source k ((decode e).cell v) z
  calc (∫⁻ w : Plane, scaledNeighborhoodTransport k (e, w, z) ∂volume)
      = ∫⁻ w : Plane, ∑' v : Vertex e.val,
          cellScaledNeighborhoodTransport k ((decode e).cell v) w z ∂volume :=
        lintegral_congr fun w => scaledNeighborhoodTransport_eq_tsum_vertex k e w z
    _ = ∑' v : Vertex e.val, ∫⁻ w : Plane,
          cellScaledNeighborhoodTransport k ((decode e).cell v) w z ∂volume :=
        lintegral_tsum fun v => (hmeas v).aemeasurable
    _ = ∑' v : Vertex e.val,
          Set.indicator (cellScaledNeighborhood k ((decode e).cell v))
            (fun _ => (1 : ℝ≥0∞)) z :=
        tsum_congr fun v => lintegral_cellScaledNeighborhoodTransport_source _ _ _
          (hgeom.2.2.1 v) (cellVolume_pos_lt_top (decode e) hgeom v).1
          (cellVolume_pos_lt_top (decode e) hgeom v).2

/-! ### The scaled near-cell count -/

/-- The number of cells that are within `k` of their own diameter of a point. -/
noncomputable def scaledNearCellCount (k : ℝ) (F : IndexedCells V) (z : Plane) : ℝ≥0∞ :=
  ∑' v : V, Set.indicator (cellScaledNeighborhood k (F.cell v)) (fun _ => (1 : ℝ≥0∞)) z

/-- The boundary-masked scaled-neighbourhood-to-area ratio of the rooted cell. -/
noncomputable def rootedScaledNeighborhoodAreaRatio (k : ℝ) (F : IndexedCells V) (z : Plane) :
    ℝ≥0∞ :=
  (RootDensities.rootAt F z).elim 0 fun v =>
    volume (cellScaledNeighborhood k (F.cell v)) / volume (F.cell v : Set Plane)

theorem lintegral_scaledNeighborhoodTransport_incoming_eq_count (k : ℝ) (e : Env) :
    (∫⁻ w : Plane, scaledNeighborhoodTransport k (e, w, 0) ∂volume)
      = scaledNearCellCount k (decode e) 0 :=
  lintegral_scaledNeighborhoodTransport_incoming k e 0

theorem lintegral_scaledNeighborhoodTransport_outgoing_eq_rooted (k : ℝ) (e : Env)
    (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    (∫⁻ z : Plane, scaledNeighborhoodTransport k (e, 0, z) ∂volume)
      = rootedScaledNeighborhoodAreaRatio k (decode e) 0 := by
  have hgeom := decode_geometry e
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom he
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom he
  rw [lintegral_scaledNeighborhoodTransport_outgoing k e 0]
  rw [tsum_eq_single v₀ ?_]
  · rw [Set.indicator_of_mem hint, one_mul]
    simp [rootedScaledNeighborhoodAreaRatio, hv₀]
  · intro v hv
    have hnot : (0 : Plane) ∉ interior ((decode e).cell v : Set Plane) := by
      intro hmem
      exact hv (huniq.unique hmem hint)
    rw [Set.indicator_of_notMem hnot, zero_mul]

/-- Mass transport at the scale `k`: the expected number of cells whose
`k`-neighbourhood contains the origin is the expected rooted ratio. -/
theorem lintegral_scaledNearCellCount_eq_rootedRatio (k : ℝ) (ν : Measure Env)
    (hν : MassTransport ν) :
    (∫⁻ e : Env, scaledNearCellCount k (decode e) 0 ∂ν)
      = ∫⁻ e : Env, rootedScaledNeighborhoodAreaRatio k (decode e) 0 ∂ν := by
  have hmt : (∫⁻ e : Env, ∫⁻ z : Plane, scaledNeighborhoodTransport k (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ z : Plane, scaledNeighborhoodTransport k (e, z, 0) ∂volume ∂ν :=
    hν (scaledNeighborhoodTransportKernel k)
  have hout : (∫⁻ e : Env, ∫⁻ z : Plane, scaledNeighborhoodTransport k (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, rootedScaledNeighborhoodAreaRatio k (decode e) 0 ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_notMem_boundaryMask_of_massTransport ν hν] with e he
    exact lintegral_scaledNeighborhoodTransport_outgoing_eq_rooted k e he
  have hin : (∫⁻ e : Env, ∫⁻ z : Plane, scaledNeighborhoodTransport k (e, z, 0) ∂volume ∂ν)
      = ∫⁻ e : Env, scaledNearCellCount k (decode e) 0 ∂ν :=
    lintegral_congr fun e => lintegral_scaledNeighborhoodTransport_incoming_eq_count k e
  exact hin.symm.trans (hmt.symm.trans hout)

/-- The rooted scaled ratio is dominated by the rooted diameter density. -/
theorem rootedScaledNeighborhoodAreaRatio_le {k : ℝ} (hk : 0 ≤ k) (F : IndexedCells V)
    (z : Plane) :
    rootedScaledNeighborhoodAreaRatio k F z
      ≤ ENNReal.ofReal ((k + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) *
          rootedDiamSqAreaDensity F z := by
  cases hroot : RootDensities.rootAt F z with
  | none => simp [rootedScaledNeighborhoodAreaRatio, hroot]
  | some v =>
      simp only [rootedScaledNeighborhoodAreaRatio, rootedDiamSqAreaDensity, hroot, Option.elim]
      calc volume (cellScaledNeighborhood k (F.cell v)) / volume (F.cell v : Set Plane)
          ≤ (ENNReal.ofReal ((k + 1) ^ 2 * Metric.diam (F.cell v : Set Plane) ^ 2) *
              volume (Metric.ball (0 : Plane) 1)) / volume (F.cell v : Set Plane) :=
            ENNReal.div_le_div_right (volume_cellScaledNeighborhood_le hk (F.cell v)) _
        _ = ENNReal.ofReal ((k + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) *
              (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
                volume (F.cell v : Set Plane)) := by
            rw [ENNReal.ofReal_mul (by positivity), div_eq_mul_inv, div_eq_mul_inv]
            ring

/-! ### The conductance factor: `π_H + π*_H ≥ 2` -/

/-- A single compact cell cannot cover all but an `H¹`-null set of the plane, so a
valid cell family has at least two cells: the uncovered set has dense complement, so a
closed set containing that complement is the whole plane. -/
theorem nontrivial_of_geometry [Countable V] (F : IndexedCells V) (hF : Geometry F) :
    Nontrivial V := by
  by_contra hcon
  have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hcon
  rcases isEmpty_or_nonempty V with hV | hV
  · obtain ⟨_, _, v, _⟩ :=
      exists_mem_cell_of_isOpen hF (U := (Set.univ : Set Plane)) isOpen_univ
        ⟨(0 : Plane), Set.mem_univ _⟩
    exact (IsEmpty.false v).elim
  · obtain ⟨v₀⟩ := hV
    have hsub2 : (Set.univ : Set Plane) ⊆ (F.cell v₀ : Set Plane) := by
      refine subset_of_isClosed_of_inter_compl_subset hF isOpen_univ
        (F.cell v₀).isCompact.isClosed ?_
      rintro z ⟨-, hz⟩
      obtain ⟨v, hv⟩ := exists_mem_cell_of_notMem_uncoveredSet hz
      have hvv : v = v₀ := Subsingleton.elim v v₀
      rw [← hvv]
      exact hv
    have hcpt : IsCompact (Set.univ : Set Plane) :=
      (F.cell v₀).isCompact.of_isClosed_subset isClosed_univ hsub2
    exact absurd hcpt NoncompactSpace.noncompact_univ

/-- Local finiteness makes the reciprocal conductance sum a finite-support sum. -/
theorem summable_inv_conductance [Countable V] (F : IndexedCells V) (hF : Geometry F) (v : V) :
    Summable fun w : V => (F.graph.c v w)⁻¹ := by
  have hfin : (F.graph.toSimpleGraph.neighborSet v).Finite := hF.2.2.2.2.2.2.1 v
  refine summable_of_ne_finset_zero (s := hfin.toFinset) ?_
  intro w hw
  have hnadj : ¬ (0 : ℝ) < F.graph.c v w := by
    intro hadj
    exact hw (hfin.mem_toFinset.mpr hadj)
  have hc : F.graph.c v w = 0 := le_antisymm (not_lt.mp hnadj) (F.graph.c_nonneg v w)
  rw [hc, inv_zero]

/-- The manuscript's AM–GM bound: every vertex of a connected cell graph has a
neighbour, and `c + c⁻¹ ≥ 2`. -/
theorem two_le_pi_add_piStar [Countable V] [Nontrivial V] (F : IndexedCells V)
    (hF : Geometry F) (v : V) :
    2 ≤ RootDensities.pi F v + RootDensities.piStar F v := by
  obtain ⟨w, hw⟩ := F.graph.exists_adj_of_connected (hF.2.2.2.2.2.1) v
  have hcpos : 0 < F.graph.c v w := hw
  have h1 : F.graph.c v w ≤ RootDensities.pi F v := F.graph.c_le_pi v w
  have h2 : (F.graph.c v w)⁻¹ ≤ RootDensities.piStar F v :=
    (summable_inv_conductance F hF v).le_tsum w
      fun b _ => inv_nonneg.mpr (F.graph.c_nonneg v b)
  have hinv : F.graph.c v w * (F.graph.c v w)⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
  have hkey : (2 : ℝ) ≤ F.graph.c v w + (F.graph.c v w)⁻¹ := by
    nlinarith [sq_nonneg (F.graph.c v w - 1), hcpos, hinv]
  linarith

theorem piStar_nonneg (F : IndexedCells V) (v : V) : 0 ≤ RootDensities.piStar F v :=
  tsum_nonneg fun w => inv_nonneg.mpr (F.graph.c_nonneg v w)

/-- The missing pointwise step of `RootedMassBounds`: the rooted diameter density
is dominated by the manuscript's (FE) integrand. -/
theorem rootedDiamSqAreaDensity_le_rootedFiniteEnergyDensity [Countable V] [Nontrivial V]
    (F : IndexedCells V) (hF : Geometry F) (z : Plane) :
    rootedDiamSqAreaDensity F z ≤ RootDensities.rootedFiniteEnergyDensity F z := by
  rw [rootedDiamSqAreaDensity_eq_ofReal_cellArea F hF z]
  cases hroot : RootDensities.rootAt F z with
  | none => simp [RootDensities.rootedFiniteEnergyDensity, hroot]
  | some v =>
      simp only [RootDensities.rootedFiniteEnergyDensity, RootDensities.finiteEnergyDensity,
        hroot, Option.elim]
      have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (RootDensities.pi F v)
          + ENNReal.ofReal (RootDensities.piStar F v) := by
        have hpi : 0 ≤ RootDensities.pi F v := F.graph.pi_nonneg v
        have hpis : 0 ≤ RootDensities.piStar F v := piStar_nonneg F v
        have h2 := two_le_pi_add_piStar F hF v
        rw [← ENNReal.ofReal_add hpi hpis]
        calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
          _ ≤ ENNReal.ofReal (RootDensities.pi F v + RootDensities.piStar F v) :=
              ENNReal.ofReal_le_ofReal (by linarith)
      calc ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
            ENNReal.ofReal (StatementIngredients.cellArea F v)
          = ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
              ENNReal.ofReal (StatementIngredients.cellArea F v) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
              ENNReal.ofReal (StatementIngredients.cellArea F v) *
                (ENNReal.ofReal (RootDensities.pi F v)
                  + ENNReal.ofReal (RootDensities.piStar F v)) := mul_le_mul' le_rfl hone

/-! ### The near-cell count is controlled by the (FE) moment -/

/-- Large-cell control at every scale `k`: under mass transport the expected
number of cells whose `k`-neighbourhood contains the origin is bounded by the
manuscript's finite-energy moment. -/
theorem lintegral_scaledNearCellCount_le_rootedFiniteEnergyMoment {k : ℝ} (hk : 0 ≤ k)
    (ν : Measure Env) (hν : MassTransport ν) :
    (∫⁻ e : Env, scaledNearCellCount k (decode e) 0 ∂ν)
      ≤ ENNReal.ofReal ((k + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) *
          ∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν := by
  have hconst : ENNReal.ofReal ((k + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  rw [lintegral_scaledNearCellCount_eq_rootedRatio k ν hν]
  calc (∫⁻ e : Env, rootedScaledNeighborhoodAreaRatio k (decode e) 0 ∂ν)
      ≤ ∫⁻ e : Env, ENNReal.ofReal ((k + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) *
          RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν := by
        refine lintegral_mono fun e => ?_
        haveI : Nontrivial (Vertex e.val) :=
          nontrivial_of_geometry (decode e) (decode_geometry e)
        refine le_trans (rootedScaledNeighborhoodAreaRatio_le hk _ _) ?_
        exact mul_le_mul' le_rfl
          (rootedDiamSqAreaDensity_le_rootedFiniteEnergyDensity (decode e)
            (decode_geometry e) 0)
    _ = ENNReal.ofReal ((k + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) *
          ∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν :=
        lintegral_const_mul' _ _ hconst

/-- A finite count really is a finite family of cells. -/
theorem finite_of_scaledNearCellCount_ne_top (k : ℝ) (F : IndexedCells V) (z : Plane)
    (h : scaledNearCellCount k F z ≠ ∞) :
    {v : V | z ∈ cellScaledNeighborhood k (F.cell v)}.Finite := by
  by_contra hcon
  have hinf : {v : V | z ∈ cellScaledNeighborhood k (F.cell v)}.Infinite := hcon
  haveI : Infinite {v : V | z ∈ cellScaledNeighborhood k (F.cell v)} := hinf.to_subtype
  have hsupp : Function.support
      (fun v : V =>
        Set.indicator (cellScaledNeighborhood k (F.cell v)) (fun _ => (1 : ℝ≥0∞)) z)
      ⊆ {v : V | z ∈ cellScaledNeighborhood k (F.cell v)} := by
    intro v hv
    by_contra hz
    have hz' : z ∉ cellScaledNeighborhood k (F.cell v) := hz
    exact hv (Set.indicator_of_notMem hz' _)
  refine h ?_
  calc scaledNearCellCount k F z
      = ∑' v : {v : V | z ∈ cellScaledNeighborhood k (F.cell v)},
          Set.indicator (cellScaledNeighborhood k (F.cell v.1)) (fun _ => (1 : ℝ≥0∞)) z :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' _ : {v : V | z ∈ cellScaledNeighborhood k (F.cell v)}, (1 : ℝ≥0∞) := by
        refine tsum_congr fun v => ?_
        have hmem : z ∈ cellScaledNeighborhood k (F.cell v.1) := v.2
        exact Set.indicator_of_mem hmem _
    _ = ∞ := ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- Under mass transport and a finite (FE) moment, almost every environment has,
at every integer scale `n`, only finitely many cells whose `n`-neighbourhood
contains the origin. -/
theorem ae_finite_scaledNear_of_finiteEnergyMoment (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, ∀ n : ℕ,
      {v : Vertex e.val |
        (0 : Plane) ∈ cellScaledNeighborhood (n : ℝ) ((decode e).cell v)}.Finite := by
  rw [ae_all_iff]
  intro n
  have hk : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmeas : Measurable fun e : Env => scaledNearCellCount (n : ℝ) (decode e) 0 := by
    have hinc : Measurable fun e : Env =>
        ∫⁻ z : Plane, scaledNeighborhoodTransport (n : ℝ) (e, z, 0) ∂volume :=
      (scaledNeighborhoodTransportKernel (n : ℝ)).measurable_incoming.lintegral_prod_right'
    have hEq : (fun e : Env => ∫⁻ z : Plane,
          scaledNeighborhoodTransport (n : ℝ) (e, z, 0) ∂volume)
        = fun e : Env => scaledNearCellCount (n : ℝ) (decode e) 0 :=
      funext fun e => lintegral_scaledNeighborhoodTransport_incoming_eq_count (n : ℝ) e
    rwa [hEq] at hinc
  have hbound := lintegral_scaledNearCellCount_le_rootedFiniteEnergyMoment hk ν hν
  have hconst : ENNReal.ofReal (((n : ℝ) + 1) ^ 2) * volume (Metric.ball (0 : Plane) 1) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hfin : (∫⁻ e : Env, scaledNearCellCount (n : ℝ) (decode e) 0 ∂ν) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ hbound
    exact ENNReal.mul_ne_top hconst hFE
  filter_upwards [ae_lt_top hmeas hfin] with e he
  exact finite_of_scaledNearCellCount_ne_top (n : ℝ) (decode e) 0 he.ne

/-! ### The deterministic decay of the large-cell diameter -/

/-- `D_R`: the extended supremum of the diameters of the cells meeting the closed
ball of radius `R` about the origin. -/
noncomputable def maxDiamHittingBall (F : IndexedCells V) (R : ℝ) : ℝ≥0∞ :=
  ⨆ v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
    ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane))

/-- A cell meeting `B_R` whose diameter is at least `ε R` has the origin in its
`k`-neighbourhood as soon as `k ε ≥ 1`. -/
theorem mem_cellScaledNeighborhood_zero_of_hits (F : IndexedCells V) {k ε R : ℝ}
    (hk : 0 ≤ k) (hkε : 1 ≤ k * ε) (hR : 0 ≤ R) {v : V}
    (hv : Hits F (Metric.closedBall (0 : Plane) R) v)
    (hd : ε * R ≤ Metric.diam (F.cell v : Set Plane)) :
    (0 : Plane) ∈ cellScaledNeighborhood k (F.cell v) := by
  obtain ⟨x, hxcell, hxball⟩ := hv
  have h1 : Metric.infDist (0 : Plane) (F.cell v : Set Plane) ≤ dist (0 : Plane) x :=
    Metric.infDist_le_dist_of_mem hxcell
  have h2 : dist (0 : Plane) x ≤ R := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp hxball
  have h4 : k * (ε * R) ≤ k * Metric.diam (F.cell v : Set Plane) :=
    mul_le_mul_of_nonneg_left hd hk
  have h5 : R ≤ k * (ε * R) := by nlinarith [mul_nonneg (sub_nonneg.mpr hkε) hR]
  have h3 : R ≤ k * Metric.diam (F.cell v : Set Plane) := le_trans h5 h4
  exact le_trans (le_trans h1 h2) h3

/-- One finite `k`-neighbourhood family bounds `D_R` by a fixed finite number
plus the linear term `ε R`. -/
theorem exists_maxDiamHittingBall_bound (F : IndexedCells V) {k ε : ℝ} (hk : 0 ≤ k)
    (hkε : 1 ≤ k * ε)
    (hfin : {v : V | (0 : Plane) ∈ cellScaledNeighborhood k (F.cell v)}.Finite) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ R : ℝ, 0 ≤ R →
      maxDiamHittingBall F R ≤ M ⊔ ENNReal.ofReal (ε * R) := by
  refine ⟨∑ v ∈ hfin.toFinset, ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)), ?_, ?_⟩
  · exact (ENNReal.sum_lt_top.mpr fun v _ => ENNReal.ofReal_lt_top).ne
  · intro R hR
    refine iSup_le ?_
    rintro ⟨v, hv⟩
    by_cases hmem : (0 : Plane) ∈ cellScaledNeighborhood k (F.cell v)
    · refine le_sup_of_le_left ?_
      exact Finset.single_le_sum
        (f := fun v : V => ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)))
        (fun i _ => zero_le) (hfin.mem_toFinset.mpr hmem)
    · refine le_sup_of_le_right (ENNReal.ofReal_le_ofReal ?_)
      by_contra hlt
      push_neg at hlt
      exact hmem (mem_cellScaledNeighborhood_zero_of_hits F hk hkε hR hv hlt.le)

/-- `D_R < ∞`: only finitely many cells meeting a bounded patch are large. -/
theorem maxDiamHittingBall_lt_top (F : IndexedCells V)
    (hfin : ∀ n : ℕ,
      {v : V | (0 : Plane) ∈ cellScaledNeighborhood (n : ℝ) (F.cell v)}.Finite)
    (R : ℝ) (hR : 0 ≤ R) : maxDiamHittingBall F R < ∞ := by
  have h1 : {v : V | (0 : Plane) ∈ cellScaledNeighborhood (1 : ℝ) (F.cell v)}.Finite := by
    simpa using hfin 1
  obtain ⟨M, hMtop, hMbound⟩ :=
    exists_maxDiamHittingBall_bound F (k := (1 : ℝ)) (ε := (1 : ℝ)) zero_le_one
      (by norm_num) h1
  refine lt_of_le_of_lt (hMbound R hR) ?_
  exact sup_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr hMtop, ENNReal.ofReal_lt_top⟩

/-- `D_R / R → 0`, in the `ε`-form used elsewhere in this development. -/
theorem maxDiamHittingBall_sublinear (F : IndexedCells V)
    (hfin : ∀ n : ℕ,
      {v : V | (0 : Plane) ∈ cellScaledNeighborhood (n : ℝ) (F.cell v)}.Finite) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      maxDiamHittingBall F R ≤ ENNReal.ofReal (ε * R) := by
  intro ε hε
  have hεne : ε ≠ 0 := ne_of_gt hε
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / ε)
  have hnε : 1 ≤ (n : ℝ) * ε := by
    have h := mul_le_mul_of_nonneg_right hn hε.le
    rwa [one_div, inv_mul_cancel₀ hεne] at h
  obtain ⟨M, hMtop, hMbound⟩ :=
    exists_maxDiamHittingBall_bound F (Nat.cast_nonneg n) hnε (hfin n)
  refine ⟨max 1 (M.toReal / ε), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hdiv : M.toReal / ε ≤ R := le_trans (le_max_right _ _) hR
  have hle : M.toReal ≤ ε * R := by
    have h0 : M.toReal = ε * (M.toReal / ε) := by field_simp
    rw [h0]
    exact mul_le_mul_of_nonneg_left hdiv hε.le
  have hMR : M ≤ ENNReal.ofReal (ε * R) := by
    calc M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMtop).symm
      _ ≤ ENNReal.ofReal (ε * R) := ENNReal.ofReal_le_ofReal hle
  exact le_trans (hMbound R hRpos.le) (sup_le hMR le_rfl)

/-- The manuscript's `D_R / R → 0`. -/
theorem tendsto_maxDiamHittingBall_div_atTop (F : IndexedCells V)
    (hfin : ∀ n : ℕ,
      {v : V | (0 : Plane) ∈ cellScaledNeighborhood (n : ℝ) (F.cell v)}.Finite) :
    Filter.Tendsto (fun R : ℝ => (maxDiamHittingBall F R).toReal / R)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₀, hR₀pos, hR₀⟩ := maxDiamHittingBall_sublinear F hfin (ε / 2) (by linarith)
  refine ⟨max R₀ 1, fun R hR => ?_⟩
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_right R₀ 1) hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hle := hR₀ R (le_trans (le_max_left R₀ 1) hR)
  have htoReal : (maxDiamHittingBall F R).toReal ≤ ε / 2 * R :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  have hnonneg : 0 ≤ (maxDiamHittingBall F R).toReal := ENNReal.toReal_nonneg
  have hinv : (0 : ℝ) < R⁻¹ := inv_pos.mpr hRpos
  have h1 : (maxDiamHittingBall F R).toReal * R⁻¹ ≤ (ε / 2 * R) * R⁻¹ :=
    mul_le_mul_of_nonneg_right htoReal hinv.le
  have h2 : (ε / 2 * R) * R⁻¹ = ε / 2 := by field_simp
  have hdivnonneg : 0 ≤ (maxDiamHittingBall F R).toReal / R :=
    div_nonneg hnonneg hRpos.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdivnonneg, div_eq_mul_inv]
  have h3 : (maxDiamHittingBall F R).toReal * R⁻¹ ≤ ε / 2 := h1.trans_eq h2
  linarith

/-! ### The random-environment conclusion and the consumer bridge -/

/-- Manuscript `s:lem:largecells`: under mass transport and a finite (FE) moment,
almost every environment has `D_R < ∞` for every radius and `D_R / R → 0`. -/
theorem ae_maxDiamHittingBall_finite_and_sublinear (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν,
      (∀ R : ℝ, 0 ≤ R → maxDiamHittingBall (decode e) R < ∞) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          maxDiamHittingBall (decode e) R ≤ ENNReal.ofReal (ε * R)) ∧
      Filter.Tendsto (fun R : ℝ => (maxDiamHittingBall (decode e) R).toReal / R)
        Filter.atTop (nhds 0) := by
  filter_upwards [ae_finite_scaledNear_of_finiteEnergyMoment ν hν hFE] with e he
  exact ⟨fun R hR => maxDiamHittingBall_lt_top (decode e) he R hR,
    maxDiamHittingBall_sublinear (decode e) he,
    tendsto_maxDiamHittingBall_div_atTop (decode e) he⟩

/-- The bridge to `ReflectedGMS.Geometry.DiameterBlockIndex`: the dyadic patch
maximum is dominated by `D_R` for any ball containing the square. -/
theorem maxCellDiameter_le_maxDiamHittingBall (F : IndexedCells V)
    (D : DyadicApproximation.Grid) (s : DyadicApproximation.SquareIndex) {R : ℝ}
    (hsub : (DyadicApproximation.square D s).carrier ⊆ Metric.closedBall (0 : Plane) R) :
    DyadicApproximation.maxCellDiameter F D s ≤ maxDiamHittingBall F R := by
  refine iSup_le ?_
  rintro ⟨v, hv⟩
  simp only [StatementIngredients.patchVertices, Set.mem_setOf_eq, Hits] at hv
  obtain ⟨z, hz1, hz2⟩ := hv
  exact le_iSup (fun w : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v} =>
    ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, ⟨z, hz1, hsub hz2⟩⟩

end ReflectedGMS.Spatial
