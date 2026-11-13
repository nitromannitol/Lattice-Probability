/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.LineVariation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.AELineConnectivity
import LatticeProb.Bonanno.ReflectedGMS.Analysis.ExtendedEnergy
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Energy controls the integrated line variation

This module proves the countable-edge Cauchy-Schwarz line estimate: the Lebesgue
integral over the horizontal offset `y` of the total variation of `f` along the
edges of the cell graph meeting the segment `[a,b] × {y}` is bounded by the
square root of the geometric reciprocal-conductance mass
`∑ d_H ^ 2 π*(H)` times the square root of the graph energy of `f`.

Everything is stated in `ℝ≥0∞`, so no summability, finiteness or integrability
hypothesis is needed: the vertex set may be infinite, the edge set countable,
the energy infinite, and the geometric mass infinite.

Sums over `V × V` count each unordered edge twice, which is the normalization
already used by `ReflectedGMS.energyENN`; the line variation is therefore also
defined as an ordered-pair sum divided by two.

The oscillation half of the manuscript lemma (finite paths inside a line
subgraph at a non-exceptional offset) is *not* proved here; see
`ReflectedGMS.HorizontalGood` for the connectivity input it needs.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {V : Type*}

/-! ### Offsets met by a cell -/

/-- The set of offsets `y` whose horizontal segment `[a,b] × {y}` meets the cell of `v`. -/
def horizontalHitOffsets (F : IndexedCells V) (a b : ℝ) (v : V) : Set ℝ :=
  {y | Hits F (horizontal a b y) v}

theorem mem_horizontalHitOffsets {F : IndexedCells V} {a b y : ℝ} {v : V} :
    y ∈ horizontalHitOffsets F a b v ↔ Hits F (horizontal a b y) v := Iff.rfl

/-- The offsets met by a cell are exactly the second coordinates of the part of the
cell lying in the vertical strip `a ≤ z 0 ≤ b`. -/
theorem horizontalHitOffsets_eq_image (F : IndexedCells V) (a b : ℝ) (v : V) :
    horizontalHitOffsets F a b v =
      (fun z : Plane => z 1) ''
        ((F.cell v : Set Plane) ∩ (fun z : Plane => z 0) ⁻¹' Set.Icc a b) := by
  ext y
  constructor
  · rintro ⟨z, hzcell, hz0a, hz0b, hz1⟩
    exact ⟨z, ⟨hzcell, ⟨hz0a, hz0b⟩⟩, hz1⟩
  · rintro ⟨z, ⟨hzcell, hz0⟩, hz1⟩
    exact ⟨z, hzcell, hz0.1, hz0.2, hz1⟩

/-- The offset set of a cell is compact, since cells are compact. -/
theorem horizontalHitOffsets_isCompact (F : IndexedCells V) (a b : ℝ) (v : V) :
    IsCompact (horizontalHitOffsets F a b v) := by
  rw [horizontalHitOffsets_eq_image]
  refine IsCompact.image ?_ (PiLp.continuous_apply 2 _ (1 : Fin 2))
  exact (F.cell v).isCompact.inter_right
    (IsClosed.preimage (PiLp.continuous_apply 2 _ (0 : Fin 2)) isClosed_Icc)

/-- The offset set of a cell is Lebesgue measurable. -/
theorem horizontalHitOffsets_measurableSet (F : IndexedCells V) (a b : ℝ) (v : V) :
    MeasurableSet (horizontalHitOffsets F a b v) :=
  (horizontalHitOffsets_isCompact F a b v).measurableSet

/-- The diameter `d_H` of a cell, as an extended nonnegative real. -/
noncomputable def cellDiameter (F : IndexedCells V) (v : V) : ℝ≥0∞ :=
  Metric.ediam (F.cell v : Set Plane)

/-- The length of the offset set of a cell is at most the diameter of the cell. -/
theorem volume_horizontalHitOffsets_le_cellDiameter (F : IndexedCells V) (a b : ℝ) (v : V) :
    volume (horizontalHitOffsets F a b v) ≤ cellDiameter F v := by
  refine (Real.volume_le_diam _).trans ?_
  rw [horizontalHitOffsets_eq_image, cellDiameter]
  refine Metric.ediam_le ?_
  rintro y ⟨z, ⟨hz, -⟩, rfl⟩ y' ⟨z', ⟨hz', -⟩, rfl⟩
  exact (PiLp.edist_apply_le z z' 1).trans (Metric.edist_le_ediam_of_mem hz hz')

/-! ### Edge data -/

open scoped Classical in
/-- The absolute gradient `|f H' - f H|` of `f` on an edge, and `0` off the edge set. -/
noncomputable def edgeGradAbs (G : ReflectedWalk.ConductanceGraph V) (f : V → ℝ)
    (p : V × V) : ℝ≥0∞ :=
  if G.Adj p.1 p.2 then ENNReal.ofReal |f p.2 - f p.1| else 0

open scoped Classical in
/-- The reciprocal conductance `1/c(e)` of an edge, and `0` off the edge set. -/
noncomputable def reciprocalConductance (G : ReflectedWalk.ConductanceGraph V)
    (p : V × V) : ℝ≥0∞ :=
  if G.Adj p.1 p.2 then (ENNReal.ofReal (G.c p.1 p.2))⁻¹ else 0

/-- The reciprocal-conductance mass `π*(H) = ∑_{H' ∼ H} 1/c(H,H')` of a vertex. -/
noncomputable def reciprocalConductanceMass (G : ReflectedWalk.ConductanceGraph V)
    (v : V) : ℝ≥0∞ :=
  ∑' w : V, reciprocalConductance G (v, w)

/-- The geometric mass `∑_H d_H ^ 2 π*(H)` appearing in the line estimate. -/
noncomputable def diameterReciprocalConductanceMass (F : IndexedCells V) : ℝ≥0∞ :=
  ∑' v : V, cellDiameter F v ^ (2 : ℝ) * reciprocalConductanceMass F.graph v

/-- The length of the set of offsets whose segment is met by both endpoints of a pair. -/
noncomputable def horizontalEdgeOffsetLength (F : IndexedCells V) (a b : ℝ)
    (p : V × V) : ℝ≥0∞ :=
  volume (horizontalHitOffsets F a b p.1 ∩ horizontalHitOffsets F a b p.2)

/-! ### The line variation -/

/-- The contribution of an ordered pair of cells to the variation along the segment
`[a,b] × {y}`: it is `|f H' - f H|` when the pair is an edge and both cells meet the
segment, and `0` otherwise. -/
noncomputable def horizontalLineEdgeTerm (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) (y : ℝ) : ℝ≥0∞ :=
  (horizontalHitOffsets F a b p.1 ∩ horizontalHitOffsets F a b p.2).indicator
    (fun _ => edgeGradAbs F.graph f p) y

open scoped Classical in
theorem horizontalLineEdgeTerm_apply (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) (y : ℝ) :
    horizontalLineEdgeTerm F f a b p y =
      if F.graph.Adj p.1 p.2 ∧ Hits F (horizontal a b y) p.1 ∧
          Hits F (horizontal a b y) p.2 then
        ENNReal.ofReal |f p.2 - f p.1| else 0 := by
  by_cases hhit : y ∈ horizontalHitOffsets F a b p.1 ∩ horizontalHitOffsets F a b p.2
  · rw [horizontalLineEdgeTerm, Set.indicator_of_mem hhit, edgeGradAbs]
    by_cases hadj : F.graph.Adj p.1 p.2
    · rw [if_pos hadj, if_pos ⟨hadj, hhit.1, hhit.2⟩]
    · rw [if_neg hadj, if_neg]
      rintro ⟨hadj', -, -⟩
      exact hadj hadj'
  · rw [horizontalLineEdgeTerm, Set.indicator_of_notMem hhit, if_neg]
    rintro ⟨-, h1, h2⟩
    exact hhit ⟨h1, h2⟩

/-- `V_f(y)`: the total variation of `f` along the edges of the cell graph meeting the
horizontal segment `[a,b] × {y}`.  The ordered-pair sum is divided by two, so each
unordered edge is counted once. -/
noncomputable def horizontalLineVariation (F : IndexedCells V) (f : V → ℝ)
    (a b y : ℝ) : ℝ≥0∞ :=
  (∑' p : V × V, horizontalLineEdgeTerm F f a b p y) / 2

theorem measurable_horizontalLineEdgeTerm (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) : Measurable (horizontalLineEdgeTerm F f a b p) :=
  measurable_const.indicator
    ((horizontalHitOffsets_measurableSet F a b p.1).inter
      (horizontalHitOffsets_measurableSet F a b p.2))

theorem lintegral_horizontalLineEdgeTerm (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) :
    ∫⁻ y, horizontalLineEdgeTerm F f a b p y
      = horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p := by
  have hmeas : MeasurableSet
      (horizontalHitOffsets F a b p.1 ∩ horizontalHitOffsets F a b p.2) :=
    (horizontalHitOffsets_measurableSet F a b p.1).inter
      (horizontalHitOffsets_measurableSet F a b p.2)
  simp only [horizontalLineEdgeTerm]
  rw [lintegral_indicator hmeas, setLIntegral_const]
  simp only [horizontalEdgeOffsetLength]
  exact mul_comm _ _

/-- **Tonelli for the line variation.**  Integrating the line variation over the offset
turns it into the edge sum weighted by the length of the set of offsets at which the
edge meets the segment.  Countably many edges are allowed. -/
theorem lintegral_horizontalLineVariation [Countable V] (F : IndexedCells V) (f : V → ℝ)
    (a b : ℝ) :
    ∫⁻ y, horizontalLineVariation F f a b y
      = (∑' p : V × V,
          horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p) / 2 := by
  have hinv : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  calc ∫⁻ y, horizontalLineVariation F f a b y
      = ∫⁻ y, (2 : ℝ≥0∞)⁻¹ * ∑' p : V × V, horizontalLineEdgeTerm F f a b p y := by
        simp only [horizontalLineVariation, ENNReal.div_eq_inv_mul]
    _ = (2 : ℝ≥0∞)⁻¹ * ∫⁻ y, ∑' p : V × V, horizontalLineEdgeTerm F f a b p y :=
        lintegral_const_mul' _ _ hinv
    _ = (2 : ℝ≥0∞)⁻¹ * ∑' p : V × V, ∫⁻ y, horizontalLineEdgeTerm F f a b p y := by
        rw [lintegral_tsum fun p => (measurable_horizontalLineEdgeTerm F f a b p).aemeasurable]
    _ = (2 : ℝ≥0∞)⁻¹ * ∑' p : V × V,
          horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p := by
        rw [tsum_congr fun p => lintegral_horizontalLineEdgeTerm F f a b p]
    _ = (∑' p : V × V,
          horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p) / 2 := by
        rw [ENNReal.div_eq_inv_mul]

/-! ### Cauchy-Schwarz -/

theorem ennreal_rpow_inv_two_rpow_two (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Cauchy-Schwarz for unordered sums in `ℝ≥0∞`, obtained from the finite-sum Hölder
inequality by monotone approximation.  No summability hypothesis is needed. -/
theorem tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq {ι : Type*} (u v : ι → ℝ≥0∞) :
    ∑' i, u i * v i
      ≤ (∑' i, u i ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) * (∑' i, v i ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  refine (ENNReal.inner_le_Lp_mul_Lq s u v Real.HolderConjugate.two_two).trans ?_
  rw [one_div]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num))
    (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num))

/-- The Cauchy-Schwarz splitting of an edge weight into a reciprocal-conductance factor
and an energy factor. -/
theorem horizontalEdgeOffsetLength_mul_edgeGradAbs_le (F : IndexedCells V) (f : V → ℝ)
    (a b : ℝ) (p : V × V) :
    horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p
      ≤ (horizontalEdgeOffsetLength F a b p * reciprocalConductance F.graph p ^ (2⁻¹ : ℝ)) *
        (edgeGradAbs F.graph f p * ENNReal.ofReal (F.graph.c p.1 p.2) ^ (2⁻¹ : ℝ)) := by
  by_cases hadj : F.graph.Adj p.1 p.2
  · have hpos : 0 < F.graph.c p.1 p.2 := hadj
    have h0 : ENNReal.ofReal (F.graph.c p.1 p.2) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hpos]
    have htop : ENNReal.ofReal (F.graph.c p.1 p.2) ≠ ∞ := ENNReal.ofReal_ne_top
    have key :
        (horizontalEdgeOffsetLength F a b p * reciprocalConductance F.graph p ^ (2⁻¹ : ℝ)) *
            (edgeGradAbs F.graph f p * ENNReal.ofReal (F.graph.c p.1 p.2) ^ (2⁻¹ : ℝ))
          = horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p := by
      rw [reciprocalConductance, if_pos hadj, mul_mul_mul_comm,
        ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        ENNReal.inv_mul_cancel h0 htop, ENNReal.one_rpow, mul_one]
    exact le_of_eq key.symm
  · simp [edgeGradAbs, hadj]

/-! ### The two Cauchy-Schwarz factors -/

/-- The reciprocal-conductance factor is bounded by the geometric mass
`∑_H d_H ^ 2 π*(H)`, because an edge meets a segment only for offsets in the
projection of either of its two cells. -/
theorem tsum_horizontalEdgeOffsetLength_sq_reciprocal_le (F : IndexedCells V) (a b : ℝ) :
    (∑' p : V × V,
        (horizontalEdgeOffsetLength F a b p *
          reciprocalConductance F.graph p ^ (2⁻¹ : ℝ)) ^ (2 : ℝ))
      ≤ diameterReciprocalConductanceMass F := by
  calc (∑' p : V × V,
        (horizontalEdgeOffsetLength F a b p *
          reciprocalConductance F.graph p ^ (2⁻¹ : ℝ)) ^ (2 : ℝ))
      = ∑' p : V × V,
          horizontalEdgeOffsetLength F a b p ^ (2 : ℝ) * reciprocalConductance F.graph p := by
        refine tsum_congr fun p => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
          ennreal_rpow_inv_two_rpow_two]
    _ ≤ ∑' p : V × V, cellDiameter F p.1 ^ (2 : ℝ) * reciprocalConductance F.graph p := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        have hle : horizontalEdgeOffsetLength F a b p ≤ cellDiameter F p.1 := by
          refine le_trans (measure_mono Set.inter_subset_left) ?_
          exact volume_horizontalHitOffsets_le_cellDiameter F a b p.1
        exact mul_le_mul' (ENNReal.rpow_le_rpow hle (by norm_num)) le_rfl
    _ = ∑' v : V, ∑' w : V,
          cellDiameter F v ^ (2 : ℝ) * reciprocalConductance F.graph (v, w) :=
        ENNReal.tsum_prod'
    _ = diameterReciprocalConductanceMass F := by
        rw [diameterReciprocalConductanceMass]
        exact tsum_congr fun v => ENNReal.tsum_mul_left

/-- The energy factor is exactly twice the graph energy of `f`. -/
theorem tsum_edgeGradAbs_sq_mul_conductance (G : ReflectedWalk.ConductanceGraph V)
    (f : V → ℝ) :
    (∑' p : V × V,
        (edgeGradAbs G f p * ENNReal.ofReal (G.c p.1 p.2) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ))
      = 2 * energyENN G f := by
  have hterm : ∀ p : V × V,
      (edgeGradAbs G f p * ENNReal.ofReal (G.c p.1 p.2) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
        = ENNReal.ofReal (G.gradSq f p) := by
    intro p
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ennreal_rpow_inv_two_rpow_two, ENNReal.rpow_two]
    by_cases hadj : G.Adj p.1 p.2
    · rw [edgeGradAbs, if_pos hadj, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      simp only [ReflectedWalk.ConductanceGraph.gradSq]
      rw [mul_comm]
    · have hc : G.c p.1 p.2 = 0 := le_antisymm (not_lt.1 hadj) (G.c_nonneg _ _)
      rw [edgeGradAbs, if_neg hadj]
      simp only [ReflectedWalk.ConductanceGraph.gradSq, hc]
      simp
  rw [tsum_congr hterm, energyENN]
  exact (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm

/-! ### The line estimate -/

/-- **Energy controls the average line variation** (manuscript `s:lem:lines`, first
assertion).  The offset integral of the line variation of `f` is bounded by the square
root of the geometric reciprocal-conductance mass times the square root of the graph
energy of `f`.  Countably many edges and infinitely many cells are allowed, and both
sides may be infinite. -/
theorem lintegral_horizontalLineVariation_le [Countable V] (F : IndexedCells V)
    (f : V → ℝ) (a b : ℝ) :
    ∫⁻ y, horizontalLineVariation F f a b y
      ≤ diameterReciprocalConductanceMass F ^ (2⁻¹ : ℝ) * energyENN F.graph f ^ (2⁻¹ : ℝ) := by
  have harr : ∀ x y z w : ℝ≥0∞, x * (z * y) * w = x * y * (z * w) := by
    intro x y z w
    ring
  have hCS : (∑' p : V × V,
        horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p)
      ≤ diameterReciprocalConductanceMass F ^ (2⁻¹ : ℝ) *
        (2 * energyENN F.graph f) ^ (2⁻¹ : ℝ) := by
    refine le_trans (ENNReal.tsum_le_tsum fun p =>
      horizontalEdgeOffsetLength_mul_edgeGradAbs_le F f a b p) ?_
    refine le_trans (tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq _ _) ?_
    exact mul_le_mul'
      (ENNReal.rpow_le_rpow (tsum_horizontalEdgeOffsetLength_sq_reciprocal_le F a b)
        (by norm_num))
      (le_of_eq (by rw [tsum_edgeGradAbs_sq_mul_conductance]))
  have hsplit : ((2 : ℝ≥0∞) * energyENN F.graph f) ^ (2⁻¹ : ℝ)
      = (2 : ℝ≥0∞) ^ (2⁻¹ : ℝ) * energyENN F.graph f ^ (2⁻¹ : ℝ) :=
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hhalf : (2 : ℝ≥0∞) ^ (2⁻¹ : ℝ) * (2 : ℝ≥0∞)⁻¹ ≤ 1 := by
    have hmono : (2 : ℝ≥0∞) ^ (2⁻¹ : ℝ) ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [ENNReal.rpow_one] at hmono
    calc (2 : ℝ≥0∞) ^ (2⁻¹ : ℝ) * (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ :=
          mul_le_mul' hmono le_rfl
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [lintegral_horizontalLineVariation]
  calc (∑' p : V × V, horizontalEdgeOffsetLength F a b p * edgeGradAbs F.graph f p) / 2
      ≤ (diameterReciprocalConductanceMass F ^ (2⁻¹ : ℝ) *
          (2 * energyENN F.graph f) ^ (2⁻¹ : ℝ)) / 2 := by gcongr
    _ = (diameterReciprocalConductanceMass F ^ (2⁻¹ : ℝ) *
          energyENN F.graph f ^ (2⁻¹ : ℝ)) * ((2 : ℝ≥0∞) ^ (2⁻¹ : ℝ) * (2 : ℝ≥0∞)⁻¹) := by
        rw [hsplit, div_eq_mul_inv]
        exact harr _ _ _ _
    _ ≤ (diameterReciprocalConductanceMass F ^ (2⁻¹ : ℝ) *
          energyENN F.graph f ^ (2⁻¹ : ℝ)) * 1 := mul_le_mul' le_rfl hhalf
    _ = diameterReciprocalConductanceMass F ^ (2⁻¹ : ℝ) *
          energyENN F.graph f ^ (2⁻¹ : ℝ) := mul_one _

end ReflectedGMS
