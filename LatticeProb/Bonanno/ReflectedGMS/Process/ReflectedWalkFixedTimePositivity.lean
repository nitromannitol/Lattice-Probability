/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ReflectedWalkFixedTimePositivity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockRealTimeShift
import LatticeProb.Bonanno.ReflectedGMS.Forms.ExponentialTruncatedMean

/-! # Fixed-time positivity of a reflected walk on a connected graph

For a process family satisfying `IsReflectedWalk G rate hmin PF` with positive rates on a
connected conductance graph, every vertex is occupied at every positive time with positive
probability from every start:

  `PF.P v {ω | PF.X t ω = some u} ≠ 0`   for all `v u` and `t > 0`
  (`transition_ne_zero`).

This is the manuscript's positivity step in the start-cell independence argument (tex:1504-1505:
follow a finite graph path with total holding `< t`, then stay).  The proof uses ONLY the
properties already packaged in `IsReflectedWalk` — no sample-level representation of the
process as holdings plus jumps is needed:

* `transition_mul_le` — Chapman–Kolmogorov lower bound `p_s(x,y) p_r(y,z) ≤ p_{r+s}(x,z)`,
  the one-term bound of `AreaClockRealTimeShift.measure_shiftedPath_preimage` (property (iv));
* `transition_self_ne_zero` — staying: before the exit time the walk sits at its start
  (definition of `hittingAfter`), and the exit time is `Exp(rate x)` (property (iii)), so
  `p_t(x,x) ≥ e^{-rate(x) t} > 0` for every `t ≥ 0`;
* `transition_ne_zero_of_adj` — one step: for a neighbour `y` of `x`, `p_s(x,y) > 0` for every
  `s > 0`.  If `p_s(x,y) = 0` then (by the two facts above) `p_r(x,y) = 0` for all `r ≤ s`, so
  a.s. the walk is never at `y` at rational times `≤ s`; by right continuity (property (ii)) the
  event `{exit time ≤ s/2, exit position = y}` is then null.  But property (iii) makes the exit
  time and the exit position independent with `P(exit ≤ s/2) = 1 - e^{-rate(x) s/2} > 0` and
  `P(exit position = y) = c(x,y)/π(x) > 0`;
* `transition_ne_zero_of_walk` — induction along a graph walk, halving the time at each step.

The possible explosion of the reflected walk (end-valued times) plays no role: only fixed
times, the first exit, and right continuity at a vertex-valued time are used.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.ReflectedWalkFixedTimePositivity

open ReflectedWalk ReflectedWalk.Theorem16 ReflectedGMS.AreaClockRealTimeShift

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {rate : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}

/-- **Chapman–Kolmogorov lower bound** (property (iv)): `p_s(x,y) p_r(y,z) ≤ p_{r+s}(x,z)`. -/
theorem transition_mul_le (h : IsReflectedWalk G rate hmin PF) (x y z : V) (s r : ℝ≥0) :
    PF.transition x s y * PF.transition y r z ≤ PF.transition x (r + s) z := by
  have hB : MeasurableSet ((fun f : Trajectory V => f r) ⁻¹' {some z}) :=
    measurable_pi_apply r (measurableSet_singleton _)
  have hCK := measure_shiftedPath_preimage h x s hB
  have hpre : shiftedPath PF.X s ⁻¹' ((fun f : Trajectory V => f r) ⁻¹' {some z}) =
      {ω | PF.X (r + s) ω = some z} := by
    ext ω
    simp [shiftedPath]
  rw [hpre] at hCK
  show _ ≤ PF.P x {ω | PF.X (r + s) ω = some z}
  rw [hCK, ← PF.law_eval y r z]
  exact ENNReal.le_tsum (f := fun w : V =>
    PF.transition x s w * PF.law w ((fun f : Trajectory V => f r) ⁻¹' {some z})) y

/-- **Staying** (property (iii)): from `x`, the walk is at `x` at every fixed time with positive
probability (at least `P(exit time > t) = e^{-rate(x) t}`). -/
theorem transition_self_ne_zero (h : IsReflectedWalk G rate hmin PF) (hw : ∀ x, 0 < rate x)
    (x : V) (t : ℝ≥0) : PF.transition x t x ≠ 0 := by
  obtain ⟨hσm, -, -, hlaw, -⟩ := (h x).2.2.2.2.1
  have hsub : exitTime PF.X x ⁻¹' Ioi (t : WithTop ℝ≥0) ⊆ {ω | PF.X t ω = some x} := by
    intro ω hω
    have hω' : ((t : ℝ≥0) : WithTop ℝ≥0) <
        hittingAfter PF.X {o : Option V | o ≠ some x} 0 ω := hω
    have hnot : PF.X t ω ∉ {o : Option V | o ≠ some x} :=
      notMem_of_lt_hittingAfter hω' zero_le
    by_contra hne
    exact hnot hne
  have h1 : ProbabilityTheory.expMeasure (rate x) (Ioi (t : ℝ)) ≤
      ProbabilityTheory.expMeasure (rate x) (toWithTop ⁻¹' Ioi (t : WithTop ℝ≥0)) := by
    refine measure_mono fun r hr => ?_
    show (t : WithTop ℝ≥0) < ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0)
    exact WithTop.coe_lt_coe.2 (Real.lt_toNNReal_iff_coe_lt.2 hr)
  have h2 : 0 < ProbabilityTheory.expMeasure (rate x) (Ioi (t : ℝ)) := by
    rw [ExponentialTruncatedMean.expMeasure_Ioi_eq (hw x) t t.2]
    exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hpos : PF.P x (exitTime PF.X x ⁻¹' Ioi (t : WithTop ℝ≥0)) ≠ 0 := by
    rw [← Measure.map_apply_of_aemeasurable hσm measurableSet_Ioi, hlaw,
      Measure.map_apply measurable_toWithTop measurableSet_Ioi]
    exact (lt_of_lt_of_le h2 h1).ne'
  exact fun h0 => hpos (measure_mono_null hsub h0)

/-- **One step** (properties (ii), (iii), (iv)): for a neighbour `y` of `x`, the walk from `x`
is at `y` at every positive time with positive probability. -/
theorem transition_ne_zero_of_adj (h : IsReflectedWalk G rate hmin PF) (hw : ∀ x, 0 < rate x)
    {x y : V} (hxy : G.Adj x y) {s : ℝ≥0} (hs : 0 < s) : PF.transition x s y ≠ 0 := by
  intro hzero
  -- vanishing at every earlier time
  have hle : ∀ r : ℝ≥0, r ≤ s → PF.transition x r y = 0 := by
    intro r hr
    have hm := transition_mul_le h x y y r (s - r)
    rw [tsub_add_cancel_of_le hr, hzero, nonpos_iff_eq_zero, mul_eq_zero] at hm
    exact hm.resolve_right (transition_self_ne_zero h hw y (s - r))
  -- a.s. no visit to `y` at rational times `≤ s`
  have hrat : ∀ᵐ ω ∂PF.P x, ∀ q : ℚ, (q : ℝ).toNNReal ≤ s →
      PF.X (q : ℝ).toNNReal ω ≠ some y := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ).toNNReal ≤ s
    · have h0 : PF.P x {ω | PF.X (q : ℝ).toNNReal ω = some y} = 0 := hle _ hq
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h' => absurd h' hq
  obtain ⟨hσm, -, hind, hlaw, hstep⟩ := (h x).2.2.2.2.1
  have hrc := (h x).2.2.1
  -- the event `{exit ≤ s/2, exit position = y}` is null
  have hE0 : PF.P x (exitTime PF.X x ⁻¹' Iic ((s / 2 : ℝ≥0) : WithTop ℝ≥0) ∩
      stoppedValue PF.X (exitTime PF.X x) ⁻¹' {some y}) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hrat, hrc] with ω hω hrcω
    rintro ⟨hA, hB⟩
    have hA' : exitTime PF.X x ω ≤ ((s / 2 : ℝ≥0) : WithTop ℝ≥0) := hA
    obtain ⟨σ0, hσ0⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hA')
    have hσle : σ0 ≤ s / 2 := by
      rw [← hσ0] at hA'
      exact WithTop.coe_le_coe.1 hA'
    have hX : PF.X σ0 ω = some y := by
      have hB' : PF.X (exitTime PF.X x ω).untopA ω = some y := hB
      rw [← hσ0] at hB'
      exact hB'
    obtain ⟨ε, hε, hεX⟩ := hrcω σ0 ⟨y, hX⟩
    have hs2 : s / 2 < s := half_lt_self hs
    have hlt : (σ0 : ℝ) < min ((σ0 + ε : ℝ≥0) : ℝ) (s : ℝ) := by
      refine lt_min ?_ ?_
      · exact NNReal.coe_lt_coe.2 (lt_add_of_pos_right σ0 hε)
      · exact NNReal.coe_lt_coe.2 (lt_of_le_of_lt hσle hs2)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq0 : (0 : ℝ) ≤ q := le_trans (NNReal.coe_nonneg σ0) hq1.le
    have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have hqs : (q : ℝ).toNNReal ≤ s := by
      rw [← NNReal.coe_le_coe, hqc]
      exact (lt_of_lt_of_le hq2 (min_le_right _ _)).le
    have hmem : (q : ℝ).toNNReal ∈ Ico σ0 (σ0 + ε) := by
      constructor
      · rw [← NNReal.coe_le_coe, hqc]
        exact hq1.le
      · rw [← NNReal.coe_lt_coe, hqc]
        exact lt_of_lt_of_le hq2 (min_le_left _ _)
    exact hω q hqs ((hεX _ hmem).trans hX)
  -- but it has positive probability by property (iii)
  have hApos : PF.P x (exitTime PF.X x ⁻¹' Iic ((s / 2 : ℝ≥0) : WithTop ℝ≥0)) ≠ 0 := by
    rw [← Measure.map_apply_of_aemeasurable hσm measurableSet_Iic, hlaw,
      ExponentialTruncatedMean.map_toWithTop_expMeasure_Iic,
      ExponentialTruncatedMean.expMeasure_Iic_eq (hw x) ((s / 2 : ℝ≥0) : ℝ)
        (NNReal.coe_nonneg _)]
    refine (ENNReal.ofReal_pos.2 (sub_pos.2 (Real.exp_lt_one_iff.2 ?_))).ne'
    have hpos2 : (0 : ℝ) < ((s / 2 : ℝ≥0) : ℝ) := NNReal.coe_pos.2 (half_pos hs)
    have := mul_pos (hw x) hpos2
    linarith
  have hBpos : PF.P x (stoppedValue PF.X (exitTime PF.X x) ⁻¹' {some y}) ≠ 0 := by
    have hset : stoppedValue PF.X (exitTime PF.X x) ⁻¹' {some y} =
        {ω | stoppedValue PF.X (exitTime PF.X x) ω = some y} := rfl
    rw [hset, hstep y]
    exact (ENNReal.ofReal_pos.2 (div_pos hxy (G.pi_pos_of_adj hxy))).ne'
  rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_Iic (measurableSet_singleton _)] at hE0
  exact mul_ne_zero hApos hBpos hE0

/-- **Along a graph walk**: from `a`, the walk is at `b` at every positive time with positive
probability, whenever `b` is reachable from `a` by a walk of `G`. -/
theorem transition_ne_zero_of_walk (h : IsReflectedWalk G rate hmin PF) (hw : ∀ x, 0 < rate x)
    {a b : V} (p : G.toSimpleGraph.Walk a b) :
    ∀ {t : ℝ≥0}, 0 < t → PF.transition a t b ≠ 0 := by
  induction p with
  | nil => exact fun {t} _ => transition_self_ne_zero h hw _ t
  | @cons x c y hac p ih =>
    intro t ht
    have ht2 : 0 < t / 2 := half_pos ht
    have hle := transition_mul_le h x c y (t / 2) (t / 2)
    rw [add_halves] at hle
    intro h0
    rw [h0, nonpos_iff_eq_zero] at hle
    exact mul_ne_zero (transition_ne_zero_of_adj h hw hac ht2) (ih ht2) hle

/-- **Fixed-time positivity of a reflected walk on a connected graph with positive rates**:
from every vertex, every vertex is occupied at every positive time with positive probability.
Uses only `IsReflectedWalk` (properties (ii), (iii), (iv)). -/
theorem transition_ne_zero (h : IsReflectedWalk G rate hmin PF) (hw : ∀ x, 0 < rate x)
    (hG : G.toSimpleGraph.Connected) (v u : V) {t : ℝ≥0} (ht : 0 < t) :
    PF.P v {ω | PF.X t ω = some u} ≠ 0 := by
  obtain ⟨p⟩ := hG.preconnected v u
  exact transition_ne_zero_of_walk h hw p ht

end ReflectedGMS.ReflectedWalkFixedTimePositivity
