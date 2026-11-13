/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CompactContainmentProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualWindowModulus
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialInfinityAvoidance
import LatticeProb.Bonanno.ReflectedGMS.Limit.SquareMartingaleMaximal

/-!
# Compact containment of the rescaled reflected walk, from the martingale arrays

`ActualWindowModulus.CompactContainment` (`:75`) is manuscript `p:lem:lindeberg`
in the shape `CorrectorInterpolationTransfer` consumes: along every positive null
sequence of scales `ε n` and on every horizon `H`, the representative of the
occupied vertex stays in `B̄(0, R/ε n)` up to time `(ε n)⁻² H`, with probability
at least `1 - η`, for **one** radius `R` chosen before the scale.  It appeared
only in consumer positions and had no producer.

## What is proved here

`compactContainment_of_arrays` derives it from hypotheses the consumer of
`ActualWindowModulus.hmodExp_of_inputs` **already holds**: the cell
representatives `hz`, the corrector sublinearity `hsub`, the spatial-extension
clause `hM`, and the localized martingale arrays `harray`.  So compact
containment is *not* an independent open atom of `hmodExp`: after this module and
`RightDenseVertexTimesProducer`, the only atom left is `harray`.

The mechanism is the project's own continuous-time `L²` Doob bound
`MartingaleLimit.continuous_time_abs_maximal` (`Limit/SquareMartingaleMaximal.lean:52`)
applied to each row of each coordinate array:

* `terminal` gives a second-moment bound `C` at the horizon that is **uniform in
  the row index `n`** — this is exactly the Lindeberg-type input of the
  manuscript lemma, and it is what makes the radius choosable before the scale;
* Doob converts it into `P(sup_{u ≤ H} |Y n u| > b) ≤ C / b²`, uniformly in `n`;
* `agree` transports the bound from the array row `Y n` to the actual rescaled
  coordinate `ε n · M((ε n)⁻² u)`, at a cost tending to `0`;
* the two coordinates are combined by `‖x‖ ≤ |x 0| + |x 1|`
  (`WindowModulusGridTransfer.norm_le_abs_zero_add_abs_one`), giving
  `ε n · ‖M s‖ ≤ 2 b` on the good event;
* `IsSpatialExtension` identifies `M s` with `Φ v` at a vertex time, and
  `exists_bound_norm_representative` — a two-line consequence of
  `UniformlySublinearError` at tolerance `1/2` — upgrades a bound on `‖Φ v‖` to
  `‖z v‖ ≤ max R₀ (2‖Φ v‖)`.  The additive `R₀` is absorbed because `ε n ≤ 1`
  eventually.

The radius produced is `R = max R₀ (4 b)` with `R₀` depending only on `hsub` and
`b` only on the arrays' second-moment constants and on `η`: **both are fixed
before `n`**, which is the anti-vacuity requirement of this lane.

Nothing here certifies `harray`, `hΦ`, or tightness.
-/

-- Merged from `ReflectedGMS/Limit/RightDenseVertexTimesProducer.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_RightDenseVertexTimesProducer

/-!
# Right-density of the vertex times of the area-clock reflected walk

`CorrectorInterpolationTransfer.RightDenseVertexTimes F X` (`:278`) is the
hypothesis "every time is approached from the right by times at which `X` sits at
an actual vertex".  It is consumed by
`exists_pos_forall_scaled_interpolation_sub_le_allTimes` (`:306`) and hence by
`ActualWindowModulus.hclose_of_containment`, and it had **no producer** anywhere
in the tree.

This module supplies one.  Two steps, both cheap:

* `rightDenseVertexTimes_of_dense` — a purely topological implication.  On `ℝ≥0`
  the filter `𝓝[>] t` is `NeBot` (`nhdsGT_neBot`, since `ℝ≥0` is a densely
  ordered `NoMaxOrder`), so any set that is *dense* meets every
  `𝓝[>] t`-neighbourhood: plain density already gives right-density at every
  point.  No monotonicity or regularity of the path is used.
* `ae_rightDenseVertexTimes_of_isReflectedWalk` — the transport of
  `Forms/SpatialInfinityAvoidance.dense_vertices_ae_of_isReflectedWalk` (`:64`)
  to the area clock.  That theorem already proves almost-sure *density* of the
  vertex times of a collapsed lift, from fixed-time definedness of the reflected
  walk on the rational grid alone.

The end products take the two facts a consumer of
`ActualWindowModulus.hmodExp_of_clock_inputs` already holds:
`QuenchedFormulation.EnvironmentWalkData e D hG` (closed almost surely in the
environment by `Recurrence/AreaClockAdmissibleDischarge.ae_environmentWalkData`,
from mass transport and the (FE) moment) and the first clause of
`InvarianceAssembly.PathwiseClockClauses`.  So the `hdense` slot of `hmodExp` is
**not** an independent open atom.

Nothing here certifies compact containment, `harray`, or tightness.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.RightDenseVertexTimesProducer

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement
open ReflectedWalk QuenchedFormulation
open ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.CorrectorInterpolationTransfer
open ReflectedGMS.InvarianceAssembly

/-! ## The topological step -/

/-- **Density implies right-density on `ℝ≥0`.**  `𝓝[>] t` is a `NeBot` filter for
every `t : ℝ≥0` (`nhdsGT_neBot`), so every one of its members contains a nonempty
open set, which a dense set must meet. -/
theorem rightDenseVertexTimes_of_dense {V : Type*} (F : IndexedCells V)
    (X : ℝ≥0 → State F) (hdense : Dense {t : ℝ≥0 | ∃ v, X t = Sum.inl v}) :
    RightDenseVertexTimes F X := by
  intro t
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨W, hWopen, htW, hWsub⟩ := mem_nhdsWithin.1 hU
  have hmem : W ∩ Set.Ioi t ∈ 𝓝[>] t :=
    Filter.inter_mem (nhdsWithin_le_nhds (hWopen.mem_nhds htW)) self_mem_nhdsWithin
  have hne : (W ∩ Set.Ioi t).Nonempty := Filter.nonempty_of_mem hmem
  obtain ⟨s, hsS, hsW⟩ := hdense.exists_mem_open (hWopen.inter isOpen_Ioi) hne
  exact ⟨s, hWsub hsW, hsS⟩

/-! ## The almost-sure statement at the area clock -/

/-- **Almost-sure right-density of the vertex times of the exponential-area-clock
lift.**  The canonical process family `Existence.processFamily D hG (areaRate …)`
has `P start` definitionally `areaSampleLaw (decode e) D hG start` and `X`
definitionally `exponentialAreaPath (decode e) D`, so
`SpatialInfinityAvoidance.dense_vertices_ae_of_isReflectedWalk` applies verbatim
to a lift `Xexp` collapsing onto it. -/
theorem ae_rightDenseVertexTimes_of_isReflectedWalk (e : Env)
    [Nontrivial (Vertex e.val)] (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (start : Vertex e.val)
    {hmin : (decode e).graph.EnergyMinimizer}
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (hcollapse : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω) := by
  filter_upwards [SpatialInfinityAvoidance.dense_vertices_ae_of_isReflectedWalk
    (decode e) (Existence.processFamily D hG (areaRate (decode e))) hwalk start Xexp
    hcollapse] with ω hω
  exact rightDenseVertexTimes_of_dense (decode e) (fun t => Xexp t ω) hω

/-- **The `hdense` slot of `ActualWindowModulus.hmodExp_of_clock_inputs`, from the
environment walk data and the clock clauses.**  `EnvironmentWalkData` carries the
`IsReflectedWalk` witness for the area rate; clause 1 of `PathwiseClockClauses`
is the collapse identity. -/
theorem ae_rightDenseVertexTimes_of_walkData (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω) := by
  obtain ⟨hmin, _hrate, hwalk, _⟩ := hdata
  exact ae_rightDenseVertexTimes_of_isReflectedWalk e D hG start hwalk Xexp
    (hclock.mono fun _ h => h.1)

/-- **Integration check.**  The producer really does fill the `hdense` slot of
`ActualWindowModulus.hmodExp_of_clock_inputs`: the partial application below
elaborates, leaving exactly the atoms this module does not discharge. -/
example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hcont : ActualWindowModulus.CompactContainment e D hG z start Xexp)
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (WindowModulusGridTransfer.LocalizedMartingaleArray
          (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) : True := by
  have _fits := ActualWindowModulus.hmodExp_of_clock_inputs e D hG z Φ start Xexp Xexact
    M hclock hz hsub hdiam
    (ae_rightDenseVertexTimes_of_walkData e D hG Φ start Xexp Xexact M hdata hclock)
    hcont harray
  trivial

end ReflectedGMS.RightDenseVertexTimesProducer

end Merged_RightDenseVertexTimesProducer

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CompactContainmentProducer

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement
open ReflectedWalk QuenchedFormulation
open ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.CorrectorInterpolationTransfer
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.ActualWindowModulus
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.WindowModulusUniformScales
open ReflectedGMS.RightDenseVertexTimesProducer

/-! ## Two elementary helpers -/

/-- For every real `c` and every positive `τ : ℝ≥0∞` there is a nonzero `b : ℝ≥0`
with `ofReal c ≤ τ * b²`.  This is the "choose the Doob radius after the
probability level, before the scale" step. -/
theorem exists_nnreal_le_mul_sq (c : ℝ) {τ : ℝ≥0∞} (hτ : 0 < τ) :
    ∃ b : ℝ≥0, b ≠ 0 ∧ ENNReal.ofReal c ≤ τ * (b : ℝ≥0∞) ^ 2 := by
  rcases eq_or_ne τ ⊤ with rfl | hτtop
  · exact ⟨1, one_ne_zero, by simp⟩
  · lift τ to ℝ≥0 using hτtop with t
    have ht0 : (0 : ℝ≥0) < t := by exact_mod_cast hτ
    have ht : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    obtain ⟨N, hN⟩ := Archimedean.arch c ht
    simp only [nsmul_eq_mul] at hN
    refine ⟨(N : ℝ≥0) + 1, ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self), ?_⟩
    rw [show ENNReal.ofReal c = ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) from rfl,
      ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
      Real.toNNReal_le_iff_le_coe]
    push_cast
    have hsq : (0 : ℝ) ≤ (t : ℝ) * (N : ℝ) ^ 2 := by positivity
    have hlin : (0 : ℝ) ≤ (t : ℝ) * (N : ℝ) := by positivity
    nlinarith [hN, ht.le, hsq, hlin]

/-- **A bound on the corrector forces a bound on the representative.**  At
tolerance `1/2` the sublinear error is at most half the radius already reached by
the representative, so `‖z v‖ ≤ max R₀ (2‖Φ v‖)` with `R₀` depending only on
`hsub`. -/
theorem exists_bound_norm_representative {V : Type*} (F : IndexedCells V)
    (Φ zz : V → Plane) (hz : CellRepresentatives F zz)
    (hsub : UniformlySublinearError F Φ zz) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ v : V, ‖zz v‖ ≤ max R₀ (2 * ‖Φ v‖) := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hsub (1 / 2) (by norm_num)
  refine ⟨R₀, hR₀pos, fun v => ?_⟩
  by_cases hle : ‖zz v‖ ≤ R₀
  · exact le_max_of_le_left hle
  · push_neg at hle
    have hHits : Hits F (Metric.closedBall (0 : Plane) ‖zz v‖) v :=
      ⟨zz v, hz v, by simp⟩
    have hbound := hR₀ ‖zz v‖ hle.le v hHits
    have hsplit : ‖zz v‖ ≤ ‖Φ v‖ + ‖Φ v - zz v‖ := by
      have h : Φ v - (Φ v - zz v) = zz v := by abel
      calc ‖zz v‖ = ‖Φ v - (Φ v - zz v)‖ := by rw [h]
        _ ≤ ‖Φ v‖ + ‖Φ v - zz v‖ := norm_sub_le _ _
    exact le_max_of_le_right (by linarith)

/-! ## The Doob step for one row of a localized martingale array -/

/-- **Doob at the horizon, transported to the array's target process.**  The
terminal second-moment constant `A.C` is uniform in the row, so the exceedance
probability of the target `X n` is at most `τ + τ` as soon as `ofReal A.C ≤ τ b²`
and the row agrees with the target up to probability `τ`. -/
theorem measure_exceed_le_of_array {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → ℝ≥0 → Ω → ℝ} {Hor : ℝ≥0}
    (A : LocalizedMartingaleArray P X Hor) (n : ℕ) {b : ℝ≥0} (hb : b ≠ 0)
    {τ : ℝ≥0∞} (hC : ENNReal.ofReal A.C ≤ τ * (b : ℝ≥0∞) ^ 2)
    (hagree : P {ω | ∃ t ≤ Hor, A.Y n t ω ≠ X n t ω} ≤ τ) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) Hor, (b : ℝ) < |X n t ω|} ≤ τ + τ := by
  have hmax : (b : ℝ≥0∞) ^ 2 *
      P {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) Hor, (b : ℝ) < |A.Y n t ω|}
        ≤ ENNReal.ofReal A.C :=
    le_trans (continuous_time_abs_maximal (A.martingale n) (fun t => A.memLp n t)
      (A.cadlag n) Hor b) (ENNReal.ofReal_le_ofReal (A.terminal n))
  have hb0 : ((b : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero 2 (ENNReal.coe_ne_zero.2 hb)
  have hbt : ((b : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hY : P {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) Hor, (b : ℝ) < |A.Y n t ω|} ≤ τ := by
    have hdiv : P {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) Hor, (b : ℝ) < |A.Y n t ω|}
        ≤ ENNReal.ofReal A.C / (b : ℝ≥0∞) ^ 2 :=
      (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt)).2 (by rwa [mul_comm] at hmax)
    exact le_trans hdiv (ENNReal.div_le_of_le_mul hC)
  have hsubset : {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) Hor, (b : ℝ) < |X n t ω|} ⊆
      {ω | ∃ t ≤ Hor, A.Y n t ω ≠ X n t ω} ∪
      {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) Hor, (b : ℝ) < |A.Y n t ω|} := by
    rintro ω ⟨t, ht, hlt⟩
    by_cases hEq : A.Y n t ω = X n t ω
    · exact Or.inr ⟨t, ht, by rwa [hEq]⟩
    · exact Or.inl ⟨t, ht.2, hEq⟩
  exact le_trans (measure_mono hsubset)
    (le_trans (measure_union_le _ _) (add_le_add hagree hY))

/-! ## Compact containment -/

/-- **`ActualWindowModulus.CompactContainment` from the localized martingale
arrays.**  `R := max R₀ (4 b)` is chosen before the scale index `n`: `R₀` depends
only on the corrector sublinearity and `b` only on the arrays' terminal
second-moment constants and on `η`.

Conditional on `hz`, `hsub`, `hM` and `harray` only — every one of which is
already a hypothesis of `ActualWindowModulus.hmodExp_of_inputs`. -/
theorem compactContainment_of_arrays (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hM : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω))
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    CompactContainment e D hG z start Xexp := by
  intro ε hεpos hεlim H η hη
  obtain ⟨R₀, hR₀pos, hrep⟩ :=
    exists_bound_norm_representative (decode e) (Φ.at e) (z.at e) (fun v => hz e v) hsub
  have hη₀pos : (0 : ℝ≥0∞) < min η 1 := lt_min hη (by norm_num)
  have hτpos : (0 : ℝ≥0∞) < min η 1 / 4 := ENNReal.div_pos hη₀pos.ne' (by norm_num)
  obtain ⟨A0⟩ := harray ε hεpos hεlim 0 H
  obtain ⟨A1⟩ := harray ε hεpos hεlim 1 H
  obtain ⟨b, hbne, hbC⟩ := exists_nnreal_le_mul_sq (max A0.C A1.C) hτpos
  have hnull : (areaSampleLaw (decode e) D hG start)
      {ω | ¬ IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
        (fun t => M t ω)} = 0 := ae_iff.1 hM
  refine ⟨max R₀ (4 * (b : ℝ)), le_trans hR₀pos.le (le_max_left _ _), ?_⟩
  have hcoe : Tendsto (fun n => ((ε n : ℝ))) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 hεlim
  have hε1 : ∀ᶠ n in atTop, ((ε n : ℝ)) ≤ 1 :=
    ((tendsto_order.1 hcoe).2 1 (by norm_num)).mono fun _ h => h.le
  have hag0 := (ENNReal.tendsto_nhds_zero.1 A0.agree) (min η 1 / 4) hτpos
  have hag1 := (ENNReal.tendsto_nhds_zero.1 A1.agree) (min η 1 / 4) hτpos
  filter_upwards [hε1, hag0, hag1] with n hn1 hn0 hnn1
  have hεn : (0 : ℝ≥0) < ε n := hεpos n
  have hεR : (0 : ℝ) < (ε n : ℝ) := by exact_mod_cast hεn
  have hb0 : (areaSampleLaw (decode e) D hG start)
      {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) H,
        (b : ℝ) < |(ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * t) ω 0|}
      ≤ min η 1 / 4 + min η 1 / 4 :=
    measure_exceed_le_of_array A0 n hbne
      (le_trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hbC) hn0
  have hb1 : (areaSampleLaw (decode e) D hG start)
      {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) H,
        (b : ℝ) < |(ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * t) ω 1|}
      ≤ min η 1 / 4 + min η 1 / 4 :=
    measure_exceed_le_of_array A1 n hbne
      (le_trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)) hbC) hnn1
  have hsubset : {ω | ¬ ∀ (s : ℝ≥0) (v : Vertex e.val), s < (ε n)⁻¹ ^ 2 * H →
        Xexp s ω = Sum.inl v → ‖z.at e v‖ ≤ (max R₀ (4 * (b : ℝ))) / (ε n : ℝ)} ⊆
      {ω | ¬ IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
        (fun t => M t ω)} ∪
      ({ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) H,
          (b : ℝ) < |(ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * t) ω 0|} ∪
       {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) H,
          (b : ℝ) < |(ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * t) ω 1|}) := by
    intro ω hω
    by_cases hext : IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
        (fun t => M t ω)
    · refine Or.inr ?_
      by_cases h0 : ∃ t ∈ Set.Icc (0 : ℝ≥0) H,
          (b : ℝ) < |(ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * t) ω 0|
      · exact Or.inl h0
      by_cases h1 : ∃ t ∈ Set.Icc (0 : ℝ≥0) H,
          (b : ℝ) < |(ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * t) ω 1|
      · exact Or.inr h1
      exfalso
      apply hω
      push_neg at h0 h1
      intro s v hs hXs
      -- the rescaled time of `s`
      have hkey : ((ε n : ℝ)) ^ 2 * ((((ε n : ℝ)))⁻¹ ^ 2 * (H : ℝ)) = (H : ℝ) := by
        field_simp
      have hsR : (s : ℝ) < (((ε n : ℝ)))⁻¹ ^ 2 * (H : ℝ) := by
        have h := hs
        rw [← NNReal.coe_lt_coe] at h
        push_cast at h
        exact h
      have hεsq : (0 : ℝ) < ((ε n : ℝ)) ^ 2 := by positivity
      have htHR : ((ε n : ℝ)) ^ 2 * (s : ℝ) ≤ (H : ℝ) := by
        have h := mul_lt_mul_of_pos_left hsR hεsq
        rw [hkey] at h
        exact h.le
      have htH : (ε n) ^ 2 * s ≤ H := by
        rw [← NNReal.coe_le_coe]
        push_cast
        exact htHR
      have hst : ((ε n)⁻¹ : ℝ≥0) ^ 2 * ((ε n) ^ 2 * s) = s := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hεn.ne', one_pow, one_mul]
      have hM0 := h0 ((ε n) ^ 2 * s) ⟨by positivity, htH⟩
      have hM1 := h1 ((ε n) ^ 2 * s) ⟨by positivity, htH⟩
      rw [hst] at hM0 hM1
      have hMv : M s ω = (Φ.at e) v := hext.2.1 s v hXs
      rw [hMv] at hM0 hM1
      have hc0 : (ε n : ℝ) * |(Φ.at e) v 0| ≤ (b : ℝ) := by
        calc (ε n : ℝ) * |(Φ.at e) v 0| = |(ε n : ℝ) * (Φ.at e) v 0| := by
              rw [abs_mul, abs_of_nonneg hεR.le]
          _ ≤ (b : ℝ) := hM0
      have hc1 : (ε n : ℝ) * |(Φ.at e) v 1| ≤ (b : ℝ) := by
        calc (ε n : ℝ) * |(Φ.at e) v 1| = |(ε n : ℝ) * (Φ.at e) v 1| := by
              rw [abs_mul, abs_of_nonneg hεR.le]
          _ ≤ (b : ℝ) := hM1
      have hnormbd : (ε n : ℝ) * ‖(Φ.at e) v‖ ≤ 2 * (b : ℝ) := by
        have hn := WindowModulusGridTransfer.norm_le_abs_zero_add_abs_one ((Φ.at e) v)
        have hstep : (ε n : ℝ) * ‖(Φ.at e) v‖
            ≤ (ε n : ℝ) * (|(Φ.at e) v 0| + |(Φ.at e) v 1|) :=
          mul_le_mul_of_nonneg_left hn hεR.le
        rw [mul_add] at hstep
        linarith
      rw [le_div_iff₀ hεR]
      rcases le_max_iff.1 (hrep v) with hcase | hcase
      · have hmul : ‖z.at e v‖ * (ε n : ℝ) ≤ R₀ * 1 :=
          mul_le_mul hcase hn1 hεR.le hR₀pos.le
        linarith [le_max_left R₀ (4 * (b : ℝ))]
      · have hmul : ‖z.at e v‖ * (ε n : ℝ) ≤ (2 * ‖(Φ.at e) v‖) * (ε n : ℝ) :=
          mul_le_mul_of_nonneg_right hcase hεR.le
        have hrw : (2 * ‖(Φ.at e) v‖) * (ε n : ℝ)
            = 2 * ((ε n : ℝ) * ‖(Φ.at e) v‖) := by ring
        rw [hrw] at hmul
        linarith [le_max_right R₀ (4 * (b : ℝ))]
    · exact Or.inl hext
  refine le_trans (measure_mono hsubset) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [hnull, zero_add]
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add hb0 hb1) ?_
  have h4 : (min η 1 / 4 + min η 1 / 4) + (min η 1 / 4 + min η 1 / 4)
      = 4 * (min η 1 / 4) := by ring
  rw [h4]
  exact le_trans ENNReal.mul_div_le (min_le_left _ _)

/-! ## `hmodExp` from the clock clauses, the walk data and the arrays -/

/-- **The `hmodExp` slot of
`TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
at `T := Set.Ioc 0 1`, with compact containment and right-density discharged.**

Compared with `ActualWindowModulus.hmodExp_of_clock_inputs` this drops both
`hdense` and `hcont`: right-density comes from
`RightDenseVertexTimesProducer.ae_rightDenseVertexTimes_of_walkData` and compact
containment from `compactContainment_of_arrays`.  The only remaining probabilistic
input is `harray`. -/
theorem hmodExp_of_clock_inputs_and_arrays (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp)
        (Set.Ioc 0 1) :=
  hmodExp_of_clock_inputs e D hG z Φ start Xexp Xexact M hclock hz hsub hdiam
    (ae_rightDenseVertexTimes_of_walkData e D hG Φ start Xexp Xexact M hdata hclock)
    (compactContainment_of_arrays e D hG z Φ start Xexp M hz hsub
      (Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1) harray)
    harray

/-- **Integration check.**  `hmodExp_of_clock_inputs_and_arrays` fills the
`hmodExp` slot of
`TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
at `T := Set.Ioc 0 1`; the partial application below elaborates, leaving exactly
`hmodExact`, `hfddExp` and `hfddExact`. -/
example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) : True := by
  have _fits := twoClockScalingLimit_of_window_modulus_of_finiteDimensional e D hG z Φ
    target start Xexp Xexact M hclock (Set.Ioc 0 1) Ioc_zero_one_mem_nhdsWithin
    (hmodExp_of_clock_inputs_and_arrays e D hG z Φ start Xexp Xexact M hdata hclock hz
      hsub hdiam harray)
  trivial

end ReflectedGMS.CompactContainmentProducer
