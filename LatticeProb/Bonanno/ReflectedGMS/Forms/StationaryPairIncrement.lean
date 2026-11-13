/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryPairIncrement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPotentialVariance
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupEnergyBound
import LatticeProb.Bonanno.ReflectedGMS.Forms.CadlagJumpPartitionFatou
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide

/-!
# Stationary two-time law and the dyadic partition square sums

Under the unnormalised stationary speed law `P_m = ∑ m(z) P_z`, the pair `(X_t, X_{t+s})` has
the same law as `(X_0, X_s)`: the deterministic-time Markov property (Lemma 3.10 at a constant
stopping time) factorises the pair probability through `P_x(X_s = b)`, and the one-time
marginal is `m` at every time.  Consequently the expected squared increment of every weighted
`L²` vector over `[t, t + s]` equals `2(‖U‖² − ⟪U, P_s U⟫)`, which the semigroup energy bound
dominates by `2 s 𝓔(U)`.

Summing over the dyadic partition of `[0, T]` gives `E_m[∑_i (ΔU)²] ≤ 2 T 𝓔(U)` uniformly in
the mesh, and Fatou's lemma bounds the expectation of the `liminf` of the partition square
sums.  This is the **upper** half of the energy budget for the nonvertex-time continuity of
the full-energy potential paths.  Nothing here concerns jumps or boundary times.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace ReflectedGMS.StationaryPairIncrement

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open ReflectedGMS.CadlagJumpPartitionFatou

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The speed mixture evaluated on a measurable set is the speed-weighted series of the
starting laws. -/
theorem reflectedSpeedLaw_apply_eq_tsum (PF : ProcessFamily V) (m : V → ℝ)
    {A : Set PF.Ω} (hA : MeasurableSet A) :
    reflectedSpeedLaw PF m A = ∑' z, ENNReal.ofReal (m z) * PF.P z A := by
  unfold reflectedSpeedLaw reflectedStartKernel
  rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ hA]
  simp only [vertexSpeedMeasure_singleton, Measure.smul_apply, smul_eq_mul]
  rfl

section Markov

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- **The Markov property at a deterministic time, for one pair of positions.**  This is
Lemma 3.10 at the constant stopping time `t`, evaluated on the cylinder `{X_s = b}`. -/
theorem measure_pair_eq_mul (h : IsReflectedWalk G w hmin PF) (z x : V) (t s : ℝ≥0)
    (b : Option V) :
    PF.P z {ω | PF.X t ω = some x ∧ PF.X (t + s) ω = b} =
      PF.P z {ω | PF.X t ω = some x} * PF.P x {ω | PF.X s ω = b} := by
  have hR : RightContinuousAtInfty (PF.P z) PF.X := (h z).2.2.2.1
  let τ : PF.Ω → WithTop ℝ≥0 := fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)
  have hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ :=
    isAEStoppingTime_const PF.measurable_X t
  have hB : MeasurableSet {γ : Trajectory V | γ s = b} := by
    have hB' : MeasurableSet ((fun γ : Trajectory V => γ s) ⁻¹' {b}) :=
      measurable_pi_apply s (measurableSet_singleton b)
    exact hB'
  have hSM := strongMarkov_completed h z hR (τ := τ) aemeasurable_const hτ x
    (aemeasurableSetStopped_univ hτ) hB
  have hτω : ∀ ω, τ ω = (t : WithTop ℝ≥0) := fun _ => rfl
  have hfut : ∀ ω, futureAt PF.X τ ω s = PF.X (t + s) ω := by
    intro ω
    show PF.X (s + (τ ω).untopA) ω = PF.X (t + s) ω
    rw [hτω ω, untopA_coe, add_comm]
  have hstop : ∀ ω, ω ∈ stopEvent PF.X τ x ↔ PF.X t ω = some x := by
    intro ω
    show τ ω ≠ ⊤ ∧ stoppedValue PF.X τ ω = some x ↔ _
    rw [stoppedValue_of_eq (hτω ω), hτω ω]
    exact ⟨fun hh => hh.2, fun hh => ⟨WithTop.coe_ne_top, hh⟩⟩
  have h1 : Set.univ ∩ stopEvent PF.X τ x ∩ futureAt PF.X τ ⁻¹' {γ | γ s = b} =
      {ω | PF.X t ω = some x ∧ PF.X (t + s) ω = b} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_setOf_eq,
      hfut, hstop]
  have h2 : Set.univ ∩ stopEvent PF.X τ x = {ω | PF.X t ω = some x} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq, hstop]
  have h3 : PF.law x {γ | γ s = b} = PF.P x {ω | PF.X s ω = b} := by
    have htraj : Measurable PF.trajectory := measurable_pi_iff.mpr PF.measurable_X
    rw [ProcessFamily.law, Measure.map_apply htraj hB]
    rfl
  rw [h1, h2, h3] at hSM
  exact hSM

/-- A fixed time is almost surely a vertex time, so the `none` fibre is null. -/
theorem measure_none_eq_zero (h : IsReflectedWalk G w hmin PF) (z : V) (t : ℝ≥0) :
    PF.P z {ω | PF.X t ω = none} = 0 := by
  have hae : ∀ᵐ ω ∂PF.P z, ¬ (PF.X t ω = none) := by
    filter_upwards [(h z).2.1 t] with ω hω hn
    obtain ⟨x, hx⟩ := hω.1
    rw [hn] at hx
    exact Option.some_ne_none x hx.symm
  rw [ae_iff] at hae
  simpa only [not_not] using hae

end Markov

section Stationary

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v) (hmsum : Summable m)

include h hG hm hmsum

/-- The one-time marginal of the speed mixture at a vertex is its speed mass. -/
theorem reflectedSpeedLaw_vertex_eq (t : ℝ≥0) (x : V) :
    reflectedSpeedLaw PF m {ω | PF.X t ω = some x} = ENNReal.ofReal (m x) := by
  have hpre : {ω | PF.X t ω = some x} = PF.X t ⁻¹' {some x} := by
    ext ω
    simp
  rw [hpre, ← Measure.map_apply (PF.measurable_X t) (measurableSet_singleton _),
    reflectedSpeedLaw_map_position h hG hm hmsum t,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre' : (some : V → Option V) ⁻¹' {some x} = {x} := by
    ext y
    simp
  rw [hpre', vertexSpeedMeasure_singleton]

/-- **Two-time cylinder mass under the speed mixture.**  Stationarity of the one-time
marginal combined with the deterministic-time Markov property. -/
theorem reflectedSpeedLaw_pair_eq (t s : ℝ≥0) (x : V) (b : Option V) :
    reflectedSpeedLaw PF m {ω | PF.X t ω = some x ∧ PF.X (t + s) ω = b} =
      ENNReal.ofReal (m x) * PF.P x {ω | PF.X s ω = b} := by
  have hmeas : MeasurableSet {ω | PF.X t ω = some x ∧ PF.X (t + s) ω = b} :=
    ((PF.measurable_X t) (measurableSet_singleton _)).inter
      ((PF.measurable_X (t + s)) (measurableSet_singleton _))
  have hm1 : MeasurableSet {ω | PF.X t ω = some x} :=
    (PF.measurable_X t) (measurableSet_singleton (some x))
  rw [reflectedSpeedLaw_apply_eq_tsum PF m hmeas]
  simp_rw [measure_pair_eq_mul h _ x t s b, ← mul_assoc]
  rw [ENNReal.tsum_mul_right, ← reflectedSpeedLaw_apply_eq_tsum PF m hm1,
    reflectedSpeedLaw_vertex_eq h hG hm hmsum]

/-- The `none` fibre is null under the speed mixture as well. -/
theorem reflectedSpeedLaw_none_eq_zero (t : ℝ≥0) :
    reflectedSpeedLaw PF m {ω | PF.X t ω = none} = 0 := by
  have hm0 : MeasurableSet {ω | PF.X t ω = none} :=
    (PF.measurable_X t) (measurableSet_singleton none)
  rw [reflectedSpeedLaw_apply_eq_tsum PF m hm0]
  simp only [measure_none_eq_zero h, mul_zero, tsum_zero]

/-- **The law of `(X_t, X_{t+s})` under the speed mixture does not depend on `t`.** -/
theorem map_pair_reflectedSpeedLaw_eq (t s : ℝ≥0) :
    (reflectedSpeedLaw PF m).map (fun ω => (PF.X t ω, PF.X (t + s) ω)) =
      (reflectedSpeedLaw PF m).map (fun ω => (PF.X 0 ω, PF.X s ω)) := by
  have hpair : Measurable (fun ω => (PF.X t ω, PF.X (t + s) ω)) :=
    (PF.measurable_X t).prodMk (PF.measurable_X (t + s))
  have hpair0 : Measurable (fun ω => (PF.X 0 ω, PF.X s ω)) :=
    (PF.measurable_X 0).prodMk (PF.measurable_X s)
  have hpre : ∀ (a b : Option V),
      (fun ω => (PF.X t ω, PF.X (t + s) ω)) ⁻¹' {(a, b)} =
        {ω | PF.X t ω = a ∧ PF.X (t + s) ω = b} := by
    intro a b
    ext ω
    simp
  have hpre0 : ∀ (a b : Option V),
      (fun ω => (PF.X 0 ω, PF.X s ω)) ⁻¹' {(a, b)} =
        {ω | PF.X 0 ω = a ∧ PF.X s ω = b} := by
    intro a b
    ext ω
    simp
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.map_apply hpair (measurableSet_singleton _),
    Measure.map_apply hpair0 (measurableSet_singleton _), hpre, hpre0]
  cases a with
  | none =>
      have hz : reflectedSpeedLaw PF m {ω | PF.X t ω = none ∧ PF.X (t + s) ω = b} = 0 :=
        measure_mono_null (fun ω hω => hω.1) (reflectedSpeedLaw_none_eq_zero h hG hm hmsum t)
      have hz0 : reflectedSpeedLaw PF m {ω | PF.X 0 ω = none ∧ PF.X s ω = b} = 0 :=
        measure_mono_null (fun ω hω => hω.1) (reflectedSpeedLaw_none_eq_zero h hG hm hmsum 0)
      rw [hz, hz0]
  | some x =>
      have h0 := reflectedSpeedLaw_pair_eq h hG hm hmsum 0 s x b
      rw [zero_add] at h0
      rw [reflectedSpeedLaw_pair_eq h hG hm hmsum t s x b, h0]

/-- **Stationary expected squared increment over `[t, t + s]`** for every weighted `L²`
vector: it is the value at `s` of the semigroup quadratic form deficit, independently of `t`. -/
theorem integral_sq_sub_unweight_shift (U : ValueSpace V) (t s : ℝ≥0) :
    (∫ ω, ((PF.X (t + s) ω).elim 0 (unweight m U) -
        (PF.X t ω).elim 0 (unweight m U)) ^ 2 ∂reflectedSpeedLaw PF m) =
      2 * (‖U‖ ^ 2 - ⟪U, fullFormSemigroup G m s U⟫_ℝ) := by
  let g : Option V × Option V → ℝ := fun p => (p.2.elim 0 (unweight m U) - p.1.elim 0 (unweight m U)) ^ 2
  have hg : Measurable g := measurable_of_countable g
  have hpair : Measurable (fun ω => (PF.X t ω, PF.X (t + s) ω)) :=
    (PF.measurable_X t).prodMk (PF.measurable_X (t + s))
  have hpair0 : Measurable (fun ω => (PF.X 0 ω, PF.X s ω)) :=
    (PF.measurable_X 0).prodMk (PF.measurable_X s)
  have h1 : (∫ ω, ((PF.X (t + s) ω).elim 0 (unweight m U) -
      (PF.X t ω).elim 0 (unweight m U)) ^ 2 ∂reflectedSpeedLaw PF m) =
      ∫ p, g p ∂(reflectedSpeedLaw PF m).map (fun ω => (PF.X t ω, PF.X (t + s) ω)) :=
    (integral_map hpair.aemeasurable hg.aestronglyMeasurable).symm
  have h2 : (∫ p, g p ∂(reflectedSpeedLaw PF m).map (fun ω => (PF.X 0 ω, PF.X s ω))) =
      ∫ ω, ((PF.X s ω).elim 0 (unweight m U) -
        (PF.X 0 ω).elim 0 (unweight m U)) ^ 2 ∂reflectedSpeedLaw PF m :=
    integral_map hpair0.aemeasurable hg.aestronglyMeasurable
  rw [h1, map_pair_reflectedSpeedLaw_eq h hG hm hmsum t s, h2]
  exact integral_sq_sub_unweight_reflectedSpeedLaw h hG hm hmsum U s

end Stationary

/-! ## The dyadic partition square sums of the raw vertex path -/

/-- The raw vertex path of `u` along the process, with the `none`-as-zero convention. -/
noncomputable def rawPath (PF : ProcessFamily V) (u : V → ℝ) (ω : PF.Ω) : ℝ≥0 → ℝ :=
  fun r => (PF.X r ω).elim 0 u

theorem measurable_rawPath (PF : ProcessFamily V) (u : V → ℝ) (r : ℝ≥0) :
    Measurable (fun ω => rawPath PF u ω r) :=
  (measurable_of_countable (fun q : Option V => q.elim 0 u)).comp (PF.measurable_X r)

theorem measurable_partitionSquareSum_rawPath (PF : ProcessFamily V) (u : V → ℝ) (T : ℝ≥0)
    (n : ℕ) : Measurable (fun ω => partitionSquareSum (rawPath PF u ω) T n) := by
  unfold partitionSquareSum
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_rawPath PF u _).sub (measurable_rawPath PF u _)).pow_const 2

section Partition

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v) (hmsum : Summable m)
  (U : hilbertDomain G m)

include h hG hm hmsum

/-- Each cell increment of the raw path of a Hilbert-domain vector is square integrable under
the speed mixture. -/
theorem integrable_sq_sub_rawPath (a b : ℝ≥0) :
    Integrable (fun ω => (rawPath PF (unweight m (valueInclusion G m U)) ω a -
      rawPath PF (unweight m (valueInclusion G m U)) ω b) ^ 2) (reflectedSpeedLaw PF m) := by
  have ha := memLp_two_reflected_unweight_speedLaw h hG hm hmsum (valueInclusion G m U) a
  have hb := memLp_two_reflected_unweight_speedLaw h hG hm hmsum (valueInclusion G m U) b
  have hsub := ha.sub hb
  have hmeas : AEStronglyMeasurable (fun ω => rawPath PF (unweight m (valueInclusion G m U)) ω a -
      rawPath PF (unweight m (valueInclusion G m U)) ω b) (reflectedSpeedLaw PF m) :=
    ((measurable_rawPath PF _ a).sub (measurable_rawPath PF _ b)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).1 hsub

/-- The partition square sum of the raw path is integrable. -/
theorem integrable_partitionSquareSum_rawPath (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n)
      (reflectedSpeedLaw PF m) := by
  unfold partitionSquareSum
  exact integrable_finset_sum _ fun i _ => integrable_sq_sub_rawPath h hG hm hmsum U _ _

/-- **The expected dyadic partition square sum is at most `2 T 𝓔(U)`**, uniformly in the
mesh. -/
theorem integral_partitionSquareSum_rawPath_le (T : ℝ≥0) (n : ℕ) :
    (∫ ω, partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n
        ∂reflectedSpeedLaw PF m) ≤
      (T : ℝ) * (2 * G.Energy (unweight m (valueInclusion G m U))) := by
  unfold partitionSquareSum
  rw [integral_finsetSum _ fun i _ => integrable_sq_sub_rawPath h hG hm hmsum U _ _]
  have hterm : ∀ i ∈ Finset.range (2 ^ n),
      (∫ ω, (rawPath PF (unweight m (valueInclusion G m U)) ω (dyadicPoint T n (i + 1)) -
        rawPath PF (unweight m (valueInclusion G m U)) ω (dyadicPoint T n i)) ^ 2
          ∂reflectedSpeedLaw PF m) ≤
        2 * (((T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) * G.Energy (unweight m (valueInclusion G m U))) := by
    intro i _
    rw [dyadicPoint_succ]
    have hid := integral_sq_sub_unweight_shift h hG hm hmsum (valueInclusion G m U)
      (dyadicPoint T n i) (T / (2 : ℝ≥0) ^ n)
    change (∫ ω, ((PF.X (dyadicPoint T n i + T / (2 : ℝ≥0) ^ n) ω).elim 0
      (unweight m (valueInclusion G m U)) -
        (PF.X (dyadicPoint T n i) ω).elim 0 (unweight m (valueInclusion G m U))) ^ 2
        ∂reflectedSpeedLaw PF m) ≤ _
    rw [hid]
    exact mul_le_mul_of_nonneg_left
      (fullFormSemigroup_quadratic_deficit_le_energy G m hm U (T / (2 : ℝ≥0) ^ n)) (by norm_num)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcast : ((T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) = (T : ℝ) / (2 : ℝ) ^ n := by
    rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  rw [hcast]
  push_cast
  field_simp <;> ring

/-- **Fatou over the dyadic partitions.**  The expectation under the speed mixture of the
`liminf` of the partition square sums of the raw path is at most `2 T 𝓔(U)`. -/
theorem lintegral_liminf_partitionSquareSum_rawPath_le (T : ℝ≥0) :
    (∫⁻ ω, liminf (fun n => ENNReal.ofReal
        (partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n)) atTop
        ∂reflectedSpeedLaw PF m) ≤
      ENNReal.ofReal ((T : ℝ) * (2 * G.Energy (unweight m (valueInclusion G m U)))) := by
  have hmeas : ∀ n, Measurable (fun ω => ENNReal.ofReal
      (partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n)) :=
    fun n => ENNReal.measurable_ofReal.comp (measurable_partitionSquareSum_rawPath PF _ T n)
  refine (lintegral_liminf_le hmeas).trans ?_
  have hbound : ∀ n, (∫⁻ ω, ENNReal.ofReal
      (partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n)
        ∂reflectedSpeedLaw PF m) ≤
      ENNReal.ofReal ((T : ℝ) * (2 * G.Energy (unweight m (valueInclusion G m U)))) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_partitionSquareSum_rawPath h hG hm hmsum U T n)
      (Eventually.of_forall fun ω => partitionSquareSum_nonneg _ _ _)]
    exact ENNReal.ofReal_le_ofReal (integral_partitionSquareSum_rawPath_le h hG hm hmsum U T n)
  calc liminf (fun n => ∫⁻ ω, ENNReal.ofReal
        (partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n)
          ∂reflectedSpeedLaw PF m) atTop ≤
      liminf (fun _ : ℕ => ENNReal.ofReal
        ((T : ℝ) * (2 * G.Energy (unweight m (valueInclusion G m U))))) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = _ := liminf_const _

end Partition

end ReflectedGMS.StationaryPairIncrement
