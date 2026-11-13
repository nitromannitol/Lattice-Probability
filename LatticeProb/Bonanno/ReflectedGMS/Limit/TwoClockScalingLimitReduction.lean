/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.TwoClockScalingLimitReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.InterpolatedTwoClockReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.QuenchedPathLimitReduction
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.EnvironmentWalkDataProducer

/-!
# `TwoClockScalingLimit` reduced to four atomic analytic inputs

`ReflectedGMS/Limit/InterpolatedTwoClockReduction.lean` splits the `hlimit` input of
`ReflectedGMS/InvarianceAssembly.lean` into a construction half
(`RepresentativeInterpolationData`) and an analytic half
(`InterpolatedTwoClockReduction.TwoClockScalingLimit`, manuscript `p:thm:areaclt`).
This file attacks the analytic half.

Unfolded, `TwoClockScalingLimit e D hG z target start Xexp Xexact` says: for every
pair of spatial extensions and every pair of *measurable* continuous interpolations
`Iexp`, `Iexact` satisfying the pathwise clauses,

* `Measurable Iexp`, `Measurable Iexact` — free, they are hypotheses; and
* `TwoClockQuenchedWeakLimitAtFixedStart` for the two pushforward path laws, i.e. two
  assertions `diffusivelyRescaledPathLaw μ ε ⟶ target.pathLaw` as `ε → 0⁺`.

`ReflectedGMS.MartingaleLimit.twoClockQuenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict`
already reduces the second bullet to *six* inputs: a window size tail, a window
modulus tail and finite-dimensional convergence, for each of the two clocks.  What is
new here is that **the two size tails are discharged**, leaving four:

* `hmodExp`, `hmodExact` — a uniform modulus-of-continuity tail on every bounded time
  window `[0, m]`, for the rescaled law of each clock (`RescaledWindowModulusTail`);
* `hfddExp`, `hfddExact` — convergence of every finite-dimensional distribution to
  the corresponding one of the anisotropic Brownian target
  (`RescaledFiniteDimensionalLimit`).

The size tails are discharged because a diffusively rescaled interpolation starts, at
time `0`, at `ε • z(start)`: the walk is at its starting cell at time `0` (mathlib-free:
`ReflectedWalk.Existence.ae_process_zero` together with
`ReflectedGMS.EnvironmentWalkDataProducer.areaRate_pos`, which needs no hypothesis), the
exact clock is at the same place by the time-change clause of `PathwiseClockClauses`, and
a continuous interpolation is pinned to the representative at the left endpoint of its
first complete holding interval.  With a deterministic starting point, the window size
bound follows from the window modulus bound by chaining `N ≈ m/d` steps
(`halfLineSizeFailure_subset_of_modulus`).

**This file certifies neither `p:thm:areaclt`, nor `hlimit`, nor either main theorem.**
Both remaining inputs are genuinely open in this development: a full sweep of the
`Limit/` modulus track found no producer of `hmod` (all checked modulus work lives on
`C(Set.Icc (0:ℝ) T, ℝ)`, scalar-valued, indexed by `atTop : Filter ℕ`), and no bridge at
all from the martingale-CLT lane to `hfdd` (that lane is scalar-valued with a scalar
rate, and every weak convergence of prelimit path laws in the corpus is a hypothesis).

## Main results

* `dist_apply_le_of_notMem_halfLineModulusFailure`, `halfLineSizeFailure_subset_of_modulus`
  — the deterministic chaining step.
* `halfLineSize_tail_of_modulus_tail_of_start_tail` — the window size tail from the
  window modulus tail and an initial-point tail, for an arbitrary family of laws.
* `continuousInterpolation_apply_zero`, `ae_interpolation_apply_zero` — the interpolation
  starts at the representative of the starting cell, almost surely.
* `rescaled_start_failure_eq_zero`, `rescaled_size_tail_of_modulus_tail` — the initial
  point tail is vacuous for the rescaled laws, hence the size tail is free.
* `twoClockScalingLimit_of_window_modulus_of_finiteDimensional` — the reduction.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.TwoClockScalingLimitReduction

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit

/-! ## Chaining: a window size bound out of a window modulus bound -/

section HalfLine

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- `n` consecutive steps of size at most `c` move a point by at most `n * c`. -/
theorem dist_le_of_chain (g : ℕ → E) (c : ℝ) : ∀ n : ℕ,
    (∀ i, i < n → dist (g (i + 1)) (g i) ≤ c) → dist (g n) (g 0) ≤ (n : ℝ) * c := by
  intro n
  induction n with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro h
      have hk : dist (g k) (g 0) ≤ (k : ℝ) * c :=
        ih fun i hi => h i (Nat.lt_succ_of_lt hi)
      have hstep : dist (g (k + 1)) (g k) ≤ c := h k (Nat.lt_succ_self k)
      have htri : dist (g (k + 1)) (g 0) ≤ dist (g (k + 1)) (g k) + dist (g k) (g 0) :=
        dist_triangle _ _ _
      have hring : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
      push_cast
      linarith

/-- **A path with no `(c, d)`-oscillation on the window `[0, m]` moves by at most
`N * c` from its starting point**, for any `N` with `m < N * d`.  The subdivision of
`[0, t]` into `N` equal pieces has mesh `t / N ≤ m / N < d`. -/
theorem dist_apply_le_of_notMem_halfLineModulusFailure
    {m : ℕ} {c d : ℝ} {N : ℕ} (hN : (m : ℝ) < (N : ℝ) * d)
    {f : C(ℝ≥0, E)} (hf : f ∉ halfLineModulusFailure (E := E) m c d)
    {t : ℝ≥0} (ht : t ≤ (m : ℝ≥0)) :
    dist (f t) (f 0) ≤ (N : ℝ) * c := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · rw [Nat.cast_zero, zero_mul] at hN
      linarith
    · exact h
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have htR : (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast ht
  have htnn : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
  have hpt : ∀ i : ℕ,
      (((i : ℝ≥0) * t / (N : ℝ≥0) : ℝ≥0) : ℝ) = (i : ℝ) * (t : ℝ) / (N : ℝ) := by
    intro i
    rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
  have hmem : ∀ i : ℕ, i ≤ N → (i : ℝ≥0) * t / (N : ℝ≥0) ≤ (m : ℝ≥0) := by
    intro i hi
    have hiN : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have h1 : (i : ℝ) * (t : ℝ) / (N : ℝ) ≤ (m : ℝ) := by
      rw [div_le_iff₀ hNR]
      calc (i : ℝ) * (t : ℝ) = (t : ℝ) * (i : ℝ) := mul_comm _ _
        _ ≤ (t : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left hiN htnn
        _ ≤ (m : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right htR hNR.le
    have h2 : (((i : ℝ≥0) * t / (N : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((m : ℝ≥0) : ℝ) := by
      rw [hpt i, NNReal.coe_natCast]
      exact h1
    exact_mod_cast h2
  have hspace : ∀ i : ℕ,
      dist (((i + 1 : ℕ) : ℝ≥0) * t / (N : ℝ≥0)) ((i : ℝ≥0) * t / (N : ℝ≥0)) < d := by
    intro i
    have hnum : ((i + 1 : ℕ) : ℝ) * (t : ℝ) = (i : ℝ) * (t : ℝ) + (t : ℝ) := by
      push_cast
      ring
    have hdiff : ((i + 1 : ℕ) : ℝ) * (t : ℝ) / (N : ℝ) - (i : ℝ) * (t : ℝ) / (N : ℝ)
        = (t : ℝ) / (N : ℝ) := by
      rw [hnum, add_div]
      ring
    rw [NNReal.dist_eq, hpt (i + 1), hpt i, hdiff,
      abs_of_nonneg (div_nonneg htnn hNR.le), div_lt_iff₀ hNR]
    calc (t : ℝ) ≤ (m : ℝ) := htR
      _ < (N : ℝ) * d := hN
      _ = d * (N : ℝ) := mul_comm _ _
  have hnot : ∀ s : ℝ≥0, s ≤ (m : ℝ≥0) → ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) → dist s u < d →
      dist (f s) (f u) ≤ c := by
    intro s hs u hu hsu
    by_contra hcon
    exact hf ⟨s, hs, u, hu, hsu, lt_of_not_ge hcon⟩
  have hfull : (N : ℝ≥0) * t / (N : ℝ≥0) = t := by
    have hc : (((N : ℝ≥0) * t / (N : ℝ≥0) : ℝ≥0) : ℝ) = (t : ℝ) := by
      rw [hpt N, mul_comm, mul_div_assoc, div_self hNne, mul_one]
    exact_mod_cast hc
  have hchain := dist_le_of_chain (fun i : ℕ => f ((i : ℝ≥0) * t / (N : ℝ≥0))) c N
    (fun i hi => hnot _ (hmem (i + 1) hi) _ (hmem i hi.le) (hspace i))
  simp only [Nat.cast_zero, zero_mul, zero_div] at hchain
  rw [hfull] at hchain
  exact hchain

/-- **The window size failure is contained in the window modulus failure together with
an initial-point failure.** -/
theorem halfLineSizeFailure_subset_of_modulus (e₀ : E) {m : ℕ} {c d : ℝ} {N : ℕ}
    (hN : (m : ℝ) < (N : ℝ) * d) (r : ℝ) :
    halfLineSizeFailure e₀ m (r + (N : ℝ) * c) ⊆
      halfLineModulusFailure (E := E) m c d ∪
        {f : C(ℝ≥0, E) | r < dist (f 0) e₀} := by
  intro f hfsize
  simp only [halfLineSizeFailure, Set.mem_setOf_eq] at hfsize
  by_contra hcon
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq] at hcon
  obtain ⟨hmodf, hstartf⟩ := hcon
  obtain ⟨t, ht, hlt⟩ := hfsize
  have h1 : dist (f t) (f 0) ≤ (N : ℝ) * c :=
    dist_apply_le_of_notMem_halfLineModulusFailure hN hmodf ht
  have h2 : dist (f 0) e₀ ≤ r := not_lt.mp hstartf
  have htri : dist (f t) e₀ ≤ dist (f t) (f 0) + dist (f 0) e₀ := dist_triangle _ _ _
  linarith

/-- **The window size tail follows from the window modulus tail and an initial-point
tail**, uniformly over an arbitrary index set `T`.  No measurability of the failure sets
is used, only monotonicity and subadditivity. -/
theorem halfLineSize_tail_of_modulus_tail_of_start_tail {ι : Type*} (e₀ : E)
    (ν : ι → Measure C(ℝ≥0, E)) (T : Set ι)
    (hmod : ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ i ∈ T,
      ν i (halfLineModulusFailure (E := E) m c d) ≤ η)
    (hstart : ∀ η : ℝ≥0∞, 0 < η → ∃ r : ℝ, ∀ i ∈ T,
      ν i {f : C(ℝ≥0, E) | r < dist (f 0) e₀} ≤ η)
    (m : ℕ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ R : ℝ, ∀ i ∈ T, ν i (halfLineSizeFailure e₀ m R) ≤ η := by
  have hhalf : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨d, hd, hdT⟩ := hmod m 1 one_pos (η / 2) hhalf
  obtain ⟨r, hrT⟩ := hstart (η / 2) hhalf
  obtain ⟨N, hNlt⟩ := exists_nat_gt ((m : ℝ) / d)
  have hN : (m : ℝ) < (N : ℝ) * d := (div_lt_iff₀ hd).mp hNlt
  refine ⟨r + (N : ℝ) * 1, fun i hi => ?_⟩
  calc ν i (halfLineSizeFailure e₀ m (r + (N : ℝ) * 1))
      ≤ ν i (halfLineModulusFailure (E := E) m 1 d ∪
          {f : C(ℝ≥0, E) | r < dist (f 0) e₀}) :=
        measure_mono (halfLineSizeFailure_subset_of_modulus e₀ hN r)
    _ ≤ ν i (halfLineModulusFailure (E := E) m 1 d) +
          ν i {f : C(ℝ≥0, E) | r < dist (f 0) e₀} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hdT i hi) (hrT i hi)
    _ = η := ENNReal.add_halves η

end HalfLine

/-! ## The interpolation starts at the representative of the starting cell -/

/-- A state collapsing to an actual vertex is that vertex. -/
theorem eq_inl_of_collapse_eq_some {V : Type*} {F : IndexedCells V} {x : State F} {v : V}
    (h : collapse x = some v) : x = Sum.inl v := by
  cases x with
  | inl u =>
      have hu : u = v := by simpa [collapse] using h
      rw [hu]
  | inr w => simp [collapse] at h

/-- **A continuous interpolation sits at the representative of the occupied cell at time
`0`.**  Time `0` lies in a complete holding interval whose left endpoint is `0` by
minimality in `ℝ≥0`, and the affine interpolation formula at parameter `0` returns the
left representative. -/
theorem continuousInterpolation_apply_zero {V : Type*} {F : IndexedCells V}
    {ζ : V → Plane} {X : ℝ≥0 → State F} {Z Ztilde : ℝ≥0 → Plane}
    (hI : IsContinuousInterpolation F ζ X Z Ztilde) {v : V} (h0 : X 0 = Sum.inl v) :
    Ztilde 0 = ζ v := by
  obtain ⟨s, u, w, hHI, hmem⟩ := hI.2.1 0 v h0
  have hs : s = 0 := by simpa using hmem.1
  subst hs
  have hu : (0 : ℝ≥0) < u := hmem.2
  have hval := hI.2.2.1 v w 0 u hHI 0 (Set.left_mem_Icc.mpr hu.le)
  simpa [AffineMap.lineMap_apply_zero] using hval

/-- **Both interpolations start, almost surely, at the representative of the starting
cell.**

The exponential clock is at `start` at time `0` because the constructed reflected process
is (`ReflectedWalk.Existence.ae_process_zero`, whose only hypothesis is positivity of the
rate, discharged unconditionally by `EnvironmentWalkDataProducer.areaRate_pos`).  The
exact clock is at the same place because `PathwiseClockClauses` supplies a time-change
homeomorphism fixing `0`.  The interpolations then follow by
`continuousInterpolation_apply_zero`. -/
theorem ae_interpolation_apply_zero (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hpath : PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact
      Iexp Iexact) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Iexp ω 0 = z.at e start ∧ Iexact ω 0 = z.at e start := by
  have hproc : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Existence.process D (areaRate (decode e)) 0 ω = some start :=
    Existence.ae_process_zero D hG (areaRate (decode e))
      (EnvironmentWalkDataProducer.areaRate_pos e) start
  unfold PathwiseClockClauses at hclock
  unfold PathwiseInterpolationClauses at hpath
  filter_upwards [hclock, hpath, hproc] with x hc hp hpr
  obtain ⟨hc1, hc2, -, -, -, -, -, hc8, -, -⟩ := hc
  have hexp0 : exponentialAreaPath (decode e) D 0 x = some start := hpr
  obtain ⟨φ, -, hφ0, hφ⟩ := hc8
  have hexact0 : exactAreaPath (decode e) D 0 x = some start := by
    have hstep : exactAreaPath (decode e) D 0 x
        = exponentialAreaPath (decode e) D (φ 0) x := hφ 0
    rw [hφ0] at hstep
    exact hstep.trans hexp0
  have hXexp0 : Xexp 0 x = Sum.inl start :=
    eq_inl_of_collapse_eq_some ((hc1 0).trans hexp0)
  have hXexact0 : Xexact 0 x = Sum.inl start :=
    eq_inl_of_collapse_eq_some ((hc2 0).trans hexact0)
  exact ⟨continuousInterpolation_apply_zero hp.2.2.1 hXexp0,
    continuousInterpolation_apply_zero hp.2.2.2 hXexact0⟩

/-! ## The two analytic inputs, named -/

/-- **A uniform modulus-of-continuity tail on every bounded time window, over the scales
`T`.**  This is exactly the `hmod` hypothesis of
`ReflectedGMS.MartingaleLimit.quenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict`
for the diffusively rescaled law of `μ`. -/
def RescaledWindowModulusTail (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (T : Set ℝ≥0) : Prop :=
  ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ ε ∈ T,
    ((diffusivelyRescaledPathLaw μ ε :
        ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
        Measure (BouRabeeGwynne.BrownianPath 2))
      (halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m c d) ≤ η

/-- **Convergence of every finite-dimensional distribution of the diffusively rescaled
law to the corresponding one of the anisotropic Brownian target.**  This is exactly the
`hfdd` hypothesis of
`ReflectedGMS.MartingaleLimit.quenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict`. -/
def RescaledFiniteDimensionalLimit
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) : Prop :=
  ∀ I : Finset ℝ≥0,
    Tendsto (fun ε => (diffusivelyRescaledPathLaw μ ε).map
        (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f)))
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
      (𝓝 (target.pathLaw.map
        (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (pathCoordinates f))))

/-! ## The initial-point tail is vacuous, so the size tail is free -/

/-- **A rescaled law whose paths almost surely start at `p` never leaves the closed ball
of radius `‖p‖` at time `0`**, at any scale in `(0, 1]`: the rescaling multiplies the
starting point by `ε`. -/
theorem rescaled_start_failure_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    (p : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ x ∂P, I x 0 = p)
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map I) ε :
        ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
        Measure (BouRabeeGwynne.BrownianPath 2))
      {f : BouRabeeGwynne.BrownianPath 2 |
        ‖p‖ < dist (f 0) (0 : BouRabeeGwynne.Euc 2)} = 0 := by
  have hopen : IsOpen {y : BouRabeeGwynne.Euc 2 |
      ‖p‖ < dist y (0 : BouRabeeGwynne.Euc 2)} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hSmeas : MeasurableSet {f : BouRabeeGwynne.BrownianPath 2 |
      ‖p‖ < dist (f 0) (0 : BouRabeeGwynne.Euc 2)} :=
    (ContinuousMap.measurable_eval (0 : ℝ≥0)) hopen.measurableSet
  have hcoe : ((diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map I) ε :
      ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
      Measure (BouRabeeGwynne.BrownianPath 2))
      = (P.map I).map (BouRabeeGwynne.scaledBrownianPath ε⁻¹) := rfl
  rw [hcoe, Measure.map_map (BouRabeeGwynne.measurable_scaledBrownianPath (d := 2) ε⁻¹) hI,
    Measure.map_apply
      ((BouRabeeGwynne.measurable_scaledBrownianPath (d := 2) ε⁻¹).comp hI) hSmeas]
  refine measure_mono_null ?_ (ae_iff.mp h0)
  intro x hx
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_setOf_eq] at hx
  intro hEq
  rw [StatementIngredients.scaledBrownianPath_inv_apply ε hε (I x) 0, mul_zero, hEq,
    dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ε.coe_nonneg] at hx
  have hεR : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hle : (ε : ℝ) * ‖p‖ ≤ ‖p‖ := by
    calc (ε : ℝ) * ‖p‖ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right hεR (norm_nonneg p)
      _ = ‖p‖ := one_mul _
  linarith

/-- **The window size tail of a rescaled interpolation law is free**, given the window
modulus tail, provided the paths almost surely start at a fixed point and the scales are
positive and at most one. -/
theorem rescaled_size_tail_of_modulus_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    (p : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ x ∂P, I x 0 = p)
    (T : Set ℝ≥0) (hT0 : ∀ ε ∈ T, 0 < ε) (hT1 : ∀ ε ∈ T, ε ≤ 1)
    (hmod : RescaledWindowModulusTail (P.toProbabilityMeasure.map I) T)
    (m : ℕ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ R : ℝ, ∀ ε ∈ T,
      ((diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map I) ε :
          ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2))
        (halfLineSizeFailure (0 : BouRabeeGwynne.Euc 2) m R) ≤ η := by
  refine halfLineSize_tail_of_modulus_tail_of_start_tail (0 : BouRabeeGwynne.Euc 2)
    (fun ε => ((diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map I) ε :
        ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
        Measure (BouRabeeGwynne.BrownianPath 2))) T hmod ?_ m η hη
  intro η' hη'
  refine ⟨‖p‖, fun ε hε => ?_⟩
  refine (rescaled_start_failure_eq_zero P I hI p h0 (hT0 ε hε) (hT1 ε hε)).trans_le ?_
  simp

/-! ## The scales that are positive and at most one -/

/-- The scales of `T` that are positive and at most one. -/
def smallScales (T : Set ℝ≥0) : Set ℝ≥0 := {ε ∈ T | 0 < ε ∧ ε ≤ 1}

theorem smallScales_subset (T : Set ℝ≥0) : smallScales T ⊆ T := fun _ h => h.1

theorem smallScales_pos {T : Set ℝ≥0} {ε : ℝ≥0} (h : ε ∈ smallScales T) : 0 < ε := h.2.1

theorem smallScales_le_one {T : Set ℝ≥0} {ε : ℝ≥0} (h : ε ∈ smallScales T) : ε ≤ 1 := h.2.2

theorem smallScales_mem_nhdsWithin {T : Set ℝ≥0}
    (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) :
    smallScales T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) := by
  have h1 : Set.Iic (1 : ℝ≥0) ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds zero_lt_one)
  have h2 : Set.Ioi (0 : ℝ≥0) ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) := self_mem_nhdsWithin
  filter_upwards [hT, h1, h2] with ε hεT hε1 hε0
  simp only [smallScales, Set.mem_sep_iff]
  exact ⟨hεT, hε0, hε1⟩

/-! ## The reduction -/

/-- **`TwoClockScalingLimit` from a window modulus tail and finite-dimensional
convergence, for each of the two clocks.**

CONDITIONAL on `hmodExp`, `hmodExact`, `hfddExp`, `hfddExact`; nothing here certifies any
of them, nor `p:thm:areaclt`, nor `hlimit`, nor either main theorem.  What is discharged
relative to
`ReflectedGMS.MartingaleLimit.twoClockQuenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict`
is the pair of window *size* tails, which follow from the modulus tails because the two
interpolations almost surely start at `z(start)` (`ae_interpolation_apply_zero`) and the
diffusive rescaling contracts that starting point at every scale in `(0, 1]`.

The extra hypothesis `hclock` is exactly the `PathwiseClockClauses` input that the
`hlaw` slot of
`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit`
already hands its producer, so this consumes nothing new.  The scale set `T` is only
required to be a neighbourhood of `0` within the positive scales; the two modulus tails
are asked for on `T` itself, and the proof restricts to `smallScales T`. -/
theorem twoClockScalingLimit_of_window_modulus_of_finiteDimensional
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (hmodExp : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) T)
    (hmodExact : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) T)
    (hfddExp : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledFiniteDimensionalLimit
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) target)
    (hfddExact : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledFiniteDimensionalLimit
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) target) :
    TwoClockScalingLimit e D hG z target start Xexp Xexact := by
  intro Zexp Zexact Iexp Iexact hmexp hmexact hpath
  refine ⟨hmexp, hmexact, ?_⟩
  have hae := ae_interpolation_apply_zero e D hG z Φ start Xexp Xexact M Zexp Zexact
    Iexp Iexact hclock hpath
  have haeExp : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Iexp ω 0 = z.at e start := hae.mono fun _ h => h.1
  have haeExact : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Iexact ω 0 = z.at e start := hae.mono fun _ h => h.2
  have hT' : smallScales T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) :=
    smallScales_mem_nhdsWithin hT
  have hmodExp' : RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp)
      (smallScales T) := by
    intro m c hc η hη
    obtain ⟨d, hd, hdT⟩ :=
      hmodExp Zexp Zexact Iexp Iexact hmexp hmexact hpath m c hc η hη
    exact ⟨d, hd, fun ε hε => hdT ε (smallScales_subset T hε)⟩
  have hmodExact' : RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact)
      (smallScales T) := by
    intro m c hc η hη
    obtain ⟨d, hd, hdT⟩ :=
      hmodExact Zexp Zexact Iexp Iexact hmexp hmexact hpath m c hc η hη
    exact ⟨d, hd, fun ε hε => hdT ε (smallScales_subset T hε)⟩
  have hsizeExp := rescaled_size_tail_of_modulus_tail
    (areaSampleLaw (decode e) D hG start) Iexp hmexp (z.at e start) haeExp
    (smallScales T) (fun _ hε => smallScales_pos hε) (fun _ hε => smallScales_le_one hε)
    hmodExp'
  have hsizeExact := rescaled_size_tail_of_modulus_tail
    (areaSampleLaw (decode e) D hG start) Iexact hmexact (z.at e start) haeExact
    (smallScales T) (fun _ hε => smallScales_pos hε) (fun _ hε => smallScales_le_one hε)
    hmodExact'
  exact twoClockQuenchedWeakLimitAtFixedStart_of_window_tails_of_tendsto_map_finsetRestrict
    (fun (_ : Unit) (_ : Unit) =>
      (areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp)
    (fun (_ : Unit) (_ : Unit) =>
      (areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact)
    target () () (0 : BouRabeeGwynne.Euc 2) (smallScales T) hT'
    hsizeExp hmodExp' (hfddExp Zexp Zexact Iexp Iexact hmexp hmexact hpath)
    hsizeExact hmodExact' (hfddExact Zexp Zexact Iexp Iexact hmexp hmexact hpath)

end ReflectedGMS.TwoClockScalingLimitReduction
