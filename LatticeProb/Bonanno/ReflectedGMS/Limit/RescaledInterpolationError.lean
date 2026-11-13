/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RescaledInterpolationError at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledFddCharFunReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.ExactClockModulus

/-!
# `hinterp`: the fixed-time interpolation error of the rescaled walk

`RescaledFddCharFunReduction.RescaledInterpolationErrorVanishes P Iw M` (`:177`) is the
`hinterp` atom of the FCLT identification lane, consumed by
`rescaledFddCharFunLimits_of_increment_limits` (`:207`): along every sequence of scales
`εₖ → 0⁺` and at every fixed rescaled time `u`,

  `εₖ • Iw(u/εₖ²) − εₖ • M(u/εₖ²) ⟶ 0`  in probability.

It was the last atom of that lane with no reduction.  **It is strictly weaker than the
`hclose` input the `hmod` lane already discharges**, and this file proves exactly that.

## Route

`WindowModulusGridTransfer.rescaledWindowModulusTail_of_localized_arrays` (`:653`) takes a
closeness input

  `hclose : ∀ H κ > 0, P {ω | ∃ r < εₙ⁻² H, κ < εₙ · dist (I ω r) (G r ω)} ⟶ 0`,

*uniform on the whole window* `[0, εₙ⁻² H)`.  `hinterp` asks the same thing at the single
time `r = εₙ⁻² u`, which is inside the window `H := u + 1`.  So the reduction is a set
inclusion plus a `κ/2` split, and needs **no measurability** of either event (only
`measure_mono`).

Two mismatches have to be absorbed, and both are cheap:

* **The scale quantifier.**  `hinterp` quantifies over `ε` with `Tendsto ε atTop (𝓝[>] 0)`,
  which gives positivity only *eventually*; `hclose` asks `∀ n, 0 < ε n`.  The shift
  `n ↦ ε (n + N)` past the positivity threshold fixes this
  (`tendsto_add_atTop_iff_nat`), because both statements are limits along `atTop`.
* **The CENTERING TRAP.**  `LocalizedArrayProducer.ThresholdArrayInputs.start_martingale`
  forces the array's process to vanish at `0`, while the interpolation starts at
  `z.at e start ≠ 0`, so the array consumers are fed the **centered** extension `M − p`.
  `hclose` is stated for the uncentered `M` and tolerates the shift because it only sees
  `εₙ · dist`.  The theorems below therefore carry an explicit constant `c` with
  `M t ω = G t ω − c`: the comparison process of `hinterp` may be the centered extension
  while the closeness input is about the uncentered one, since `εₙ‖c‖ → 0`.  Taking
  `c := 0` recovers the uncentered statement.

## What is proved

* `rescaledInterpolationErrorVanishes_of_windowCloseness` — the abstract reduction, on an
  arbitrary sample space.  `hinterp` from `WindowCloseness` and the centering constant.
* `rescaledInterpolationErrorVanishes_exp_of_containment` — `hinterp` for the
  exponential-clock interpolation of the reflected walk, from exactly the inputs of
  `ActualWindowModulus.hclose_of_containment`.
* `rescaledInterpolationErrorVanishes_exp_of_clock_inputs_and_arrays` — **`hinterp` at the
  walk with compact containment and right-density discharged**: from the clock clauses, the
  environment walk data, `hz`/`hsub`/`hdiam` and `harray`, i.e. *exactly* the inputs of
  `CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays`.  So `hinterp` costs the
  `hmodExp` lane nothing new.
* `rescaledInterpolationErrorVanishes_exact_of_crossCloseness` — the exact-clock analogue,
  at the additional cost of `ExactClockModulus.ClockCrossCloseness`, which is the *same*
  extra input `hmodExact` already pays.

## Anti-vacuity

`WindowCloseness` is satisfiable (`windowCloseness_self`: it holds when the interpolation
traces the comparison process) and is not conclusion-shaped: it is a statement on the
walk's own sample space, with no law, no tightness and no weak limit in it.  Nothing here
assumes a scaling limit, a finite-dimensional convergence, or `hinc`.

CONDITIONAL, in the walk instances, on the same `harray` (and, for the exact clock,
`ClockCrossCloseness`) that the `hmod` lane names; nothing about the reflected walk is
certified here.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.RescaledInterpolationError

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement
open ReflectedWalk QuenchedFormulation
open ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.CorrectorInterpolationTransfer
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.ActualWindowModulus
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.CompactContainmentProducer
open ReflectedGMS.RightDenseVertexTimesProducer
open ReflectedGMS.ExactClockModulus
open ReflectedGMS.RescaledFddCharFun
open ReflectedGMS.GaussianWeakLimit
open ReflectedGMS.GaussianLimitIdentification
open ReflectedGMS.BrownianFdd

/-! ## The window-closeness input, named -/

/-- **The `hclose` input of `WindowModulusGridTransfer.rescaledWindowModulusTail_of_localized_arrays`,
named.**  Along every positive null sequence of scales and on every horizon, the
diffusively scaled distance between the continuous interpolation `I` and the comparison
process `G` exceeds a fixed threshold before the rescaled horizon with probability tending
to `0`.

This is *uniform on the window*; `hinterp` below is the same statement at one time. -/
def WindowCloseness {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) : Prop :=
  ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ →
      Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
        κ < (ε n : ℝ) * dist (I ω r) (G r ω)}) atTop (𝓝 0)

/-! ## The abstract reduction -/

/-- **A positive null sequence, from a sequence tending to `0` from the right.**  The
`hinterp` quantifier `Tendsto ε atTop (𝓝[>] 0)` gives positivity only eventually, so
`WindowCloseness` — which asks for it everywhere — is applied to the shifted sequence and
the conclusion is shifted back. -/
theorem tendsto_windowCloseness_of_tendsto_nhdsWithin {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {I : Ω → BouRabeeGwynne.BrownianPath 2}
    {G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} (hclose : WindowCloseness P I G)
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)))
    (H : ℝ≥0) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      κ < (ε n : ℝ) * dist (I ω r) (G r ω)}) atTop (𝓝 0) := by
  have hεmem : ∀ᶠ n in atTop, (0 : ℝ≥0) < ε n := by
    have h := hε.eventually_mem (self_mem_nhdsWithin (a := (0 : ℝ≥0)) (s := Set.Ioi 0))
    simpa using h
  have hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0)) := tendsto_nhds_of_tendsto_nhdsWithin hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hεmem
  have hpos : ∀ n, (0 : ℝ≥0) < ε (n + N) := fun n => hN _ (Nat.le_add_left N n)
  have hlim' : Tendsto (fun n => ε (n + N)) atTop (𝓝 (0 : ℝ≥0)) :=
    (tendsto_add_atTop_iff_nat N).2 hεlim
  have hshift := hclose (fun n => ε (n + N)) hpos hlim' H κ hκ
  rw [← tendsto_add_atTop_iff_nat N]
  exact hshift

/-- **`hinterp` from `WindowCloseness`.**

The comparison process of `hinterp` may differ from the one in the closeness input by a
fixed constant `c` — this is the centering trap: the array consumers need `M 0 = 0`, the
interpolation starts at `p ≠ 0`, and the closeness input is stated for the uncentered
extension.  The shift is absorbed because `εₖ‖c‖ → 0`.

Only `measure_mono` and `measure_union`-free monotonicity are used, so **no measurability
of either event is needed**. -/
theorem rescaledInterpolationErrorVanishes_of_windowCloseness {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (Iw : Ω → BouRabeeGwynne.BrownianPath 2)
    (G M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (c : BouRabeeGwynne.Euc 2)
    (hM : ∀ t ω, M t ω = G t ω - c)
    (hclose : WindowCloseness P Iw G) :
    RescaledInterpolationErrorVanishes P Iw M := by
  intro ε hε u
  have hεmem : ∀ᶠ n in atTop, (0 : ℝ≥0) < ε n := by
    have h := hε.eventually_mem (self_mem_nhdsWithin (a := (0 : ℝ≥0)) (s := Set.Ioi 0))
    simpa using h
  have hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0)) := tendsto_nhds_of_tendsto_nhdsWithin hε
  have hεR : Tendsto (fun n => ((ε n : ℝ))) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 hεlim
  rw [tendstoInMeasure_iff_norm]
  intro κ hκ
  simp only [Pi.zero_apply, sub_zero]
  have hκ2 : (0 : ℝ) < κ / 2 := by linarith
  have hwin := tendsto_windowCloseness_of_tendsto_nhdsWithin hclose ε hε (u + 1) (κ / 2) hκ2
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have h1 := (ENNReal.tendsto_nhds_zero.1 hwin) η hη
  have hc : Tendsto (fun n => (ε n : ℝ) * ‖c‖) atTop (𝓝 0) := by
    simpa using hεR.mul_const ‖c‖
  have h2 : ∀ᶠ n in atTop, (ε n : ℝ) * ‖c‖ < κ / 2 :=
    (tendsto_order.1 hc).2 (κ / 2) hκ2
  filter_upwards [h1, h2, hεmem] with n hn1 hn2 hnpos
  refine le_trans (measure_mono ?_) hn1
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  refine ⟨(ε n)⁻¹ ^ 2 * u, ?_, ?_⟩
  · have hinv0 : (0 : ℝ≥0) < (ε n)⁻¹ := inv_pos.2 hnpos
    exact mul_lt_mul_of_pos_left (lt_add_one u) (pow_pos hinv0 2)
  · have hsplit : (ε n : ℝ) • Iw ω ((ε n)⁻¹ ^ 2 * u) - rescaleProcess M (ε n) u ω
        = (ε n : ℝ) • (Iw ω ((ε n)⁻¹ ^ 2 * u) - G ((ε n)⁻¹ ^ 2 * u) ω) + (ε n : ℝ) • c := by
      show (ε n : ℝ) • Iw ω ((ε n)⁻¹ ^ 2 * u) - (ε n : ℝ) • M ((ε n)⁻¹ ^ 2 * u) ω
        = (ε n : ℝ) • (Iw ω ((ε n)⁻¹ ^ 2 * u) - G ((ε n)⁻¹ ^ 2 * u) ω) + (ε n : ℝ) • c
      rw [hM, smul_sub, smul_sub]
      abel
    have hbound : ‖(ε n : ℝ) • Iw ω ((ε n)⁻¹ ^ 2 * u) - rescaleProcess M (ε n) u ω‖
        ≤ (ε n : ℝ) * dist (Iw ω ((ε n)⁻¹ ^ 2 * u)) (G ((ε n)⁻¹ ^ 2 * u) ω)
          + (ε n : ℝ) * ‖c‖ := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ε n).coe_nonneg,
        dist_eq_norm]
    linarith

/-! ## `hinterp` at the reflected walk: the exponential clock -/

/-- **`hinterp` for the exponential-clock interpolation of the reflected walk**, from
exactly the inputs of `ActualWindowModulus.hclose_of_containment`.

`Mc` is the comparison process actually fed to the consumer; `hMc` allows it to be the
centered extension `M − p` (the centering trap), with `Mc := M` and `p := 0` the uncentered
case.

CONDITIONAL on `hM`, `hI`, `hdense` and `hcont`; nothing here certifies any of them. -/
theorem rescaledInterpolationErrorVanishes_exp_of_containment (e : Env)
    [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M Zexp Mc : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (p : Plane) (hMc : ∀ t ω, Mc t ω = M t ω - p)
    (Iexp : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hM : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω))
    (hI : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω))
    (hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω))
    (hcont : CompactContainment e D hG z start Xexp) :
    RescaledInterpolationErrorVanishes (areaSampleLaw (decode e) D hG start) Iexp Mc :=
  rescaledInterpolationErrorVanishes_of_windowCloseness Iexp M Mc p hMc
    (hclose_of_containment e D hG z Φ start Xexp M Zexp Iexp hz hsub hdiam hM hI hdense
      hcont)

/-- **`hinterp` at the walk with compact containment and right-density discharged.**

The hypotheses are *exactly* those of
`CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays` plus the interpolation
clauses the `hmodExp` slot is quantified over: the environment walk data, the pathwise
clock clauses, the cell representatives, the corrector sublinearity, the submacroscopic
diameters and the localized martingale arrays.  So **`hinterp` costs the `hmodExp` lane
nothing beyond what it already pays**; in particular it adds no new open atom.

`harray` is the threshold-stopped bracket lane and is not proved anywhere; every other
input is discharged inside the lane. -/
theorem rescaledInterpolationErrorVanishes_exp_of_clock_inputs_and_arrays (e : Env)
    [Nontrivial (Vertex e.val)]
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
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      ∀ (Mc : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane) (p : Plane),
        (∀ t ω, Mc t ω = M t ω - p) →
        RescaledInterpolationErrorVanishes (areaSampleLaw (decode e) D hG start) Iexp Mc := by
  intro Zexp Zexact Iexp Iexact hpath Mc p hMc
  have hM : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω) :=
    Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1
  have hI : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω) :=
    Filter.Eventually.mono hpath fun _ h => h.2.2.1
  exact rescaledInterpolationErrorVanishes_exp_of_containment e D hG z Φ start Xexp M Zexp
    Mc p hMc Iexp hz hsub hdiam hM hI
    (ae_rightDenseVertexTimes_of_walkData e D hG Φ start Xexp Xexact M hdata hclock)
    (compactContainment_of_arrays e D hG z Φ start Xexp M hz hsub hM harray)

/-! ## `hinterp` at the reflected walk: the exact clock -/

/-- **`hinterp` for the exact-clock interpolation**, at the same extra cost as `hmodExact`:
`ExactClockModulus.ClockCrossCloseness`.  The comparison process is the *same* `M`, so the
same arrays serve both clocks, exactly as in
`ExactClockModulus.rescaledWindowModulusTail_exact_of_inputs`. -/
theorem rescaledInterpolationErrorVanishes_exact_of_crossCloseness (e : Env)
    [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M Zexp Mc : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (p : Plane) (hMc : ∀ t ω, Mc t ω = M t ω - p)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hM : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω))
    (hI : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω))
    (hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω))
    (hcont : CompactContainment e D hG z start Xexp)
    (hcross : ClockCrossCloseness e D hG start Iexp Iexact) :
    RescaledInterpolationErrorVanishes (areaSampleLaw (decode e) D hG start) Iexact Mc :=
  rescaledInterpolationErrorVanishes_of_windowCloseness Iexact M Mc p hMc
    (hclose_exact_of_hclose_exp e D hG start M Iexp Iexact
      (hclose_of_containment e D hG z Φ start Xexp M Zexp Iexp hz hsub hdiam hM hI hdense
        hcont)
      hcross)

/-! ## Machine-checked welds into the FCLT consumer -/

/-- **The `hinterp` slot of
`RescaledFddCharFunReduction.rescaledFddCharFunLimits_of_increment_limits` is filled by the
window-closeness route.**  Only `hinc` and the deterministic start are left on that side. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (Iw : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable Iw)
    (𝔽 : Filtration ℝ≥0 mΩ) (G M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (c : BouRabeeGwynne.Euc 2) (hM : ∀ t ω, M t ω = G t ω - c)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t))
    (q : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ ω ∂P, M 0 ω = q)
    (target : AnisotropicBrownianTarget)
    (hinc : RescaledIncrementCharFunLimit P 𝔽 M target)
    (hclose : WindowCloseness P Iw G) :
    RescaledFddCharFunLimits (P.toProbabilityMeasure.map Iw) target :=
  rescaledFddCharFunLimits_of_increment_limits Iw hI 𝔽 M hadapt q h0 target hinc
    (rescaledInterpolationErrorVanishes_of_windowCloseness Iw G M c hM hclose)

/-- **Integration check at the walk.**  The exponential-clock producer really does fill the
`hinterp` slot for the walk's own interpolation and its centered extension. -/
example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (p : Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hpath : PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    RescaledInterpolationErrorVanishes (areaSampleLaw (decode e) D hG start) Iexp
      (fun t ω => M t ω - p) :=
  rescaledInterpolationErrorVanishes_exp_of_clock_inputs_and_arrays e D hG z Φ start Xexp
    Xexact M hdata hclock hz hsub hdiam harray Zexp Zexact Iexp Iexact hpath
    (fun t ω => M t ω - p) p (fun _ _ => rfl)

end ReflectedGMS.RescaledInterpolationError
