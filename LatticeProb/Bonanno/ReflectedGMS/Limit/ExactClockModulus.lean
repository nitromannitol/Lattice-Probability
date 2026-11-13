/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ExactClockModulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CompactContainmentProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.TwoClockLiftEnvironment

/-!
# The window modulus tail of the **exact**-clock interpolation

`ActualWindowModulus` / `CompactContainmentProducer` produce the `hmodExp` slot of
`TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
at `T := Set.Ioc 0 1`.  The exact-clock analogue `hmodExact` had **zero producers** and had
not been reduced one step.

This file reduces it, and names what is left.

## The route, and why it is the cheap one

The abstract weld `WindowModulusGridTransfer.rescaledWindowModulusTail_of_localized_arrays`
takes a path `I`, a comparison process `G`, a closeness input `hclose` and one localized
martingale array per coordinate of the rescaled `G`.  For the exponential clock it is used
with `I := Iexp` and `G := M`.  The **same** `G := M`, and therefore the **same** `harray`,
works for `I := Iexact`: the only thing that changes is `hclose`.

`hclose` for `Iexact` is obtained from `hclose` for `Iexp` — which
`ActualWindowModulus.hclose_of_containment` already derives from compact containment alone —
by the triangle inequality in probability, at the cost of one genuinely new input:

> `ClockCrossCloseness`: after diffusive scaling, the two interpolations are uniformly close
> on every horizon, in probability.

That input is the manuscript's clock equivalence `p:eq:clockequiv` in exactly the form this
lane needs: the two interpolations trace the same polygonal curve, at speeds that differ by
the clock defect, so their diffusively scaled distance is controlled by the scaled clock
deviation.  `Process/ClockDefectMaximalIndex` supplies the maximal-index half of that
estimate (`abs_scaled_visitClock_sub_le_of_notMem`, `measure_exists_abs_scaled_clockDefect_ge`);
turning it into `ClockCrossCloseness` also needs the spatial modulus of the polygonal curve,
and is **not** done here.

So `hmodExact` is now at ONE named input, the same `harray` as `hmodExp`, and the same
containment data.

## What is proved here

* `tendsto_measure_dist_gt_of_triangle` — the triangle inequality for the "scaled distance
  exceeds `κ` before the horizon" events, in probability.  Abstract, no walk content.
* `hclose_exact_of_hclose_exp` — `hclose` for `Iexact` against `M` from `hclose` for `Iexp`
  against `M` and `ClockCrossCloseness`.
* `rescaledWindowModulusTail_exact_of_inputs`, `modulusSlotExact_of_clock_inputs_and_arrays` —
  the `hmodExact` slot of the per-environment producers, at `T := Set.Ioc 0 1`, in the named
  form `TwoClockLiftEnvironment.ModulusSlotExact`.
* `gaussianClockLimitAtoms_of_arrays_and_crossCloseness` — both modulus slots filled at once,
  leaving exactly the two Gaussian identification atoms.

**Nothing here certifies `hmodExact`, `p:thm:areaclt`, `hlimit` or either main theorem.**
`harray` and `ClockCrossCloseness` are open, and so are the two identification atoms.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ExactClockModulus

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
open ReflectedGMS.CompactContainmentProducer
open ReflectedGMS.TwoClockLiftEnvironment

/-! ## A triangle inequality in probability -/

/-- **The "scaled distance exceeds `κ` before the horizon" events obey the triangle
inequality in probability.**

If `u` is close to `v` and `v` is close to `w` — each in the sense that the probability of
ever exceeding a fixed scaled threshold before the rescaled horizon tends to `0` — then `u`
is close to `w`.  Splitting at `κ/2` is what makes the inclusion pointwise; only monotonicity
and subadditivity of the outer measure are used, so no measurability of the events is
needed. -/
theorem tendsto_measure_dist_gt_of_triangle {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u v w : ℝ≥0 → Ω → Plane) (ε : ℕ → ℝ≥0) (H : ℝ≥0)
    (huv : ∀ κ : ℝ, 0 < κ → Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      κ < (ε n : ℝ) * dist (u r ω) (v r ω)}) atTop (𝓝 0))
    (hvw : ∀ κ : ℝ, 0 < κ → Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      κ < (ε n : ℝ) * dist (v r ω) (w r ω)}) atTop (𝓝 0))
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      κ < (ε n : ℝ) * dist (u r ω) (w r ω)}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.div_pos hη.ne' (by norm_num)
  have hκ2 : (0 : ℝ) < κ / 2 := by linarith
  have h1 := (ENNReal.tendsto_nhds_zero.1 (huv (κ / 2) hκ2)) (η / 2) hη2
  have h2 := (ENNReal.tendsto_nhds_zero.1 (hvw (κ / 2) hκ2)) (η / 2) hη2
  filter_upwards [h1, h2] with n hn1 hn2
  have hsub : {ω | ∃ r < (ε n)⁻¹ ^ 2 * H, κ < (ε n : ℝ) * dist (u r ω) (w r ω)} ⊆
      {ω | ∃ r < (ε n)⁻¹ ^ 2 * H, κ / 2 < (ε n : ℝ) * dist (u r ω) (v r ω)} ∪
      {ω | ∃ r < (ε n)⁻¹ ^ 2 * H, κ / 2 < (ε n : ℝ) * dist (v r ω) (w r ω)} := by
    rintro ω ⟨r, hr, hlt⟩
    by_cases hc : κ / 2 < (ε n : ℝ) * dist (u r ω) (v r ω)
    · exact Or.inl ⟨r, hr, hc⟩
    · refine Or.inr ⟨r, hr, ?_⟩
      replace hc : (ε n : ℝ) * dist (u r ω) (v r ω) ≤ κ / 2 := not_lt.1 hc
      have hεnn : (0 : ℝ) ≤ (ε n : ℝ) := (ε n).coe_nonneg
      have htri : dist (u r ω) (w r ω)
          ≤ dist (u r ω) (v r ω) + dist (v r ω) (w r ω) := dist_triangle _ _ _
      have hmul := mul_le_mul_of_nonneg_left htri hεnn
      rw [mul_add] at hmul
      linarith
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  exact le_trans (add_le_add hn1 hn2) (le_of_eq (ENNReal.add_halves η))

/-! ## The new input: the two interpolations are close after diffusive scaling -/

/-- **The clock-equivalence input, `p:eq:clockequiv`, in the shape this lane consumes.**

After diffusive scaling, the exact-clock and exponential-clock interpolations stay uniformly
close on every horizon, in probability.  This is the *only* thing `hmodExact` asks beyond
what `hmodExp` already asks.

It is a statement about the pair of interpolations alone — no spatial extension, no
martingale array and no target occur in it. -/
def ClockCrossCloseness (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (start : Vertex e.val)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2) :
    Prop :=
  ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ →
      Tendsto (fun n => (areaSampleLaw (decode e) D hG start)
        {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
          κ < (ε n : ℝ) * dist (Iexact ω r) (Iexp ω r)}) atTop (𝓝 0)

/-- `ClockCrossCloseness`, asked at every admissible pair of interpolations — the shape in
which the slot-filling theorems below consume it. -/
def ClockCrossClosenessSlot (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) : Prop :=
  ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp → Measurable Iexact →
    PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
    ClockCrossCloseness e D hG start Iexp Iexact

/-! ## `hclose` for the exact clock -/

/-- **The closeness input of the abstract modulus weld, for the exact-clock
interpolation.**

Obtained from the exponential-clock closeness — which `ActualWindowModulus.hclose_of_containment`
derives from compact containment alone — and `ClockCrossCloseness`, by
`tendsto_measure_dist_gt_of_triangle`.  The comparison process is the *same* `M`, so the same
`harray` serves both clocks. -/
theorem hclose_exact_of_hclose_exp (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hexp : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ →
        Tendsto (fun n => (areaSampleLaw (decode e) D hG start)
          {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
            κ < (ε n : ℝ) * dist (Iexp ω r) (M r ω)}) atTop (𝓝 0))
    (hcross : ClockCrossCloseness e D hG start Iexp Iexact) :
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ →
        Tendsto (fun n => (areaSampleLaw (decode e) D hG start)
          {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
            κ < (ε n : ℝ) * dist (Iexact ω r) (M r ω)}) atTop (𝓝 0) := by
  intro ε hεpos hεlim H κ hκ
  exact tendsto_measure_dist_gt_of_triangle (areaSampleLaw (decode e) D hG start)
    (fun r ω => Iexact ω r) (fun r ω => Iexp ω r) M ε H
    (fun c hc => hcross ε hεpos hεlim H c hc)
    (fun c hc => hexp ε hεpos hεlim H c hc) κ hκ

/-! ## The window modulus tail, and the `hmodExact` slot -/

/-- **`RescaledWindowModulusTail` for the exact-clock interpolation of the reflected walk.**

The exact-clock analogue of `ActualWindowModulus.rescaledWindowModulusTail_exp_of_inputs`,
with the *same* localized martingale arrays: only the closeness input changes, and the extra
cost is exactly `ClockCrossCloseness`.

CONDITIONAL on `hcont`, `hdense`, `harray` and `hcross`; nothing here certifies any of
them. -/
theorem rescaledWindowModulusTail_exact_of_inputs (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M Zexp : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hIexact : Measurable Iexact)
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
    (hcross : ClockCrossCloseness e D hG start Iexp Iexact)
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact)
      (Set.Ioc 0 1) :=
  rescaledWindowModulusTail_of_localized_arrays
    (Q := areaSampleLaw (decode e) D hG start)
    (P := areaSampleLaw (decode e) D hG start) (fun _ => rfl) Iexact hIexact M
    (hclose_exact_of_hclose_exp e D hG start M Iexp Iexact
      (hclose_of_containment e D hG z Φ start Xexp M Zexp Iexp hz hsub hdiam hM hI hdense
        hcont)
      hcross)
    harray

/-- **The `hmodExact` slot, verbatim**, at `T := Set.Ioc 0 1`, from the clock clauses, the
walk data, the martingale arrays and `ClockCrossCloseness`.

The exact-clock mirror of `CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays`:
right-density comes from `RightDenseVertexTimesProducer.ae_rightDenseVertexTimes_of_walkData`
and compact containment from `CompactContainmentProducer.compactContainment_of_arrays`, so
the remaining probabilistic inputs are `harray` and `hcross`. -/
theorem modulusSlotExact_of_clock_inputs_and_arrays (e : Env) [Nontrivial (Vertex e.val)]
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
    (hcross : ClockCrossClosenessSlot e D hG z start Xexp Xexact)
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    ModulusSlotExact e D hG z start Xexp Xexact (Set.Ioc 0 1) := by
  intro Zexp Zexact Iexp Iexact hIexp hIexact hpath
  have hM : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω) :=
    Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1
  have hI : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω) :=
    Filter.Eventually.mono hpath fun _ h => h.2.2.1
  exact rescaledWindowModulusTail_exact_of_inputs e D hG z Φ start Xexp M Zexp Iexp Iexact
    hIexact hz hsub hdiam hM hI
    (ae_rightDenseVertexTimes_of_walkData e D hG Φ start Xexp Xexact M hdata hclock)
    (compactContainment_of_arrays e D hG z Φ start Xexp M hz hsub hM harray)
    (hcross Zexp Zexact Iexp Iexact hIexp hIexact hpath) harray

/-! ## Both modulus slots at once -/

/-- **The two window-modulus atoms of `TwoClockLiftEnvironment.GaussianClockLimitAtoms`,
both filled**, leaving exactly the two Gaussian identification atoms.

CONDITIONAL on `harray`, `hcross`, `hgaussExp` and `hgaussExact`; it certifies none of
them. -/
theorem gaussianClockLimitAtoms_of_arrays_and_crossCloseness (e : Env)
    [Nontrivial (Vertex e.val)]
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
    (hcross : ClockCrossClosenessSlot e D hG z start Xexp Xexact)
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H))
    (hgaussExp : GaussSlotExp e D hG z target start Xexp Xexact)
    (hgaussExact : GaussSlotExact e D hG z target start Xexp Xexact) :
    GaussianClockLimitAtoms e D hG z target start Xexp Xexact (Set.Ioc 0 1) :=
  ⟨hmodExp_of_clock_inputs_and_arrays e D hG z Φ start Xexp Xexact M hdata hclock hz hsub
      hdiam harray,
    modulusSlotExact_of_clock_inputs_and_arrays e D hG z Φ start Xexp Xexact M hdata hclock
      hz hsub hdiam hcross harray,
    hgaussExp, hgaussExact⟩

end ReflectedGMS.ExactClockModulus
