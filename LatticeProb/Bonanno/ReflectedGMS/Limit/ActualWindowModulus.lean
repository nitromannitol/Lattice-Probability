/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualWindowModulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WindowModulusGridTransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.CorrectorInterpolationTransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.TwoClockScalingLimitReduction

/-!
# The window modulus of the reflected walk's exponential-clock interpolation

This is gap 4 of the `hmod` weld: the abstract implication
`WindowModulusGridTransfer.rescaledWindowModulusTail_of_localized_arrays` is instantiated
at the actual data of manuscript `p:thm:areaclt`, namely

* `P := areaSampleLaw (decode e) D hG start` — the canonical sample law;
* `I := Iexp` — any measurable continuous interpolation satisfying
  `InterpolatedTwoClockReduction.PathwiseInterpolationClauses` (the `z`-extension);
* `G := M` — the harmonic extension of `Φ` supplied by clause 10 of
  `InvarianceAssembly.PathwiseClockClauses`.

## What is proved here, and what is assumed

The genuinely new content is `hclose_of_containment`: the `hclose` hypothesis of the
abstract weld — the interpolation and the harmonic extension are uniformly close after
diffusive scaling, in probability, on every horizon — is **derived**, not assumed, from
compact containment alone.  The reason is that
`CorrectorInterpolationTransfer.exists_pos_forall_scaled_interpolation_sub_le_allTimes`
is a *deterministic* bound: once `ε ≤ ε₀` and the containment event holds, the scaled
distance is at most `κ` at **every** time before the horizon, so the failure set is
literally empty there.  The whole probabilistic content of `hclose` is therefore the
containment probability, and nothing else.

`harray` — a `LocalizedMartingaleArray` for each coordinate of the rescaled `M` — is
**not** proved here and is not provable from anything currently in the tree: it is the
threshold-stopped bracket lane (manuscript `p:lem:bracketlimit`), and the search recorded
in the packet handoff found no producer of `LocalizedMartingaleArray` anywhere.  It is a
named hypothesis below, as are compact containment (`p:lem:lindeberg`) and the almost-sure
right-density of vertex times.

**Nothing in this file certifies tightness for the reflected walk**; every result is an
implication.  The remaining open atoms are named in the theorem statements.

## The completion variant

The abstract weld allows the martingale array to live on a second measurable structure `Q`
with the same outer measure as `P` (for instance `P.completion`, so that the array's
filtrations may contain null sets).  That generality is *not* re-exposed here: a
`{mQ : MeasurableSpace Ω}` binder would become a local instance shadowing the sample
space's own `MeasurableSpace` instance throughout this file.  A consumer who needs the
completion should apply `rescaledWindowModulusTail_of_localized_arrays` directly.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ActualWindowModulus

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement
open MartingaleIngredients ReflectedWalk ProcessFiltration QuenchedFormulation
open ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.CorrectorInterpolationTransfer
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.WindowModulusUniformScales
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.InvarianceAssembly

/-! ## Compact containment, named -/

/-- **Compact containment of the rescaled representative positions**, manuscript
`p:lem:lindeberg`, in the shape `CorrectorInterpolationTransfer` consumes: along every
positive null sequence of scales and on every horizon, the rescaled representative of the
occupied vertex stays in a fixed ball, with probability tending to one. -/
def CompactContainment (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) : Prop :=
  ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ (H : ℝ≥0) (η : ℝ≥0∞), 0 < η → ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
      (areaSampleLaw (decode e) D hG start)
        {ω | ¬ ∀ (s : ℝ≥0) (v : Vertex e.val), s < (ε n)⁻¹ ^ 2 * H →
          Xexp s ω = Sum.inl v → ‖z.at e v‖ ≤ R / (ε n : ℝ)} ≤ η

/-! ## `hclose` is exactly compact containment -/

/-- **The closeness input of the abstract weld, derived from compact containment.**

The corrector/interpolation transfer bounds `ε ‖Iexp r − M r‖` by `κ` *deterministically*,
uniformly over all times before the horizon, as soon as `ε ≤ ε₀(κ, R)` and the containment
event holds.  So the event that the scaled distance ever exceeds `κ` before the horizon is
contained in the union of a null set (where the pathwise clauses fail) and the containment
failure event; only the latter carries probability. -/
theorem hclose_of_containment (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M Zexp : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
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
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ →
        Tendsto (fun n => (areaSampleLaw (decode e) D hG start)
          {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
            κ < (ε n : ℝ) * dist (Iexp ω r) (M r ω)}) atTop (𝓝 0) := by
  intro ε hεpos hεlim H κ hκ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨R, hR, hev⟩ := hcont ε hεpos hεlim H η hη
  obtain ⟨ε₀, hε₀, htrans⟩ :=
    exists_pos_forall_scaled_interpolation_sub_le_allTimes (decode e) (decode_geometry e)
      (Φ.at e) (z.at e) (fun v => hz e v) hsub hdiam hR hκ
  have hcoe : Tendsto (fun n => ((ε n : ℝ))) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 hεlim
  have hε₀ev : ∀ᶠ n in atTop, ((ε n : ℝ)) ≤ ε₀ :=
    ((tendsto_order.1 hcoe).2 ε₀ hε₀).mono fun _ h => h.le
  -- the full-measure event on which all three pathwise clauses hold
  have hae := (hM.and hI).and hdense
  have hnull : (areaSampleLaw (decode e) D hG start)
      {ω | ¬ ((IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
            (fun t => M t ω) ∧
          IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
            (fun t => Zexp t ω) (Iexp ω)) ∧
        RightDenseVertexTimes (decode e) (fun t => Xexp t ω))} = 0 := ae_iff.1 hae
  filter_upwards [hev, hε₀ev] with n hn hεn
  have hεnpos : (0 : ℝ) < (ε n : ℝ) := by exact_mod_cast hεpos n
  have hsubset : {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
        κ < (ε n : ℝ) * dist (Iexp ω r) (M r ω)} ⊆
      {ω | ¬ ((IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
            (fun t => M t ω) ∧
          IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
            (fun t => Zexp t ω) (Iexp ω)) ∧
        RightDenseVertexTimes (decode e) (fun t => Xexp t ω))} ∪
      {ω | ¬ ∀ (s : ℝ≥0) (v : Vertex e.val), s < (ε n)⁻¹ ^ 2 * H →
        Xexp s ω = Sum.inl v → ‖z.at e v‖ ≤ R / (ε n : ℝ)} := by
    rintro ω ⟨r, hr, hlt⟩
    by_cases hg : ((IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
          (fun t => M t ω) ∧
        IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
          (fun t => Zexp t ω) (Iexp ω)) ∧
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω))
    · by_cases hc : ∀ (s : ℝ≥0) (v : Vertex e.val), s < (ε n)⁻¹ ^ 2 * H →
          Xexp s ω = Sum.inl v → ‖z.at e v‖ ≤ R / (ε n : ℝ)
      · exfalso
        have hbound := htrans ((ε n : ℝ)) hεnpos hεn (fun t => Xexp t ω)
          (fun t => Zexp t ω) (fun t => Iexp ω t) (fun t => M t ω)
          hg.1.2 hg.1.1 hg.2 ((ε n)⁻¹ ^ 2 * H) hc r hr
        rw [dist_eq_norm] at hlt
        exact absurd hbound (not_le.2 hlt)
      · exact Or.inr hc
    · exact Or.inl hg
  refine le_trans (measure_mono hsubset) (le_trans (measure_union_le _ _) ?_)
  rw [hnull, zero_add]
  exact hn

/-! ## The window modulus tail at the actual data -/

/-- **`RescaledWindowModulusTail` for the exponential-clock interpolation of the reflected
walk**, from compact containment, almost-sure right-density of the vertex times, and one
localized martingale array per coordinate of the rescaled harmonic extension.

This is `hmodExp` of
`TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
at `T := Set.Ioc 0 1`, which is a neighbourhood of `0` within the positive scales
(`WindowModulusUniformScales.Ioc_zero_one_mem_nhdsWithin`).

CONDITIONAL on `hcont`, `hdense` and `harray`.  Of these, `harray` is the threshold-stopped
bracket lane and has no producer in the tree. -/
theorem rescaledWindowModulusTail_exp_of_inputs (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M Zexp : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hIm : Measurable Iexp)
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
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp)
      (Set.Ioc 0 1) :=
  rescaledWindowModulusTail_of_localized_arrays
    (Q := areaSampleLaw (decode e) D hG start)
    (P := areaSampleLaw (decode e) D hG start) (fun _ => rfl) Iexp hIm M
    (hclose_of_containment e D hG z Φ start Xexp M Zexp Iexp hz hsub hdiam hM hI hdense
      hcont)
    harray

/-- **The `hmodExp` slot of `twoClockScalingLimit_of_window_modulus_of_finiteDimensional`,
verbatim**, at `T := Set.Ioc 0 1`.

The hypotheses do not mention the quantified interpolations `Zexp`, `Zexact`, `Iexp`,
`Iexact`: compact containment, right-density and the martingale arrays are statements
about `Xexp`, `z` and `M` only.  So the universally quantified slot is discharged for
every admissible interpolation at once. -/
theorem hmodExp_of_inputs (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hM : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω))
    (hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω))
    (hcont : CompactContainment e D hG z start Xexp)
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
        (Set.Ioc 0 1) := by
  intro Zexp Zexact Iexp Iexact hIm _ hpath
  have hI : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω) :=
    Filter.Eventually.mono hpath fun _ h => h.2.2.1
  exact rescaledWindowModulusTail_exp_of_inputs e D hG z Φ start Xexp M Zexp Iexp hIm hz
    hsub hdiam hM hI hdense hcont harray

/-- **`hmodExp` from the clock clauses the consumer already holds.**

`InvarianceAssembly.PathwiseClockClauses` clause 10 is
`RegularSpatialExtension (decode e) (Φ.at e) (Xexp · ω) (M · ω)`, whose first component is
the `IsSpatialExtension` hypothesis of `hmodExp_of_inputs`.  So a consumer holding `hclock`
supplies that input for free. -/
theorem hmodExp_of_clock_inputs (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω))
    (hcont : CompactContainment e D hG z start Xexp)
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
  hmodExp_of_inputs e D hG z Φ start Xexp Xexact M hz hsub hdiam
    (Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1) hdense hcont harray

/-- **Integration check.**  `hmodExp_of_clock_inputs` really does fill the `hmodExp` slot of
`TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
at `T := Set.Ioc 0 1`: the partial application below elaborates, leaving exactly the three
slots this packet does not discharge (`hmodExact`, `hfddExp`, `hfddExact`). -/
example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RightDenseVertexTimes (decode e) (fun t => Xexp t ω))
    (hcont : CompactContainment e D hG z start Xexp)
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) : True := by
  have _fits := twoClockScalingLimit_of_window_modulus_of_finiteDimensional e D hG z Φ
    target start Xexp Xexact M hclock (Set.Ioc 0 1) Ioc_zero_one_mem_nhdsWithin
    (hmodExp_of_clock_inputs e D hG z Φ start Xexp Xexact M hclock hz hsub hdiam hdense
      hcont harray)
  trivial

end ReflectedGMS.ActualWindowModulus
