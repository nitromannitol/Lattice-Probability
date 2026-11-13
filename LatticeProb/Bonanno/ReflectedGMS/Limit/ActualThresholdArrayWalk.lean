/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualThresholdArrayWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayRescale
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayDescent
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketClausesScalarReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.CompactContainmentProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledBracketLLNBridge
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystem
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNPolarizedWeld

/-!
**⚠ VACUOUS/SUPERSEDED (2026-09-18):** `harray` here is sound (it takes the LLN as a hypothesis),
but the supplier of `hLLN`/`hdir` named below and in the docstring of
`harray_of_canonicalBracket_of_directionalLLN`,
`RescaledBracketLLNBridgeWalk.rescaledBracketLLN_dirBracket_of_regenerativeInvariance_target`, is
VACUOUS at a continuous environment law (its `hQP`, AGENTS.md "VACUITY (fifth)").  Use
`RescaledBracketLLNBridgeDisintegrated.rescaledBracketLLN_dirBracket_of_regenerativeInvariance_disintegrated_target`
or, from every start, `BracketLLNAllStarts.rescaledBracketLLN_dirBracket_allStarts_target`.

# `harray` at the actual rescaled walk

The `harray` slot of the four walk consumers
(`CompactContainmentProducer.compactContainment_of_arrays`, `ExactClockModulus`,
`RescaledInterpolationError`, `ActualWindowModulus`) asks, for every positive null scale sequence,
every coordinate `k` and every horizon `H`,

`Nonempty (LocalizedMartingaleArray (areaSampleLaw …) (fun n u ω => εₙ * M (εₙ⁻² u) ω k) H)`

where `M` is the walk's harmonic-coordinate spatial extension.  This module produces it:

* `harray_completion_of_canonicalBracket` — on the **completed** sample space, from the walk's
  bracket `InvarianceMainStatement.CanonicalBracket` (i.e. `HasOrdinaryEdgeBracket` on the
  completed natural filtration, the invariance assembly's `hbracket`), the start value of `M`,
  and the bracket law of large numbers `RescaledBracketLLN` of each diagonal bracket.  This is
  `ActualThresholdArray.harray_of_local_coordinate` at the coordinate `N = M·k`, `A = [M]_{kk}`,
  `p = Φ(start) k`; every field of the local threshold lane is discharged from `CanonicalBracket`
  except the bracket LLN.
* `harray_of_canonicalBracket` — **the consumer shape**, on the original sample space, via the
  completion descent `ActualThresholdArrayDescent.nonempty_localizedMartingaleArray_of_completion`.
  The start value is not a hypothesis: `ae_start_of_pathwiseClockClauses` derives `M 0 = Φ start`
  a.s. from `PathwiseClockClauses`, which every consumer already holds.
* `harray_of_canonicalBracket_of_directionalLLN` — the same with the bracket LLN in the directional
  form `∀ η, RescaledBracketLLN P (dirBracket B η) (ηᵀΣη)`, which is verbatim the conclusion of the
  regeneration lane's
  `RescaledBracketLLNBridgeWalk.rescaledBracketLLN_dirBracket_of_regenerativeInvariance_target`
  (at `η = eₖ`, `dirBracket B eₖ = B k k`, `dirBracket_single`).

The final `example` feeds `harray_of_canonicalBracket` into
`CompactContainmentProducer.compactContainment_of_arrays`, so the binders match.

## What `harray` costs at the walk (honest list)

* `hclock : PathwiseClockClauses …` — already a hypothesis of every consumer.
* `hbr : CanonicalBracket e D Φ P M` — the invariance assembly's `hbracket` input, owned by the
  bracket lane (`Limit/CanonicalBracketClauses`, `Limit/BracketClausesScalarReduction` reduce it to
  atomic clauses).
* `hLLN` / `hdir` — the bracket law of large numbers, owned by the regeneration lane.

Nothing else: no true-martingale hypothesis (the local→global passage is inside the producer),
no `null`-set hypothesis on the original space (which would be unsatisfiable, see
`ActualThresholdArrayDescent`), no start-point hypothesis, no bracket-slope sign hypothesis
(`rescaledBracketLLN_const_nonneg`), no monotonicity hypothesis (the diagonal density is
nonnegative, `stateBracketDensity_diag_nonneg`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ActualThresholdArray

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement MartingaleIngredients
open ReflectedWalk QuenchedFormulation ProcessFiltration
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.ApproximateBracketCLT
open ReflectedGMS.RescaledBracketLLNBridge

/-! ## From the plane to one coordinate -/

section Coordinates

variable {Ω : Type*} {m : MeasurableSpace Ω}

theorem martingale_coord {P : Measure Ω} {F : Filtration ℝ≥0 m}
    {Y : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hY : Martingale Y F P) (k : Fin 2) :
    Martingale (fun t ω => Y t ω k) F P := by
  have hfun : ∀ t, (fun ω => Y t ω k) =
      (EuclideanSpace.proj (𝕜 := ℝ) k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ Y t :=
    fun _ => rfl
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · exact (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_stronglyMeasurable
      (hY.stronglyAdapted t)
  · show P[fun ω => Y j ω k | F i] =ᵐ[P] fun ω => Y i ω k
    rw [hfun j, hfun i]
    exact ((EuclideanSpace.proj (𝕜 := ℝ) k).comp_condExp_comm (m := F i)
      (hY.integrable j)).symm.trans ((hY.condExp_ae_eq hij).fun_comp _)

theorem memLp_coord {P : Measure Ω} {f : Ω → EuclideanSpace ℝ (Fin 2)} {p : ℝ≥0∞}
    (hf : MemLp f p P) (k : Fin 2) : MemLp (fun ω => f ω k) p P :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).comp_memLp' hf

/-- **A coordinate of a plane-valued locally square-integrable martingale is one**, with the same
localizing sequence. -/
theorem isLocallySquareIntegrableMartingale_coord {P : Measure Ω} {F : Filtration ℝ≥0 m}
    {M : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)}
    (hM : MartingaleIngredients.IsLocallySquareIntegrableMartingale P F M) (k : Fin 2) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P F (fun t ω => M t ω k) := by
  refine ⟨fun t => (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_stronglyMeasurable
      (hM.1 t), hM.2.localSeq, hM.2.isLocalizingSequence_localSeq, fun n => ?_⟩
  obtain ⟨hmart, hmem⟩ := hM.2.stoppedProcess_localSeq n
  have heq : (fun t ω => stoppedProcess (fun t => {ω | ⊥ < hM.2.localSeq n ω}.indicator (M t))
        (hM.2.localSeq n) t ω k) =
      stoppedProcess (fun t => {ω | ⊥ < hM.2.localSeq n ω}.indicator (fun ω => M t ω k))
        (hM.2.localSeq n) := by
    funext t ω
    exact PlaneCoordinateMartingale.stoppedProcess_indicator_coord M _ k t ω
  have key : Martingale (fun t ω => stoppedProcess
        (fun t => {ω | ⊥ < hM.2.localSeq n ω}.indicator (M t)) (hM.2.localSeq n) t ω k) F P ∧
      ∀ t, MemLp ((fun t ω => stoppedProcess
        (fun t => {ω | ⊥ < hM.2.localSeq n ω}.indicator (M t)) (hM.2.localSeq n) t ω k) t)
          2 P :=
    ⟨martingale_coord hmart k, fun t => memLp_coord (hmem t) k⟩
  rw [heq] at key
  exact key

end Coordinates

/-! ## The diagonal bracket is nonnegative and monotone -/

theorem stateBracketDensity_diag_nonneg {V : Type*} (cells : IndexedCells V) (Φ : V → Plane)
    (q : Option V) (k : Fin 2) : 0 ≤ stateBracketDensity cells Φ q k k := by
  cases q with
  | none => simp
  | some v =>
    simp only [stateBracketDensity_some, StatementIngredients.bracketDensity]
    refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (tsum_nonneg fun w => ?_)
    rw [mul_assoc]
    exact mul_nonneg (cells.graph.c_nonneg v w) (mul_self_nonneg _)

theorem ordinaryEdgeBracket_diag_monotone {Ω V : Type*} (cells : IndexedCells V)
    (Φ : V → Plane) (X : ℝ≥0 → Ω → Option V) (ω : Ω) (k : Fin 2)
    (hint : ∀ t : ℝ≥0, IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X s.toNNReal ω) k k) volume 0 (t : ℝ)) :
    Monotone (fun t => ordinaryEdgeBracket cells Φ X k k t ω) := by
  intro a b hab
  simp only [ordinaryEdgeBracket]
  have hsub := intervalIntegral.integral_interval_sub_left (hint b) (hint a)
  have hnn : 0 ≤ ∫ s in (a : ℝ)..(b : ℝ), stateBracketDensity cells Φ (X s.toNNReal ω) k k :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hab)
      fun u _ => stateBracketDensity_diag_nonneg cells Φ _ k
  linarith

/-- The directional bracket along a coordinate vector is the diagonal entry. -/
theorem dirBracket_single {Ω : Type*} (B : Fin 2 → Fin 2 → ℝ≥0 → Ω → ℝ) (k : Fin 2) :
    dirBracket B (EuclideanSpace.single k 1) = B k k := by
  funext u ω
  fin_cases k <;> simp [dirBracket, Fin.sum_univ_two, EuclideanSpace.single_apply]

/-! ## The start value -/

/-- **The harmonic extension starts at the harmonic coordinate of the start vertex**, almost
surely, as a consequence of the pathwise clock clauses alone. -/
theorem ae_start_of_pathwiseClockClauses (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), M 0 ω = Φ.at e start := by
  have hproc : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Existence.process D (areaRate (decode e)) 0 ω = some start :=
    Existence.ae_process_zero D hG (areaRate (decode e))
      (EnvironmentWalkDataProducer.areaRate_pos e) start
  filter_upwards [hclock, hproc] with ω hc hpr
  obtain ⟨hc1, -, -, -, -, -, -, -, -, hreg⟩ := hc
  have hexp0 : exponentialAreaPath (decode e) D 0 ω = some start := hpr
  have hX0 : Xexp 0 ω = Sum.inl start :=
    TwoClockScalingLimitReduction.eq_inl_of_collapse_eq_some ((hc1 0).trans hexp0)
  exact hreg.1.2.1 0 start hX0

/-! ## `harray` on the completed sample space -/

/-- The bracket law of large numbers transfers verbatim to the completion
(`Measure.completion_apply` is `rfl`). -/
theorem rescaledBracketLLN_completion {Ω : Type*} {m : MeasurableSpace Ω} {P : @Measure Ω m}
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ} (h : RescaledBracketLLN P A C) :
    RescaledBracketLLN (Ω := NullMeasurableSpace Ω P) P.completion A C :=
  fun ε hε t δ hδ => h ε hε t δ hδ

/-- **`harray` on the completed sample space**, from the walk's bracket, the start value and the
diagonal bracket laws of large numbers. -/
theorem harray_completion_of_canonicalBracket (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (p : Plane) (hstart : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), M 0 ω = p)
    (C : Fin 2 → ℝ)
    (hLLN : ∀ k : Fin 2, RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
      (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k) (C k)) :
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray
          (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val))
            (areaSampleLaw (decode e) D hG start))
          (areaSampleLaw (decode e) D hG start).completion
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H) := by
  intro ε hεpos hεlim k H
  have hP : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
    BracketClausesScalarReduction.isProbabilityMeasure_areaSampleLaw e D hG start
  have hPc : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start).completion :=
    ⟨(Measure.completion_apply _ Set.univ).trans measure_univ⟩
  obtain ⟨hloc, hpath, hcov⟩ := hbr
  have hcovk := hcov k k
  exact harray_of_local_coordinate
    (areaFiltration e D (areaSampleLaw (decode e) D hG start))
    (fun t ω => M t ω k)
    (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k)
    (p k) (C k)
    (BracketClausesScalarReduction.measurableSet_areaFiltration_of_null e D hG start)
    (isLocallySquareIntegrableMartingale_coord hloc k)
    hcovk.2.2
    (hpath.mono fun ω h => h.1.continuous_comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k))
    (ae_completion_of_ae (hstart.mono fun ω h => congrArg (fun v : Plane => v k) h))
    (hcovk.2.1.mono fun ω h => h.1)
    (hcovk.2.1.mono fun ω h => h.2.1)
    (hpath.mono fun ω h => ordinaryEdgeBracket_diag_monotone _ _ _ ω k fun t => h.2 k k t)
    (rescaledBracketLLN_completion (hLLN k)) ε hεpos hεlim H

/-! ## `harray` at the walk, in the consumers' shape -/

/-- **`harray` at the actual rescaled walk.**  Exactly the binder of
`CompactContainmentProducer.compactContainment_of_arrays`, `ExactClockModulus`,
`RescaledInterpolationError` and `ActualWindowModulus`, from:

* `hclock` — the pathwise clock clauses (already held by every consumer);
* `hbr` — the walk's bracket `CanonicalBracket` (the invariance assembly's `hbracket`);
* `hLLN` — the bracket law of large numbers of each diagonal bracket (the regeneration lane). -/
theorem harray_of_canonicalBracket (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (C : Fin 2 → ℝ)
    (hLLN : ∀ k : Fin 2, RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
      (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k) (C k)) :
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H) := by
  intro ε hεpos hεlim k H
  have hP : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
    BracketClausesScalarReduction.isProbabilityMeasure_areaSampleLaw e D hG start
  exact nonempty_localizedMartingaleArray_of_completion _
    (harray_completion_of_canonicalBracket e D hG Φ start M hbr (Φ.at e start)
      (ae_start_of_pathwiseClockClauses e D hG Φ start Xexp Xexact M hclock) C hLLN
      ε hεpos hεlim k H)

/-- **`harray` at the walk from the directional bracket LLN** — the exact output form of the
regeneration lane (`RescaledBracketLLNBridgeWalk.rescaledBracketLLN_dirBracket_of_regenerativeInvariance_target`),
with slopes `C k = eₖᵀ Σ eₖ`.  (⚠ 2026-09-18: that supplier is vacuous through its `hQP`; use
`BracketLLNAllStarts.rescaledBracketLLN_dirBracket_allStarts_target`.) -/
theorem harray_of_canonicalBracket_of_directionalLLN (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (target : AnisotropicBrownianTarget)
    (hdir : ∀ η : EuclideanSpace ℝ (Fin 2),
      RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
        (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η)
        (GaussianLimitIdentification.bilinForm target.covariance η η)) :
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H) :=
  harray_of_canonicalBracket e D hG Φ start Xexp Xexact M hclock hbr
    (fun k => GaussianLimitIdentification.bilinForm target.covariance
      (EuclideanSpace.single k 1) (EuclideanSpace.single k 1))
    (fun k => by
      have h := hdir (EuclideanSpace.single k 1)
      rwa [dirBracket_single] at h)

/-! ## Shape check against a consumer

`harray_of_canonicalBracket` fills the `harray` slot of
`CompactContainmentProducer.compactContainment_of_arrays` with no adaptation: this `example`
elaborates. -/

example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (C : Fin 2 → ℝ)
    (hLLN : ∀ k : Fin 2, RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
      (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k)
        (C k)) :
    ActualWindowModulus.CompactContainment e D hG z start Xexp :=
  CompactContainmentProducer.compactContainment_of_arrays e D hG z Φ start Xexp M hz hsub
    (Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1)
    (harray_of_canonicalBracket e D hG Φ start Xexp Xexact M hclock hbr C hLLN)

end ReflectedGMS.ActualThresholdArray
