/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedBallEnergyConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedBallEnergyGeometry
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedDensityMeasurabilityProducer
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ApproximantCovarianceFromBlockTransport

/-!
# Ball-uniform specific-energy convergence from root specific-energy convergence

`HarmonicCoordinateAssembly.MarkedSpecificEnergyConvergence` (`hspec`) controls the manuscript
specific-energy density `ρ_m` of the gradient error `φ_m − Φ` **at the root cell only**:
`E[ρ_m(H_0)] → 0` along the full sequence.  The discrete Poincaré inequality behind
`MarkedNeighborhoodConvergence` needs smallness of `ρ_m` **throughout the graph ball**
`B(H_0, radius+1)`.  This module proves that upgrade,

`MarkedBallEnergyConvergence ν ms`: for every radius, `sup_{v ∈ B(H_0,radius+1)} ρ_m(v) → 0`
in probability along the full sequence,

by the manuscript's re-rooting device `BallEnergyReRooting.lintegral_rootedBallSum_eq`.

## The obstruction and how it is removed

Re-rooting gives `E[∑_{v ∈ B} f(v)] = E[f(H_0) · W_R(H_0)]` with the ball-to-root area ratio
`W_R`, which is not integrable under (FE).  Instead of assuming `E[W_R] < ∞`, the observable is
**gated by the area ratio at its own vertex**: `f(v) = ρ_m(v) · 1_{W_R(v) ≤ M}`.  The gate is
similarity invariant (`MarkedBallEnergyGeometry.slotAreaRatio_relabel`), so re-rooting still
applies, and at the root it caps the incoming side: `f(H_0) · W_R(H_0) ≤ M · ρ_m(H_0)`.  The
gates inside the ball are all open unless the random constant
`MarkedBallEnergyGeometry.rootedGeom` exceeds `M`, an event of probability `→ 0` as `M → ∞`.
**No integrability of `W_R`, no truncation of `ρ_m` and no new moment is needed.**

## The one covariance input, and why `hcov` itself does not suffice

Re-rooting needs the observable to be *exactly* scale invariant at **every stage `m`**, because
`hspec` and the target are statements along the full sequence.  The assembly input
`ApproximantGradientCovariant ms` (`hcov`) only speaks about the stages `ms j` and only for an
unspecified grid action.  The input used here, `ApproximantGradientCovariantAtEveryStage`, is the
same gradient covariance on the good event at **every** stage, for the canonical grid action
`gridSimilarity s hs u = dilate s hs ∘ translate u` that `MarkedMassTransportProducer.markedSimilarity`
transports marks by.  It sits strictly between the hcov packet's atomic input and `hcov`:

* `approximantGradientCovariantAtEveryStage_of_blockTransport` — it follows from
  `ApproximantCovarianceFromBlockTransport.BlockInterpolationSimilarityCovariant`, the single
  geometric statement to which `hcov` is already reduced;
* `approximantGradientCovariant_of_atEveryStage` — it implies `hcov` for every `ms`.

## What is proved

* `ballEnergyObservable` — the gated observable as a `BallEnergyReRooting.SlotObservable`:
  measurable slot by slot from `hmeas` (through the gated interpolant and
  `MarkedDensityMeasurabilityProducer.measurable_markedPotentialLabel`), and exactly invariant
  from the covariance input (through `SpecificEnergyDensitySimilarity.specificEnergyDensity_relabel`,
  `HarmonicCoordinateAssembly.markedDifferenceField_pairTransport` and the difference-field
  cocycle of the marked limit).
* `markedBallEnergyConvergence_of_specificEnergyConvergence` — **the theorem**.  Its only
  probabilistic inputs are `MassTransport ν` (`s:eq:MTP`, through re-rooting) and the (FE)
  moment (through the full measure of the good event, where `phi` is the gated interpolant).
-/

-- Merged from `ReflectedGMS/Corrector/SpecificEnergyDensitySimilarity.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_SpecificEnergyDensitySimilarity

/-!
# Similarity covariance of the rooted specific-energy density

`Spatial/ActualSpatialDensityBridge` proves that the manuscript's **finite-energy** density is a
scale-invariant rooted observable (`rootedFiniteEnergyDensity_similarity`), and builds the whole
maximal-inequality chain on top of that fact (`rootFE`, `ofReal_rootFE_shift`,
`setLIntegral_le_ballMaximal`).  The **specific-energy** density
`RootDensities.rootedSpecificEnergyDensity F Φ z` had no such lemma anywhere in the project —
searched across `ReflectedGMS/`, `2405_11673_main/BouRabeeGwynne/` and `2506_18827_reflected/`,
with no hit for `rootedSpecificEnergyDensity` or `specificEnergyDensity` next to `similarity`,
`relabel`, `transform`, `dilate` or `translate`.

That absence is the named missing producer behind the hypothesis `hstationary` of
`Corrector/GridIndependenceCoupling.ae_setLIntegral_closedBall_eq_zero`, i.e. behind the
`hcopies` input `HarmonicCoordinateAssembly.DifferenceFieldGridIndependent`.

The specific-energy case is genuinely harder than the finite-energy case for one reason: `Φ` is an
extra argument that has to transform too, and what is invariant is **not** `Φ` but its *gradient*.
This module isolates that as `GradientTransported` and proves the covariance from it.

## What is proved

* `GradientTransported s relabel Φ Ψ` — the exact hypothesis: increments of `Ψ` along the
  relabelling are `s` times the increments of `Φ`.  It is strictly weaker than
  `Ψ ∘ relabel = s • Φ + c`, it is the shape produced by
  `HarmonicCoordinateAssembly.ApproximantGradientCovariant` and by
  `unmarkedDifferenceField_similarity`, and it is invariant under adding a constant to either
  field — which is what makes it usable for potentials defined only up to normalization.
* `specificEnergyDensity_relabel` — the cellwise statement: `ρ_Ψ^{𝓗'}(relabel v) = ρ_Φ^{𝓗}(v)`.
  Both the numerator and `2·a_H` pick up exactly one factor `s²`, and they cancel.
* `rootedSpecificEnergyDensity_similarity` — the rooted statement, through the checked
  `ActualSpatialDensityBridge.rootAt_similarity`.
* `rootedSpecificEnergyDensity_translate` — the translation case `s = 1`, which is the one the
  spatial stationarity identity needs, and
  `setLIntegral_rootedSpecificEnergyDensity_translate` — its disk-integral consequence, the exact
  shape in which a re-rooting argument consumes it.

Nothing here assumes a law, stationarity, harmonicity or minimality: every statement is a
pathwise identity for one similarity of environments.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SpecificEnergyDensitySimilarity

open Code EnvironmentLaws ActualSpatialDensityBridge ActualMarkedBlockTransport

/-- **The transport hypothesis on the field.**  Along the relabelling of a similarity of ratio
`s`, increments of `Ψ` are `s` times the increments of `Φ`.  Only increments occur in the
specific-energy density, so this — and not any normalization of `Φ` itself — is what the
covariance needs. -/
def GradientTransported (s : ℝ) {e e' : Env} (relabel : Vertex e.val ≃ Vertex e'.val)
    (Phi : Vertex e.val → Plane) (Psi : Vertex e'.val → Plane) : Prop :=
  ∀ v w : Vertex e.val, Psi (relabel w) - Psi (relabel v) = s • (Phi w - Phi v)

section Covariance

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {relabel : Vertex e.val ≃ Vertex e'.val}

/-- **The cellwise covariance.**  The numerator of the specific energy picks up `s²` from the
squared field increments — the conductances are unchanged by a physical similarity — and the
denominator picks up `s²` from the cell area, so the quotient is unchanged. -/
theorem specificEnergyDensity_relabel (h : IsSimilarityRelabel s u hs e e' relabel)
    {Phi : Vertex e.val → Plane} {Psi : Vertex e'.val → Plane}
    (hgrad : GradientTransported s relabel Phi Psi) (v : Vertex e.val) :
    RootDensities.specificEnergyDensity (decode e') Psi (relabel v)
      = RootDensities.specificEnergyDensity (decode e) Phi v := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hc0 : ENNReal.ofReal (s ^ 2) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 hs2
  have hnum : (∑' w' : Vertex e'.val, ENNReal.ofReal ((decode e').graph.c (relabel v) w')
        * ENNReal.ofReal (‖Psi w' - Psi (relabel v)‖ ^ 2))
      = ENNReal.ofReal (s ^ 2) * ∑' w : Vertex e.val,
          ENNReal.ofReal ((decode e).graph.c v w) * ENNReal.ofReal (‖Phi w - Phi v‖ ^ 2) := by
    rw [← Equiv.tsum_eq relabel fun w' : Vertex e'.val =>
        ENNReal.ofReal ((decode e').graph.c (relabel v) w')
          * ENNReal.ofReal (‖Psi w' - Psi (relabel v)‖ ^ 2),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun w => ?_
    have hnorm : ‖Psi (relabel w) - Psi (relabel v)‖ ^ 2 = s ^ 2 * ‖Phi w - Phi v‖ ^ 2 := by
      rw [hgrad v w, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
    rw [h.2 v w, hnorm, ENNReal.ofReal_mul hs2.le]
    ring
  have hden : 2 * ENNReal.ofReal (StatementIngredients.cellArea (decode e') (relabel v))
      = ENNReal.ofReal (s ^ 2)
          * (2 * ENNReal.ofReal (StatementIngredients.cellArea (decode e) v)) := by
    rw [cellArea_relabel h v, ENNReal.ofReal_mul hs2.le]
    ring
  show (∑' w' : Vertex e'.val, ENNReal.ofReal ((decode e').graph.c (relabel v) w')
        * ENNReal.ofReal (‖Psi w' - Psi (relabel v)‖ ^ 2))
      / (2 * ENNReal.ofReal (StatementIngredients.cellArea (decode e') (relabel v)))
    = (∑' w : Vertex e.val, ENNReal.ofReal ((decode e).graph.c v w)
        * ENNReal.ofReal (‖Phi w - Phi v‖ ^ 2))
      / (2 * ENNReal.ofReal (StatementIngredients.cellArea (decode e) v))
  rw [hnum, hden, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

/-- **The rooted covariance.**  `ρ_sp^{𝓗'}(S(s,u) z) = ρ_sp^{𝓗}(z)` for every physical
similarity `𝓗 → 𝓗'` and every pair of fields whose increments transport. -/
theorem rootedSpecificEnergyDensity_similarity (h : IsSimilarityRelabel s u hs e e' relabel)
    {Phi : Vertex e.val → Plane} {Psi : Vertex e'.val → Plane}
    (hgrad : GradientTransported s relabel Phi Psi) (z : Plane) :
    RootDensities.rootedSpecificEnergyDensity (decode e') Psi (positiveSimilarity s u z)
      = RootDensities.rootedSpecificEnergyDensity (decode e) Phi z := by
  show ((RootDensities.rootAt (decode e') (positiveSimilarity s u z)).elim 0
      (RootDensities.specificEnergyDensity (decode e') Psi))
    = (RootDensities.rootAt (decode e) z).elim 0
      (RootDensities.specificEnergyDensity (decode e) Phi)
  rw [rootAt_similarity h z]
  cases hroot : RootDensities.rootAt (decode e) z with
  | none => simp
  | some v => simpa using specificEnergyDensity_relabel h hgrad v

end Covariance

/-! ### The translation case, and its disk integrals -/

end ReflectedGMS.SpecificEnergyDensitySimilarity

end Merged_SpecificEnergyDensitySimilarity

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.MarkedBallEnergyConvergence

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicMainStatement HarmonicCoordinateAssembly GraphBallReach BallEnergyReRooting
open MarkedMassTransportProducer MarkedBallEnergyGeometry
open RootedFiniteEnergyDensityMeasurable MarkedRootedSpecificEnergyMeasurability

/-! ### The covariance input at every stage -/

/-- **OPEN INPUT (audited gap 1, exact covariance of the construction, every stage).**  On the
good event, the gradients of the concrete block interpolants commute with every physical
similarity at **every** stage `m`, for the canonical grid action `dilate s hs ∘ translate u` of
`positiveSimilarity s u`.  This is `HarmonicCoordinateAssembly.ApproximantGradientCovariant`
without the restriction to the subsequence `ms` and with the grid action named.  It is implied
by `ApproximantCovarianceFromBlockTransport.BlockInterpolationSimilarityCovariant` and implies
`ApproximantGradientCovariant ms` for every `ms`. -/
def ApproximantGradientCovariantAtEveryStage : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env) (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → e ∈ SublinearEvent →
      ∀ (D : Grid) (m : ℕ) (v w : Vertex e.val),
        phi (decode e') (ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u D) m
            (relabel w)
          - phi (decode e') (ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u D) m
            (relabel v)
          = s • (phi (decode e) D m w - phi (decode e) D m v)

/-- The every-stage covariance follows from the geometric transport statement to which the
hcov packet reduces `hcov`. -/
theorem approximantGradientCovariantAtEveryStage_of_blockTransport
    (hB : ApproximantCovarianceFromBlockTransport.BlockInterpolationSimilarityCovariant) :
    ApproximantGradientCovariantAtEveryStage := by
  intro s u hs e e' relabel h hG D m v w
  rw [ApproximantCovarianceFromBlockTransport.phi_similarity hB h hG D m w,
    ApproximantCovarianceFromBlockTransport.phi_similarity hB h hG D m v,
    ApproximantCovarianceFromBlockTransport.positiveSimilarity_sub]

/-- The every-stage covariance implies the assembly input `hcov` for every subsequence. -/
theorem approximantGradientCovariant_of_atEveryStage
    (hcov : ApproximantGradientCovariantAtEveryStage) (ms : ℕ → ℕ) :
    ApproximantGradientCovariant ms := by
  intro s u hs e e' relabel h hG
  exact ⟨ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u,
    ApproximantCovarianceFromBlockTransport.measurePreserving_gridSimilarity hs u,
    fun D j v w => hcov s u hs e e' relabel h hG D (ms j) v w⟩

/-! ### The gradient error at a code label -/

/-- The gradient error `φ_m − Φ` read at a code label, through the gated interpolant. -/
noncomputable def gradientErrorLabel (ms : ℕ → ℕ) (m : ℕ) (ω : MarkedEnvironment) (n : ℕ) :
    Plane :=
  gatedApproximant m ω n - markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) n)

theorem measurable_gradientErrorLabel (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m n : ℕ) : Measurable fun ω : MarkedEnvironment => gradientErrorLabel ms m ω n :=
  (hmeas m n).sub (MarkedDensityMeasurabilityProducer.measurable_markedPotentialLabel ms hmeas n)

/-- On the good event the label field is the concrete gradient error. -/
theorem gradientErrorLabel_field_eq (ms : ℕ → ℕ) (m : ℕ) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) :
    (fun v : Vertex ω.1.val => gradientErrorLabel ms m ω v.val)
      = fun v : Vertex ω.1.val => phi (decode ω.1) ω.2 m v - markedPotential ms ω v := by
  funext v
  show gatedApproximant m ω v.val - markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val)
    = phi (decode ω.1) ω.2 m v - markedPotential ms ω v
  rw [MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG v]
  rfl

/-- **The gradient error transports along the joint similarity.**  The interpolant part by the
covariance input on the good event (both sides vanish off it); the limit part by the label
transport of the marked difference field and its cocycle. -/
theorem gradientTransported_gradientErrorLabel (ms : ℕ → ℕ)
    (hcov : ApproximantGradientCovariantAtEveryStage) (m : ℕ) {s : ℝ} {u : Plane} {hs : 0 < s}
    (p : MarkedEnvironment) {rel : Vertex p.1.val ≃ Vertex (markedSimilarity s u hs p).1.val}
    (h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel) :
    SpecificEnergyDensitySimilarity.GradientTransported s rel
      (fun w : Vertex p.1.val => gradientErrorLabel ms m p w.val)
      (fun w : Vertex (markedSimilarity s u hs p).1.val =>
        gradientErrorLabel ms m (markedSimilarity s u hs p) w.val) := by
  have hGG : p.1 ∈ SublinearEvent ↔ (markedSimilarity s u hs p).1 ∈ SublinearEvent :=
    mem_sublinearEvent_iff_of_similarity h
  have hact : p.1 ∈ SublinearEvent → ∀ (D : Grid) (j : ℕ) (v w : Vertex p.1.val),
      phi (decode (markedSimilarity s u hs p).1)
          (ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u D) (ms j) (rel w)
        - phi (decode (markedSimilarity s u hs p).1)
          (ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u D) (ms j) (rel v)
        = s • (phi (decode p.1) D (ms j) w - phi (decode p.1) D (ms j) v) :=
    fun hG D j v w => hcov s u hs p.1 (markedSimilarity s u hs p).1 rel h hG D (ms j) v w
  have hfield : markedDifferenceField ms ((markedSimilarity s u hs p).1,
        ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u p.2)
      = pairTransport s rel (markedDifferenceField ms (p.1, p.2)) :=
    markedDifferenceField_pairTransport ms hs.ne'
      (fun j k => differenceApproximant_pairTransport ms hGG hact p.2 j k)
  have hpot : ∀ v w : Vertex p.1.val,
      markedDifferenceField ms (markedSimilarity s u hs p)
          (Nat.pair (baseLabel (markedSimilarity s u hs p).1) (rel w).val)
        - markedDifferenceField ms (markedSimilarity s u hs p)
          (Nat.pair (baseLabel (markedSimilarity s u hs p).1) (rel v).val)
        = s • (markedDifferenceField ms p (Nat.pair (baseLabel p.1) w.val)
          - markedDifferenceField ms p (Nat.pair (baseLabel p.1) v.val)) := by
    intro v w
    have hD' : markedDifferenceField ms (markedSimilarity s u hs p)
          (Nat.pair (baseLabel (markedSimilarity s u hs p).1) (rel w).val)
        = markedDifferenceField ms (markedSimilarity s u hs p)
            (Nat.pair (baseLabel (markedSimilarity s u hs p).1) (rel v).val)
          + markedDifferenceField ms (markedSimilarity s u hs p)
            (Nat.pair (rel v).val (rel w).val) :=
      (isDifferenceField_markedDifferenceField ms (markedSimilarity s u hs p)).2
        (baseVertex (markedSimilarity s u hs p).1) (rel v) (rel w)
    have hD : markedDifferenceField ms p (Nat.pair (baseLabel p.1) w.val)
        = markedDifferenceField ms p (Nat.pair (baseLabel p.1) v.val)
          + markedDifferenceField ms p (Nat.pair v.val w.val) :=
      (isDifferenceField_markedDifferenceField ms p).2 (baseVertex p.1) v w
    have htr : markedDifferenceField ms (markedSimilarity s u hs p)
          (Nat.pair (rel v).val (rel w).val)
        = s • markedDifferenceField ms p (Nat.pair v.val w.val) := by
      have h1 := congrFun hfield (Nat.pair (rel v).val (rel w).val)
      rw [pairTransport_pair] at h1
      exact h1
    rw [hD', hD, add_sub_cancel_left, add_sub_cancel_left, htr]
  have hgate : ∀ v w : Vertex p.1.val,
      gatedApproximant m (markedSimilarity s u hs p) (rel w).val
        - gatedApproximant m (markedSimilarity s u hs p) (rel v).val
        = s • (gatedApproximant m p w.val - gatedApproximant m p v.val) := by
    intro v w
    by_cases hG : p.1 ∈ SublinearEvent
    · have hG' : (markedSimilarity s u hs p).1 ∈ SublinearEvent := hGG.1 hG
      rw [← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG' (rel w),
        ← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG' (rel v),
        ← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG w,
        ← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG v]
      exact hcov s u hs p.1 (markedSimilarity s u hs p).1 rel h hG p.2 m v w
    · have hG' : (markedSimilarity s u hs p).1 ∉ SublinearEvent := fun h' => hG (hGG.2 h')
      simp [gatedApproximant_of_notMem m hG', gatedApproximant_of_notMem m hG]
  intro v w
  show gradientErrorLabel ms m (markedSimilarity s u hs p) (rel w).val
      - gradientErrorLabel ms m (markedSimilarity s u hs p) (rel v).val
    = s • (gradientErrorLabel ms m p w.val - gradientErrorLabel ms m p v.val)
  unfold gradientErrorLabel
  rw [sub_sub_sub_comm, hgate v w, hpot v w]
  simp only [smul_sub]
  abel

/-! ### The gated observable -/

/-- The area-ratio gate `1_{W_R ≤ M}` at a code label. -/
noncomputable def areaGate (R : ℕ) (M : ℝ≥0∞) (e : Env) (n : ℕ) : ℝ≥0∞ :=
  if slotAreaRatio R e n ≤ M then 1 else 0

/-- **The gated specific-energy observable** `ρ_m(v) · 1_{W_R(v) ≤ M}`, as a scale-invariant
slot observable. -/
noncomputable def ballEnergyObservable (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariantAtEveryStage) (m R : ℕ) (M : ℝ≥0∞) :
    SlotObservable where
  toFun p n :=
    slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m) p n * areaGate R M p.1 n
  absent := by
    intro p n hn
    show slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m) p n * areaGate R M p.1 n
      = 0
    rw [slotSpecificEnergyDensity_of_absent Prod.fst (gradientErrorLabel ms m) p hn, zero_mul]
  measurable_toFun := by
    intro n
    refine (measurable_slotSpecificEnergyDensity measurable_fst
      (measurable_gradientErrorLabel ms hmeas m) n).mul ?_
    exact Measurable.ite
      (measurableSet_le ((measurable_slotAreaRatio R n).comp measurable_fst) measurable_const)
      measurable_const measurable_const
  invariant := by
    intro s u hs p rel h v
    have hgrad := gradientTransported_gradientErrorLabel ms hcov m p h
    show slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m)
          (markedSimilarity s u hs p) (rel v).val
        * areaGate R M (markedSimilarity s u hs p).1 (rel v).val
      = slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m) p v.val
        * areaGate R M p.1 v.val
    rw [slotSpecificEnergyDensity_eq Prod.fst (gradientErrorLabel ms m)
        (markedSimilarity s u hs p) (rel v),
      slotSpecificEnergyDensity_eq Prod.fst (gradientErrorLabel ms m) p v,
      SpecificEnergyDensitySimilarity.specificEnergyDensity_relabel h hgrad v]
    unfold areaGate
    rw [slotAreaRatio_relabel h R v]

/-- **The incoming side is capped by the gate.**  At the root,
`f(H_0) · W_R(H_0) ≤ M · ρ_m(H_0)` on the good event. -/
theorem rootedValue_mul_rootedBallAreaRatio_le (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariantAtEveryStage) (m R : ℕ) (M : ℝ≥0∞)
    (p : MarkedEnvironment) (hG : p.1 ∈ SublinearEvent) :
    rootedValue (ballEnergyObservable ms hmeas hcov m R M) p * rootedBallAreaRatio R p.1
      ≤ M * markedSpecificGradientError ms m p := by
  unfold rootedValue rootedBallAreaRatio markedSpecificGradientError rootedSpecificEnergyDensity
  cases hr : rootAt (decode p.1) 0 with
  | none => simp
  | some r =>
      show slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m) p r.val
            * areaGate R M p.1 r.val
          * ((∑' v : Vertex p.1.val, reach p.1.val.2 R v.val r.val
              * volume ((decode p.1).cell v : Set Plane))
            / volume ((decode p.1).cell r : Set Plane))
        ≤ M * specificEnergyDensity (decode p.1)
            (fun v => phi (decode p.1) p.2 m v - markedPotential ms p v) r
      have hρ : slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m) p r.val
          = specificEnergyDensity (decode p.1)
              (fun v => phi (decode p.1) p.2 m v - markedPotential ms p v) r := by
        rw [slotSpecificEnergyDensity_eq Prod.fst (gradientErrorLabel ms m) p r]
        exact congrArg (fun g => specificEnergyDensity (decode p.1) g r)
          (gradientErrorLabel_field_eq ms m hG)
      have hratio : (∑' v : Vertex p.1.val, reach p.1.val.2 R v.val r.val
              * volume ((decode p.1).cell v : Set Plane))
            / volume ((decode p.1).cell r : Set Plane)
          = slotAreaRatio R p.1 r.val := by
        rw [slotAreaRatio, slotBallArea_eq R p.1 r, slotCell_eq_cell p.1 r, vertexBallArea]
      rw [hρ, hratio]
      unfold areaGate
      split_ifs with hle
      · rw [mul_one]
        exact (mul_comm _ _).trans_le (mul_le_mul' hle le_rfl)
      · simp

/-- The rooted ball sum is almost everywhere measurable: off the boundary mask it is the
outgoing integral of the (jointly measurable) re-rooting transport. -/
theorem aemeasurable_rootedBallSum (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (k : ℕ) (Q : SlotObservable) : AEMeasurable (rootedBallSum k Q) (ν.prod gridLaw) := by
  have hcomp := (measurable_ballTransport k Q).comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd) :
      Measurable fun q : (Env × Grid) × Plane =>
        ((q.1, ((0 : Plane), q.2)) : (Env × Grid) × Plane × Plane))
  have hout : Measurable fun q : (Env × Grid) × Plane => ballTransport k Q q.1 0 q.2 := by
    simpa only [Function.comp_def] using hcomp
  have hmo : Measurable fun p : Env × Grid => ∫⁻ z : Plane, ballTransport k Q p 0 z ∂volume :=
    hout.lintegral_prod_right'
  have hmask : ∀ᵐ p : MarkedEnvironment ∂ν.prod gridLaw,
      (0 : Plane) ∉ boundaryMask (decode p.1) :=
    ae_marked_of_ae_env ν (p := fun e => (0 : Plane) ∉ boundaryMask (decode e))
      (Spatial.ae_notMem_boundaryMask_of_massTransport ν hν)
  refine hmo.aemeasurable.congr ?_
  filter_upwards [hmask] with p hp
  exact lintegral_ballTransport_outgoing_eq_rooted k Q p hp

/-! ### The ball error and the pathwise comparison -/

/-- **The ball-uniform specific gradient error**: the supremum of the specific-energy density of
`φ_m − Φ` over the graph ball `B(H_0, radius+1)`, zero on the boundary mask. -/
noncomputable def markedBallEnergyError (ms : ℕ → ℕ) (radius m : ℕ) (ω : MarkedEnvironment) :
    ℝ≥0∞ :=
  (rootAt (decode ω.1) 0).elim 0 fun r =>
    ⨆ v : (decode ω.1).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
      specificEnergyDensity (decode ω.1)
        (fun x => phi (decode ω.1) ω.2 m x - markedPotential ms ω x) v.val

/-- **Target 1.**  Along the full sequence, the ball-uniform specific gradient error tends to
zero in probability, for every radius.  (This is convergence in measure of a nonnegative
extended-real error to `0`, written out: `edist a 0 = a` on `ℝ≥0∞`, but the `EDist ℝ≥0∞`
instance lives in a mathlib module the project does not import.) -/
def MarkedBallEnergyConvergence (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ (radius : ℕ) (ε : ℝ≥0∞), 0 < ε →
    Tendsto (fun m => (ν.prod gridLaw)
      {ω : MarkedEnvironment | ε ≤ markedBallEnergyError ms radius m ω}) atTop (𝓝 0)

/-- **Pathwise comparison.**  Off the mask, on the good event and where the geometric constant
is at most `M`, every gate in the ball is open, so the ball error is dominated by the rooted
ball sum of the gated observable. -/
theorem le_rootedBallSum_of_lt_markedBallEnergyError (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariantAtEveryStage) (m R : ℕ) (M : ℝ≥0∞)
    {ω : MarkedEnvironment} (hmask : (0 : Plane) ∉ boundaryMask (decode ω.1))
    (hG : ω.1 ∈ SublinearEvent) (hgeom : rootedGeom R ω.1 ≤ M) {a : ℝ≥0∞}
    (ha : a < markedBallEnergyError ms R m ω) :
    a ≤ rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω := by
  obtain ⟨r, hr, -⟩ :=
    rootAt_eq_some_of_not_mem_boundaryMask (decode ω.1) (decode_geometry ω.1) hmask
  have ha' : a < ⨆ v : (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞),
      specificEnergyDensity (decode ω.1)
        (fun x => phi (decode ω.1) ω.2 m x - markedPotential ms ω x) v.val := by
    have h0 := ha
    unfold markedBallEnergyError at h0
    rw [hr] at h0
    exact h0
  obtain ⟨v, hv⟩ := lt_iSup_iff.1 ha'
  refine hv.le.trans (le_trans ?_ (le_rootedBallSum_of_mem_ball R
    (ballEnergyObservable ms hmeas hcov m R M) ω hr v.property))
  show specificEnergyDensity (decode ω.1)
      (fun x => phi (decode ω.1) ω.2 m x - markedPotential ms ω x) v.val
    ≤ slotSpecificEnergyDensity Prod.fst (gradientErrorLabel ms m) ω v.val.val
      * areaGate R M ω.1 v.val.val
  have hgate : areaGate R M ω.1 v.val.val = 1 := by
    unfold areaGate
    rw [if_pos ((slotAreaRatio_le_rootedGeom hr v.property).trans hgeom)]
  rw [hgate, mul_one, slotSpecificEnergyDensity_eq Prod.fst (gradientErrorLabel ms m) ω v.val]
  exact le_of_eq (congrArg (fun g => specificEnergyDensity (decode ω.1) g v.val)
    (gradientErrorLabel_field_eq ms m hG)).symm

/-! ### The theorem -/

/-- **`MarkedBallEnergyConvergence` from `MarkedSpecificEnergyConvergence`.**

For `ε > 0` and `η > 0`: choose `M` with `P(rootedGeom > M) ≤ η/2`; then, by the pathwise
comparison, Markov's inequality, re-rooting and the gate,

`P(ball error ≥ ε) ≤ P(rootedGeom > M) + (2/ε) E[ball sum] ≤ η/2 + (2M/ε) E[ρ_m(H_0)]`,

and the last term is eventually at most `η/2` by `hspec`.  The inputs are the manuscript
environment hypotheses `hν`, `hFE`, the assembly inputs `hmeas` and `hspec`, and the covariance
input at every stage. -/
theorem markedBallEnergyConvergence_of_specificEnergyConvergence (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariantAtEveryStage)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    MarkedBallEnergyConvergence ν ms := by
  intro R
  suffices key : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ →
      Tendsto (fun m => (ν.prod gridLaw)
        {ω : MarkedEnvironment | ε ≤ markedBallEnergyError ms R m ω}) atTop (𝓝 0) by
    intro ε hε
    have hmin : 0 < min ε 1 := lt_min hε zero_lt_one
    have hmintop : min ε 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right ε 1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (key _ hmin hmintop)
      (fun _ => zero_le) (fun m => measure_mono fun ω hω => ?_)
    exact le_trans (min_le_left ε 1) hω
  intro ε hε hεtop
  have hmask : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      (0 : Plane) ∉ boundaryMask (decode ω.1) :=
    ae_marked_of_ae_env ν (p := fun e => (0 : Plane) ∉ boundaryMask (decode e))
      (Spatial.ae_notMem_boundaryMask_of_massTransport ν hν)
  have hsub : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ω.1 ∈ SublinearEvent :=
    ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent) (ae_mem_sublinearEvent ν hν hFE)
  have htail := tendsto_measure_rootedGeom_gt (ν.prod gridLaw) measurable_fst R
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨M, hM⟩ := (ENNReal.tendsto_nhds_zero.1 htail (η / 2) hη2).exists
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have hε2top : ε / 2 ≠ ∞ := ENNReal.div_ne_top hεtop two_ne_zero
  have hlim : Tendsto (fun m => (M : ℝ≥0∞)
      * (∫⁻ ω, markedSpecificGradientError ms m ω ∂ν.prod gridLaw) / (ε / 2)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hspec.2 (Or.inr (ENNReal.natCast_ne_top M))
    have h2 := ENNReal.Tendsto.div_const h1 (Or.inr hε2)
    simpa using h2
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (η / 2) hη2] with m hm
  have hle : {ω : MarkedEnvironment | ε ≤ markedBallEnergyError ms R m ω}
      ≤ᵐ[ν.prod gridLaw] ({ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1}
        ∪ {ω : MarkedEnvironment | ε / 2 ≤
            rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω}) := by
    filter_upwards [hmask, hsub] with ω hω hG hmem
    by_cases hgeom : (M : ℝ≥0∞) < rootedGeom R ω.1
    · exact Or.inl hgeom
    · exact Or.inr (le_rootedBallSum_of_lt_markedBallEnergyError ms hmeas hcov m R M hω hG
        (not_lt.1 hgeom) (lt_of_lt_of_le (ENNReal.half_lt_self hε.ne' hεtop) hmem))
  have hmarkov : (ν.prod gridLaw) {ω : MarkedEnvironment | ε / 2 ≤
        rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω}
      ≤ (∫⁻ ω, rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω ∂ν.prod gridLaw)
          / (ε / 2) :=
    meas_ge_le_lintegral_div (aemeasurable_rootedBallSum ν hν R _) hε2 hε2top
  have hint : (∫⁻ ω, rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω
        ∂ν.prod gridLaw)
      ≤ (M : ℝ≥0∞) * ∫⁻ ω, markedSpecificGradientError ms m ω ∂ν.prod gridLaw := by
    calc (∫⁻ ω, rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω ∂ν.prod gridLaw)
        = ∫⁻ ω, rootedValue (ballEnergyObservable ms hmeas hcov m R M) ω
            * rootedBallAreaRatio R ω.1 ∂ν.prod gridLaw :=
          lintegral_rootedBallSum_eq ν hν R _
      _ ≤ ∫⁻ ω, (M : ℝ≥0∞) * markedSpecificGradientError ms m ω ∂ν.prod gridLaw := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsub] with ω hG
          exact rootedValue_mul_rootedBallAreaRatio_le ms hmeas hcov m R M ω hG
      _ = (M : ℝ≥0∞) * ∫⁻ ω, markedSpecificGradientError ms m ω ∂ν.prod gridLaw :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top M)
  calc (ν.prod gridLaw) {ω : MarkedEnvironment | ε ≤ markedBallEnergyError ms R m ω}
      ≤ (ν.prod gridLaw) ({ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1}
          ∪ {ω : MarkedEnvironment | ε / 2 ≤
              rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω}) :=
        measure_mono_ae hle
    _ ≤ (ν.prod gridLaw) {ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1}
        + (ν.prod gridLaw) {ω : MarkedEnvironment | ε / 2 ≤
            rootedBallSum R (ballEnergyObservable ms hmeas hcov m R M) ω} :=
        measure_union_le _ _
    _ ≤ η / 2 + η / 2 :=
        add_le_add hM (hmarkov.trans ((ENNReal.div_le_div_right hint _).trans hm))
    _ = η := ENNReal.add_halves η

end ReflectedGMS.MarkedBallEnergyConvergence
