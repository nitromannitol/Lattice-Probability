/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CopyDifferenceDensitySimilarity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedResidualWeakMaximal
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedBallEnergyConvergence

/-!
# `hcov` and `hinv` for the grid-copy difference density

`Corrector/GatedResidualWeakMaximal.copyDifferenceWeakMaximal_of_twoGridSpace` (:522) is the
embedding-free consumer head for `hcopies`' maximal input.  It already discharges `hproj`,
`hmeas0` and `hjoint` at no cost, because `firstPotential`/`secondPotential` are
`markedPotential` at the two grid copies and contain **no `phi`**.  It still carries the two
*pathwise identities*

* `hcov` — re-rooting covariance `ρ_p(z) = ρ_{p−z}(0)`, and
* `hinv` — scale invariance `ρ_{S_t p}(0) = ρ_p(0)`,

for the copy-difference density `GatedResidualWeakMaximal.copyDifferenceDensity`.  This module
proves the single identity both are instances of, **with no hypothesis and no gate**:

`copyDifferenceDensity_coupledSimilarity` : for every `s > 0`, `u`, `z` and every point `p` of
the coupled space `Env × Grid × Grid`,

  `ρ_{Σ(s,u) p}(S(s,u) z) = ρ_p(z)`,

where `Σ(s,u)` acts by `markedSimilarity s u` on **both** grid copies simultaneously.

## Why it is free — and why it is easier than the residual case

`Corrector/ResidualDensitySimilarity` ran the analogous argument for the residual density and
needed the pathwise gate `p.1 ∈ SublinearEvent`, because the residual field is
`φ_m − Φ` and `φ` is a `Classical.choose` which is only pinned down on the good event.  The
copy-difference field is `Φ¹ − Φ²`, two marked potentials, with **no `φ`** — so no gate appears
anywhere below.

The single new ingredient is `gradientTransported_markedPotential`: the marked potential itself
transports along every joint similarity.  It is *not* new mathematics — it is the difference of
two statements that are already checked and already ungated,

* `Corrector/MarkedBallEnergyConvergence.gradientTransported_gradientErrorLabel` (:136), the
  transport of `φ_m − Φ`, whose only hypothesis `ApproximantGradientCovariantAtEveryStage` is
  discharged hypothesis-free by `Corrector/MarkedStageFieldCovariance.covariantAtEveryStage`, and
* `Corrector/MarkedStageFieldCovariance.gradientTransported_stageField` (:157), the transport of
  `φ_m` itself, also ungated,

subtracted at the stage index `0`.  Since `GradientTransported` is a linear condition on the
field (`gradientTransported_sub`), `Φ = φ₀ − (φ₀ − Φ)` transports.  Feeding that into the checked
`Corrector/SpecificEnergyDensitySimilarity.rootedSpecificEnergyDensity_similarity` gives the
identity for the difference of the two grid copies, because both copies carry the *same*
environment and therefore the *same* relabelling `similarityRelabel s u hs p.1`.

## What is DISCHARGED and what is REDUCED

* `gradientTransported_markedPotential`, `copyDifferenceDensity_coupledSimilarity` and its two
  specializations `copyDifferenceDensity_shift` / `copyDifferenceDensity_dilate` are
  **DISCHARGED**: no open input, no hypothesis, no gate.
* Nothing here is reduced or assumed; this module has no hypotheses of its own beyond the
  ambient definitions.  The marked space that `copyDifferenceWeakMaximal_of_twoGridSpace` still
  needs is built in `Spatial/CopyDifferenceThreeGridSpace`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.CopyDifferenceDensitySimilarity

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicCoordinateAssembly HarmonicMainStatement HarmonicLawIngredients
open MarkedMassTransportProducer SpecificEnergyDensitySimilarity
open LabelBijectionProducer GridIndependenceCoupling GridIndependenceDifferenceBridge
open GatedResidualWeakMaximal
open DyadicGridTranslation UniformGridDilationInvariance

/-! ### `GradientTransported` is linear in the field -/

/-- **A difference of transported fields transports.**  `GradientTransported` is a condition on
increments, so it is stable under pointwise subtraction. -/
theorem gradientTransported_sub {s : ℝ} {e e' : Env} {rel : Vertex e.val ≃ Vertex e'.val}
    {Phi1 Phi2 : Vertex e.val → Plane} {Psi1 Psi2 : Vertex e'.val → Plane}
    (h1 : GradientTransported s rel Phi1 Psi1) (h2 : GradientTransported s rel Phi2 Psi2) :
    GradientTransported s rel (fun x => Phi1 x - Phi2 x) (fun x => Psi1 x - Psi2 x) := by
  intro v w
  show Psi1 (rel w) - Psi2 (rel w) - (Psi1 (rel v) - Psi2 (rel v))
    = s • (Phi1 w - Phi2 w - (Phi1 v - Phi2 v))
  rw [sub_sub_sub_comm, h1 v w, h2 v w, ← smul_sub]
  congr 1
  abel

/-! ### The marked potential transports along every joint similarity -/

/-- The marked potential is the stage field minus the gradient error, at any stage index. -/
theorem markedPotential_eq_stage_sub_error (ms : ℕ → ℕ) (m : ℕ) (q : MarkedEnvironment)
    (x : Vertex q.1.val) :
    markedPotential ms q x
      = MarkedStageFieldCovariance.stageField m q x
        - MarkedBallEnergyConvergence.gradientErrorLabel ms m q x.val := by
  show markedDifferenceField ms q (Nat.pair (baseLabel q.1) x.val)
    = gatedApproximant m q x.val
      - (gatedApproximant m q x.val
          - markedDifferenceField ms q (Nat.pair (baseLabel q.1) x.val))
  abel

section Potential

variable {s : ℝ} {u : Plane} {hs : 0 < s} {p : MarkedEnvironment}
  {rel : Vertex p.1.val ≃ Vertex (markedSimilarity s u hs p).1.val}

/-- **The marked potential transports along every joint similarity, at every marked
configuration.**  No gate: it is the difference of the two ungated transport statements for the
gated stage field and for the gradient error. -/
theorem gradientTransported_markedPotential (ms : ℕ → ℕ)
    (h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel) :
    GradientTransported s rel (markedPotential ms p)
      (markedPotential ms (markedSimilarity s u hs p)) := by
  have h1 : GradientTransported s rel (MarkedStageFieldCovariance.stageField 0 p)
      (MarkedStageFieldCovariance.stageField 0 (markedSimilarity s u hs p)) :=
    MarkedStageFieldCovariance.gradientTransported_stageField 0 h
  have h2 : GradientTransported s rel
      (fun w : Vertex p.1.val => MarkedBallEnergyConvergence.gradientErrorLabel ms 0 p w.val)
      (fun w : Vertex (markedSimilarity s u hs p).1.val =>
        MarkedBallEnergyConvergence.gradientErrorLabel ms 0 (markedSimilarity s u hs p) w.val) :=
    MarkedBallEnergyConvergence.gradientTransported_gradientErrorLabel ms
      MarkedStageFieldCovariance.covariantAtEveryStage 0 p h
  have hsub := gradientTransported_sub h1 h2
  intro v w
  rw [markedPotential_eq_stage_sub_error ms 0 (markedSimilarity s u hs p) (rel w),
    markedPotential_eq_stage_sub_error ms 0 (markedSimilarity s u hs p) (rel v),
    markedPotential_eq_stage_sub_error ms 0 p w, markedPotential_eq_stage_sub_error ms 0 p v]
  exact hsub v w

end Potential

/-! ### The joint similarity on the coupled space -/

/-- **The joint similarity of the coupled space**: the same physical similarity applied to the
environment and to **both** grid copies.  Both copies see the same environment, hence the same
relabelling, which is exactly what makes the difference field transport. -/
noncomputable def coupledSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (p : CoupledSpace) :
    CoupledSpace :=
  ((markedSimilarity s u hs (p.1, p.2.1)).1, (markedSimilarity s u hs (p.1, p.2.1)).2,
    (markedSimilarity s u hs (p.1, p.2.2)).2)

/-- **At unit scale the joint similarity is the coupled re-rooting**: the environment is
translated and both grid copies are translated. -/
theorem coupledSimilarity_one (z : Plane) (p : CoupledSpace) :
    coupledSimilarity 1 z one_pos p
      = (ActualMarkedBlockTransport.translateEnv z p.1, translate z p.2.1, translate z p.2.2) := by
  show (similarityTargetEnv 1 z one_pos p.1,
      dilate 1 one_pos (translate z p.2.1), dilate 1 one_pos (translate z p.2.2)) = _
  rw [dilate_one, dilate_one]
  rfl

/-! ### The identity -/

/-- **The copy-difference density is exactly similarity covariant, with no gate.**

`ρ_{Σ(s,u) p}(S(s,u) z) = ρ_p(z)` for every positive scale `s`, every centre `u`, every base
point `z` and **every** point `p` of the coupled space.  Both `hcov` and `hinv` of
`GatedResidualWeakMaximal.copyDifferenceWeakMaximal_of_twoGridSpace` are instances of it. -/
theorem copyDifferenceDensity_coupledSimilarity (ms : ℕ → ℕ) (s : ℝ) (u : Plane) (hs : 0 < s)
    (p : CoupledSpace) (z : Plane) :
    copyDifferenceDensity ms (coupledSimilarity s u hs p) (positiveSimilarity s u z)
      = copyDifferenceDensity ms p z := by
  have h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs (p.1, p.2.1)).1
      (similarityRelabel s u hs p.1) := isSimilarityRelabel_similarityRelabel s u hs p.1
  have h1 : GradientTransported s (similarityRelabel s u hs p.1)
      (markedPotential ms (p.1, p.2.1))
      (markedPotential ms (markedSimilarity s u hs (p.1, p.2.1))) :=
    gradientTransported_markedPotential (p := (p.1, p.2.1)) ms h
  have h2 : GradientTransported s (similarityRelabel s u hs p.1)
      (markedPotential ms (p.1, p.2.2))
      (markedPotential ms (markedSimilarity s u hs (p.1, p.2.2))) :=
    gradientTransported_markedPotential (p := (p.1, p.2.2)) ms h
  exact rootedSpecificEnergyDensity_similarity h (gradientTransported_sub h1 h2) z

/-- **`hcov`'s identity**: the case `s = 1`, `u = z`. -/
theorem copyDifferenceDensity_shift (ms : ℕ → ℕ) (p : CoupledSpace) (z : Plane) :
    copyDifferenceDensity ms (coupledSimilarity 1 z one_pos p) 0
      = copyDifferenceDensity ms p z := by
  have h := copyDifferenceDensity_coupledSimilarity ms 1 z one_pos p z
  rwa [show positiveSimilarity (1 : ℝ) z z = 0 by simp] at h

/-- **`hinv`'s identity**: the case `u = 0`, `z = 0`. -/
theorem copyDifferenceDensity_dilate (ms : ℕ → ℕ) (s : ℝ) (hs : 0 < s) (p : CoupledSpace) :
    copyDifferenceDensity ms (coupledSimilarity s 0 hs p) 0
      = copyDifferenceDensity ms p 0 := by
  have h := copyDifferenceDensity_coupledSimilarity ms s 0 hs p 0
  rwa [show positiveSimilarity s (0 : Plane) 0 = 0 by simp] at h

end ReflectedGMS.CopyDifferenceDensitySimilarity
