/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.Field at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import Mathlib.Analysis.Complex.Isometry
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower1

/-!
* `Field := LQGMetric.DistC` (Decision F1), `FieldOn U := LQGMetric.DistOn U`.
* `testPullCLE L : TestC →L[ℝ] TestC`, `φ ↦ φ ∘ L` for a continuous real-linear automorphism `L`
  of `ℂ`. **Adapted** from LQGMetric's affine pullback `LQGMetric.testAffinePull` / `pullK`
  (`LQGMetric/Statement/Field.lean`): same proof with the affine map replaced by `L`.
* `conjField h = h ∘ conj`, `rotateField θ h = h(e^{iθ} ·)` (both linear isometries, so the Jacobian
  is `1`: `⟨h ∘ L, φ⟩ = ⟨h, φ ∘ L⁻¹⟩`), `evenPart h = (h + h ∘ conj)/2`, `IsEvenField h`.
* `toFS : Field → QuantumZipper.FieldSample` (Decisions F2, D5): pairing with a measure `μ` as the
  limit of the pairings `⟨h, η_{ε_k(μ)} ∗ μ⟩` of `h` with the mollified measures
  `Bridge.molTest ε μ` (QuantumZipper's radial bump `K3.ηε`) along the deterministic
  `μ`-dependent scales `ε_k(μ) = Bridge.epsSeq μ k` (`Foundations/BridgeSeq.lean`: error variance
  `≤ 4^{-k}`, so that a.s. convergence is Borel–Cantelli); junk `0` if there is no limit, and
  junk `0` at measures that are not s-finite. `measurable_toFS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions

namespace MatedCRTHarmonic.MoTPort

/-- the field type: real distributions on `ℂ` (LQGMetric's `DistC`) -/
abbrev Field := LQGMetric.DistC

/-- distributions on an open set `U` -/
abbrev FieldOn (U : Opens ℂ) := LQGMetric.DistOn U

namespace FieldOps

open LQGMetric

section pullCLE

variable (L : ℂ ≃L[ℝ] ℂ)

lemma iteratedFDeriv_comp_cle {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (i : ℕ) (x : ℂ) :
    iteratedFDeriv ℝ i (φ ∘ L) x =
      (iteratedFDeriv ℝ i φ (L x)).compContinuousLinearMap fun _ => (L : ℂ →L[ℝ] ℂ) :=
  (L : ℂ →L[ℝ] ℂ).iteratedFDeriv_comp_right hφ x (by exact_mod_cast le_top)

/-- the compact `L⁻¹ K` -/
def cleK (K : Compacts ℂ) : Compacts ℂ := K.map L.symm L.symm.continuous

lemma mem_cleK_of {K : Compacts ℂ} {x : ℂ} (hx : L x ∈ (K : Set ℂ)) :
    x ∈ (cleK L K : Set ℂ) :=
  ⟨L x, hx, L.symm_apply_apply x⟩

/-- `φ ↦ φ ∘ L` from `𝓓_K` to `𝓓_{L⁻¹K}` -/
def pullCLEK (K : Compacts ℂ) : 𝓓^{⊤}_{K}(ℂ, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{cleK L K}(ℂ, ℝ) where
  toFun φ :=
    { toFun := φ ∘ L
      contDiff' := φ.contDiff.comp (L : ℂ →L[ℝ] ℂ).contDiff
      zero_on_compl' := fun _ hx => φ.zero_on_compl (fun hK => hx (mem_cleK_of L hK)) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma continuous_pullCLEK (K : Compacts ℂ) : Continuous (pullCLEK L K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  let Ψ := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
      (E := fun _ : Fin i => ℂ) (E₁ := fun _ : Fin i => ℂ) (F := ℝ)
      (fun _ => (L : ℂ →L[ℝ] ℂ))).compLeftContinuousBounded ℂ
  have key : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ pullCLEK L K) =
      (fun g => (Ψ g).compContinuous ⟨L, L.continuous⟩) ∘
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext φ
    ext x : 1
    simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rw [BoundedContinuousFunction.compContinuous_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_comp_cle L φ.contDiff i x
  rw [key]
  exact ((BoundedContinuousFunction.continuous_compContinuous _).comp Ψ.continuous).comp
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous

lemma hasCompactSupport_comp_cle {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (φ ∘ L) := by
  refine HasCompactSupport.intro (K := L.symm '' tsupport φ)
    (hφ.isCompact.image L.symm.continuous) fun x hx => ?_
  have : L x ∉ tsupport φ := fun h => hx ⟨L x, h, L.symm_apply_apply x⟩
  exact image_eq_zero_of_notMem_tsupport (f := φ) this

/-- `φ ↦ φ ∘ L` on `𝓓(ℂ)` -/
def testPullCLE : TestC →L[ℝ] TestC :=
  TestFunction.mkCLM ℝ
    (fun φ => ⟨φ ∘ L, φ.contDiff.comp (L : ℂ →L[ℝ] ℂ).contDiff,
      hasCompactSupport_comp_cle L φ.hasCompactSupport, subset_univ _⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K _ => by
      have : (fun φ : TestC => (⟨φ ∘ L, φ.contDiff.comp (L : ℂ →L[ℝ] ℂ).contDiff,
          hasCompactSupport_comp_cle L φ.hasCompactSupport, subset_univ _⟩ : TestC)) ∘
          TestFunction.ofSupportedIn (subset_univ (K : Set ℂ)) =
          TestFunction.ofSupportedInCLM ℝ (subset_univ (cleK L K : Set ℂ)) ∘ pullCLEK L K := by
        funext φ; ext x; rfl
      rw [this]
      exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp (continuous_pullCLEK L K))

@[simp] lemma testPullCLE_apply (φ : TestC) (x : ℂ) : testPullCLE L φ x = φ (L x) := rfl

end pullCLE

end FieldOps

open FieldOps

/-! ## The bridge to QuantumZipper's `FieldSample` -/

end MatedCRTHarmonic.MoTPort
