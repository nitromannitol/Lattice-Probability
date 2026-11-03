/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.KernelForm4 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm3

/-!
# GFF-K3 §3, node C2: `dualCov_conformal_withDensity`

Blueprint `blueprint/GFF_K3_BLUEPRINT.md` §3 node **C2**: for a conformal map `φ : D → ℍ` with
`D ⊆ ℍ` and bounded measurable densities `g₁, g₂` with bounded support (they may touch `∂D`),

`dualCov D (zeroSpace D) (g₁ dz) (g₂ dz) = ∫_D ∫_D g₁(x) g₂(y) G_ℍ(φ x, φ y) dy dx`.

Polarization of `dualNormSq_conformal_withDensity` (`KernelForm3.lean`): the `ℝ≥0∞` kernel
integrals are bilinear, symmetric (`greenH_symm`) and finite, and the diagonal `y = x` is
Lebesgue-null, off which `G_ℍ(φ x, φ y) ≥ 0` (`greenH_nonneg`, `φ` injective).  Source:
Sheffield, *Gaussian free fields for mathematicians* (2007), §2.2 and §3.
-/

noncomputable section

open MeasureTheory Set Function Filter Topology
open Classical
open scoped ENNReal

namespace QuantumZipper.K3

variable {φ : ℂ → ℂ} {D : Set ℂ}

/-- The `ℝ≥0∞` integrand `1_D u(x) · 1_D v(y) · G_ℍ(φ x, φ y)`. -/
def kerDens (φ : ℂ → ℂ) (D : Set ℂ) (u v : ℂ → ℝ≥0∞) (p : ℂ × ℂ) : ℝ≥0∞ :=
  D.indicator u p.1 * (D.indicator v p.2 * confKer φ D p)

lemma measurable_kerDens (hφ : IsConformalOnto φ D H) {u v : ℂ → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) : Measurable (kerDens φ D u v) := by
  have hDm : MeasurableSet D := hφ.isOpen.measurableSet
  have h1 := hu.indicator hDm
  have h2 := hv.indicator hDm
  have hK := measurable_confKer hφ
  unfold kerDens
  fun_prop

/-- Bounded densities with bounded support: the hypotheses used below. -/
structure BddDens (u : ℂ → ℝ≥0∞) (M : ℝ≥0∞) (R : ℝ) : Prop where
  meas : Measurable u
  lt_top : M < ⊤
  le : ∀ z, u z ≤ M
  zero : ∀ z, z ∉ Metric.closedBall 0 R → u z = 0

lemma BddDens.add {u v : ℂ → ℝ≥0∞} {M N : ℝ≥0∞} {R S : ℝ} (hu : BddDens u M R)
    (hv : BddDens v N S) : BddDens (u + v) (M + N) (max R S) where
  meas := hu.meas.add hv.meas
  lt_top := ENNReal.add_lt_top.2 ⟨hu.lt_top, hv.lt_top⟩
  le z := add_le_add (hu.le z) (hv.le z)
  zero z hz := by
    have h1 : z ∉ Metric.closedBall 0 R := fun h => hz
      (Metric.closedBall_subset_closedBall (le_max_left R S) h)
    have h2 : z ∉ Metric.closedBall 0 S := fun h => hz
      (Metric.closedBall_subset_closedBall (le_max_right R S) h)
    simp [hu.zero z h1, hv.zero z h2]

/-- The kernel integral `∬ 1_D u(x) 1_D v(y) G_ℍ(φ x, φ y)` in `ℝ≥0∞`. -/
def kerInt (φ : ℂ → ℂ) (D : Set ℂ) (u v : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, kerDens φ D u v p ∂((volume : Measure ℂ).prod volume)

lemma dualNormSq_eq_kerInt (hφ : IsConformalOnto φ D H) (hDH : D ⊆ H) {u : ℂ → ℝ≥0∞}
    {M : ℝ≥0∞} {R : ℝ} (hu : BddDens u M R) :
    dualNormSq D (zeroSpace D) (volume.withDensity u) = kerInt φ D u u :=
  dualNormSq_conformal_withDensity hφ hDH hu.meas hu.lt_top hu.le hu.zero

lemma dualNormSq_withDensity_lt_top (hφ : IsConformalOnto φ D H) (hDH : D ⊆ H)
    {u : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ} (hu : BddDens u M R) :
    dualNormSq D (zeroSpace D) (volume.withDensity u) < ⊤ := by
  have hDm : MeasurableSet D := hφ.isOpen.measurableSet
  have := isFiniteMeasure_withDensity_bdd hu.lt_top hu.le hu.zero
  rw [dualNormSq_zeroSpace_restrict hφ.isOpen, restrict_withDensity hDm,
    ← withDensity_indicator hDm]
  refine (isAdmissibleDual_withDensity hφ hDH (hu.meas.indicator hDm) hu.lt_top
    (fun z => (indicator_le_self _ _ z).trans (hu.le z)) (R := R) ?_).2.2.2
  intro z hz
  by_cases hzD : z ∈ D
  · rw [indicator_of_mem hzD]; exact hu.zero z fun h => hz ⟨hzD, h⟩
  · exact indicator_of_notMem hzD _

end QuantumZipper.K3
