/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenLower3 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower2
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# GFF-K3, node H5: cutting off the Green potential of a smooth density

For a smooth nonnegative density `φ` with compact support in `{Im ≥ ε}`, the Green potential
`gpot φ x = ∫ greenH x y φ(y) dy` is smooth (`contDiff_gpot`, a difference of convolutions with
`log ‖·‖`), satisfies the weak equation `(2π)⁻¹ ∫ ⟪∇u, ∇ψ⟫ = ∫ ψ φ` on `zeroSpace H`
(`weak_gpot`), and the IMS identity `E(χu) = ∫ χ²u φ + (2π)⁻¹ ∫ u² ‖∇χ‖²` (`energy_mul_gpot`).
With the cutoffs `χn n` (`= 1` on `{‖z‖ ≤ n+1, Im z ≥ 2/(n+1)}`) and the decay bound
`0 ≤ u(z) ≤ C Im z / (1 + ‖z‖)²` away from the support, dominated convergence gives
`E(χn n * u) → B(σ, σ)` and `∫ χn n * u dσ → B(σ, σ)` (`exists_cutoff_approx`).
-/

noncomputable section

open MeasureTheory Filter Set Topology Real
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper.K3

/-- Hypotheses on a smooth density near `ℍ`. -/
structure GoodDens (φ : ℂ → ℝ) (ε : ℝ) : Prop where
  pos : 0 < ε
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
  compact : HasCompactSupport φ
  nonneg : ∀ z, 0 ≤ φ z
  im_ge : ∀ z, φ z ≠ 0 → ε ≤ z.im

/-- The measure `φ(z) dz`. -/
def densMeas (φ : ℂ → ℝ) : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (φ z)

/-- The Green potential of `φ(z) dz`. -/
def gpot (φ : ℂ → ℝ) (x : ℂ) : ℝ := ∫ y, greenH x y ∂densMeas φ

section Basic

variable {φ : ℂ → ℝ} {ε : ℝ}

lemma GoodDens.tsupport_subset (hφ : GoodDens φ ε) : tsupport φ ⊆ {z | ε ≤ z.im} :=
  closure_minimal (fun z hz => hφ.im_ge z hz)
    (isClosed_le continuous_const Complex.continuous_im)

lemma GoodDens.tsupport_subset_H (hφ : GoodDens φ ε) : tsupport φ ⊆ H := fun z hz =>
  show 0 < z.im from hφ.pos.trans_le (hφ.tsupport_subset hz)

lemma integral_densMeas (hφ : GoodDens φ ε) (g : ℂ → ℝ) :
    ∫ y, g y ∂densMeas φ = ∫ y, φ y * g y := by
  change ∫ y, g y ∂(volume.withDensity fun z => ((φ z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hφ.smooth.continuous.measurable.real_toNNReal]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ.nonneg _), smul_eq_mul]

theorem isAdmissibleH_densMeas (hφ : GoodDens φ ε) : IsAdmissibleH (densMeas φ) := by
  obtain ⟨C, hC⟩ := hφ.smooth.continuous.bounded_above_of_compact_support hφ.compact
  refine isAdmissibleH_withDensity (ENNReal.measurable_ofReal.comp hφ.smooth.continuous.measurable)
    (M := ENNReal.ofReal C) ENNReal.ofReal_lt_top
    (fun a => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa using hC a)))
    hφ.compact (fun z hz => show (0 : ℝ) ≤ z.im from (hφ.tsupport_subset_H hz).le)
    (fun a ha => by rw [image_eq_zero_of_notMem_tsupport ha, ENNReal.ofReal_zero])

/-- The logarithmic potential of `φ`. -/
def Vpot (φ : ℂ → ℝ) (w : ℂ) : ℝ := ∫ y, Real.log ‖y - w‖ * φ y

lemma gpot_eq (hφ : GoodDens φ ε) (x : ℂ) : gpot φ x = Vpot φ (conj x) - Vpot φ x := by
  unfold gpot Vpot
  rw [integral_densMeas hφ, ← integral_sub
    (integrable_log_norm_sub_mul_K3 hφ.smooth.continuous hφ.compact _)
    (integrable_log_norm_sub_mul_K3 hφ.smooth.continuous hφ.compact _)]
  congr 1; funext y
  simp only [greenH, norm_sub_conj_comm x y, norm_sub_rev x y]
  ring

lemma locallyIntegrable_log_norm : LocallyIntegrable (fun v : ℂ => Real.log ‖v‖) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall 0
  set R := max R0 1
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, by positivity, by linarith⟩
  have hint := integrable_log_norm_sub_mul_K3 (ψ := fun z => b z) b.continuous b.hasCompactSupport 0
  refine (hint.integrableOn (s := K)).congr_fun (fun z hz => ?_) hK.measurableSet
  have hz' : z ∈ Metric.closedBall (0 : ℂ) b.rIn :=
    Metric.closedBall_subset_closedBall (le_max_left R0 1) (hR0 hz)
  simp [b.one_of_mem_closedBall hz']

lemma Vpot_eq_conv (φ : ℂ → ℝ) (w : ℂ) :
    Vpot φ w = MeasureTheory.convolution φ (fun v : ℂ => Real.log ‖v‖)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume w := by
  rw [MeasureTheory.convolution_def]
  unfold Vpot
  congr 1; funext t
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_sub_rev t w]
  ring

lemma contDiff_Vpot (hφ : GoodDens φ ε) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Vpot φ) := by
  have h := hφ.compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤)
    hφ.smooth locallyIntegrable_log_norm
  have e : Vpot φ = MeasureTheory.convolution φ (fun v : ℂ => Real.log ‖v‖)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := funext (Vpot_eq_conv φ)
  rw [e]; exact h

theorem contDiff_gpot (hφ : GoodDens φ ε) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gpot φ) := by
  have e : gpot φ = fun x => Vpot φ (conj x) - Vpot φ x := funext (gpot_eq hφ)
  rw [e]
  exact ((contDiff_Vpot hφ).comp Complex.conjCLE.contDiff).sub (contDiff_Vpot hφ)

end Basic

end QuantumZipper.K3
