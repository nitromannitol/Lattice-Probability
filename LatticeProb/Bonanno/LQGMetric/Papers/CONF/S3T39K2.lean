/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J10
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K0
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3Norm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Jordan
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.1 modulo additive constants for a.s. stopping times (D130 §4 L2, packet J6b)

CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, Lemma 2.1 (C:476–479), used at
C:1431–1432 with `h` viewed modulo additive constants (C:1154).

**The D130 form of L2 is false.** `IsFilledBallStoppingTimeAE0 P D h z₀ τ` puts the *raw* ball
sets `𝓑^•_s` into `localSigma0` (through `setSigma`), so every deterministic `τ ≡ s` satisfies it
(`t39k2_ae0_const`). For `h = h₀ + Z` with `Z` an independent nondegenerate constant (an
`IsWholePlaneGFF`, D108/D112 (a)), Weyl scaling gives `𝓑^•_1(D_h) = 𝓑^•_{e^{-ξZ}}(D_{h₀})`, so for
`U = B_R(z₀)` the conditional probability of `{𝓑^•_1(D_h) ⊆ U}` given `h₀` lies a.s. in `(0,1)`,
while `σ(h|_U mod const) ⊆ σ(h₀)`: `IsLocalSetDet0 P h 𝓑^•_1` fails. The step of the raw proof
that has no mod-constant analogue is the deterministic-radius step `conf21_aeEventIn_det`
(`{𝓑^•_s ⊆ U}` is a function of `D_h(·,·;U)`, which sees the constant).

**Corrected form proved here** (`t39k2_isLocalSetDet0_of_cov`): CONF L2.1 modulo constants for a
time `τ` that is *covariant*: for every `ψ` with `∫ ψ = 1` the ball `𝓑^•_τ(D_h)` is a.s. the ball
at an a.s. raw stopping time `τ' > 0` of the normalized field `h − h(ψ)` (`CONF.normIn`). This is
how CONF's own times (`τ_𝕣`, `σ^ε_{τ,𝕣}`, …) are local modulo constants. Proof: copy of
`GM.p412n_isLocalSetDet0_s4T'` (P412pLocal, P2-WIRE21) with `CONF.confLem2_1_filled_ofAE`
(S3T39J10) in place of `confLem2_1_filled_of` and the covariance hypothesis in place of
`p412n_s4T_ball_addConst`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF
open GM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

variable [IsProbabilityMeasure P]

/-- **CONF Lemma 2.1 modulo additive constants, covariant a.s. stopping times** (C:476–479 with
C:1154; corrected form of D130 §4 L2) -/
theorem t39k2_isLocalSetDet0_of_cov (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) (τ : Ω → ℝ)
    (hcov : ∀ ψ : TestC, ∫ y, ψ y = 1 → ∃ τ' : Ω → ℝ,
      IsFilledBallStoppingTimeAE P D (normIn h ψ) z₀ τ' ∧ (∀ᵐ ω ∂P, 0 < τ' ω) ∧
      ∀ᵐ ω ∂P, filledBall (D (normIn h ψ ω)) z₀ (τ' ω) = filledBall (D (h ω)) z₀ (τ ω))
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) := by
  intro U hU
  by_cases hne : U.Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
    set ψ₁ : TestC := bumpTest n x with hψ₁
    have hψ₁1 : ∫ y, ψ₁ y = 1 := GFFLaw.integral_bumpTest n x
    have hψ₁U : tsupport (ψ₁ : ℂ → ℝ) ⊆ U := by
      rw [hψ₁, tsupport_bumpTest]
      exact (closedBall_subset_ball hn).trans hrU
    obtain ⟨τ', hτ', hpos', hball⟩ := hcov ψ₁ hψ₁1
    have hloc := confLem2_1_filled_ofAE h38 hγ hγ2 hD (isWholePlaneGFF_normIn hh ψ₁) z₀ τ'
      hτ' hpos' (TopologicalSpace.Opens.mk U hU)
    obtain ⟨F, hF, hEF⟩ := hloc
    have e1 : fieldSigma (normIn h ψ₁) (TopologicalSpace.Opens.mk U hU) = fieldSigma0On h U := by
      rw [gm_fieldSigma_eq_fieldSigma0On hψ₁1 (normIn_apply_psi h hψ₁1)
        (V := TopologicalSpace.Opens.mk U hU) hψ₁U]
      exact fieldSigma0On_normIn h ψ₁ U
    rw [e1] at hF
    refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
    filter_upwards [hball] with ω hω
    show (filledBall (D (h ω)) z₀ (τ ω) ⊆ U) =
      (filledBall (D (normIn h ψ₁ ω)) z₀ (τ' ω) ⊆ U)
    rw [hω]
  · have hU0 : U = ∅ := not_nonempty_iff_eq_empty.1 hne
    refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma0On h U), ?_⟩
    filter_upwards [hpos] with ω hτω
    have hz := jo_mem_filledBall_self (D := D (h ω)) (z := z₀) hτω
    show (filledBall (D (h ω)) z₀ (τ ω) ⊆ U) = (ω ∈ (∅ : Set Ω))
    simp only [mem_empty_iff_false, eq_iff_iff, iff_false]
    intro hs
    rw [hU0] at hs
    exact hs hz

end LQGMetric.CONF
