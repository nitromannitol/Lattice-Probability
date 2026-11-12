/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412pLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nLocal
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1C

/-!
# `𝓑^•_{t_k}` is a local set modulo constants, from the proved CONF Lemma 2.1 (task P2-WIRE21)

Primed copy of `p412n_isLocalSetDet0_s4T` (P412nLocal.lean): the Blueprint hypothesis
`CONFLem2_1` is replaced by `CONF.confLem2_1_filled_of` (CONF Lemma 2.1, C:476–479, for filled
balls at stopping times `τ > 0`, L2_1C.lean), which needs `DFGPSLem3_8`; `t_k > 0` from
`gm_s4T_eq`, `gm_tauD_pos` (as in Iterate2L419).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Local
variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **`𝓑^•_{t_k}` is a local set modulo additive constants** (`IsLocalSetDet0`), from CONF
Lemma 2.1 in its raw D32 form -/
theorem p412n_isLocalSetDet0_s4T' (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) :
    IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)) := by
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
    set h₁ := CONF.normIn h ψ₁ with hh₁
    have hh₁g : IsWholePlaneGFF h₁ P := CONF.isWholePlaneGFF_normIn hh ψ₁
    have hpos1 : ∀ ω, 0 < s4T D h₁ 𝕫 ℓ 𝕣 ε β k ω := fun ω => by
      rw [gm_s4T_eq]
      have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
      have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
      exact mul_pos (gm_tauD_pos _ 𝕫 hℓ𝕣) (by linarith)
    have hloc := CONF.confLem2_1_filled_of h38 hγ hγ2 hD hh₁g 𝕫 _
      (gm_S4_12_uncond D h₁ 𝕫 ℓ 𝕣 ε β hε k).2 (Eventually.of_forall hpos1)
      (TopologicalSpace.Opens.mk U hU)
    obtain ⟨F, hF, hEF⟩ := hloc
    have e1 : fieldSigma h₁ (TopologicalSpace.Opens.mk U hU) = fieldSigma0On h U := by
      rw [gm_fieldSigma_eq_fieldSigma0On hψ₁1 (CONF.normIn_apply_psi h hψ₁1)
        (V := TopologicalSpace.Opens.mk U hU) hψ₁U]
      exact CONF.fieldSigma0On_normIn h ψ₁ U
    rw [e1] at hF
    refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
    filter_upwards [p412n_s4T_ball_addConst hD hh (fun ω => -(h ω ψ₁)) 𝕫 ℓ 𝕣 ε β] with ω hω
    have e2 : filledBall (D (h₁ ω)) 𝕫 (s4T D h₁ 𝕫 ℓ 𝕣 ε β k ω) =
        filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) := hω k
    show (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ⊆ U) =
      (filledBall (D (h₁ ω)) 𝕫 (s4T D h₁ 𝕫 ℓ 𝕣 ε β k ω) ⊆ U)
    rw [e2]
  · have hU0 : U = ∅ := not_nonempty_iff_eq_empty.1 hne
    refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma0On h U), Eventually.of_forall fun ω => ?_⟩
    have hpos : 0 < s4T D h 𝕫 ℓ 𝕣 ε β k ω := by
      rw [gm_s4T_eq]
      have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
      have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
      exact mul_pos (gm_tauD_pos _ 𝕫 hℓ𝕣) (by linarith)
    have hz := jo_mem_filledBall_self (D := D (h ω)) (z := 𝕫) hpos
    show (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ⊆ U) = (ω ∈ (∅ : Set Ω))
    simp only [mem_empty_iff_false, eq_iff_iff, iff_false]
    intro hs
    rw [hU0] at hs
    exact hs hz

end Local

end LQGMetric.GM
