/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412b440 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bStep1E
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bRate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodP412
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412pLocal

/-!
# GM (4.40): `P[ℰ_𝕣, max_{k ≤ K} #𝒳_k > ε^{-ω}] = o^∞_ε(ε)` (L4.15 Step 1)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 1, l. 2123–2131,
display (4.40) (`eqn-stab-interval-count`). From CONF Theorem 3.9 (`CONFThm3_9At`) via
`p412b_hT_of_CONF`, the one-`k` bound `p412b_step1_E`, the union bound `p412b_step1_union` and
the rate `p412b_rate`, with `N = ⌊ε^{-ω}⌋`, `K = p4K` (GM (4.35′)) and `β` with `2β < ωβ_C`
("`β` chosen sufficiently small, in a manner depending only on `ω` and `D`").

Open input (D76): the bridge `confPts(s_k, t_k) ⊆ hitSetDD(s_k, t_k)` a.s. (hypothesis `hbr`).
The constants `βC, ε₁` depend only on the metric data and on `ℓ, ξ, χ', a, ω, β, M` (not on
`E`, `rr`, `U`, `V`, `𝕣`, `𝕫` or the probability space), as GMP4_12At (D75) needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the time `τ = s_k ∧ τ_{2ℓ𝕣}` at which `p412b_step1_k` applies CONF Theorem 3.9 has a filled
ball which is a local set modulo additive constants (the D130 hypothesis of `CONFThm3_9At`).
Copy-and-adapt of `p412n_isLocalSetDet0_s4T'` (P412pLocal; CONF Lemma 2.1, C:476–479, for the
field normalized near `U`, `CONF.normIn`), with `t_k` replaced by `s_k ∧ τ_{2ℓ𝕣}`. -/
theorem p412b_isLocalSetDet0_tauMin {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) :
    IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) 𝕫
      (min (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω))) := by
  have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
  have hpos : ∀ (h' : Ω → DistC) ω,
      0 < min (s4S D h' 𝕫 ℓ 𝕣 ε β k ω) (tauR D h' 𝕫 (2 * (ℓ * 𝕣)) ω) := fun h' ω =>
    lt_min (mul_pos (gm_tauD_pos _ 𝕫 hℓ𝕣) (by linarith)) (gm_tauD_pos _ 𝕫 (by linarith))
  intro U hU
  by_cases hne : U.Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
    set ψ₁ : TestC := bumpTest n x with hψ₁
    have hψ₁1 : ∫ y, ψ₁ y = 1 := GFFLaw.integral_bumpTest n x
    have hψ₁U : tsupport (ψ₁ : ℂ → ℝ) ⊆ U := by
      rw [hψ₁, tsupport_bumpTest]
      exact (Metric.closedBall_subset_ball hn).trans hrU
    set h₁ := CONF.normIn h ψ₁ with hh₁
    have hh₁g : IsWholePlaneGFF h₁ P := CONF.isWholePlaneGFF_normIn hh ψ₁
    have hloc := CONF.confLem2_1_filled_of h38 hγ hγ2 hD hh₁g 𝕫 _
      (p412b_min_isStop (gm_S4_12_uncond D h₁ 𝕫 ℓ 𝕣 ε β hε k).1 (gm_tauR_isStop D h₁ 𝕫 _))
      (Filter.Eventually.of_forall (hpos h₁)) (TopologicalSpace.Opens.mk U hU)
    obtain ⟨F, hF, hEF⟩ := hloc
    have e1 : fieldSigma h₁ (TopologicalSpace.Opens.mk U hU) = fieldSigma0On h U := by
      rw [gm_fieldSigma_eq_fieldSigma0On hψ₁1 (CONF.normIn_apply_psi h hψ₁1)
        (V := TopologicalSpace.Opens.mk U hU) hψ₁U]
      exact CONF.fieldSigma0On_normIn h ψ₁ U
    rw [e1] at hF
    refine ⟨F, hF, Filter.EventuallyEq.trans ?_ hEF⟩
    filter_upwards [hD.ae_dist_addConst (detGFFPlusCont hh)] with ω hω
    have hlm : 0 < Real.exp (xiGamma γ * -(h ω ψ₁)) := Real.exp_pos _
    have hd := fun u v => hω (-(h ω ψ₁)) u v
    have e2 : filledBall (D (h₁ ω)) 𝕫
        (min (s4S D h₁ 𝕫 ℓ 𝕣 ε β k ω) (tauR D h₁ 𝕫 (2 * (ℓ * 𝕣)) ω)) =
        filledBall (D (h ω)) 𝕫
        (min (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω)) := by
      change filledBall (D (addConst (h ω) (-(h ω ψ₁)))) 𝕫
        (min (tauD (D (addConst (h ω) (-(h ω ψ₁)))) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
          (tauD (D (addConst (h ω) (-(h ω ψ₁)))) 𝕫 (2 * (ℓ * 𝕣)))) =
        filledBall (D (h ω)) 𝕫 (min (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
          (tauD (D (h ω)) 𝕫 (2 * (ℓ * 𝕣))))
      rw [p412n_tauD_smul hlm hd, p412n_tauD_smul hlm hd, mul_assoc,
        ← mul_min_of_nonneg _ _ hlm.le, p412n_filledBall_smul hlm hd]
    show (filledBall (D (h ω)) 𝕫
        (min (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω)) ⊆ U) =
      (filledBall (D (h₁ ω)) 𝕫
        (min (s4S D h₁ 𝕫 ℓ 𝕣 ε β k ω) (tauR D h₁ 𝕫 (2 * (ℓ * 𝕣)) ω)) ⊆ U)
    rw [e2]
  · have hU0 : U = ∅ := not_nonempty_iff_eq_empty.1 hne
    refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma0On h U), Filter.Eventually.of_forall
      fun ω => ?_⟩
    have hz := jo_mem_filledBall_self (D := D (h ω)) (z := 𝕫) (hpos h ω)
    show (filledBall (D (h ω)) 𝕫
        (min (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω)) ⊆ U) = (ω ∈ (∅ : Set Ω))
    simp only [mem_empty_iff_false, eq_iff_iff, iff_false]
    intro hs
    rw [hU0] at hs
    exact hs hz

/-- **GM (4.40)** (l. 2128–2131). -/
theorem p412b_eq440 (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {cp : CONFParams} {χ : ℝ}
    (H39 : CONFThm3_9At γ D c cp χ) :
    ∃ βC : ℝ, 0 < βC ∧ ∀ ω₀ β : ℝ, 0 < ω₀ → 0 < β → 2 * β < ω₀ * βC →
    ∀ ℓ ξ χ' : ℝ, ∀ a ∈ Ioo (0 : ℝ) 1, a ≤ ℓ → ∀ M : ℝ, ∃ ε₁ : ℝ, 0 < ε₁ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    ∀ R : RegPar, R.ξ = xiGamma γ → R.c = c → R.p = cp → R.χ = χ → R.ℓ = ℓ → R.ξ = ξ →
      R.χ' = χ' → 0 ≤ R.ξ → 0 ≤ R.χ → R.U ⊆ R.V →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ H : ℝ → ℂ → Ω → ℝ, ∀ 𝕣 : ℝ, 0 < 𝕣 → 0 < R.c 𝕣 →
      0 ≤ R.c (R.ℓ * 𝕣) → ∀ 𝕫 ∈ rScale 𝕣 R.U,
      (∀ᵐ ω ∂P, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0) →
      (∀ᵐ ω ∂P, H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫) →
      (∀ᵐ ω ∂P, H (R.ℓ * 𝕣) 𝕫 ω = circleAvg (h ω) (R.ℓ * 𝕣) 𝕫) →
      (∀ᵐ ω ∂P, (D (h ω)).IsLength ∧ ∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
      (∀ k ≤ p4K R a ε β, ∀ᵐ ω ∂P,
        confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆
        hitSetDD (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
      P (regEvent D P h H R 𝕣 a ∩ {ω | ∃ k ≤ p4K R a ε β, ((⌊ε ^ (-ω₀)⌋₊ : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard}) ≤
        ENNReal.ofReal (ε ^ M) := by
  obtain ⟨b₁, βC, hb₁, hβC, H39'⟩ := H39
  refine ⟨βC, hβC, fun ω₀ β hω₀ hβ hβω ℓ ξ χ' a ha haℓ M => ?_⟩
  obtain ⟨b₀, hb₀, hT⟩ := H39' a ha
  have ha0 : 0 < a := ha.1
  have hℓ : 0 < ℓ := lt_of_lt_of_le ha0 haℓ
  set c₂ := (ℓ / a + 1) * Real.exp (ξ / a) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  have hC'0 : 0 ≤ p412bC ℓ a χ' := by
    unfold p412bC; have := ha.1; positivity
  obtain ⟨ε₁, hε₁, hrate⟩ := p412b_rate (A := a / c₂) (C' := p412bC ℓ a χ') (M := M) hb₀ hb₁
    hβC hω₀ hβ hβω (by have := ha.1; positivity) hC'0
  refine ⟨ε₁, hε₁, fun ε hε R hRξ hRc hRp hRχ hRℓ hRξ' hRχ' hξ hχ hUV Ω _ P _ h hGFF H 𝕣 h𝕣 hc hcℓ
    𝕫 h𝕫 hH0 hH𝕫 hHℓ hLen hbr => ?_⟩
  obtain ⟨hN1, hNε, hfin⟩ := hrate ε hε
  have hε0 : 0 < ε := hε.1
  have hc2R : regC2const R a = c₂ := by rw [regC2const, hRℓ, hRξ']
  have hTR : ∀ (z₀ : ℂ) (Rr : ℝ), 0 < Rr → ∀ N : ℕ, 1 ≤ N →
      ∀ τ : Ω → ℝ, IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ Rr ω) (tauR D h z₀ (2 * Rr) ω)) →
      P {ω | ω ∈ confReg R.ξ R.c D P h R.p R.χ z₀ Rr a ∧
          ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
            (τ ω + (N : ℝ) ^ (-βC) * scaleFac R.ξ R.c (h ω) Rr z₀)).encard} ≤
        ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)) := by
    rw [hRξ, hRc, hRp, hRχ]; exact hT P h hGFF
  set K := p4K R a ε β
  have hKle : (K : ℝ) ≤ a / c₂ * ε ^ (-β) := by
    have h1 : K ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ := Nat.sub_le _ _
    refine (Nat.cast_le.2 h1).trans ?_
    rw [hc2R]; exact Nat.floor_le (by positivity)
  have hK : (K : ℝ) * ε ^ β ≤ a / regC2const R a := by
    rw [hc2R]
    have hεβ : ε ^ (-β) * ε ^ β = 1 := by rw [← Real.rpow_add hε0]; simp
    calc (K : ℝ) * ε ^ β ≤ a / c₂ * ε ^ (-β) * ε ^ β :=
          mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hε0.le _)
      _ = a / c₂ := by rw [mul_assoc, hεβ, mul_one]
  have hNε' : (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ (-βC) * p412bC R.ℓ a R.χ' ≤ ε ^ (2 * β) := by
    rw [hRℓ, hRχ']; exact hNε
  refine (p412b_step1_union P h H R hTR h𝕣 ha.1 ha.2 (hRℓ ▸ haℓ) hχ hUV hc hcℓ
    hξ h𝕫 hH0 hH𝕫 hHℓ hLen hε0 K hK _ hN1 hNε' hbr
    (fun k => p412b_isLocalSetDet0_tauMin h38 hγ hγ2 hD hGFF 𝕫
      (by rw [hRℓ]; exact mul_pos hℓ h𝕣) hε0 k)).trans ?_
  have hx0 : 0 ≤ b₀ * Real.exp (-b₁ * (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ βC) := by positivity
  calc ((K : ENNReal) + 1) * ENNReal.ofReal (b₀ * Real.exp (-b₁ * (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ βC))
      = ENNReal.ofReal ((K : ℝ) + 1) *
          ENNReal.ofReal (b₀ * Real.exp (-b₁ * (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ βC)) := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]
    _ = ENNReal.ofReal (((K : ℝ) + 1) * (b₀ * Real.exp (-b₁ * (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ βC))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ((a / c₂ * ε ^ (-β) + 1) *
          (b₀ * Real.exp (-b₁ * (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ βC))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hx0)
    _ ≤ ENNReal.ofReal (ε ^ M) := ENNReal.ofReal_le_ofReal hfin

end LQGMetric.GM
