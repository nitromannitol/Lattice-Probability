/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412pMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412pLocal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nMain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412kBridge
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412U4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S2

/-!
# GM Proposition 4.12 (`P412OfL36AE0`) without the hypothesis `CONFLem2_1` (task P2-WIRE21)

Primed copies of `p412n_step_k` (P412nStep.lean), `p412n_P4_12AtC` (P412nMain.lean) and
`p412n_P412OfL36AE0` (P412nOpen.lean), unchanged except that CONF Lemma 2.1 enters through the
proved `p412n_isLocalSetDet0_s4T'` (P412pLocal.lean, from `CONF.confLem2_1_filled_of` and
`DFGPSLem3_8`) instead of the Blueprint hypothesis `CONFLem2_1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LQGMetric.Blueprint

namespace LQGMetric.GM

section Step
variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}

/-- **GM L4.15 Step 3–4 at one `k`** for a field normalized at `ψ₀`, on `E_η` (D110) -/
theorem p412n_step_k' (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) {p : CONFParams} (H36 : CONF.CONFLem3_6AtAENE γ D c₀ p)
    (hEDet : P412iEDetAll γ D c₀ p) :
    ∃ α C₀ : ℝ, 0 < α ∧ 1 < C₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (g : Ω → DistC), IsWholePlaneGFF g P → ∀ ψ₀ : TestC, (∫ x, ψ₀ x = 1) →
      (∀ ω, g ω ψ₀ = 0) →
    ∀ (𝕫 : ℂ) {ℓ 𝕣 ε β δ κ : ℝ}, 0 < ℓ * 𝕣 → 0 < 𝕣 → 0 < ε → ε ≤ 1 → 0 ≤ β →
      δ ∈ Ioo (0 : ℝ) 1 → C₀ * δ ^ α < 1 →
    ∀ (k L : ℕ) (Eη : Set Ω), MeasurableSet[p412iFilt P D g 𝕫 ℓ 𝕣 ε β 0] Eη →
      (∀ ω ∈ Eη, tsupport (ψ₀ : ℂ → ℝ) ⊆
        interior (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω))) →
    ∃ (x : ℕ → Ω → ℂ) (G : ℕ → Set Ω),
      (∀ᵐ ω ∂P, ∀ j, x j ω ∈ frontier (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω))) ∧
      (∀ᵐ ω ∂P, ω ∈ Eη → (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 ℓ 𝕣 ε β k ω)
          (s4T D g 𝕫 ℓ 𝕣 ε β k ω)).encard ≤ L →
        ∀ e ∈ p412fEndSet (D (g ω)) 𝕫 (s4S D g 𝕫 ℓ 𝕣 ε β k ω) (s4T D g 𝕫 ℓ 𝕣 ε β k ω),
          ∃ j < 2 * L, ∃ z : ℂ,
            p412eGoodZ (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) e z (ε ^ κ * 𝕣) ∧
            dist z (x j ω) ≤ ε ^ κ * 𝕣) ∧
      (∀ j, ∀ ω ∈ G j, x j ω ∈ frontier (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) →
        confRK (xiGamma γ) c₀ D P g p 𝕣 δ
          (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) ω ≤
          Metric.ediam (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) →
        ∀ (y : ℂ) (Q : ℝ → ℂ) (Lq : ℝ),
          y ∉ enbhd (confRK (xiGamma γ) c₀ D P g p 𝕣 δ
            (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) ω)
            (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) →
          IsGeodesicL (D (g ω)) Q Lq 𝕫 y → ∀ u ∈ Icc 0 Lq,
            Q u ∉ Metric.ball (x j ω) (δ * 𝕣) \
              filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 ℓ 𝕣 ε β k ω)) ∧
      MeasurableSet[p412iFilt P D g 𝕫 ℓ 𝕣 ε β (k + 1)]
        ((⋂ j ∈ Finset.range (2 * L), G j) ∪
          {ω | ENNReal.ofReal (s4S D g 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
            confSigma (xiGamma γ) c₀ D P g p 𝕫 𝕣 δ (s4T D g 𝕫 ℓ 𝕣 ε β k ω) ω} ∪
          {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 ℓ 𝕣 ε β k ω)
            (s4T D g 𝕫 ℓ 𝕣 ε β k ω)).encard} ∪ Eηᶜ) ∧
      ∀ᵐ ω ∂P, 1 - (2 * L : ℕ) * (C₀ * δ ^ α) ≤
        P[((⋂ j ∈ Finset.range (2 * L), G j) ∪
          {ω | ENNReal.ofReal (s4S D g 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
            confSigma (xiGamma γ) c₀ D P g p 𝕫 𝕣 δ (s4T D g 𝕫 ℓ 𝕣 ε β k ω) ω} ∪
          {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 ℓ 𝕣 ε β k ω)
            (s4T D g 𝕫 ℓ 𝕣 ε β k ω)).encard} ∪ Eηᶜ).indicator (fun _ => (1 : ℝ)) |
          p412iFilt P D g 𝕫 ℓ 𝕣 ε β k] ω := by
  classical
  obtain ⟨α, C₀, hα, hC₀, HU⟩ := p412n_union_k H36
  refine ⟨α, C₀, hα, hC₀, ?_⟩
  intro Ω _ P _ _ g hg ψ₀ hψ₀ hg0 𝕫 ℓ 𝕣 ε β δ κ hℓ𝕣 h𝕣 hε hε1 hβ hδ hδc k L Eη hEη hEk
  set T := s4T D g 𝕫 ℓ 𝕣 ε β k with hTdef
  set K : Ω → Set ℂ := fun ω => filledBall (D (g ω)) 𝕫 (T ω) with hKdef
  have hKc : ∀ ω, IsClosed (K ω) := fun ω => gm_filledBall_isClosed _ _ _
  have hTpos : ∀ ω, 0 < T ω := fun ω => by
    rw [hTdef, gm_s4T_eq]
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
    exact mul_pos (gm_tauD_pos _ 𝕫 hℓ𝕣) (by linarith)
  have hz : ∀ ω, 𝕫 ∈ K ω := fun ω => jo_mem_filledBall_self (hTpos ω)
  -- centres
  obtain ⟨x₀, hx₀m, hx₀f, hx₀c⟩ := p412m_centres (κ := κ) h38 hC24 hC27 hC14 hγ hγ2 hD hg 𝕫
    hℓ𝕣 h𝕣 hε hβ k L
  obtain ⟨fb, hfbm, hfb⟩ := p412m_select_near K hKc 𝕫 hz 𝕫 0
  set E := {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (K ω)} with hEdef
  set x : ℕ → Ω → ℂ := fun j ω => if tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (K ω) then x₀ j ω
    else fb ω with hxdef
  have hxm : ∀ j, @Measurable Ω ℂ (localSigma0 g K) _ (x j) := fun j =>
    p412n_measurable_trace g hψ₀ hg0 hKc (hx₀m j) hfbm
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P g hg
  have hxf : ∀ᵐ ω ∂P, ∀ j, x j ω ∈ frontier (K ω) := by
    filter_upwards [hx₀f, hlen] with ω h1 hl j
    simp only [hxdef]
    split_ifs
    · exact h1 j
    · exact (hfb ω (gm_filledBall_isBounded_of_lenSet hl 𝕫 _)).1
  -- the CONF L3.6 events
  have hdet := p412n_isLocalSetDet0_s4T' (β := β) h38 hγ hγ2 hD hg 𝕫 hℓ𝕣 hε k
  have hm : localSigma g K ≤ ‹MeasurableSpace Ω› := p412i_sigA_le h38 hγ hγ2 hD hg 𝕫 ℓ 𝕣 ε β k
  obtain ⟨G, hGm, hGA, hGc⟩ := HU P g hg 𝕫 𝕣 h𝕣 T (gm_S4_12_uncond D g 𝕫 ℓ 𝕣 ε β hε k).2 ψ₀
    hψ₀ hg0 hdet hm δ hδ hδc (2 * L) x hxm hxf
  refine ⟨x, G, hxf, ?_, hGA, ?_⟩
  · filter_upwards [hx₀c] with ω hω hωE hC e he
    have hωE' : tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (K ω) := hEk ω hωE
    obtain ⟨j, hj, z, hz1, hz2⟩ := hω hC e he
    refine ⟨j, hj, z, hz1, ?_⟩
    simp only [hxdef, if_pos hωE']
    exact hz2
  have hδ𝕣 : 0 < δ * 𝕣 := mul_pos hδ.1 h𝕣
  have hAk := p412i_Ak_mem_ae h38 hγ hγ2 hD hg (xiGamma γ) c₀ p (hEDet P g hg) 𝕫 hℓ𝕣 hε hε1 hβ
    hδ𝕣 k (2 * L) L G hGm
  have hEη' : MeasurableSet[p412iFilt P D g 𝕫 ℓ 𝕣 ε β (k + 1)] Eηᶜ :=
    ((p412iFilt P D g 𝕫 ℓ 𝕣 ε β).mono (Nat.zero_le _) _ hEη).compl
  refine ⟨hAk.union hEη', ?_⟩
  set A := (⋂ j ∈ Finset.range (2 * L), G j) ∪
          {ω | ENNReal.ofReal (s4S D g 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
            confSigma (xiGamma γ) c₀ D P g p 𝕫 𝕣 δ (s4T D g 𝕫 ℓ 𝕣 ε β k ω) ω} ∪
          {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 ℓ 𝕣 ε β k ω)
            (s4T D g 𝕫 ℓ 𝕣 ε β k ω)).encard} ∪ Eηᶜ with hAdef
  by_cases hN : ((2 * L : ℕ) : ℝ) * (C₀ * δ ^ α) < 1
  · have hIm : MeasurableSet ((⋂ j ∈ Finset.range (2 * L), G j) ∪ Eᶜ) :=
      (p412f_nullMeas_of_condExp hN hGc).measurable_of_complete
    have hsub : (⋂ j ∈ Finset.range (2 * L), G j) ∪ Eᶜ ⊆ A := by
      rintro ω (hω | hω)
      · exact Or.inl (Or.inl (Or.inl hω))
      · refine Or.inr fun hωη => hω ?_
        exact hEk ω hωη
    exact p412i_hq h38 hγ hγ2 hD hg 𝕫 hℓ𝕣 hε k hIm
      ((p412iFilt P D g 𝕫 ℓ 𝕣 ε β).le (k + 1) _ (hAk.union hEη')) hsub hGc
  · have hnn := condExp_nonneg (μ := P) (m := (p412iFilt P D g 𝕫 ℓ 𝕣 ε β) k)
      (f := A.indicator fun _ => (1 : ℝ))
      (Eventually.of_forall fun ω => indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) ω)
    filter_upwards [hnn] with ω hω
    simp only [Pi.zero_apply] at hω
    have := not_lt.1 hN
    linarith

end Step

/-- **GM Proposition 4.12 on complete spaces** from CONF L3.6 in the on-event form
`CONFLem3_6AtAENE` (D110), CONF Lemma 2.1 and `ConfRKAddConst` -/
theorem p412n_P4_12AtC' (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) (hRK : ConfRKAddConst) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {cp : CONFParams}
    (H36 : CONF.CONFLem3_6AtAENE γ D c cp)
    {χ χ' : ℝ} (hχ : 0 < χ) (hχχ' : χ < χ') (H39 : CONFThm3_9At γ D c cp χ)
    (hHL : P412jHarmLoc) (hbr : P412jBridge D) (hGU : P412jGoodU)
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) :
    GMP4_12AtC γ D c cp χ χ' sel := by
  obtain ⟨α, C₀, hα, hC₀, HS⟩ := p412n_step_k' h38 hC24 hC27 hC14 hγ hγ2 hD H36
    (p412j_EDetAll hHL hD cp)
  obtain ⟨βC, hβC, H40⟩ := p412b_eq440 h38 hγ hγ2 hD H39
  have hχ' : 0 < χ' := hχ.trans hχχ'
  have hq1 : 1 < χ' / χ := (one_lt_div hχ).2 hχχ'
  set mm := min (χ / χ') 1 with hmm
  have hm0 : 0 < mm := lt_min (div_pos hχ hχ') one_pos
  set κ := mm / (2 * (χ' / χ)) with hκdef
  have hκ : 0 < κ := div_pos hm0 (by linarith)
  have hκq : κ * (χ' / χ) = mm / 2 := by
    rw [hκdef]; field_simp
  have he1 : κ * (χ' / χ) < χ / χ' := by
    rw [hκq]; linarith [min_le_left (χ / χ') 1, div_pos hχ hχ']
  have he2 : κ * (χ' / χ) < 1 := by rw [hκq]; linarith [min_le_right (χ / χ') 1]
  have hκ1 : κ ≤ 1 := by
    have : κ * (χ' / χ) ≥ κ := le_mul_of_one_le_right hκ.le hq1.le
    linarith
  set ω₀ := κ * α / 4 with hω₀def
  have hω₀ : 0 < ω₀ := by positivity
  set β := min (min (κ * χ / 8) (ω₀ * βC / 4)) (min (χ / χ' / 2) (1 / 2)) with hβdef
  have hβ : 0 < β := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) (by norm_num))
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hβκ8 : β ≤ κ * χ / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hβκ : β < κ * χ / 4 := hβκ8.trans_lt (by linarith [mul_pos hκ hχ])
  have hβω : 2 * β < ω₀ * βC := by
    have : β ≤ ω₀ * βC / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith [mul_pos hω₀ hβC]
  have hβχ' : β < χ / χ' :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith [div_pos hχ hχ'])
  have hβχ : β < χ := hβκ.trans_le (by nlinarith)
  set θ := min (β / 4) (ω₀ / 2) with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθ1 : θ < 1 := (min_le_left _ _).trans_lt (by linarith)
  have hθω : θ < ω₀ := (min_le_right _ _).trans_lt (by linarith)
  have hθβ : θ < β / 2 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨ε₄, hε₄, Hsm⟩ := p412j_small hκ hα (by linarith : (0 : ℝ) < C₀)
  refine ⟨β, θ, ⟨hβ, hβ1⟩, ⟨hθ, hθ1⟩, hβχ', fun R hRξ hRc hRp hRχ hRχ' hl0 hl01 hl12 hl23 hlam
    _ hμ hμν hℓ hUV _ a ha haℓ M _ => ?_⟩
  have hℓ0 : 0 < R.ℓ := hℓ.1
  have hξ : 0 ≤ R.ξ := by rw [hRξ]; exact (xiGamma_pos hγ).le
  have hc2 : 0 < regC2const R a := by have := ha.1; unfold regC2const; positivity
  have ha' : 0 < a / regC2const R a := div_pos ha.1 hc2
  obtain ⟨ε₂, hε₂, Hrate⟩ := gm_L4_15_step4_rate.{0} ha' hθ hθω hθβ M
  obtain ⟨ε₁, hε₁, H40'⟩ := H40 ω₀ β hω₀ hβ hβω R.ℓ R.ξ χ' a ha haℓ M
  obtain ⟨ε₃, hε₃, HG⟩ := hGU R ha.1 ha.2 haℓ (by rw [hRχ]; exact hχ) (by rw [hRχ']; exact hχ')
    hβ (by rw [hRχ]; exact hβχ) hl0 hl01 hl12 hl23 hlam (hμ.trans hμν).le hUV hξ
    (by rw [hRχ, hRχ']; exact hχχ'.le) hκ (by rw [hRχ]; exact hβκ) (by rw [hRχ, hRχ']; exact he1)
    (by rw [hRχ, hRχ']; exact he2)
  refine ⟨2, min (min ε₁ ε₂) (min ε₃ ε₄), lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄),
    fun E rr hrr Ω _ P _ _ h hh hgeo H hH 𝕣 h𝕣 𝕫 h𝕫 𝕨 h𝕨 hzw n hn => ?_⟩
  set R' : RegPar := { R with E := E, rr := rr } with hR'
  set ε : ℝ := (2 : ℝ)⁻¹ ^ n with hεdef
  have hε0 : 0 < ε := by positivity
  have hnε : ε < min (min ε₁ ε₂) (min ε₃ ε₄) := hn
  have hεε₁ : ε < ε₁ := hnε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεε₂ : ε < ε₂ := hnε.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεε₃ : ε < ε₃ := hnε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεε₄ : ε < ε₄ := hnε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hε1, hκ36, hsm⟩ := Hsm ε ⟨hε0, hεε₄⟩
  obtain ⟨m, hm18, hm36⟩ := p412j_dyadic (Real.rpow_pos_of_pos hε0 κ) hκ36.le
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by linarith
  obtain ⟨hNC, hC1⟩ := p412j_NC_le hκ hα (by linarith) hε0 hε1 hδ0 hm36 hsm
  set L : ℕ := ⌊ε ^ (-ω₀)⌋₊ with hLdef
  set N : ℕ := 2 * L with hNdef
  have hℓ𝕣 : 0 < R.ℓ * 𝕣 := mul_pos hℓ0 h𝕣
  have hcpos : ∀ r, 0 < r → 0 < c r := hD.tightness.1
  have hc𝕣 : 0 < R'.c 𝕣 := by show 0 < R.c 𝕣; rw [hRc]; exact hcpos 𝕣 h𝕣
  have hcℓ : 0 ≤ R'.c (R'.ℓ * 𝕣) := by
    show 0 ≤ R.c (R.ℓ * 𝕣); rw [hRc]; exact (hcpos _ hℓ𝕣).le
  have h𝕫𝕨 : 𝕫 ≠ 𝕨 := by
    intro e; rw [e, sub_self, norm_zero] at hzw; linarith
  -- the a.s. good set of `h`
  set G₀ : Set Ω := {ω | H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 ∧ H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 ∧
    ((D (h ω)).IsLength ∧ (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) ∧
      ∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) ∧
    IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧
    (∀ s t : ℝ, 0 < s → s < t → ⋃ x ∈ confPts (D (h ω)) 𝕫 s t, arcOf (D (h ω)) 𝕫 t x =
        frontier (filledBall (D (h ω)) 𝕫 t))} with hG₀def
  have hG₀ : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    filter_upwards [hH.ae_eq 𝕣 h𝕣 0, hH.ae_eq 𝕣 h𝕣 𝕫, gm_ae_len_bdd_geod h38 hγ hγ2 hD hh 𝕫,
      hgeo 𝕫 𝕨 h𝕫𝕨, gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫] with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, fun s t hs hst => (h5 s t hs hst).2.2.2⟩
  have hG₀c : P G₀ᶜ = 0 := ae_iff.1 hG₀
  -- (4.40): the bad event
  set Ereg : Set Ω := regEvent D P h H R' 𝕣 a with hEregdef
  set B1 : Set Ω := {ω | ∃ k ≤ p4K R' a ε β, ((L : ℕ∞) : ℕ∞) <
    (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R'.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R'.ℓ 𝕣 ε β k ω)).encard}
    with hB1def
  have h440 : P (Ereg ∩ B1) ≤ ENNReal.ofReal (ε ^ M) :=
    H40' ε ⟨hε0, hεε₁⟩ R' hRξ hRc hRp hRχ rfl rfl hRχ' hξ (by rw [show R'.χ = χ from hRχ]; exact hχ.le)
      hUV P h hh H 𝕣 h𝕣 hc𝕣 hcℓ 𝕫 h𝕫 (hH.ae_eq 𝕣 h𝕣 0) (hH.ae_eq 𝕣 h𝕣 𝕫)
      (hH.ae_eq (R.ℓ * 𝕣) hℓ𝕣 𝕫)
      ((gm_ae_len_bdd_geod h38 hγ hγ2 hD hh 𝕫).mono fun ω hω => ⟨hω.1, hω.2.1⟩)
      (fun k _ => hbr P h hh 𝕫 R.ℓ 𝕣 ε β k)
  set Good : ℕ → Set Ω := fun k => {ω | (zkE D sel h R' 𝕫 𝕨 𝕣 ε β k ω).Nonempty} with hGooddef
  have hRξ' : R'.ξ = xiGamma γ := hRξ
  have hRc' : R'.c = c := hRc
  have hRp' : R'.p = cp := hRp
  -- the events `F_q = {B̄_{2^{-q}}(𝕫) ⊆ int 𝓑^•_{t_0}}`
  set F : ℕ → Set Ω := fun q => {ω | closedBall 𝕫 ((2 : ℝ)⁻¹ ^ q) ⊆
    interior (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β 0 ω))} with hFdef
  have hkey : ∀ q : ℕ, P.real (p412Bad D sel P h H R' 𝕫 𝕨 𝕣 a ε β θ) ≤
      2 * ε ^ M + P.real (F q)ᶜ := by
    intro q
    -- the field normalized at `ψ_q`
    set ψ : TestC := bumpTest q 𝕫 with hψdef
    have hψ1 : ∫ x, ψ x = 1 := GFFLaw.integral_bumpTest q 𝕫
    have hψs : tsupport (ψ : ℂ → ℝ) = closedBall 𝕫 ((2 : ℝ)⁻¹ ^ q) := tsupport_bumpTest q 𝕫
    set a₀ : Ω → ℝ := fun ω => -(h ω ψ) with ha₀
    have ha₀m : Measurable a₀ := ((measurable_evalDist ψ).comp hh.measurable).neg
    set g : Ω → DistC := fun ω => addConst (h ω) (a₀ ω) with hgdef
    have hg : IsWholePlaneGFF g P := CONF.isWholePlaneGFF_normIn hh ψ
    have hg0 : ∀ ω, g ω ψ = 0 := fun ω => CONF.normIn_apply_psi h hψ1 ω
    set Eη : Set Ω := {ω | tsupport (ψ : ℂ → ℝ) ⊆
      interior (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β 0 ω))} with hEηdef
    have hEηm : MeasurableSet[p412iFilt P D g 𝕫 R.ℓ 𝕣 ε β 0] Eη := by
      have h1 := CONF.confD110_setSigma_supp_subset_interior
        (A := fun ω => filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β 0 ω))
        (fun ω => gm_filledBall_isClosed _ _ _) ψ.hasCompactSupport.isCompact
      have h2 := p412f_setSigma_le_localSigma g _ _ h1
      have h3 := gm_le_aeSigma (μ := P) (p412i_sigA_le h38 hγ hγ2 hD hg 𝕫 R.ℓ 𝕣 ε β 0) _ h2
      have hle : gmAESigma (gmSigA D g 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β 0)) P ≤
          p412iFilt P D g 𝕫 R.ℓ 𝕣 ε β 0 :=
        le_iSup₂_of_le (f := fun (j : ℕ) (_ : j ≤ 0) =>
          gmAESigma (gmSigA D g 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β j)) P) 0 le_rfl le_rfl
      exact hle _ h3
    have hEk : ∀ k, ∀ ω ∈ Eη, tsupport (ψ : ℂ → ℝ) ⊆
        interior (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω)) := by
      intro k ω hω
      refine hω.trans (interior_mono (gm_filledBall_mono _ _ ?_))
      rw [gm_s4T_eq, gm_s4T_eq]
      refine mul_le_mul_of_nonneg_left ?_ (gm_tauD_pos _ 𝕫 hℓ𝕣).le
      have : (0 : ℝ) ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε0.le β)
      simp only [Nat.cast_zero, zero_mul]
      linarith
    -- centres and CONF L3.6 events of `g`
    choose x G hxf hxc hGA hAm hAq using fun k => HS P g hg ψ hψ1 hg0 𝕫 (κ := κ) hℓ𝕣 h𝕣 hε0
      hε1.le hβ.le ⟨hδ0, hδ1⟩ hC1 k L Eη hEηm (hEk k)
    -- the a.s. comparison event
    set lm : Ω → ℝ := fun ω => Real.exp (xiGamma γ * a₀ ω) with hlmdef
    set G₁ : Set Ω := {ω | (∀ u v, (D (g ω)).1 (u, v) = lm ω * (D (h ω)).1 (u, v)) ∧
      (∀ K, confRK (xiGamma γ) c D P g cp 𝕣 δ K ω = confRK (xiGamma γ) c D P h cp 𝕣 δ K ω) ∧
      (∀ k j, x k j ω ∈ frontier (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω))) ∧
      ∀ k, ω ∈ Eη → (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω)
          (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω)).encard ≤ L →
        ∀ e ∈ p412fEndSet (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω),
          ∃ j < 2 * L, ∃ z : ℂ,
            p412eGoodZ (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω)) e z (ε ^ κ * 𝕣) ∧
            dist z (x k j ω) ≤ ε ^ κ * 𝕣} with hG₁def
    have hG₁ : ∀ᵐ ω ∂P, ω ∈ G₁ := by
      filter_upwards [hD.ae_dist_addConst (detGFFPlusCont hh),
        hRK hγ hγ2 hD cp P h hh a₀ ha₀m 𝕣 δ h𝕣 ⟨hδ0, hδ1⟩, ae_all_iff.2 hxf,
        ae_all_iff.2 hxc] with ω h1 h2 h3 h4
      exact ⟨fun u v => h1 (a₀ ω) u v, h2, h3, h4⟩
    have hG₁c : P G₁ᶜ = 0 := ae_iff.1 hG₁
    set Bad : Set Ω := B1 ∪ G₀ᶜ ∪ G₁ᶜ ∪ (F q)ᶜ with hBaddef
    have hBadE : P (Ereg ∩ Bad) ≤ ENNReal.ofReal (ε ^ M) + P (F q)ᶜ := by
      calc P (Ereg ∩ Bad) ≤ P ((Ereg ∩ B1) ∪ G₀ᶜ ∪ G₁ᶜ ∪ (F q)ᶜ) := by
            refine measure_mono fun ω hω => ?_
            obtain ⟨hE, ((hb | hb) | hb) | hb⟩ := hω
            · exact Or.inl (Or.inl (Or.inl ⟨hE, hb⟩))
            · exact Or.inl (Or.inl (Or.inr hb))
            · exact Or.inl (Or.inr hb)
            · exact Or.inr hb
        _ ≤ P (Ereg ∩ B1) + P G₀ᶜ + P G₁ᶜ + P (F q)ᶜ :=
            (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
              (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
        _ ≤ ENNReal.ofReal (ε ^ M) + P (F q)ᶜ := by
            rw [hG₀c, hG₁c, add_zero, add_zero]; exact add_le_add h440 le_rfl
    have hB' : P.real (Ereg ∩ Bad) ≤ ε ^ M + P.real (F q)ᶜ := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        measure_ne_top _ _⟩) hBadE
      rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),
        ENNReal.toReal_ofReal (by positivity)] at this
    -- the events `A_k ∪ E_ηᶜ`
    set A : ℕ → Set Ω := fun k => (⋂ j ∈ Finset.range N, G k j) ∪
      {ω | ENNReal.ofReal (s4S D g 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) <
        confSigma (xiGamma γ) c D P g cp 𝕫 𝕣 δ (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω) ω} ∪
      {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω)
        (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω)).encard} ∪ Eηᶜ with hAdef
    have hq : ∀ k ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ - 1, ∀ᵐ ω ∂P,
        1 - ε ^ ω₀ ≤ P[(A k).indicator (fun _ => (1 : ℝ)) | p412iFilt P D g 𝕫 R.ℓ 𝕣 ε β k] ω :=
      fun k _ => (hAq k).mono fun ω hω => by rw [← hNdef] at hω; linarith
    have hgood : ∀ k ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ - 1, Ereg ∩ Badᶜ ∩ A k ⊆ Good k := by
      intro k hk ω hω
      obtain ⟨⟨hωE, hωB⟩, hωA⟩ := hω
      have hωB1 : ω ∉ B1 := fun h' => hωB (Or.inl (Or.inl (Or.inl h')))
      have hωG : ω ∈ G₀ := by by_contra h'; exact hωB (Or.inl (Or.inl (Or.inr h')))
      have hωG1 : ω ∈ G₁ := by by_contra h'; exact hωB (Or.inl (Or.inr h'))
      have hωF : ω ∈ F q := by by_contra h'; exact hωB (Or.inr h')
      obtain ⟨hH0, hH𝕫, ⟨hL', hbd, hgeod⟩, hsel, hcov⟩ := hωG
      obtain ⟨hd, hRKω, hfr, hcen⟩ := hωG1
      have hlm : 0 < lm ω := Real.exp_pos _
      have hS : ∀ j, s4S D g 𝕫 R.ℓ 𝕣 ε β j ω = lm ω * s4S D h 𝕫 R.ℓ 𝕣 ε β j ω := fun j => by
        rw [gm_s4S_eq, gm_s4S_eq, p412n_tauD_smul hlm hd, mul_assoc]
      have hT : ∀ j, s4T D g 𝕫 R.ℓ 𝕣 ε β j ω = lm ω * s4T D h 𝕫 R.ℓ 𝕣 ε β j ω := fun j => by
        rw [gm_s4T_eq, gm_s4T_eq, p412n_tauD_smul hlm hd, mul_assoc]
      have hB : ∀ j, filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β j ω) =
          filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β j ω) := fun j => by
        rw [hT, p412n_filledBall_smul hlm hd]
      have hCf : confPts (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω) =
          confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) := by
        rw [hS, hT, p412n_confPts_smul hlm hd]
      have hEs : p412fEndSet (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω)
          (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω) =
          p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) := by
        rw [hS, hT, p412n_endSet_smul hlm hd]
      have hωη : ω ∈ Eη := by
        show tsupport (ψ : ℂ → ℝ) ⊆
          interior (filledBall (D (g ω)) 𝕫 (s4T D g 𝕫 R.ℓ 𝕣 ε β 0 ω))
        rw [hB 0, hψs]; exact hωF
      have hωA' : ω ∈ (⋂ j ∈ Finset.range N, G k j) ∪
          {ω | ENNReal.ofReal (s4S D g 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) <
            confSigma (xiGamma γ) c D P g cp 𝕫 𝕣 δ (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω) ω} ∪
          {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω)
            (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω)).encard} := by
        rcases hωA with h' | h'
        · exact h'
        · exact absurd hωη h'
      have hConf : (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω)
          (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard ≤ L := by
        by_contra h'; exact hωB1 ⟨k, hk, not_le.1 h'⟩
      have hτ : 0 < s4Unit D h 𝕫 R.ℓ 𝕣 ω := gm_tauD_pos (D (h ω)) 𝕫 hℓ𝕣
      have hs0 : 0 < s4S D h 𝕫 R.ℓ 𝕣 ε β k ω := by unfold s4S; positivity
      have hst : s4S D h 𝕫 R.ℓ 𝕣 ε β k ω < s4T D h 𝕫 R.ℓ 𝕣 ε β k ω := by
        unfold s4T
        have : 0 < ε ^ (2 * β) * s4Unit D h 𝕫 R.ℓ 𝕣 ω := by positivity
        linarith
      have hcen' : ∀ e ∈ p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω)
          (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω), ∃ j < N, ∃ z : ℂ,
          p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) e z (ε ^ κ * 𝕣) ∧
          dist z (x k j ω) ≤ ε ^ κ * 𝕣 := by
        intro e he
        rw [← hEs] at he
        obtain ⟨j, hj, z, hz1, hz2⟩ := hcen k hωη (by rw [hCf]; exact hConf) e he
        exact ⟨j, hj, z, by rw [← hB k]; exact hz1, hz2⟩
      have HG' := HG E rr R' rfl (D := D) (P := P) (h := h) (H := H) (sel := sel) h𝕣 hc𝕣 n hεε₃
        m hm18 hm36 ω hωE 𝕫 h𝕫 𝕨 hzw hH0 hH𝕫 hL' hbd hgeod
        (fun j hj => hrr 𝕣 h𝕣 ε ⟨hε0, hε1⟩ j hj) hsel k hk (hcov _ _ hs0 hst) N L (x k) (G k)
        hcen'
      rw [hRξ', hRc', hRp'] at HG'
      refine HG' (fun j hj => ?_) ?_ hConf
      · have hA := hGA k j ω hj (hfr k j)
        rw [hB k] at hA
        exact p412n_propA_of_smul hlm hd (le_of_eq (hRKω _)) hA
      · rcases hωA' with (h1 | h1) | h1
        · exact Or.inl (Or.inl h1)
        · refine Or.inl (Or.inr ?_)
          have h1' : ENNReal.ofReal (s4S D g 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) <
              confSigma (xiGamma γ) c D P g cp 𝕫 𝕣 δ (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω) ω := h1
          rw [hS, hT] at h1'
          have h2 := h1'.trans_le (p412n_confSigma_le hlm hd (fun K => le_of_eq (hRKω K)))
          rw [ENNReal.ofReal_mul hlm.le] at h2
          exact lt_of_not_ge fun hle => (not_lt.2 (mul_le_mul_of_nonneg_left hle zero_le)) h2
        · refine Or.inr ?_
          have h1' : ((L : ℕ∞) : ℕ∞) < (confPts (D (g ω)) 𝕫 (s4S D g 𝕫 R.ℓ 𝕣 ε β k ω)
              (s4T D g 𝕫 R.ℓ 𝕣 ε β k ω)).encard := h1
          rw [hCf] at h1'
          exact h1'
    have hmain := Hrate ε ⟨hε0, hεε₂⟩ (p412iFilt P D g 𝕫 R.ℓ 𝕣 ε β) A Ereg Bad Good
      (fun k _ => hAm k) hq hgood
    classical
    have e : P.real (p412Bad D sel P h H R' 𝕫 𝕨 𝕣 a ε β θ) =
        P.real (Ereg ∩ {x | (((Finset.range (⌊a / regC2const R a * ε ^ (-β)⌋₊ - 1 + 1)).filter
          (fun k => x ∈ Good k)).card : ℝ) <
            (1 - ε ^ θ) * ((⌊a / regC2const R a * ε ^ (-β)⌋₊ - 1 : ℕ) : ℝ)}) := rfl
    rw [e]; linarith
  -- `q → ∞`
  have hFm : ∀ q, MeasurableSet (F q) := fun q => by
    have h1 := CONF.confD110_setSigma_supp_subset_interior
      (A := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β 0 ω))
      (fun ω => gm_filledBall_isClosed _ _ _) (isCompact_closedBall 𝕫 ((2 : ℝ)⁻¹ ^ q))
    exact p412i_sigA_le h38 hγ hγ2 hD hh 𝕫 R.ℓ 𝕣 ε β 0 _ (p412f_setSigma_le_localSigma h _ _ h1)
  have hFanti : Antitone fun q => (F q)ᶜ := by
    intro q q' hqq' ω hω hω'
    exact hω fun y hy => hω' (closedBall_subset_closedBall
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hqq') hy)
  have hFint : (⋂ q, (F q)ᶜ) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_compl_iff, mem_empty_iff_false, iff_false, not_forall, not_not]
    have htpos : 0 < s4T D h 𝕫 R.ℓ 𝕣 ε β 0 ω := by
      rw [gm_s4T_eq]
      have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
      exact mul_pos (gm_tauD_pos _ 𝕫 hℓ𝕣) (by simp only [Nat.cast_zero, zero_mul]; linarith)
    have hopen : IsOpen (ballM (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β 0 ω)) := jb_isOpen_ballM _ _ _
    obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 hopen 𝕫 (jb_mem_ballM _ _ _ htpos)
    obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨q, (closedBall_subset_ball hq).trans (hrB.trans
      (interior_maximal (fun w hw => Or.inl (subset_closure hw)) hopen))⟩
  have hlim : Tendsto (fun q => P.real (F q)ᶜ) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := P)
      (fun q => (hFm q).compl.nullMeasurableSet) hFanti ⟨0, measure_ne_top _ _⟩
    rw [hFint, measure_empty] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, Measure.real] using h2
  have hfin : P.real (p412Bad D sel P h H R' 𝕫 𝕨 𝕣 a ε β θ) ≤ 2 * ε ^ M := by
    have := ge_of_tendsto' ((tendsto_const_nhds (x := 2 * ε ^ M)).add hlim) hkey
    rwa [add_zero] at this
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hfin

/-- **`P412OfL36AE0` from the proved CONF Lemma 2.1 and the constant-invariance of `R^ε_𝕣`** -/
theorem p412n_P412OfL36AE0' (hRK : ConfRKAddConst) : P412OfL36AE0 := by
  intro h38 hC27 hC14 γ hγ hγ2 D c hD cp H0 χ χ' hχ hχχ' H39 sel _
  exact p412j_P4_12At_of_complete
    (p412n_P4_12AtC' h38 (CONF.confLem2_4 h38) hC27 hC14 hRK hγ hγ2 hD
      (CONF.confLem3_6AtAENE_of_AE0 H0) hχ hχχ' H39 HarmLoc.p412jHarmLoc
      (p412k_bridge h38 hγ hγ2 hD) p412j_goodU sel)

end LQGMetric.GM
