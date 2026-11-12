/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iConf at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iStopK
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Pos1

/-!
# GM L4.15 Step 3–4: `{#Conf_k > ε^{-ω}}` is an event of `σ(𝓑^•_{t_{k+1}}, h|)` (a.s.)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
L4.15 Step 3, l. 2174 ("On the event `{#𝒳_k ≤ ε^{-ω}}` (which is in `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`")
and Step 4, l. 2189–2191. Decision D98 §3: "`{#Conf_k > ε^{-ω}}` [is an] a.s. event of
`σ(𝓑^•_{s_{k+1}}, h|)` … by D65 (`gmP_leEncardAn`)".

* `p412i_confCount_aeEventIn`: `{m ≤ #Conf(τc₁, τc)}` is a.s. an event of `σ(𝓑^•_{τc}, h|)`
  (analytic by `gmP_leEncardAn`, saturated by `gm_hitSet_transfer`, piece method
  `gm_aeEventIn_sigA_of_sat`);
* **`p412i_confGt_aeSigma`**: the event `{⌊ε^{-ω₀}⌋ < #Conf_k}` of (4.40) / `p412b_eq440` is an event
  of the completed `σ(𝓑^•_{t_{k+1}}, h|)` — the input `B` of `p412i_Ak_filt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

theorem p412i_posS_eq (d : ContMetric) (𝕫 : ℂ) (s t : ℝ) :
    gmPosS (fun _ => univ) (fun _ _ => True) d 𝕫 s t ∅ ∅ = confPts d 𝕫 s t := by
  ext x
  simp [gmPosS]

/-- `{m ≤ #Conf(τ c₁, τ c)}` is a.s. an event of `σ(𝓑^•_{τ c}, h|)` (GM l. 2174) -/
theorem p412i_confCount_aeEventIn (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {R c₁ c : ℝ}
    (hR : 0 < R) (hc₁ : c₁ ≤ c) (hc : 1 < c) (m : ℕ) :
    AEEventIn P (localSigma h (fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * c)))
      {ω | (m : ℕ∞) ≤ (confPts (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * c₁)
        (tauD (D (h ω)) 𝕫 R * c)).encard} := by
  have hΦ : GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet}
      {p : ContMetric × ℂ | (fun (_ : ContMetric) (_ : ℂ) => True) p.1 p.2} :=
    gmAn_of_measurableSet (by simp only [setOf_true]; exact MeasurableSet.univ)
  have hAn := gmP_leEncardAn (V := fun _ => univ) (Φ := fun _ _ => True) (fun _ => isOpen_univ) hΦ 𝕫 R c₁ c ∅ m
  simp only [p412i_posS_eq] at hAn
  exact gm_aeEventIn_sigA_of_sat h38 hγ hγ2 hD hh 𝕫 hR hc (gm_uMeas_of_an hAn)
    (fun d₁ h₁ d₂ h₂ U hU heq hKU hd => by
      have l1 := isLength_of_mem_lenSet h₁
      have l2 := isLength_of_mem_lenSet h₂
      have hτpos := gm_tauD_pos d₁ 𝕫 hR
      obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hc hU heq hτpos hKU
      have hA : GMAgree d₁ d₂ U 𝕫 (tauD d₁ 𝕫 R * c) :=
        ⟨fun x _ y _ => by rw [heq], fun u hu => (hball u hu).symm, hKU,
          mul_pos hτpos (by linarith)⟩
      have h1 : tauD d₁ 𝕫 R * c₁ ≤ tauD d₁ 𝕫 R * c :=
        mul_le_mul_of_nonneg_left hc₁ hτpos.le
      show (m : ℕ∞) ≤ (confPts d₂ 𝕫 (tauD d₂ 𝕫 R * c₁) (tauD d₂ 𝕫 R * c)).encard
      rw [hτ]
      exact hd.trans (encard_le_encard fun x hx => gm_hitSet_transfer hA h1 le_rfl hx))

/-- **`{⌊ε^{-ω₀}⌋ < #Conf_k}` is an event of the completed `σ(𝓑^•_{t_{k+1}}, h|)`** -/
theorem p412i_confGt_aeSigma [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k L : ℕ) :
    MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1))) P]
      {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)
        (s4T D h 𝕫 ℓ 𝕣 ε β k ω)).encard} := by
  have h1 : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) h1
  have hA := p412i_confCount_aeEventIn h38 hγ hγ2 hD hh 𝕫 (R := ℓ * 𝕣)
    (c₁ := 1 + k * ε ^ β) (c := 1 + k * ε ^ β + ε ^ (2 * β)) hℓ𝕣 (by linarith) (by linarith)
    (L + 1)
  have e1 : {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)
      (s4T D h 𝕫 ℓ 𝕣 ε β k ω)).encard} =
      {ω | ((L + 1 : ℕ) : ℕ∞) ≤ (confPts (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) *
        (1 + k * ε ^ β)) (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β)))).encard} := by
    ext ω
    simp only [mem_setOf_eq, gm_s4S_eq, gm_s4T_eq, Nat.cast_add, Nat.cast_one]
    exact (ENat.add_one_le_iff (ENat.coe_ne_top L)).symm
  have hsig : gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k) =
      localSigma h (fun ω => filledBall (D (h ω)) 𝕫
        (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β)))) := by
    unfold gmSigA
    rw [funext (gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β k)]
  rw [e1]
  obtain ⟨F, hF, hEF⟩ := hA
  have hF' : MeasurableSet[gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)] F := by rw [hsig]; exact hF
  obtain ⟨F', hF'm, hFF'⟩ := gm_measurableSet_aeSigma
    (gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (Nat.le_succ k) F hF')
  exact p412i_aeSigma_of_aeEventIn _ (p412i_sigA_le h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β (k + 1))
    ⟨F', hF'm, hEF.trans hFF'⟩

/-- **GM l. 2189–2191, `A_k ∈ ℱ (k+1)`** with GM's `A_k = (⋂_{j<N} G_j) ∪ {σ_k > s_{k+1}} ∪
{#Conf_k > ⌊ε^{-ω₀}⌋}` (input `hA` of `gm_L4_15_step4_rate`), from CONF l. 1260 (`P412iEDet`) -/
theorem p412i_Ak_mem [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k N L : ℕ)
    (G : ℕ → Set Ω) (hG : ∀ j, MeasurableSet[filledBallSigmaAt D h 𝕫
      (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)] (G j)) :
    MeasurableSet[p412iFilt P D h 𝕫 ℓ 𝕣 ε β (k + 1)]
      ((⋂ j ∈ Finset.range N, G j) ∪
        {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
          confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} ∪
        {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)
          (s4T D h 𝕫 ℓ 𝕣 ε β k ω)).encard}) :=
  p412i_Ak_filt h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k N G hG
    (p412i_confGt_aeSigma h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε k L)

omit [IsProbabilityMeasure P] in
/-- `ℱ (k+1)` (built from completed σ-algebras) is closed under `P`-a.e. modification -/
theorem p412i_filt_congr [P.IsComplete] (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ)
    (ℓ 𝕣 ε β : ℝ) (k : ℕ) {E E' : Set Ω}
    (hE : MeasurableSet[p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] E) (hEE : E =ᵐ[P] E') :
    MeasurableSet[p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] E' := by
  have hN0 : P (symmDiff E E') = 0 := (measure_symmDiff_eq_zero_iff).2 hEE
  have hNm : MeasurableSet (symmDiff E E') := (NullMeasurableSet.of_null hN0).measurable_of_complete
  have hNa : MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)) P] (symmDiff E E') := by
    refine MeasurableSpace.measurableSet_inf.2 ⟨hNm, ∅,
      @MeasurableSet.empty Ω (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)), ?_⟩
    rw [inter_univ]
    exact (measure_eq_zero_iff_ae_notMem.1 hN0).mono fun ω hω => by simp [hω]
  have hN : MeasurableSet[p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] (symmDiff E E') :=
    gm_le_supFilt _ _ k _ hNa
  have e : E' = symmDiff E (symmDiff E E') := (symmDiff_symmDiff_cancel_left E E').symm
  rw [e]
  exact hE.symmDiff hN

/-- **`A_k ∈ ℱ (k+1)`** (`p412i_Ak_mem`) for a.s. events `G_j` of `σ(𝓑^•_{σ_k}, h|)` (D114:
CONF L3.6 gives `G_j` in `AEEventIn` form) -/
theorem p412i_Ak_mem_ae [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k N L : ℕ)
    (G : ℕ → Set Ω) (hG : ∀ j, AEEventIn P (filledBallSigmaAt D h 𝕫
      (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)) (G j)) :
    MeasurableSet[p412iFilt P D h 𝕫 ℓ 𝕣 ε β (k + 1)]
      ((⋂ j ∈ Finset.range N, G j) ∪
        {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
          confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} ∪
        {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)
          (s4T D h 𝕫 ℓ 𝕣 ε β k ω)).encard}) := by
  choose G₀ hG₀m hG₀e using hG
  refine p412i_filt_congr D h 𝕫 ℓ 𝕣 ε β (k + 1)
    (p412i_Ak_mem h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k N L G₀ hG₀m) ?_
  have hall : ∀ᵐ ω ∂P, ∀ j, (ω ∈ G j ↔ ω ∈ G₀ j) :=
    ae_all_iff.2 fun j => (hG₀e j).mem_iff
  filter_upwards [hall] with ω hω
  simp only [mem_union, mem_iInter, Finset.mem_range, hω]

end LQGMetric.GM
