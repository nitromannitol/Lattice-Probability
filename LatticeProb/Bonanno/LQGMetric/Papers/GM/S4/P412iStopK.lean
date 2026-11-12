/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iStopK at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iPiece2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasF
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasA

/-!
# GM L4.15 Step 4 (l. 2189–2191): `σ_k` is a stopping time — the events of D98 (b) for `A_k`

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
L4.15 Step 4, l. 2189–2191 ("The radius `σ_k` is a stopping time for `{(𝓑^•_s, h|_{𝓑^•_s})}`, so
the event inside the conditional probability in (4.40′) belongs to
`σ(𝓑^•_{s_{k+1}}, h|_{𝓑^•_{s_{k+1}}})`"); CONF (arXiv:1905.00381) l. 1302. Decision D98 (b2),
packet P-stop. `σ_k = confSigma … 𝕫 𝕣 δ t_k` (GM (4.38) with `δ = ε^κ`, or the dyadic `δ` of
DV-L36-dyadic).

* (b2-C′) **`p412i_stopC_piece`**: `{σ_k ≤ s_{k+1}}` is piecewise local for `𝓑^•_{t_{k+1}}`;
* (b2-H′) **`p412i_stopH_piece`**: so are the events `{𝓑^•_{σ_k} ∩ V ≠ ∅} ∩ {σ_k ≤ s_{k+1}}`;
* **`p412i_stop_s4`**: `E ∈ σ(𝓑^•_{σ_k}, h|)` ⇒ `E ∩ {σ_k ≤ s_{k+1}}` is an event of the completed
  `σ(𝓑^•_{t_{k+1}}, h|)` (`gmAESigma`, D70), and **`p412i_stopGt_s4`**: so is `{σ_k > s_{k+1}}`.
All from CONF l. 1260 in the form `P412iEDet` (hypothesis; see P412iPiece).
GM state the conclusion for `σ(𝓑^•_{s_{k+1}}, h|)`; we land in `σ(𝓑^•_{t_{k+1}}, h|)` which is what
GM use next ("Since `t_{k+1} ≥ s_{k+1}`", l. 2190) — no deviation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

theorem p412i_gmTauB_nonneg (𝕫 : ℂ) (R : ℝ) (d : ContMetric) : 0 ≤ gmTauB 𝕫 R d :=
  Real.sInf_nonneg (fun _ hx => hx.1.le)

/-- the constants `c_t = 1 + kε^β + ε^{2β} ≤ c_s = 1 + (k+1)ε^β < c_T = c_s + ε^{2β}` -/
theorem p412i_consts {ε β : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (k : ℕ) :
    0 < 1 + (k : ℝ) * ε ^ β + ε ^ (2 * β) ∧
    1 + (k : ℝ) * ε ^ β + ε ^ (2 * β) ≤ 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β ∧
    1 + ((k + 1 : ℕ) : ℝ) * ε ^ β < 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) ∧
    1 < 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) := by
  have h1 : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have h3 : ε ^ (2 * β) ≤ ε ^ β :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hk : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) h1
  push_cast
  refine ⟨by linarith, by nlinarith, by linarith, by nlinarith⟩

/-- **(b2-C′)**: `{σ_k ≤ s_{k+1}}` is piecewise local for `𝓑^•_{t_{k+1}}` (GM l. 2189) -/
theorem p412i_stopC_piece (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k n : ℕ)
    (fs : Finset (ℤ × ℤ)) :
    MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)) n
      (hullFin n fs) P]
      {ω | confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω ≤
        ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)} := by
  obtain ⟨hct, hcs, hcT, hcT1⟩ := p412i_consts hε hε1 hβ k
  have hB : (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)) = fun ω =>
      filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) *
        (1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β))) :=
    funext fun ω => by rw [gm_s4T_eq]
  rw [hB]
  simp only [gm_s4T_eq, gm_s4S_eq]
  refine p412i_sig_piece h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hct hcs hcT hcT1 hδ
    (fun _ τ x => x ≤ ENNReal.ofReal (τ * (1 + ((k + 1 : ℕ) : ℝ) * ε ^ β)))
    (fun _ _ _ hx => hx) (fun _ _ _ _ _ _ hx => hx) ?_ n fs
  have hm := gm_measurable_tauB 𝕫 (ℓ * 𝕣)
  exact p412i_measurableSet_sigLe 𝕫 (hm.mul_const _) (hm.mul_const _) (confN p δ) 𝕣 δ
    (fun d => mul_nonneg (p412i_gmTauB_nonneg _ _ d) hct.le)
    (fun d => mul_le_mul_of_nonneg_left hcs (p412i_gmTauB_nonneg _ _ d))

/-- **(b2-H′)**: the hit events of `𝓑^•_{σ_k}` on `{σ_k ≤ s_{k+1}}` are piecewise local for
`𝓑^•_{t_{k+1}}` -/
theorem p412i_stopH_piece (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k n : ℕ)
    (fs : Finset (ℤ × ℤ)) {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)) n
      (hullFin n fs) P]
      ({ω | (filledBallE (D (h ω)) 𝕫
          (confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω) ∩ V).Nonempty} ∩
        {ω | confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω ≤
          ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)}) := by
  obtain ⟨hct, hcs, hcT, hcT1⟩ := p412i_consts hε hε1 hβ k
  set cs := 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β
  set cT := 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β)
  have e1 : ({ω | (filledBallE (D (h ω)) 𝕫
          (confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω) ∩ V).Nonempty} ∩
        {ω | confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω ≤
          ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)}) =
      {ω | (fun _ τ x => x ≤ ENNReal.ofReal (τ * cs) ∧ (filledBallE (D (h ω)) 𝕫 x ∩ V).Nonempty)
        (D (h ω)) (tauD (D (h ω)) 𝕫 (ℓ * 𝕣)) (confSigma ξ cc D P h p 𝕫 𝕣 δ
          (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + (k : ℝ) * ε ^ β + ε ^ (2 * β))) ω)} := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, gm_s4T_eq, gm_s4S_eq]
    exact and_comm
  have hfe : ∀ (d₁ d₂ : ContMetric) (τ : ℝ) (x : ℝ≥0∞),
      (∀ u ≤ τ * cT, filledBall d₂ 𝕫 u = filledBall d₁ 𝕫 u) → x < ENNReal.ofReal (τ * cT) →
      filledBallE d₂ 𝕫 x = filledBallE d₁ 𝕫 x := by
    intro d₁ d₂ τ x hfb hx
    have hne : x ≠ ⊤ := ne_top_of_lt hx
    have h0 : 0 < τ * cT := ENNReal.ofReal_pos.1 (pos_of_gt hx)
    simp only [filledBallE, hne, ↓reduceIte]
    exact hfb _ (ENNReal.toReal_le_of_le_ofReal h0.le hx.le)
  have hB : (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)) = fun ω =>
      filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) *
        (1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β))) :=
    funext fun ω => by rw [gm_s4T_eq]
  rw [e1, hB]
  refine p412i_sig_piece h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hct hcs hcT hcT1 hδ
    (fun d τ x => x ≤ ENNReal.ofReal (τ * cs) ∧ (filledBallE d 𝕫 x ∩ V).Nonempty)
    (fun _ _ _ hx => hx.1)
    (fun d₁ d₂ τ x hfb hx h1 => ⟨h1.1, (hfe d₁ d₂ τ x hfb hx).symm ▸ h1.2⟩) ?_ n fs
  have hm := gm_measurable_tauB 𝕫 (ℓ * 𝕣)
  exact (p412i_measurableSet_sigLe 𝕫 (hm.mul_const _) (hm.mul_const _) (confN p δ) 𝕣 δ
    (fun d => mul_nonneg (p412i_gmTauB_nonneg _ _ d) hct.le)
    (fun d => mul_le_mul_of_nonneg_left hcs (p412i_gmTauB_nonneg _ _ d))).inter
    (p412i_measurableSet_sigHit 𝕫 (hm.mul_const _) (confN p δ) 𝕣 δ hV)

/-- `σ(𝓑^•_{t_k}, h|) ≤ 𝓕` and `𝓑^•_{t_k}` a.s. bounded -/
theorem p412i_sigA_le [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) :
    gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k) ≤ ‹MeasurableSpace Ω› :=
  (iInf_le _ 0).trans (gm_hullSigma_filledBall_le (P := P) hh
    (hD.measurable.comp hh.measurable) (gm_measurable_s4T h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β k) 𝕫 0)

/-- **GM l. 2189–2191 for `σ_k`**: an event of `σ(𝓑^•_{σ_k}, h|)` intersected with
`{σ_k ≤ s_{k+1}}` is an event of the completed `σ(𝓑^•_{t_{k+1}}, h|)` -/
theorem p412i_stop_s4 [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k : ℕ)
    {E : Set Ω} (hE : MeasurableSet[filledBallSigmaAt D h 𝕫
      (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)] E) :
    MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1))) P]
      (E ∩ {ω | confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω ≤
        ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)}) := by
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  refine p412i_stop_inter_aeSigma D h 𝕫 _ (fun ω => ?_) (fun ω => gm_s4S_le_s4T hε _ ω) ?_
    (p412i_sigA_le h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β (k + 1))
    (fun n fs => p412i_stopC_piece h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k n fs)
    (fun n fs V hV => p412i_stopH_piece h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k n fs
      hV) hE
  · rw [gm_s4S_eq]
    obtain ⟨hct, hcs, -, -⟩ := p412i_consts hε hε1 hβ k
    exact mul_nonneg (gm_tauD_pos _ 𝕫 hℓ𝕣).le (hct.le.trans hcs)
  · filter_upwards [hlen] with ω hω
    exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _

/-- **`{σ_k > s_{k+1}}` is an event of the completed `σ(𝓑^•_{t_{k+1}}, h|)`** -/
theorem p412i_stopGt_s4 [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k : ℕ) :
    MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1))) P]
      {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
        confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} := by
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hC := p412i_stopEvent_aeSigma D h 𝕫
    (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)
    (s := s4S D h 𝕫 ℓ 𝕣 ε β (k + 1)) (by
      filter_upwards [hlen] with ω hω
      exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _)
    (p412i_sigA_le h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β (k + 1))
    (fun n fs => p412i_stopC_piece h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k n fs)
  have e1 : {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
      confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} =
      {ω | confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω ≤
        ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)}ᶜ := by
    ext ω; simp only [mem_setOf_eq, mem_compl_iff, not_le]
  rw [e1]
  exact hC.compl

/-- **`A_k` of GM (4.40′) is an event of the completed `σ(𝓑^•_{t_{k+1}}, h|)`** (D98 §3 (b)):
`A_k = (⋂_{j<N} G_j) ∪ {σ_k > s_{k+1}} ∪ B` with `G_j ∈ σ(𝓑^•_{σ_k}, h|)` and `B` (in GM
`{#Conf_k > ε^{-ω}}`) an event of the completed `σ(𝓑^•_{t_{k+1}}, h|)` -/
theorem p412i_Ak_aeSigma [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k N : ℕ)
    (G : ℕ → Set Ω) (hG : ∀ j, MeasurableSet[filledBallSigmaAt D h 𝕫
      (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)] (G j))
    {B : Set Ω} (hB : MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1))) P] B) :
    MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1))) P]
      ((⋂ j ∈ Finset.range N, G j) ∪
        {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
          confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} ∪ B) := by
  have hI : MeasurableSet[filledBallSigmaAt D h 𝕫
      (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)]
      (⋂ j ∈ Finset.range N, G j) :=
    @MeasurableSet.biInter Ω ℕ (filledBallSigmaAt D h 𝕫 _) _ _
      (Finset.range N).countable_toSet fun j _ => hG j
  have h1 := p412i_stop_s4 h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k hI
  have h2 := p412i_stopGt_s4 h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k
  have e1 : (⋂ j ∈ Finset.range N, G j) ∪
      {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
        confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} =
      ((⋂ j ∈ Finset.range N, G j) ∩
        {ω | confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω ≤
          ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)}) ∪
      {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
        confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_setOf_eq]
    rcases le_or_gt (confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)
      (ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω)) with hc | hc
    · exact ⟨fun h' => h'.elim (fun h'' => Or.inl ⟨h'', hc⟩) Or.inr,
        fun h' => h'.elim (fun h'' => Or.inl h''.1) Or.inr⟩
    · exact ⟨fun _ => Or.inr hc, fun _ => Or.inr hc⟩
  rw [e1]
  exact (h1.union h2).union hB

/-- the filtration of D98 §2: `ℱ k := ⨆_{j ≤ k} gmAESigma σ(𝓑^•_{t_j}, h|)` -/
def p412iFilt (P : Measure Ω) (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ)
    (ℓ 𝕣 ε β : ℝ) : Filtration ℕ ‹MeasurableSpace Ω› :=
  gmSupFilt (fun j => gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β j)) P)
    (fun _ => gm_aeSigma_le _)

/-- **`A_k ∈ ℱ (k+1)`** (hypothesis `hA` of `gm_L4_15_step4_rate`) -/
theorem p412i_Ak_filt [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {ℓ 𝕣 ε β δ : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hδ : 0 < δ * 𝕣) (k N : ℕ)
    (G : ℕ → Set Ω) (hG : ∀ j, MeasurableSet[filledBallSigmaAt D h 𝕫
      (fun ω => confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω)] (G j))
    {B : Set Ω} (hB : MeasurableSet[gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1))) P] B) :
    MeasurableSet[p412iFilt P D h 𝕫 ℓ 𝕣 ε β (k + 1)]
      ((⋂ j ∈ Finset.range N, G j) ∪
        {ω | ENNReal.ofReal (s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω) <
          confSigma ξ cc D P h p 𝕫 𝕣 δ (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ω} ∪ B) :=
  gm_le_supFilt _ _ (k + 1) _
    (p412i_Ak_aeSigma h38 hγ hγ2 hD hh ξ cc p hEDet 𝕫 hℓ𝕣 hε hε1 hβ hδ k N G hG hB)

end LQGMetric.GM
