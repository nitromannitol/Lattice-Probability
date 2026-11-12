/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_6Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P5
import LatticeProb.Bonanno.LQGMetric.Field.GermSplitA

/-!
# LM Theorem 1.6, unconditional (task P2-GERM)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 3.1 (l. 573–590, proof l. 723–764), Lemma 3.3 proof
(l. 631–637), and l. 534 ("`h` is determined by `h|_V` and `h|_{U∖V}`").

The chain `n2_condIndep_scale → n2_condIndep_past → n2_condExp_field / n2_condExp_event →
lmN2ScaleInput_of_germ → lmThm1_6_of_germ` of `L3_1N2P3`–`L3_1N2P5` (task P2-LM31N2) uses
`LocGermSplit` only at the bounded annuli `V = A_k`. Here the same chain is restated with the
hypothesis `GermSplit.LocGermSplitBdd` (LM l. 534 for bounded `V`), which is proved
(`GermSplit.locGermSplitBdd`, `Field/GermSplitA.lean`). The proofs are those of P2-LM31N2,
verbatim except for the boundedness argument `isBounded_n2Ann`.

* `lmThm1_6 : Blueprint.LMThm1_6`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

lemma isBounded_n2Ann (s₁ s₂ : ℝ) (r : ℕ → ℝ) (k : ℕ) :
    Bornology.IsBounded (n2Ann s₁ s₂ r k : Set ℂ) :=
  (isBounded_ball (x := (0 : ℂ)) (r := s₂ * r k)).subset fun _ hw => mem_ball_iff_norm.2 hw.2

/-- `n2_condIndep_scale` for bounded `V`, from `LocGermSplitBdd` -/
theorem n2_condIndep_scale_bdd (hgerm : GermSplit.LocGermSplitBdd) {ξ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) (hX : IsXiAdditive2 ξ P h D₁ D₂) {r : ℝ} (hr : 0 < r)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) :
    CondIndepEv (fieldSigma (recentre h r) V) (n2Sig ξ h D₁ D₂ r V)
      (MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ r (closure (V : Set ℂ))ᶜ) P := by
  obtain ⟨⟨hD₁, hD₂, hlen, -⟩, hloc⟩ := hX
  have J : CondIndepEv (fieldSigma (recentre h r) V)
      (famSigma (normIntFam ξ h D₁ r) V ⊔ famSigma (normIntFam ξ h D₂ r) V)
      (fieldSigmaClosed (recentre h r) (V : Set ℂ)ᶜ ⊔
        famSigma (normIntFam ξ h D₁ r) (closure (V : Set ℂ))ᶜ ⊔
        famSigma (normIntFam ξ h D₂ r) (closure (V : Set ℂ))ᶜ) P := hloc 0 r hr V
  have hXm : Measurable (recentre h r) := measurable_recentre hh.1.measurable r
  have hXg : IsWholePlaneGFF (recentre h r) P :=
    hh.1.addConst ((measurable_circleAvg_left r 0).comp hh.1.measurable).neg
  have hWo : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hlen1 : ∀ᵐ ω ∂P, (D₁ ω).IsLength := hlen.mono fun _ h => h.1
  have hlen2 : ∀ᵐ ω ∂P, (D₂ ω).IsLength := hlen.mono fun _ h => h.2
  have J1 : CondIndepEv (fieldSigma (recentre h r) V) (n2Sig ξ h D₁ D₂ r V)
      (fieldSigmaClosed (recentre h r) (V : Set ℂ)ᶜ ⊔ n2Sig ξ h D₁ D₂ r (closure (V : Set ℂ))ᶜ)
      P := by
    refine GM.Bilip.CondIndepEv.of_le_aeClosure J ?_ ?_
    · exact sup_le_aeClosure (n2Chain_le_famSigma hlen1 V.isOpen)
        (n2Chain_le_famSigma hlen2 V.isOpen)
    · refine sup_le ((le_aeClosure _).trans (aeClosure_mono (le_sup_left.trans le_sup_left))) ?_
      exact (sup_le_aeClosure (n2Chain_le_famSigma hlen1 hWo)
        (n2Chain_le_famSigma hlen2 hWo)).trans
        (aeClosure_mono (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hG : fieldSigma (recentre h r) V ≤ mΩ := ((measurable_restrictTo V).comp hXm).comap_le
  have hS : ∀ W, n2Sig ξ h D₁ D₂ r W ≤ mΩ := n2Sig_le hh.1.measurable hD₁ hD₂ r
  refine condIndepEv_transfer hG (hS _) (sup_le (GM.fieldSigmaClosed_le_gm hXm _) (hS _)) hG J1
    (le_aeClosure _) (le_sup_right.trans (le_aeClosure _)) (le_sup_left.trans (le_aeClosure _))
    (sup_le ?_ ((le_sup_right.trans le_sup_left).trans (le_aeClosure _)))
  refine le_aeClosure_trans (comap_h_le_recentre hh r) ((hgerm P _ hXg V hVb).trans ?_)
  exact aeClosure_mono (sup_le le_sup_right (le_sup_left.trans le_sup_left))

/-- **LM l. 635–636**: the past metric data is conditionally independent of `h` given
`𝓕_{r_k}` (null-augmented field σ-algebra). -/
theorem n2_condIndep_past_bdd (hgerm : GermSplit.LocGermSplitBdd) {ξ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) (hX : IsXiAdditive2 ξ P h D₁ D₂) {s₁ s₂ : ℝ}
    (hs₁ : s₁ ≤ 1) (hs₂ : s₂ < 1) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r)
    (hrs : ∀ k, r (k + 1) / r k ≤ s₁) (k : ℕ) :
    ∀ i, i ≤ k → CondIndepEv (lmFiltration P hh.1 hr0 hrA k) (MeasurableSpace.comap h inferInstance)
      (n2Past ξ h D₁ D₂ s₁ s₂ r i) P
  | 0, _ => condIndepEv_of_le_cond ((lmFiltration P hh.1 hr0 hrA).le k)
      hh.1.measurable.comap_le bot_le
  | i + 1, hi => by
    obtain ⟨hD₁, hD₂, hlen, -⟩ := hX.1
    have hL := (lmFiltration P hh.1 hr0 hrA).le k
    have hH : MeasurableSpace.comap h inferInstance ≤ mΩ := hh.1.measurable.comap_le
    have hS : ∀ ρ W, n2Sig ξ h D₁ D₂ ρ W ≤ mΩ := n2Sig_le hh.1.measurable hD₁ hD₂
    have hPi := n2Past_le hh.1.measurable hD₁ hD₂ s₁ s₂ r (ξ := ξ) i
    have IH := n2_condIndep_past_bdd hgerm hh hX hs₁ hs₂ hr0 hrA hrs k i (by omega)
    have CI := n2_condIndep_scale_bdd hgerm hh hX (hr0 i) (n2Ann s₁ s₂ r i) (isBounded_n2Ann s₁ s₂ r i)
    have hΦ : fieldSigma (recentre h (r i)) (n2Ann s₁ s₂ r i) ≤ lmFiltration P hh.1 hr0 hrA k :=
      (annSigma_le_lmFiltration hh.1 hr0 hrA hs₁ hrs i).trans
        ((lmFiltration P hh.1 hr0 hrA).mono (by omega))
    have hΦm : fieldSigma (recentre h (r i)) (n2Ann s₁ s₂ r i) ≤ mΩ :=
      ((measurable_restrictTo _).comp (measurable_recentre hh.1.measurable (r i))).comap_le
    have h2 : CondIndepEv (n2Past ξ h D₁ D₂ s₁ s₂ r i ⊔ lmFiltration P hh.1 hr0 hrA k)
        (n2Sig ξ h D₁ D₂ (r i) (n2Ann s₁ s₂ r i)) (MeasurableSpace.comap h inferInstance) P := by
      refine condIndepEv_transfer hΦm (hS _ _) (sup_le hH (hS _ _)) (sup_le hPi hL) CI
        ((hΦ.trans le_sup_right).trans (le_aeClosure _)) ?_ (le_sup_left.trans (le_aeClosure _))
        ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
      refine sup_le ((n2Past_le_out hD₁ hD₂ hlen hs₂ hr0 hrA hrs i i le_rfl).trans
        (aeClosure_mono le_sup_left)) ?_
      exact (lmFiltration_le_aeClosure_h hh.1 hr0 hrA k).trans
        (aeClosure_mono (le_sup_left.trans le_sup_left))
    exact condIndepEv_contraction hL hH hPi (hS _ _) IH h2.symm

variable {ξ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
  {D₁ D₂ : Ω → ContMetric} {s₁ s₂ : ℝ} {r : ℕ → ℝ}

/-- **Step (ii)** (LM l. 635–636): for `a ∈ σ(h)`, `P[a | ℱ_k] = P[a | 𝓕_{r_k}]`. -/
theorem n2_condExp_field_bdd (hgerm : GermSplit.LocGermSplitBdd) (hh : IsNormalizedWPGFF h P)
    (hX : IsXiAdditive2 ξ P h D₁ D₂) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ < 1) (hr0 : ∀ k, 0 < r k)
    (hrA : Antitone r) (hrs : ∀ k, r (k + 1) / r k ≤ s₁) (k : ℕ) {a : Set Ω}
    (ha : MeasurableSet[MeasurableSpace.comap h inferInstance] a) :
    P⟦a | n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k⟧ =ᵐ[P] P⟦a | lmFiltration P hh.1 hr0 hrA k⟧ := by
  obtain ⟨hD₁, hD₂, -, -⟩ := hX.1
  have CI := n2_condIndep_past_bdd hgerm hh hX hs₁ hs₂ hr0 hrA hrs k k le_rfl
  have hL := (lmFiltration P hh.1 hr0 hrA).le k
  have hH : MeasurableSpace.comap h inferInstance ≤ mΩ := hh.1.measurable.comap_le
  have hPk := n2Past_le hh.1.measurable hD₁ hD₂ s₁ s₂ r (ξ := ξ) k
  have e := condExp_sup_eq_of_condIndepEv hL hPk hH CI.symm ha
  refine condExp_sandwich (lmFiltration_le_n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k)
    ((n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA).le k) (sup_le hPk hL) ?_
    (integrable_indOne (hH a ha)) e
  refine (n2Filt_le_aeClosure P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k).trans (aeClosure_mono ?_)
  exact sup_le ((le_augSigma P (lmF_le' hh.1 _)).trans le_sup_right) le_sup_left

/-- **Step (i)** (LM l. 632–633): for `E ∈ σ((h − h_{r_k}(0))|_{A_k}) ∨ (metrics on A_k)`,
`P[E | ℱ_k] = E[P[E | (h − h_{r_k}(0))|_{A_k}] | ℱ_k]`. -/
theorem n2_condExp_event_bdd (hgerm : GermSplit.LocGermSplitBdd) (hh : IsNormalizedWPGFF h P)
    (hX : IsXiAdditive2 ξ P h D₁ D₂) (hs₂ : s₂ < 1) (hr0 : ∀ k, 0 < r k)
    (hrA : Antitone r) (hrs : ∀ k, r (k + 1) / r k ≤ s₁) (k : ℕ) {E : Set Ω}
    (hE : MeasurableSet[annSigma h s₁ s₂ (r k) ⊔ n2Sig ξ h D₁ D₂ (r k) (n2Ann s₁ s₂ r k)] E) :
    P⟦E | n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k⟧ =ᵐ[P]
      P[P⟦E | annSigma h s₁ s₂ (r k)⟧ | n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k] := by
  obtain ⟨hD₁, hD₂, hlen, -⟩ := hX.1
  have CI : CondIndepEv (annSigma h s₁ s₂ (r k)) (n2Sig ξ h D₁ D₂ (r k) (n2Ann s₁ s₂ r k)) (MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ (r k) (closure (n2Ann s₁ s₂ r k : Set ℂ))ᶜ) P := n2_condIndep_scale_bdd hgerm hh hX (hr0 k) (n2Ann s₁ s₂ r k) (isBounded_n2Ann s₁ s₂ r k)
  have hΦ : (annSigma h s₁ s₂ (r k)) ≤ mΩ :=
    ((measurable_restrictTo _).comp (measurable_recentre hh.1.measurable (r k))).comap_le
  have hS : ∀ ρ W, n2Sig ξ h D₁ D₂ ρ W ≤ mΩ := n2Sig_le hh.1.measurable hD₁ hD₂
  have hH : MeasurableSpace.comap h inferInstance ≤ mΩ := hh.1.measurable.comap_le
  have hB : (MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ (r k) (closure (n2Ann s₁ s₂ r k : Set ℂ))ᶜ) ≤ mΩ := sup_le hH (hS _ _)
  have sup := condIndepEv_sup_cond hΦ (hS _ _) hB CI
  have hE' : MeasurableSet[(n2Sig ξ h D₁ D₂ (r k) (n2Ann s₁ s₂ r k)) ⊔ (annSigma h s₁ s₂ (r k))] E := by rw [sup_comm]; exact hE
  have ce := condExp_sup_eq_of_condIndepEv hΦ (sup_le hB hΦ) (sup_le (hS _ _) hΦ) sup.symm hE'
  have hF := (n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA).le k
  have hFK : (n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k : MeasurableSpace Ω) ≤
      aeClosure P ((MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ (r k) (closure (n2Ann s₁ s₂ r k : Set ℂ))ᶜ) ⊔ (annSigma h s₁ s₂ (r k)) ⊔ (annSigma h s₁ s₂ (r k))) := by
    have h1 : lmF h (r k) ⊔ n2Past ξ h D₁ D₂ s₁ s₂ r k ≤ aeClosure P (MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ (r k) (closure (n2Ann s₁ s₂ r k : Set ℂ))ᶜ) :=
      sup_le (((lmF_le_comap h (r k)).trans le_sup_left).trans (le_aeClosure _))
        (n2Past_le_out hD₁ hD₂ hlen hs₂ hr0 hrA hrs k k le_rfl)
    exact (le_aeClosure_trans (n2Filt_le_aeClosure P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k) h1).trans
      (aeClosure_mono (le_sup_left.trans le_sup_left))
  refine (condExp_tower_aeClosure hF (sup_le (sup_le hB hΦ) hΦ) hFK
    (integrable_indOne ((sup_le (hS _ _) hΦ) E hE'))).trans ?_
  exact condExp_congr_ae ce

/-- The locality input of LM Lemma 3.1 (`N = 2`) from `LocGermSplitBdd` (LM l. 534, bounded `V`) and joint
locality (LM l. 631–637). -/
theorem lmN2ScaleInput_of_germ_bdd (hgerm : GermSplit.LocGermSplitBdd) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) : LMN2ScaleInput s₁ s₂ := by
  intro ξ Ω _ P _ h D₁ D₂ hh hX r E hr0 hrA hE
  obtain ⟨-, -, hrs, hEm⟩ := hE
  obtain ⟨hD₁, hD₂, hlen, -⟩ := hX.1
  have hs₁1 : s₁ ≤ 1 := by linarith
  have hS : ∀ ρ W, n2Sig ξ h D₁ D₂ ρ W ≤ ‹MeasurableSpace Ω› :=
    n2Sig_le hh.1.measurable hD₁ hD₂
  have hΦ : ∀ k, annSigma h s₁ s₂ (r k) ≤ ‹MeasurableSpace Ω› := fun k =>
    ((measurable_restrictTo _).comp (measurable_recentre hh.1.measurable (r k))).comap_le
  have hlen1 : ∀ᵐ ω ∂P, (D₁ ω).IsLength := hlen.mono fun _ h => h.1
  have hlen2 : ∀ᵐ ω ∂P, (D₂ ω).IsLength := hlen.mono fun _ h => h.2
  have hver : ∀ k, ∃ t, MeasurableSet[annSigma h s₁ s₂ (r k) ⊔
      n2Sig ξ h D₁ D₂ (r k) (n2Ann s₁ s₂ r k)] t ∧ E k =ᵐ[P] t := by
    intro k
    have hle : annSigma h s₁ s₂ (r k) ⊔
        famSigma (normIntFam ξ h D₁ (r k)) (annulus 0 (s₁ * r k) (s₂ * r k)) ⊔
        famSigma (normIntFam ξ h D₂ (r k)) (annulus 0 (s₁ * r k) (s₂ * r k)) ≤
        aeClosure P (annSigma h s₁ s₂ (r k) ⊔ n2Sig ξ h D₁ D₂ (r k) (n2Ann s₁ s₂ r k)) := by
      refine sup_le (sup_le (le_sup_left.trans (le_aeClosure _)) ?_) ?_
      · exact (famSigma_normInt_le hlen1 (annulus 0 _ _).isOpen).trans
          (aeClosure_mono (le_sup_left.trans le_sup_right))
      · exact (famSigma_normInt_le hlen2 (annulus 0 _ _).isOpen).trans
          (aeClosure_mono (le_sup_right.trans le_sup_right))
    exact hle _ (hEm k)
  choose E' hE'm hEE' using hver
  have hE'0 : ∀ k, MeasurableSet (E' k) := fun k => (sup_le (hΦ k) (hS _ _)) _ (hE'm k)
  refine ⟨n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA, E',
    lmFiltration_le_n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA, hEE', fun k => ?_, ?_⟩
  · refine ⟨hE'0 k, ?_⟩
    have hle : annSigma h s₁ s₂ (r k) ⊔ n2Sig ξ h D₁ D₂ (r k) (n2Ann s₁ s₂ r k) ≤
        aeClosure P (lmF h (r (k + 1)) ⊔ n2Past ξ h D₁ D₂ s₁ s₂ r (k + 1)) := by
      refine sup_le_aeClosure (fun s hs => ?_) (le_sup_right.trans (le_aeClosure _))
      obtain ⟨-, t, ht, hst⟩ := annSigma_le_lmFiltration hh.1 hr0 hrA hs₁1 hrs k s hs
      exact ⟨t, ht, hst⟩
    exact hle _ (hE'm k)
  intro k η hη0 hη1
  have hfm : Measurable[annSigma h s₁ s₂ (r k)] (P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)]) :=
    stronglyMeasurable_condExp.measurable
  have hf01 : ∀ᵐ ω ∂P, P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω ∈ Icc (0 : ℝ) 1 :=
    QuantumZipper.Thm18Asm.condExp_indicator_one_mem_Icc (hΦ k) (hE'0 k)
  have ha : MeasurableSet[annSigma h s₁ s₂ (r k)]
      {ω | 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω} := measurableSet_le measurable_const hfm
  have ha0 := hΦ k _ ha
  refine ⟨_, ha, ?_, ?_, ?_⟩
  · -- Markov's inequality for `1 − f`
    have hint : ∫ ω, P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω ∂P = P.real (E' k) := by
      rw [integral_condExp (hΦ k), integral_indicator_const _ (hE'0 k)]
      simp
    have hmono : (fun ω => η * {ω | 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω}ᶜ.indicator
        (fun _ => (1 : ℝ)) ω) ≤ᵐ[P] fun ω => 1 - P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω := by
      filter_upwards [hf01] with ω hω
      by_cases hωa : 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω
      · rw [indicator_of_notMem (by simpa using hωa)]; linarith [hω.2]
      · rw [indicator_of_mem (by simpa using hωa)]; push Not at hωa; linarith
    have h1 := integral_mono_ae ((integrable_indOne ha0.compl).const_mul η)
      ((integrable_const (1 : ℝ)).sub (integrable_condExp (f := (E' k).indicator fun _ => (1 : ℝ))
        (m := annSigma h s₁ s₂ (r k)) (μ := P))) hmono
    have e1 : ∫ ω, η * {ω | 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω}ᶜ.indicator (fun _ => (1 : ℝ)) ω ∂P =
        η * (1 - P.real {ω | 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω}) := by
      rw [integral_const_mul, integral_indicator_const _ ha0.compl, measureReal_compl ha0]
      simp
    have e2 : ∫ ω, ((fun _ : Ω => (1 : ℝ)) - P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] : Ω → ℝ) ω ∂P = 1 - P.real (E' k) := by
      simp only [Pi.sub_apply]
      rw [integral_sub (integrable_const _) integrable_condExp, hint]
      simp
    rw [e1, e2] at h1
    linarith
  · refine n2_condExp_field_bdd hgerm hh hX hs₁1 hs₂ hr0 hrA hrs k ?_
    exact ((fieldSigma_le_comapH _ _).trans (@measurable_recentre Ω
      (MeasurableSpace.comap h inferInstance) h (comap_measurable h) (r k)).comap_le) _ ha
  · have hstep := n2_condExp_event_bdd hgerm hh hX hs₂ hr0 hrA hrs k (hE'm k)
    have hle : ((1 - η) • {ω | 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω}.indicator
        (fun _ => (1 : ℝ))) ≤ᵐ[P] P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] := by
      filter_upwards [hf01] with ω hω
      by_cases hωa : 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [indicator_of_mem (by simpa using hωa)]; linarith
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [indicator_of_notMem (by simpa using hωa)]; linarith [hω.1]
    have hm := condExp_mono (m := n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k)
      ((integrable_indOne ha0).smul (1 - η)) integrable_condExp hle
    have hs := condExp_smul (μ := P) (1 - η)
      ({ω | 1 - η ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | annSigma h s₁ s₂ (r k)] ω}.indicator fun _ => (1 : ℝ))
      (n2Filt P ξ D₁ D₂ s₁ s₂ hh.1 hr0 hrA k)
    filter_upwards [hm, hs, hstep] with ω h1 h2 h3
    rw [h3]; rw [h2] at h1; simpa using h1

/-- **LM Lemma 3.1 (1)** with `N = 2`, unconditional. -/
theorem lmLem3_1aN2 : LMLem3_1aN2 :=
  lmLem3_1aN2_of_scale (lmAnnulusIterInputQ_of_canon fun s₁ _ _ => lmNestCanonLeaf s₁)
    fun _ _ h1 h2 h3 => lmN2ScaleInput_of_germ_bdd GermSplit.locGermSplitBdd h1 h2 h3

/-- **LM Theorem 1.6** (`thm-local-metric-bound`), unconditional. -/
theorem lmThm1_6 : LMThm1_6 :=
  lmThm1_6_of_N2 lmLem3_1aN2

end LQGMetric.LM
