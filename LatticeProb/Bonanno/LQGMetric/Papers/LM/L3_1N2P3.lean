/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1N2P3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P2

/-!
# LM Lemma 3.1 with `N = 2`: locality at one scale and the past metrics (task P2-LM31N2)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 3.3, l. 631–637.

* `n2_condIndep_scale` (LM l. 632–633): for every open `V`,
  `n2Sig r V ⟂ (σ(h), n2Sig r (ℂ∖V̄)) | (h − h_r(0))|_V`, from LM Def 1.5 (joint locality of
  `e^{−ξh_r(0)} D_n` for `h − h_r(0)`) by weak union (`DFGPS.L219.condIndepEv_transfer`), using
  `σ(h) ⊆ σ((h − h_r(0))|_V) ∨ σ((h − h_r(0))|_{ℂ∖V})` (`LocGermSplit`, LM l. 534).
* `n2_condIndep_past` (LM l. 635–636, "the conditional law of `(h − h_r(0))|_{B_{sr}(0)}` given
  `𝓕_r` depends only on `(h − h_r(0))|_{ℂ∖B_r(0)}`"): the metric data `n2Past i` of the annuli
  `A_0, …, A_{i−1}` is conditionally independent of `h` given `𝓕_{r_k}` (`i ≤ k`), by induction
  on `i` with the contraction property (`condIndepEv_contraction`).
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

/-- the annulus `A_k = A_{s₁r_k, s₂r_k}(0)` -/
def n2Ann (s₁ s₂ : ℝ) (r : ℕ → ℝ) (k : ℕ) : TopologicalSpace.Opens ℂ :=
  annulus 0 (s₁ * r k) (s₂ * r k)

/-- the metric data of the annuli `A_0, …, A_{i−1}` -/
def n2Past (ξ : ℝ) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (s₁ s₂ : ℝ) (r : ℕ → ℝ) :
    ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | i + 1 => n2Past ξ h D₁ D₂ s₁ s₂ r i ⊔ n2Sig ξ h D₁ D₂ (r i) (n2Ann s₁ s₂ r i)

lemma n2Past_le {ξ : ℝ} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric} (hh : Measurable h)
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂) (s₁ s₂ : ℝ) (r : ℕ → ℝ) :
    ∀ i, n2Past ξ h D₁ D₂ s₁ s₂ r i ≤ mΩ
  | 0 => bot_le
  | i + 1 => sup_le (n2Past_le hh hD₁ hD₂ s₁ s₂ r i) (n2Sig_le hh hD₁ hD₂ _ _)

lemma n2Past_mono (ξ : ℝ) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (s₁ s₂ : ℝ) (r : ℕ → ℝ) :
    Monotone (n2Past ξ h D₁ D₂ s₁ s₂ r) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

/-- LM l. 731–733 (geometry): `A_i ∩ cl A_j = ∅` for `i < j`. -/
lemma n2Ann_subset {s₁ s₂ : ℝ} (hs₂ : s₂ < 1) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k)
    (hrA : Antitone r) (hrs : ∀ k, r (k + 1) / r k ≤ s₁) {i j : ℕ} (hij : i < j) :
    (n2Ann s₁ s₂ r i : Set ℂ) ⊆ (closure (n2Ann s₁ s₂ r j : Set ℂ))ᶜ := by
  have hcl : closure (n2Ann s₁ s₂ r j : Set ℂ) ⊆ closedBall 0 (s₂ * r j) := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    have := hx.2; simp only [sub_zero] at this
    simp only [mem_closedBall, dist_zero_right]; exact this.le
  intro x hx hxc
  have h1 := hx.1; simp only [sub_zero] at h1
  have h2 := hcl hxc; simp only [mem_closedBall, dist_zero_right] at h2
  have h3 : r (i + 1) ≤ s₁ * r i := (div_le_iff₀ (hr0 i)).1 (hrs i)
  have h4 : r j ≤ r (i + 1) := hrA hij
  have h5 : s₂ * r j < r j := by nlinarith [hr0 j]
  linarith

/-- the past metric data at scale `j` is outside `cl A_j`, up to null events -/
lemma n2Past_le_out {ξ : ℝ} {P : Measure Ω} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hlen : ∀ᵐ ω ∂P, (D₁ ω).IsLength ∧ (D₂ ω).IsLength) {s₁ s₂ : ℝ} (hs₂ : s₂ < 1)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) (hrs : ∀ k, r (k + 1) / r k ≤ s₁)
    (j : ℕ) : ∀ i, i ≤ j → n2Past ξ h D₁ D₂ s₁ s₂ r i ≤
      aeClosure P (MeasurableSpace.comap h inferInstance ⊔
        n2Sig ξ h D₁ D₂ (r j) (closure (n2Ann s₁ s₂ r j : Set ℂ))ᶜ)
  | 0, _ => bot_le
  | i + 1, hi => sup_le (n2Past_le_out hD₁ hD₂ hlen hs₂ hr0 hrA hrs j i (by omega))
      (n2Sig_le_nest hD₁ hD₂ hlen _ _ (n2Ann s₁ s₂ r i).isOpen isClosed_closure.isOpen_compl
        (n2Ann_subset hs₂ hr0 hrA hrs (by omega)))

lemma lmFiltration_le_aeClosure_h {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) (k : ℕ) :
    (lmFiltration P hh hr0 hrA k : MeasurableSpace Ω) ≤
      aeClosure P (MeasurableSpace.comap h inferInstance) := by
  rintro s ⟨-, t, ht, hst⟩
  have h1 : lmF h (r k) ≤ MeasurableSpace.comap h inferInstance :=
    (fieldSigmaClosed_le_comapH _ _).trans
      (@measurable_recentre Ω (MeasurableSpace.comap h inferInstance) h
        (comap_measurable h) (r k)).comap_le
  exact ⟨t, h1 t ht, hst⟩

end LQGMetric.LM
