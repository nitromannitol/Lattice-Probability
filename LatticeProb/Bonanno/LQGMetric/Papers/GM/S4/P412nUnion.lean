/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412nUnion at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110C
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iCond

/-!
# GM (4.40′) at one stopping time from the on-event form of CONF Lemma 3.6 (D110 P6, part 1)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3, l. 2164–2180 (CONF
L3.6 = GM L2.14 at the centres `z_y`); CONF L3.6 (C:1308–1320) in the form
`CONF.CONFLem3_6AtAENE` (DEC-110 §3, S3D110C.lean).

* `p412n_condExp_union_compl`: a conditional lower bound `P[G | F] ≥ 1 − c` on an `F`-event `E`
  gives `P[G ∪ Eᶜ | F] ≥ 1 − c` a.s. (own elementary glue);
* `p412n_union_k`: the proof of `p412m_union_k` (P412mStep.lean) for a field normalized at `ψ₀`
  with `CONFLem3_6AtAENE`; the union bound holds for
  `(⋂_j G_j) ∪ {supp ψ₀ ⊄ int 𝓑^•_τ}`. Since D114 the `G_j` are a.s. events of
  `σ(𝓑^•_{σ}, h|)` (`AEEventIn`, the D114 form of CONF L3.6), with the constant `ε = δ`
  (countably valued).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- a conditional lower bound on an `F`-event `E` extends to `G ∪ Eᶜ` everywhere -/
theorem p412n_condExp_union_compl {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : MeasurableSpace Ω} (hF : F ≤ m0) {E G : Set Ω}
    (hE : MeasurableSet[F] E) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1)
    (h : ∀ᵐ x ∂μ, x ∈ E → 1 - c ≤ μ[G.indicator (fun _ => (1 : ℝ)) | F] x) :
    ∀ᵐ x ∂μ, 1 - c ≤ μ[(G ∪ Eᶜ).indicator (fun _ => (1 : ℝ)) | F] x := by
  have hEm : MeasurableSet[m0] E := hF _ hE
  by_cases hE0 : μ E = 0
  · have hae : (G ∪ Eᶜ).indicator (fun _ => (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with x hx
      exact indicator_of_mem (show x ∈ G ∪ Eᶜ from Or.inr hx) _
    filter_upwards [condExp_congr_ae (m := F) hae] with x hx
    rw [hx, condExp_const hF]
    linarith
  · have hGn : @NullMeasurableSet Ω m0 G μ := by
      by_contra hn
      have hni : ¬ Integrable (G.indicator (fun _ => (1 : ℝ))) μ := fun hi =>
        hn ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hi.aestronglyMeasurable.aemeasurable)
      rw [condExp_of_not_integrable hni] at h
      refine hE0 (measure_eq_zero_iff_ae_notMem.2 ?_)
      filter_upwards [h] with x hx hxE
      have := hx hxE
      simp only [Pi.zero_apply] at this
      linarith
    have hiG : Integrable (G.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator₀ hGn
    have hi1 : Integrable (E.indicator (G.indicator (fun _ => (1 : ℝ)))) μ := hiG.indicator hEm
    have hi2 : Integrable (Eᶜ.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hEm.compl
    have e : (G ∪ Eᶜ).indicator (fun _ => (1 : ℝ)) =
        E.indicator (G.indicator (fun _ => (1 : ℝ))) + Eᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ E
      · by_cases hg : x ∈ G
        · rw [Pi.add_apply, indicator_of_mem (show x ∈ G ∪ Eᶜ from Or.inl hg),
            indicator_of_mem hx, indicator_of_mem hg,
            indicator_of_notMem (show x ∉ Eᶜ from not_not.2 hx), add_zero]
        · rw [Pi.add_apply, indicator_of_notMem (show x ∉ G ∪ Eᶜ from
            fun h' => h'.elim hg fun h'' => h'' hx),
            indicator_of_mem hx, indicator_of_notMem hg,
            indicator_of_notMem (show x ∉ Eᶜ from not_not.2 hx), add_zero]
      · rw [Pi.add_apply, indicator_of_mem (show x ∈ G ∪ Eᶜ from Or.inr hx),
          indicator_of_notMem hx, indicator_of_mem (show x ∈ Eᶜ from hx), zero_add]
    have h2 : μ[Eᶜ.indicator (fun _ => (1 : ℝ)) | F] = Eᶜ.indicator (fun _ => (1 : ℝ)) :=
      condExp_of_stronglyMeasurable hF (stronglyMeasurable_const.indicator hE.compl) hi2
    rw [e]
    filter_upwards [condExp_add hi1 hi2 F, condExp_indicator hiG hE, h] with x hx1 hx2 hx3
    rw [hx1, Pi.add_apply, hx2, h2]
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, indicator_of_notMem (show x ∉ Eᶜ from not_not.2 hx), add_zero]
      exact hx3 hx
    · rw [indicator_of_notMem hx, indicator_of_mem (show x ∈ Eᶜ from hx), zero_add]
      linarith

/-- `⋂_{j<N} (G_j ∪ B) = (⋂_{j<N} G_j) ∪ B` -/
theorem p412n_iInter_union {Ω : Type*} (G : ℕ → Set Ω) (B : Set Ω) (N : ℕ) :
    (⋂ j ∈ Finset.range N, (G j ∪ B)) = (⋂ j ∈ Finset.range N, G j) ∪ B := by
  ext x
  simp only [mem_iInter, mem_union, Finset.mem_range]
  by_cases hx : x ∈ B
  · simp [hx]
  · simp [hx]

/-- **GM (4.40′)** at one stopping time (l. 2164–2180), from `CONFLem3_6AtAENE` (D110), for a
field normalized at `ψ₀`: the union bound holds for `(⋂_j G_j) ∪ {supp ψ₀ ⊄ int 𝓑^•_τ}` -/
theorem p412n_union_k {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (H36 : CONF.CONFLem3_6AtAENE γ D c p) :
    ∃ α C₀ : ℝ, 0 < α ∧ 1 < C₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTime D h z₀ τ →
      ∀ ψ₀ : TestC, (∫ x, ψ₀ x = 1) → (∀ ω, h ω ψ₀ = 0) →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ ‹MeasurableSpace Ω› →
      ∀ δ ∈ Ioo (0 : ℝ) 1, C₀ * δ ^ α < 1 →
      ∀ (N : ℕ) (x : ℕ → Ω → ℂ),
      (∀ j, @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ (x j)) →
      (∀ᵐ ω ∂P, ∀ j, x j ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) →
      ∃ G : ℕ → Set Ω,
        (∀ j, AEEventIn P (filledBallSigmaAt D h z₀
          (fun ω => confSigma (xiGamma γ) c D P h p z₀ R δ (τ ω) ω)) (G j)) ∧
        (∀ j, ∀ ω ∈ G j, x j ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
          confRK (xiGamma γ) c D P h p R δ (filledBall (D (h ω)) z₀ (τ ω)) ω ≤
            Metric.ediam (filledBall (D (h ω)) z₀ (τ ω)) →
          ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
            y ∉ enbhd (confRK (xiGamma γ) c D P h p R δ (filledBall (D (h ω)) z₀ (τ ω)) ω)
              (filledBall (D (h ω)) z₀ (τ ω)) →
            IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L,
              Q u ∉ Metric.ball (x j ω) (δ * R) \ filledBall (D (h ω)) z₀ (τ ω)) ∧
        ∀ᵐ ω ∂P, 1 - N * (C₀ * δ ^ α) ≤
          (P[((⋂ j ∈ Finset.range N, G j) ∪
              {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (filledBall (D (h ω)) z₀ (τ ω))}ᶜ).indicator
              (fun _ => (1 : ℝ)) |
            localSigma h (fun ω => filledBall (D (h ω)) z₀ (τ ω))]) ω := by
  obtain ⟨α, C₀, hα, hC₀, H⟩ := H36
  refine ⟨α, C₀, hα, hC₀, ?_⟩
  intro Ω _ P _ h hh z₀ R hR τ hτ ψ₀ hψ₀ h0 hdet hm δ hδ hδc N x hxm hxf
  have hG := fun j => H P h hh z₀ R hR τ hτ ψ₀ hψ₀ h0 hdet hm (x j) (fun _ => δ) (hxm j)
    measurable_const (hxf.mono fun ω hω => hω j) (fun _ => hδ)
    ((Set.countable_singleton δ).mono Set.range_const_subset)
  choose G hGm hGA hGc using hG
  refine ⟨G, hGm, hGA, ?_⟩
  set E := {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (filledBall (D (h ω)) z₀ (τ ω))} with hEdef
  have hEs : MeasurableSet[setSigma (fun ω => filledBall (D (h ω)) z₀ (τ ω))] E :=
    CONF.confD110_setSigma_supp_subset_interior (fun ω => gm_filledBall_isClosed _ _ _)
      ψ₀.hasCompactSupport.isCompact
  have hE : MeasurableSet[localSigma h (fun ω => filledBall (D (h ω)) z₀ (τ ω))] E :=
    CONF.localSigma0_le_localSigma h _ _
      (CONF.confD110_setSigma_le_localSigma0 h _ _ hEs)
  have hc0 : 0 ≤ C₀ * δ ^ α := by
    have := Real.rpow_pos_of_pos hδ.1 α
    positivity
  have hG' : ∀ j, ∀ᵐ ω ∂P, 1 - C₀ * δ ^ α ≤
      (P[(G j ∪ Eᶜ).indicator (fun _ => (1 : ℝ)) |
        localSigma h (fun ω => filledBall (D (h ω)) z₀ (τ ω))]) ω :=
    fun j => p412n_condExp_union_compl hm hE hc0 hδc (hGc j)
  have hF := p412f_condExp_iInter hm N (fun j => G j ∪ Eᶜ)
    (fun j => p412f_nullMeas_of_condExp hδc (hG' j)) (fun j _ => hG' j)
  rwa [p412n_iInter_union] at hF

end LQGMetric.GM
