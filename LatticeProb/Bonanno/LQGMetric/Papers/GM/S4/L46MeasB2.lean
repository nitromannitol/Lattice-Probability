/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasB2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46Meas
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4

/-!
# GM Lemma 4.6 (a), unconditional (task P2-E3b)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6 and its proof, l. 1701–1706 ("we find that `{(z,r) ∈ 𝒵_k}` is determined by
`h|_{ℂ∖B_r(z)}`"), in the form `gm_L4_7_pair` consumes.

* `gm_uMeasurableSet_candEvD`: on the Borel set `lenSet` of boundedly compact length metrics the
  event `(z,r) ∈ 𝒵_k` is universally measurable (D30): the exit time is Borel (`gmTauB`), the
  complement of the filled ball is analytic (`gm_uMeasurableSet_notMem_filledBall`) and the
  distance to its frontier is the distance to the metric ball (`gm_infDist_frontier_filledBall`).
* `gm_aeEventIn_of_local`: the glue of `gm_L4_6a` (Axiom II on `U_n = B_{1/(n+1)}(ℂ∖B_ρ(z))`,
  Lusin separation for null-measurable sets `LocalEvent.ae_preimage_eq_of_saturated_null`,
  `gm_aeEventIn_fieldSigmaClosed`) for an arbitrary event `B` of the metric which is invariant
  under changes of the metric not affecting the internal metric of open sets `U ⊇ ℂ∖B_ρ(z)`, and
  universally measurable on `L`. Used for L4.6 (a) here and for L4.6 (b) (`Stab`).
* `gm_L4_6a_uncond`: GM Lemma 4.6 (a) from `DFGPSLem3_8` only (through `ae_mem_lenSet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint TopologicalSpace

namespace LQGMetric.GM
open LocalEvent

/-- **the event `(z,r) ∈ 𝒵_k` is universally measurable on `lenSet`** -/
theorem gm_uMeasurableSet_candEvD (𝕫 : ℂ) (R c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) (z : ℂ)
    (r : ℝ) : UMeasurableSet (lenSet ∩ {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r}) := by
  set Q : Set (ContMetric × ℝ) :=
    {_p | z ∈ gridPts (lam1 * ε ^ (1 + ν) * 𝕣 / 4) ∧ r ∈ Rads} ∩
      ({p | z ∉ filledBall p.1 𝕫 p.2} ∩
        {p | infDist z (ballM p.1 𝕫 p.2) ∈ Icc (lam4 * ε * 𝕣) (2 * lam4 * ε * 𝕣)})
  have hQ : UMeasurableSet Q :=
    (UMeasurableSet.of_measurableSet (MeasurableSet.const _)).inter
      ((gm_uMeasurableSet_notMem_filledBall 𝕫 z).inter
        (UMeasurableSet.of_measurableSet (gm_measurable_infDist_ballM 𝕫 z measurableSet_Icc)))
  have hg : Measurable fun d : ContMetric => (d, gmTauB 𝕫 R d * c) :=
    measurable_id.prodMk ((gm_measurable_tauB 𝕫 R).mul_const c)
  have e : lenSet ∩ {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r} =
      lenSet ∩ (fun d : ContMetric => (d, gmTauB 𝕫 R d * c)) ⁻¹' Q := by
    ext d
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    refine and_congr_right fun hd => ?_
    have hbd : Bornology.IsBounded (ballM d 𝕫 (gmTauB 𝕫 R d * c)) :=
      (gm_isCompact_closure_ballM hd 𝕫 _).isBounded.subset subset_closure
    unfold candEvD
    rw [gm_tauD_eq_tauB hd]
    show (z ∈ _ ∧ z ∉ _ ∧ r ∈ Rads ∧ _) ↔ ((z ∈ _ ∧ r ∈ Rads) ∧ (z ∉ _ ∧ _))
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨h1, h3⟩, h2, ?_⟩
      show infDist z (ballM d 𝕫 (gmTauB 𝕫 R d * c)) ∈ Icc (lam4 * ε * 𝕣) (2 * lam4 * ε * 𝕣)
      rwa [← gm_infDist_frontier_filledBall hbd h2]
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      have h4' : infDist z (ballM d 𝕫 (gmTauB 𝕫 R d * c)) ∈ Icc (lam4 * ε * 𝕣) (2 * lam4 * ε * 𝕣) := h4
      exact ⟨h1, h2, h3, by rwa [gm_infDist_frontier_filledBall hbd h2]⟩
  rw [e]
  exact (UMeasurableSet.of_measurableSet measurableSet_lenSet).inter (hQ.preimage hg)

/-- **local events of the metric are local events of the field** (glue of GM Lemma 4.6):
an event `B` of the metric, universally measurable on a Borel set `L` of length metrics carrying
the law of `D_h`, and invariant under changes of the metric that keep the internal metric of
some open `U ⊇ ℂ ∖ B_ρ(z)`, is a.s. an event of `σ(h|_{ℂ∖B_ρ(z)})`. -/
theorem gm_aeEventIn_of_local {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) (L : Set ContMetric)
    (hLm : MeasurableSet L) (hLlen : ∀ d ∈ L, d.IsLength) (hLae : ∀ᵐ ω ∂P, D (h ω) ∈ L)
    (z : ℂ) (ρ : ℝ) (B : Set ContMetric) (hB : UMeasurableSet (L ∩ B))
    (hsat : ∀ d₁ ∈ L, ∀ d₂ ∈ L, ∀ U : Set ℂ, IsOpen U → (Metric.ball z ρ)ᶜ ⊆ U →
      (∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y) → d₁ ∈ B → d₂ ∈ B) :
    AEEventIn P (fieldSigmaClosed h (Metric.ball z ρ)ᶜ) (h ⁻¹' (D ⁻¹' B)) := by
  have hBL : h ⁻¹' (D ⁻¹' B) =ᵐ[P] h ⁻¹' (D ⁻¹' (L ∩ B)) := by
    filter_upwards [hLae] with ω hω
    exact propext ⟨fun hb => ⟨hω, hb⟩, fun hb => hb.2⟩
  suffices H : AEEventIn P (fieldSigmaClosed h (Metric.ball z ρ)ᶜ) (h ⁻¹' (D ⁻¹' (L ∩ B))) by
    obtain ⟨F, hF, hFe⟩ := H
    exact ⟨F, hF, hBL.trans hFe⟩
  have hBn : NullMeasurableSet (D ⁻¹' (L ∩ B)) (P.map h) :=
    (hB.preimage hD.measurable).nullMeasurableSet _
  refine gm_aeEventIn_fieldSigmaClosed h _ fun n => ?_
  set U := nbhdO (1 / ((n : ℝ) + 1)) (Metric.ball z ρ)ᶜ with hUdef
  have hUρ : (Metric.ball z ρ)ᶜ ⊆ (U : Set ℂ) := self_subset_thickening (by positivity) _
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hh U
  obtain ⟨x₀, hx₀⟩ := gm_compl_ball_nonempty z ρ
  have : Nonempty U := ⟨⟨x₀, hUρ hx₀⟩⟩
  let q : ℕ → ℂ := fun i => (denseSeq U i : ℂ)
  have hqU : ∀ i, q i ∈ (U : Set ℂ) := fun i => (denseSeq U i).2
  let R₀ : DistOn U → (ℕ × ℕ → ℝ≥0∞) := fun x p => Φ x (q p.1) (q p.2)
  have hR₀ : Measurable R₀ := measurable_pi_iff.2 fun p : ℕ × ℕ =>
    (measurable_pi_apply (q p.2)).comp ((measurable_pi_apply (q p.1)).comp hΦ)
  have hR : Measurable (R₀ ∘ restrictTo U) := hR₀.comp (measurable_restrictTo U)
  set W : Set DistC := D ⁻¹' L ∩ ⋂ i, ⋂ j,
    {g | (D g).chainInf U (q i) (q j) = Φ (restrictTo U g) (q i) (q j)} with hWdef
  have hWm' : MeasurableSet (⋂ i, ⋂ j,
      {g : DistC | (D g).chainInf U (q i) (q j) = Φ (restrictTo U g) (q i) (q j)}) := by
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_eq_fun ?_ ?_
    · exact (ContMetric.measurable_chainInf (U : Set ℂ)).comp
        (hD.measurable.prodMk (measurable_const (a := (q i, q j))))
    · exact (measurable_pi_apply (q j)).comp ((measurable_pi_apply (q i)).comp
        (hΦ.comp (measurable_restrictTo U)))
  have hWm : MeasurableSet W := (hD.measurable hLm).inter hWm'
  have hYW : ∀ᵐ ω ∂P, h ω ∈ W := by
    filter_upwards [hLae, hΦae] with ω h1 h2
    refine ⟨h1, mem_iInter.2 fun i => mem_iInter.2 fun j => ?_⟩
    show (D (h ω)).chainInf U (q i) (q j) = Φ (restrictTo U (h ω)) (q i) (q j)
    rw [← ContMetric.internal_eq_chainInf _ (hLlen _ h1) U.isOpen]
    exact h2 _ (hqU i) _ (hqU j)
  have hclos : ∀ x ∈ (U : Set ℂ), x ∈ closure (range q) := by
    intro x hx
    have hd : (⟨x, hx⟩ : U) ∈ closure (range (denseSeq U)) := by
      rw [(denseRange_denseSeq U).closure_eq]; exact mem_univ _
    exact map_mem_closure continuous_subtype_val hd (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
  have hsat' : ∀ g₁ ∈ W, ∀ g₂ ∈ W, (R₀ ∘ restrictTo U) g₁ = (R₀ ∘ restrictTo U) g₂ →
      g₁ ∈ D ⁻¹' (L ∩ B) → g₂ ∈ D ⁻¹' (L ∩ B) := by
    intro g₁ hg₁ g₂ hg₂ hRe hB₁
    have hl₁ := hLlen _ hg₁.1
    have hl₂ := hLlen _ hg₂.1
    have hval : ∀ g ∈ W, ∀ i j, (D g).internal U (q i) (q j) = Φ (restrictTo U g) (q i) (q j) := by
      intro g hg i j
      rw [ContMetric.internal_eq_chainInf _ (hLlen _ hg.1) U.isOpen]
      exact mem_iInter.1 (mem_iInter.1 hg.2 i) j
    have hEq : EqOn (fun p : ℂ × ℂ => (D g₁).internal U p.1 p.2)
        (fun p : ℂ × ℂ => (D g₂).internal U p.1 p.2) ((U : Set ℂ) ×ˢ (U : Set ℂ)) := by
      refine EqOn.of_subset_closure (s := range q ×ˢ range q) ?_
        ((D g₁).continuousOn_internal hl₁ U.isOpen) ((D g₂).continuousOn_internal hl₂ U.isOpen)
        ?_ ?_
      · rintro ⟨_, _⟩ ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
        show (D g₁).internal U (q i) (q j) = (D g₂).internal U (q i) (q j)
        rw [hval g₁ hg₁, hval g₂ hg₂]
        exact congrFun hRe (i, j)
      · rintro ⟨_, _⟩ ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
        exact ⟨hqU i, hqU j⟩
      · rw [closure_prod_eq]
        exact prod_mono (fun x hx => hclos x hx) (fun x hx => hclos x hx)
    exact ⟨hg₂.1, hsat _ hg₁.1 _ hg₂.1 U U.isOpen hUρ
      (fun x hx y hy => hEq (mk_mem_prod hx hy)) hB₁.2⟩
  obtain ⟨S, hS, hae⟩ := LocalEvent.ae_preimage_eq_of_saturated_null (Y := h) hh.1 hR hWm hBn
    hYW hsat'
  exact ⟨_, ⟨R₀ ⁻¹' S, hR₀ hS, rfl⟩, hae⟩

end LQGMetric.GM
