/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.CondIndepDetermined at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepEv
import LatticeProb.Bonanno.LQGMetric.Prob.EfronStein

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# "Determined by" for σ-algebras: two-copies criterion, removing an independent variable,
# and GM Lemma 4.9

`LQGMetric.AEDeterminedSigma A G μ`: every event of `A` agrees a.s. with an event of `G`
("`A` is a.s. determined by `G`", i.e. `A ⊆ G ∨ {null sets}`). For `A = σ(Y)`, `G = σ(X)` this
is the event form of "Y is a.s. determined by X" (GM_B M2; FOUNDATIONS §9a; the bridge to
`AEDeterminedBy` for standard Borel targets is not done here).

* `LQGMetric.aeDeterminedSigma_of_condIndepEv_of_ae_eq` (**LM S5.d**, two-copies criterion):
  if `X` and `Y` are conditionally independent given `G` and `X = Y` a.s., then `σ(X)` is a.s.
  determined by `G`. Used in Gwynne–Miller, *Local metrics of the Gaussian free field*,
  arXiv:1905.00379, proof of Lemma 5.3 (`local-metrics-final.tex` lines 956–986: two
  conditionally independent samples of `D` given the data agree, so `D` is determined by the
  data). The equality of the conditional laws of `X` and `Y` is not needed (it follows from
  `X = Y` a.s.). Own elementary proof: `p = P[X ∈ B | G]` satisfies `p = p²`.
* `LQGMetric.aeDeterminedSigma_of_indep_of_sup` (**LM S5.c**, tex line 1087: "Since `(h, D)` is
  independent from `θ`, a.s. `D(·,·;V)` is determined by `h`"): if `𝓗 ∨ 𝒜 ⟂ Θ` and `𝒜` is a.s.
  determined by `𝓗 ∨ Θ`, then `𝒜` is a.s. determined by `𝓗`. Proof: `1_a = P[a | Θ ∨ 𝓗] =
  P[a | 𝓗]` by `LQGMetric.condExp_sup_indep_eq`.
* `LQGMetric.condExp_inter_le_of_sup_singleton` (**GM.L4.9**, Gwynne–Miller, *Existence and
  uniqueness of the LQG metric*, arXiv:1905.00383, Lemma 4.9 = `lem-cond-expectation`,
  `uniqueness-final.tex` lines 1839–1880), with the hypothesis `F ∩ E ∈ 𝒢 ∨ σ(E)` relaxed to
  "up to a null set" (as GM Lemma 4.6 provides it; blueprint GM_B.md line 129). Own shorter
  proof: GM compute `P[H ∩ E | 𝒢 ∨ σ(E)]` by a ratio formula and then condition on `𝓕`; we test
  directly against `F ∈ 𝓕`, using `F ∩ E = g ∩ E` a.s. with `g ∈ 𝒢`, which is the step GM's
  proof of (4.21) also uses.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `A` is a.s. determined by `G`: every event of `A` is a.s. equal to an event of `G`. -/
def AEDeterminedSigma (A G : MeasurableSpace Ω) (μ : Measure[mΩ] Ω) : Prop :=
  ∀ s, MeasurableSet[A] s → ∃ t, MeasurableSet[G] t ∧ s =ᵐ[μ] t

lemma indOne_ae_eq_of_ae_eq {s t : Set Ω} (h : s =ᵐ[μ] t) :
    (s.indicator fun _ => (1 : ℝ)) =ᵐ[μ] t.indicator fun _ => (1 : ℝ) :=
  indicator_ae_eq_of_ae_eq_set h

/-- If `P[s | G] = 1_t` a.s. with `t ∈ G`, then `s = t` a.s. -/
lemma ae_eq_set_of_condExp_eq_indOne [IsFiniteMeasure μ] {G : MeasurableSpace Ω}
    (hG : G ≤ mΩ) {s t : Set Ω} (hs : MeasurableSet[mΩ] s) (ht : MeasurableSet[G] t)
    (h : μ⟦s | G⟧ =ᵐ[μ] t.indicator fun _ => (1 : ℝ)) : s =ᵐ[μ] t := by
  have ht0 := hG t ht
  have key : ∀ u, MeasurableSet[G] u → μ.real (u ∩ s) = μ.real (u ∩ t) := by
    intro u hu
    have e := setIntegral_condExp hG (integrable_indOne (μ := μ) hs) hu
    rw [setIntegral_congr_ae (hG u hu) (h.mono fun x hx _ => hx), setIntegral_indicator ht0,
      setIntegral_indicator hs, setIntegral_const, setIntegral_const] at e
    simpa using e.symm
  have h1 := key t ht
  have h2 := key tᶜ ht.compl
  rw [compl_inter_self, measureReal_empty] at h2
  rw [inter_self] at h1
  rw [ae_eq_set]
  constructor
  · have e : s \ t = tᶜ ∩ s := by ext; simp [and_comm]
    rw [e]
    exact (measureReal_eq_zero_iff).1 h2
  · have e := measureReal_inter_add_sdiff (μ := μ) (s := t) hs
    rw [h1] at e
    exact (measureReal_eq_zero_iff).1 (by linarith)

/-- **LM S5.d, core.** If `s = s'` a.s. and `s, s'` are conditionally independent given `G`,
then `s` is a.s. equal to an event of `G`. -/
lemma exists_ae_eq_set_of_condIndep_self [IsProbabilityMeasure μ] {G : MeasurableSpace Ω}
    (hG : G ≤ mΩ) {s s' : Set Ω} (hs : MeasurableSet[mΩ] s)
    (hss' : s =ᵐ[μ] s') (h : μ⟦s ∩ s' | G⟧ =ᵐ[μ] μ⟦s | G⟧ * μ⟦s' | G⟧) :
    ∃ t, MeasurableSet[G] t ∧ s =ᵐ[μ] t := by
  set p := μ⟦s | G⟧ with hp
  have hq : μ⟦s' | G⟧ =ᵐ[μ] p := condExp_congr_ae (indOne_ae_eq_of_ae_eq hss'.symm)
  have hr : μ⟦s ∩ s' | G⟧ =ᵐ[μ] p := by
    refine condExp_congr_ae (indOne_ae_eq_of_ae_eq ?_)
    have := EventuallyEqSet.inter (EventuallyEq.refl _ s) hss'.symm
    rwa [inter_self] at this
  have hpp : ∀ᵐ x ∂μ, p x = p x * p x := by
    filter_upwards [hr, h, hq] with x h1 h2 h3
    have e := h1.symm.trans h2
    rw [Pi.mul_apply, h3] at e
    exact e
  refine ⟨p ⁻¹' {1}, stronglyMeasurable_condExp.measurable (measurableSet_singleton 1), ?_⟩
  refine ae_eq_set_of_condExp_eq_indOne hG hs
    (stronglyMeasurable_condExp.measurable (measurableSet_singleton 1)) ?_
  filter_upwards [hpp] with x hx
  have h01 : p x = 0 ∨ p x = 1 := by
    have : p x * (p x - 1) = 0 := by linear_combination -hx
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases h01 with h0 | h1
  · have : x ∉ p ⁻¹' {1} := by simp [h0]
    rw [indicator_of_notMem this]; exact h0
  · have : x ∈ p ⁻¹' {1} := by simp [h1]
    rw [indicator_of_mem this]; exact h1

/-- **LM S5.d** (two-copies criterion). If `X` and `Y` are conditionally independent given `G`
and `X = Y` a.s., then `σ(X)` is a.s. determined by `G`. -/
theorem aeDeterminedSigma_of_condIndepEv_of_ae_eq [IsProbabilityMeasure μ] {β : Type*}
    [mβ : MeasurableSpace β] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {X Y : Ω → β}
    (hX : Measurable[mΩ] X) (hXY : CondIndepEv G (mβ.comap X) (mβ.comap Y) μ)
    (heq : X =ᵐ[μ] Y) : AEDeterminedSigma (mβ.comap X) G μ := by
  rintro _ ⟨B, hB, rfl⟩
  refine exists_ae_eq_set_of_condIndep_self hG (hX hB) ?_ (hXY _ _ ⟨B, hB, rfl⟩
    ⟨B, hB, rfl⟩)
  rw [eventuallyEqSet_iff]
  filter_upwards [heq] with x hx
  simp [hx]

/-- Events of `G ∨ σ(E)` agree with an event of `G` on `E`. -/
lemma exists_inter_eq_of_measurableSet_sup_singleton {G : MeasurableSpace Ω} {E t : Set Ω}
    (ht : MeasurableSet[G ⊔ generateFrom {E}] t) :
    ∃ g, MeasurableSet[G] g ∧ t ∩ E = g ∩ E := by
  let M : MeasurableSpace Ω :=
    { MeasurableSet' := fun t => ∃ g, MeasurableSet[G] g ∧ t ∩ E = g ∩ E
      measurableSet_empty := ⟨∅, MeasurableSet.empty, by simp⟩
      measurableSet_compl := by
        rintro t ⟨g, hg, h⟩
        refine ⟨gᶜ, hg.compl, ?_⟩
        ext x
        have hx := Set.ext_iff.1 h x
        simp only [mem_inter_iff, mem_compl_iff] at hx ⊢
        tauto
      measurableSet_iUnion := by
        intro f hf
        choose g hg hgE using hf
        exact ⟨⋃ i, g i, MeasurableSet.iUnion hg, by simp only [iUnion_inter, hgE]⟩ }
  have hle : G ⊔ generateFrom {E} ≤ M := by
    refine sup_le (fun g hg => ⟨g, hg, rfl⟩) (generateFrom_le ?_)
    rintro s hs
    rw [mem_singleton_iff] at hs
    subst hs
    exact ⟨univ, MeasurableSet.univ, by simp⟩
  exact hle t ht

/-- `∫_u f · 1_{G₀} = ∫_{u ∩ G₀} f`. -/
lemma setIntegral_mul_indOne {G₀ u : Set Ω} (hG₀ : MeasurableSet[mΩ] G₀) (f : Ω → ℝ) :
    ∫ x in u, f x * G₀.indicator (fun _ => (1 : ℝ)) x ∂μ = ∫ x in u ∩ G₀, f x ∂μ := by
  have e : (fun x => f x * G₀.indicator (fun _ => (1 : ℝ)) x) = G₀.indicator f := by
    funext x; by_cases hx : x ∈ G₀ <;> simp [hx]
  rw [e, setIntegral_indicator hG₀]

/-- `∫_u P[H ∩ E | K] 1_{G₀} = P[u ∩ G₀ ∩ H ∩ E]` for `u, G₀ ∈ K`. -/
lemma setIntegral_condExp_mul_indOne [IsFiniteMeasure μ] {K : MeasurableSpace Ω} (hK : K ≤ mΩ)
    {u G₀ S : Set Ω} (hu : MeasurableSet[K] u) (hG₀ : MeasurableSet[K] G₀)
    (hS : MeasurableSet[mΩ] S) :
    ∫ x in u, (μ⟦S | K⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real (u ∩ G₀ ∩ S) := by
  rw [setIntegral_mul_indOne (hK _ hG₀), setIntegral_condExp hK (integrable_indOne hS)
    (hu.inter hG₀), setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]

lemma integrable_condExp_mul_indOne [IsFiniteMeasure μ] {K : MeasurableSpace Ω}
    {G₀ S : Set Ω} (hG₀ : MeasurableSet[mΩ] G₀) :
    Integrable (fun x => (μ⟦S | K⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x) μ := by
  have e : (fun x => (μ⟦S | K⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x) =
      G₀.indicator (μ⟦S | K⟧) := by
    funext x; by_cases hx : x ∈ G₀ <;> simp [hx]
  rw [e]; exact integrable_condExp.indicator hG₀

/-- **GM Lemma 4.9** (`lem-cond-expectation`). Let `𝓕, 𝒢` be sub-σ-algebras and `E` an event such
that for each `F ∈ 𝓕`, `F ∩ E` agrees a.s. with an event of `𝒢 ∨ σ(E)`. Let `G₀ ∈ 𝓕 ∩ 𝒢`, let
`H₁, H₂` be events and `Λ > 0`. If a.s. `P[H₁ ∩ E | 𝒢] 1_{G₀} ≤ Λ P[H₂ ∩ E | 𝒢] 1_{G₀}`, then a.s.
`P[H₁ ∩ E | 𝓕] 1_{G₀} ≤ Λ P[H₂ ∩ E | 𝓕] 1_{G₀}`. -/
theorem condExp_inter_le_of_sup_singleton [IsProbabilityMeasure μ] {F G : MeasurableSpace Ω}
    (hF : F ≤ mΩ) (hG : G ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[mΩ] E)
    (hFE : ∀ F', MeasurableSet[F] F' →
      ∃ t, MeasurableSet[G ⊔ generateFrom {E}] t ∧ F' ∩ E =ᵐ[μ] t)
    {G₀ : Set Ω} (hG₀F : MeasurableSet[F] G₀) (hG₀G : MeasurableSet[G] G₀)
    {H₁ H₂ : Set Ω} (hH₁ : MeasurableSet[mΩ] H₁) (hH₂ : MeasurableSet[mΩ] H₂) {Λ : ℝ}
    (_hΛ : 0 < Λ)
    (h : ∀ᵐ x ∂μ, (μ⟦H₁ ∩ E | G⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((μ⟦H₂ ∩ E | G⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x)) :
    ∀ᵐ x ∂μ, (μ⟦H₁ ∩ E | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((μ⟦H₂ ∩ E | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x) := by
  have hG₀ := hG G₀ hG₀G
  -- the measure inequality on each `F' ∈ 𝓕`
  have key : ∀ F', MeasurableSet[F] F' →
      μ.real (F' ∩ G₀ ∩ (H₁ ∩ E)) ≤ Λ * μ.real (F' ∩ G₀ ∩ (H₂ ∩ E)) := by
    intro F' hF'
    obtain ⟨t, ht, hFt⟩ := hFE F' hF'
    obtain ⟨g, hg, htg⟩ := exists_inter_eq_of_measurableSet_sup_singleton ht
    have hFg : F' ∩ E =ᵐ[μ] g ∩ E := by
      have := EventuallyEqSet.inter hFt (EventuallyEq.refl _ E)
      rwa [inter_assoc, inter_self, htg] at this
    have hrepl : ∀ H : Set Ω, μ.real (F' ∩ G₀ ∩ (H ∩ E)) = μ.real (g ∩ G₀ ∩ (H ∩ E)) := by
      intro H
      have e1 : F' ∩ G₀ ∩ (H ∩ E) = (F' ∩ E) ∩ (G₀ ∩ H) := by ext; simp; tauto
      have e2 : g ∩ G₀ ∩ (H ∩ E) = (g ∩ E) ∩ (G₀ ∩ H) := by ext; simp; tauto
      rw [e1, e2, measureReal_def, measureReal_def,
        measure_congr (EventuallyEqSet.inter hFg (EventuallyEq.rfl : G₀ ∩ H =ᵐ[μ] G₀ ∩ H))]
    rw [hrepl, hrepl, ← setIntegral_condExp_mul_indOne hG hg hG₀G (hH₁.inter hE),
      ← setIntegral_condExp_mul_indOne hG hg hG₀G (hH₂.inter hE), ← integral_const_mul]
    exact setIntegral_mono_ae_restrict (integrable_condExp_mul_indOne hG₀).integrableOn
      ((integrable_condExp_mul_indOne hG₀).const_mul Λ).integrableOn (ae_restrict_of_ae h)
  -- conclude on the trimmed measure
  set f₁ : Ω → ℝ := fun x => (μ⟦H₁ ∩ E | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x with hf₁
  set f₂ : Ω → ℝ := fun x => Λ * ((μ⟦H₂ ∩ E | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x)
    with hf₂
  have hf₁m : StronglyMeasurable[F] f₁ :=
    stronglyMeasurable_condExp.mul (stronglyMeasurable_const.indicator hG₀F)
  have hf₂m : StronglyMeasurable[F] f₂ :=
    stronglyMeasurable_const.mul
      (stronglyMeasurable_condExp.mul (stronglyMeasurable_const.indicator hG₀F))
  have hf₁i : Integrable f₁ μ := integrable_condExp_mul_indOne hG₀
  have hf₂i : Integrable f₂ μ := (integrable_condExp_mul_indOne hG₀).const_mul Λ
  refine ae_le_of_ae_le_trim (hm := hF) (ae_le_of_forall_setIntegral_le (hf₁i.trim hF hf₁m)
    (hf₂i.trim hF hf₂m) fun s hs _ => ?_)
  rw [← setIntegral_trim hF hf₁m hs, ← setIntegral_trim hF hf₂m hs, hf₁, hf₂, integral_const_mul,
    setIntegral_condExp_mul_indOne hF hs hG₀F (hH₁.inter hE),
    setIntegral_condExp_mul_indOne hF hs hG₀F (hH₂.inter hE)]
  exact key s hs

end LQGMetric
