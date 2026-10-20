/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/CondIndepEv.lean.
Source: QuantumZipper/Proofs/Thm18/G3SchemeCI.lean.
Source: QuantumZipper/Proofs/Thm18/G3Core.lean.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional

/-!
# Conditional independence of σ-algebras, event form

`LatticeProb.CondIndepEv G A B μ` says that for all `a ∈ A` and `b ∈ B`,
`P[a ∩ b | G] = P[a | G] P[b | G]` almost surely. This is mathlib's `CondIndep G A B` written out
(`ProbabilityTheory.condIndep_iff`), without mathlib's standing assumption `StandardBorelSpace Ω`,
which mathlib uses to define `CondIndep` through the regular conditional kernel `condExpKernel`.

Bridges to mathlib's vocabulary:
* `LatticeProb.condIndep_iff_condIndepEv`: `CondIndepEv` is mathlib's `CondIndep` (needs a standard
  Borel sample space).
* `LatticeProb.condIndepEv_comap_iff`: for two random variables, `CondIndepEv` on the σ-algebras
  they generate is mathlib's `CondIndepFun` (needs a standard Borel sample space).

Main results:
* `LatticeProb.condExp_sup_eq_of_condIndepEv`: if `A ⟂ B | G`, then `P[b | A ⊔ G] = P[b | G]`
  almost surely for `b ∈ B` (the Markov form of conditional independence).
* `LatticeProb.condIndepEv_of_condExp_sup_eq`: the converse.
* `LatticeProb.condIndepEv_top`: conditioning on the full σ-algebra makes any two sub-σ-algebras
  conditionally independent; it is used for the nonvacuity examples.

The proofs are elementary: set integrals of conditional expectations, and the π–λ theorem through
mathlib's `induction_on_inter`.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditional independence of the σ-algebras `A` and `B` given `G`, in event form:
`P[a ∩ b | G] = P[a | G] · P[b | G]` almost surely, for all `a ∈ A` and `b ∈ B`. -/
def CondIndepEv (G A B : MeasurableSpace Ω) (μ : Measure[mΩ] Ω) : Prop :=
  ∀ a b, MeasurableSet[A] a → MeasurableSet[B] b → μ⟦a ∩ b | G⟧ =ᵐ[μ] μ⟦a | G⟧ * μ⟦b | G⟧

/-- Conditional independence is symmetric in the two σ-algebras. -/
lemma CondIndepEv.symm {G A B : MeasurableSpace Ω} (h : CondIndepEv G A B μ) :
    CondIndepEv G B A μ := by
  intro b a hb ha
  filter_upwards [h a b ha hb] with x hx
  rw [inter_comm]
  simp only [Pi.mul_apply] at hx ⊢
  rw [hx, mul_comm]

/-- Conditional independence passes to smaller σ-algebras. -/
lemma CondIndepEv.mono {G A B A' B' : MeasurableSpace Ω} (h : CondIndepEv G A B μ)
    (hA : A' ≤ A) (hB : B' ≤ B) : CondIndepEv G A' B' μ :=
  fun a b ha hb => h a b (hA a ha) (hB b hb)

/-- Bridge to mathlib's `CondIndep`, which needs a standard Borel sample space. -/
theorem condIndep_iff_condIndepEv [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {G A B : MeasurableSpace Ω} (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) :
    CondIndep G A B hG μ ↔ CondIndepEv G A B μ :=
  condIndep_iff G A B hG hA hB μ

/-- Bridge to mathlib's `CondIndepFun`: for random variables `X` and `Y`, conditional independence
of the σ-algebras they generate, in event form, is conditional independence of the functions.
Needs a standard Borel sample space, as mathlib's `CondIndepFun` does. -/
theorem condIndepEv_comap_iff [StandardBorelSpace Ω] [IsFiniteMeasure μ] {G : MeasurableSpace Ω}
    (hG : G ≤ mΩ) {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {X : Ω → β}
    {Y : Ω → γ} (hX : Measurable[mΩ] X) (hY : Measurable[mΩ] Y) :
    CondIndepEv G (mβ.comap X) (mγ.comap Y) μ ↔ CondIndepFun G hG X Y μ := by
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
  constructor
  · intro h s t hs ht
    exact h (X ⁻¹' s) (Y ⁻¹' t) (measurableSet_comap.2 ⟨s, hs, rfl⟩)
      (measurableSet_comap.2 ⟨t, ht, rfl⟩)
  · intro h a b ha hb
    obtain ⟨s, hs, rfl⟩ := measurableSet_comap.1 ha
    obtain ⟨t, ht, rfl⟩ := measurableSet_comap.1 hb
    exact h s t hs ht

/-- The π-system `{a ∩ o : a ∈ 𝒜, o ∈ 𝒪}`, which generates `𝒜 ⊔ 𝒪`. -/
def interPi (𝒜 𝒪 : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a o, MeasurableSet[𝒜] a ∧ MeasurableSet[𝒪] o ∧ s = a ∩ o}

/-- The sets `a ∩ o` with `a ∈ 𝒜` and `o ∈ 𝒪` form a π-system. -/
theorem isPiSystem_interPi {𝒜 𝒪 : MeasurableSpace Ω} : IsPiSystem (interPi 𝒜 𝒪) := by
  rintro _ ⟨a, o, ha, ho, rfl⟩ _ ⟨a', o', ha', ho', rfl⟩ -
  exact ⟨a ∩ a', o ∩ o', ha.inter ha', ho.inter ho', by ext; simp; tauto⟩

/-- The π-system `{a ∩ o : a ∈ 𝒜, o ∈ 𝒪}` generates the σ-algebra `𝒜 ⊔ 𝒪`. -/
theorem sup_eq_generateFrom_interPi {𝒜 𝒪 : MeasurableSpace Ω} :
    𝒜 ⊔ 𝒪 = generateFrom (interPi 𝒜 𝒪) := by
  apply le_antisymm
  · refine sup_le (fun a ha => ?_) (fun o ho => ?_)
    · exact measurableSet_generateFrom ⟨a, univ, ha, MeasurableSet.univ, (inter_univ a).symm⟩
    · exact measurableSet_generateFrom ⟨univ, o, MeasurableSet.univ, ho, (univ_inter o).symm⟩
  · refine generateFrom_le ?_
    rintro _ ⟨a, o, ha, ho, rfl⟩
    exact (le_sup_left (a := 𝒜) (b := 𝒪) a ha).inter (le_sup_right (a := 𝒜) (b := 𝒪) o ho)

/-- Conditional probabilities lie in `[0, 1]` almost surely. -/
theorem condExp_indicator_one_mem_Icc {P : Measure Ω} [IsProbabilityMeasure P]
    {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[mΩ] A) :
    ∀ᵐ ω ∂P, P[A.indicator (fun _ => (1 : ℝ)) | G] ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have h0 : 0 ≤ᵐ[P] P[A.indicator (fun _ => (1 : ℝ)) | G] :=
    condExp_nonneg (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h1 : P[A.indicator (fun _ => (1 : ℝ)) | G] ≤ᵐ[P] P[(fun _ => (1 : ℝ)) | G] :=
    condExp_mono hint (integrable_const _)
      (Eventually.of_forall fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω)
  rw [condExp_const hG] at h1
  filter_upwards [h0, h1] with ω a b using ⟨a, b⟩

/-- Conditional probabilities are bounded by one. -/
lemma norm_condExp_indOne_le [IsProbabilityMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {s : Set Ω} (hs : MeasurableSet[mΩ] s) : ∀ᵐ x ∂μ, ‖(μ⟦s | G⟧) x‖ ≤ 1 := by
  filter_upwards [condExp_indicator_one_mem_Icc (P := μ) hG hs] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- The indicator of a measurable set is integrable for a finite measure. -/
lemma integrable_indOne [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (s.indicator fun _ => (1 : ℝ)) μ :=
  (integrable_const 1).indicator hs

/-- Multiplying the indicator of `s` by `f` gives the indicator of `f` restricted to `s`. -/
lemma indOne_mul_eq {s : Set Ω} (f : Ω → ℝ) :
    (s.indicator fun _ => (1 : ℝ)) * f = s.indicator f := by
  funext x; by_cases hx : x ∈ s <;> simp [hx]

/-- The product of an indicator with an integrable function is integrable. -/
lemma integrable_indOne_mul {s : Set Ω} (hs : MeasurableSet s) {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable ((s.indicator fun _ => (1 : ℝ)) * f) μ := by
  rw [indOne_mul_eq]; exact hf.indicator hs

/-- The indicator of an intersection is the product of the indicators. -/
lemma indOne_inter_eq (a b : Set Ω) :
    (a ∩ b).indicator (fun _ => (1 : ℝ)) =
      (a.indicator fun _ => (1 : ℝ)) * (b.indicator fun _ => (1 : ℝ)) := by
  funext x; by_cases hxa : x ∈ a <;> by_cases hxb : x ∈ b <;> simp [hxa, hxb]

/-- Pull-out on a set integral: `∫_{g ∩ a} Z = ∫_g P[a | G] Z` for `G`-measurable `Z`. -/
lemma setIntegral_inter_eq_condExp_mul [IsFiniteMeasure μ] {G : MeasurableSpace Ω}
    (hG : G ≤ mΩ) {a g : Set Ω} (ha : MeasurableSet[mΩ] a) (hg : MeasurableSet[G] g) {Z : Ω → ℝ}
    (hZm : StronglyMeasurable[G] Z) (hZi : Integrable Z μ) :
    ∫ x in g ∩ a, Z x ∂μ = ∫ x in g, (μ⟦a | G⟧) x * Z x ∂μ := by
  have hint := integrable_indOne_mul (μ := μ) ha hZi
  calc ∫ x in g ∩ a, Z x ∂μ
      = ∫ x in g, ((a.indicator fun _ => (1 : ℝ)) * Z) x ∂μ := by
        rw [← setIntegral_indicator ha, indOne_mul_eq]
    _ = ∫ x in g, μ[(a.indicator fun _ => (1 : ℝ)) * Z | G] x ∂μ :=
        (setIntegral_condExp hG hint hg).symm
    _ = ∫ x in g, (μ⟦a | G⟧) x * Z x ∂μ :=
        setIntegral_congr_ae (hG g hg)
          ((condExp_mul_of_aestronglyMeasurable_right hZm.aestronglyMeasurable hint
            (integrable_indOne ha)).mono fun x hx _ => by rw [hx]; rfl)

/-- Identification of a conditional expectation by set integrals over a generating π-system. -/
lemma ae_eq_condExp_of_isPiSystem [IsFiniteMeasure μ] {H : MeasurableSpace Ω} (hH : H ≤ mΩ)
    {p : Set (Set Ω)} (hgen : H = generateFrom p) (hp : IsPiSystem p) {f Z : Ω → ℝ}
    (hf : Integrable f μ) (hZi : Integrable Z μ) (hZm : StronglyMeasurable[H] Z)
    (huniv : ∫ x, Z x ∂μ = ∫ x, f x ∂μ)
    (hbasic : ∀ s ∈ p, ∫ x in s, Z x ∂μ = ∫ x in s, f x ∂μ) : Z =ᵐ[μ] μ[f | H] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hH hf (fun s _ _ => hZi.integrableOn) ?_
    hZm.aestronglyMeasurable
  intro S hS _
  refine induction_on_inter (C := fun S _ => ∫ x in S, Z x ∂μ = ∫ x in S, f x ∂μ) hgen hp
    (by simp) hbasic ?_ ?_ S hS
  · intro t htm ht
    have ht0 : MeasurableSet[mΩ] t := hH t htm
    have e1 := integral_add_compl ht0 hZi
    have e2 := integral_add_compl ht0 hf
    linarith
  · intro s hd hsm hs
    have hs0 : ∀ i, MeasurableSet[mΩ] (s i) := fun i => hH _ (hsm i)
    rw [integral_iUnion hs0 hd hZi.integrableOn, integral_iUnion hs0 hd hf.integrableOn]
    exact tsum_congr hs

/-- Conditioning on the full σ-algebra: any two sub-σ-algebras are conditionally independent
given `mΩ`, because the conditional probabilities are then indicators. -/
lemma condIndepEv_top [IsProbabilityMeasure μ] {A B : MeasurableSpace Ω} (hA : A ≤ mΩ)
    (hB : B ≤ mΩ) : CondIndepEv mΩ A B μ := by
  have key : ∀ s : Set Ω, MeasurableSet[mΩ] s → μ⟦s | mΩ⟧ = s.indicator fun _ => (1 : ℝ) :=
    fun s hs => condExp_of_stronglyMeasurable le_rfl (stronglyMeasurable_const.indicator hs)
      (integrable_indOne hs)
  intro a b ha hb
  have ha0 : MeasurableSet[mΩ] a := hA a ha
  have hb0 : MeasurableSet[mΩ] b := hB b hb
  rw [key _ (ha0.inter hb0), key _ ha0, key _ hb0, indOne_inter_eq]

/-- **Markov form of conditional independence.** If `A ⟂ B | G`, then for `b ∈ B`,
`P[b | A ⊔ G] = P[b | G]` almost surely. -/
theorem condExp_sup_eq_of_condIndepEv [IsProbabilityMeasure μ] {G A B : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (h : CondIndepEv G A B μ) {b : Set Ω}
    (hb : MeasurableSet[B] b) : μ⟦b | A ⊔ G⟧ =ᵐ[μ] μ⟦b | G⟧ := by
  have hsup : A ⊔ G ≤ mΩ := sup_le hA hG
  have hb0 := hB b hb
  refine (ae_eq_condExp_of_isPiSystem hsup sup_eq_generateFrom_interPi
    isPiSystem_interPi (integrable_indOne hb0) integrable_condExp
    (stronglyMeasurable_condExp.mono le_sup_right) (integral_condExp hG) ?_).symm
  rintro _ ⟨a, g, ha, hg, rfl⟩
  have ha0 := hA a ha
  have hg0 := hG g hg
  rw [inter_comm a g, setIntegral_inter_eq_condExp_mul hG ha0 hg stronglyMeasurable_condExp
    integrable_condExp]
  calc ∫ x in g, (μ⟦a | G⟧) x * (μ⟦b | G⟧) x ∂μ = ∫ x in g, (μ⟦a ∩ b | G⟧) x ∂μ :=
        setIntegral_congr_ae hg0 ((h a b ha hb).mono fun x hx _ => hx.symm)
    _ = ∫ x in g, (a ∩ b).indicator (fun _ => (1 : ℝ)) x ∂μ :=
        setIntegral_condExp hG (integrable_indOne (ha0.inter hb0)) hg
    _ = ∫ x in g ∩ a, b.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [setIntegral_indicator (ha0.inter hb0), setIntegral_indicator hb0, inter_assoc]

/-- **Conditional independence from the Markov form.** If `P[a | B ⊔ G] = P[a | G]` for all
`a ∈ A`, then `A ⟂ B | G`. -/
theorem condIndepEv_of_condExp_sup_eq [IsProbabilityMeasure μ] {G A B : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : ∀ a, MeasurableSet[A] a → μ⟦a | B ⊔ G⟧ =ᵐ[μ] μ⟦a | G⟧) : CondIndepEv G A B μ := by
  intro a b ha hb
  have ha0 := hA a ha
  have hb0 := hB b hb
  have hsup : B ⊔ G ≤ mΩ := sup_le hB hG
  have hbm : StronglyMeasurable[B ⊔ G] (b.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator (le_sup_left (a := B) (b := G) b hb)
  have h1 : μ[(b.indicator fun _ => (1 : ℝ)) * (a.indicator fun _ => (1 : ℝ)) | B ⊔ G]
      =ᵐ[μ] (b.indicator fun _ => (1 : ℝ)) * μ⟦a | B ⊔ G⟧ :=
    condExp_mul_of_aestronglyMeasurable_left hbm.aestronglyMeasurable
      (integrable_indOne_mul hb0 (integrable_indOne ha0)) (integrable_indOne ha0)
  calc μ⟦a ∩ b | G⟧
      =ᵐ[μ] μ[μ[(b.indicator fun _ => (1 : ℝ)) * (a.indicator fun _ => (1 : ℝ)) | B ⊔ G] | G] := by
        rw [inter_comm, indOne_inter_eq]
        exact (condExp_condExp_of_le le_sup_right hsup).symm
    _ =ᵐ[μ] μ[(b.indicator fun _ => (1 : ℝ)) * μ⟦a | B ⊔ G⟧ | G] := condExp_congr_ae h1
    _ =ᵐ[μ] μ[(b.indicator fun _ => (1 : ℝ)) * μ⟦a | G⟧ | G] :=
        condExp_congr_ae (by filter_upwards [h a ha] with x hx; simp [hx])
    _ =ᵐ[μ] μ⟦b | G⟧ * μ⟦a | G⟧ :=
        condExp_mul_of_aestronglyMeasurable_right stronglyMeasurable_condExp.aestronglyMeasurable
          (integrable_indOne_mul hb0 integrable_condExp) (integrable_indOne hb0)
    _ =ᵐ[μ] μ⟦a | G⟧ * μ⟦b | G⟧ := Eventually.of_forall fun x => by simp [mul_comm]

namespace CondIndepEvExample

-- Nonvacuity: with `G = mΩ`, the hypothesis of `condExp_sup_eq_of_condIndepEv` holds for every
-- probability measure and every pair of sub-σ-algebras, so the Markov form applies.
example [IsProbabilityMeasure μ] {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    {b : Set Ω} (hb : MeasurableSet[B] b) : μ⟦b | A ⊔ mΩ⟧ =ᵐ[μ] μ⟦b | mΩ⟧ :=
  condExp_sup_eq_of_condIndepEv le_rfl hA hB (condIndepEv_top hA hB) hb

-- Nonvacuity: the converse, with `G = mΩ`, where the Markov hypothesis is an equality of
-- conditional expectations on the same σ-algebra.
example [IsProbabilityMeasure μ] {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ) :
    CondIndepEv mΩ A B μ :=
  condIndepEv_of_condExp_sup_eq le_rfl hA hB fun a _ => by rw [sup_eq_right.2 hB]

-- Nonvacuity with a trivial conditioning σ-algebra: the coordinate σ-algebras of a product of two
-- probability measures are independent, hence conditionally independent given `⊥`.
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α) (ν' : Measure β)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    CondIndepEv ⊥ (MeasurableSpace.comap Prod.fst inferInstance)
      (MeasurableSpace.comap Prod.snd inferInstance) (ν.prod ν') := by
  have hind : IndepFun (Prod.fst : α × β → α) (Prod.snd : α × β → β) (ν.prod ν') :=
    indepFun_prod (X := fun x : α => x) (Y := fun y : β => y) measurable_id measurable_id
  intro a b ha hb
  obtain ⟨s, hs, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ha
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hb
  have hA : MeasurableSet (Prod.fst ⁻¹' s : Set (α × β)) := measurable_fst hs
  have hB : MeasurableSet (Prod.snd ⁻¹' t : Set (α × β)) := measurable_snd ht
  refine Eventually.of_forall fun x => ?_
  simp only [condExp_bot, Pi.mul_apply, integral_indicator_const (1 : ℝ) (hA.inter hB),
    integral_indicator_const (1 : ℝ) hA, integral_indicator_const (1 : ℝ) hB, measureReal_def,
    hind.measure_inter_preimage_eq_mul s t hs ht, ENNReal.toReal_mul, smul_eq_mul, mul_one]

end CondIndepEvExample

end LatticeProb
