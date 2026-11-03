/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.CondIndepEv at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Conditional
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G3SchemeCI

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Conditional independence of σ-algebras, event form

`LQGMetric.CondIndepEv G A B μ` says that for all `a ∈ A`, `b ∈ B`,
`P[a ∩ b | G] = P[a | G] P[b | G]` a.s. This is mathlib's `CondIndep G A B` written out
(`ProbabilityTheory.condIndep_iff`), without mathlib's standing assumption
`StandardBorelSpace Ω` (mathlib defines `CondIndep` through the regular conditional kernel
`condExpKernel`). The bridge is `LQGMetric.condIndep_iff_condIndepEv`. QuantumZipper's
`QZ.Thm18Asm.CondIndepCE` is the same notion for random variables
(`LQGMetric.condIndepEv_comap_iff`).

Main results:
* `LQGMetric.condExp_sup_eq_of_condIndepEv`: if `A ⟂ B | G` then `P[b | A ∨ G] = P[b | G]`
  for `b ∈ B` (the Markov form of conditional independence; standard, e.g. Kallenberg,
  *Foundations of Modern Probability*, Prop. 6.6 (not supplied; cited for the statement only).
* `LQGMetric.condIndepEv_of_condExp_sup_eq`: the converse.
* `LQGMetric.condIndepEv_bot_iff_indep`: conditioning on the trivial σ-algebra is independence.

Proofs: own elementary arguments (set integrals of conditional expectations, the π–λ theorem
via mathlib's `induction_on_inter`, as in `LQGMetric.condExp_sup_indep_eq`).
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditional independence of the σ-algebras `A` and `B` given `G`, event form:
`P[a ∩ b | G] = P[a | G] · P[b | G]` a.s. for all `a ∈ A`, `b ∈ B`. -/
def CondIndepEv (G A B : MeasurableSpace Ω) (μ : Measure[mΩ] Ω) : Prop :=
  ∀ a b, MeasurableSet[A] a → MeasurableSet[B] b → μ⟦a ∩ b | G⟧ =ᵐ[μ] μ⟦a | G⟧ * μ⟦b | G⟧

lemma CondIndepEv.symm {G A B : MeasurableSpace Ω} (h : CondIndepEv G A B μ) :
    CondIndepEv G B A μ := by
  intro b a hb ha
  filter_upwards [h a b ha hb] with x hx
  rw [inter_comm]
  simp only [Pi.mul_apply] at hx ⊢
  rw [hx, mul_comm]

lemma CondIndepEv.mono {G A B A' B' : MeasurableSpace Ω} (h : CondIndepEv G A B μ)
    (hA : A' ≤ A) (hB : B' ≤ B) : CondIndepEv G A' B' μ :=
  fun a b ha hb => h a b (hA a ha) (hB b hb)

/-- Bridge to mathlib's `CondIndep` (which needs a standard Borel sample space). -/
theorem condIndep_iff_condIndepEv [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {G A B : MeasurableSpace Ω} (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) :
    CondIndep G A B hG μ ↔ CondIndepEv G A B μ :=
  condIndep_iff G A B hG hA hB μ

lemma integrable_indOne [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (s.indicator fun _ => (1 : ℝ)) μ :=
  (integrable_const 1).indicator hs

lemma indOne_mul_eq {s : Set Ω} (f : Ω → ℝ) :
    (s.indicator fun _ => (1 : ℝ)) * f = s.indicator f := by
  funext x; by_cases hx : x ∈ s <;> simp [hx]

lemma integrable_indOne_mul {s : Set Ω} (hs : MeasurableSet s) {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable ((s.indicator fun _ => (1 : ℝ)) * f) μ := by
  rw [indOne_mul_eq]; exact hf.indicator hs

lemma indOne_inter_eq (a b : Set Ω) :
    (a ∩ b).indicator (fun _ => (1 : ℝ)) =
      (a.indicator fun _ => (1 : ℝ)) * (b.indicator fun _ => (1 : ℝ)) := by
  funext x; by_cases hxa : x ∈ a <;> by_cases hxb : x ∈ b <;> simp [hxa, hxb]

/-- Conditional probabilities are bounded by one. -/
lemma norm_condExp_indOne_le [IsProbabilityMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {s : Set Ω} (hs : MeasurableSet[mΩ] s) : ∀ᵐ x ∂μ, ‖(μ⟦s | G⟧) x‖ ≤ 1 := by
  filter_upwards [QuantumZipper.Thm18Asm.condExp_indicator_one_mem_Icc (P := μ) hG hs] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

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

/-- **Markov form of conditional independence.** If `A ⟂ B | G`, then for `b ∈ B`,
`P[b | A ∨ G] = P[b | G]` a.s. -/
theorem condExp_sup_eq_of_condIndepEv [IsProbabilityMeasure μ] {G A B : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (h : CondIndepEv G A B μ) {b : Set Ω}
    (hb : MeasurableSet[B] b) : μ⟦b | A ⊔ G⟧ =ᵐ[μ] μ⟦b | G⟧ := by
  have hsup : A ⊔ G ≤ mΩ := sup_le hA hG
  have hb0 := hB b hb
  refine (ae_eq_condExp_of_isPiSystem hsup QuantumZipper.Thm18Asm.sup_eq_generateFrom_interPi
    QuantumZipper.Thm18Asm.isPiSystem_interPi (integrable_indOne hb0) integrable_condExp
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

/-- **Conditional independence from the Markov form.** If `P[a | B ∨ G] = P[a | G]` for all
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

end LQGMetric
