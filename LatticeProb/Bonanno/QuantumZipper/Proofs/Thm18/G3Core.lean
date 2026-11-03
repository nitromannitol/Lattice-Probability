/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.G3Core at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# G3 core: independence of a limit from asymptotic conditional independence

Abstract probabilistic core of blueprint node G3 (independence of the two wedges in Theorem 1.8;
Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, last paragraph of the proof of
Theorem 1.8, §5.4, pp. 70–71). The paper's mechanism is:

1. condition on a σ-algebra `𝒢` (field outside two small balls around `x` and `R(x)`, plus
   quantum lengths); by the GFF Markov property the two zoomed surfaces are conditionally
   independent given `𝒢`;
2. by (a generalized) Proposition 5.5, each zoomed surface has a conditional law given `𝒢` close
   to a fixed law (the `γ`-wedge law);
3. hence the pair is asymptotically independent, and in the limit the two sides are independent.

This file proves steps 3 abstractly:

* `abs_real_inter_sub_le_of_condIndep`: if `U, V` are conditionally independent given `𝒢`
  (event form, `CondIndepCE`), then
  `|P(U ∈ s, V ∈ t) − a b| ≤ E|P(U ∈ s | 𝒢) − a| + E|P(V ∈ t | 𝒢) − b|` for `a, b ∈ [0,1]`;
* `indepFun_of_generating_eq_mul`: product formula on generating π-systems for a.e.-measurable
  maps gives `IndepFun`;
* `indepFun_of_asymptotic_condIndep`: the limit statement (steps 1–3 combined).

Conditional independence is taken in its textbook event form (`P[A ∩ B | 𝒢] = P[A | 𝒢] P[B | 𝒢]`
a.s. for `A ∈ σ(U)`, `B ∈ σ(V)`; e.g. Kallenberg, *Foundations of Modern Probability*, 2nd ed.,
Ch. 6, p. 109), stated with `condExp`, so no standard-Borel assumption on the sample space is
needed (mathlib's `CondIndepFun` requires one; the GFF sample spaces are not standard Borel).
Own elementary proofs (standard facts, cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open scoped ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

section Core

variable {Ω α β : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]

/-- Conditional independence of `U` and `V` given the sub-σ-algebra `𝒢`, in event form:
`P[U ∈ s, V ∈ t | 𝒢] = P[U ∈ s | 𝒢] · P[V ∈ t | 𝒢]` a.s., for all measurable `s, t`. -/
def CondIndepCE (𝒢 : MeasurableSpace Ω) (U : Ω → α) (V : Ω → β) (P : Measure[mΩ] Ω) : Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t →
    P[(U ⁻¹' s ∩ V ⁻¹' t).indicator (fun _ => (1 : ℝ)) | 𝒢] =ᵐ[P]
      P[(U ⁻¹' s).indicator (fun _ => (1 : ℝ)) | 𝒢] *
        P[(V ⁻¹' t).indicator (fun _ => (1 : ℝ)) | 𝒢]

/-- Conditional probabilities lie in `[0, 1]` a.e. -/
theorem condExp_indicator_one_mem_Icc {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂P, P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have h0 : 0 ≤ᵐ[P] P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] :=
    condExp_nonneg (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h1 : P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ≤ᵐ[P] P[(fun _ => (1 : ℝ)) | 𝒢] :=
    condExp_mono hint (integrable_const _)
      (Eventually.of_forall fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω)
  rw [condExp_const h𝒢] at h1
  filter_upwards [h0, h1] with ω a b using ⟨a, b⟩

/-- **Decorrelation from conditional independence.** If `U, V` are conditionally independent given
`𝒢` and `a, b ∈ [0, 1]`, then `|P(U ∈ s, V ∈ t) − a b|` is at most the sum of the `L¹` distances
of the two conditional probabilities to `a` and `b`. Own elementary proof. -/
theorem abs_real_inter_sub_le_of_condIndep {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {U : Ω → α} {V : Ω → β} (hU : Measurable U)
    (hV : Measurable V) (hCI : CondIndepCE 𝒢 U V P) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |P.real (U ⁻¹' s ∩ V ⁻¹' t) - a * b| ≤
      (∫ ω, |P[(U ⁻¹' s).indicator (fun _ => (1 : ℝ)) | 𝒢] ω - a| ∂P) +
        ∫ ω, |P[(V ⁻¹' t).indicator (fun _ => (1 : ℝ)) | 𝒢] ω - b| ∂P := by
  set f := P[(U ⁻¹' s).indicator (fun _ => (1 : ℝ)) | 𝒢]
  set g := P[(V ⁻¹' t).indicator (fun _ => (1 : ℝ)) | 𝒢]
  have hA : MeasurableSet (U ⁻¹' s) := hU hs
  have hB : MeasurableSet (V ⁻¹' t) := hV ht
  have hAB : MeasurableSet (U ⁻¹' s ∩ V ⁻¹' t) := hA.inter hB
  have hf : Integrable f P := integrable_condExp
  have hg : Integrable g P := integrable_condExp
  have hreal : P.real (U ⁻¹' s ∩ V ⁻¹' t) = ∫ ω, f ω * g ω ∂P := by
    rw [← integral_indicator_one hAB, ← integral_condExp h𝒢]
    exact integral_congr_ae (hCI s t hs ht)
  have hfI := condExp_indicator_one_mem_Icc (P := P) h𝒢 hA
  have hgI := condExp_indicator_one_mem_Icc (P := P) h𝒢 hB
  have hfa : Integrable (fun ω => |f ω - a|) P := (hf.sub (integrable_const a)).abs
  have hgb : Integrable (fun ω => |g ω - b|) P := (hg.sub (integrable_const b)).abs
  have hpt : ∀ᵐ ω ∂P, |f ω * g ω - a * b| ≤ |f ω - a| + |g ω - b| := by
    filter_upwards [hfI, hgI] with ω h1 h2
    have e : f ω * g ω - a * b = (f ω - a) * g ω + a * (g ω - b) := by ring
    rw [e]
    calc |(f ω - a) * g ω + a * (g ω - b)| ≤ |(f ω - a) * g ω| + |a * (g ω - b)| := abs_add_le _ _
      _ = |f ω - a| * |g ω| + |a| * |g ω - b| := by rw [abs_mul, abs_mul]
      _ ≤ |f ω - a| * 1 + 1 * |g ω - b| := by
          gcongr
          · rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
          · rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
      _ = |f ω - a| + |g ω - b| := by ring
  have hfg : Integrable (fun ω => f ω * g ω) P := by
    refine (integrable_condExp (μ := P) (m := 𝒢)
      (f := (U ⁻¹' s ∩ V ⁻¹' t).indicator (fun _ => (1 : ℝ)))).congr ?_
    exact hCI s t hs ht
  rw [hreal, ← integral_add hfa hgb]
  have : ∫ ω, f ω * g ω ∂P - a * b = ∫ ω, (f ω * g ω - a * b) ∂P := by
    rw [integral_sub hfg (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [this]
  exact (abs_integral_le_integral_abs).trans
    (integral_mono_ae (hfg.sub (integrable_const _)).abs (hfa.add hgb) hpt)

/-- **Independence from a product formula on generating π-systems**, for a.e.-measurable maps. -/
theorem indepFun_of_generating_eq_mul {P : Measure Ω} [IsProbabilityMeasure P]
    {U : Ω → α} {V : Ω → β} (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    {Cα : Set (Set α)} {Cβ : Set (Set β)} (hCα : IsPiSystem Cα) (hCβ : IsPiSystem Cβ)
    (hgα : mα = generateFrom Cα) (hgβ : mβ = generateFrom Cβ)
    (h : ∀ s ∈ Cα, ∀ t ∈ Cβ, P (U ⁻¹' s ∩ V ⁻¹' t) = P (U ⁻¹' s) * P (V ⁻¹' t)) :
    IndepFun U V P := by
  have hU' := hU.ae_eq_mk
  have hV' := hV.ae_eq_mk
  refine IndepFun.congr ?_ hU'.symm hV'.symm
  rw [IndepFun_iff_Indep]
  refine IndepSets.indep hU.measurable_mk.comap_le hV.measurable_mk.comap_le
    (hCα.comap hU.mk) (hCβ.comap hV.mk) ?_ ?_ ?_
  · have key : ∀ u : Ω → α, MeasurableSpace.comap u mα =
        generateFrom {s | ∃ t ∈ Cα, u ⁻¹' t = s} := fun u => by
      rw [hgα, comap_generateFrom]; rfl
    exact key _
  · have key : ∀ u : Ω → β, MeasurableSpace.comap u mβ =
        generateFrom {s | ∃ t ∈ Cβ, u ⁻¹' t = s} := fun u => by
      rw [hgβ, comap_generateFrom]; rfl
    exact key _
  · rw [IndepSets_iff]
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have e1 : (hU.mk ⁻¹' s : Set Ω) =ᵐ[P] (U ⁻¹' s : Set Ω) := (hU'.symm).preimage s
    have e2 : (hV.mk ⁻¹' t : Set Ω) =ᵐ[P] (V ⁻¹' t : Set Ω) := (hV'.symm).preimage t
    rw [measure_congr e1, measure_congr e2, measure_congr (e1.inter e2)]
    exact h s hs t ht

end Core

end Thm18Asm
end QuantumZipper
