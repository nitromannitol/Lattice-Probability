/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.CondCopies at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.CondDistrib
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepAEDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Conditionally i.i.d. copies given a random variable

Let `X : Ω → α` (e.g. the field `h`) and `Y : Ω → β` (e.g. the metric `D`) with `β` standard
Borel, so that the regular conditional law `κ := condDistrib Y X μ` of `Y` given `X` exists
(mathlib). The **conditionally i.i.d. copy** of `Y` given `X` (LM = Gwynne–Miller, *Local
metrics of the Gaussian free field*, arXiv:1905.00379, Theorem 1.7 and Corollary 1.8, tex:306–311
and tex:317–332: "condition on `h` and let `D, D̃` be conditionally i.i.d. samples from the
conditional law of `D` given `h`") lives on the extended probability space `Ω × β` with the
measure `μ ⊗ₘ (κ ∘ X)`: the first coordinate carries all the original random variables, and the
second coordinate `Ỹ` is a sample from `κ (X ω)`.

Main results:
* `condCopyMeasure`, the extended space; `condCopyMeasure_fst`: its first marginal is `μ`;
* `condCopyMeasure_map_snd`: `(X, Ỹ)` has the law of `(X, Y)`;
* `condCopyMeasure_map_triple`: the law of `(X, Y, Ỹ)` is `law(X) ⊗ (κ × κ)`, i.e. `Y` and `Ỹ`
  are conditionally independent given `X` with the same conditional law (this law depends only
  on the law of `(X, Y)`, so the copy is canonical);
* `condIndepEv_condCopy_fst`, `condIndepEv_condCopy`: `σ(Ω) ⟂ σ(Ỹ) | σ(X)`, in particular
  `σ(Y) ⟂ σ(Ỹ) | σ(X)`, in event form (`CondIndepEv`);
* `aeDeterminedBy_of_condCopy_ae_eq`: **LM S5.d** in copy form: if `Y = Ỹ` a.s. then `Y` is
  a.s. determined by `X`.

This is the textbook construction of a conditionally independent copy (e.g. Kallenberg,
*Foundations of Modern Probability*, 2nd ed., Thm 6.3 and Prop. 6.13 — not supplied; cited for
the statement only). The Lean proofs are own bookkeeping with mathlib's `condDistrib`,
`Measure.compProd` and `ae_eq_condExp_of_forall_setIntegral_eq`.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open scoped ENNReal

namespace LQGMetric

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]

/-- The kernel `ω ↦ condDistrib Y X μ (X ω)`: the conditional law of `Y` given `X`, evaluated at
`X ω`. -/
noncomputable def condCopyKernel (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) :
    Kernel Ω β :=
  (condDistrib Y X μ).comap X hX

instance (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ] (hX : Measurable X) :
    IsMarkovKernel (condCopyKernel Y X μ hX) := by
  unfold condCopyKernel; infer_instance

/-- The extended probability space `Ω × β` carrying a conditionally independent copy
`Ỹ = Prod.snd` of `Y` given `X`. -/
noncomputable def condCopyMeasure (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) :
    Measure (Ω × β) :=
  μ ⊗ₘ condCopyKernel Y X μ hX

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}

instance (hX : Measurable X) : IsProbabilityMeasure (condCopyMeasure Y X μ hX) := by
  unfold condCopyMeasure; infer_instance

/-- The original random variables keep their joint law on the extended space. -/
theorem condCopyMeasure_fst (hX : Measurable X) :
    (condCopyMeasure Y X μ hX).map Prod.fst = μ :=
  Measure.fst_compProd μ _

theorem condCopyMeasure_apply_prod (hX : Measurable X) {s : Set Ω} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    condCopyMeasure Y X μ hX (s ×ˢ t) = ∫⁻ ω in s, condDistrib Y X μ (X ω) t ∂μ := by
  rw [condCopyMeasure, Measure.compProd_apply_prod hs ht]
  simp only [condCopyKernel, Kernel.comap_apply]

/-- The copy `(X, Ỹ)` has the law of `(X, Y)`. -/
theorem condCopyMeasure_map_snd (hX : Measurable X) (hY : Measurable Y) :
    (condCopyMeasure Y X μ hX).map (fun p => (X p.1, p.2)) = μ.map (fun ω => (X ω, Y ω)) := by
  have hm : Measurable fun p : Ω × β => (X p.1, p.2) := (hX.comp measurable_fst).prodMk
    measurable_snd
  refine Measure.ext_prod (fun {s t} hs ht => ?_)
  rw [Measure.map_apply hm (hs.prod ht), Measure.map_apply (hX.prodMk hY) (hs.prod ht)]
  have h1 : (fun p : Ω × β => (X p.1, p.2)) ⁻¹' (s ×ˢ t) = (X ⁻¹' s) ×ˢ t := by ext; simp
  have h2 : (fun ω => (X ω, Y ω)) ⁻¹' (s ×ˢ t) = X ⁻¹' s ∩ Y ⁻¹' t := by ext; simp
  rw [h1, h2, condCopyMeasure_apply_prod hX (hX hs) ht,
    setLIntegral_preimage_condDistrib hX hY.aemeasurable ht hs]

/-- **Law of the triple.** `(X, Y, Ỹ)` has law `law(X) ⊗ (κ × κ)` with `κ = condDistrib Y X μ`:
`Y` and `Ỹ` are conditionally independent given `X`, each with conditional law `κ`. -/
theorem condCopyMeasure_map_triple (hX : Measurable X) (hY : Measurable Y) :
    (condCopyMeasure Y X μ hX).map (fun p => (X p.1, Y p.1, p.2)) =
      μ.map X ⊗ₘ (condDistrib Y X μ ×ₖ condDistrib Y X μ) := by
  set κ := condDistrib Y X μ
  have hm : Measurable fun p : Ω × β => (X p.1, Y p.1, p.2) :=
    (hX.comp measurable_fst).prodMk ((hY.comp measurable_fst).prodMk measurable_snd)
  refine Measure.ext_prod₃ (fun {s t u} hs ht hu => ?_)
  rw [Measure.map_apply hm (hs.prod (ht.prod hu)), Measure.compProd_apply_prod hs (ht.prod hu)]
  have h1 : (fun p : Ω × β => (X p.1, Y p.1, p.2)) ⁻¹' (s ×ˢ t ×ˢ u) =
      (X ⁻¹' s ∩ Y ⁻¹' t) ×ˢ u := by ext; simp [and_assoc]
  rw [h1, condCopyMeasure_apply_prod hX ((hX hs).inter (hY ht)) hu]
  simp_rw [Kernel.prod_apply_prod]
  -- `∫⁻_{X∈s, Y∈t} κ(X) u dμ = ∫⁻_s κ(x) t · κ(x) u d law(X)`
  have hku : Measurable fun x => κ x u := κ.measurable_coe hu
  have hf : Measurable fun q : α × β => κ q.1 u := hku.comp measurable_fst
  have hjoint : μ.map (fun ω => (X ω, Y ω)) = μ.map X ⊗ₘ κ :=
    (compProd_map_condDistrib hX.aemeasurable hY.aemeasurable).symm
  calc ∫⁻ ω in X ⁻¹' s ∩ Y ⁻¹' t, κ (X ω) u ∂μ
      = ∫⁻ q in s ×ˢ t, κ q.1 u ∂(μ.map (fun ω => (X ω, Y ω))) := by
        rw [setLIntegral_map (hs.prod ht) hf (hX.prodMk hY)]
        rfl
    _ = ∫⁻ x in s, ∫⁻ _ in t, κ x u ∂(κ x) ∂(μ.map X) := by
        rw [hjoint, Measure.setLIntegral_compProd hf hs ht]
    _ = ∫⁻ x in s, κ x t * κ x u ∂(μ.map X) := by
        refine setLIntegral_congr_fun hs (fun x _ => ?_)
        rw [setLIntegral_const, mul_comm]

theorem setIntegral_condCopy_fst (hX : Measurable X) {s₀ : Set Ω} (hs₀ : MeasurableSet s₀)
    {u : Set β} (hu : MeasurableSet u) :
    ∫ p in Prod.fst ⁻¹' s₀, (condDistrib Y X μ (X p.1)).real u ∂(condCopyMeasure Y X μ hX) =
      (∫⁻ ω in s₀, condDistrib Y X μ (X ω) u ∂μ).toReal := by
  set κ := condDistrib Y X μ
  have hku : Measurable fun x => (κ x).real u := (κ.measurable_coe hu).ennreal_toReal
  have h := setIntegral_map (μ := condCopyMeasure Y X μ hX) (f := fun ω => (κ (X ω)).real u) hs₀
    (hku.comp hX).aestronglyMeasurable measurable_fst.aemeasurable
  rw [condCopyMeasure_fst hX] at h
  rw [← h]
  have hm : AEMeasurable (fun ω => κ (X ω) u) (μ.restrict s₀) :=
    ((κ.measurable_coe hu).comp hX).aemeasurable
  exact integral_toReal hm (Eventually.of_forall fun ω => measure_lt_top _ _)

/-- `P[Ỹ ∈ u | G] = κ(X) u` for every σ-algebra `G` between `σ(X ∘ fst)` and `σ(fst)`. -/
theorem condExp_condCopy_snd (hX : Measurable X) {G : MeasurableSpace (Ω × β)}
    (hXG : mα.comap (fun p : Ω × β => X p.1) ≤ G) (hG : G ≤ mΩ.comap Prod.fst) {u : Set β}
    (hu : MeasurableSet u) :
    (fun p : Ω × β => (condDistrib Y X μ (X p.1)).real u) =ᵐ[condCopyMeasure Y X μ hX]
      (condCopyMeasure Y X μ hX)⟦Prod.snd ⁻¹' u | G⟧ := by
  set ν := condCopyMeasure Y X μ hX
  set κ := condDistrib Y X μ
  have hG0 : G ≤ (Prod.instMeasurableSpace : MeasurableSpace (Ω × β)) := fun s hs => by
    obtain ⟨s₀, hs₀, rfl⟩ := hG s hs
    exact measurable_fst hs₀
  have hku : Measurable fun x => (κ x).real u := (κ.measurable_coe hu).ennreal_toReal
  have hfm : Measurable[G] fun p : Ω × β => (κ (X p.1)).real u :=
    (hku.comp (comap_measurable (fun p : Ω × β => X p.1))).mono hXG le_rfl
  have hbd : ∀ p : Ω × β, ‖(κ (X p.1)).real u‖ ≤ 1 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hint : Integrable (fun p : Ω × β => (κ (X p.1)).real u) ν :=
    Integrable.of_bound (hfm.mono hG0 le_rfl).aestronglyMeasurable 1 (Eventually.of_forall hbd)
  refine ae_eq_condExp_of_forall_setIntegral_eq hG0
    ((integrable_const (1 : ℝ)).indicator (measurable_snd hu)) (fun _ _ _ => hint.integrableOn)
    (fun s hs _ => ?_) hfm.aestronglyMeasurable
  obtain ⟨s₀, hs₀, rfl⟩ := hG s hs
  rw [setIntegral_indicator (measurable_snd hu), integral_const, smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply_univ, ← Set.prod_eq,
    condCopyMeasure_apply_prod hX hs₀ hu]
  exact setIntegral_condCopy_fst hX hs₀ hu

/-- **The copy is conditionally independent of everything on `Ω` given `X`** (event form):
`σ(fst) ⟂ σ(Ỹ) | σ(X)`. In particular `Ỹ` is conditionally independent given `X` of `Y` and of
all other random variables defined on `Ω` (LM Lemma 5.3 uses copies given data `(h, θ, …)`). -/
theorem condIndepEv_condCopy_fst (hX : Measurable X) :
    CondIndepEv (mα.comap (fun p : Ω × β => X p.1)) (mΩ.comap (Prod.fst : Ω × β → Ω))
      (mβ.comap (Prod.snd : Ω × β → β)) (condCopyMeasure Y X μ hX) := by
  have hXm : Measurable fun p : Ω × β => X p.1 := hX.comp measurable_fst
  have hXf : mα.comap (fun p : Ω × β => X p.1) ≤ mΩ.comap Prod.fst := by
    rw [show (fun p : Ω × β => X p.1) = X ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hX.comap_le
  refine (condIndepEv_of_condExp_sup_eq hXm.comap_le measurable_snd.comap_le
    measurable_fst.comap_le ?_).symm
  rintro _ ⟨u, hu, rfl⟩
  exact (condExp_condCopy_snd hX le_sup_right (sup_le le_rfl hXf) hu).symm.trans
    (condExp_condCopy_snd hX le_rfl hXf hu)

/-- **The copy is conditionally independent of the original given `X`** (event form). -/
theorem condIndepEv_condCopy (hX : Measurable X) (hY : Measurable Y) :
    CondIndepEv (mα.comap (fun p : Ω × β => X p.1)) (mβ.comap (fun p : Ω × β => Y p.1))
      (mβ.comap (Prod.snd : Ω × β → β)) (condCopyMeasure Y X μ hX) := by
  refine (condIndepEv_condCopy_fst hX).mono ?_ le_rfl
  rw [show (fun p : Ω × β => Y p.1) = Y ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hY.comap_le

/-- **LM S5.d, copy form.** If the conditionally i.i.d. copy agrees with the original a.s., then
`Y` is a.s. determined by `X` (LM, proofs of Lemma 5.3 and Theorem 1.7, tex:956–986,
tex:1084–1087). -/
theorem aeDeterminedBy_of_condCopy_ae_eq (hX : Measurable X) (hY : Measurable Y)
    (heq : (fun p : Ω × β => Y p.1) =ᵐ[condCopyMeasure Y X μ hX] Prod.snd) :
    AEDeterminedBy Y X μ := by
  obtain ⟨F, hF, hYF⟩ := aeDeterminedBy_of_condIndepEv_of_ae_eq (hX.comp measurable_fst)
    (hY.comp measurable_fst) (condIndepEv_condCopy hX hY) heq
  refine ⟨F, hF, ?_⟩
  rw [Filter.EventuallyEq, ← condCopyMeasure_fst (Y := Y) (μ := μ) hX,
    ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hY (hF.comp hX))]
  exact hYF

end LQGMetric
