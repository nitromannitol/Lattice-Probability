/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/CondCopies.lean.
-/

import Mathlib.Probability.Kernel.CondDistrib
import LatticeProb.Prob.AEDetermined
import LatticeProb.Prob.CondIndepDetermined

/-!
# Conditionally independent copies given a random variable

Let `μ` be a probability measure and let `X : Ω → α` and `Y : Ω → β` be measurable, with `β`
nonempty and standard Borel, so that the regular conditional law
`κ := condDistrib Y X μ` of `Y` given `X` exists. A conditionally independent copy of `Y` given
`X` lives on the extended space `Ω × β` with the measure `μ ⊗ₘ (κ ∘ X)`: the first coordinate
carries all the original random variables, and the second coordinate `Ỹ` is a sample from
`κ (X ω)`. Given `X`, the two variables `Y` and `Ỹ` are independent and have the same law.

Main results:
* `condCopyMeasure`, the extended space; `condCopyMeasure_fst`: its first marginal is `μ`;
* `condCopyMeasure_map_snd`: `(X, Ỹ)` has the law of `(X, Y)`;
* `condCopyMeasure_map_triple`: the law of `(X, Y, Ỹ)` is `law(X) ⊗ (κ × κ)`, i.e. `Y` and `Ỹ`
  are conditionally independent given `X` with the same conditional law (this law depends only
  on the law of `(X, Y)`, so the copy is canonical);
* `condIndepEv_condCopy_fst`, `condIndepEv_condCopy`: `σ(fst) ⟂ σ(Ỹ) | σ(X)`, where `σ(fst)` is
  the σ-algebra of the first coordinate, in particular
  `σ(Y) ⟂ σ(Ỹ) | σ(X)`, in event form (`CondIndepEv`);
* `aeDeterminedBy_of_condCopy_ae_eq`: if `Y = Ỹ` almost surely, then `Y` is almost surely a
  measurable function of `X`.

The construction is the standard one for conditionally independent copies, as in the textbook
literature on conditioning and disintegration (e.g. Kallenberg, *Foundations of Modern
Probability*, 2nd ed.). The Lean proofs use mathlib's `condDistrib`, `Measure.compProd` and
`ae_eq_condExp_of_forall_setIntegral_eq`.

The namespace `LatticeProb.CondCopiesExample` checks that the agreement hypothesis of
`aeDeterminedBy_of_condCopy_ae_eq` is satisfiable with nontrivial content: on `Bool` with the fair
coin, `Y = not ∘ X` with `X = id`.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]

/-- The kernel `ω ↦ condDistrib Y X μ (X ω)`. For measurable `Y`, this is the conditional law
of `Y` given `X`, evaluated at `X ω`. -/
noncomputable def condCopyKernel (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) :
    Kernel Ω β :=
  (condDistrib Y X μ).comap X hX

/-- The kernel `condCopyKernel` is Markov. -/
instance (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ] (hX : Measurable X) :
    IsMarkovKernel (condCopyKernel Y X μ hX) := by
  unfold condCopyKernel; infer_instance

/-- The finite measure `μ ⊗ₘ (condDistrib Y X μ ∘ X)` on `Ω × β`, extending `μ` via the first
coordinate. It is a probability measure when `μ` is (the instance below). When `μ` is a
probability measure and `Y` is measurable, it carries a conditionally independent copy
`Ỹ = Prod.snd` of `Y` given `X`. -/
noncomputable def condCopyMeasure (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) :
    Measure (Ω × β) :=
  μ ⊗ₘ condCopyKernel Y X μ hX

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}

/-- The extended space `condCopyMeasure` is a probability measure. -/
instance (hX : Measurable X) : IsProbabilityMeasure (condCopyMeasure Y X μ hX) := by
  unfold condCopyMeasure; infer_instance

/-- The original random variables keep their joint law on the extended space. -/
theorem condCopyMeasure_fst (hX : Measurable X) :
    (condCopyMeasure Y X μ hX).map Prod.fst = μ :=
  Measure.fst_compProd μ _

/-- The measure of a rectangle on the extended space is the integral of the conditional law of
`Y` given `X` over the first factor. -/
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
    (compProd_map_condDistrib hY.aemeasurable).symm
  calc ∫⁻ ω in X ⁻¹' s ∩ Y ⁻¹' t, κ (X ω) u ∂μ
      = ∫⁻ q in s ×ˢ t, κ q.1 u ∂(μ.map (fun ω => (X ω, Y ω))) := by
        rw [setLIntegral_map (hs.prod ht) hf (hX.prodMk hY)]
        rfl
    _ = ∫⁻ x in s, ∫⁻ _ in t, κ x u ∂(κ x) ∂(μ.map X) := by
        rw [hjoint, Measure.setLIntegral_compProd hf hs ht]
    _ = ∫⁻ x in s, κ x t * κ x u ∂(μ.map X) := by
        refine setLIntegral_congr_fun hs (fun x _ => ?_)
        rw [setLIntegral_const, mul_comm]

/-- Over `Prod.fst ⁻¹' s₀`, the extended measure integrates the conditional probability
`κ (X p.1) u` to the integral of `κ (X ω) u` over `s₀` under `μ`. -/
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
all other random variables defined on `Ω`. -/
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

/-- If the conditionally independent copy agrees with the original almost surely, then `Y` is
almost surely a measurable function of `X`: `Y = F ∘ X` a.s. for a measurable `F`. -/
theorem aeDeterminedBy_of_condCopy_ae_eq (hX : Measurable X) (hY : Measurable Y)
    (heq : (fun p : Ω × β => Y p.1) =ᵐ[condCopyMeasure Y X μ hX] Prod.snd) :
    AEDeterminedBy Y X μ := by
  obtain ⟨F, hF, hYF⟩ := aeDeterminedBy_of_condIndepEv_of_ae_eq (hX.comp measurable_fst)
    (hY.comp measurable_fst) (condIndepEv_condCopy hX hY) heq
  refine ⟨F, hF, ?_⟩
  rw [Filter.EventuallyEq, ← condCopyMeasure_fst (Y := Y) (μ := μ) hX,
    ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hY (hF.comp hX))]
  exact hYF

/-- If `Y = g ∘ X` for a measurable `g`, the copy `Ỹ` agrees with `Y` almost surely: the
conditional law of `Y` given `X` is a point mass at `g (X ω)`. -/
theorem ae_eq_snd_of_comp {g : α → β} (hg : Measurable g) (hX : Measurable X) :
    (fun p : Ω × β => g (X p.1)) =ᵐ[condCopyMeasure (g ∘ X) X μ hX] Prod.snd := by
  have hae : ∀ᵐ ω ∂μ, ∀ᵐ b ∂(condCopyKernel (g ∘ X) X μ hX ω), b = g (X ω) := by
    filter_upwards [ae_of_ae_map hX.aemeasurable (condDistrib_comp_self X hg)] with ω hω
    rw [condCopyKernel, Kernel.comap_apply, hω, Kernel.deterministic_apply, ae_dirac_eq]
    exact eventually_pure.2 rfl
  have hm : MeasurableSet {p : Ω × β | g (X p.1) = p.2} :=
    measurableSet_eq_fun (hg.comp (hX.comp measurable_fst)) measurable_snd
  rw [Filter.EventuallyEq, condCopyMeasure, Measure.ae_compProd_iff hm]
  filter_upwards [hae] with ω hω
  exact hω.mono fun b hb => hb.symm

namespace CondCopiesExample

/-- Nonvacuity of the agreement hypothesis: on `Bool` with the fair coin, `X = id` and
`Y = not ∘ X`, so the copy `Ỹ` agrees with `Y` almost surely. -/
theorem ae_eq_coin :
    (fun p : Bool × Bool => (fun b : Bool => !b) (id p.1)) =ᵐ[
      condCopyMeasure (fun b : Bool => !b) id AEDeterminedSigmaExample.coin measurable_id]
      Prod.snd :=
  ae_eq_snd_of_comp (μ := AEDeterminedSigmaExample.coin) (measurable_of_countable _)
    measurable_id

/-- Nonvacuity of `aeDeterminedBy_of_condCopy_ae_eq`: on `Bool` with the fair coin, `Y = not ∘ X`
with `X = id` is almost surely a measurable function of `X`. -/
theorem aeDeterminedBy_coin :
    AEDeterminedBy (fun b : Bool => !b) (id : Bool → Bool) AEDeterminedSigmaExample.coin :=
  aeDeterminedBy_of_condCopy_ae_eq measurable_id (measurable_of_countable _) ae_eq_coin

end CondCopiesExample

end LatticeProb
