import Mathlib

/-!
# Laws of processes whose coordinates agree almost surely

A process indexed by an arbitrary set `ι` (a map `Ω → ι → ℝ`, with the product σ-algebra) is determined in law by its
finite dimensional distributions. Two such processes whose coordinates agree almost surely, coordinate by
coordinate (the exceptional null set may depend on the coordinate), therefore have the same law, and the same joint
law with any further random variable.

* `map_prodMk_eq_of_ae_eq_apply`: if `Y i = Y' i` almost surely for each `i`, then `(X, Y)` and `(X, Y')` have the
  same law on `E × (ι → ℝ)`.
* `map_eq_of_ae_eq_apply`: the same for the laws of `Y` and `Y'` alone.
* `indepFun_prodMk_snd_of_indepFun`: if `X` and `L` are independent random variables of a probability space `P`, and
  `Ψ` is a random variable of a second probability space `ν`, then on the product space `P ⊗ ν` the pair
  `(X, Ψ)` is independent of `L`.
-/

open MeasureTheory MeasurableSpace Set ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

section Coordinates

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- **Coordinatewise almost sure equality gives equality of joint laws.** If `X : Ω → E` is measurable and the
real processes `Y, Y' : Ω → ι → ℝ` have measurable coordinates which agree almost surely, each coordinate with
its own null set, then `(X, Y)` and `(X, Y')` have the same law on `E × (ι → ℝ)`. -/
theorem map_prodMk_eq_of_ae_eq_apply {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → E} {Y Y' : Ω → ι → ℝ}
    (hX : Measurable X) (hY : ∀ i, Measurable fun ω => Y ω i) (hY' : ∀ i, Measurable fun ω => Y' ω i)
    (h : ∀ i, ∀ᵐ ω ∂μ, Y ω i = Y' ω i) :
    μ.map (fun ω => (X ω, Y ω)) = μ.map (fun ω => (X ω, Y' ω)) := by
  have hm : Measurable fun ω => (X ω, Y ω) := hX.prodMk (measurable_pi_iff.2 hY)
  have hm' : Measurable fun ω => (X ω, Y' ω) := hX.prodMk (measurable_pi_iff.2 hY')
  set C : Set (Set E) := {A | MeasurableSet A} with hC
  set D : Set (Set (ι → ℝ)) := measurableCylinders (fun _ : ι => ℝ) with hD
  have huniv : (univ : Set (ι → ℝ)) ∈ D :=
    (mem_measurableCylinders _).2 ⟨∅, univ, MeasurableSet.univ, by simp [cylinder]⟩
  have hCs : IsCountablySpanning C := ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩
  have hDs : IsCountablySpanning D := ⟨fun _ => univ, fun _ => huniv, iUnion_const _⟩
  have hgen : (inferInstance : MeasurableSpace (E × (ι → ℝ))) = generateFrom (image2 (· ×ˢ ·) C D) := by
    have := generateFrom_prod_eq hCs hDs
    rw [hC, hD, generateFrom_measurableSet, generateFrom_measurableCylinders] at this
    exact this
  have hpi : IsPiSystem (image2 (· ×ˢ ·) C D) :=
    (MeasurableSpace.isPiSystem_measurableSet (α := E)).prod isPiSystem_measurableCylinders
  refine ext_of_generate_finite _ hgen hpi ?_ ?_
  · rintro _ ⟨A, hA, T, hT, rfl⟩
    have hSm : MeasurableSet (A ×ˢ T) :=
      (show MeasurableSet A from hA).prod (MeasurableSet.of_mem_measurableCylinders hT)
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hT
    rw [Measure.map_apply hm hSm, Measure.map_apply hm' hSm]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [(Filter.eventually_all_finset I).2 fun i _ => h i] with ω hω
    have hres : I.restrict (Y ω) = I.restrict (Y' ω) := funext fun i => hω i i.2
    simp only [mem_preimage, mem_prod, mem_cylinder, hres]
  · rw [Measure.map_apply hm MeasurableSet.univ, Measure.map_apply hm' MeasurableSet.univ]
    simp

/-- Coordinatewise almost sure equality gives equality of laws. -/
theorem map_eq_of_ae_eq_apply {μ : Measure Ω} [IsFiniteMeasure μ] {Y Y' : Ω → ι → ℝ}
    (hY : ∀ i, Measurable fun ω => Y ω i) (hY' : ∀ i, Measurable fun ω => Y' ω i)
    (h : ∀ i, ∀ᵐ ω ∂μ, Y ω i = Y' ω i) : μ.map Y = μ.map Y' := by
  have := map_prodMk_eq_of_ae_eq_apply (μ := μ) (X := fun _ : Ω => ()) measurable_const hY hY' h
  have h2 := congrArg (Measure.map Prod.snd) this
  rwa [Measure.map_map measurable_snd (measurable_const.prodMk (measurable_pi_iff.2 hY)),
    Measure.map_map measurable_snd (measurable_const.prodMk (measurable_pi_iff.2 hY'))] at h2

end Coordinates

section Product

variable {Ω₁ Ω₂ E₁ E₂ E₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace E₁]
  [MeasurableSpace E₂] [MeasurableSpace E₃]

/-- **Adding an independent factor.** Let `X, L` be independent random variables on a probability space
`(Ω₁, P)` and `Ψ` a random variable on a probability space `(Ω₂, ν)`. On the product space the pair
`(X(ω₁), Ψ(ω₂))` is independent of `L(ω₁)`. -/
theorem indepFun_prodMk_snd_of_indepFun {P : Measure Ω₁} {ν : Measure Ω₂} [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] {X : Ω₁ → E₁} {L : Ω₁ → E₃} {Ψ : Ω₂ → E₂} (hX : Measurable X)
    (hL : Measurable L) (hΨ : Measurable Ψ) (h : IndepFun X L P) :
    IndepFun (fun ω : Ω₁ × Ω₂ => (X ω.1, Ψ ω.2)) (fun ω => L ω.1) (P.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hF : Measurable fun ω : Ω₁ × Ω₂ => (X ω.1, Ψ ω.2) :=
    (hX.comp measurable_fst).prodMk (hΨ.comp measurable_snd)
  have hG : Measurable fun ω : Ω₁ × Ω₂ => L ω.1 := hL.comp measurable_fst
  set g : E₁ → ℝ≥0∞ := fun a => (ν.map Ψ) (Prod.mk a ⁻¹' s) with hg
  have hgm : Measurable g := measurable_measure_prodMk_left hs
  have hpre : ∀ a, ν ((fun w => (a, Ψ w)) ⁻¹' s) = g a := fun a => by
    simp only [hg]
    rw [Measure.map_apply hΨ (measurable_prodMk_left hs)]; rfl
  -- the three measures as integrals over `Ω₁`
  have h1 : (P.prod ν) ((fun ω : Ω₁ × Ω₂ => (X ω.1, Ψ ω.2)) ⁻¹' s) = ∫⁻ x, g (X x) ∂P := by
    rw [Measure.prod_apply (hF hs)]
    refine lintegral_congr fun x => ?_
    exact hpre (X x)
  have h2 : (P.prod ν) ((fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t) = P (L ⁻¹' t) := by
    rw [Measure.prod_apply (hG ht)]
    have : ∀ x, ν (Prod.mk x ⁻¹' ((fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t)) = (L ⁻¹' t).indicator 1 x := fun x => by
      by_cases hx : L x ∈ t
      · have e : Prod.mk x ⁻¹' ((fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t) = univ := by ext w; simp [hx]
        rw [e]; simp [hx, Set.indicator]
      · have e : Prod.mk x ⁻¹' ((fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t) = ∅ := by ext w; simp [hx]
        rw [e]; simp [hx, Set.indicator]
    simp_rw [this]
    rw [lintegral_indicator_one (hL ht)]
  have h3 : (P.prod ν) ((fun ω : Ω₁ × Ω₂ => (X ω.1, Ψ ω.2)) ⁻¹' s ∩ (fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t) =
      ∫⁻ x, (L ⁻¹' t).indicator 1 x * g (X x) ∂P := by
    rw [Measure.prod_apply ((hF hs).inter (hG ht))]
    refine lintegral_congr fun x => ?_
    by_cases hx : L x ∈ t
    · have : Prod.mk x ⁻¹' ((fun ω : Ω₁ × Ω₂ => (X ω.1, Ψ ω.2)) ⁻¹' s ∩ (fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t) =
          (fun w => (X x, Ψ w)) ⁻¹' s := by
        ext w; simp [hx]
      rw [this, hpre]; simp [hx, Set.indicator]
    · have : Prod.mk x ⁻¹' ((fun ω : Ω₁ × Ω₂ => (X ω.1, Ψ ω.2)) ⁻¹' s ∩ (fun ω : Ω₁ × Ω₂ => L ω.1) ⁻¹' t) = ∅ := by
        ext w; simp [hx]
      rw [this]; simp [hx, Set.indicator]
  rw [h1, h2, h3]
  have hind : IndepFun (fun x => (L ⁻¹' t).indicator (1 : Ω₁ → ℝ≥0∞) x) (fun x => g (X x)) P := by
    have hL' : IndepFun (fun x => (t.indicator (1 : E₃ → ℝ≥0∞)) (L x)) (fun x => g (X x)) P :=
      (h.symm.comp (measurable_one.indicator ht) hgm)
    refine hL'.congr (Filter.Eventually.of_forall fun x => ?_) Filter.EventuallyEq.rfl
    by_cases hx : L x ∈ t <;> simp [Set.indicator, hx]
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (measurable_one.indicator (hL ht)) (hgm.comp hX) hind
  simp only [Pi.mul_apply, Function.comp_apply] at this
  rw [this, lintegral_indicator_one (hL ht), mul_comm]

end Product

end LatticeProb
