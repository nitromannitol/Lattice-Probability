/-
One coordinate of an infinite product, against everything else.

Every paper in the program conditions on all the coordinates of a stack but
one.  The fact behind that is here: under `Measure.infinitePi`, a function that
does not read the coordinate `q` is independent of that coordinate, so an
integral of such a function against a function of `ω q` factors.

"Does not read the coordinate `q`" is stated as invariance under overwriting
that coordinate with a fixed value, `F (Function.update ω q c) = F ω`, which is
how it arises: the event that the odometer has reached the `j`-th instruction at
a site does not depend on that instruction.
-/
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Independence.Integration
import LatticeProb.Prob.ZeroOne

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- A map into a product is measurable for a sigma algebra as soon as each of
its coordinates is. -/
theorem comap_pi_le_of_coordinates {α : Type*} {m : MeasurableSpace α}
    (f : α → Π i, X i)
    (h : ∀ i, MeasurableSpace.comap (fun a => f a i) inferInstance ≤ m) :
    MeasurableSpace.comap f inferInstance ≤ m := by
  rw [show (inferInstance : MeasurableSpace (Π i, X i))
      = ⨆ i : ι, MeasurableSpace.comap (fun ω : Π i, X i => ω i) inferInstance from rfl,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun i => ?_
  rw [MeasurableSpace.comap_comp]
  exact h i

variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- A function that does not read the coordinate `q` is independent of that
coordinate. -/
theorem indepFun_of_update_invariant [DecidableEq ι] {q : ι} (c : X q)
    {E : Type*} [MeasurableSpace E] (F : (Π i, X i) → E) (hF : Measurable F)
    (hinv : ∀ ω, F (Function.update ω q c) = F ω) :
    IndepFun F (fun ω : Π i, X i => ω q) (Measure.infinitePi μ) := by
  classical
  set s : ι → MeasurableSpace (Π i, X i) := fun i =>
    MeasurableSpace.comap (fun ω : Π i, X i => ω i) inferInstance with hs
  have hcoord : iIndepFun (fun (i : ι) (ω : Π i, X i) => ω i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) fun _ => measurable_id
  have hind : iIndep s (Measure.infinitePi μ) := (iIndepFun_iff_iIndep _ _ _).mp hcoord
  have hle : ∀ i : ι, s i ≤ (inferInstance : MeasurableSpace (Π i, X i)) := fun i =>
    (measurable_pi_apply i).comap_le
  have hsplit := ProbabilityTheory.indep_biSup_compl hle hind (({q} : Set ι)ᶜ)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le hsplit ?_ ?_
  · -- `F` is measurable for the coordinates away from `q`
    have hupd : MeasurableSpace.comap (fun ω : Π i, X i => Function.update ω q c)
        inferInstance ≤ ⨆ i ∈ (({q} : Set ι)ᶜ), s i := by
      refine comap_pi_le_of_coordinates _ fun i => ?_
      by_cases hi : i = q
      · subst hi
        have he : (fun ω : Π i, X i => Function.update ω i c i) = fun _ => c := by
          funext ω; simp
        rw [he, MeasurableSpace.comap_const]
        exact bot_le
      · have he : (fun ω : Π i, X i => Function.update ω q c i) = fun ω => ω i := by
          funext ω; rw [Function.update_of_ne hi]
        rw [he]
        exact le_biSup s (show i ∈ (({q} : Set ι)ᶜ) by simpa using hi)
    have hFupd : (F ∘ fun ω : Π i, X i => Function.update ω q c) = F := funext hinv
    calc MeasurableSpace.comap F inferInstance
        = MeasurableSpace.comap (fun ω : Π i, X i => Function.update ω q c)
            (MeasurableSpace.comap F inferInstance) := by
          rw [MeasurableSpace.comap_comp, hFupd]
      _ ≤ MeasurableSpace.comap (fun ω : Π i, X i => Function.update ω q c) inferInstance :=
          MeasurableSpace.comap_mono hF.comap_le
      _ ≤ _ := hupd
  · exact le_biSup s (show q ∈ ((({q} : Set ι)ᶜ)ᶜ) by simp)

/-- The integral of a function of one coordinate is the integral against that
coordinate's law. -/
theorem integral_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ι) (g : X q → E) (hg : AEStronglyMeasurable g (μ q)) :
    ∫ ω, g (ω q) ∂(Measure.infinitePi μ) = ∫ u, g u ∂(μ q) := by
  conv_rhs => rw [← Measure.infinitePi_map_eval μ q]
  rw [integral_map (measurable_pi_apply q).aemeasurable
    (by rw [Measure.infinitePi_map_eval]; exact hg)]

/-- **One coordinate against the rest.**  If `F` does not read the coordinate
`q`, then its integral against the indicator of an event in that coordinate
factors. -/
theorem integral_mul_indicator_eval [DecidableEq ι] (q : ι) (c : X q)
    (F : (Π i, X i) → ℝ) (hF : Measurable F)
    (hinv : ∀ ω, F (Function.update ω q c) = F ω)
    {t : Set (X q)} (ht : MeasurableSet t) :
    ∫ ω, F ω * Set.indicator t (fun _ => (1 : ℝ)) (ω q) ∂(Measure.infinitePi μ)
      = (μ q t).toReal * ∫ ω, F ω ∂(Measure.infinitePi μ) := by
  classical
  have hind : IndepFun F (fun ω : Π i, X i => Set.indicator t (fun _ => (1 : ℝ)) (ω q))
      (Measure.infinitePi μ) := by
    have h := indepFun_of_update_invariant μ c F hF hinv
    exact h.comp measurable_id
      ((measurable_const.indicator ht : Measurable
        (Set.indicator t fun _ : X q => (1 : ℝ))))
  have hmeas2 : AEStronglyMeasurable
      (fun ω : Π i, X i => Set.indicator t (fun _ => (1 : ℝ)) (ω q))
      (Measure.infinitePi μ) :=
    (((measurable_const.indicator ht).comp (measurable_pi_apply q))).aestronglyMeasurable
  have hval : ∫ ω, Set.indicator t (fun _ => (1 : ℝ)) (ω q) ∂(Measure.infinitePi μ)
      = (μ q t).toReal := by
    rw [integral_eval μ q (Set.indicator t fun _ => (1 : ℝ))
      (measurable_const.indicator ht).aestronglyMeasurable]
    rw [show (Set.indicator t fun _ : X q => (1 : ℝ)) = Set.indicator t 1 from rfl,
      integral_indicator_one ht, measureReal_def]
  rw [hind.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hmeas2, hval]
  ring

/-- **One coordinate against the rest, on a product.**  The same factorization
when the function also reads a second, independent, source of randomness, which
is the shape `LatticeProb.stackLaw` and `LatticeProb.rankLaw` sit in. -/
theorem integral_mul_indicator_eval_prod [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (q : ι) (c : X q)
    (F : (Π i, X i) × Ω → ℝ) (hF : Measurable F)
    (hFint : Integrable F ((Measure.infinitePi μ).prod ν))
    (hinv : ∀ (ω : Π i, X i) (y : Ω), F (Function.update ω q c, y) = F (ω, y))
    {t : Set (X q)} (ht : MeasurableSet t) :
    ∫ p, F p * Set.indicator t (fun _ => (1 : ℝ)) (p.1 q) ∂((Measure.infinitePi μ).prod ν)
      = (μ q t).toReal * ∫ p, F p ∂((Measure.infinitePi μ).prod ν) := by
  classical
  have hset : MeasurableSet ((fun p : (Π i, X i) × Ω => p.1 q) ⁻¹' t) :=
    ((measurable_pi_apply q).comp measurable_fst) ht
  have heq : (fun p : (Π i, X i) × Ω => F p * Set.indicator t (fun _ => (1 : ℝ)) (p.1 q))
      = Set.indicator ((fun p : (Π i, X i) × Ω => p.1 q) ⁻¹' t) F := by
    funext p
    by_cases hp : p.1 q ∈ t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ _ from hp), mul_one]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ _ from hp), mul_zero]
  have hint : Integrable
      (fun p : (Π i, X i) × Ω => F p * Set.indicator t (fun _ => (1 : ℝ)) (p.1 q))
      ((Measure.infinitePi μ).prod ν) := by
    rw [heq]; exact hFint.indicator hset
  rw [integral_prod_symm _ hint, integral_prod_symm _ hFint]
  have hslice : ∀ y : Ω,
      ∫ ω, F (ω, y) * Set.indicator t (fun _ => (1 : ℝ)) (ω q) ∂(Measure.infinitePi μ)
        = (μ q t).toReal * ∫ ω, F (ω, y) ∂(Measure.infinitePi μ) := by
    intro y
    exact integral_mul_indicator_eval μ q c (fun ω => F (ω, y))
      (hF.comp (measurable_id.prodMk measurable_const)) (fun ω => hinv ω y) ht
  rw [integral_congr_ae (Filter.Eventually.of_forall hslice), integral_const_mul]

end LatticeProb

end
