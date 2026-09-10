/-
Revealing one coordinate of a product law, and the product rule for the
i.i.d. law.

`integral_coordinate_sections_int` is the reveal identity for an integrable
observable: integrating over the whole product field is the same as
integrating over the field with the `j`-th coordinate held out and then
integrating that coordinate back in.  It is the engine behind the
one-count-at-a-time inductions of the parking model's Step 2 and Step 3
(`parking.tex:2367-2412`), and it is generic in the index type and the
factor spaces.

`prod_coords` is the accompanying product rule: a product of one-site
functions over a finite set of sites is integrable for the i.i.d. law and
its mean is the product of the one-site means.  It supplies the exponential
moment of a finite sum of counts.
-/
import LatticeProb.Prob.Splice
import LatticeProb.Site
import LatticeProb.IID
import LatticeProb.Prob.CountableMeasurable

open MeasureTheory

noncomputable section

namespace LatticeProb

/-- Revealing one coordinate of a product law, for an integrable observable. -/
theorem integral_coordinate_sections_int {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [DecidableEq ι] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Π i, X i) → ℝ) (hf : Measurable f) (hi : Integrable f (Measure.infinitePi μ))
    (j : ι) :
    (∫ ω, f ω ∂(Measure.infinitePi μ)) =
      ∫ ω, ∫ a, f (Function.update ω j a) ∂(μ j) ∂(Measure.infinitePi μ) := by
  let P := Measure.infinitePi μ
  let T : (Π i, X i) × X j → Π i, X i := fun q => Function.update q.1 j q.2
  have hT : MeasurePreserving T (P.prod (μ j)) P :=
    measurePreserving_update_infinitePi μ j
  have hcomp : Integrable (fun q => f (T q)) (P.prod (μ j)) := hT.integrable_comp_of_integrable hi
  have he := integral_map (μ := P.prod (μ j)) (φ := T) (f := f) hT.measurable.aemeasurable
    (by rw [hT.map_eq]; exact hf.aestronglyMeasurable)
  rw [hT.map_eq] at he
  exact he.trans (integral_prod _ hcomp)

/-- Updating the count at a site outside `N` splits a sum over `insert x₀ N`. -/
theorem sum_update_insert {d : ℕ} (x₀ : Site d) (N : Finset (Site d)) (hx : x₀ ∉ N)
    (a : Site d → ℤ) (k : ℤ) :
    ∑ x ∈ insert x₀ N, (((Function.update a x₀ k) x : ℤ) : ℝ)
      = (k : ℝ) + ∑ x ∈ N, ((a x : ℤ) : ℝ) := by
  rw [Finset.sum_insert hx, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hx hy)]

/-- The same for a product of one-site functions. -/
theorem prod_update_insert {d : ℕ} (w : Site d → ℤ → ℝ) (x₀ : Site d)
    (N : Finset (Site d)) (hx : x₀ ∉ N) (a : Site d → ℤ) (k : ℤ) :
    ∏ y ∈ insert x₀ N, w y (Function.update a x₀ k y)
      = w x₀ k * ∏ y ∈ N, w y (a y) := by
  rw [Finset.prod_insert hx, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hx hy)]

/-- A product of one-site functions over a finite set of sites is measurable. -/
theorem measurable_prod_coords {d : ℕ} (w : Site d → ℤ → ℝ) (N : Finset (Site d)) :
    Measurable (fun a : Site d → ℤ => ∏ y ∈ N, w y (a y)) :=
  Finset.measurable_prod _ fun y _ =>
    (measurable_from_countable' (w y)).comp (measurable_pi_apply y)

/-- **The product rule for the i.i.d. law.**  A product of one-site functions
over a finite set of sites is integrable and its mean is the product of the
one-site means. -/
theorem prod_coords {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (w : Site d → ℤ → ℝ) (hwi : ∀ y, Integrable (w y) ν) (N : Finset (Site d)) :
    Integrable (fun a : Site d → ℤ => ∏ y ∈ N, w y (a y)) (iidLaw d ν)
    ∧ ∫ a, ∏ y ∈ N, w y (a y) ∂(iidLaw d ν) = ∏ y ∈ N, ∫ k, w y k ∂ν := by
  classical
  haveI : IsProbabilityMeasure (iidLaw d ν) := by
    unfold iidLaw; infer_instance
  induction N using Finset.induction_on with
  | empty => simp
  | @insert x₀ N hx ih =>
      obtain ⟨ihI, ihV⟩ := ih
      have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x₀ q.2)
          ((iidLaw d ν).prod ν) (iidLaw d ν) :=
        measurePreserving_update_infinitePi (fun _ : Site d => ν) x₀
      have hcomp : (fun q : (Site d → ℤ) × ℤ =>
            ∏ y ∈ insert x₀ N, w y (Function.update q.1 x₀ q.2 y))
          = fun q : (Site d → ℤ) × ℤ => (∏ y ∈ N, w y (q.1 y)) * w x₀ q.2 := by
        funext q
        rw [prod_update_insert w x₀ N hx q.1 q.2]
        ring
      have hprodint : Integrable
          (fun q : (Site d → ℤ) × ℤ => (∏ y ∈ N, w y (q.1 y)) * w x₀ q.2)
          ((iidLaw d ν).prod ν) := ihI.mul_prod (hwi x₀)
      have hmeas : Measurable (fun a : Site d → ℤ => ∏ y ∈ insert x₀ N, w y (a y)) :=
        measurable_prod_coords w (insert x₀ N)
      have hI : Integrable (fun a : Site d → ℤ => ∏ y ∈ insert x₀ N, w y (a y))
          (iidLaw d ν) := by
        refine (hu.integrable_comp hmeas.aestronglyMeasurable).mp ?_
        show Integrable (fun q : (Site d → ℤ) × ℤ =>
          ∏ y ∈ insert x₀ N, w y (Function.update q.1 x₀ q.2 y)) _
        rw [hcomp]
        exact hprodint
      refine ⟨hI, ?_⟩
      have he := integral_map (μ := (iidLaw d ν).prod ν)
        (φ := fun q : (Site d → ℤ) × ℤ => Function.update q.1 x₀ q.2)
        (f := fun a : Site d → ℤ => ∏ y ∈ insert x₀ N, w y (a y))
        hu.measurable.aemeasurable (by rw [hu.map_eq]; exact hmeas.aestronglyMeasurable)
      rw [hu.map_eq] at he
      rw [he]
      show ∫ q : (Site d → ℤ) × ℤ,
          ∏ y ∈ insert x₀ N, w y (Function.update q.1 x₀ q.2 y)
          ∂((iidLaw d ν).prod ν) = _
      rw [hcomp, integral_prod_mul (fun a : Site d → ℤ => ∏ y ∈ N, w y (a y)) (w x₀), ihV,
        Finset.prod_insert hx]
      ring

end LatticeProb

end