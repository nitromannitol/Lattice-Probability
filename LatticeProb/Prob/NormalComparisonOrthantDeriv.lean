/-
# Li--Shao normal comparison: the orthant integration by parts (route item 4)

Continuing `LatticeProb/Prob/NormalComparison.lean` and
`LatticeProb/Prob/NormalComparisonOrthant.lean`: the smart-path derivative of the
orthant probability is a sum of boundary contributions `D_{ij}`, and each `D_{ij}`
is the `(m-2)`-fold integral of the density over the orthant of the remaining
coordinates (`route item 4`).  Getting there needs three measure-theory facts:

* **`lintegral_Iic_cons`** — the box-Fubini splitting of the orthant
  `Set.Iic b ⊆ (Fin (m+1) → ℝ)` into the last-`Fin.cons` coordinate times the tail
  orthant.  This is the exact declaration the previous packet named as missing
  (“no lemma of the form `∫ x in Set.univ.pi (fun i => Set.Iic (b i)), f x = …`”):
  Mathlib only has Fubini for *product* functions, not for a general function on a
  box.  It is proved here from `MeasureTheory.volume_preserving_piFinSuccAbove`.
* **`lintegral_Iic_cons₂`** — the two-coordinate iteration, peeling off coordinates
  `0` and `1` and leaving the `(m-2)`-fold orthant integral; this is the reduction
  route item 4 uses to isolate the two distinguished coordinates.
* **`integral_Iic_deriv_eq_of_tendsto`** — the one-coordinate half-line FTC on
  `(-∞, b]`: `∫_{x ≤ b} deriv f = f b - lim_{-∞} f`.  This is
  `MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'` in the shape the route
  consumes.
* **`integral_integral_mixed_deriv`** — route item 4 at `m = 2`: integrating the
  mixed second derivative `∂_x ∂_y p` over the quadrant `{x ≤ a} × {y ≤ b}` leaves
  `p` at the corner `(a, b)`.

## What is *not* here (the named gap)

The *general-`m`* form of `integral_integral_mixed_deriv` — selecting the two
distinguished coordinates `i`, `j` inside `Fin m`, applying `lintegral_Iic_cons`
to peel them off, and restating the mixed partial derivative as an explicit
`Fin m`-partial — is not landed; it is index bookkeeping over the two lemmas above.
On top of it, route item 3 (`hasDerivAt_orthant_multivariateGaussian`, the
covariance derivative) still needs `LatticeProb.multivariateGaussian_eq_withDensity`
together with `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, and route item 5
(`boundaryIntegral_le_bivariateDensity`) the conditional factorisation.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonOrthant

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

/-! ### Box-Fubini for the orthant of `Fin (m+1) → ℝ` -/

/-- **Box-Fubini for the orthant.**  Splitting off the `0`-th coordinate of the
orthant `Set.Iic b ⊆ (Fin (m+1) → ℝ)` turns the orthant integral into the iterated
integral over `Iic (b 0)` and the tail orthant `Iic (b ∘ Fin.succ)`.

This is the missing ingredient the previous packet named for route item 4: Mathlib's
`lintegral_prod` handles `Measure.pi`-splittings only through the measure-preserving
`MeasurableEquiv.piFinSuccAbove`, and no orthant (`Set.pi` of `Set.Iic`) version is
stated. -/
theorem lintegral_Iic_cons {m : ℕ} (b : Fin (m + 1) → ℝ)
    (f : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in Set.Iic b, f x
      = ∫⁻ x₀ in Set.Iic (b 0),
          ∫⁻ x' in Set.Iic (fun j : Fin m => b j.succ), f (Fin.cons x₀ x') := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving (⇑e) (volume : Measure (Fin (m + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hsymm : ∀ (x₀ : ℝ) (x' : Fin m → ℝ), e.symm (x₀, x') = Fin.cons x₀ x' := by
    intro x₀ x'
    funext j
    rw [show ⇑(e.symm) = ⇑(Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) 0) from rfl]
    rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero]
    exact Fin.cases rfl (fun i => rfl) j
  have hmeas : MeasurableSet (Set.Iic b) := by
    rw [show Set.Iic b = ⋂ i, {x : Fin (m + 1) → ℝ | x i ≤ b i} by
      ext x; simp [Pi.le_def]]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  have hpre : e.symm ⁻¹' (Set.Iic b)
      = Set.Iic (b 0) ×ˢ Set.Iic (fun j : Fin m => b j.succ) := by
    ext p
    obtain ⟨x₀, x'⟩ := p
    rw [Set.mem_preimage, hsymm, Set.mem_prod, Set.mem_Iic, Set.mem_Iic, Set.mem_Iic, Pi.le_def]
    constructor
    · intro h; exact ⟨h 0, fun j => h j.succ⟩
    · rintro ⟨h0, h'⟩ i
      refine Fin.cases h0 (fun j => h' j) i
  calc ∫⁻ x in Set.Iic b, f x
      = ∫⁻ x, (Set.Iic b).indicator f x := (lintegral_indicator hmeas f).symm
    _ = ∫⁻ p, (Set.Iic b).indicator f (e.symm p) :=
        (hmp.symm.lintegral_comp (hf.indicator hmeas)).symm
    _ = ∫⁻ p, (e.symm ⁻¹' (Set.Iic b)).indicator (fun q => f (e.symm q)) p := by
        refine lintegral_congr fun p => ?_
        by_cases hp : e.symm p ∈ Set.Iic b
        · rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem (show p ∈ e.symm ⁻¹' Set.Iic b from hp)]
        · rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem (show p ∉ e.symm ⁻¹' Set.Iic b from hp)]
    _ = ∫⁻ p in e.symm ⁻¹' (Set.Iic b), f (e.symm p) :=
        lintegral_indicator (hmeas.preimage e.symm.measurable) _
    _ = ∫⁻ p in Set.Iic (b 0) ×ˢ Set.Iic (fun j : Fin m => b j.succ), f (e.symm p) := by
        rw [hpre]
    _ = ∫⁻ x₀ in Set.Iic (b 0),
          ∫⁻ x' in Set.Iic (fun j : Fin m => b j.succ), f (e.symm (x₀, x')) :=
        setLIntegral_prod _ ((hf.comp e.symm.measurable).aemeasurable)
    _ = ∫⁻ x₀ in Set.Iic (b 0),
          ∫⁻ x' in Set.Iic (fun j : Fin m => b j.succ), f (Fin.cons x₀ x') := by
        refine lintegral_congr fun x₀ => lintegral_congr fun x' => ?_
        rw [hsymm]

/-- **Two-coordinate box-Fubini for the orthant.**  Iterating `lintegral_Iic_cons` peels off
coordinates `0` and `1`, leaving the `(m-2)`-fold orthant integral.  This is the reduction route
item 4 needs to isolate the two distinguished coordinates before applying the two-dimensional
fundamental theorem of calculus of `integral_integral_mixed_deriv`. -/
theorem lintegral_Iic_cons₂ {m : ℕ} (b : Fin (m + 2) → ℝ)
    (f : (Fin (m + 2) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in Set.Iic b, f x
      = ∫⁻ x₀ in Set.Iic (b 0), ∫⁻ x₁ in Set.Iic (b 1),
          ∫⁻ x'' in Set.Iic (fun j : Fin m => b j.succ.succ),
            f (Fin.cons x₀ (Fin.cons x₁ x'')) := by
  rw [lintegral_Iic_cons b f hf]
  refine lintegral_congr fun x₀ => ?_
  have hfc : Measurable fun x' : Fin (m + 1) → ℝ =>
      Fin.cons (α := fun _ : Fin (m + 2) => ℝ) x₀ x' := by
    rw [measurable_pi_iff]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (measurable_const : Measurable fun _ : Fin (m + 1) → ℝ => x₀)
    · simpa only [Fin.cons_succ] using (measurable_pi_apply j)
  have hf' : Measurable fun x' : Fin (m + 1) → ℝ =>
      f (Fin.cons (α := fun _ : Fin (m + 2) => ℝ) x₀ x') := hf.comp hfc
  rw [lintegral_Iic_cons (fun j : Fin (m + 1) => b j.succ)
    (fun x' => f (Fin.cons (α := fun _ : Fin (m + 2) => ℝ) x₀ x')) hf']
  refine lintegral_congr fun x₁ => lintegral_congr fun x'' => ?_
  congr 2

/-- **The mixed-derivative orthant integral, two coordinates** (route item 4 at `m = 2`).
Integrating `∂_x ∂_y p` over the quadrant `{x ≤ a} × {y ≤ b}` leaves `p` at the corner
`(a, b)`.  `px` is `∂_x p` and `pxy` is `∂_y ∂_x p`; the three limit hypotheses are the
"rapidly decaying" side conditions of the route. -/
theorem integral_integral_mixed_deriv (p : ℝ × ℝ → ℝ) (a b : ℝ)
    (px : ℝ → ℝ → ℝ) (pxy : ℝ → ℝ → ℝ)
    (hdy : ∀ x, ∀ y ∈ Set.Iic b, HasDerivAt (fun y' => px x y') (pxy x y) y)
    (hdy'int : ∀ x, IntegrableOn (fun y => pxy x y) (Set.Iic b))
    (hdy'lim : ∀ x, Tendsto (fun y => px x y) atBot (𝓝 0))
    (hdx : ∀ x ∈ Set.Iic a, HasDerivAt (fun x' => p (x', b)) (px x b) x)
    (hdx'int : IntegrableOn (fun x => px x b) (Set.Iic a))
    (hlim : Tendsto (fun x => p (x, b)) atBot (𝓝 0)) :
    ∫ x in Set.Iic a, ∫ y in Set.Iic b, pxy x y = p (a, b) := by
  have hinner : ∀ x, ∫ y in Set.Iic b, pxy x y = px x b := by
    intro x
    have h := integral_Iic_of_hasDerivAt_of_tendsto' (f := fun y => px x y)
      (f' := fun y => pxy x y) (a := b) (m := 0) (hdy x) (hdy'int x) (hdy'lim x)
    simpa using h
  calc ∫ x in Set.Iic a, ∫ y in Set.Iic b, pxy x y
      = ∫ x in Set.Iic a, px x b :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hinner x)
    _ = p (a, b) := by
        have h := integral_Iic_of_hasDerivAt_of_tendsto' (f := fun x => p (x, b))
          (f' := fun x => px x b) (a := a) (m := 0) hdx hdx'int hlim
        simpa using h

/-- **The half-line fundamental theorem of calculus** (route item 4, one coordinate).
On `(-∞, b]`, the integral of `deriv f` is `f b` minus the limit of `f` at `-∞`. -/
theorem integral_Iic_deriv_eq_of_tendsto (f : ℝ → ℝ) (b m : ℝ)
    (hderiv : ∀ x ∈ Set.Iic b, HasDerivAt f (deriv f x) x)
    (hint : IntegrableOn (deriv f) (Set.Iic b)) (hlim : Tendsto f atBot (𝓝 m)) :
    ∫ x in Set.Iic b, deriv f x = f b - m :=
  integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint hlim

end LatticeProb

#print axioms LatticeProb.lintegral_Iic_cons
#print axioms LatticeProb.lintegral_Iic_cons₂
#print axioms LatticeProb.integral_integral_mixed_deriv
#print axioms LatticeProb.integral_Iic_deriv_eq_of_tendsto
