/-
One coordinate of an infinite product against the rest, for a general function
of that coordinate.

`LatticeProb.integral_mul_indicator_eval` and its companion on a product
factorize the integral of a function that does not read a coordinate against the
INDICATOR of an event in that coordinate.  The conditional mean of a martingale
increment needs the same factorization against an arbitrary function of the
coordinate, and that is what these two lemmas are.  Nothing here is special to
the lattice.  Taken in from `Parking/Support/CoordIntegral.lean`, statements
verbatim with the namespace changed.
-/
import LatticeProb.Prob.Coordinate

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **One coordinate against the rest.**  A function that does not read the
coordinate `q` is independent of it, so the integral of their product
factorizes. -/
theorem integral_mul_eval (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (q : ι) (c : X q) (F : (Π i, X i) → ℝ) (hF : Measurable F)
    (hinv : ∀ ω, F (Function.update ω q c) = F ω)
    (g : X q → ℝ) (hg : Measurable g) :
    ∫ ω, F ω * g (ω q) ∂(Measure.infinitePi μ)
      = (∫ ω, F ω ∂(Measure.infinitePi μ)) * ∫ u, g u ∂(μ q) := by
  classical
  set P : Measure (Π i, X i) := Measure.infinitePi μ with hP
  have hind : IndepFun F (fun ω : Π i, X i => ω q) P :=
    indepFun_of_update_invariant μ c F hF hinv
  have hmapq : P.map (fun ω : Π i, X i => ω q) = μ q := Measure.infinitePi_map_eval μ q
  have hgae : AEStronglyMeasurable g (P.map fun ω : Π i, X i => ω q) := by
    rw [hmapq]; exact hg.aestronglyMeasurable
  have h := hind.integral_fun_comp_mul_comp (f := (id : ℝ → ℝ)) (g := g)
    hF.aemeasurable (measurable_pi_apply q).aemeasurable aestronglyMeasurable_id hgae
  simp only [id_eq] at h
  rw [h, integral_eval μ q g hg.aestronglyMeasurable]

/-- **One coordinate against the rest, on a product.**  The same factorization
when the function also reads a second, independent, source of randomness. -/
theorem integral_mul_eval_prod (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Ω : Type*} [MeasurableSpace Ω] (κ : Measure Ω) [IsProbabilityMeasure κ]
    (q : ι) (c : X q) (F : (Π i, X i) × Ω → ℝ) (hF : Measurable F)
    (hinv : ∀ (ω : Π i, X i) (y : Ω), F (Function.update ω q c, y) = F (ω, y))
    (g : X q → ℝ) (hg : Measurable g)
    (hFint : Integrable F ((Measure.infinitePi μ).prod κ))
    (hint : Integrable (fun p : (Π i, X i) × Ω => F p * g (p.1 q))
      ((Measure.infinitePi μ).prod κ)) :
    ∫ p, F p * g (p.1 q) ∂((Measure.infinitePi μ).prod κ)
      = (∫ p, F p ∂((Measure.infinitePi μ).prod κ)) * ∫ u, g u ∂(μ q) := by
  classical
  rw [integral_prod_symm _ hint, integral_prod_symm _ hFint]
  have hslice : ∀ y : Ω,
      ∫ ω, F (ω, y) * g (ω q) ∂(Measure.infinitePi μ)
        = (∫ ω, F (ω, y) ∂(Measure.infinitePi μ)) * ∫ u, g u ∂(μ q) := fun y =>
    integral_mul_eval μ q c (fun ω => F (ω, y))
      (hF.comp (measurable_id.prodMk measurable_const)) (fun ω => hinv ω y) g hg
  rw [integral_congr_ae (Filter.Eventually.of_forall hslice), integral_mul_const]

end LatticeProb

end
