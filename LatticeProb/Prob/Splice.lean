/-
Splicing two configurations along a set of coordinates, and the partial
integral it defines.

Every passage from a finite product to a countable one goes through the same
object: the configuration that reads `ω` on a set `S` of coordinates and a
second, independent configuration `η` off it.  Splicing is measure preserving
for the product of two copies of the field law, and the average of a functional
over the second configuration is the partial integral, a functional of the
coordinates in `S` alone.  That partial integral is the conditional expectation
of the functional on the coordinates in `S`, which is what the countable
Efron-Stein inequality needs, and it is written here without naming a
sigma-algebra.
-/
import Mathlib
import LatticeProb.Prob.PiSum
import LatticeProb.Prob.EfronStein

noncomputable section

namespace LatticeProb

open MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The configuration that reads `ω` on `S` and `η` off it. -/
def comb (S : Set ι) [DecidablePred (· ∈ S)] (ω η : Π i, X i) : Π i, X i :=
  fun i => if i ∈ S then ω i else η i

omit [∀ i, MeasurableSpace (X i)] in
theorem comb_apply_of_mem {S : Set ι} [DecidablePred (· ∈ S)] {ω η : Π i, X i} {i : ι}
    (hi : i ∈ S) : comb S ω η i = ω i := by simp [comb, hi]

omit [∀ i, MeasurableSpace (X i)] in
theorem comb_apply_of_notMem {S : Set ι} [DecidablePred (· ∈ S)] {ω η : Π i, X i} {i : ι}
    (hi : i ∉ S) : comb S ω η i = η i := by simp [comb, hi]

theorem measurable_comb (S : Set ι) [DecidablePred (· ∈ S)] :
    Measurable (fun p : (Π i, X i) × (Π i, X i) => comb S p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i ∈ S
  · simp only [comb, hi, if_pos]
    fun_prop
  · simp only [comb, hi, if_neg, not_false_iff]
    fun_prop

/-- **Splicing is measure preserving.**  Reading the field on `S` from one
independent copy and off `S` from another gives the field law again. -/
theorem measurePreserving_comb (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] :
    MeasurePreserving (fun p : (Π i, X i) × (Π i, X i) => comb S p.1 p.2)
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
  classical
  refine ⟨measurable_comb S, ?_⟩
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  have hpre : (fun p : (Π i, X i) × (Π i, X i) => comb S p.1 p.2) ⁻¹' Set.pi (↑s) t
      = (Set.pi (↑(s.filter (· ∈ S))) t) ×ˢ (Set.pi (↑(s.filter (fun i => i ∉ S))) t) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter,
      Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := h i hi.1
        rwa [comb_apply_of_mem hi.2] at this
      · have := h i hi.1
        rwa [comb_apply_of_notMem hi.2] at this
    · rintro ⟨h1, h2⟩ i hi
      by_cases hS : i ∈ S
      · rw [comb_apply_of_mem hS]; exact h1 i ⟨hi, hS⟩
      · rw [comb_apply_of_notMem hS]; exact h2 i ⟨hi, hS⟩
  rw [Measure.map_apply (measurable_comb S) (MeasurableSet.pi (Set.to_countable _) (fun i _ => ht i)), hpre,
    Measure.prod_prod, Measure.infinitePi_pi μ (fun i _ => ht i),
    Measure.infinitePi_pi μ (fun i _ => ht i),
    Finset.prod_filter_mul_prod_filter_not s (· ∈ S)]

omit [∀ i, MeasurableSpace (X i)] in
/-- Resampling one coordinate is splicing along the complement of that
coordinate. -/
theorem comb_compl_singleton [DecidableEq ι] (v : ι) (ω η : Π i, X i) :
    comb ({v}ᶜ : Set ι) ω η = Function.update ω v (η v) := by
  funext i
  by_cases hi : i = v
  · subst hi; simp [comb]
  · simp [comb, hi]

/-- **Resampling one coordinate preserves the field law.**  Replacing the value
at a single site by an independent draw from that site's law leaves the law of
the field unchanged.  This is the splice along the complement of the site,
composed with reading the second copy at that site. -/
theorem measurePreserving_update_infinitePi [DecidableEq ι] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (v : ι) :
    MeasurePreserving (fun q : (Π i, X i) × X v => Function.update q.1 v q.2)
      ((Measure.infinitePi μ).prod (μ v)) (Measure.infinitePi μ) := by
  have hg : MeasurePreserving (fun p : (Π i, X i) × (Π i, X i) => (p.1, p.2 v))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      ((Measure.infinitePi μ).prod (μ v)) :=
    (MeasurePreserving.id _).prod (measurePreserving_eval_infinitePi μ v)
  have hfg : MeasurePreserving
      ((fun q : (Π i, X i) × X v => Function.update q.1 v q.2) ∘
        (fun p : (Π i, X i) × (Π i, X i) => (p.1, p.2 v)))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
    have : ((fun q : (Π i, X i) × X v => Function.update q.1 v q.2) ∘
        (fun p : (Π i, X i) × (Π i, X i) => (p.1, p.2 v)))
        = fun p : (Π i, X i) × (Π i, X i) => comb ({v}ᶜ : Set ι) p.1 p.2 := by
      funext p
      exact (comb_compl_singleton v p.1 p.2).symm
    rw [this]
    exact measurePreserving_comb μ ({v}ᶜ : Set ι)
  have hfmeas : Measurable (fun q : (Π i, X i) × X v => Function.update q.1 v q.2) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases hi : i = v
    · subst hi
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne hi]
      fun_prop
  refine ⟨hfmeas, ?_⟩
  rw [← hg.map_eq, Measure.map_map hfmeas hg.measurable]
  exact hfg.map_eq

/-! ### Jensen for an average, with no integrability hypothesis -/

/-- **Jensen's inequality for the square of an average, in `ℝ≥0∞`.**  No
integrability is assumed: if the upper integral of the square is infinite the
bound is vacuous, and otherwise the square is integrable and so is the function,
on a probability space. -/
theorem ofReal_sq_integral_le_lintegral {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {g : α → ℝ} (hg : AEStronglyMeasurable g P) :
    ENNReal.ofReal ((∫ x, g x ∂P) ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P = ⊤
  · simp [hfin]
  · have hnn : (0 : α → ℝ) ≤ᵐ[P] fun x => g x ^ 2 :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    have hg2 : Integrable (fun x => g x ^ 2) P := by
      refine ⟨hg.pow 2, ?_⟩
      have henorm : ∀ x : α, ‖g x ^ 2‖ₑ = ENNReal.ofReal (g x ^ 2) := fun x =>
        Real.enorm_eq_ofReal (sq_nonneg _)
      unfold HasFiniteIntegral
      simp only [henorm]
      exact lt_of_le_of_ne le_top hfin
    have hgi : Integrable g P := by
      refine Integrable.mono ((integrable_const (1 : ℝ)).add hg2) hg ?_
      filter_upwards with x
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + g x ^ 2)]
      nlinarith [sq_abs (g x), abs_nonneg (g x), sq_nonneg (|g x| - 1)]
    calc ENNReal.ofReal ((∫ x, g x ∂P) ^ 2)
        ≤ ENNReal.ofReal (∫ x, g x ^ 2 ∂P) :=
          ENNReal.ofReal_le_ofReal (sq_integral_le P g hgi hg2)
      _ = ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P :=
          ofReal_integral_eq_lintegral_ofReal hg2 hnn

/-! ### The partial integral -/

/-- The average of `F` over the coordinates outside `S`, a functional of the
coordinates in `S` alone. -/
def partialInt (μ : ∀ i, Measure (X i)) (S : Set ι) [DecidablePred (· ∈ S)]
    (F : (Π i, X i) → ℝ) (ω : Π i, X i) : ℝ :=
  ∫ η, F (comb S ω η) ∂(Measure.infinitePi μ)

variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- The partial integral reads only the coordinates in `S`. -/
theorem partialInt_congr (S : Set ι) [DecidablePred (· ∈ S)] (F : (Π i, X i) → ℝ)
    {ω ω' : Π i, X i} (h : ∀ i ∈ S, ω i = ω' i) :
    partialInt μ S F ω = partialInt μ S F ω' := by
  unfold partialInt
  congr 1
  funext η
  congr 1
  funext i
  by_cases hi : i ∈ S
  · rw [comb_apply_of_mem hi, comb_apply_of_mem hi, h i hi]
  · rw [comb_apply_of_notMem hi, comb_apply_of_notMem hi]

theorem measurable_partialInt (S : Set ι) [DecidablePred (· ∈ S)] {F : (Π i, X i) → ℝ}
    (hF : Measurable F) : Measurable (partialInt μ S F) :=
  ((hF.comp (measurable_comb S)).stronglyMeasurable.integral_prod_right' (ν :=
    Measure.infinitePi μ)).measurable

/-- Splicing carries an integrable functional to an integrable functional of the
pair. -/
theorem integrable_comp_comb (S : Set ι) [DecidablePred (· ∈ S)] {F : (Π i, X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ)) :
    Integrable (fun p : (Π i, X i) × (Π i, X i) => F (comb S p.1 p.2))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) :=
  (measurePreserving_comb μ S).integrable_comp_of_integrable hF

/-- The partial integral of an integrable functional is integrable. -/
theorem integrable_partialInt (S : Set ι) [DecidablePred (· ∈ S)] {F : (Π i, X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ)) :
    Integrable (partialInt μ S F) (Measure.infinitePi μ) :=
  (integrable_comp_comb μ S hF).integral_prod_left

/-- The partial integral has the same mean as the functional. -/
theorem integral_partialInt (S : Set ι) [DecidablePred (· ∈ S)] {F : (Π i, X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ)) :
    ∫ ω, partialInt μ S F ω ∂(Measure.infinitePi μ) = ∫ ω, F ω ∂(Measure.infinitePi μ) := by
  have hmap := (measurePreserving_comb μ S).map_eq
  have hasm : AEStronglyMeasurable F
      (Measure.map (fun p : (Π i, X i) × (Π i, X i) => comb S p.1 p.2)
        ((Measure.infinitePi μ).prod (Measure.infinitePi μ))) := by
    rw [hmap]; exact hF.aestronglyMeasurable
  have h : ∫ p, F (comb S p.1 p.2) ∂((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      = ∫ ω, F ω ∂(Measure.infinitePi μ) := by
    rw [← integral_map (measurable_comb S).aemeasurable hasm, hmap]
  rw [← h, integral_prod _ (integrable_comp_comb μ S hF)]
  rfl

/-- **The defining property of the partial integral.**  Against a functional
that reads only the coordinates in `S`, the partial integral and the functional
itself have the same integral.  Holding for every such multiplier is the
statement that the partial integral is the conditional expectation on the
coordinates in `S`. -/
theorem integral_mul_partialInt (S : Set ι) [DecidablePred (· ∈ S)] {F g : (Π i, X i) → ℝ}
    (hg : ∀ ω η : Π i, X i, g (comb S ω η) = g ω)
    (hgF : Integrable (fun ω => g ω * F ω) (Measure.infinitePi μ)) :
    ∫ ω, g ω * partialInt μ S F ω ∂(Measure.infinitePi μ)
      = ∫ ω, g ω * F ω ∂(Measure.infinitePi μ) := by
  have hkey : Integrable
      (fun p : (Π i, X i) × (Π i, X i) => g (comb S p.1 p.2) * F (comb S p.1 p.2))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) :=
    integrable_comp_comb μ S hgF
  have hrw : (fun p : (Π i, X i) × (Π i, X i) => g (comb S p.1 p.2) * F (comb S p.1 p.2))
      = fun p : (Π i, X i) × (Π i, X i) => g p.1 * F (comb S p.1 p.2) := by
    funext p; rw [hg]
  rw [hrw] at hkey
  have h1 : ∫ p, g p.1 * F (comb S p.1 p.2)
        ∂((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      = ∫ ω, g ω * partialInt μ S F ω ∂(Measure.infinitePi μ) := by
    rw [integral_prod _ hkey]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only []
      rw [integral_const_mul]
      rfl)
  have h2 : ∫ p, g (comb S p.1 p.2) * F (comb S p.1 p.2)
        ∂((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      = ∫ ω, g ω * F ω ∂(Measure.infinitePi μ) := by
    have hmap := (measurePreserving_comb μ S).map_eq
    have hasm : AEStronglyMeasurable (fun ω => g ω * F ω)
        (Measure.map (fun p : (Π i, X i) × (Π i, X i) => comb S p.1 p.2)
          ((Measure.infinitePi μ).prod (Measure.infinitePi μ))) := by
      rw [hmap]; exact hgF.aestronglyMeasurable
    rw [← integral_map (measurable_comb S).aemeasurable hasm, hmap]
  rw [← h1, ← h2, hrw]

end LatticeProb

end
