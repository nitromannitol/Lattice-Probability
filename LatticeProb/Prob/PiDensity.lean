/-
Tonelli for a finite product, and the density of a finite product measure.

A product of measures given by densities is the product measure given by the
product of the densities.  Mathlib has the Bochner form of Fubini in `n`
variables but not the lower-integral form, and neither form of the density
statement; both are what a multivariate Gaussian density rests on.
-/
import Mathlib

noncomputable section

namespace LatticeProb

open MeasureTheory

open scoped ENNReal NNReal

/-- **Tonelli in `n` variables.**  The lower integral of a product of functions
of the separate coordinates is the product of the lower integrals. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] {ν : (i : Fin n) → Measure (X i)} [∀ i, SigmaFinite (ν i)]
    (f : (i : Fin n) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → X i, ∏ i, f i (x i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, f i x ∂(ν i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hF : Measurable fun x : (i : Fin (n + 1)) → X i => ∏ i, f i (x i) :=
        Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
      have hg : Measurable fun y : (i : Fin n) → X (Fin.succ i) =>
          ∏ i : Fin n, f (Fin.succ i) (y i) :=
        Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
      calc ∫⁻ x : (i : Fin (n + 1)) → X i, ∏ i, f i (x i) ∂(Measure.pi ν)
          = ∫⁻ p : X 0 × ((i : Fin n) → X (Fin.succ i)),
              f 0 p.1 * ∏ i : Fin n, f (Fin.succ i) (p.2 i)
              ∂((ν 0).prod (Measure.pi fun i => ν i.succ)) := by
            rw [← ((measurePreserving_piFinSuccAbove ν 0).symm).lintegral_comp hF]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
            rfl
        _ = (∫⁻ x, f 0 x ∂(ν 0))
              * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(ν i.succ) := by
            rw [lintegral_prod_mul (f := f 0)
              (g := fun y : (i : Fin n) → X (Fin.succ i) => ∏ i : Fin n, f (Fin.succ i) (y i))
              (hf 0).aemeasurable hg.aemeasurable,
              ih (fun i => f (Fin.succ i)) fun i => hf _]
        _ = ∏ i, ∫⁻ x, f i x ∂(ν i) := by rw [Fin.prod_univ_succ]

/-- **Tonelli for a finite product.** -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {ν : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i, f i (x i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, f i x ∂(ν i) := by
  classical
  set e := (Fintype.equivFin ι).symm with he
  have hF : Measurable fun x : (i : ι) → X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft X e)
      (Measure.pi fun i' => ν (e i')) (Measure.pi ν) := measurePreserving_piCongrLeft ν e
  rw [← hmp.lintegral_comp hF]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod (ν := fun i => ν (e i)) (fun i => f (e i))
    fun i => hf _]

/-- **A product of measures with densities has the product density.** -/
theorem pi_withDensity_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : (i : ι) → Measure (X i)) [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] :
    Measure.pi (fun i => (ν i).withDensity (f i))
      = (Measure.pi ν).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (ν i).withDensity (f i))
    (μ' := (Measure.pi ν).withDensity fun x => ∏ i, f i (x i)) fun s hs => ?_)
  have hF : Measurable fun x : (i : ι) → X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hpt : ∀ x : (i : ι) → X i,
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
        = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi (f i))).symm
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox,
    lintegral_congr hpt,
    lintegral_fintype_prod_eq_prod (fun i => (s i).indicator (f i))
      fun i => (hf i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

/-! ### The standard Gaussian on a finite product of lines -/

open ProbabilityTheory in
/-- **The standard Gaussian on `ι → ℝ` has the product density.** -/
theorem pi_gaussianReal_eq_withDensity {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1)
      = (volume : Measure (ι → ℝ)).withDensity fun x => ∏ i, gaussianPDF 0 1 (x i) := by
  haveI hprob : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]
    infer_instance
  have hone : ∀ _ : ι, (gaussianReal 0 1 : Measure ℝ)
      = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) :=
    fun _ => gaussianReal_of_var_ne_zero 0 one_ne_zero
  have hpi : Measure.pi (fun _ : ι => gaussianReal 0 1)
      = Measure.pi fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    congr 1
    funext i
    exact hone i
  rw [hpi, pi_withDensity_prod (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => gaussianPDF 0 1) (fun _ => measurable_gaussianPDF 0 1), ← volume_pi]

end LatticeProb

end
