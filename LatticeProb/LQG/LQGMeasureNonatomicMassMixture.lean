import Mathlib
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Mixtures of whole-plane GFFs over the dyadic scales: LP form

LP copy of `HarmonicBalls/Proofs/Sec2/Mixture.lean` (the mixing probability measure `ν{k} ∝ (k+1)⁻²` on `ℕ`, its slice
bounds and its almost sure transfer) and of `HarmonicBalls/Proofs/Sec2/MixtureGFF.lean` (a mixture of whole-plane GFFs is a
whole-plane GFF). The Step `WholePlaneGFFMixtureStep` (`HarmonicBalls/Steps/Sec2/VolumeGrowth.lean:335`) is copied as the
definition `WholePlaneGFFMixtureStepLP` and PROVED here (`wholePlaneGFFMixtureStep_lp`), not assumed.

Argument: `IsWholePlaneGFF` determines every finite-dimensional law of the admissible observables (a centred Gaussian vector with
covariance `wholePlaneGFFCov`, Mathlib's `IsGaussian.ext_covarianceBilinDual`). Hence the field `(k, ω) ↦ (hC k ω, hcirc k ω)`
under `ν ⊗ P` has the same finite-dimensional laws as the field at `k = 0`, which is the device behind the uniform
Ding-Gwynne Lemma 3.8 of Berestycki-Powell (*Gaussian free field, Liouville quantum gravity and Gaussian multiplicative chaos*)
for the rescaled fields `h^{(k)} = h^ℂ(2^{-k} ·) - h^ℂ_{2^{-k}}(0)`.
The statement and the proof use no Harmonic-balls object.
-/

universe u

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory ProbabilityTheory Set LatticeProb.Gauss
open scoped ENNReal

/-! ### The mixing measure on the dyadic scales -/

/-- The weight `(k+1)⁻²`. -/
noncomputable def mixWeight (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (((k : ℝ) + 1) ^ 2)⁻¹

/-- The total weight `S = ∑ₖ (k+1)⁻²`. -/
noncomputable def mixMass : ℝ≥0∞ := ∑' k, mixWeight k

/-- The mixing probability measure `ν{k} = S⁻¹ (k+1)⁻²` on `ℕ`. -/
noncomputable def mixMeasure : Measure ℕ := mixMass⁻¹ • Measure.sum fun k => mixWeight k • Measure.dirac k

theorem summable_mixWeight : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem mixMass_ne_top : mixMass ≠ ∞ := by
  unfold mixMass mixWeight
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_mixWeight]
  exact ENNReal.ofReal_ne_top

theorem one_le_mixMass : 1 ≤ mixMass := by
  calc (1 : ℝ≥0∞) = mixWeight 0 := by simp [mixWeight]
    _ ≤ mixMass := ENNReal.le_tsum 0

theorem mixMass_ne_zero : mixMass ≠ 0 := (zero_lt_one.trans_le one_le_mixMass).ne'

theorem sum_apply_singleton (k : ℕ) :
    (Measure.sum fun j => mixWeight j • Measure.dirac j) {k} = mixWeight k := by
  rw [Measure.sum_apply _ (measurableSet_singleton k)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton k),
    indicator, mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [tsum_ite_eq]

theorem mixMeasure_singleton (k : ℕ) : mixMeasure {k} = mixMass⁻¹ * mixWeight k := by
  rw [mixMeasure, Measure.smul_apply, smul_eq_mul, sum_apply_singleton]

instance : IsProbabilityMeasure mixMeasure := by
  constructor
  rw [mixMeasure, Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.inv_mul_cancel mixMass_ne_zero mixMass_ne_top

/-- `ν{k}⁻¹ = S (k+1)²`. -/
theorem mixMeasure_singleton_inv (k : ℕ) :
    (mixMeasure {k})⁻¹ = ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) := by
  rw [mixMeasure_singleton, mixWeight, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
    (Or.inl (ENNReal.inv_ne_top.2 mixMass_ne_zero)), inv_inv, ENNReal.ofReal_inv_of_pos (by positivity),
    inv_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal mixMass_ne_top]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A bound for the mixture at the slice `k`: `P{ω | (k, ω) ∈ S} ≤ ν{k}⁻¹ (ν ⊗ P)(S)`. -/
theorem measure_slice_le [SFinite P] (S : Set (ℕ × Ω)) (k : ℕ) :
    P {ω | (k, ω) ∈ S} ≤ ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) * (mixMeasure.prod P) S := by
  have hsub : ({k} : Set ℕ) ×ˢ {ω | (k, ω) ∈ S} ⊆ S := by
    rintro ⟨j, ω⟩ ⟨hj, hω⟩
    have hj' : j = k := hj
    subst hj'
    exact hω
  have h1 : mixMeasure {k} * P {ω | (k, ω) ∈ S} ≤ (mixMeasure.prod P) S := by
    rw [← Measure.prod_prod]; exact measure_mono hsub
  have hk0 : mixMeasure {k} ≠ 0 := by
    rw [mixMeasure_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 mixMass_ne_top) (by simp [mixWeight]; positivity)
  have hktop : mixMeasure {k} ≠ ∞ := measure_ne_top _ _
  rw [← mixMeasure_singleton_inv]
  calc P {ω | (k, ω) ∈ S} = (mixMeasure {k})⁻¹ * (mixMeasure {k} * P {ω | (k, ω) ∈ S}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hk0 hktop, one_mul]
    _ ≤ (mixMeasure {k})⁻¹ * (mixMeasure.prod P) S := by gcongr

/-- Almost sure statements for every slice hold for the mixture. -/
theorem ae_mix_of_forall [SFinite P] {p : ℕ → Ω → Prop} (h : ∀ k, ∀ᵐ ω ∂P, p k ω) :
    ∀ᵐ x ∂(mixMeasure.prod P), p x.1 x.2 := by
  rw [ae_iff]
  set N : ℕ → Set Ω := fun k => toMeasurable P {ω | ¬ p k ω}
  have hN : ∀ k, P (N k) = 0 := fun k => by rw [measure_toMeasurable]; exact ae_iff.1 (h k)
  refine measure_mono_null (t := ⋃ k, ({k} : Set ℕ) ×ˢ N k) ?_ (measure_iUnion_null fun k => ?_)
  · rintro ⟨k, ω⟩ hx
    exact mem_iUnion.2 ⟨k, mem_singleton k, subset_toMeasurable P _ hx⟩
  · rw [Measure.prod_prod, hN, mul_zero]

/-! ### A mixture of whole-plane GFFs is a whole-plane GFF -/

/-- The covariance of two continuous linear functionals of a random vector in `ι → ℝ`, through the coordinates. -/
theorem covariance_strongDual_comp {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι]
    [DecidableEq ι] {X : Ω → ι → ℝ} (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) (L₁ L₂ : StrongDual ℝ (ι → ℝ)) :
    cov[fun ω => L₁ (X ω), fun ω => L₂ (X ω); P] =
      ∑ i, ∑ j, L₁ (fun k => if i = k then 1 else 0) * L₂ (fun k => if j = k then 1 else 0) *
        cov[fun ω => X ω i, fun ω => X ω j; P] := by
  have hL : ∀ L : StrongDual ℝ (ι → ℝ), ∀ x : ι → ℝ,
      L x = ∑ i, L (fun k => if i = k then 1 else 0) * x i := by
    intro L x
    have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h1 : (fun ω => L₁ (X ω)) = fun ω => ∑ i, L₁ (fun k => if i = k then 1 else 0) * X ω i :=
    funext fun ω => hL L₁ (X ω)
  have h2 : (fun ω => L₂ (X ω)) = fun ω => ∑ i, L₂ (fun k => if i = k then 1 else 0) * X ω i :=
    funext fun ω => hL L₂ (X ω)
  rw [h1, h2]
  rw [covariance_fun_sum_left (X := fun i ω => L₁ (fun k => if i = k then 1 else 0) * X ω i)
    (fun i => (hX i).const_mul _) (memLp_finsetSum _ fun j _ => (hX j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covariance_const_mul_left, covariance_fun_sum_right
    (X := fun j ω => L₂ (fun k => if j = k then 1 else 0) * X ω j) (fun j => (hX j).const_mul _) (hX i),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_right]; ring

/-- The vector of the observables in a finite set `I` of admissible observables. -/
def obsVector (I : Finset GFFObservable.Admissible) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) :
    I → ℝ :=
  I.restrict fun o : GFFObservable.Admissible => o.1.eval hC hcirc

/-- `IsWholePlaneGFF` determines the finite-dimensional laws (LP copy of `IsWholePlaneGFF.map_restrict_eq`). -/
theorem isWholePlaneGFF_map_restrict_eq {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc')
    (I : Finset GFFObservable.Admissible) :
    P.map (fun ω => obsVector I (hC ω) (hcirc ω)) = P.map (fun ω => obsVector I (hC' ω) (hcirc' ω)) := by
  classical
  have hP := h.isProbabilityMeasure
  have hG : HasGaussianLaw (fun ω => obsVector I (hC ω) (hcirc ω)) P :=
    h.isGaussianProcess.hasGaussianLaw I
  have hG' : HasGaussianLaw (fun ω => obsVector I (hC' ω) (hcirc' ω)) P :=
    h'.isGaussianProcess.hasGaussianLaw I
  have := hG.isGaussian_map
  have := hG'.isGaussian_map
  have hc : ∀ i : I, HasGaussianLaw (fun ω => obsVector I (hC ω) (hcirc ω) i) P := fun i =>
    h.isGaussianProcess.hasGaussianLaw_eval i.1
  have hc' : ∀ i : I, HasGaussianLaw (fun ω => obsVector I (hC' ω) (hcirc' ω) i) P := fun i =>
    h'.isGaussianProcess.hasGaussianLaw_eval i.1
  have hmean : ∀ {Y : Ω → I → ℝ}, AEMeasurable Y P → (∀ i, Integrable (fun ω => Y ω i) P) →
      (∀ i, ∫ ω, Y ω i ∂P = 0) → (P.map Y)[id] = 0 := by
    intro Y hY hint h0
    rw [integral_map hY aestronglyMeasurable_id]
    simp only [id_eq]
    funext i
    rw [eval_integral hint]
    exact h0 i
  apply IsGaussian.ext_covarianceBilinDual
  · rw [hmean hG.aemeasurable (fun i => (hc i).integrable) (fun i => h.integral_eq_zero i.1.1 i.1.2),
      hmean hG'.aemeasurable (fun i => (hc' i).integrable) (fun i => h'.integral_eq_zero i.1.1 i.1.2)]
  · ext L₁ L₂
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covariance_map (by fun_prop) (by fun_prop) hG.aemeasurable,
      covariance_map (by fun_prop) (by fun_prop) hG'.aemeasurable]
    simp only [Function.comp_def]
    rw [covariance_strongDual_comp (fun i => (hc i).memLp_two),
      covariance_strongDual_comp (fun i => (hc' i).memLp_two)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e1 := h.covariance_eq i.1.1 j.1.1 i.1.2 j.1.2
    have e2 := h'.covariance_eq i.1.1 j.1.1 i.1.2 j.1.2
    congr 1
    exact e1.trans e2.symm

/-- The law of a mixture of random variables with a common law. -/
theorem map_mixture_eq {E : Type*} [MeasurableSpace E] [SFinite P] {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → E} (hY : ∀ k, Measurable (Y k)) (hlaw : ∀ k, P.map (Y k) = P.map (Y 0)) :
    (ν.prod P).map (fun x => Y x.1 x.2) = P.map (Y 0) := by
  have hmeas : Measurable (fun x : ℕ × Ω => Y x.1 x.2) := measurable_from_prod_countable_right hY
  ext A hA
  rw [Measure.map_apply hmeas hA, Measure.prod_apply (hmeas hA)]
  have h : ∀ k, P (Prod.mk k ⁻¹' ((fun x : ℕ × Ω => Y x.1 x.2) ⁻¹' A)) = P.map (Y 0) A := by
    intro k
    rw [← hlaw k, Measure.map_apply (hY k) hA]; rfl
  simp_rw [h]
  rw [lintegral_const, measure_univ, mul_one]

/-- Almost sure statements for every slice hold for the mixture under `ν ⊗ P`. -/
theorem ae_prod_nat_of_forall [SFinite P] {ν : Measure ℕ} {p : ℕ → Ω → Prop}
    (h : ∀ k, ∀ᵐ ω ∂P, p k ω) : ∀ᵐ x ∂(ν.prod P), p x.1 x.2 := by
  rw [ae_iff]
  set N : ℕ → Set Ω := fun k => toMeasurable P {ω | ¬ p k ω}
  have hN : ∀ k, P (N k) = 0 := fun k => by rw [measure_toMeasurable]; exact ae_iff.1 (h k)
  refine measure_mono_null (t := ⋃ k, ({k} : Set ℕ) ×ˢ N k) ?_ (measure_iUnion_null fun k => ?_)
  · rintro ⟨k, ω⟩ hx
    exact mem_iUnion.2 ⟨k, mem_singleton k, subset_toMeasurable P _ hx⟩
  · rw [Measure.prod_prod, hN, mul_zero]

/-- The LP form of `WholePlaneGFFMixtureStep` (`HarmonicBalls/Steps/Sec2/VolumeGrowth.lean:335`). If `(hC k, hcirc k)` is a
whole-plane GFF under `P` for every `k : ℕ`, and `ν` is a probability measure on `ℕ`, then `(k, ω) ↦ (hC k ω, hcirc k ω)`
is a whole-plane GFF under `ν ⊗ P`. A definition, proved below. -/
def WholePlaneGFFMixtureStepLP : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : ℕ → Ω → (ℂ → ℝ) → ℝ) (hcirc : ℕ → Ω → ℝ → ℂ → ℝ)
    (ν : Measure ℕ), IsProbabilityMeasure ν → (∀ k, IsWholePlaneGFF P (hC k) (hcirc k)) →
    IsWholePlaneGFF (ν.prod P) (fun x => hC x.1 x.2) (fun x => hcirc x.1 x.2)

/-- `WholePlaneGFFMixtureStepLP` is proved (LP copy of `wholePlaneGFFMixtureStep_holds`). -/
theorem wholePlaneGFFMixtureStep_lp : WholePlaneGFFMixtureStepLP.{u} := by
  intro Ω _ P hC hcirc ν hν hG
  have hP := (hG 0).isProbabilityMeasure
  have hmeasO : ∀ k (o : GFFObservable.Admissible), Measurable fun ω => o.1.eval (hC k ω) (hcirc k ω) := by
    rintro k ⟨o, ho⟩
    cases o with
    | pairing φ => exact (hG k).measurable_pairing φ ho
    | circle r z => exact (hG k).measurable_circle r z ho
  have hmeasI : ∀ k (I : Finset GFFObservable.Admissible),
      Measurable fun ω => obsVector I (hC k ω) (hcirc k ω) := fun k I =>
    measurable_pi_iff.2 fun i => hmeasO k i.1
  have hlawI : ∀ I : Finset GFFObservable.Admissible,
      (ν.prod P).map (fun x => obsVector I (hC x.1 x.2) (hcirc x.1 x.2)) =
        P.map (fun ω => obsVector I (hC 0 ω) (hcirc 0 ω)) := fun I =>
    map_mixture_eq (Y := fun k ω => obsVector I (hC k ω) (hcirc k ω)) (fun k => hmeasI k I)
      (fun k => isWholePlaneGFF_map_restrict_eq (hG k) (hG 0) I)
  have hmeasM : ∀ I : Finset GFFObservable.Admissible,
      Measurable fun x : ℕ × Ω => obsVector I (hC x.1 x.2) (hcirc x.1 x.2) := fun I =>
    measurable_from_prod_countable_right fun k => hmeasI k I
  refine ⟨fun φ hφ => ?_, fun r z hr => ?_, ⟨fun I => ?_⟩, fun o ho => ?_, fun o o' ho ho' => ?_, ?_⟩
  · exact measurable_from_prod_countable_right fun k => (hG k).measurable_pairing φ hφ
  · exact measurable_from_prod_countable_right fun k => (hG k).measurable_circle r z hr
  · refine ⟨(hmeasM I).aemeasurable, ?_⟩
    have h := hlawI I
    simp only [obsVector] at h
    rw [h]
    exact ((hG 0).isGaussianProcess.hasGaussianLaw I).isGaussian_map
  · classical
    set I : Finset GFFObservable.Admissible := {⟨o, ho⟩}
    set i : I := ⟨⟨o, ho⟩, Finset.mem_singleton_self _⟩
    have hg : Measurable fun v : I → ℝ => v i := measurable_pi_apply i
    have h1 := integral_map (μ := ν.prod P) (hmeasM I).aemeasurable hg.aestronglyMeasurable
    have h2 := integral_map (μ := P) (hmeasI 0 I).aemeasurable hg.aestronglyMeasurable
    rw [hlawI I] at h1
    exact h1.symm.trans (h2.trans ((hG 0).integral_eq_zero o ho))
  · classical
    set I : Finset GFFObservable.Admissible := {⟨o, ho⟩, ⟨o', ho'⟩}
    set i : I := ⟨⟨o, ho⟩, Finset.mem_insert_self _ _⟩
    set j : I := ⟨⟨o', ho'⟩, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    have hgi : Measurable fun v : I → ℝ => v i := measurable_pi_apply i
    have hgj : Measurable fun v : I → ℝ => v j := measurable_pi_apply j
    have h1 := covariance_map (μ := ν.prod P) hgi.aestronglyMeasurable hgj.aestronglyMeasurable
      (hmeasM I).aemeasurable
    have h2 := covariance_map (μ := P) hgi.aestronglyMeasurable hgj.aestronglyMeasurable
      (hmeasI 0 I).aemeasurable
    rw [hlawI I] at h1
    exact h1.symm.trans (h2.trans ((hG 0).covariance_eq o o' ho ho'))
  · exact ae_prod_nat_of_forall (p := fun k ω => ContinuousOn (fun p : ℝ × ℂ => hcirc k ω p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ)) fun k => (hG k).ae_continuousOn_circle

end LatticeProb.LQG.LQGMeasureNonatomicMass
