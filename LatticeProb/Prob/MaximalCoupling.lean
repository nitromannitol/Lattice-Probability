import Mathlib

/-!
# Maximal coupling of two probability measures

If two probability measures `μ` and `ν` on a measurable space with measurable diagonal satisfy
`μ S ≤ ν S + a` for every measurable `S` (total variation distance at most `a`), then there is a
coupling `ρ` of `μ` and `ν` (a measure on the product with marginals `μ` and `ν`) that gives mass at
most `a` to the off-diagonal `{p | p.1 ≠ p.2}`.

* `LatticeProb.exists_coupling_ne_le_of_forall_le_add`: the coupling, for every measurable space with
  measurable diagonal (for instance every second countable Borel space).

The construction is the classical one: with `f = dμ/d(μ+ν)`, `g = dν/d(μ+ν)` and `m = min f g`, the
coupling is the image of `m • (μ+ν)` under the diagonal plus the normalised product of the
remainders `(f - m) • (μ+ν)` and `(g - m) • (μ+ν)`.
-/

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal

namespace LatticeProb

variable {α : Type*} [MeasurableSpace α]

/-- **Maximal coupling.**  If `μ S ≤ ν S + a` for every measurable `S`, there is a coupling of `μ` and
`ν` under which the two coordinates differ with probability at most `a`. -/
theorem exists_coupling_ne_le_of_forall_le_add (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ≥0∞} (hTV : ∀ S : Set α, MeasurableSet S → μ S ≤ ν S + a)
    (hΔ : MeasurableSet {p : α × α | p.1 = p.2}) :
    ∃ ρ : Measure (α × α), ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν ∧
      ρ {p : α × α | p.1 ≠ p.2} ≤ a := by
  classical
  let l : Measure α := μ + ν
  have hμl : μ ≪ l := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνl : ν ≪ l := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  let f : α → ℝ≥0∞ := μ.rnDeriv l
  let g : α → ℝ≥0∞ := ν.rnDeriv l
  have hf : Measurable f := Measure.measurable_rnDeriv μ l
  have hg : Measurable g := Measure.measurable_rnDeriv ν l
  have hfμ : l.withDensity f = μ := Measure.withDensity_rnDeriv_eq μ l hμl
  have hgν : l.withDensity g = ν := Measure.withDensity_rnDeriv_eq ν l hνl
  let m : α → ℝ≥0∞ := fun x => min (f x) (g x)
  have hm : Measurable m := hf.min hg
  have hmf : ∀ x, m x ≤ f x := fun x => min_le_left _ _
  have hmg : ∀ x, m x ≤ g x := fun x => min_le_right _ _
  let P : Measure α := l.withDensity m
  let μ1 : Measure α := l.withDensity (f - m)
  let ν1 : Measure α := l.withDensity (g - m)
  have hμs : P + μ1 = μ := by
    have h1 : P + μ1 = l.withDensity f := by
      show l.withDensity m + l.withDensity (f - m) = l.withDensity f
      rw [← withDensity_add_left hm]
      congr 1
      funext x
      exact add_tsub_cancel_of_le (hmf x)
    exact h1.trans hfμ
  have hνs : P + ν1 = ν := by
    have h1 : P + ν1 = l.withDensity g := by
      show l.withDensity m + l.withDensity (g - m) = l.withDensity g
      rw [← withDensity_add_left hm]
      congr 1
      funext x
      exact add_tsub_cancel_of_le (hmg x)
    exact h1.trans hgν
  have hμ1fin : IsFiniteMeasure μ1 :=
    isFiniteMeasure_of_le μ ((Measure.le_add_left (le_refl μ1) : μ1 ≤ P + μ1).trans hμs.le)
  have hν1fin : IsFiniteMeasure ν1 :=
    isFiniteMeasure_of_le ν ((Measure.le_add_left (le_refl ν1) : ν1 ≤ P + ν1).trans hνs.le)
  have hPfin : IsFiniteMeasure P :=
    isFiniteMeasure_of_le μ ((Measure.le_add_right (le_refl P) : P ≤ P + μ1).trans hμs.le)
  have hPtop : P Set.univ ≠ ∞ := measure_ne_top P _
  -- the total masses of the remainders agree
  have hu1 : P Set.univ + μ1 Set.univ = 1 := by
    have := congrArg (fun κ : Measure α => κ Set.univ) hμs
    simpa using this
  have hu2 : P Set.univ + ν1 Set.univ = 1 := by
    have := congrArg (fun κ : Measure α => κ Set.univ) hνs
    simpa using this
  have htt : μ1 Set.univ = ν1 Set.univ := by
    have h := hu1.trans hu2.symm
    exact (ENNReal.add_right_inj hPtop).1 h
  set t : ℝ≥0∞ := μ1 Set.univ with ht
  have htle : t ≤ 1 := by
    rw [← hu1]
    exact le_add_self
  have htop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
  -- the remainder mass is at most `a`
  have hta : t ≤ a := by
    let S : Set α := {x | g x < f x}
    have hS : MeasurableSet S := measurableSet_lt hg hf
    have hμ1c : μ1 Sᶜ = 0 := by
      rw [withDensity_apply _ hS.compl]
      refine (setLIntegral_congr_fun hS.compl fun x hx => ?_).trans lintegral_zero
      have hx' : f x ≤ g x := not_lt.1 hx
      show f x - min (f x) (g x) = 0
      rw [min_eq_left hx']
      exact tsub_self _
    have hν1S : ν1 S = 0 := by
      rw [withDensity_apply _ hS]
      refine (setLIntegral_congr_fun hS fun x hx => ?_).trans lintegral_zero
      have hx' : g x < f x := hx
      show g x - min (f x) (g x) = 0
      rw [min_eq_right hx'.le]
      exact tsub_self _
    have hμ1S : μ1 S = t := by
      have := measure_add_measure_compl (μ := μ1) hS
      rw [hμ1c, add_zero] at this
      exact this
    have h1 : μ S = P S + t := by
      rw [← hμs, Measure.add_apply, hμ1S]
    have h2 : ν S = P S := by
      rw [← hνs, Measure.add_apply, hν1S, add_zero]
    have h3 := hTV S hS
    rw [h1, h2] at h3
    have hPS : P S ≠ ∞ := measure_ne_top P S
    exact (ENNReal.add_le_add_iff_left hPS).1 h3
  have hsm1 : t⁻¹ • (t • μ1) = μ1 := by
    by_cases h0 : t = 0
    · have : μ1 = 0 := Measure.measure_univ_eq_zero.1 h0
      simp [this]
    · rw [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul]
  have hsm2 : t⁻¹ • (t • ν1) = ν1 := by
    by_cases h0 : t = 0
    · have : ν1 = 0 := Measure.measure_univ_eq_zero.1 (htt.symm.trans h0)
      simp [this]
    · rw [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul]
  have hdiag : Measurable fun x : α => (x, x) := measurable_id.prodMk measurable_id
  have hΔc : MeasurableSet {p : α × α | p.1 ≠ p.2} := hΔ.compl
  have hdiag0 : (P.map fun x : α => (x, x)) {p : α × α | p.1 ≠ p.2} = 0 := by
    rw [Measure.map_apply hdiag hΔc]
    simp
  have hpu : (μ1.prod ν1) Set.univ = t * t := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, ← ht, ← htt]
  have hcancel : t⁻¹ * (t * t) = t := by
    by_cases h0 : t = 0
    · simp [h0]
    · rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
  refine ⟨(P.map fun x : α => (x, x)) + t⁻¹ • μ1.prod ν1, ?_, ?_, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_map measurable_fst hdiag, Measure.map_smul,
      Measure.map_fst_prod, ← htt, hsm1,
      show (Prod.fst ∘ fun x : α => (x, x)) = id from rfl, Measure.map_id]
    · exact hμs
    · exact measurable_fst.aemeasurable
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_map measurable_snd hdiag, Measure.map_smul,
      Measure.map_snd_prod, ← ht, hsm2,
      show (Prod.snd ∘ fun x : α => (x, x)) = id from rfl, Measure.map_id]
    · exact hνs
    · exact measurable_snd.aemeasurable
  · rw [Measure.add_apply, hdiag0, zero_add, Measure.smul_apply, smul_eq_mul]
    calc t⁻¹ * (μ1.prod ν1) {p : α × α | p.1 ≠ p.2}
        ≤ t⁻¹ * (μ1.prod ν1) Set.univ := mul_le_mul' (le_refl _) (measure_mono (Set.subset_univ _))
      _ = t := by rw [hpu, hcancel]
      _ ≤ a := hta

end LatticeProb
