import LatticeProb.Prob.UpcrossGlueFixedPointUnique

/-!
# Uniqueness of product gluing fixed points

Probability laws with a common starting value are equal when both are fixed by gluing
an independent path that hits every negative integer level.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- Two probability laws initialized at the same value coincide if each is fixed by gluing
an independent path at every positive integer level. -/
theorem glueC_law_unique_of_product_fixed_points
    (ρ μ ν : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : ℝ)
    (hhit : ∀ᵐ (y : C(ℝ≥0, ℝ)) ∂ρ, ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hμzero : ∀ᵐ z ∂μ, z 0 = a) (hνzero : ∀ᵐ z ∂ν, z 0 = a)
    (hμ : ∀ n : ℕ, 0 < n → (ρ.prod μ).map (fun p => glueC (n : ℝ) p.1 p.2) = μ)
    (hν : ∀ n : ℕ, 0 < n → (ρ.prod ν).map (fun p => glueC (n : ℝ) p.1 p.2) = ν) :
    μ = ν := by
  let P := ρ.prod (μ.prod ν)
  let Y : C(ℝ≥0, ℝ) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) → C(ℝ≥0, ℝ) := Prod.fst
  let Z : C(ℝ≥0, ℝ) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) → C(ℝ≥0, ℝ) := fun p => p.2.1
  let W : C(ℝ≥0, ℝ) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) → C(ℝ≥0, ℝ) := fun p => p.2.2
  have hY : Measurable Y := measurable_fst
  have hZ : Measurable Z := measurable_fst.comp measurable_snd
  have hW : Measurable W := measurable_snd.comp measurable_snd
  have hhit' : ∀ᵐ p ∂P, ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (Y p : ℝ≥0 → ℝ) ≠ ⊤ :=
    (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := μ.prod ν)).ae hhit
  have hz : ∀ᵐ p ∂P, Z p 0 = a :=
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := μ.prod ν)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hμzero)
  have hw : ∀ᵐ p ∂P, W p 0 = a :=
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := μ.prod ν)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hνzero)
  have hzero : ∀ᵐ p ∂P, Z p 0 = W p 0 := by
    filter_upwards [hz, hw] with p hp hq
    exact hp.trans hq.symm
  have hYZ : P.map (fun p => (Y p, Z p)) = ρ.prod μ := by
    change (ρ.prod (μ.prod ν)).map (Prod.map id Prod.fst) = ρ.prod μ
    rw [← Measure.map_prod_map ρ (μ.prod ν) measurable_id measurable_fst,
      Measure.map_id, Measure.map_fst_prod]
    simp
  have hYW : P.map (fun p => (Y p, W p)) = ρ.prod ν := by
    change (ρ.prod (μ.prod ν)).map (Prod.map id Prod.snd) = ρ.prod ν
    rw [← Measure.map_prod_map ρ (μ.prod ν) measurable_id measurable_snd,
      Measure.map_id, Measure.map_snd_prod]
    simp
  apply glueC_law_unique_of_common_coupling P Y Z W μ ν hY hZ hW hhit' hzero
  · intro n hn
    change P.map ((fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueC (n : ℝ) p.1 p.2) ∘
      fun p => (Y p, Z p)) = μ
    rw [← Measure.map_map (measurable_glueC (n : ℝ)) (hY.prodMk hZ), hYZ]
    exact hμ n hn
  · intro n hn
    change P.map ((fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueC (n : ℝ) p.1 p.2) ∘
      fun p => (Y p, W p)) = ν
    rw [← Measure.map_map (measurable_glueC (n : ℝ)) (hY.prodMk hW), hYW]
    exact hν n hn

end LatticeProb
