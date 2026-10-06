/-
# Li--Shao normal comparison: the orthant transport to `EuclideanSpace`, signed form

Continuing `LatticeProb/Prob/NormalComparisonOrthantDeriv.lean`, where
`lintegral_orthant_eq` transports the `ℝ≥0∞`-valued orthant integral on
`EuclideanSpace ℝ (Fin n)` to `Set.Iic b ⊆ (Fin n → ℝ)` along the volume-preserving
`WithLp.toLp 2`.  Route item 4 integrates the *signed* mixed derivative `∂_i ∂_j p` of the
Gaussian density, so the Bochner integral and the integrability need the same transport.

* **`integral_orthant_eq`** — the Bochner form of the transport.  No hypothesis on `f` is
  needed: `MeasurePreserving.setIntegral_preimage_emb` applies to the measurable embedding
  `MeasurableEquiv.toLp 2 (Fin n → ℝ)`, and its preimage of the orthant
  `{y | ∀ i, y i ≤ b i}` is exactly `Set.Iic b`.
* **`integrableOn_orthant_iff`** — integrability on the orthant is equivalent to integrability
  of the pulled-back integrand on `Set.Iic b`, by
  `MeasurePreserving.integrableOn_comp_preimage` with the same preimage computation.
* **`integral_orthant_cons`** — the signed twin of `lintegral_orthant_cons`: the orthant
  integral on `EuclideanSpace ℝ (Fin (m+1))` as the iterated integral over the `0`-th
  coordinate and the tail orthant, obtained by chaining the two lemmas above with the
  Bochner box-Fubini `integral_Iic_cons`.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonOrthantDeriv

open MeasureTheory

namespace LatticeProb

/-- The preimage of the `EuclideanSpace` orthant `{y | ∀ i, y i ≤ b i}` under
`MeasurableEquiv.toLp 2` is the orthant `Set.Iic b ⊆ (Fin n → ℝ)`. -/
theorem preimage_toLp_orthant {n : ℕ} (b : Fin n → ℝ) :
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹'
      {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} = Set.Iic b := by
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic, Pi.le_def,
    MeasurableEquiv.coe_toLp]

/-- **Orthant transport to `EuclideanSpace`, Bochner form.**  Pushing the orthant integral
along the volume-preserving `WithLp.toLp 2` turns it into an integral over `Set.Iic b`.
No hypothesis on `f` is needed. -/
theorem integral_orthant_eq {n : ℕ} (b : Fin n → ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ y in {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}, f y
      = ∫ x in Set.Iic b, f (WithLp.toLp 2 x) := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin n → ℝ)))
      (volume : Measure (Fin n → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    PiLp.volume_preserving_toLp (Fin n)
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f
    {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}
  rw [preimage_toLp_orthant] at h
  exact h.symm

/-- **Integrability on the orthant transports to `Set.Iic b`.**  The integrand `f` is
integrable on the `EuclideanSpace` orthant exactly when its pull-back along `WithLp.toLp 2`
is integrable on `Set.Iic b`. -/
theorem integrableOn_orthant_iff {n : ℕ} (b : Fin n → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    IntegrableOn f {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} volume
      ↔ IntegrableOn (fun x => f (WithLp.toLp 2 x)) (Set.Iic b) volume := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin n → ℝ)))
      (volume : Measure (Fin n → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    PiLp.volume_preserving_toLp (Fin n)
  have h := hmp.integrableOn_comp_preimage
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (f := f)
    (s := {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i})
  rw [preimage_toLp_orthant] at h
  exact h.symm

/-- **The signed orthant box-Fubini on `EuclideanSpace`.**  The transport of
`integral_Iic_cons` to `EuclideanSpace ℝ (Fin (m+1))`, the setting of the Li--Shao route:
for `f` integrable on the orthant, the orthant integral is the iterated integral over
the `0`-th coordinate and the tail orthant. -/
theorem integral_orthant_cons {m : ℕ} (b : Fin (m + 1) → ℝ)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IntegrableOn f {y : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, y i ≤ b i} volume) :
    ∫ y in {y : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, y i ≤ b i}, f y
      = ∫ x₀ in Set.Iic (b 0), ∫ x' in Set.Iic (fun j : Fin m => b j.succ),
          f (WithLp.toLp 2 (Fin.cons (α := fun _ : Fin (m + 1) => ℝ) x₀ x')) := by
  rw [integral_orthant_eq b f]
  exact integral_Iic_cons b (fun x => f (WithLp.toLp 2 x)) ((integrableOn_orthant_iff b f).mp hf)

end LatticeProb
