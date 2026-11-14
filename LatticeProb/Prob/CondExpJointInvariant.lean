import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional expectation of a first-coordinate observable given a jointly invariant σ-algebra

Let a group `Γ` act on two measurable spaces `Ω₁` and `Ω₂`. Let `μ` be a probability measure on `Ω₁`
which is *ergodic* for the action, in the sense that every measurable, exactly `Γ`-invariant real
function is `μ`-a.e. constant, and let `m` be a `Γ`-invariant probability measure on `Ω₂`. Let `I` be
a sub-σ-algebra of the product σ-algebra each of whose sets agrees `μ ⊗ m`-a.e. with a measurable set
that is exactly invariant under the diagonal action `(x, y) ↦ (g • x, g • y)`.

Then for every integrable `G : Ω₁ → ℝ`, the conditional expectation of `(x, y) ↦ G x` given `I` is
a.s. the constant `∫ G dμ` (`condExp_fst_eq_integral_of_jointInvariant`): observables of the first
coordinate alone carry no information beyond their mean on the jointly invariant σ-algebra, even
though the pair need not be jointly ergodic.

The proof: for an exactly invariant measurable `t`, the section measure `x ↦ m {y | (x, y) ∈ t}` is
exactly invariant (`measureReal_prodMk_smul_preimage`), hence a.e. equal to a constant `c`; Fubini
gives `∫_t G(x) d(μ ⊗ m)(x, y) = c ∫ G dμ` and, for `G = 1`, `(μ ⊗ m)(t) = c`
(`exists_setIntegral_fst_eq_mul_integral`). Uniqueness of the conditional expectation concludes.

Implementation note: the sub-σ-algebra `I` is an explicit binder of type `MeasurableSpace (Ω₁ × Ω₂)`,
hence a local instance; the product σ-algebra is therefore named explicitly
(`Prod.instMeasurableSpace`) in the hypotheses `hI` and `hIinv`.
-/

namespace LatticeProb.JointInvariant

open MeasureTheory

variable {Γ Ω₁ Ω₂ : Type*} [Group Γ] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MulAction Γ Ω₁] [MulAction Γ Ω₂]

/-- For a set `t` invariant under the diagonal action and a `Γ`-invariant measure `m`, the section
measure `x ↦ m {y | (x, y) ∈ t}` is invariant under the action on the first coordinate. -/
theorem measureReal_prodMk_smul_preimage (m : Measure Ω₂)
    (hmeas₂ : ∀ g : Γ, Measurable (fun y : Ω₂ => g • y))
    (hm : ∀ g : Γ, m.map (fun y => g • y) = m) {t : Set (Ω₁ × Ω₂)} (ht : MeasurableSet t)
    (htinv : ∀ (g : Γ) x y, ((g • x, g • y) ∈ t ↔ (x, y) ∈ t)) (g : Γ) (x : Ω₁) :
    m.real (Prod.mk (g • x) ⁻¹' t) = m.real (Prod.mk x ⁻¹' t) := by
  have hset : Prod.mk (g • x) ⁻¹' t = (fun y => g⁻¹ • y) ⁻¹' (Prod.mk x ⁻¹' t) := by
    ext y
    simp only [Set.mem_preimage]
    rw [← htinv g⁻¹ (g • x) y, inv_smul_smul]
  rw [measureReal_def, measureReal_def, hset,
    ← Measure.map_apply (hmeas₂ g⁻¹) (measurable_prodMk_left ht), hm]

/-- Fubini for a first-coordinate observable on a measurable set `t`: the integral over `t` is the
`μ`-integral of `G` weighted by the section measure. -/
theorem setIntegral_fst_eq_integral_measureReal_mul (μ : Measure Ω₁) [IsFiniteMeasure μ]
    (m : Measure Ω₂) [IsFiniteMeasure m] {t : Set (Ω₁ × Ω₂)} (ht : MeasurableSet t)
    {G : Ω₁ → ℝ} (hG : Integrable G μ) :
    ∫ p in t, G p.1 ∂(μ.prod m) = ∫ x, m.real (Prod.mk x ⁻¹' t) * G x ∂μ := by
  have hGf : Integrable (fun p : Ω₁ × Ω₂ => G p.1) (μ.prod m) := hG.comp_fst m
  rw [← integral_indicator ht, integral_prod _ (hGf.indicator ht)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hsec : (fun y => t.indicator (fun p : Ω₁ × Ω₂ => G p.1) (x, y)) =
      (Prod.mk x ⁻¹' t).indicator (fun _ => G x) := by
    ext y
    by_cases hy : (x, y) ∈ t
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ Prod.mk x ⁻¹' t from hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show y ∉ Prod.mk x ⁻¹' t from hy)]
  simp only [hsec, integral_indicator (measurable_prodMk_left ht), setIntegral_const, smul_eq_mul]

/-- For an exactly jointly invariant measurable set `t`, under the ergodicity of `μ` and the
invariance of `m`, there is a constant `c` with `∫_t G(x) d(μ ⊗ m) = c ∫ G dμ` for every integrable
`G`, and `(μ ⊗ m)(t) = c`. -/
theorem exists_setIntegral_fst_eq_mul_integral (μ : Measure Ω₁) [IsProbabilityMeasure μ]
    (m : Measure Ω₂) [IsProbabilityMeasure m]
    (hmeas₂ : ∀ g : Γ, Measurable (fun y : Ω₂ => g • y))
    (hm : ∀ g : Γ, m.map (fun y => g • y) = m)
    (herg : ∀ f : Ω₁ → ℝ, Measurable f → (∀ (g : Γ) x, f (g • x) = f x) →
      ∃ c, f =ᵐ[μ] fun _ => c)
    {t : Set (Ω₁ × Ω₂)} (ht : MeasurableSet t)
    (htinv : ∀ (g : Γ) x y, ((g • x, g • y) ∈ t ↔ (x, y) ∈ t)) :
    ∃ c : ℝ, (μ.prod m).real t = c ∧
      ∀ G : Ω₁ → ℝ, Integrable G μ → ∫ p in t, G p.1 ∂(μ.prod m) = c * ∫ x, G x ∂μ := by
  have hfm : Measurable fun x : Ω₁ => m.real (Prod.mk x ⁻¹' t) :=
    (measurable_measure_prodMk_left ht).ennreal_toReal
  obtain ⟨c, hc⟩ := herg _ hfm (measureReal_prodMk_smul_preimage m hmeas₂ hm ht htinv)
  have key : ∀ G : Ω₁ → ℝ, Integrable G μ →
      ∫ p in t, G p.1 ∂(μ.prod m) = c * ∫ x, G x ∂μ := by
    intro G hG
    rw [setIntegral_fst_eq_integral_measureReal_mul μ m ht hG, ← integral_const_mul]
    exact integral_congr_ae (hc.mono fun x (hx : m.real (Prod.mk x ⁻¹' t) = c) => by simp only [hx])
  refine ⟨c, ?_, key⟩
  have h1 := key (fun _ => 1) (integrable_const 1)
  simpa only [setIntegral_const, smul_eq_mul, mul_one, integral_const, probReal_univ,
    measureReal_restrict_apply_univ] using h1

/-- **Observables of the first coordinate are deterministic given a jointly invariant σ-algebra.**
Let `μ` be ergodic for the action of `Γ` on `Ω₁` (every measurable exactly invariant real function
is a.e. constant), `m` a `Γ`-invariant probability measure on `Ω₂`, and `I` a sub-σ-algebra of the
product σ-algebra each of whose sets agrees `μ ⊗ m`-a.e. with a measurable set invariant under the
diagonal action. Then for every integrable `G`, `E[G(x) | I] = ∫ G dμ` a.s. under `μ ⊗ m`. -/
theorem condExp_fst_eq_integral_of_jointInvariant
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (m : Measure Ω₂) [IsProbabilityMeasure m]
    (hmeas₂ : ∀ g : Γ, Measurable (fun y : Ω₂ => g • y))
    (hm : ∀ g : Γ, m.map (fun y => g • y) = m)
    (herg : ∀ f : Ω₁ → ℝ, Measurable f → (∀ (g : Γ) x, f (g • x) = f x) →
      ∃ c, f =ᵐ[μ] fun _ => c)
    (I : MeasurableSpace (Ω₁ × Ω₂)) (hI : I ≤ Prod.instMeasurableSpace)
    (hIinv : ∀ s, MeasurableSet[I] s → ∃ t, MeasurableSet[Prod.instMeasurableSpace] t ∧
      (∀ (g : Γ) x y, ((g • x, g • y) ∈ t ↔ (x, y) ∈ t)) ∧ s =ᵐ[μ.prod m] t)
    (G : Ω₁ → ℝ) (hG : Integrable G μ) :
    (μ.prod m)[fun p => G p.1 | I] =ᵐ[μ.prod m] fun _ => ∫ x, G x ∂μ := by
  have hGf : Integrable (fun p : Ω₁ × Ω₂ => G p.1) (μ.prod m) := hG.comp_fst m
  refine (ae_eq_condExp_of_forall_setIntegral_eq hI hGf
    (fun s _ _ => (integrable_const _).integrableOn) (fun s hs _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  obtain ⟨t, ht, htinv, hst⟩ := hIinv s hs
  obtain ⟨c, hct, key⟩ := exists_setIntegral_fst_eq_mul_integral μ m hmeas₂ hm herg ht htinv
  show ∫ _ in s, (∫ x, G x ∂μ) ∂(μ.prod m) = ∫ p in s, G p.1 ∂(μ.prod m)
  rw [setIntegral_congr_set hst, setIntegral_congr_set hst, setIntegral_const, key G hG, hct,
    smul_eq_mul]

end LatticeProb.JointInvariant
