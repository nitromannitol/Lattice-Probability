import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

Two consequences: an `I`-measurable function that agrees a.s. with a function of the first
coordinate is a.s. constant (`exists_ae_eq_const_of_ae_eq_fst`, via `arctan`, without integrability),
and, for any sub-σ-algebra, the conditional expectations of an a.s. antitone, nonnegative sequence
tending to `0` with integrable first term tend to `0` a.s. (`ae_tendsto_condExp_zero_of_antitone`).

Implementation note: the sub-σ-algebra `I` is an explicit binder of type `MeasurableSpace (Ω₁ × Ω₂)`,
hence a local instance; the product σ-algebra is therefore named explicitly
(`Prod.instMeasurableSpace`) in the hypotheses `hI` and `hIinv`.
-/

namespace LatticeProb.JointInvariant

open MeasureTheory Filter Topology

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

/-- **An `I`-measurable function of the first coordinate is a.s. constant.** Under the hypotheses of
`condExp_fst_eq_integral_of_jointInvariant`, if `F` is `I`-measurable and `F = G(x)` a.s. for a
measurable `G : Ω₁ → ℝ`, then `F` is a.s. constant. No integrability is assumed: the argument is
applied to the bounded injective function `arctan`. -/
theorem exists_ae_eq_const_of_ae_eq_fst
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (m : Measure Ω₂) [IsProbabilityMeasure m]
    (hmeas₂ : ∀ g : Γ, Measurable (fun y : Ω₂ => g • y))
    (hm : ∀ g : Γ, m.map (fun y => g • y) = m)
    (herg : ∀ f : Ω₁ → ℝ, Measurable f → (∀ (g : Γ) x, f (g • x) = f x) →
      ∃ c, f =ᵐ[μ] fun _ => c)
    (I : MeasurableSpace (Ω₁ × Ω₂)) (hI : I ≤ Prod.instMeasurableSpace)
    (hIinv : ∀ s, MeasurableSet[I] s → ∃ t, MeasurableSet[Prod.instMeasurableSpace] t ∧
      (∀ (g : Γ) x y, ((g • x, g • y) ∈ t ↔ (x, y) ∈ t)) ∧ s =ᵐ[μ.prod m] t)
    (F : Ω₁ × Ω₂ → ℝ) (hF : StronglyMeasurable[I] F) (G : Ω₁ → ℝ) (hG : Measurable G)
    (hFG : F =ᵐ[μ.prod m] fun p => G p.1) :
    ∃ c : ℝ, F =ᵐ[μ.prod m] fun _ => c := by
  have hb : ∀ y : ℝ, ‖Real.arctan y‖ ≤ Real.pi / 2 := fun y => by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩
  have hAm : StronglyMeasurable[I] (fun p => Real.arctan (F p)) :=
    Real.continuous_arctan.comp_stronglyMeasurable hF
  have hAFint : Integrable (fun p => Real.arctan (F p)) (μ.prod m) :=
    (integrable_const (Real.pi / 2)).mono' (hAm.mono hI).aestronglyMeasurable
      (ae_of_all _ fun p => hb (F p))
  have hAG : Integrable (fun x => Real.arctan (G x)) μ :=
    (integrable_const (Real.pi / 2)).mono'
      (Real.continuous_arctan.measurable.comp hG).aestronglyMeasurable
      (ae_of_all _ fun x => hb (G x))
  have h1 : (μ.prod m)[fun p => Real.arctan (F p) | I] = fun p => Real.arctan (F p) :=
    condExp_of_stronglyMeasurable hI hAm hAFint
  have h2 : (μ.prod m)[fun p => Real.arctan (F p) | I] =ᵐ[μ.prod m]
      (μ.prod m)[fun p => Real.arctan (G p.1) | I] :=
    condExp_congr_ae (hFG.mono fun p (hp : F p = G p.1) =>
      show Real.arctan (F p) = Real.arctan (G p.1) by rw [hp])
  have h3 := condExp_fst_eq_integral_of_jointInvariant μ m hmeas₂ hm herg I hI hIinv
    (fun x => Real.arctan (G x)) hAG
  have h4 := h2.trans h3
  rw [h1] at h4
  refine ⟨Real.tan (∫ x, Real.arctan (G x) ∂μ), h4.mono fun p hp => ?_⟩
  have hp' : Real.arctan (F p) = ∫ x, Real.arctan (G x) ∂μ := hp
  show F p = Real.tan (∫ x, Real.arctan (G x) ∂μ)
  rw [← hp', Real.tan_arctan]

/-- **Conditional monotone convergence to `0`.** For any sub-σ-algebra `m` and a finite measure, if
`0 ≤ F j` and `j ↦ F j` is antitone a.s., `F j → 0` a.s., each `F j` is a.e. strongly measurable and
`F 0` is integrable, then `E[F j | m] → 0` a.s. -/
theorem ae_tendsto_condExp_zero_of_antitone {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ m₀) {F : ℕ → Ω → ℝ}
    (hmeas : ∀ j, AEStronglyMeasurable (F j) μ) (hint0 : Integrable (F 0) μ)
    (hnn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ F j ω) (hanti : ∀ᵐ ω ∂μ, Antitone fun j => F j ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun j => F j ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun j => μ[F j | m] ω) atTop (𝓝 0) := by
  have hdom : ∀ j, ∀ᵐ ω ∂μ, ‖F j ω‖ ≤ F 0 ω := fun j => by
    filter_upwards [hnn, hanti] with ω h0 ha
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 j)]
    exact ha (Nat.zero_le j)
  have hint : ∀ j, Integrable (F j) μ := fun j => hint0.mono' (hmeas j) (hdom j)
  have hCle : ∀ j, μ[F (j + 1) | m] ≤ᵐ[μ] μ[F j | m] := fun j =>
    condExp_mono (hint (j + 1)) (hint j) (by
      filter_upwards [hanti] with ω ha using ha (Nat.le_succ j))
  have hCnn : ∀ j, 0 ≤ᵐ[μ] μ[F j | m] := fun j =>
    condExp_nonneg (by filter_upwards [hnn] with ω h using h j)
  set L : Ω → ℝ := fun ω => ⨅ j, μ[F j | m] ω with hL
  have hgood : ∀ᵐ ω ∂μ, Tendsto (fun j => μ[F j | m] ω) atTop (𝓝 (L ω)) := by
    filter_upwards [ae_all_iff.2 hCle, ae_all_iff.2 hCnn] with ω hle h0
    exact tendsto_atTop_ciInf (antitone_nat_of_succ_le (f := fun j => μ[F j | m] ω) hle) ⟨0, by
      rintro _ ⟨j, rfl⟩
      exact h0 j⟩
  have hCm : ∀ j, AEStronglyMeasurable (μ[F j | m]) μ := fun j =>
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hLm : AEStronglyMeasurable L μ := aestronglyMeasurable_of_tendsto_ae atTop hCm hgood
  have hLnn : 0 ≤ᵐ[μ] L := by
    filter_upwards [ae_all_iff.2 hCnn] with ω h
    exact le_ciInf h
  have hCbound : ∀ j, ∀ᵐ ω ∂μ, ‖μ[F j | m] ω‖ ≤ μ[F 0 | m] ω := fun j => by
    filter_upwards [ae_all_iff.2 hCle, ae_all_iff.2 hCnn] with ω hle h
    rw [Real.norm_eq_abs, abs_of_nonneg (h j)]
    exact antitone_nat_of_succ_le (f := fun j => μ[F j | m] ω) hle (Nat.zero_le j)
  have hLle : ∀ᵐ ω ∂μ, ‖L ω‖ ≤ μ[F 0 | m] ω := by
    filter_upwards [ae_all_iff.2 hCnn, hLnn] with ω h hL0
    rw [Real.norm_eq_abs, abs_of_nonneg hL0]
    exact ciInf_le ⟨0, by
      rintro _ ⟨j, rfl⟩
      exact h j⟩ 0
  have h1 : Tendsto (fun j => ∫ ω, μ[F j | m] ω ∂μ) atTop (𝓝 (∫ ω, L ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence _ hCm integrable_condExp hCbound hgood
  have h2 : Tendsto (fun j => ∫ ω, μ[F j | m] ω ∂μ) atTop (𝓝 0) := by
    simp_rw [integral_condExp hm]
    simpa using tendsto_integral_of_dominated_convergence (F 0) hmeas hint0 hdom hlim
  have hLint : Integrable L μ := integrable_condExp.mono' hLm hLle
  have hL0 : L =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hLnn hLint).1 (tendsto_nhds_unique h1 h2)
  filter_upwards [hgood, hL0] with ω hω h0
  rw [h0] at hω
  exact hω

end LatticeProb.JointInvariant
