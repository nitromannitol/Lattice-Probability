import Mathlib

/-!
# Vitali convergence for the sections of a product measure

Let `μ` and `ν` be finite measures and let `f n` be a sequence of real functions on `α × β` that is uniformly
integrable for `μ.prod ν` and converges almost everywhere to `g`. By the Vitali convergence theorem `f n → g` in
`L¹(μ.prod ν)`, so, by the Tonelli theorem, the `L¹(ν)` distances of the sections `y ↦ f n (x, y)` and
`y ↦ g (x, y)` tend to `0` in `L¹(μ)`. Along a subsequence they tend to `0` for `μ`-almost every `x`, and the
section integrals `∫ f n (x, y) dν(y)` converge to `∫ g (x, y) dν(y)` along that subsequence, for `μ`-almost every
`x`.

A typical use is the identification of the limit of quenched expectations: if moreover the section integrals
converge to `L x` along the full sequence, for `μ`-almost every `x`, then `∫ g (x, y) dν(y) = L x` for `μ`-almost
every `x`. The same holds for nonnegative extended real functions whose real parts are uniformly integrable.

## Main results

* `integrable_of_ae_tendsto_of_eLpNorm_le`: an almost everywhere limit of a sequence bounded in `L¹` is integrable;
* `exists_strictMono_ae_tendsto_integral_section`: almost everywhere convergence of the section integrals along a
  subsequence;
* `ae_integral_section_eq_of_uniformIntegrable`: identification of the limit of the section integrals;
* `ae_lintegral_section_eq_of_uniformIntegrable`: the same for lower Lebesgue integrals of nonnegative functions.
-/

namespace LatticeProb.Prob

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- An almost everywhere limit of a sequence of real functions that is bounded in `L¹` is integrable (Fatou's
lemma for the `L¹` norm). -/
theorem integrable_of_ae_tendsto_of_eLpNorm_le {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {C : ℝ≥0} (hC : ∀ n, eLpNorm (f n) 1 μ ≤ C)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Integrable g μ := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  exact memLp_one_iff_integrable.1 (memLp_iff.2 (((Lp.eLpNorm_lim_le_liminf_eLpNorm hf g hg hfg).trans
    (liminf_le_of_frequently_le' (Frequently.of_forall hC))).trans_lt ENNReal.coe_lt_top))

/-- **Vitali convergence for the sections of a product measure.** If `f n → g` almost everywhere on `α × β` and the
sequence `f n` is uniformly integrable for the finite product measure `μ.prod ν`, then along a subsequence the
section integrals `∫ f n (x, y) dν(y)` converge to `∫ g (x, y) dν(y)` for `μ`-almost every `x`. -/
theorem exists_strictMono_ae_tendsto_integral_section {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : ℕ → α × β → ℝ} {g : α × β → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (μ.prod ν)) (hui : UniformIntegrable f 1 (μ.prod ν))
    (hfg : ∀ᵐ p ∂(μ.prod ν), Tendsto (fun n => f n p) atTop (𝓝 (g p))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i => ∫ y, f (ns i) (x, y) ∂ν) atTop (𝓝 (∫ y, g (x, y) ∂ν)) := by
  obtain ⟨hunif, C, hC⟩ := hui
  have hgi : Integrable g (μ.prod ν) := integrable_of_ae_tendsto_of_eLpNorm_le hf hC hfg
  have hfi : ∀ n, Integrable (f n) (μ.prod ν) := fun n =>
    memLp_one_iff_integrable.1 (memLp_iff.2 ((hC n).trans_lt ENNReal.coe_lt_top))
  -- Vitali: `f n → g` in `L¹(μ.prod ν)`.
  have hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 (μ.prod ν)) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hf (memLp_one_iff_integrable.2 hgi) hunif
      (tendstoInMeasure_of_tendsto_ae hf hfg)
  -- The `L¹(ν)` distances of the sections tend to `0` in `L¹(μ)`.
  set Φ : ℕ → α → ℝ := fun n x => ∫ y, ‖f n (x, y) - g (x, y)‖ ∂ν
  have hΦle : ∀ n, eLpNorm (Φ n - 0) 1 μ ≤ eLpNorm (f n - g) 1 (μ.prod ν) := by
    intro n
    have hd : AEStronglyMeasurable (f n - g) (μ.prod ν) := (hf n).sub hgi.1
    have hΦm : AEStronglyMeasurable (Φ n) μ := hd.norm.integral_prod_right'
    rw [sub_zero, eLpNorm_one_eq_lintegral_enorm hΦm,
      eLpNorm_one_eq_lintegral_enorm hd, lintegral_prod _ hd.enorm]
    refine lintegral_mono fun x => ?_
    refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
    simp only [enorm_norm, Pi.sub_apply]
  have hΦ0 : Tendsto (fun n => eLpNorm (Φ n - 0) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun _ => zero_le) hΦle
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (f := Φ) (g := 0) one_ne_zero hΦ0).exists_seq_tendsto_ae
  have hsec : ∀ᵐ x ∂μ, (∀ n, Integrable (fun y => f n (x, y)) ν) ∧ Integrable (fun y => g (x, y)) ν :=
    (ae_all_iff.2 fun n => (hfi n).prod_right_ae).and hgi.prod_right_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hsec] with x hx hxi
  have hx0 : Tendsto (fun i => Φ (ns i) x) atTop (𝓝 0) := by simpa using hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hx0
  rw [← integral_sub (hxi.1 _) hxi.2]
  exact norm_integral_le_integral_norm _

/-- **Identification of the limit of the section integrals.** If `f n → g` almost everywhere on `α × β`, the
sequence `f n` is uniformly integrable for the finite product measure `μ.prod ν`, and for `μ`-almost every `x` the
section integrals `∫ f n (x, y) dν(y)` converge to `L x`, then `∫ g (x, y) dν(y) = L x` for `μ`-almost every `x`. -/
theorem ae_integral_section_eq_of_uniformIntegrable {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : ℕ → α × β → ℝ} {g : α × β → ℝ} {L : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (μ.prod ν)) (hui : UniformIntegrable f 1 (μ.prod ν))
    (hfg : ∀ᵐ p ∂(μ.prod ν), Tendsto (fun n => f n p) atTop (𝓝 (g p)))
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n => ∫ y, f n (x, y) ∂ν) atTop (𝓝 (L x))) :
    ∀ᵐ x ∂μ, ∫ y, g (x, y) ∂ν = L x := by
  obtain ⟨ns, hns, hae⟩ := exists_strictMono_ae_tendsto_integral_section hf hui hfg
  filter_upwards [hae, hL] with x hx hLx
  exact tendsto_nhds_unique hx (hLx.comp hns.tendsto_atTop)

/-- **Identification of the limit of the section integrals, nonnegative form.** Let `f n` and `g` be extended
nonnegative functions on `α × β` with `f n` almost everywhere finite, `f n → g` almost everywhere, and the real parts
`(f n).toReal` uniformly integrable for the finite product measure `μ.prod ν`. If for `μ`-almost every `x` the
section integrals `∫⁻ f n (x, y) dν(y)` converge to `L x`, then `∫⁻ g (x, y) dν(y) = L x` for `μ`-almost every `x`. -/
theorem ae_lintegral_section_eq_of_uniformIntegrable {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : ℕ → α × β → ℝ≥0∞} {g : α × β → ℝ≥0∞} {L : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) (μ.prod ν)) (hfin : ∀ n, ∀ᵐ p ∂(μ.prod ν), f n p ≠ ∞)
    (hui : UniformIntegrable (fun n p => (f n p).toReal) 1 (μ.prod ν))
    (hfg : ∀ᵐ p ∂(μ.prod ν), Tendsto (fun n => f n p) atTop (𝓝 (g p)))
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n => ∫⁻ y, f n (x, y) ∂ν) atTop (𝓝 (L x))) :
    ∀ᵐ x ∂μ, ∫⁻ y, g (x, y) ∂ν = L x := by
  obtain ⟨hunif, C, hC⟩ := hui
  have hF : ∀ n, AEStronglyMeasurable (fun p => (f n p).toReal) (μ.prod ν) := fun n =>
    (hf n).ennreal_toReal.aestronglyMeasurable
  -- The lower integrals of `f n` are the `L¹` norms of their real parts, hence bounded by `C`.
  have hlint : ∀ n, ∫⁻ p, f n p ∂(μ.prod ν) ≤ C := by
    intro n
    refine le_of_eq_of_le ?_ (hC n)
    rw [eLpNorm_one_eq_lintegral_enorm (hF n)]
    refine lintegral_congr_ae ((hfin n).mono fun p hp => ?_)
    dsimp only
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hp]
  -- Fatou: the limit `g` has finite integral, hence is almost everywhere finite.
  have hgm : AEMeasurable g (μ.prod ν) := aemeasurable_of_tendsto_metrizable_ae' hf hfg
  have hglint : ∫⁻ p, g p ∂(μ.prod ν) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := C)) ?_
    calc ∫⁻ p, g p ∂(μ.prod ν) = ∫⁻ p, liminf (fun n => f n p) atTop ∂(μ.prod ν) :=
          lintegral_congr_ae (hfg.mono fun p hp => hp.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ p, f n p ∂(μ.prod ν)) atTop := lintegral_liminf_le' hf
      _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hlint)
  have hgfin : ∀ᵐ p ∂(μ.prod ν), g p ≠ ∞ := (ae_lt_top' hgm hglint).mono fun p hp => hp.ne
  -- The real parts converge almost everywhere, and are integrable.
  have hFG : ∀ᵐ p ∂(μ.prod ν), Tendsto (fun n => (f n p).toReal) atTop (𝓝 (g p).toReal) := by
    filter_upwards [hfg, hgfin] with p hp hgp
    exact (ENNReal.tendsto_toReal hgp).comp hp
  have hFi : ∀ n, Integrable (fun p => (f n p).toReal) (μ.prod ν) := fun n =>
    memLp_one_iff_integrable.1 (memLp_iff.2 ((hC n).trans_lt ENNReal.coe_lt_top))
  have hGi : Integrable (fun p => (g p).toReal) (μ.prod ν) :=
    integrable_of_ae_tendsto_of_eLpNorm_le hF hC hFG
  obtain ⟨ns, hns, hae⟩ := exists_strictMono_ae_tendsto_integral_section hF ⟨hunif, C, hC⟩ hFG
  have hsec : ∀ᵐ x ∂μ, (∀ n, Integrable (fun y => (f n (x, y)).toReal) ν ∧ ∀ᵐ y ∂ν, f n (x, y) ≠ ∞) ∧
      Integrable (fun y => (g (x, y)).toReal) ν ∧ ∀ᵐ y ∂ν, g (x, y) ≠ ∞ :=
    (ae_all_iff.2 fun n => (hFi n).prod_right_ae.and (Measure.ae_ae_of_ae_prod (hfin n))).and
      (hGi.prod_right_ae.and (Measure.ae_ae_of_ae_prod hgfin))
  have hof : ∀ {φ : β → ℝ≥0∞}, Integrable (fun y => (φ y).toReal) ν → (∀ᵐ y ∂ν, φ y ≠ ∞) →
      ∫⁻ y, φ y ∂ν = ENNReal.ofReal (∫ y, (φ y).toReal ∂ν) := by
    intro φ hi hφ
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    exact lintegral_congr_ae (hφ.mono fun y hy => (ENNReal.ofReal_toReal hy).symm)
  filter_upwards [hae, hL, hsec] with x hx hLx hxs
  have h1 : Tendsto (fun i => ∫⁻ y, f (ns i) (x, y) ∂ν) atTop (𝓝 (∫⁻ y, g (x, y) ∂ν)) := by
    rw [hof hxs.2.1 hxs.2.2]
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hx).congr fun i => ?_
    exact (hof (hxs.1 (ns i)).1 (hxs.1 (ns i)).2).symm
  exact tendsto_nhds_unique h1 (hLx.comp hns.tendsto_atTop)

end LatticeProb.Prob
