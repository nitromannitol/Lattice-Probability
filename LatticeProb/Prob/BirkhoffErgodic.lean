import Mathlib
import LatticeProb.Prob.Birkhoff

/-!
# Birkhoff's pointwise ergodic theorem, with the limit identified

**Birkhoff's pointwise ergodic theorem.** Let `ν` be a probability measure on `Y`, `T : Y → Y` measure-preserving and
ergodic, and `f` integrable. Then the Cesàro averages `(∑ n < k, f (T^[n] y)) / k` converge `ν`-almost everywhere to
the constant `∫ f ∂ν`.

Route:
* `ae_tendsto_bLimsup` and `ae_bLimsup_comp` (`LatticeProb.Prob.Birkhoff`): the averages converge a.e. to a measurable
  limit `bLimsup T f` which is a.e. `T`-invariant;
* `Ergodic.ae_eq_const_of_ae_eq_comp₀` (Mathlib): an a.e. invariant measurable function is a.e. constant;
* for bounded `g`, `∫ bLimsup T g = ∫ g` (dominated convergence along `n ↦ bAvg T g (n + 1)`, as in
  `LatticeProb.Prob.ErgodicDecomposition`);
* the truncations `clip N f` with `tendsto_integral_abs_sub_clip` (`LatticeProb.Prob.Birkhoff`), a pointwise comparison of
  the averages and Fatou's lemma for nonnegative averages identify the constant with `∫ f`.

Imports: Mathlib and `LatticeProb.Prob.Birkhoff` only. `LatticeProb.Prob.ErgodicDecomposition` is not imported because it
does not build at the pinned commit (see the report).
-/

namespace LatticeProb

open MeasureTheory Filter Topology

variable {Y : Type*} [MeasurableSpace Y]

/-- Composition with an iterate of a measure-preserving map preserves integrability. -/
theorem integrable_comp_iterate_of_measurePreserving {ν : Measure Y} {T : Y → Y}
    (hT : MeasurePreserving T ν ν) {h : Y → ℝ} (hh : Integrable h ν) (k : ℕ) :
    Integrable (fun x => h (T^[k] x)) ν :=
  (hT.iterate k).integrable_comp_of_integrable hh

/-- Composition with an iterate of a measure-preserving map preserves the integral. -/
theorem integral_comp_iterate_eq_of_measurePreserving {ν : Measure Y} {T : Y → Y}
    (hT : MeasurePreserving T ν ν) {h : Y → ℝ} (hh : AEStronglyMeasurable h ν) (k : ℕ) :
    ∫ x, h (T^[k] x) ∂ν = ∫ x, h x ∂ν := by
  have hk : MeasurePreserving (T^[k]) ν ν := hT.iterate k
  have hmap : AEStronglyMeasurable h (Measure.map (T^[k]) ν) := by
    rw [hk.map_eq]
    exact hh
  rw [← integral_map hk.measurable.aemeasurable hmap, hk.map_eq]

/-- The mean of a Birkhoff average is the mean of the function. -/
theorem integral_bAvg_eq_of_measurePreserving {ν : Measure Y} {T : Y → Y}
    (hT : MeasurePreserving T ν ν) {f : Y → ℝ} (hf : Integrable f ν) {n : ℕ} (hn : n ≠ 0) :
    ∫ x, bAvg T f n x ∂ν = ∫ x, f x ∂ν := by
  unfold bAvg birkhoffSum
  rw [integral_div, integral_finsetSum _ (fun k _ => integrable_comp_iterate_of_measurePreserving hT hf k)]
  simp_rw [integral_comp_iterate_eq_of_measurePreserving hT hf.aestronglyMeasurable]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

omit [MeasurableSpace Y] in
/-- Pointwise comparison of Birkhoff averages: the average of `f - g` is dominated in absolute value by the average of
`|f - g|`. -/
theorem abs_bAvg_sub_le_bAvg_abs_sub (T : Y → Y) (f g : Y → ℝ) (n : ℕ) (x : Y) :
    |bAvg T f n x - bAvg T g n x| ≤ bAvg T (fun y => |f y - g y|) n x := by
  have hsub : bAvg T f n x - bAvg T g n x
      = (∑ k ∈ Finset.range n, (f (T^[k] x) - g (T^[k] x))) / (n : ℝ) := by
    unfold bAvg birkhoffSum
    rw [Finset.sum_sub_distrib, sub_div]
  have hR : bAvg T (fun y => |f y - g y|) n x
      = (∑ k ∈ Finset.range n, |f (T^[k] x) - g (T^[k] x)|) / (n : ℝ) := rfl
  rw [hsub, hR, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Bounded Birkhoff limits have the mean of the function.** For a measure-preserving `T` on a probability space and a
measurable `f` with `|f| ≤ C`, `∫ bLimsup T f = ∫ f`. -/
theorem integral_bLimsup_eq_of_abs_le {ν : Measure Y} [IsProbabilityMeasure ν] {T : Y → Y}
    (hT : MeasurePreserving T ν ν) {f : Y → ℝ} (hfm : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) :
    ∫ x, bLimsup T f x ∂ν = ∫ x, f x ∂ν := by
  have hfi : Integrable f ν :=
    Integrable.of_bound hfm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hc : ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => bAvg T f (n + 1) x) atTop (𝓝 (bLimsup T f x)) := by
    filter_upwards [ae_tendsto_bLimsup hT hfm hfi] with x hx
    exact hx.comp (tendsto_add_atTop_nat 1)
  have hd : ∀ n : ℕ, ∀ᵐ x ∂ν, ‖bAvg T f (n + 1) x‖ ≤ C := fun n =>
    Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using abs_bAvg_le hC hb (n + 1) x
  have hl := tendsto_integral_of_dominated_convergence (fun _ : Y => C)
    (fun n => (measurable_bAvg hT.measurable hfm (n + 1)).aestronglyMeasurable)
    (integrable_const C) hd hc
  have hmean : ∀ n : ℕ, ∫ x, bAvg T f (n + 1) x ∂ν = ∫ x, f x ∂ν :=
    fun n => integral_bAvg_eq_of_measurePreserving hT hfi (Nat.add_one_ne_zero n)
  simp only [hmean] at hl
  exact (tendsto_nhds_unique tendsto_const_nhds hl).symm

/-- **Fatou's inequality for Birkhoff limits.** For a measure-preserving `T` on a probability space and a nonnegative
integrable `h`, the a.e. limit `bLimsup T h` of the averages of `h` is integrable and
`∫ bLimsup T h ≤ ∫ h`. -/
theorem integral_bLimsup_le_of_nonneg {ν : Measure Y} [IsProbabilityMeasure ν] {T : Y → Y}
    (hT : MeasurePreserving T ν ν) {h : Y → ℝ} (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hhi : Integrable h ν) :
    Integrable (bLimsup T h) ν ∧ ∫ x, bLimsup T h x ∂ν ≤ ∫ x, h x ∂ν := by
  have hTm : Measurable T := hT.measurable
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => bAvg T h n x) atTop (𝓝 (bLimsup T h x)) :=
    ae_tendsto_bLimsup hT hhm hhi
  have hav : ∀ n : ℕ, Integrable (bAvg T h n) ν := fun n => by
    unfold bAvg birkhoffSum
    exact (integrable_finsetSum _ fun k _ => integrable_comp_iterate_of_measurePreserving hT hhi k).div_const _
  have hnn : ∀ n : ℕ, ∀ x, 0 ≤ bAvg T h n x := fun n x => by
    unfold bAvg birkhoffSum
    exact div_nonneg (Finset.sum_nonneg fun k _ => hh0 _) (Nat.cast_nonneg n)
  have hL0 : 0 ≤ᵐ[ν] bLimsup T h := by
    filter_upwards [hlim] with x hx
    exact ge_of_tendsto hx (Eventually.of_forall fun n => hnn n x)
  have hmeasL : Measurable (bLimsup T h) := measurable_bLimsup hTm hhm
  -- Fatou along the shifted averages `n ↦ bAvg T h (n + 1)` in `ℝ≥0∞`
  have hF := lintegral_liminf_le (μ := ν) (u := atTop)
    (f := fun (n : ℕ) (x : Y) => ENNReal.ofReal (bAvg T h (n + 1) x))
    (fun n => (measurable_bAvg hTm hhm (n + 1)).ennreal_ofReal)
  have hshift : ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => ENNReal.ofReal (bAvg T h (n + 1) x)) atTop
      (𝓝 (ENNReal.ofReal (bLimsup T h x))) := by
    filter_upwards [hlim] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hx.comp (tendsto_add_atTop_nat 1))
  have hlin : ∀ᵐ x ∂ν, liminf (fun n : ℕ => ENNReal.ofReal (bAvg T h (n + 1) x)) atTop
      = ENNReal.ofReal (bLimsup T h x) := by
    filter_upwards [hshift] with x hx using hx.liminf_eq
  have hint : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (bAvg T h (n + 1) x) ∂ν = ENNReal.ofReal (∫ x, h x ∂ν) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hav (n + 1)) (Eventually.of_forall fun x => hnn (n + 1) x),
      integral_bAvg_eq_of_measurePreserving hT hhi (Nat.add_one_ne_zero n)]
  have hliminf_const : liminf (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (bAvg T h (n + 1) x) ∂ν) atTop
      = ENNReal.ofReal (∫ x, h x ∂ν) := by
    simp only [hint]
    exact liminf_const _
  have hcongr : ∫⁻ x, liminf (fun n : ℕ => ENNReal.ofReal (bAvg T h (n + 1) x)) atTop ∂ν
      = ∫⁻ x, ENNReal.ofReal (bLimsup T h x) ∂ν := lintegral_congr_ae hlin
  have hFatou : ∫⁻ x, ENNReal.ofReal (bLimsup T h x) ∂ν ≤ ENNReal.ofReal (∫ x, h x ∂ν) := by
    rw [← hcongr]
    exact hF.trans_eq hliminf_const
  have hLi : Integrable (bLimsup T h) ν := by
    refine ⟨hmeasL.aestronglyMeasurable, ?_⟩
    have hfin : ∫⁻ x, ENNReal.ofReal (bLimsup T h x) ∂ν ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFatou
    have hcongr' : ∫⁻ x, ‖bLimsup T h x‖ₑ ∂ν = ∫⁻ x, ENNReal.ofReal (bLimsup T h x) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hL0] with x hx
      exact Real.enorm_eq_ofReal hx
    unfold HasFiniteIntegral
    rw [hcongr']
    exact lt_top_iff_ne_top.mpr hfin
  refine ⟨hLi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hL0 hmeasL.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => hh0 x) hFatou

/-- **Birkhoff's pointwise ergodic theorem, with the limit identified.** Let `ν` be a probability measure, `T`
measure-preserving and ergodic, and `f` measurable and integrable. Then the Cesàro averages
`(∑ n < k, f (T^[n] y)) / k` converge `ν`-almost everywhere to the constant `∫ f ∂ν`. -/
theorem ae_tendsto_birkhoffAverage_integral_of_ergodic {ν : Measure Y} [IsProbabilityMeasure ν] {T : Y → Y}
    (hT : MeasurePreserving T ν ν) (herg : Ergodic T ν) {f : Y → ℝ} (hfm : Measurable f)
    (hf : Integrable f ν) :
    ∀ᵐ y ∂ν, Tendsto (fun k : ℕ => (∑ n ∈ Finset.range k, f (T^[n] y)) / (k : ℝ)) atTop
      (𝓝 (∫ z, f z ∂ν)) := by
  have hTm : Measurable T := hT.measurable
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => bAvg T f n x) atTop (𝓝 (bLimsup T f x)) :=
    ae_tendsto_bLimsup hT hfm hf
  have hinv : ∀ᵐ x ∂ν, bLimsup T f (T x) = bLimsup T f x := ae_bLimsup_comp hT hfm hf
  obtain ⟨c, hc⟩ := herg.ae_eq_const_of_ae_eq_comp₀ (measurable_bLimsup hTm hfm).nullMeasurable hinv
  -- `c = ∫ f`: compare with the bounded truncations `clip N f`.
  have hcf : c = ∫ z, f z ∂ν := by
    have hkey : ∀ N : ℕ, |c - ∫ x, f x ∂ν| ≤ 2 * ∫ x, |f x - clip (N : ℝ) f x| ∂ν := by
      intro N
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hgm : Measurable (clip (N : ℝ) f) := measurable_clip _ hfm
      have hgb : ∀ x, |clip (N : ℝ) f x| ≤ (N : ℝ) := fun x => abs_clip_le (f := f) hN0 x
      have hgi : Integrable (clip (N : ℝ) f) ν :=
        Integrable.of_bound hgm.aestronglyMeasurable (N : ℝ)
          (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hgb x)
      have hLg : ∫ x, bLimsup T (clip (N : ℝ) f) x ∂ν = ∫ x, clip (N : ℝ) f x ∂ν :=
        integral_bLimsup_eq_of_abs_le hT hgm hN0 hgb
      have hLgm : Measurable (bLimsup T (clip (N : ℝ) f)) := measurable_bLimsup hTm hgm
      have hLgi : Integrable (bLimsup T (clip (N : ℝ) f)) ν := by
        refine Integrable.of_bound hLgm.aestronglyMeasurable (N : ℝ) ?_
        filter_upwards [ae_tendsto_bLimsup hT hgm hgi] with x hx
        simpa only [Real.norm_eq_abs] using
          le_of_tendsto hx.abs (Eventually.of_forall fun n => abs_bAvg_le hN0 hgb n x)
      have hhm : Measurable (fun x => |f x - clip (N : ℝ) f x|) :=
        continuous_abs.measurable.comp (hfm.sub hgm)
      have hhi : Integrable (fun x => |f x - clip (N : ℝ) f x|) ν := (hf.sub hgi).abs
      obtain ⟨hLhi, hLh_le⟩ := integral_bLimsup_le_of_nonneg hT hhm (fun x => abs_nonneg _) hhi
      -- pointwise a.e.: `|L_f - L_g| ≤ L_{|f - g|}`
      have hpt : ∀ᵐ x ∂ν, |bLimsup T f x - bLimsup T (clip (N : ℝ) f) x|
          ≤ bLimsup T (fun y => |f y - clip (N : ℝ) f y|) x := by
        filter_upwards [hlim, ae_tendsto_bLimsup hT hgm hgi, ae_tendsto_bLimsup hT hhm hhi] with x h1 h2 h3
        exact le_of_tendsto_of_tendsto (h1.sub h2).abs h3
          (Eventually.of_forall fun n => abs_bAvg_sub_le_bAvg_abs_sub T f (clip (N : ℝ) f) n x)
      have hcg : ∀ᵐ x ∂ν, |c - bLimsup T (clip (N : ℝ) f) x|
          ≤ bLimsup T (fun y => |f y - clip (N : ℝ) f y|) x := by
        filter_upwards [hpt, hc] with x hx1 hx2
        have hx2' : bLimsup T f x = c := hx2
        rw [hx2'] at hx1
        exact hx1
      have h1 : |c - ∫ x, clip (N : ℝ) f x ∂ν| ≤ ∫ x, |f x - clip (N : ℝ) f x| ∂ν := by
        rw [← hLg]
        calc |c - ∫ x, bLimsup T (clip (N : ℝ) f) x ∂ν|
            = |∫ x, (c - bLimsup T (clip (N : ℝ) f) x) ∂ν| := by
              rw [integral_sub (integrable_const c) hLgi, integral_const]
              simp
          _ ≤ ∫ x, |c - bLimsup T (clip (N : ℝ) f) x| ∂ν := abs_integral_le_integral_abs
          _ ≤ ∫ x, bLimsup T (fun y => |f y - clip (N : ℝ) f y|) x ∂ν :=
              integral_mono_ae ((integrable_const c).sub hLgi).abs hLhi hcg
          _ ≤ ∫ x, |f x - clip (N : ℝ) f x| ∂ν := hLh_le
      have h2 : |∫ x, clip (N : ℝ) f x ∂ν - ∫ x, f x ∂ν| ≤ ∫ x, |f x - clip (N : ℝ) f x| ∂ν := by
        rw [← integral_sub hgi hf]
        calc |∫ x, (clip (N : ℝ) f x - f x) ∂ν|
            ≤ ∫ x, |clip (N : ℝ) f x - f x| ∂ν := abs_integral_le_integral_abs
          _ = ∫ x, |f x - clip (N : ℝ) f x| ∂ν :=
              integral_congr_ae (Eventually.of_forall fun x => abs_sub_comm _ _)
      calc |c - ∫ x, f x ∂ν|
          ≤ |c - ∫ x, clip (N : ℝ) f x ∂ν| + |∫ x, clip (N : ℝ) f x ∂ν - ∫ x, f x ∂ν| :=
            abs_sub_le _ _ _
        _ ≤ 2 * ∫ x, |f x - clip (N : ℝ) f x| ∂ν := by linarith
    have hD := tendsto_integral_abs_sub_clip hfm hf
    have hlast : |c - ∫ x, f x ∂ν| ≤ 2 * 0 :=
      ge_of_tendsto (hD.const_mul 2) (Eventually.of_forall hkey)
    have hz : |c - ∫ x, f x ∂ν| = 0 := le_antisymm (by simpa using hlast) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  filter_upwards [hlim, hc] with y hy hyc
  have hyc' : bLimsup T f y = ∫ z, f z ∂ν := hyc.trans hcf
  rw [hyc'] at hy
  exact hy

end LatticeProb
