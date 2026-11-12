/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18R2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2D
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# DG:1776: circle averages of `h = 𝔥 + h^U` at small radius (task P2-DG105q)

DG L2.2 (DG:572–590, `L22T.dg_lemma22_tr`) writes the whole-plane field as `h = hh' + hz` with
`hh'` harmonic on `U` and `hz` a zero-boundary GFF on `U`. At a point `x` with `B̄(x, 4ρ) ⊆ U`
and `δ < ρ`, the circle average of the harmonic part is its value (mean value property,
mathlib `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`), so `h_δ(x) = g(x) + hz_δ(x)`.

* `r18_tendsto_mollAvg_harm` — the mollified circle averages of a distribution that equals a
  harmonic `g` on `U` converge to `g(x)` (compare with the continuous `g ∘ clamp`, then
  `CircleAvg.tendsto_mollAvg_ofCont`);
* `r18_circleAvg_split` — `T = T₁ + T₂`, `T₁ = g` on `U`: `T_δ(x) = g(x) + (T₂)_δ(x)` wherever
  the limit for `T` exists;
* `r18G` — a choice of the harmonic function of `hh'`; **`r18_ae_version`**:
  `H_δ(x) − G(x) = hz_δ(x)` a.s., for the continuous circle-average process `H` of `h`.

Own routine glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped ENNReal

namespace LQGMetric.DG

open CircleAvg

variable {Ω : Type}

lemma r18Cl_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (v : ℂ) : ‖r18Cl (-ρ) ρ v‖ ≤ 4 * ρ := by
  have h := r18X_bdd (-ρ) ρ (r18Cl_mem (by linarith) v)
  rw [mem_closedBall, dist_zero_right] at h
  rw [abs_neg, abs_of_nonneg hρ] at h
  linarith

/-- the mollified circle averages of `T = g` on `U` converge to `g(x)` -/
theorem r18_tendsto_mollAvg_harm {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g (U : Set ℂ))
    {T : DistC} (hT : ∀ φ : TestOn U, restrictTo U T φ = ∫ y, g y * φ y) {x : ℂ} {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ < ρ) (hB : closedBall x (4 * ρ) ⊆ (U : Set ℂ)) :
    Tendsto (fun n => mollAvg T n x δ) atTop (𝓝 (g x)) := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hgc : ContinuousOn g (U : Set ℂ) := fun y hy => (hg y hy).1.continuousAt.continuousWithinAt
  set c : ℂ → ℂ := fun y => x + r18Cl (-ρ) ρ (y - x) with hc
  have hcB : ∀ y, c y ∈ closedBall x (4 * ρ) := fun y => by
    rw [mem_closedBall, dist_eq_norm, hc]
    simpa using r18Cl_norm_le hρ.le (y - x)
  have hcc : Continuous c := continuous_const.add ((r18Cl_continuous _ _).comp
    (continuous_id.sub continuous_const))
  let f : C(ℂ, ℝ) := ⟨g ∘ c, hgc.comp_continuous hcc fun y => hB (hcB y)⟩
  have hfg : ∀ y, ‖y - x‖ ≤ ρ → f y = g y := fun y hy => by
    show g (x + r18Cl (-ρ) ρ (y - x)) = g y
    have hmem : y - x ∈ r18X (-ρ) ρ := ⟨abs_le.1 ((Complex.abs_re_le_norm _).trans hy),
      abs_le.1 ((Complex.abs_im_le_norm _).trans hy)⟩
    rw [r18Cl_eq hmem, add_sub_cancel]
  -- eventually the two mollified averages agree
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hδρ) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hev : ∀ n, N ≤ n → mollAvg T n x δ = mollAvg (ofCont f) n x δ := fun n hn => by
    have hn' : (2 : ℝ)⁻¹ ^ n < ρ - δ :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans_lt hN
    unfold mollAvg
    refine Real.circleAverage_congr_sphere fun y hy => ?_
    rw [mem_sphere, abs_of_pos hδ] at hy
    have hsupp : tsupport (bumpTest n y : ℂ → ℝ) ⊆ (U : Set ℂ) := by
      rw [GM.tsupport_bumpTest]
      intro z hz
      refine hB ?_
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle z y x, (by norm_num : (0 : ℝ) ≤ 3) , hρ]
    let φ : TestOn U := ⟨bumpTest n y, (bumpTest n y).contDiff,
      (bumpTest n y).hasCompactSupport, hsupp⟩
    have h1 : T (bumpTest n y) = restrictTo U T φ := by
      show T _ = T (TestFunction.monoCLM ℝ φ)
      congr 1
      ext z
      simp [TestFunction.monoCLM_apply, φ]
    show T (bumpTest n y) = ofCont f (bumpTest n y)
    rw [h1, hT φ, LQGMetric.ofCont_apply]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show g z * bumpTest n y z = bumpTest n y z * f z
    by_cases hz : dist z y < (2 : ℝ)⁻¹ ^ n
    · rw [hfg z ?_, mul_comm]
      rw [← dist_eq_norm]
      linarith [dist_triangle z y x, dist_comm y x]
    · rw [CircleAvg.bumpTest_eq_zero_of_le n (not_lt.1 hz)]
      ring
  have hlim := (tendsto_mollAvg_ofCont f δ x).congr' (eventually_atTop.2 ⟨N, fun n hn =>
    (hev n hn).symm⟩)
  have hca : Real.circleAverage f x δ = g x := by
    rw [Real.circleAverage_congr_sphere (f₂ := g) fun y hy => hfg y ?_]
    · refine HarmonicOnNhd.circleAverage_eq (fun y hy => hg y (hB ?_))
      rw [mem_closedBall, abs_of_pos hδ] at hy; rw [mem_closedBall]
      linarith
    · rw [mem_sphere, abs_of_pos hδ, dist_eq_norm] at hy
      linarith
  rwa [hca] at hlim

/-- **`T_δ(x) = g(x) + (T₂)_δ(x)`** for `T = T₁ + T₂`, `T₁ = g` harmonic on `U` -/
theorem r18_circleAvg_split {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g (U : Set ℂ))
    {T T₁ T₂ : DistC} (hsum : T = T₁ + T₂)
    (hT : ∀ φ : TestOn U, restrictTo U T₁ φ = ∫ y, g y * φ y) {x : ℂ} {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ < ρ) (hB : closedBall x (4 * ρ) ⊆ (U : Set ℂ)) {a : ℝ}
    (ha : Tendsto (fun n => mollAvg T n x δ) atTop (𝓝 a)) :
    circleAvg T δ x = g x + circleAvg T₂ δ x := by
  have h1 := r18_tendsto_mollAvg_harm hg hT hδ hδρ hB
  have hsplit : ∀ n, mollAvg T₂ n x δ = mollAvg T n x δ - mollAvg T₁ n x δ := fun n => by
    simp only [mollAvg_eq, hsum, ContinuousLinearMap.add_apply]
    ring
  have h2 : Tendsto (fun n => mollAvg T₂ n x δ) atTop (𝓝 (a - g x)) := by
    simp_rw [hsplit]; exact ha.sub h1
  rw [circleAvg_eq_of_tendsto ha, circleAvg_eq_of_tendsto h2]
  ring

open Classical in
/-- a choice of the harmonic function representing `hh'` on `U` (`0` if there is none) -/
def r18G (U : Opens ℂ) (hh' : Ω → DistC) (ω : Ω) : ℂ → ℝ :=
  if h : ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x then h.choose else 0

lemma r18G_spec {U : Opens ℂ} {hh' : Ω → DistC} {ω : Ω}
    (h : ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x) :
    HarmonicOnNhd (r18G U hh' ω) (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, r18G U hh' ω x * φ x := by
  rw [r18G, dif_pos h]; exact h.choose_spec

lemma r18G_continuousOn (U : Opens ℂ) (hh' : Ω → DistC) (ω : Ω) :
    ContinuousOn (r18G U hh' ω) (U : Set ℂ) := by
  by_cases h : ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x
  · exact fun y hy => ((r18G_spec h).1 y hy).1.continuousAt.continuousWithinAt
  · rw [r18G, dif_neg h]; exact continuousOn_const

/-- **`H_δ(x) − G(x)` is a version of `hz_δ(x)`** -/
theorem r18_ae_version [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) {H : ℝ → ℂ → Ω → ℝ}
    (hH : ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z)
    {U : Opens ℂ} {hh' hz : Ω → DistC} (hsum : ∀ ω, h ω = hh' ω + hz ω)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x)
    {x : ℂ} {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ) (hB : closedBall x (4 * ρ) ⊆ (U : Set ℂ)) :
    (fun ω => H δ x ω - r18G U hh' ω x) =ᵐ[P] fun ω => circleAvg (hz ω) δ x := by
  filter_upwards [hH δ hδ x, hharm, ae_tendsto_mollAvg hh.1 x hδ] with ω hω hg ⟨a, ha⟩
  have hs := r18G_spec hg
  rw [hω, r18_circleAvg_split hs.1 (hsum ω) hs.2 hδ hδρ hB ha]
  ring

end LQGMetric.DG
