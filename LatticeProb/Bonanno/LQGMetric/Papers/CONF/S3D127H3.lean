/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127H3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127H2
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBDist
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.GaussFdd

/-!
# (L3) `exists_zbDistU`: the white-noise zero-boundary GFF on a bounded open `U` as a random
distribution (packet P-127H, decision D127)

CONF (arXiv:1905.00381, `confluence-final.tex`) C:722–724: `(h^U, φ) = √π W(K_U(φ 1_U))`
(`zbProcU`, S3D108R2). Generalisation of `DGo.ZB.exists_zbDist` (the square `(a, a+L)²`, task
P2-DGZB) to a bounded open `U`, same proof: `hz₀ = antiDist Y` for the continuous version `Y`
of the antiderivative field (`exists_continuous_uRectField`, S3D127H2), pairings identified by
stochastic Fubini (`ae_integral_d12_mul_zbU`), then the null-set modification of
`MarkovVer.exists_vanishing_version_zbExt` (as in `DGo.ZB.exists_zbDist`).

* **`exists_zbDistU_of_le`**: the construction measurable for a sub-σ-algebra `m'` carrying
  versions of `W g` for every `g` supported in `(0, ∞) × ℂ` (for the filtration of (L4),
  handoff/P2-CONFZBM.md: "`X₀'` is measurable for `⨆ ℱ n`"); Kolmogorov–Čentsov is run on
  `(Ω, m', P|_{m'})`;
* **`exists_zbDistU`**: the case `m' = m`;
* `isZBExtField_of_zbDistU`: under `ZBHeatRepr U` (D39 at `U`, (L1)), such a field is
  `IsZBExtField (toOpens U hU)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ GFFExist DGo.ZB MarkovGerm MarkovVer Blueprint

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

lemma supportedIn_smul' {A : Set (ℝ × ℂ)} (r : ℝ) {f : WNSpace} (hf : SupportedIn A f) :
    SupportedIn A (r • f) := by
  unfold SupportedIn at *
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul r f), hf] with p h1 h2
  rw [h1, Pi.smul_apply, h2, smul_zero]

lemma supportedIn_uRectL2 (x : ℂ) : SupportedIn (Ioi 0 ×ˢ univ) (uRectL2 U x) :=
  supportedIn_smul' _ (supportedIn_uKerL2 measurableSet_Ioi _)

lemma uKerL2_zero (I : Set ℝ) : uKerL2 U I (0 : ℂ → ℝ) = 0 := by
  have e : uKer U I (0 : ℂ → ℝ) = 0 := funext fun p => by simp [uKer]
  unfold uKerL2
  split_ifs with h
  · refine Lp.ext ?_
    filter_upwards [h.coeFn_toLp, Lp.coeFn_zero ℝ 2 (volume : Measure (ℝ × ℂ))] with p h1 h2
    rw [h1, h2, e]
  · rfl

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma map_trim_of_measurable {m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ) {f : Ω → ℝ}
    (hf : Measurable[m'] f) :
    @Measure.map Ω ℝ m' _ f (P.trim hm') = @Measure.map Ω ℝ mΩ _ f P := by
  ext s hs
  rw [Measure.map_apply hf hs, trim_measurableSet_eq hm' (hf hs),
    Measure.map_apply (show Measurable[mΩ] f from hf.mono hm' le_rfl) hs]

/-- a test function vanishing on `U` pairs to `0` a.s. -/
lemma zbProcU_ae_zero (hW : IsWhiteNoise P W) {ψ : TestC} (hψ : ∀ x ∈ U, ψ x = 0) :
    zbProcU W U ψ =ᵐ[P] 0 := by
  have e : U.indicator ψ = 0 := funext fun z => by
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz, hψ z hz]; rfl
    · rw [indicator_of_notMem hz]; rfl
  filter_upwards [wn_zero_ae hW] with ω hω
  simp only [zbProcU, e, uKerL2_zero, Pi.zero_apply]
  rw [hω, Pi.zero_apply, mul_zero]

/-- **The white-noise zero-boundary GFF on a bounded open `U` as a random distribution**,
vanishing off `cl U`, measurable for any sub-σ-algebra `m'` carrying versions of the white
noise on `(0, ∞) × ℂ`. -/
theorem exists_zbDistU_of_le (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R)
    (hW : IsWhiteNoise P W) {m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ)
    (hW' : ∀ g : WNSpace, SupportedIn (Ioi 0 ×ˢ univ) g →
      ∃ f : Ω → ℝ, Measurable[m'] f ∧ W g =ᵐ[P] f) :
    ∃ hz : Ω → DistC, Measurable[m'] hz ∧
      (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbProcU W U φ) ∧
      ∀ ω, restrictTo (toOpens (closure U)ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0 := by
  let _ : MeasurableSpace Ω := mΩ
  have := hW.isProbabilityMeasure
  have hR : 0 ≤ |R| := abs_nonneg R
  have hUR' : U ⊆ Metric.ball c |R| := hUR.trans (Metric.ball_subset_ball (le_abs_self R))
  choose Z hZm hZae using fun x => hW' (uRectL2 U x) (supportedIn_uRectL2 x)
  have hlaw : ∀ x x', @HasLaw Ω ℝ m' _ (fun ω => Z x ω - Z x' ω)
      (gaussianReal 0 (‖uRectL2 U x - uRectL2 U x'‖ ^ 2).toNNReal) (P.trim hm') := by
    intro x x'
    have h := hasLaw_uRect_sub (U := U) hW x x'
    have hm : Measurable[m'] (fun ω => Z x ω - Z x' ω) := (hZm x).sub (hZm x')
    refine @HasLaw.mk Ω ℝ m' _ _ _ _ (@Measurable.aemeasurable Ω ℝ m' _ _ _ hm) ?_
    rw [map_trim_of_measurable hm' hm, ← h.map_eq]
    refine Measure.map_congr ?_
    filter_upwards [hZae x, hZae x'] with ω h1 h2
    rw [h1, h2]
  obtain ⟨Y, hYc, hYm', hYZ⟩ := @exists_continuous_modification_of_gauss Ω m' (P.trim hm') Z
    hZm (fun x x' => (‖uRectL2 U x - uRectL2 U x'‖ ^ 2).toNNReal) hlaw
    (fun A => ⟨Real.pi * rectBnd U |R| * (4 * |A|), by
      have := rectBnd_nonneg U |R|; positivity, fun x x' h0 h1 h2 h3 => by
        have := rectBnd_nonneg U |R|
        have hA : 0 ≤ A := (abs_nonneg _).trans h0
        rw [Real.coe_toNNReal', max_le_iff, abs_of_nonneg hA]
        exact ⟨sq_norm_uRectL2_sub_le hU hR hUR' hA h1 h2, by positivity⟩⟩)
  have hYm : ∀ x, Measurable (Y x) := fun x => (hYm' x).mono hm' le_rfl
  have hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (uRectL2 U x) := fun x => by
    filter_upwards [ae_eq_of_ae_eq_trim (hYZ x), hZae x] with ω h1 h2
    rw [h1, h2]
  set hz := gffOf Y hYc
  have hmz' : Measurable[m'] hz := @measurable_gffOf Ω m' Y hYc hYm'
  have hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbProcU W U φ := fun φ => by
    filter_upwards [ae_integral_d12_mul_zbU hU hR hUR' hW hYc hYm hYW φ,
      hW.smul_ae (Real.sqrt Real.pi) (uKerL2 U (Ioi 0) (U.indicator φ))] with ω h1 h2
    simp only [hz, gffOf_apply]
    rw [h1, h2]; rfl
  -- the null-set modification (copied from `DGo.ZB.exists_zbDist`)
  set V : Opens ℂ := toOpens U hU
  set O := outV V
  set S : Set Ω := {ω | ∀ c : CoordJ, hz ω (extC O (comb O c)) = 0}
  have hS : MeasurableSet[m'] S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun c =>
      measurableSet_eq_fun ((measurable_distOn_apply _).comp hmz') measurable_const
  have hvan : ∀ c : CoordJ, ∀ x ∈ U, (extC O (comb O c)) x = 0 := by
    intro c x hx
    rw [coe_extC]
    refine (comb O c).zero_on_compl fun hxW => ?_
    have : x ∉ closure (V : Set ℂ) := hxW
    exact this (subset_closure (show x ∈ (V : Set ℂ) from hx))
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    have : ∀ᵐ ω ∂P, ∀ c : CoordJ, hz ω (extC O (comb O c)) = 0 := by
      rw [ae_all_iff]
      intro c
      filter_upwards [hv (extC O (comb O c)), zbProcU_ae_zero hW (hvan c)] with ω h1 h2
      rw [h1, h2]; rfl
    exact this
  have hrS : ∀ ω ∈ S, restrictTo O (hz ω) = 0 := fun ω hω =>
    injective_pairJ O (funext fun c => by
      show restrictTo O (hz ω) (comb O c) = (0 : DistOn O) (comb O c)
      rw [ContinuousLinearMap.zero_apply]
      exact hω c)
  classical
  refine ⟨fun ω => if ω ∈ S then hz ω else 0, Measurable.ite hS hmz' measurable_const,
    fun φ => ?_, fun ω => ?_⟩
  · filter_upwards [hSae, hv φ] with ω h1 h2
    simp only [if_pos h1]
    exact h2
  · by_cases hω : ω ∈ S
    · simp only [if_pos hω]
      exact hrS ω hω
    · simp only [if_neg hω]
      exact ContinuousLinearMap.zero_comp _

/-- under `ZBHeatRepr U` (D39 at `U`), the white-noise field is the zero-boundary GFF on `U`
extended by `0` -/
theorem isZBExtField_of_zbDistU (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R)
    (hW : IsWhiteNoise P W) (hH : ZBHeatRepr U) {hz : Ω → DistC} (hm : Measurable hz)
    (hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbProcU W U φ) :
    IsZBExtField (toOpens U hU) hz P := by
  have hUR' : U ⊆ Metric.ball c |R| := hUR.trans (Metric.ball_subset_ball (le_abs_self R))
  refine ⟨hm, (isGaussianProcess_zbProcU hW U).congr fun φ => (hv φ).symm, fun φ => ?_,
    fun φ ψ => ?_⟩
  · rw [integral_congr_ae (hv φ)]; exact integral_zbProcU hW U φ
  · rw [DDDF.covariance_congr_ae (hv φ) (hv ψ)]
    exact cov_zbProcU_of_heatRepr hW hU (abs_nonneg R) hUR' hH φ ψ

end LQGMetric.CONF.ZBM
