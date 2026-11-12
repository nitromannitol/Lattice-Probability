/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127H4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127H3

/-!
# (L3) `exists_zbDistU` measurable for the coarse filtration (packet P-127H)

The (L4) assembly (handoff/P2-CONFZBM.md) uses `ℱ n = σ(W g : g supported in (t_n, ∞) × ℂ)`
with `t_n → 0` and needs the field measurable for `⨆ ℱ n`. Here:

* `exists_version_of_supportedIn`: if every `W g` with `g` supported in `(t_n, ∞) × ℂ` is
  `m'`-measurable (`t_n → 0`), then every `W g` with `g` supported in `(0, ∞) × ℂ` has an
  `m'`-measurable version (the truncations `g 1_{(t_n,∞) × ℂ} → g` in `L²` by dominated
  convergence, the Itô isometry, and closedness of the `m'`-a.e.-strongly-measurable classes in
  `L²(P)`, mathlib's `isClosed_aestronglyMeasurable`). Own elementary argument;
* **`exists_zbDistU_filt`**: `exists_zbDistU_of_le` under that hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open WhiteNoise GFFExist Blueprint

lemma sq_norm_L2_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (F : Lp ℝ 2 μ) :
    ‖F‖ ^ 2 = ∫ a, (F : α → ℝ) a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma norm_toLp_wn_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    ‖(wn_memLp hW f).toLp (W f) - (wn_memLp hW g).toLp (W g)‖ = ‖f - g‖ := by
  have := hW.isProbabilityMeasure
  have hsub : W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
    have h := hW.ae_eq_zero_of_norm_eq_zero ![f - g, f, g] ![1, -1, 1] (by
      simp [Fin.sum_univ_three]; abel)
    filter_upwards [h] with ω hω
    simp only [Fin.sum_univ_three, Pi.zero_apply] at hω
    simp at hω
    linarith
  have e : ‖(wn_memLp hW f).toLp (W f) - (wn_memLp hW g).toLp (W g)‖ ^ 2 = ‖f - g‖ ^ 2 := by
    rw [sq_norm_L2_eq, ← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((wn_memLp hW f).toLp (W f)) ((wn_memLp hW g).toLp (W g)),
      (wn_memLp hW f).coeFn_toLp, (wn_memLp hW g).coeFn_toLp, hsub] with ω h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4, sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e

/-- the truncation `g 1_A` -/
lemma memLp_trunc (g : WNSpace) {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) :
    MemLp (A.indicator (g : ℝ × ℂ → ℝ)) 2 volume := (Lp.memLp g).indicator hA

lemma supportedIn_trunc (g : WNSpace) {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) :
    SupportedIn A ((memLp_trunc g hA).toLp _) := by
  unfold SupportedIn
  filter_upwards [ae_restrict_of_ae (memLp_trunc g hA).coeFn_toLp, ae_restrict_mem hA.compl]
    with p h1 h2
  rw [h1, indicator_of_notMem h2]

lemma tendsto_trunc {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) {g : WNSpace}
    (hg : SupportedIn (Ioi 0 ×ˢ univ) g) :
    Tendsto (fun n => (memLp_trunc g (measurableSet_Ioi.prod MeasurableSet.univ :
      MeasurableSet (Ioi (t n) ×ˢ (univ : Set ℂ)))).toLp _) atTop (𝓝 g) := by
  set A : ℕ → Set (ℝ × ℂ) := fun n => Ioi (t n) ×ˢ univ with hAdef
  have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_Ioi.prod MeasurableSet.univ
  set F : ℕ → ℝ × ℂ → ℝ := fun n => (A n)ᶜ.indicator (fun p => (g : ℝ × ℂ → ℝ) p ^ 2)
  have hnorm : ∀ n, ‖(memLp_trunc g (hA n)).toLp _ - g‖ ^ 2 = ∫ p, F n p := fun n => by
    rw [sq_norm_L2_eq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((memLp_trunc g (hA n)).toLp _) g,
      (memLp_trunc g (hA n)).coeFn_toLp] with p h1 h2
    rw [h1, Pi.sub_apply, h2]
    by_cases hp : p ∈ A n
    · simp [F, hp]
    · simp [F, hp]
  have hg2 : Integrable fun p => (g : ℝ × ℂ → ℝ) p ^ 2 := (Lp.memLp g).integrable_sq
  have hg0 : ∀ᵐ p, p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) → (g : ℝ × ℂ → ℝ) p = 0 := by
    have := hg
    unfold SupportedIn at this
    rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ).compl] at this
    exact this
  have hlim : Tendsto (fun n => ∫ p, F n p) atTop (𝓝 (∫ _p : ℝ × ℂ, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun p => (g : ℝ × ℂ → ℝ) p ^ 2)
      (fun n => (hg2.indicator (hA n).compl).aestronglyMeasurable) hg2
      (fun n => Eventually.of_forall fun p => ?_) ?_
    · simp only [F, Real.norm_eq_abs]
      by_cases hp : p ∈ (A n)ᶜ
      · rw [indicator_of_mem hp, abs_of_nonneg (sq_nonneg _)]
      · rw [indicator_of_notMem hp, abs_zero]; exact sq_nonneg _
    · filter_upwards [hg0] with p hp
      by_cases h1 : 0 < p.1
      · have hev : ∀ᶠ n in atTop, t n < p.1 := ht.eventually (gt_mem_nhds h1)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        have : p ∈ A n := ⟨hn, trivial⟩
        simp [F, this]
      · have h0 := hp fun h => h1 h.1
        have : ∀ n, F n p = 0 := fun n => by
          by_cases hpA : p ∈ (A n)ᶜ
          · simp only [F, indicator_of_mem hpA, h0]; ring
          · simp only [F, indicator_of_notMem hpA]
        simp only [this]
        exact tendsto_const_nhds
  rw [integral_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun n => ‖(memLp_trunc g (hA n)).toLp _ - g‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hnorm]; exact hlim
  have := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

/-- **versions of the white noise on `(0, ∞) × ℂ`** measurable for the coarse σ-algebras -/
theorem exists_version_of_supportedIn (hW : IsWhiteNoise P W) {m' : MeasurableSpace Ω}
    (hm' : m' ≤ mΩ) {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0))
    (hm : ∀ n (g : WNSpace), SupportedIn (Ioi (t n) ×ˢ univ) g → Measurable[m'] (W g)) :
    ∀ g : WNSpace, SupportedIn (Ioi 0 ×ˢ univ) g →
      ∃ f : Ω → ℝ, Measurable[m'] f ∧ W g =ᵐ[P] f := by
  let _ : MeasurableSpace Ω := mΩ
  intro g hg
  have := hW.isProbabilityMeasure
  set J : WNSpace → Lp ℝ 2 P := fun f => (wn_memLp hW f).toLp (W f) with hJ
  have hJc : Continuous J := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => ?_)
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, hJ]
    exact (norm_toLp_wn_sub hW f g).le
  have hmem := (isClosed_aestronglyMeasurable (F := ℝ) (p := 2) (μ := P) hm').mem_of_tendsto
    ((hJc.tendsto g).comp (tendsto_trunc ht hg)) (Eventually.of_forall fun n => ?_)
  · obtain ⟨f, hf, hfe⟩ := hmem
    refine ⟨f, hf.measurable, ?_⟩
    filter_upwards [(wn_memLp hW g).coeFn_toLp, hfe] with ω h1 h2
    rw [← h1]; exact h2
  · set gn := (memLp_trunc g (measurableSet_Ioi.prod MeasurableSet.univ :
      MeasurableSet (Ioi (t n) ×ˢ (univ : Set ℂ)))).toLp _
    have hgm := hm n gn (supportedIn_trunc g (measurableSet_Ioi.prod MeasurableSet.univ))
    exact ⟨W gn, hgm.stronglyMeasurable, (wn_memLp hW gn).coeFn_toLp⟩

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- **(L3) for the coarse filtration**: the white-noise zero-boundary GFF on `U`, measurable
for any `m'` making `W g` measurable for `g` supported in `(t_n, ∞) × ℂ`, `t_n → 0`. -/
theorem exists_zbDistU_filt (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R)
    (hW : IsWhiteNoise P W) {m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0))
    (hm : ∀ n (g : WNSpace), SupportedIn (Ioi (t n) ×ˢ univ) g → Measurable[m'] (W g)) :
    ∃ hz : Ω → DistC, Measurable[m'] hz ∧
      (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbProcU W U φ) ∧
      ∀ ω, restrictTo (toOpens (closure U)ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0 := by
  let _ : MeasurableSpace Ω := mΩ
  exact exists_zbDistU_of_le hU hUR hW hm' (exists_version_of_supportedIn hW hm' ht hm)

end LQGMetric.CONF.ZBM
