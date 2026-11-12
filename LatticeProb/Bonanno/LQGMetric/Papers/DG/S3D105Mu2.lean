/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Mu2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D105 N4, part 2: `μ_ĥ` as the vague limit of `(2^{-k})^{γ²/2} e^{γ ĥ_{2^{-k}}} dz` (DG:984)

Ding–Gwynne, arXiv:1807.01072, DG:984 ("we can then define `μ_{h+f}` as the a.s. weak limit
`lim ε^{γ²/2} e^{γ(h+f)_ε(z)} dz`"), applied with `h = h^𝕍`, `f = ĥ − h^𝕍 = −Y` (DG:986).

* `ae_isVagueLimitOn_muOfMod`: a.s. `μ_ĥ|_{int K}` is the vague limit on `interior K` of the
  circle-average approximations of `ĥ` (any jointly measurable version `V`, which exists:
  `exists_hatCircVer`);
* `ae_muOfMod_restrict_eq`: independence of the modification `Y` (QZ `isVagueLimitOn_unique`);
* `ae_muHU_null`: `μ_{h^𝕍}` does not charge Lebesgue-null compacts `F ⊆ 𝕍` (first moment
  `lintegral_qAreaMeasureOn_le_of_cut` with cut-offs `(1 − d(·,F)/r)⁺`, circle-law transfer;
  a.e.-measurability `aemeasurable_qArea_open_circ`/`_compact_circ` as in
  `GMCIdent4.aemeasurable_qAreaMeasureOn_ball_circ`); hence `ae_muOfMod_restrict_interior`
  (`μ_ĥ` lives on `interior K` when `|∂K| = 0`) and the unrestricted form
  `ae_isVagueLimitOn_muOfMod'`;
* `ae_isVagueLimitOn_muHat`: DEC-105 N4 for `muHat` on `ferniqueBox y b` (convex, so its frontier
  is Lebesgue-null).

The deterministic core and the a.s. inputs are in `S3D105Mu.lean`. Deviation DV-D105-2 (replaces
the appeal to Rhodes–Vargas Thm 5.5, DG:988).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **D105 N4: `μ_ĥ` is the vague limit of its own circle-average approximations** (DG:984):
for `Y` a continuous modification of `h^𝕍 − ĥ` on the compact `K ⊆ 𝕍` and any jointly
measurable version `V k` of the circle averages `ĥ_{2^{-k}}`, a.s.
`(2^{-k})^{γ²/2} e^{γ ĥ_{2^{-k}}(z)} dz → μ_ĥ = e^{−γY} μ_{h^𝕍}` vaguely on `interior K` -/
theorem ae_isVagueLimitOn_muOfMod (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare) {Y : ℂ → Ω → ℝ}
    (hY : IsDGMod P K (fun z r ω => dgHU W z r ω - dgHat W z r ω) Y)
    {V : ℕ → ℂ → Ω → ℝ} (hVm : ∀ k, Measurable fun p : ℂ × Ω => V k p.1 p.2)
    (hV : ∀ k z, closedBall z (2 * (2 : ℝ)⁻¹ ^ k) ⊆ K →
      V k z =ᵐ[P] dgHat W z ((2 : ℝ)⁻¹ ^ k)) :
    ∀ᵐ ω ∂P, IsVagueLimitOn (interior K)
      (fun k => (volume.restrict (interior K)).withDensity fun z =>
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω)))
      ((muOfMod W γ K Y ω).restrict (interior K)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  set U := interior K with hUdef
  have hUo : IsOpen U := isOpen_interior
  have hUK : U ⊆ K := interior_subset
  have hUS : U ⊆ openSquare := hUK.trans hKU
  have hne : (Uᶜ).Nonempty := ⟨0, fun h => by have := hUS h; simp [openSquare] at this⟩
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [ae_isVagueLimitOn_wn hX hW hγ hγ2, ae_areaApprox_wnField_lt_top hW γ,
    ae_all_iff.2 (ae_ae_hatCirc_eq hW hUK hKU hY hVm hV)] with ω hvag hfin hdens
  have hvag' : IsVagueLimitOn openSquare (areaApprox γ (wnField W ω)) (muHU W γ ω) := hvag
  have hYc := hY.1 ω
  have hec : Continuous fun z => Real.exp (γ * -Y z ω) :=
    Real.continuous_exp.comp (continuous_const.mul hYc.neg)
  refine ⟨?_, fun C hC hCU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hUo.measurableSet.compl, compl_inter_self, measure_empty]
  · calc _ ≤ muOfMod W γ K Y ω univ :=
          (Measure.le_iff'.1 Measure.restrict_le_self C).trans (measure_mono (subset_univ C))
      _ < ⊤ := muOfMod_univ_lt_top W γ hK hKU hY.1 ω
  have hf0 : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hlim : ∫ z, f z ∂((muOfMod W γ K Y ω).restrict U) =
      ∫ z, f z * Real.exp (γ * -Y z ω) ∂(muHU W γ ω) := by
    unfold muOfMod
    rw [restrict_withDensity hUo.measurableSet, GMCIdent4.integral_withDensity_ofReal hec.measurable
      (fun _ => (Real.exp_pos _).le), Measure.restrict_restrict hUo.measurableSet,
      inter_eq_left.2 hUK, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hf0 z (fun h => hz (hfU h))])]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    ring
  rw [hlim]
  refine tendsto_integral_of_density hUS hvag' ?_ hec
    (ek := fun k z => Real.exp (γ * -∫ x, Y x ω ∂(circleUnif z (radius k)))) ?_ ?_ ?_ hf hfc hfU
  · intro C hC hCU
    obtain ⟨s, hs, hCs⟩ := exists_sqIn_of_isCompact hC (hCU.trans hUS)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / s)
    have hns : 1 / ((n : ℝ) + 2) ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hs] at hn
      nlinarith
    have hsub : sqIn s ⊆ sqIn (1 / ((n : ℝ) + 2)) := fun z ⟨a, b, c, d⟩ =>
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    filter_upwards [hr.eventually (gt_mem_nhds
      (show (0 : ℝ) < 1 / ((n : ℝ) + 2) / 2 by positivity))] with k hk
    exact (measure_mono (hCs.trans hsub)).trans_lt (hfin n k hk)
  · intro k
    exact Real.measurable_exp.comp ((((measurable_circAvg hY.1 hY.2.1 (radius k)).comp
      (measurable_id.prodMk measurable_const)).neg).const_mul γ)
  · intro C hC _
    exact tendstoUniformlyOn_exp_neg γ hC hYc (tendstoUniformlyOn_circleAvg hYc hC)
  · intro g hg hgc hgU
    have hg0 : ∀ z, z ∉ tsupport g → g z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
    obtain ⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ tsupport g, δ ≤ infDist z Uᶜ := by
      rcases (tsupport g).eq_empty_or_nonempty with he | hCne
      · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)⟩
      obtain ⟨z₀, hz₀, hmin⟩ := (hgc : IsCompact (tsupport g)).exists_isMinOn hCne
        (continuous_infDist_pt _).continuousOn
      exact ⟨_, (hUo.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h (hgU hz₀)),
        fun z hz => hmin hz⟩
    filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))] with k hk
    have hdm : Measurable fun z => ((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω) :=
      (Real.measurable_exp.comp (((hVm k).comp
        (measurable_id.prodMk measurable_const)).const_mul γ)).const_mul _
    have ham : Measurable fun z =>
        radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (wnField W ω) k z) :=
      have hav : Measurable fun z => avgReg (wnField W ω) k z :=
        (measurable_avgReg k).comp (f := fun z : ℂ => (wnField W ω, z))
          (measurable_const.prodMk measurable_id)
      (Real.measurable_exp.comp (hav.const_mul γ)).const_mul _
    rw [GMCIdent4.integral_withDensity_ofReal hdm (fun _ => by positivity)]
    unfold areaApprox
    rw [GMCIdent4.integral_withDensity_ofReal ham
      (fun _ => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by simp [hg0 z (fun h => hz (hgU h))]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by simp [hg0 z (fun h => hz (openSquare_subset_H (hUS (hgU h))))])]
    refine integral_congr_ae ?_
    filter_upwards [hdens k] with z hz
    by_cases hzC : z ∈ tsupport g
    · have hzD : z ∈ dSet U k := by
        show 2 * radius k < infDist z Uᶜ
        linarith [hδC z hzC]
      rcases hz with hz | hz
      · exact absurd hzD hz
      rw [hz, show γ * (avgReg (wnField W ω) k z - ∫ x, Y x ω ∂(circleUnif z (radius k))) =
        γ * avgReg (wnField W ω) k z + γ * -∫ x, Y x ω ∂(circleUnif z (radius k)) by ring,
        Real.exp_add]
      simp only [radius]
      ring
    · simp [hg0 z hzC]

/-! ### `μ_{h^𝕍}` does not charge Lebesgue-null compacts (so `μ_ĥ` does not charge `∂K`) -/

section Null

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {X : Ω₀ → Measure ℂ → ℝ}

/-- open-set masses are a.e.-measurable under the circle law (the proof of
`GMCIdent4.aemeasurable_qAreaMeasureOn_ball_circ`, for any bounded open `U ⊆ 𝕍`) -/
theorem aemeasurable_qArea_open_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {U : Set ℂ}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUU : U ⊆ openSquare) :
    AEMeasurable (fun v => qAreaMeasureOn γ (circExt v) openSquare U) (circLaw P₀ X) := by
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => by have := hUU h; simp [openSquare] at this⟩
  let F : (CircIdx → ℝ) → ℝ≥0∞ := fun v =>
    ⨆ n, ENNReal.ofReal (Prop16Area.Meas.Psi γ circExt (fun _ z => LQGMeas.openBump U n z) v)
  have hF : Measurable F := Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (Prop16Area.Meas.measurable_Psi γ measurable_circExt
      ((LQGMeas.continuous_openBump U n).measurable.comp measurable_snd))
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_isVagueLimitOn_circExt hX hγ hγ2] with v hm
  set μ := qAreaMeasureOn γ (circExt v) openSquare
  have hts : ∀ n, tsupport (LQGMeas.openBump U n) ⊆ openSquare := fun n =>
    (LQGMeas.tsupport_openBump_subset U n).trans hUU
  have ePsi : ∀ n, Prop16Area.Meas.Psi γ circExt (fun _ z => LQGMeas.openBump U n z) v =
      ∫ z, LQGMeas.openBump U n z ∂μ := fun n =>
    (hm.2.2 _ (LQGMeas.continuous_openBump U n) (LQGMeas.hasCompactSupport_openBump hUb n)
      (hts n)).limUnder_eq
  have eL : ∀ n, ENNReal.ofReal (∫ z, LQGMeas.openBump U n z ∂μ) =
      ∫⁻ z, ENNReal.ofReal (LQGMeas.openBump U n z) ∂μ := fun n =>
    ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hm.2.1 (LQGMeas.continuous_openBump U n)
        (LQGMeas.hasCompactSupport_openBump hUb n) (hts n))
      (ae_of_all _ (LQGMeas.openBump_nonneg U n))
  simp only [F, ePsi, eL]
  rw [← LQGMeas.measure_open_eq_iSup μ hUo hUc]

/-- radii `δ/(n+2) → 0⁺` -/
lemma tendsto_rad {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => by
    show 0 < δ / ((n : ℝ) + 2); positivity⟩
  have h := tendsto_const_nhds (x := δ) |>.div_atTop
    (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  exact h

/-- compact-set masses are a.e.-measurable under the circle law -/
theorem aemeasurable_qArea_compact_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {F : Set ℂ}
    (hF : IsCompact F) (hFU : F ⊆ openSquare) :
    AEMeasurable (fun v => qAreaMeasureOn γ (circExt v) openSquare F) (circLaw P₀ X) := by
  obtain ⟨δ, hδ, hδF⟩ := hF.exists_cthickening_subset_open isOpen_openSquare hFU
  set r : ℕ → ℝ := fun n => δ / ((n : ℝ) + 2)
  have hr : ∀ n, r n ≤ δ := fun n =>
    div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hsub : ∀ n, thickening (r n) F ⊆ openSquare := fun n =>
    (thickening_subset_cthickening_of_le (hr n) F).trans hδF
  have hG : AEMeasurable (fun v => ⨅ n, qAreaMeasureOn γ (circExt v) openSquare
      (thickening (r n) F)) (circLaw P₀ X) :=
    AEMeasurable.iInf fun n => aemeasurable_qArea_open_circ hX hγ hγ2 isOpen_thickening
      hF.isBounded.thickening (hsub n)
  refine hG.congr ?_
  filter_upwards [ae_isVagueLimitOn_circExt hX hγ hγ2] with v hm
  set μ := qAreaMeasureOn γ (circExt v) openSquare
  have hfin : ∃ R > 0, μ (thickening R F) ≠ ⊤ := ⟨δ, hδ, ne_top_of_le_ne_top
    (hm.2.1 _ hF.cthickening hδF).ne (measure_mono (thickening_subset_cthickening δ F))⟩
  have ht := (tendsto_measure_thickening_of_isClosed hfin hF.isClosed).comp (tendsto_rad hδ)
  refine le_antisymm (ge_of_tendsto' ht fun n => iInf_le _ n) ?_
  exact le_iInf fun n => measure_mono (self_subset_thickening (by positivity) F)

end Null

/-- **`μ_{h^𝕍}` does not charge Lebesgue-null compacts**: a.s. `μ_{h^𝕍}(F) = 0` for a compact
`F ⊆ 𝕍` with `|F| = 0` (first moment `E μ(F) ≤ C_γ ∫ φ`, DZZ Lemma 2.10 /
`lintegral_qAreaMeasureOn_le_of_cut`, for cut-offs `φ` of `F`; transferred by the circle law) -/
theorem ae_muHU_null (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {F : Set ℂ}
    (hF : IsCompact F) (hFU : F ⊆ openSquare) (hF0 : volume F = 0) :
    ∀ᵐ ω ∂P, muHU W γ ω F = 0 := by
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun _ => measure_empty
  obtain ⟨δ, hδ, hδF⟩ := hF.exists_cthickening_subset_open isOpen_openSquare hFU
  set g := fun v => qAreaMeasureOn γ (circExt v) openSquare F
  have hG : AEMeasurable g (circLaw P₀ X) := aemeasurable_qArea_compact_circ hX hγ hγ2 hF hFU
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  -- first moment bound with the cut-offs `φ_r = (1 − d(·,F)/r)⁺`
  have hbound : ∀ r : ℝ, 0 < r → r ≤ δ → ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare F ∂P₀ ≤
      gmcConst γ * volume (thickening r F) := by
    intro r hr hrδ
    set φ : ℂ → ℝ := fun z => max 0 (1 - infDist z F / r) with hφ
    have hφc : Continuous φ :=
      continuous_const.max (continuous_const.sub ((continuous_infDist_pt F).div_const r))
    have hsupp : ∀ z, φ z ≠ 0 → z ∈ thickening r F := by
      intro z hz
      rw [mem_thickening_iff_infDist_lt hne]
      by_contra h
      push Not at h
      apply hz
      refine max_eq_left ?_
      have : 1 ≤ infDist z F / r := (le_div_iff₀ hr).2 (by linarith)
      linarith
    have hts : tsupport φ ⊆ cthickening δ F :=
      (closure_minimal (fun z hz => thickening_subset_cthickening _ _ (hsupp z hz))
        isClosed_cthickening).trans (cthickening_mono hrδ F)
    have hφs : HasCompactSupport φ :=
      IsCompact.of_isClosed_subset hF.cthickening (isClosed_tsupport _) hts
    have h0 : ∀ z, 0 ≤ φ z := fun z => le_max_left _ _
    have h1 : ∀ z, φ z ≤ 1 := fun z => max_le zero_le_one (by
      have := div_nonneg (infDist_nonneg (x := z) (s := F)) hr.le
      linarith)
    have hK1 : ∀ z ∈ F, φ z = 1 := fun z hz => by
      simp only [hφ, infDist_zero_of_mem hz, zero_div, sub_zero]; norm_num
    refine (lintegral_qAreaMeasureOn_le_of_cut hX γ hφc hφs (hts.trans hδF) h0 h1 hK1).trans ?_
    gcongr
    calc ∫⁻ z, ENNReal.ofReal (φ z)
        ≤ ∫⁻ z, (thickening r F).indicator 1 z := lintegral_mono fun z => by
          by_cases hz : z ∈ thickening r F
          · simp only [indicator_of_mem hz, Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (h1 z)
          · have : φ z = 0 := by by_contra h; exact hz (hsupp z h)
            simp [this]
      _ = volume (thickening r F) := lintegral_indicator_one isOpen_thickening.measurableSet
  have hvol : Tendsto (fun n : ℕ => volume (thickening (δ / ((n : ℝ) + 2)) F)) atTop (𝓝 0) := by
    have := (tendsto_measure_thickening_of_isClosed
      ⟨δ, hδ, (hF.isBounded.thickening (δ := δ)).measure_lt_top (μ := volume).ne⟩ hF.isClosed).comp (tendsto_rad hδ)
    rwa [hF0] at this
  have hC : gmcConst γ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hlim := ENNReal.Tendsto.const_mul hvol (Or.inr hC)
  rw [mul_zero] at hlim
  have hE : ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare F ∂P₀ = 0 :=
    le_antisymm (ge_of_tendsto' hlim fun n => hbound _ (by positivity)
      (div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))) bot_le
  have hE' : ∫⁻ v, g v ∂(circLaw P₀ X) = 0 := by
    rw [lintegral_map' hG hm.aemeasurable]
    simp only [g, qAreaMeasureOn_circExt]
    exact hE
  have hν : ∀ᵐ v ∂(circLaw P₀ X), g v = 0 := (lintegral_eq_zero_iff' hG).1 hE'
  have hW' : ∀ᵐ ω ∂P, g (wnCircVec W ω) = 0 := by
    refine ae_of_ae_map (p := fun v => g v = 0) (measurable_wnCircVec hW).aemeasurable ?_
    rw [← map_circVec_eq hX hW]; exact hν
  exact hW'

/-- `μ_ĥ = e^{−γY} μ_{h^𝕍}|_K` lives on `interior K` when `|∂K| = 0` -/
theorem ae_muOfMod_restrict_interior (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare)
    (hK0 : volume (frontier K) = 0) (Y : ℂ → Ω → ℝ) :
    ∀ᵐ ω ∂P, (muOfMod W γ K Y ω).restrict (interior K) = muOfMod W γ K Y ω := by
  have hfK : frontier K ⊆ K := hK.isClosed.frontier_subset
  filter_upwards [ae_muHU_null hW hγ hγ2 (hK.of_isClosed_subset isClosed_frontier hfK)
    (hfK.trans hKU) hK0] with ω h
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine withDensity_absolutelyContinuous _ _ ?_
  show ((muHU W γ ω).restrict K) (interior K)ᶜ = 0
  rw [Measure.restrict_apply isOpen_interior.measurableSet.compl]
  refine measure_mono_null (fun x (hx : x ∈ (interior K)ᶜ ∩ K) =>
    (⟨subset_closure hx.2, hx.1⟩ : x ∈ frontier K)) h

/-- **D105 N4 (unrestricted form)**: if `|∂K| = 0`, a.s. `μ_ĥ` itself is the vague limit on
`interior K` of `(2^{-k})^{γ²/2} e^{γ ĥ_{2^{-k}}(z)} dz` -/
theorem ae_isVagueLimitOn_muOfMod' (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare) (hK0 : volume (frontier K) = 0)
    {Y : ℂ → Ω → ℝ} (hY : IsDGMod P K (fun z r ω => dgHU W z r ω - dgHat W z r ω) Y)
    {V : ℕ → ℂ → Ω → ℝ} (hVm : ∀ k, Measurable fun p : ℂ × Ω => V k p.1 p.2)
    (hV : ∀ k z, closedBall z (2 * (2 : ℝ)⁻¹ ^ k) ⊆ K →
      V k z =ᵐ[P] dgHat W z ((2 : ℝ)⁻¹ ^ k)) :
    ∀ᵐ ω ∂P, IsVagueLimitOn (interior K)
      (fun k => (volume.restrict (interior K)).withDensity fun z =>
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω)))
      (muOfMod W γ K Y ω) := by
  filter_upwards [ae_isVagueLimitOn_muOfMod hW hγ hγ2 hK hKU hY hVm hV,
    ae_muOfMod_restrict_interior hW hγ hγ2 hK hKU hK0 Y] with ω h1 h2
  rwa [h2] at h1

lemma volume_frontier_ferniqueBox (y : ℂ) (b : ℝ) : volume (frontier (ferniqueBox y b)) = 0 := by
  have hc : Convex ℝ (ferniqueBox y b) := by
    have e : ferniqueBox y b = convexHull ℝ (ferniqueBox y b) := by
      unfold ferniqueBox
      rw [Complex.convexHull_reProdIm, (convex_Icc _ _).convexHull_eq,
        (convex_Icc _ _).convexHull_eq]
    rw [e]; exact convex_convexHull ℝ _
  exact hc.addHaar_frontier volume

/-- **N4 for `muHat`** (DEC-105 §3 N4): on the box `K = ferniqueBox y b`, a.s. `μ_ĥ` is the vague
limit on `interior K` of `(2^{-k})^{γ²/2} e^{γ ĥ_{2^{-k}}(z)} dz`, for any jointly measurable
version `V` of the circle averages of `ĥ` (one exists: `exists_hatCircVer`) -/
theorem ae_isVagueLimitOn_muHat (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {V : ℕ → ℂ → Ω → ℝ} (hVm : ∀ k, Measurable fun p : ℂ × Ω => V k p.1 p.2)
    (hV : ∀ k z, closedBall z (2 * (2 : ℝ)⁻¹ ^ k) ⊆ ferniqueBox y b →
      V k z =ᵐ[P] dgHat W z ((2 : ℝ)⁻¹ ^ k)) :
    ∀ᵐ ω ∂P, IsVagueLimitOn (interior (ferniqueBox y b))
      (fun k => (volume.restrict (interior (ferniqueBox y b))).withDensity fun z =>
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω)))
      (muHat hW γ hb hK ω) :=
  ae_isVagueLimitOn_muOfMod' hW hγ hγ2 (isCompact_ferniqueBox y b) (ferniqueBox_subset hK)
    (volume_frontier_ferniqueBox y b) (hatMod_spec hW hb hK) hVm hV

end DG
end LQGMetric
