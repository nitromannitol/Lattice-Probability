/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.UnzipInvariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm15
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm12
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.Algebra
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardHolo
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.Main

/-!
# `Γ⁰` is invariant under unzipping (blueprint node B1)

Task S5-B1. Conditionally on Theorem 1.2 (`theorem1_2`), for `κ > 0`, `γ = √κ`, `t > 0`, a
Brownian motion `B` and a free field `X ⊥ B`, the configuration
`c ω = (𝔥₀ + X ω, √κ B(·, ω))` satisfies

* `configLawMod0 (zipCapDown γ t ∘ c) P = configLawMod0 c P` (Corollary 1.5(a) at time `-t`),
* the unzipped field is independent of the future driver `s ↦ W(t+s) - W t`.

Route (blueprint B1):
1. `fwdMapInv W t = revMap V t` on `ℍ` for the time-reversed driver `V s = W(t-s) - W t`
   (`fwdMapInv_eq_revMap_timeRev`).
2. `B'_s = B_{t-s} + B_{max s t} - 2 B_t` is a Brownian motion (`isBrownianReal_revBM`), a
   function of `B`, hence independent of `X`, and `√κ B' = V` on `[0,t]`.
3. For a deterministic good measure `ν`, a.s. `evalReg (𝔥₀ + X) ν = ∫ 𝔥₀ dν + X ν`
   (`ae_evalReg_h0rev_add`, mean-value property of `log` plus the GFF regularization lemma);
   with independence this gives, for every test function, a.s. equality of the raw pairings of
   the unzipped field and of the Theorem 1.2 field `𝔥_t(V) + X ∘ revMap V t`.
4. Theorem 1.2 for `(B', X)` identifies the field law; the weak Markov property gives the
   driver law and the independence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace UnzipInvariance

open CharFun

/-! ## 1. Unzipping is the reverse flow of the time-reversed driver -/

/-- **A1(c)** for `T ≥ 0` (the version in `Loewner/Algebra` assumes `T > 0`). -/
theorem fwdMap_revMap_timeRev_of_nonneg (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) :
    revMap W T z ∉ fwdHull (fun s => W (T - s) - W T) T ∧
      fwdMap (fun s => W (T - s) - W T) T (revMap W T z) = z := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  rw [revMap_eq W hW z hT le_rfl hu]
  obtain ⟨hf, hu0⟩ := LoewnerAlgebra.isForwardSol_of_isReverseSol hW0 hu hT
  have hV : Continuous fun s => W (T - s) - W T :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have him : 0 < (u T).im := (hu.2 T ⟨hT, le_rfl⟩).1
  refine ⟨?_, ?_⟩
  · have hzT : 0 < ((fun s => u (T - s)) T).im := by
      simp only [sub_self, hu0]; exact hz
    obtain ⟨ε, hε, w, hw⟩ := exists_isForwardSol_small
      (W := fun r => (fun s => W (T - s) - W T) (T + r) - (fun s => W (T - s) - W T) T)
      (by fun_prop) hzT
    exact LoewnerAlgebra.not_mem_fwdHull_of_sol hT (by linarith : T < T + ε)
      ⟨_, LoewnerAlgebra.isForwardSol_glue hT hε.le hf hw⟩
  · rw [fwdMap_eq hV him hf ⟨hT, le_rfl⟩]
    simp only [sub_self, hu0]

/-- The inverse forward map at time `t` is the reverse map driven by the time-reversed
increment `s ↦ W (t - s) - W t` (Maps.lean docstring, item 1). -/
theorem fwdMapInv_eq_revMap_timeRev (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv W t w = revMap (fun s => W (t - s) - W t) t w := by
  set V : ℝ → ℝ := fun s => W (t - s) - W t with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hVV : (fun s => V (t - s) - V t) = W := by
    funext s; simp only [hVdef, sub_sub_cancel, sub_self, hW0]; ring
  obtain ⟨h1, h2⟩ := fwdMap_revMap_timeRev_of_nonneg V hV hV0 ht hw
  rw [hVV] at h1 h2
  have hmem : revMap V t w ∈ H \ fwdHull W t :=
    ⟨lt_of_lt_of_le hw (im_le_im_revMap V hV w hw ht), h1⟩
  have hex : ∃! z', z' ∈ H \ fwdHull W t ∧ fwdMap W t z' = w :=
    ⟨revMap V t w, ⟨hmem, h2⟩, fun y hy =>
      FwdHolo.injOn_fwdMap hW ht hy.1 hmem (hy.2.trans h2.symm)⟩
  unfold fwdMapInv
  rw [dif_pos hex]
  exact hex.unique hex.choose_spec.1 ⟨hmem, h2⟩

/-- Coordinate changes by maps agreeing on `ℍ` agree on measures concentrated on `ℍ`. -/
theorem coordChange_congr_of_eqOn {f g : ℂ → ℂ} (hfg : EqOn f g H) {μ : Measure ℂ}
    (hμ : μ Hᶜ = 0) (y : FieldSample) (Q : ℝ) :
    coordChange y f Q μ = coordChange y g Q μ := by
  have hae : ∀ᵐ z ∂μ, z ∈ H := ae_iff.2 hμ
  unfold coordChange
  congr 1
  · congr 1
    exact Measure.map_congr (hae.mono fun z hz => hfg hz)
  · congr 1
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    show Real.log ‖deriv f z‖ = Real.log ‖deriv g z‖
    have hev : f =ᶠ[𝓝 z] g := Filter.eventually_of_mem (isOpen_H.mem_nhds hz) fun w hw => hfg hw
    rw [hev.deriv_eq]

theorem tdens_compl_H (ρ : TestFun H) :
    tdens ρ.1 Hᶜ = 0 ∧ tdens (fun z => -ρ.1 z) Hᶜ = 0 := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  exact ⟨measure_mono_null (compl_subset_compl.2 hd.subH) hd.tdens_compl,
    measure_mono_null (compl_subset_compl.2 hd.neg.subH) hd.neg.tdens_compl⟩

theorem pairRaw_coordChange_congr {f g : ℂ → ℂ} (hfg : EqOn f g H) (y : FieldSample) (Q : ℝ)
    (ρ : TestFun H) :
    pairRaw (coordChange y f Q) ρ.1 = pairRaw (coordChange y g Q) ρ.1 := by
  obtain ⟨h1, h2⟩ := tdens_compl_H ρ
  rw [pairRaw_eq_tdens, pairRaw_eq_tdens, coordChange_congr_of_eqOn hfg h1,
    coordChange_congr_of_eqOn hfg h2]

/-! ## 2. Regularized evaluation of `𝔥₀ + X` -/

theorem measurable_h0rev (κ : ℝ) : Measurable (h0rev κ) := by
  unfold h0rev
  exact measurable_const.mul (Real.measurable_log.comp measurable_norm)

/-- Mean-value property: the folded circle average of `𝔥₀` over a circle inside `ℍ`. -/
theorem ofFun_h0rev_foldedCircle (κ : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r) (hrc : r ≤ c.im) :
    ofFun (h0rev κ) (foldedCircle c r) = h0rev κ c := by
  rw [foldedCircle_eq_circleUnif hr.le hrc]
  unfold ofFun h0rev
  rw [integral_const_mul]
  have := integral_log_norm_sub_circleUnif c 0 hr
  simp only [sub_zero] at this
  rw [this, max_eq_right (hrc.trans ((le_abs_self _).trans (Complex.abs_im_le_norm c)))]

theorem tendsto_ofFun_h0rev (κ : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r) (hrz : r < z.im) :
    Tendsto (fun n => ofFun (h0rev κ) (foldedCircle (dyadicRoundC n z) r)) atTop
      (𝓝 (h0rev κ z)) := by
  have hz : z ∈ H := hr.trans hrz
  have hd := RegClosure.tendsto_dyadicRoundC z
  have hev : ∀ᶠ n in atTop, r ≤ (dyadicRoundC n z).im := by
    have : Tendsto (fun n => (dyadicRoundC n z).im) atTop (𝓝 z.im) :=
      (Complex.continuous_im.tendsto z).comp hd
    exact (this.eventually (lt_mem_nhds hrz)).mono fun n hn => hn.le
  have hc : Tendsto (fun n => h0rev κ (dyadicRoundC n z)) atTop (𝓝 (h0rev κ z)) :=
    ((continuousOn_h0rev κ).continuousAt (isOpen_H.mem_nhds hz)).tendsto.comp hd
  exact hc.congr' (hev.mono fun n hn => (ofFun_h0rev_foldedCircle κ hr hn).symm)

/-- **Regularization lemma for `𝔥₀ + X`.** For a measure with bounded density vanishing off a
compact subset of `{δ < Im z}`, almost surely `evalReg (𝔥₀ + X ω) ν = ∫ 𝔥₀ dν + X ω ν`. -/
theorem ae_evalReg_h0rev_add (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {ν : Measure ℂ} {M : ℝ≥0} (hν : ν ≤ (M : ℝ≥0∞) • volume) {K : Set ℂ} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) (hKδ : K ⊆ {z | δ < z.im}) (hνK : ν Kᶜ = 0) :
    ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω) ν = (∫ z, h0rev κ z ∂ν) + X ω ν := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hgood : SmoothConv.IsGoodSC M R ν := ⟨hν, measure_mono_null (Set.compl_subset_compl.2
    (Set.subset_inter hR fun z hz => (hδ.trans (hKδ hz)).le)) hνK⟩
  have := hgood.isFiniteMeasure
  have him : ∀ᵐ w ∂ν, δ < w.im :=
    ae_iff.2 (measure_mono_null (fun z hz hzK => hz (hKδ hzK)) hνK)
  have haeK : ∀ᵐ z ∂ν, z ∈ K := ae_iff.2 hνK
  have hKH : K ⊆ H := fun z hz => hδ.trans (hKδ hz)
  have hKc : IsCompact (Metric.closedBall (0 : ℂ) R ∩ Hbar) :=
    (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (X ω) k z ∂ν =
      X ω (ν.bind fun w => foldedCircle w (radius k)) :=
    ae_all_iff.2 fun k =>
      Regularization.ae_integral_avgReg_eq hX k ν hKc Set.inter_subset_right hgood.2
  have h2 := Regularization.ae_tendsto_smooth_single hX hδ hgood him
  have h3 : ∀ᵐ ω ∂P, ∀ k, ∀ z ∈ Hbar,
      Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k))) atTop
        (𝓝 (avgReg (X ω) k z)) :=
    ae_all_iff.2 fun k => (BdryExist.ae_avgReg_spec hX k).1
  have hcont : ∀ k : ℕ, ∃ Y : ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun z => Y z ω) Hbar) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ Hbar, avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) := by
    intro k
    obtain ⟨Y, hY, -, hl⟩ := exists_continuous_circleAvg hX k 0 (by simp [Hbar])
    exact ⟨Y, hY, hl⟩
  choose Y hYc hYl using hcont
  have h4 : ∀ᵐ ω ∂P, ∀ k, ContinuousOn (avgReg (X ω) k) Hbar := by
    filter_upwards [ae_all_iff.2 hYl] with ω hω k
    exact ((hYc k ω).add continuousOn_const).congr fun z hz => hω k z hz
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).eventually (gt_mem_nhds hδ))
  have hh0 : Integrable (h0rev κ) ν := by
    have : IntegrableOn (h0rev κ) K ν :=
      ((continuousOn_h0rev κ).mono hKH).integrableOn_compact hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem haeK] at this
  filter_upwards [h1, h2, h3, h4] with ω h1 h2 h3 h4
  have hsplit : ∀ k, k₀ ≤ k → ∫ z, avgReg (ofFun (h0rev κ) + X ω) k z ∂ν =
      (∫ z, h0rev κ z ∂ν) + X ω (ν.bind fun w => foldedCircle w (radius k)) := by
    intro k hk
    have hrk : radius k < δ := hk₀ k hk
    have hXi : Integrable (avgReg (X ω) k) ν := by
      have : IntegrableOn (avgReg (X ω) k) K ν :=
        ((h4 k).mono (hKH.trans H_subset_Hbar)).integrableOn_compact hK
      rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem haeK] at this
    rw [← h1 k, ← integral_add hh0 hXi]
    refine integral_congr_ae (haeK.mono fun z hz => ?_)
    have hzr : radius k < z.im := hrk.trans (hKδ hz)
    exact ((tendsto_ofFun_h0rev κ (radius_pos k) hzr).add
      (h3 k z (H_subset_Hbar (hKH hz)))).limUnder_eq
  unfold evalReg
  refine (Tendsto.congr' ?_ (h2.const_add (∫ z, h0rev κ z ∂ν))).limUnder_eq
  exact (eventually_ge_atTop k₀).mono fun k hk => (hsplit k hk).symm

/-! ## 3. The unzipped field versus the Theorem 1.2 field, for a fixed driver path -/

theorem integrable_tdens {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) {g : ℂ → ℝ}
    (hg : ContinuousOn g H) : Integrable g (tdens a) := by
  have := hd.admissible.1
  have hae : ∀ᵐ z ∂(tdens a), z ∈ K := ae_iff.2 hd.tdens_compl
  have : IntegrableOn g K (tdens a) := (hg.mono hd.subH).integrableOn_compact hd.compact
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this

theorem continuousOn_h0rev_revMap (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ}
    (hT : 0 ≤ T) : ContinuousOn (fun z => h0rev κ (revMap W T z)) H :=
  (continuousOn_h0rev κ).comp (differentiableOn_revMap W hW hT).continuousOn fun z hz =>
    show 0 < (revMap W T z).im from lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hT)

theorem continuousOn_log_deriv_revMap {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun z => Real.log ‖deriv (revMap W T) z‖) H :=
  ContinuousOn.log (((differentiableOn_revMap W hW hT).deriv isOpen_H).continuousOn.norm)
    fun z hz => norm_ne_zero_iff.2 (deriv_revMap_ne_zero W hW hT hz)

/-- `∫ 𝔥_T = ∫ 𝔥₀ ∘ f_T + Q ∫ log |f_T'|` against a test density. -/
theorem integral_hTrev_split (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hm : Measurable (revMap W T)) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) :
    ∫ z, hTrev κ W T z ∂(tdens a) = (∫ w, h0rev κ w ∂((tdens a).map (revMap W T))) +
      Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap W T) z‖ ∂(tdens a) := by
  rw [integral_map hm.aemeasurable (measurable_h0rev κ).aestronglyMeasurable,
    ← integral_const_mul,
    ← integral_add (integrable_tdens hd (continuousOn_h0rev_revMap κ hW hT))
      ((integrable_tdens hd (continuousOn_log_deriv_revMap hW hT)).const_mul _)]
  rfl

/-- Deterministic identity: if `evalReg` of `𝔥₀ + x` at the pushforward splits, then the
unzipped field and the Theorem 1.2 field agree at the test density. -/
theorem coordChange_eq_of_split (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hm : Measurable (revMap W T)) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ)
    (x : FieldSample)
    (hsplit : evalReg (ofFun (h0rev κ) + x) ((tdens a).map (revMap W T)) =
      (∫ w, h0rev κ w ∂((tdens a).map (revMap W T))) + evalReg x ((tdens a).map (revMap W T))) :
    coordChange (ofFun (h0rev κ) + x) (revMap W T) (Qc (Real.sqrt κ)) (tdens a) =
      (ofFun (hTrev κ W T) + coordChange x (revMap W T) 0) (tdens a) := by
  show evalReg (ofFun (h0rev κ) + x) ((tdens a).map (revMap W T)) + _ * _ =
    ofFun (hTrev κ W T) (tdens a) + (evalReg x ((tdens a).map (revMap W T)) + 0 * _)
  rw [hsplit, zero_mul, add_zero,
    show ofFun (hTrev κ W T) (tdens a) = ∫ z, hTrev κ W T z ∂(tdens a) from rfl,
    integral_hTrev_split κ hW hT hm hd]
  ring

theorem pairRaw_unzip_eq (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hm : Measurable (revMap W T)) (ρ : TestFun H) (x : FieldSample)
    (h1 : evalReg (ofFun (h0rev κ) + x) ((tdens ρ.1).map (revMap W T)) =
      (∫ w, h0rev κ w ∂((tdens ρ.1).map (revMap W T))) +
        evalReg x ((tdens ρ.1).map (revMap W T)))
    (h2 : evalReg (ofFun (h0rev κ) + x) ((tdens fun z => -ρ.1 z).map (revMap W T)) =
      (∫ w, h0rev κ w ∂((tdens fun z => -ρ.1 z).map (revMap W T))) +
        evalReg x ((tdens fun z => -ρ.1 z).map (revMap W T))) :
    pairRaw (coordChange (ofFun (h0rev κ) + x) (revMap W T) (Qc (Real.sqrt κ))) ρ.1 =
      pairRaw (ofFun (hTrev κ W T) + coordChange x (revMap W T) 0) ρ.1 := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  rw [pairRaw_eq_tdens, pairRaw_eq_tdens, coordChange_eq_of_split κ hW hT hm hd x h1,
    coordChange_eq_of_split κ hW hT hm hd.neg x h2]

theorem ae_split_fixed (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ}
    (hd : Dens a K M δ) :
    ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω) ((tdens a).map (revMap (Wof κ T hT f) T)) =
      (∫ w, h0rev κ w ∂((tdens a).map (revMap (Wof κ T hT f) T))) +
        evalReg (X ω) ((tdens a).map (revMap (Wof κ T hT f) T)) := by
  obtain ⟨M', hle, hc, hK', hsub⟩ := push_facts (goodMap_Wof κ T hT f) hd
  filter_upwards [ae_evalReg_h0rev_add κ hX hle hK' hd.delta hsub hc,
    ae_evalReg_eq_of_le_smul_volume hX hle hK' hd.delta hsub hc] with ω h1 h2
  rw [h1, h2]

theorem measurable_add_left (y : FieldSample) : Measurable fun x : FieldSample => y + x := by
  have h : ∀ μ : Measure ℂ, Measurable fun x : FieldSample => y μ + x μ :=
    fun μ => (measurable_pi_apply μ).const_add _
  exact measurable_pi_iff.2 h

theorem measurable_evalReg_h0rev_push (κ T : ℝ) (hT : 0 ≤ T) (a : ℂ → ℝ) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg (ofFun (h0rev κ) + p.2) ((tdens a).map (revMap (Wof κ T hT p.1) T)) := by
  have hpair : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      ((p.1, ofFun (h0rev κ) + p.2) : C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
    measurable_fst.prodMk ((measurable_add_left _).comp measurable_snd)
  have key := (measurable_evalReg_push κ T hT a).comp hpair
  simp only [Function.comp_def] at key
  exact key

theorem measurable_integral_h0rev_push (κ T : ℝ) (hT : 0 ≤ T) (a : ℂ → ℝ) :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ w, h0rev κ w ∂((tdens a).map (revMap (Wof κ T hT f) T)) := by
  have heq : ∀ f : C(Icc (0 : ℝ) T, ℝ),
      ∫ w, h0rev κ w ∂((tdens a).map (revMap (Wof κ T hT f) T)) =
        ∫ z, h0rev κ (Fm κ T hT (f, z)) ∂(tdens a) := fun f =>
    integral_map (measurable_revMap_Wof κ T hT f).aemeasurable
      (measurable_h0rev κ).aestronglyMeasurable
  rw [show (fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ w, h0rev κ w ∂((tdens a).map (revMap (Wof κ T hT f) T))) = _ from funext heq]
  exact (((measurable_h0rev κ).comp (measurable_Fm κ T hT)).stronglyMeasurable.integral_prod_right').measurable

theorem measurable_integral_log_deriv (κ T : ℝ) (hT : 0 ≤ T) {a : ℂ → ℝ} {K : Set ℂ}
    {M δ : ℝ} (hd : Dens a K M δ) :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ z, Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ ∂(tdens a) := by
  have heq : ∀ f : C(Icc (0 : ℝ) T, ℝ),
      ∫ z, Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ ∂(tdens a) =
        ∫ z, Real.log ‖Dm κ T hT (f, z)‖ ∂(tdens a) := fun f =>
    integral_congr_ae ((ae_iff.2 hd.tdens_compl).mono fun z hz => by
      show Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ = Real.log ‖Dm κ T hT (f, z)‖
      rw [Dm_eq κ T hT f (hd.subH hz)])
  rw [show (fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ z, Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ ∂(tdens a)) = _ from funext heq]
  exact ((Real.measurable_log.comp (measurable_Dm κ T hT).norm).stronglyMeasurable.integral_prod_right').measurable

/-- The raw pairing of the unzipped field (for a driver path `p.1` and a field sample `p.2`) is
jointly measurable. -/
theorem measurable_pair_unzip (κ T : ℝ) (hT : 0 ≤ T) (ρ : TestFun H) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      pairRaw (coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ T hT p.1) T)
        (Qc (Real.sqrt κ))) ρ.1 := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  have hc : ∀ {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ}, Dens a K M δ →
      Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
        coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ T hT p.1) T) (Qc (Real.sqrt κ))
          (tdens a) := fun {a} {K} {M} {δ} hd =>
    (measurable_evalReg_h0rev_push κ T hT a).add
      (((measurable_integral_log_deriv κ T hT hd).comp measurable_fst).const_mul _)
  exact (hc hd).sub (hc hd.neg)

theorem ae_split_random (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) :
    ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω) ((tdens a).map (revMap (Wof κ T hT (g ω)) T)) =
      (∫ w, h0rev κ w ∂((tdens a).map (revMap (Wof κ T hT (g ω)) T))) +
        evalReg (X ω) ((tdens a).map (revMap (Wof κ T hT (g ω)) T)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hE : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      evalReg (ofFun (h0rev κ) + p.2) ((tdens a).map (revMap (Wof κ T hT p.1) T)) =
        (∫ w, h0rev κ w ∂((tdens a).map (revMap (Wof κ T hT p.1) T))) +
          evalReg p.2 ((tdens a).map (revMap (Wof κ T hT p.1) T))} :=
    measurableSet_eq_fun (measurable_evalReg_h0rev_push κ T hT a)
      (((measurable_integral_h0rev_push κ T hT a).comp measurable_fst).add
        (measurable_evalReg_push κ T hT a))
  exact ae_indep hg hXm hind hE fun f => ae_split_fixed κ hT f hX hd

/-- For a random driver path independent of the field, the raw pairings of the unzipped field
and of the Theorem 1.2 field agree almost surely, test function by test function. -/
theorem ae_pairRaw_unzip_eq_Y2f (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P) (ρ : TestFun H) :
    ∀ᵐ ω ∂P, pairRaw (coordChange (ofFun (h0rev κ) + X ω) (revMap (Wof κ T hT (g ω)) T)
      (Qc (Real.sqrt κ))) ρ.1 = pairRaw (Y2f κ T hT (g ω) (X ω)) ρ.1 := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  filter_upwards [ae_split_random κ hT hX hg hind hd,
    ae_split_random κ hT hX hg hind hd.neg] with ω h1 h2
  exact pairRaw_unzip_eq κ (continuous_Wof κ T hT (g ω)) hT
    (measurable_revMap_Wof κ T hT (g ω)) ρ (X ω) h1 h2

/-! ## 4. Laws on product spaces -/

/-- Two measurable maps into a product of real lines whose coordinates agree almost surely
(coordinate by coordinate) have the same law. -/
theorem map_eq_of_forall_ae_eq {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f g : Ω → ι → ℝ} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ i, ∀ᵐ ω ∂P, f ω i = g ω i) : P.map f = P.map g := by
  classical
  refine (map_eq_iff_forall_finset_map_restrict_eq (X := fun i ω => f ω i)
    (Y := fun i ω => g ω i) hf.aemeasurable hg.aemeasurable).2 fun I => ?_
  refine Measure.map_congr ?_
  filter_upwards [ae_all_iff.2 fun i : I => h i.1] with ω hω
  funext i
  exact hω i

/-- Independent join: if `m₁, m₂ ≤ m_B` are independent and `m_X` is independent of `m_B`, then
`m₁ ⊔ m_X` is independent of `m₂`. -/
theorem indep_sup_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m₁ m₂ mX mB : MeasurableSpace Ω} (h₁ : m₁ ≤ mB) (h₂ : m₂ ≤ mB)
    (hmB : mB ≤ mΩ) (hmX : mX ≤ mΩ) (h12 : Indep m₁ m₂ P) (hXB : Indep mX mB P) :
    Indep (m₁ ⊔ mX) m₂ P := by
  refine IndepSets.indep (sup_le (h₁.trans hmB) hmX) (h₂.trans hmB)
    (GermZeroOne.isPiSystem_rectSets m₁ mX) (@MeasurableSpace.isPiSystem_measurableSet Ω m₂)
    (GermZeroOne.sup_eq_generateFrom_rectSets m₁ mX)
    (@MeasurableSpace.generateFrom_measurableSet Ω m₂).symm ?_
  rw [IndepSets_iff]
  rintro _ D ⟨A, C, hA, hC, rfl⟩ hD
  have e1 : P (C ∩ (A ∩ D)) = P C * P (A ∩ D) :=
    (Indep_iff _ _ _).1 hXB C (A ∩ D) hC ((h₁ A hA).inter (h₂ D hD))
  have e2 : P (A ∩ D) = P A * P D := (Indep_iff _ _ _).1 h12 A D hA hD
  have e3 : P (C ∩ A) = P C * P A := (Indep_iff _ _ _).1 hXB C A hC (h₁ A hA)
  calc P (A ∩ C ∩ D) = P (C ∩ (A ∩ D)) := by
        congr 1; ext ω; simp only [mem_inter_iff]; tauto
    _ = P C * (P A * P D) := by rw [e1, e2]
    _ = P (A ∩ C) * P D := by rw [inter_comm A C, e3, mul_assoc]

/-! ## 5. The time-reversed Brownian motion -/

/-- Time reversal of `B` at time `τ`, continued after `τ`: `B'_s = B_{τ-s} + B_{max s τ} - 2B_τ`,
i.e. `B_{τ-s} - B_τ` for `s ≤ τ` and `B_s - 2 B_τ` for `s ≥ τ` (when `B_0 = 0`). -/
def revBM {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (s : ℝ≥0) : Ω → ℝ :=
  B (τ - s) + B (max s τ) - (2 : ℝ) • B τ

@[simp] theorem revBM_apply {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ s : ℝ≥0) (ω : Ω) :
    revBM B τ s ω = B (τ - s) ω + B (max s τ) ω - 2 * B τ ω := by
  simp [revBM]

section Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem isGaussianProcess_revBM {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (τ : ℝ≥0) :
    IsGaussianProcess (revBM B τ) P :=
  hB.isGaussianProcess.of_isGaussianProcess fun s => ⟨{τ - s, max s τ, τ},
    { toFun x := x ⟨τ - s, by simp⟩ + x ⟨max s τ, by simp⟩ - 2 * x ⟨τ, by simp⟩
      map_add' x y := by simp; ring
      map_smul' c x := by simp; ring }, fun ω => by simp [Finset.restrict_def]⟩

theorem cov_eval_comb {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (x a b c : ℝ≥0) :
    cov[B x, B a + B b - (2 : ℝ) • B c; P] =
      ((min x a : ℝ≥0) : ℝ) + ((min x b : ℝ≥0) : ℝ) - 2 * ((min x c : ℝ≥0) : ℝ) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hm : ∀ t, MemLp (B t) 2 P := fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  rw [covariance_sub_right (hm x) ((hm a).add (hm b)) ((hm c).const_smul 2),
    covariance_add_right (hm x) (hm a) (hm b), covariance_smul_right, hB.covariance_eval,
    hB.covariance_eval, hB.covariance_eval]

theorem cov_revBM {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (τ : ℝ≥0) {s u : ℝ≥0}
    (hsu : s ≤ u) : cov[revBM B τ s, revBM B τ u; P] = s := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hm : ∀ t, MemLp (B t) 2 P := fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  unfold revBM
  have hR : MemLp (B (τ - u) + B (max u τ) - (2 : ℝ) • B τ) 2 P :=
    ((hm _).add (hm _)).sub ((hm _).const_smul _)
  rw [covariance_sub_left ((hm _).add (hm _)) ((hm _).const_smul _) hR,
    covariance_add_left (hm _) (hm _) hR, covariance_smul_left]
  rw [cov_eval_comb hB, cov_eval_comb hB, cov_eval_comb hB]
  have ha : τ - s ≤ τ := tsub_le_self
  have ha' : τ - u ≤ τ := tsub_le_self
  have hb : τ ≤ max s τ := le_max_right _ _
  have hb' : τ ≤ max u τ := le_max_right _ _
  rw [min_eq_left (ha.trans hb'), min_eq_left ha, min_eq_right (ha'.trans hb),
    min_eq_right hb, min_eq_right ha', min_eq_left hb', min_self,
    min_eq_right (tsub_le_tsub_left hsu τ), min_eq_left (max_le_max hsu le_rfl)]
  rcases le_total s τ with h | h
  · rw [max_eq_right h, NNReal.coe_sub h]
    ring
  · rw [max_eq_left h, tsub_eq_zero_of_le h]
    push_cast
    ring

theorem isBrownianReal_revBM {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (τ : ℝ≥0) : IsBrownianReal (revBM B τ) P where
  toIsPreBrownianReal := by
    refine (isGaussianProcess_revBM hB τ).isPreBrownianReal_of_covariance (fun s => ?_)
      (fun s u hsu => cov_revBM hB τ hsu)
    have hi : ∀ t, Integrable (B t) P := fun t => hB.integrable_eval t
    show ∫ ω, revBM B τ s ω ∂P = 0
    simp only [revBM_apply]
    rw [integral_sub (f := fun ω => B (τ - s) ω + B (max s τ) ω) (g := fun ω => 2 * B τ ω)
      ((hi _).add (hi _)) ((hi _).const_mul 2), integral_add (hi _) (hi _),
      integral_const_mul, hB.integral_eval, hB.integral_eval, hB.integral_eval]
    ring
  cont := ae_of_all _ fun ω => by
    simp only [revBM_apply]
    have h1 : Continuous fun s : ℝ≥0 => τ - s := continuous_const.sub continuous_id
    exact (((hc ω).comp h1).add ((hc ω).comp (continuous_id.max continuous_const))).sub
      continuous_const

end Brownian

/-! ## 6. Assembly -/

/-- On `[0,t]`, `√κ B'` (with `B' = revBM B t`) is the time-reversed driver of `√κ B`. -/
theorem revMap_timeRev_eq_drive_revBM {Ω : Type*} (κ : ℝ) (B₁ : ℝ≥0 → Ω → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ω : Ω) (z : ℂ) :
    revMap (fun s => drive κ B₁ ω (t - s) - drive κ B₁ ω t) t z =
      revMap (drive κ (revBM B₁ t.toNNReal) ω) t z := by
  refine ReverseFlow.revMap_congr_drive z fun s hs => ?_
  have hle : s.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal hs.2
  have h1 : (t - s).toNNReal = t.toNNReal - s.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hs.2), NNReal.coe_sub hle, Real.coe_toNNReal _ hs.1,
      Real.coe_toNNReal _ ht]
  have h2 : max s.toNNReal t.toNNReal = t.toNNReal := max_eq_right hle
  simp only [drive, revBM_apply, h1, h2]
  ring

/-- Weak Markov property with an independent field: a function of `(B|[0,τ], X)` is
independent of a function of the future increments `s ↦ B(τ+s) - B τ`. -/
theorem indepFun_of_past_future {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B₁ : ℝ≥0 → Ω → ℝ} (hB₁ : IsPreBrownianReal B₁ P)
    (hB₁m : ∀ s, Measurable (B₁ s)) {X : Ω → FieldSample} (hXm : Measurable X)
    (hind₁ : IndepFun (pathOf B₁) X P) (τ : ℝ≥0) {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {F : Ω → α} {G : Ω → β}
    (hF : Measurable[MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi ⊔
      MeasurableSpace.comap X MeasurableSpace.pi] F)
    (hG : Measurable[MeasurableSpace.comap (fun ω (s : ℝ≥0) => B₁ (τ + s) ω - B₁ τ ω)
      MeasurableSpace.pi] G) :
    IndepFun F G P := by
  have hPF := (IndepFun_iff_Indep _ _ _).1 (hB₁.indepFun_shift τ)
  have hXB := (IndepFun_iff_Indep _ _ _).1 hind₁.symm
  have hPle : MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi := by
    have h : @Measurable Ω _ (MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi) _
        (fun ω (u : Set.Iic τ) => B₁ u ω) := by
      letI : MeasurableSpace Ω := MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi
      exact measurable_pi_iff.2 fun u =>
        (measurable_pi_apply u.1).comp (comap_measurable (pathOf B₁))
    exact h.comap_le
  have hFle : MeasurableSpace.comap (fun ω (s : ℝ≥0) => B₁ (τ + s) ω - B₁ τ ω)
      MeasurableSpace.pi ≤ MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi := by
    have h : @Measurable Ω _ (MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi) _
        (fun ω (s : ℝ≥0) => B₁ (τ + s) ω - B₁ τ ω) := by
      letI : MeasurableSpace Ω := MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi
      exact measurable_pi_iff.2 fun s =>
        ((measurable_pi_apply (τ + s)).comp (comap_measurable (pathOf B₁))).sub
          ((measurable_pi_apply τ).comp (comap_measurable (pathOf B₁)))
    exact h.comap_le
  have hmB : MeasurableSpace.comap (pathOf B₁) MeasurableSpace.pi ≤ mΩ :=
    (measurable_pi_iff.2 hB₁m : Measurable (pathOf B₁)).comap_le
  have hjoin := indep_sup_of_indep hPle hFle hmB hXm.comap_le hPF.symm hXB
  exact (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_right (indep_of_indep_of_le_left hjoin hF.comap_le) hG.comap_le)

/-- **Blueprint B1 (conditional on Theorem 1.2).** Unzipping by capacity time `t > 0` preserves
the law `Γ⁰` of the configuration (field modulo constants, driver on `[0,∞)`), and the unzipped
field is independent of the future driver increments. -/
theorem unzip_invariance (h12 : theorem1_2) (κ : ℝ) (hκ : 0 < κ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {t : ℝ} (ht : 0 < t) :
    configLawMod0 (fun ω => zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
        configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P ∧
      IndepFun (fun ω (ρ : TestFun0 H) =>
          pairRaw (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ρ.1.1)
        (fun ω (s : ℝ≥0) => (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).2 s)
        P := by
  have ht0 := ht.le
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hB₁pm : Measurable fun ω (s : ℝ≥0) => B₁ s ω := measurable_pi_iff.2 fun s => hB₁m s
  -- the reversed Brownian motion `B'`
  have hB' : IsBrownianReal (revBM B₁ t.toNNReal) P := isBrownianReal_revBM hB₁ hB₁c _
  have hB'm : ∀ s, Measurable (revBM B₁ t.toNNReal s) := fun s =>
    ((hB₁m _).add (hB₁m _)).sub ((hB₁m _).const_smul _)
  have hB'c : ∀ ω, Continuous fun s => revBM B₁ t.toNNReal s ω := fun ω => by
    simp only [revBM_apply]
    exact (((hB₁c ω).comp (continuous_const.sub continuous_id)).add
      ((hB₁c ω).comp (continuous_id.max continuous_const))).sub continuous_const
  have hind' : IndepFun (pathOf (revBM B₁ t.toNNReal)) X P := by
    have hΦ : Measurable fun p : ℝ≥0 → ℝ =>
        fun s => p (t.toNNReal - s) + p (max s t.toNNReal) - 2 * p t.toNNReal := by
      fun_prop
    have := hind₁.comp hΦ measurable_id
    convert this using 1
    all_goals first
      | rfl
      | (funext ω s; simp [pathOf])
  set g := pathC t (revBM B₁ t.toNNReal) hB'c with hg_def
  have hgm : Measurable g := measurable_pathC t hB'm hB'c
  have hig : IndepFun g X P := indepFun_pathC t hind' hB'c
  -- pathwise identification of the unzipping map
  have hgood : ∀ᵐ ω ∂P, (∀ s, B₁ s ω = B s ω) ∧ B₁ 0 ω = 0 := by
    filter_upwards [hB₁eq, hB₁.eval_zero_ae_eq_zero] with ω h1 h2 using ⟨h1, h2⟩
  have hEq : ∀ ω, (∀ s, B₁ s ω = B s ω) → B₁ 0 ω = 0 →
      EqOn (fwdMapInv (drive κ B ω) t) (revMap (Wof κ t ht0 (g ω)) t) H := by
    intro ω h1 h0 w hw
    have hdr : drive κ B ω = drive κ B₁ ω := funext fun x => by simp [drive, h1]
    rw [hdr, fwdMapInv_eq_revMap_timeRev _ (drive_continuous (hB₁c ω)) (drive_zero h0) ht0 hw,
      revMap_timeRev_eq_drive_revBM κ B₁ ht0 ω w, revMap_drive_eq κ t ht0 _ hB'c ω]
  -- the components and their measurable versions
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : Ω → TestFun0 H → ℝ, F₁ = fun ω ρ =>
      pairRaw (coordChange (ofFun (h0rev κ) + X ω) (revMap (Wof κ t ht0 (g ω)) t)
        (Qc (Real.sqrt κ))) ρ.1.1 := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Ω → TestFun0 H → ℝ, R₁ = fun ω ρ =>
      pairRaw (Y2f κ t ht0 (g ω) (X ω)) ρ.1.1 := ⟨_, rfl⟩
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Ω → TestFun0 H → ℝ, F₀ = fun ω ρ =>
      pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 := ⟨_, rfl⟩
  obtain ⟨G₁, hG₁⟩ : ∃ G₁ : Ω → ℝ≥0 → ℝ, G₁ = fun ω s =>
      Real.sqrt κ * (B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω) := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Ω → ℝ≥0 → ℝ, G₀ = fun ω s => Real.sqrt κ * B₁ s ω := ⟨_, rfl⟩
  have hF₁m : Measurable F₁ := by
    rw [hF₁]
    refine measurable_pi_iff.2 fun ρ => ?_
    have key := (measurable_pair_unzip κ t ht0 ρ.1).comp (hgm.prodMk hXm)
    simp only [Function.comp_def] at key
    exact key
  have hR₁m : Measurable R₁ := by
    rw [hR₁]
    refine measurable_pi_iff.2 fun ρ => ?_
    have key := (measurable_pair_Y2f κ t ht0 ρ.1).comp (hgm.prodMk hXm)
    simp only [Function.comp_def] at key
    exact key
  have hF₀m : Measurable F₀ := by
    rw [hF₀]; exact measurable_pi_iff.2 fun ρ => measurable_pairRaw_lhs κ hX ρ
  have hφ : Measurable fun p : ℝ≥0 → ℝ => fun s => Real.sqrt κ * p s :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply s).const_mul _
  have hSm : Measurable fun ω (s : ℝ≥0) => B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω :=
    measurable_pi_iff.2 fun s => (hB₁m _).sub (hB₁m _)
  have hG₁m : Measurable G₁ := by rw [hG₁]; exact hφ.comp hSm
  have hG₀m : Measurable G₀ := by rw [hG₀]; exact hφ.comp hB₁pm
  -- a.e. identification of the configuration components
  have hFG : (fun ω => ((fun ρ : TestFun0 H =>
      pairRaw (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ρ.1.1),
        fun s : ℝ≥0 => (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).2 s))
      =ᵐ[P] fun ω => (F₁ ω, G₁ ω) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨h1, h0⟩ := hω
    rw [hF₁, hG₁]
    refine Prod.ext (funext fun ρ => ?_) (funext fun s => ?_)
    · show pairRaw (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t)
          (Qc (Real.sqrt κ))) ρ.1.1 = pairRaw (coordChange (ofFun (h0rev κ) + X ω)
            (revMap (Wof κ t ht0 (g ω)) t) (Qc (Real.sqrt κ))) ρ.1.1
      exact pairRaw_coordChange_congr (hEq ω h1 h0) _ _ ρ.1
    · show drive κ B ω (t + max (s : ℝ) 0) - drive κ B ω t =
        Real.sqrt κ * (B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω)
      have e1 : (t + max (s : ℝ) 0).toNNReal = t.toNNReal + s := by
        rw [max_eq_left s.coe_nonneg, Real.toNNReal_add ht0 s.coe_nonneg, Real.toNNReal_coe]
      simp only [drive]
      rw [e1, ← h1 (t.toNNReal + s), ← h1 t.toNNReal]
      ring
  have hFG0 : (fun ω => ((fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1),
        fun s : ℝ≥0 => drive κ B ω s)) =ᵐ[P] fun ω => (F₀ ω, G₀ ω) := by
    filter_upwards [hB₁eq] with ω h1
    rw [hF₀, hG₀]
    refine Prod.ext rfl (funext fun s => ?_)
    show Real.sqrt κ * B (s : ℝ).toNNReal ω = Real.sqrt κ * B₁ s ω
    rw [Real.toNNReal_coe, h1]
  -- (a) the field law, from Theorem 1.2 applied to `(B', X)`
  have hF : P.map F₁ = P.map F₀ := by
    calc P.map F₁ = P.map R₁ := map_eq_of_forall_ae_eq hF₁m hR₁m fun ρ => by
          rw [hF₁, hR₁]; exact ae_pairRaw_unzip_eq_Y2f κ ht0 hX hgm hig ρ.1
      _ = fieldLawMod0 H (fun ω => ofFun (hTrev κ (drive κ (revBM B₁ t.toNNReal) ω) t) +
            coordChange (X ω) (revMap (drive κ (revBM B₁ t.toNNReal) ω) t) 0) P := by
          unfold fieldLawMod0
          rw [hR₁]
          refine Measure.map_congr ?_
          filter_upwards [ae_rhs_eq_Y2f κ t ht0 hB'c (ae_of_all _ fun ω s => rfl) X] with ω h
          funext ρ
          rw [h]
      _ = fieldLawMod0 H (fun ω => ofFun (h0rev κ) + X ω) P :=
          (h12 κ t hκ ht P (revBM B₁ t.toNNReal) X hB' hX hind').symm
      _ = P.map F₀ := by rw [hF₀]; rfl
  -- (b) independence of the unzipped field and the future driver
  have hgP : Measurable[MeasurableSpace.comap (fun ω (u : Set.Iic t.toNNReal) => B₁ u ω)
      MeasurableSpace.pi] g := by
    letI : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω (u : Set.Iic t.toNNReal) => B₁ u ω) MeasurableSpace.pi
    have hpast : ∀ u : ℝ≥0, u ≤ t.toNNReal → Measurable (B₁ u) := fun u hu =>
      (measurable_pi_apply (⟨u, hu⟩ : Set.Iic t.toNNReal)).comp
        (comap_measurable (fun ω (u : Set.Iic t.toNNReal) => B₁ u ω))
    refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
    have hs : x.1.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal x.2.2
    show Measurable fun ω => revBM B₁ t.toNNReal x.1.toNNReal ω
    simp only [revBM_apply]
    exact ((hpast _ tsub_le_self).add (hpast _ (max_le hs le_rfl))).sub
      ((hpast _ le_rfl).const_mul 2)
  have hF₁P : Measurable[MeasurableSpace.comap (fun ω (u : Set.Iic t.toNNReal) => B₁ u ω)
      MeasurableSpace.pi ⊔ MeasurableSpace.comap X MeasurableSpace.pi] F₁ := by
    letI : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω (u : Set.Iic t.toNNReal) => B₁ u ω) MeasurableSpace.pi ⊔
        MeasurableSpace.comap X MeasurableSpace.pi
    have hpair : Measurable fun ω => (g ω, X ω) :=
      (hgP.mono le_sup_left le_rfl).prodMk ((comap_measurable X).mono le_sup_right le_rfl)
    rw [hF₁]
    refine measurable_pi_iff.2 fun ρ => ?_
    have key := (measurable_pair_unzip κ t ht0 ρ.1).comp hpair
    simp only [Function.comp_def] at key
    exact key
  have hG₁F : Measurable[MeasurableSpace.comap
      (fun ω (s : ℝ≥0) => B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω) MeasurableSpace.pi] G₁ := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (s : ℝ≥0) => B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω) MeasurableSpace.pi
    rw [hG₁]
    exact measurable_pi_iff.2 fun s =>
      ((measurable_pi_apply s).comp (comap_measurable
        (fun ω (s : ℝ≥0) => B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω))).const_mul _
  have hindFG : IndepFun F₁ G₁ P :=
    indepFun_of_past_future hB₁ hB₁m hXm hind₁ t.toNNReal hF₁P hG₁F
  -- (c) the driver law, from the weak Markov property
  have hG : P.map G₁ = P.map G₀ := by
    have hmapS := GermZeroOne.map_path_eq_of_isPreBrownianReal (hB₁.shift t.toNNReal) hB₁
      (fun s => (hB₁m _).sub (hB₁m _)) hB₁m
    beta_reduce at hmapS
    calc P.map G₁ = (P.map fun ω (s : ℝ≥0) => B₁ (t.toNNReal + s) ω - B₁ t.toNNReal ω).map
          (fun p : ℝ≥0 → ℝ => fun s => Real.sqrt κ * p s) := by
          rw [Measure.map_map hφ hSm, hG₁]; rfl
      _ = (P.map fun ω (s : ℝ≥0) => B₁ s ω).map
          (fun p : ℝ≥0 → ℝ => fun s => Real.sqrt κ * p s) := by rw [hmapS]
      _ = P.map G₀ := by rw [Measure.map_map hφ hB₁pm, hG₀]; rfl
  -- independence in the original configuration
  have hind0 : IndepFun F₀ G₀ P := by
    have hΦ0 : Measurable fun x : FieldSample => fun ρ : TestFun0 H =>
        pairRaw (ofFun (h0rev κ) + x) ρ.1.1 := by
      refine measurable_pi_iff.2 fun ρ => ?_
      have key := ((measurable_pi_apply (tdens ρ.1.1)).sub
        (measurable_pi_apply (tdens fun z => -ρ.1.1 z))).comp
        (measurable_add_left (ofFun (h0rev κ)))
      simp only [Function.comp_def] at key
      exact key
    have key := hind₁.symm.comp hΦ0 hφ
    rw [hF₀, hG₀]
    exact key
  refine ⟨?_, hindFG.congr (hFG.mono fun ω h => (congrArg Prod.fst h).symm)
    (hFG.mono fun ω h => (congrArg Prod.snd h).symm)⟩
  calc configLawMod0
        (fun ω => zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P
      = P.map (fun ω => (F₁ ω, G₁ ω)) := Measure.map_congr hFG
    _ = (P.map F₁).prod (P.map G₁) :=
        (indepFun_iff_map_prod_eq_prod_map_map hF₁m.aemeasurable hG₁m.aemeasurable).1 hindFG
    _ = (P.map F₀).prod (P.map G₀) := by rw [hF, hG]
    _ = P.map (fun ω => (F₀ ω, G₀ ω)) :=
        ((indepFun_iff_map_prod_eq_prod_map_map hF₀m.aemeasurable hG₀m.aemeasurable).1 hind0).symm
    _ = configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P :=
        (Measure.map_congr hFG0).symm

/-- **Corollary 1.5(a) for negative times, conditional on Theorem 1.2**, in the exact shape of
`theorem1_5`: for `t < 0`, `Z^CAP_t = zipCapDown γ (-t)` preserves the law of the configuration. -/
theorem theorem1_5a_neg (h12 : theorem1_2) :
    ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      let γ := Real.sqrt κ
      let c : Ω → FieldSample × (ℝ → ℝ) := fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)
      ∀ t : ℝ, t < 0 → configLawMod0 (fun ω => zipCap γ t (c ω)) P = configLawMod0 c P := by
  intro κ hκ _ Ω _ P _ B X hB hX hind γ c t ht
  rw [zipCap_of_neg ht]
  exact (unzip_invariance h12 κ hκ P B X hB hX hind (neg_pos.2 ht)).1

/-! ## 7. Unconditional versions (Theorem 1.2 is proved in `Proofs/Thm12/Main.lean`) -/

/-- **Corollary 1.5(a) for negative times, unconditional.** -/
theorem theorem1_5a_neg_holds :
    ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      let γ := Real.sqrt κ
      let c : Ω → FieldSample × (ℝ → ℝ) := fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)
      ∀ t : ℝ, t < 0 → configLawMod0 (fun ω => zipCap γ t (c ω)) P = configLawMod0 c P :=
  theorem1_5a_neg theorem1_2_holds

end UnzipInvariance
end QuantumZipper
