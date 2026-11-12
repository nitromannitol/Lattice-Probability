/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4B at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C3

/-!
# Whole-plane LQG area, part 2: the white-noise whole-plane GFF on a window

For the whole-plane GFF `h₀` built from a white noise `W` (LM `DG.exists_wn_wholePlaneGFF`), a.s.
the approximations `areaApproxC γ h₀` have a vague limit on the window `U₀ = B(c₀, 1/20)`,
`c₀ = (1 + i)/2`, and are eventually finite on its compacts (`ae_areaGood_wn`).

Source: Duplantier–Sheffield arXiv:0808.1560 Prop. 1.1 for a GFF plus a continuous function,
in the form of Ding–Gwynne arXiv:1807.01072 (`dμ_{h+f} = e^{γf} dμ_h`) with the coupling of
DG Lemma 3.1 (DG:966–976): on the box `[2/5, 3/5]²`, `h^𝕍 − h₀` has a continuous modification
(LM `DGCircMod.sub` of `dg_lemma31_hU_hat_circ'` and `dgCircMod_h0_hat`), so LM
`DG.ae_isVagueLimitOn_muOfMod_loc` applies with `G = h₀`. The finiteness half copies the
density comparison of the proof of `ae_isVagueLimitOn_muOfMod_loc` (S3L11Loc1.lean): on `dSet`,
`h₀_{2^{-k}} = (h^𝕍)_{2^{-k}} − Y_{2^{-k}}` with `Y` bounded on the box, and the `h^𝕍`
approximations are finite on compacts (`ae_areaApprox_wnField_lt_top`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric LQGMetric.DG LQGMetric.WhiteNoise LQGMetric.GFFExist LQGMetric.SupTail

/-- the centre of the reference window -/
def c₀ : ℂ := ⟨1 / 2, 1 / 2⟩

/-- the reference window `B(c₀, 1/20)` -/
def U₀ : Set ℂ := ball c₀ (1 / 20)

/-- the DG box `[2/5, 3/5]²` around the window -/
abbrev box₀ : Set ℂ := ferniqueBox ⟨2 / 5, 2 / 5⟩ (1 / 5)

lemma abs_re_im_le_of_mem_ball {z w : ℂ} {r : ℝ} (h : w ∈ ball z r) :
    |w.re - z.re| < r ∧ |w.im - z.im| < r := by
  rw [mem_ball, dist_eq_norm] at h
  exact ⟨(Complex.abs_re_le_norm (w - z)).trans_lt h, (Complex.abs_im_le_norm (w - z)).trans_lt h⟩

lemma U₀_subset_box₀ : U₀ ⊆ box₀ := by
  intro w hw
  obtain ⟨h1, h2⟩ := abs_re_im_le_of_mem_ball hw
  simp only [c₀] at h1 h2
  rw [abs_lt] at h1 h2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma ball_subset_openSquare_of_mem_box₀ : ∀ z ∈ box₀, ball z (1 / 10) ⊆ openSquare := by
  rintro z ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ w hw
  obtain ⟨h1, h2⟩ := abs_re_im_le_of_mem_ball hw
  rw [abs_lt] at h1 h2
  norm_num at a1 a2 b1 b2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma box₀_subset_openSquare : box₀ ⊆ openSquare := fun z hz =>
  ball_subset_openSquare_of_mem_box₀ z hz (mem_ball_self (by norm_num))

lemma isCompact_box₀ : IsCompact box₀ := isCompact_Icc.reProdIm isCompact_Icc

lemma isOpen_U₀ : IsOpen U₀ := isOpen_ball

lemma isBounded_U₀ : Bornology.IsBounded U₀ := isBounded_ball

lemma U₀_subset_H : U₀ ⊆ H := U₀_subset_box₀.trans (box₀_subset_openSquare.trans openSquare_subset_H)

lemma compl_U₀_nonempty : U₀ᶜ.Nonempty :=
  ⟨0, fun h => by have := box₀_subset_openSquare (U₀_subset_box₀ h); simp [openSquare] at this⟩

/-- restricting the approximations to the open set does not change vague limits on it -/
theorem isVagueLimitOn_of_restrict {U : Set ℂ} (hU : IsOpen U) {μs : ℕ → Measure ℂ}
    {μ : Measure ℂ} (h : IsVagueLimitOn U (fun k => (μs k).restrict U) μ) :
    IsVagueLimitOn U μs μ := by
  refine ⟨h.1, h.2.1, fun f hf hfc hfU => ?_⟩
  have e : ∀ k, ∫ z, f z ∂((μs k).restrict U) = ∫ z, f z ∂(μs k) := fun k =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      image_eq_zero_of_notMem_tsupport fun h' => hz (hfU h')
  simpa only [e] using h.2.2 f hf hfc hfU

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {h₀ : Ω → Field}

/-- `h^𝕍 − h₀` has a continuous modification on the box (DG Lemma 3.1, LM) -/
theorem exists_isDGMod_h0 (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) :
    ∃ Y : ℂ → Ω → ℝ,
      IsDGMod P box₀ (fun z r ω => dgHU W z r ω - circleAvg (h₀ ω) r z) Y := by
  have hm := (DGCircMod.sub (dg_lemma31_hU_hat_circ' hW (y := ⟨2 / 5, 2 / 5⟩) (by norm_num : (0 : ℝ) < 1 / 5)
    ball_subset_openSquare_of_mem_box₀)
    (dgCircMod_h0_hat hW hh hae (y := ⟨2 / 5, 2 / 5⟩) (by norm_num : (0 : ℝ) < 1 / 5))).congr
    (G := fun z r ω => dgHU W z r ω - circleAvg (h₀ ω) r z)
    (fun z r ω => by simp only [dgHU, dgHat]; ring)
  obtain ⟨Y, hY⟩ := hm
  exact ⟨Y, hY⟩

/-- jointly measurable circle averages at dyadic radii -/
lemma measurable_circleAvg_h0 (hh : IsWholePlaneGFF h₀ P) (k : ℕ) :
    Measurable fun p : ℂ × Ω => circleAvg (h₀ p.2) (radius k) p.1 :=
  measurable_circleAvg.comp (f := fun p : ℂ × Ω => (h₀ p.2, radius k, p.1))
    ((hh.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_fst))

/-- a.e. bound of a circle average of a function bounded on a set containing the circle -/
lemma abs_integral_circleUnif_le {Y : ℂ → ℝ} {S : Set ℂ} {M : ℝ} (hM : ∀ z ∈ S, ‖Y z‖ ≤ M)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ S) :
    ‖∫ x, Y x ∂(circleUnif z r)‖ ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := circleUnif z r) (f := Y) (C := M)
    (ae_iff.2 (measure_mono_null (fun x hx => fun hxB => hx (hM x (hB hxB)))
      (circleUnif_compl_closedBall hr z)))
  simpa using h

/-- **the white-noise whole-plane GFF on the window `U₀`** (DS Prop. 1.1 via the Ding–Gwynne density change and DG
Lemma 3.1): a.s. a vague limit on `U₀` and eventual finiteness on its compacts -/
theorem ae_areaGood_wn (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : ∀ᵐ ω ∂P, AreaGood U₀ (areaApproxC γ (h₀ ω)) := by
  obtain ⟨Y, hY⟩ := exists_isDGMod_h0 hW hh hae
  have hV : ∀ k z, z ∈ dSet U₀ k → (fun ω => circleAvg (h₀ ω) (radius k) z) =ᵐ[P]
      (fun z r ω => circleAvg (h₀ ω) r z) z ((2 : ℝ)⁻¹ ^ k) :=
    fun _ _ _ => ae_of_all _ fun _ => rfl
  have hvag := ae_isVagueLimitOn_muOfMod_loc hW hγ hγ2 isCompact_box₀ box₀_subset_openSquare
    isOpen_U₀ U₀_subset_box₀ hY (V := fun k z ω => circleAvg (h₀ ω) (radius k) z)
    (measurable_circleAvg_h0 hh) hV
  filter_upwards [hvag, ae_areaApprox_wnField_lt_top hW γ, ae_all_iff.2 (ae_ae_locCirc_eq hW
    U₀_subset_box₀ box₀_subset_openSquare hY (V := fun k z ω => circleAvg (h₀ ω) (radius k) z)
    (measurable_circleAvg_h0 hh) hV)] with ω hv hfin hdens
  refine ⟨⟨(muOfMod W γ box₀ Y ω).restrict U₀, isVagueLimitOn_of_restrict isOpen_U₀ ?_⟩, ?_⟩
  · convert hv using 2 with k
    unfold areaApproxC
    rw [restrict_withDensity isOpen_U₀.measurableSet]
    rfl
  intro K hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact Eventually.of_forall fun k => by simp
  obtain ⟨n, hn, -⟩ := exists_cutSet isOpen_U₀ compl_U₀_nonempty hK hKU
  obtain ⟨M, hM⟩ := isCompact_box₀.exists_bound_of_continuousOn (hY.1 ω).continuousOn
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hn hz₀
      simp only [cutSet, h0, Nat.cast_zero, zero_mul, mem_setOf_eq] at this
      linarith
    · exact_mod_cast h0
  filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((1 : ℕ) + 2 : ℝ) / 2 by
    norm_num)), hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / n / 2 by positivity))]
    with k hk1 hk2
  have hKd : K ⊆ dSet U₀ k := fun z hz => by
    have h1 : 1 ≤ (n : ℝ) * infDist z U₀ᶜ := hn hz
    show 2 * radius k < infDist z U₀ᶜ
    have : 1 / (n : ℝ) ≤ infDist z U₀ᶜ := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hKsq : K ⊆ sqIn (1 / ((1 : ℕ) + 2 : ℝ)) := fun z hz => by
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := U₀_subset_box₀ (hKU hz)
    norm_num at a1 a2 b1 b2 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hKH : K ⊆ H := hKU.trans U₀_subset_H
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hbd : ∀ᵐ z ∂(volume.restrict K),
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg (h₀ ω) (radius k) z)) ≤
        ENNReal.ofReal (Real.exp (γ * M)) * ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
          Real.exp (γ * avgReg (GMCIdent3.wnField W ω) k z)) := by
    filter_upwards [ae_restrict_of_ae (hdens k), ae_restrict_mem hKm] with z hz hzK
    rcases hz with hz | hz
    · exact absurd (hKd hzK) hz
    rw [hz, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hzd := closedBall_subset_of_mem_dSet (hKd hzK)
    have hB : closedBall z (radius k) ⊆ box₀ :=
      (closedBall_subset_closedBall (by linarith [QuantumZipper.radius_pos k])).trans
        (hzd.trans U₀_subset_box₀)
    have hI := abs_integral_circleUnif_le (Y := fun x => Y x ω) hM (QuantumZipper.radius_pos k) hB
    rw [Real.norm_eq_abs, abs_le] at hI
    have he : Real.exp (γ * (avgReg (GMCIdent3.wnField W ω) k z - ∫ x, Y x ω ∂circleUnif z (radius k))) ≤
        Real.exp (γ * M) * Real.exp (γ * avgReg (GMCIdent3.wnField W ω) k z) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [hI.1])
    have hr0 : 0 ≤ radius k ^ (γ ^ 2 / 2) := by have := QuantumZipper.radius_pos k; positivity
    nlinarith [mul_le_mul_of_nonneg_left he hr0]
  have hwn : areaApprox γ (GMCIdent3.wnField W ω) k K < ⊤ :=
    (measure_mono hKsq).trans_lt (hfin 1 k hk1)
  unfold areaApproxC
  rw [withDensity_apply _ hKm]
  refine (lintegral_mono_ae hbd).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  unfold areaApprox at hwn
  rwa [withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_eq_left.2 hKH] at hwn

end ConeArea4
end MatedCRTHarmonic.MoTPort
