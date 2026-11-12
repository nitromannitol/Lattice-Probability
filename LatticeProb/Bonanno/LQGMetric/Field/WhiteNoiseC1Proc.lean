/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseC1Proc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1L2
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont

/-!
# The difference-quotient process of `φ_{a,b}` and its continuous version (task P2-DDDFFIELD)

`dphi W a b e x h = √π W(q_{x,h})` (with `q_{x,h}` from `WhiteNoiseC1L2`) satisfies

* `phi_add_smul_sub_ae`: `φ_{a,b}(x + h e) − φ_{a,b}(x) = h · dphi(x, h)` a.s. (for each `x, h`);
* `hasLaw_dphi_sub`: Gaussian increments with variance `π ‖q_{x,h} − q_{x',h'}‖²`, which is
  `≤ C_ρ (‖x − x'‖ + |h − h'|)²` (`norm_dqKernelL2_sub_le`);
* `exists_continuous_modification_dphi`: a modification jointly continuous in `(x, h) ∈ ℂ × ℝ`
  (Kolmogorov–Čentsov in three parameters, QZ `KolmN.exists_continuous_modification_N`,
  Revuz–Yor Ch. I Thm (2.1), with Gaussian fourth moments, exponent `4 > 3`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Measurable continuous modification** from the Kolmogorov–Čentsov moment condition on
`Fin d → ℝ` (QZ `KolmN.exists_continuous_modification_N`; the measurable-version step as in
`exists_continuous_modification_phi`). -/
theorem exists_meas_continuous_modification_N {d : ℕ} {Z : (Fin d → ℝ) → Ω → ℝ}
    (hZ : ∀ q, Measurable (Z q)) {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : (d : ℝ) < a)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG Z P p a K R) :
    ∃ Y : (Fin d → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧ (∀ q, Measurable (Y q)) ∧
      ∀ q, (fun ω => Y q ω) =ᵐ[P] Z q := by
  obtain ⟨Y₀, hYc₀, hYm₀, hYt⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (P := P) (Z := Z) (fun q => (hZ q).aemeasurable) hp ha hmom
  set B : Set Ω := {ω | ¬ ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
    (nhds (Y₀ q ω))} with hB
  set G : Set Ω := (toMeasurable P B)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [hG, mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.mp hYt
  have hGt : ∀ ω ∈ G, ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
      (nhds (Y₀ q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  refine ⟨fun q ω => G.indicator (fun ω => Y₀ q ω) ω, fun ω => ?_, fun q => ?_, fun q => ?_⟩
  · by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]; exact hYc₀ ω
    · simp only [indicator_of_notMem hω]; exact continuous_const
  · refine measurable_of_tendsto_metrizable
      (f := fun n => G.indicator (Z (QuantumZipper.KolmD.rndD n q)))
      (fun n => (hZ _).indicator hGm) (tendsto_pi_nhds.mpr fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]; exact hGt ω hω q
    · simp only [indicator_of_notMem hω]; exact tendsto_const_nhds
  · filter_upwards [hGae, hYm₀ q] with ω h1 h2
    simp only [indicator_of_mem h1]
    exact h2

/-- The difference-quotient field `D_e(x, h) = √π W(q_{x,h})`
(`= (φ(x + h e) − φ(x))/h` for `h ≠ 0`, `= ∂_e φ(x)` for `h = 0`). -/
def dphi (W : WNSpace → Ω → ℝ) (a b : ℝ) (e x : ℂ) (h : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (dqKernelL2 a b e x h) ω

lemma measurable_dphi (hW : IsWhiteNoise P W) (a b : ℝ) (e x : ℂ) (h : ℝ) :
    Measurable (dphi W a b e x h) := (hW.measurable _).const_mul _

/-- `φ_{a,b}(x + h e) − φ_{a,b}(x) = h D_e(x, h)` a.s. -/
theorem phi_add_smul_sub_ae (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {e : ℂ} (he : ‖e‖ ≤ 1) (x : ℂ) (h : ℝ) :
    (fun ω => phi W a b (x + h • e) ω - phi W a b x ω) =ᵐ[P]
      fun ω => h * dphi W a b e x h ω := by
  have h1 := hW.add_ae (phiKernelL2 a b (x + h • e) - phiKernelL2 a b x) (phiKernelL2 a b x)
  rw [sub_add_cancel, phiKernelL2_add_smul_sub ha hab he] at h1
  have h2 := hW.smul_ae h (dqKernelL2 a b e x h)
  filter_upwards [h1, h2] with ω e1 e2
  simp only [phi, dphi]
  rw [e1, e2]
  ring

/-- Gaussian increments of `D_e`. -/
theorem hasLaw_dphi_sub (hW : IsWhiteNoise P W) (a b : ℝ) (e x x' : ℂ) (h h' : ℝ) :
    HasLaw (fun ω => dphi W a b e x h ω - dphi W a b e x' h' ω)
      (gaussianReal 0 (Real.pi * ‖dqKernelL2 a b e x h - dqKernelL2 a b e x' h'‖ ^ 2).toNNReal)
      P := by
  have hl := hW.hasLaw ![dqKernelL2 a b e x h, dqKernelL2 a b e x' h']
    ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hl
  rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt Real.pi_pos.le] at hl
  refine hl.congr (Eventually.of_forall fun ω => ?_)
  simp only [dphi]; ring

/-- `q ↦ q 0 + q 1 i` on `Fin 3 → ℝ`. -/
def toC3 (q : Fin 3 → ℝ) : ℂ := ⟨q 0, q 1⟩

lemma norm_toC3_sub_le (q q' : Fin 3 → ℝ) : ‖toC3 q - toC3 q'‖ ≤ 2 * ‖q - q'‖ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h0 : |(toC3 q - toC3 q').re| ≤ ‖q - q'‖ := by
    simpa [toC3, Real.norm_eq_abs] using norm_le_pi_norm (q - q') 0
  have h1 : |(toC3 q - toC3 q').im| ≤ ‖q - q'‖ := by
    simpa [toC3, Real.norm_eq_abs] using norm_le_pi_norm (q - q') 1
  linarith

/-- **Continuous version of the difference-quotient field**: for `0 < a ≤ b`, `‖e‖ ≤ 1`,
there is a modification of `(x, h) ↦ D_e(x, h)` that is jointly continuous for every `ω`. -/
theorem exists_continuous_modification_dphi (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {e : ℂ} (he : ‖e‖ ≤ 1) :
    ∃ D : ℂ → ℝ → Ω → ℝ, (∀ ω, Continuous fun p : ℂ × ℝ => D p.1 p.2 ω) ∧
      (∀ x h, Measurable (D x h)) ∧ ∀ x h, (fun ω => D x h ω) =ᵐ[P] dphi W a b e x h := by
  set Z : (Fin 3 → ℝ) → Ω → ℝ := fun q => dphi W a b e (toC3 q) (q 2) with hZ
  have hbox : ∀ (R : ℕ) (q : Fin 3 → ℝ), q ∈ QuantumZipper.KolmD.boxD (d := 3) R →
      ‖toC3 q‖ + |q 2| ≤ 3 * R := by
    intro R q hq
    have := Complex.norm_le_abs_re_add_abs_im (toC3 q)
    rw [show (toC3 q).re = q 0 from rfl, show (toC3 q).im = q 1 from rfl] at this
    have h0 := hq 0; have h1 := hq 1; have h2 := hq 2
    linarith
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG Z P 4 4 K R := by
    intro R
    set C : ℝ := Real.pi * (3 * ‖domL2 a b (3 * R)‖) ^ 2 with hC
    have hC0 : 0 ≤ C := by rw [hC]; have := Real.pi_pos; positivity
    refine ⟨C ^ 2 * QuantumZipper.gaussianAbsMoment 4, by
      have := QuantumZipper.gaussianAbsMoment_nonneg 4; positivity, fun q hq q' hq' => ?_⟩
    have hlaw := hasLaw_dphi_sub hW (P := P) a b e (toC3 q) (toC3 q') (q 2) (q' 2)
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((measurable_dphi hW a b e _ _).sub (measurable_dphi hW a b e _ _)) 2 hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [hZ]
    rw [show (4 : ℕ) = 2 * 2 from rfl, hE]
    refine ENNReal.ofReal_le_ofReal ?_
    set v := Real.pi * ‖dqKernelL2 a b e (toC3 q) (q 2) - dqKernelL2 a b e (toC3 q') (q' 2)‖ ^ 2
    have hn := norm_dqKernelL2_sub_le ha hab he (hbox R q hq) (hbox R q' hq')
    have hd : ‖toC3 q - toC3 q'‖ + |q 2 - q' 2| ≤ 3 * ‖q - q'‖ := by
      have := norm_toC3_sub_le q q'
      have h2 : |q 2 - q' 2| ≤ ‖q - q'‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 2
      linarith
    have hv : v ≤ C * ‖q - q'‖ ^ 2 := by
      have h0 : 0 ≤ ‖domL2 a b (3 * R)‖ := norm_nonneg _
      have h1 : ‖dqKernelL2 a b e (toC3 q) (q 2) - dqKernelL2 a b e (toC3 q') (q' 2)‖ ≤
          3 * ‖q - q'‖ * ‖domL2 a b (3 * R)‖ :=
        hn.trans (mul_le_mul_of_nonneg_right hd h0)
      have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc v ≤ Real.pi * (3 * ‖q - q'‖ * ‖domL2 a b (3 * R)‖) ^ 2 :=
            mul_le_mul_of_nonneg_left h1' Real.pi_pos.le
        _ = C * ‖q - q'‖ ^ 2 := by rw [hC]; ring
    have hM := QuantumZipper.gaussianAbsMoment_nonneg 4
    have hv' : ((v.toNNReal : NNReal) : ℝ) ≤ C * ‖q - q'‖ ^ 2 := by
      rw [Real.coe_toNNReal']
      exact max_le hv (by positivity)
    have hv0 : 0 ≤ ((v.toNNReal : NNReal) : ℝ) := NNReal.coe_nonneg _
    calc ((v.toNNReal : NNReal) : ℝ) ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2)
        ≤ (C * ‖q - q'‖ ^ 2) ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2) := by gcongr
      _ = C ^ 2 * QuantumZipper.gaussianAbsMoment 4 * ‖q - q'‖ ^ (4 : ℝ) := by
          rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  obtain ⟨Y, hYc, hYm, hYZ⟩ := exists_meas_continuous_modification_N (P := P) (Z := Z)
    (fun q => measurable_dphi hW a b e _ _) (p := 4) (by norm_num) (a := 4) (by norm_num) hmom
  let from3 : ℂ × ℝ → Fin 3 → ℝ := fun p => ![p.1.re, p.1.im, p.2]
  have hfc : Continuous from3 := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re.comp continuous_fst
    · exact Complex.continuous_im.comp continuous_fst
    · exact continuous_snd
  have hft : ∀ p : ℂ × ℝ, toC3 (from3 p) = p.1 ∧ from3 p 2 = p.2 := fun p =>
    ⟨by apply Complex.ext <;> simp [toC3, from3], by simp [from3]⟩
  refine ⟨fun x h ω => Y (from3 (x, h)) ω, fun ω => (hYc ω).comp hfc, fun x h => hYm _,
    fun x h => ?_⟩
  have := hYZ (from3 (x, h))
  simp only [hZ, (hft (x, h)).1, (hft (x, h)).2] at this
  exact this

end WhiteNoise
end LQGMetric
