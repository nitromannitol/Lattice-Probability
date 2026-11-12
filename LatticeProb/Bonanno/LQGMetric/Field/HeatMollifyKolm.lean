/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatMollifyKolm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyLip
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G1FMKolm5

/-!
# Uniform-in-`z` bounds for the GFF truncation differences (P2-FHEAT, part 2b)

For the mean-zero parts `G_n(z) = ⟨h, meanZeroPart (heatDiff s z n)⟩` we feed the quantitative
dyadic Kolmogorov bound `QuantumZipper.Thm18Asm.G1FM.kolm_sup_tail_N` (QZ/Proofs/Thm18/
G1FMKolm5.lean; index `Fin 2 → ℝ ≅ ℂ`, `p = a = 4`, `θ = 3/4`) with Gaussian fourth moments
(`IsWholePlaneGFF.lintegral_pow_four`) and the Lipschitz/variance bounds of
`HeatMollifyLip.lean`, and conclude with Borel–Cantelli (mathlib `ae_eventually_notMem`):
a.s., for every `R`, eventually `sup_{|z| ≤ R} |G_n(z)| ≤ 9 e^{-n/2}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric

/-! ### `Fin 2 → ℝ` as `ℂ` -/

/-- `q ↦ q 0 + i q 1` -/
def cplxOf (q : Fin 2 → ℝ) : ℂ := ⟨q 0, q 1⟩

lemma continuous_cplxOf : Continuous cplxOf := by
  have : cplxOf = fun q => Complex.equivRealProdCLM.symm (q 0, q 1) := by
    funext q; apply Complex.ext <;> simp [cplxOf]
  rw [this]; fun_prop

lemma norm_cplxOf_le (q : Fin 2 → ℝ) : ‖cplxOf q‖ ≤ 2 * ‖q‖ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h0 := norm_le_pi_norm q 0
  have h1 := norm_le_pi_norm q 1
  simp only [Real.norm_eq_abs] at h0 h1
  simp only [cplxOf]
  linarith

lemma cplxOf_sub (q q' : Fin 2 → ℝ) : cplxOf q - cplxOf q' = cplxOf (q - q') := by
  apply Complex.ext <;> simp [cplxOf]

lemma norm_le_of_mem_boxD {R : ℕ} {q : Fin 2 → ℝ} (hq : q ∈ QuantumZipper.KolmD.boxD R) :
    ‖q‖ ≤ R :=
  (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg R)).2 fun i => by
    simpa [Real.norm_eq_abs] using hq i

lemma exists_mem_boxD {R : ℕ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∃ q ∈ QuantumZipper.KolmD.boxD (d := 2) R, cplxOf q = z := by
  refine ⟨![z.re, z.im], fun i => ?_, by apply Complex.ext <;> simp [cplxOf]⟩
  fin_cases i
  · exact (Complex.abs_re_le_norm z).trans hz
  · exact (Complex.abs_im_le_norm z).trans hz

/-! ### Linearity of the mean-zero part -/

lemma meanZeroPart_sub (a b : TestC) :
    (meanZeroPart (a - b)).1 = (meanZeroPart a).1 - (meanZeroPart b).1 := by
  have ha : Integrable (a : ℂ → ℝ) := a.continuous.integrable_of_hasCompactSupport
    a.hasCompactSupport
  have hb : Integrable (b : ℂ → ℝ) := b.continuous.integrable_of_hasCompactSupport
    b.hasCompactSupport
  ext w
  show (meanZeroPart (a - b)).1 w = (meanZeroPart a).1 w - (meanZeroPart b).1 w
  simp only [meanZeroPart_apply]
  have : ∫ x, (a - b) x = (∫ x, a x) - ∫ x, b x := integral_sub ha hb
  rw [this]
  show a w - b w - _ = (a w - (∫ x, a x) * refTest w) - (b w - (∫ x, b x) * refTest w)
  ring

/-! ### The process -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `G_n(q) = ⟨h, meanZeroPart D_n(q)⟩` -/
def gaussDiffProc (h : Ω → DistC) (s : ℝ) (n : ℕ) (q : Fin 2 → ℝ) (ω : Ω) : ℝ :=
  h ω (meanZeroPart (heatDiff s (cplxOf q) n)).1

lemma continuous_gaussDiffProc (s : ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun q => gaussDiffProc h s n q ω := by
  have hT : ∀ m, Continuous fun z => h ω (heatTrunc s z m) := fun m =>
    (h ω).continuous.comp (continuous_heatTrunc s m)
  have hI : ∀ m, Continuous fun z => ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatTrunc s z m) :=
    fun m => (ofCont _).continuous.comp (continuous_heatTrunc s m)
  have key : ∀ z, h ω (meanZeroPart (heatDiff s z n)).1 =
      (h ω (heatTrunc s z (n + 1)) - h ω (heatTrunc s z n)) -
        (ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatTrunc s z (n + 1)) -
          ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatTrunc s z n)) * h ω refTest := by
    intro z
    have e := pair_eq_meanZeroPart (h ω) (heatDiff s z n)
    have e2 : ∫ x, heatDiff s z n x =
        ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatDiff s z n) := by
      rw [ofCont_apply_heat]; simp
    rw [e2] at e
    simp only [heatDiff, map_sub] at e ⊢
    linarith
  simp only [gaussDiffProc]
  simp_rw [key]
  exact (((hT _).sub (hT _)).sub (((hI _).sub (hI _)).mul continuous_const)).comp
    continuous_cplxOf

lemma measurable_gaussDiffProc (hh : IsWholePlaneGFF h P) (s : ℝ) (n : ℕ) (q : Fin 2 → ℝ) :
    Measurable (gaussDiffProc h s n q) :=
  (measurable_distOn_apply _).comp hh.measurable

lemma gaussDiffProc_sub (s : ℝ) (n : ℕ) (q q' : Fin 2 → ℝ) (ω : Ω) :
    gaussDiffProc h s n q ω - gaussDiffProc h s n q' ω =
      h ω (meanZeroPart (heatDiff s (cplxOf q) n - heatDiff s (cplxOf q') n)).1 := by
  simp only [gaussDiffProc, meanZeroPart_sub, map_sub]

/-- fourth moment bound from a sup bound and support -/
lemma IsWholePlaneGFF.lintegral_pow_four_le (hh : IsWholePlaneGFF h P) (ψ : TestC) {B t : ℝ}
    (hB : 0 ≤ B) (ht : 1 ≤ t) (hψ : ∀ w, |ψ w| ≤ B) (hs : ∀ w, t < ‖w‖ → ψ w = 0) :
    ∫⁻ ω, ENNReal.ofReal (|h ω (meanZeroPart ψ).1| ^ 4) ∂P ≤
      ENNReal.ofReal (QuantumZipper.gaussianAbsMoment 4 * mzConst ^ 2 * B ^ 4 * t ^ 18) := by
  rw [hh.lintegral_pow_four]
  apply ENNReal.ofReal_le_ofReal
  have hv := abs_logCov_meanZeroPart_le ψ hB ht hψ hs
  have hg := QuantumZipper.gaussianAbsMoment_nonneg 4
  have hsq : (logCov (meanZeroPart ψ).1 (meanZeroPart ψ).1) ^ 2 ≤ (mzConst * B ^ 2 * t ^ 9) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  calc (logCov (meanZeroPart ψ).1 (meanZeroPart ψ).1) ^ 2 * QuantumZipper.gaussianAbsMoment 4
      ≤ (mzConst * B ^ 2 * t ^ 9) ^ 2 * QuantumZipper.gaussianAbsMoment 4 :=
        mul_le_mul_of_nonneg_right hsq hg
    _ = _ := by ring

/-- **Uniform bound** on the mean-zero truncation differences: a.s., for every `R`,
eventually in `n`, `|G_n(q)| ≤ 9 e^{-n/2}` on the box `[-R,R]²`. -/
theorem IsWholePlaneGFF.ae_eventually_gaussDiffProc_le (hh : IsWholePlaneGFF h P) (s : ℝ)
    (hs : 0 < s) : ∀ᵐ ω ∂P, ∀ R : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ QuantumZipper.KolmD.boxD (d := 2) R,
        |gaussDiffProc h s n q ω| ≤ 9 * Real.exp (-(n : ℝ) / 2) := by
  rw [ae_all_iff]
  intro R
  set r : ℝ := 2 * ((R : ℝ) + 1) with hr
  have hr0 : 0 ≤ r := by positivity
  set L := heatLipConst s r
  have hL : 0 ≤ L := heatLipConst_nonneg s r hs hr0
  set K0 : ℝ := (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + r)
  have hK0 : 0 ≤ K0 := by positivity
  set g4 := QuantumZipper.gaussianAbsMoment 4
  have hg4 : 0 ≤ g4 := QuantumZipper.gaussianAbsMoment_nonneg 4
  have hmz := mzConst_nonneg
  set c : ℝ := g4 * mzConst ^ 2 * (2 * L + K0) ^ 4
  have hc : 0 ≤ c := by positivity
  set Kn : ℕ → ℝ := fun n => c * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4
  set l : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / 2)
  set cR : ℝ := ((2 * R + 1) ^ 2 + (2 : ℕ) * (2 * R + 1) ^ 2 /
    (1 - (2 : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ (4 : ℝ) / (3 / 4 : ℝ) ^ 4)))
  have hρ : (2 : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ (4 : ℝ) / (3 / 4 : ℝ) ^ 4) < 1 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hcR : 0 ≤ cR := by
    have : 0 < 1 - (2 : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ (4 : ℝ) / (3 / 4 : ℝ) ^ 4) := by linarith
    positivity
  have hbound : ∀ n : ℕ, P {ω | ∃ q ∈ QuantumZipper.KolmD.boxD (d := 2) R,
      (((2 : ℕ) : ℝ) / (1 - 3 / 4) + 1) * l n < |gaussDiffProc h s n q ω|} ≤
      ENNReal.ofReal (Kn n / l n ^ 4 * cR) := by
    intro n
    have ht : (1 : ℝ) ≤ (n : ℝ) + 3 := by linarith [n.cast_nonneg (α := ℝ)]
    have hsupp : ∀ z : ℂ, ∀ w : ℂ, (n : ℝ) + 3 < ‖w‖ → heatDiff s z n w = 0 :=
      fun z w hw => heatTrunc_succ_sub_eq_zero' s z n w hw.le
    have hmom : QuantumZipper.KolmG.MomentBoundG (fun q ω => gaussDiffProc h s n q ω) P 4 4
        (Kn n) (R + 1) := by
      intro q hq q' hq'
      simp only
      simp_rw [gaussDiffProc_sub]
      have hzq : ‖cplxOf q‖ ≤ r := (norm_cplxOf_le q).trans (by
        have := norm_le_of_mem_boxD hq; push_cast at this ⊢; linarith)
      have hzq' : ‖cplxOf q'‖ ≤ r := (norm_cplxOf_le q').trans (by
        have := norm_le_of_mem_boxD hq'; push_cast at this ⊢; linarith)
      have hB : ∀ w, |(heatDiff s (cplxOf q) n - heatDiff s (cplxOf q') n) w| ≤
          L * Real.exp (-(n : ℝ)) * (2 * ‖q - q'‖) := by
        intro w
        refine (abs_heatDiff_sub_le s hs r hr0 _ _ hzq hzq' n w).trans ?_
        rw [cplxOf_sub]
        exact mul_le_mul_of_nonneg_left (norm_cplxOf_le _) (by positivity)
      refine (hh.lintegral_pow_four_le _ (by positivity) ht hB (fun w hw => by
        show heatDiff s (cplxOf q) n w - heatDiff s (cplxOf q') n w = 0
        rw [hsupp _ w hw, hsupp _ w hw, sub_zero])).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [Kn, c]
      have hq0 := norm_nonneg (q - q')
      have hLK : (2 * L) ^ 4 ≤ (2 * L + K0) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      calc g4 * mzConst ^ 2 * (L * Real.exp (-(n : ℝ)) * (2 * ‖q - q'‖)) ^ 4 * ((n : ℝ) + 3) ^ 18
          = g4 * mzConst ^ 2 * (2 * L) ^ 4 * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4 *
              ‖q - q'‖ ^ 4 := by ring
        _ ≤ g4 * mzConst ^ 2 * (2 * L + K0) ^ 4 * ((n : ℝ) + 3) ^ 18 *
              Real.exp (-(n : ℝ)) ^ 4 * ‖q - q'‖ ^ 4 := by gcongr
    have hpt : ∀ q ∈ QuantumZipper.KolmD.boxD (d := 2) R,
        ∫⁻ ω, ENNReal.ofReal (|gaussDiffProc h s n q ω| ^ 4) ∂P ≤ ENNReal.ofReal (Kn n) := by
      intro q hq
      have hzq : ‖cplxOf q‖ ≤ r := (norm_cplxOf_le q).trans (by
        have := norm_le_of_mem_boxD hq; linarith)
      refine (hh.lintegral_pow_four_le _ (by positivity) ht
        (fun w => abs_heatTrunc_succ_sub_le s hs _ r hzq n w) (hsupp _)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      simp only [Kn, c]
      have hLK : K0 ^ 4 ≤ (2 * L + K0) ^ 4 := pow_le_pow_left₀ hK0 (by linarith) 4
      calc g4 * mzConst ^ 2 * (K0 * Real.exp (-(n : ℝ))) ^ 4 * ((n : ℝ) + 3) ^ 18
          = g4 * mzConst ^ 2 * K0 ^ 4 * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4 := by ring
        _ ≤ _ := by gcongr
    exact QuantumZipper.Thm18Asm.G1FM.kolm_sup_tail_N (θ := 3 / 4) (by norm_num) (by norm_num)
      (fun ω => continuous_gaussDiffProc s n ω)
      (fun q => (measurable_gaussDiffProc hh s n q).aemeasurable) (by norm_num)
      (by positivity) hρ hmom hpt (Real.exp_pos _)
  -- summability of the bounds
  have hsum : Summable fun n : ℕ => Kn n / l n ^ 4 * cR := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((summable_shift_pow_mul_exp 18).mul_left (c * cR)))
    simp only [Kn, l]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_div_assoc, ← Real.exp_sub]
    have : Real.exp ((4 : ℕ) * -(n : ℝ) - (4 : ℕ) * (-(n : ℝ) / 2)) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.2; push_cast; linarith [n.cast_nonneg (α := ℝ)]
    have h18 : 0 ≤ ((n : ℝ) + 3) ^ 18 := by positivity
    calc c * ((n : ℝ) + 3) ^ 18 * Real.exp ((4 : ℕ) * -(n : ℝ) - (4 : ℕ) * (-(n : ℝ) / 2)) * cR
        ≤ c * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) * cR := by gcongr
      _ = _ := by ring
  have hBC : ∑' n, P {ω | ∃ q ∈ QuantumZipper.KolmD.boxD (d := 2) R,
      (((2 : ℕ) : ℝ) / (1 - 3 / 4) + 1) * l n < |gaussDiffProc h s n q ω|} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hBC] with ω hω
  filter_upwards [hω] with n hn q hq
  simp only [mem_setOf_eq, not_exists, not_and, not_lt] at hn
  have := hn q hq
  norm_num at this
  simpa [l] using this

end LQGMetric
