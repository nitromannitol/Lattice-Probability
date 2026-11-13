/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Inputs.Gaussian at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L24
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Zero
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Sup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiSupTail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8




 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Inputs.Gaussian
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 

theorem quantile_ratio_sqrt (hW : IsWhiteNoise P W) (ξ : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (n : ℕ) :
    LambdaN ξ W P n (ENNReal.ofReal p) ≤
      Real.exp ((Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p) * Real.sqrt n) := by
  letI := hW.isProbabilityMeasure
  unfold LambdaN
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le k)
  have h23 := dddf_lemma23_sharp hW ξ k
  have hratio := L24.ratio_le_of_variance hφ.cont hφ.meas h23.1 hp0 hp
  change ellBarN ξ W P k (ENNReal.ofReal p) / ellN ξ W P k (ENNReal.ofReal p) ≤ _
  refine hratio.trans (Real.exp_le_exp.2 ?_)
  have hV : Var[fun ω => Real.log (lenObs ξ (phiMN W P 0 k) (rectAB 1 1) ω); P] ≤
      ξ ^ 2 * (n * Real.log 2) := by
    apply h23.2.trans
    gcongr
  have harg : 2 * Var[fun ω => Real.log (lenObs ξ (phiMN W P 0 k) (rectAB 1 1) ω); P] ≤
      n * (2 * ξ ^ 2 * Real.log 2) := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt harg
  calc
    _ ≤ Real.sqrt ((n : ℝ) * (2 * ξ ^ 2 * Real.log 2)) / p :=
      div_le_div_of_nonneg_right hsqrt hp0.le
    _ = Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p * Real.sqrt n := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      ring


 

theorem octave_sup_tail (hW : IsWhiteNoise P W) (m : ℕ) {a : ℝ}
    (ha0 : 0 < a) (ha_lo : ((2 : ℝ) ^ m)⁻¹ / 2 ≤ a)
    (ha_hi : a ≤ ((2 : ℝ) ^ m)⁻¹) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hY : ∀ z, (fun ω => Y z ω) =ᵐ[P]
      phi W a (((2 : ℝ) ^ m)⁻¹) z) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (2 * Real.sqrt 2) + u) ≤
      ⨆ z ∈ SupTail.ferniqueBox 0 1, ENNReal.ofReal |Y z ω|} ≤
      ENNReal.ofReal (2 * 4 ^ m * Real.exp (-u ^ 2 / (2 * Real.log 2))) := by
  letI := hW.isProbabilityMeasure
  let N : ℕ := 2 ^ m
  have hN0 : 0 < N := by simp [N]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have haN : (N : ℝ)⁻¹ / 2 ≤ a := by simpa [N] using ha_lo
  have haNhi : a ≤ (N : ℝ)⁻¹ := by simpa [N] using ha_hi
  have hY' : ∀ z, (fun ω => Y z ω) =ᵐ[P] phi W a ((N : ℝ)⁻¹) z := by
    intro z
    simpa [N] using hY z
  have hX : IsGaussianProcess Y P :=
    (isGaussianProcess_phi_comp hW a ((N : ℝ)⁻¹) (fun z : ℂ => z)).congr
      fun z => (hY' z).symm
  have h0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := fun z => by
    rw [integral_congr_ae (hY' z)]
    exact integral_phi hW a _ z
  have hinc : ∀ z w, ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤
      (2 * Real.sqrt 2 * N) * ‖z - w‖ := by
    intro z w
    have hm : AEMeasurable (fun ω => phi W a ((N : ℝ)⁻¹) w ω -
        phi W a ((N : ℝ)⁻¹) z ω) P :=
      ((measurable_phi hW a _ w).sub (measurable_phi hW a _ z)).aemeasurable
    have hmean : ∫ ω, (phi W a ((N : ℝ)⁻¹) w ω -
        phi W a ((N : ℝ)⁻¹) z ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW a _ w).integrable one_le_two)
        ((memLp_phi hW a _ z).integrable one_le_two),
        integral_phi hW, integral_phi hW, sub_zero]
    have hae : (fun ω => (Y w ω - Y z ω) ^ 2) =ᵐ[P]
        fun ω => (phi W a ((N : ℝ)⁻¹) w ω - phi W a ((N : ℝ)⁻¹) z ω) ^ 2 := by
      filter_upwards [hY' z, hY' w] with ω hz hw
      rw [hz, hw]
    rw [integral_congr_ae hae, ← variance_of_integral_eq_zero hm hmean]
    have hv := LQGMetric.DZZ.variance_phi_band_sub_le hW (b := (N : ℝ)⁻¹) ha0 w z
    refine hv.trans ?_
    have hane : (N : ℝ)⁻¹ / 2 > 0 := by positivity
    have hmul : 1 ≤ 2 * (N : ℝ) * a := by
      have := haN
      field_simp at this ⊢
      nlinarith
    have hcoef : Real.sqrt 2 / a ≤ 2 * Real.sqrt 2 * N := by
      apply (div_le_iff₀ ha0).2
      nlinarith [Real.sqrt_nonneg 2]
    calc Real.sqrt 2 * ‖w - z‖ / a = (Real.sqrt 2 / a) * ‖z - w‖ := by
          rw [norm_sub_rev]; ring
      _ ≤ (2 * Real.sqrt 2 * N) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hvar : ∀ z, Var[Y z; P] ≤ (Real.sqrt (Real.log 2)) ^ 2 := by
    intro z
    rw [variance_congr (hY' z), variance_phi hW ha0 haNhi,
      Real.sq_sqrt (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    apply Real.log_le_log (div_pos (by positivity) ha0)
    apply (div_le_iff₀ ha0).2
    have := haN
    field_simp at this ⊢
    nlinarith
  have hA : 0 < 2 * Real.sqrt 2 * (N : ℝ) := by positivity
  have hσ : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  have htail := LQGMetric.SupTail.tail_iSup_abs_square hN0 (by norm_num : (0 : ℝ) < 1)
    hX h0 hYc hA hinc hσ hvar hu
  have hfactor : 2 * Real.sqrt 2 * (N : ℝ) * (1 / N) = 2 * Real.sqrt 2 := by
    field_simp
  have hcard : (N : ℝ) ^ 2 = (4 : ℝ) ^ m := by
    simp only [N, Nat.cast_pow]
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  simpa only [hfactor, Real.sq_sqrt (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)),
    hcard] using htail


 
theorem octave_sup_eighth (hW : IsWhiteNoise P W) (m : ℕ) {a : ℝ}
    (ha0 : 0 < a) (ha_lo : ((2 : ℝ) ^ m)⁻¹ / 2 ≤ a)
    (ha_hi : a ≤ ((2 : ℝ) ^ m)⁻¹) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hY : ∀ z, (fun ω => Y z ω) =ᵐ[P]
      phi W a (((2 : ℝ) ^ m)⁻¹) z) :
    P {ω | ENNReal.ofReal
        (SupTail.ferniqueCF * Real.sqrt (2 * Real.sqrt 2) +
          Real.sqrt (2 * Real.log 2 * Real.log (16 * (4 : ℝ) ^ m))) ≤
      ⨆ z ∈ SupTail.ferniqueBox 0 1, ENNReal.ofReal |Y z ω|} ≤
      ENNReal.ofReal (1 / 8 : ℝ) := by
  let T : ℝ := 16 * (4 : ℝ) ^ m
  have hT : 0 < T := by positivity
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    dsimp [T]
    nlinarith
  let u : ℝ := Real.sqrt (2 * Real.log 2 * Real.log T)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * Real.log 2 * Real.log T :=
    Real.sq_sqrt (mul_nonneg (by positivity) (Real.log_nonneg hT1))
  have htail := octave_sup_tail hW m ha0 ha_lo ha_hi hYc hY hu
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hexp : Real.exp (-(2 * Real.log 2 * Real.log T) / (2 * Real.log 2)) = T⁻¹ := by
    rw [show -(2 * Real.log 2 * Real.log T) / (2 * Real.log 2) = -Real.log T by
      field_simp, Real.exp_neg, Real.exp_log hT]
  have hR : 2 * (4 : ℝ) ^ m * Real.exp (-u ^ 2 / (2 * Real.log 2)) = 1 / 8 := by
    rw [hu2, hexp]
    have hp : (4 : ℝ) ^ m ≠ 0 := ne_of_gt (by positivity)
    simp only [T]
    field_simp
    norm_num
  change P {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (2 * Real.sqrt 2) + u) ≤
      ⨆ z ∈ SupTail.ferniqueBox 0 1, ENNReal.ofReal |Y z ω|} ≤ ENNReal.ofReal (1 / 8 : ℝ)
  simpa only [hR] using htail


 

theorem octave_sup_sqrt (hW : IsWhiteNoise P W) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) {a : ℝ}, 0 < a →
      ((2 : ℝ) ^ m)⁻¹ / 2 ≤ a → a ≤ ((2 : ℝ) ^ m)⁻¹ →
      ∀ {Y : ℂ → Ω → ℝ}, (∀ ω, Continuous fun z => Y z ω) →
      (∀ z, (fun ω => Y z ω) =ᵐ[P] phi W a (((2 : ℝ) ^ m)⁻¹) z) →
      P {ω | ENNReal.ofReal (B * Real.sqrt (m + 1 : ℝ)) ≤
        ⨆ z ∈ SupTail.ferniqueBox 0 1, ENNReal.ofReal |Y z ω|} ≤
        ENNReal.ofReal (1 / 8 : ℝ) := by
  let c : ℝ := SupTail.ferniqueCF * Real.sqrt (2 * Real.sqrt 2)
  let d : ℝ := Real.sqrt (2 * Real.log 2 * Real.log 16)
  refine ⟨c + d, by have := SupTail.ferniqueCF_pos; positivity, ?_⟩
  intro m a ha0 ha_lo ha_hi Y hYc hY
  let T : ℝ := 16 * (4 : ℝ) ^ m
  have hT : 0 < T := by positivity
  have hlog : Real.log T ≤ (m + 1 : ℝ) * Real.log 16 := by
    have h4 : Real.log 4 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [show T = 16 * (4 : ℝ) ^ m by rfl, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
      (ne_of_gt (by positivity : (0 : ℝ) < 4 ^ m)), Real.log_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) hm]
  have harg : 2 * Real.log 2 * Real.log T ≤
      (m + 1 : ℝ) * (2 * Real.log 2 * Real.log 16) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * Real.log 2)]
  have hu : Real.sqrt (2 * Real.log 2 * Real.log T) ≤
      d * Real.sqrt (m + 1 : ℝ) := by
    have hh := Real.sqrt_le_sqrt harg
    rw [Real.sqrt_mul (by positivity : 0 ≤ (m + 1 : ℝ))] at hh
    simpa [d, mul_comm] using hh
  have hroot : (1 : ℝ) ≤ Real.sqrt (m + 1 : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
  have hc : 0 ≤ c := by have := SupTail.ferniqueCF_pos; positivity
  have hthresh : c + Real.sqrt (2 * Real.log 2 * Real.log T) ≤
      (c + d) * Real.sqrt (m + 1 : ℝ) := by
    calc c + Real.sqrt (2 * Real.log 2 * Real.log T)
        ≤ c * Real.sqrt (m + 1 : ℝ) + d * Real.sqrt (m + 1 : ℝ) :=
          add_le_add (by nlinarith) hu
      _ = (c + d) * Real.sqrt (m + 1 : ℝ) := by ring
  have htail := octave_sup_eighth hW m ha0 ha_lo ha_hi hYc hY
  refine (measure_mono ?_).trans htail
  intro ω hω
  exact (ENNReal.ofReal_le_ofReal hthresh).trans hω


 

theorem real_sup_event_subset {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω) (t : ℝ) :
    {ω | t ≤ ⨆ z : SupTail.ferniqueBox 0 1, |Y z ω|} ⊆
      {ω | ENNReal.ofReal t ≤ ⨆ z ∈ SupTail.ferniqueBox 0 1,
        ENNReal.ofReal |Y z ω|} := by
  intro ω hω
  have hc : Continuous fun z => |Y z ω| := continuous_abs.comp (hYc ω)
  obtain ⟨z, hz, hmax⟩ := (SupTail.isCompact_ferniqueBox 0 1).exists_isMaxOn
    ⟨0, SupTail.mem_ferniqueBox_self (by norm_num)⟩ hc.continuousOn
  letI : Nonempty (SupTail.ferniqueBox 0 1) :=
    ⟨⟨0, SupTail.mem_ferniqueBox_self (by norm_num)⟩⟩
  have hsup : (⨆ x : SupTail.ferniqueBox 0 1, |Y x ω|) ≤ |Y z ω| :=
    ciSup_le fun x => hmax x.2
  exact (ENNReal.ofReal_le_ofReal (hω.trans hsup)).trans
    (le_iSup₂ (f := fun z (_ : z ∈ SupTail.ferniqueBox 0 1) =>
      ENNReal.ofReal |Y z ω|) z hz)

 
end SupercriticalLQGUniqueness.Exponent.Inputs.Gaussian
