/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.WeightedMoment at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82,
   lines 86–394; the preceding declarations are imported from WeightedMoment. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedMoment

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter Topology
open QuantumZipper.LQGMeas
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-! ### The weighted mass -/

/-- The `|z|^{−γ²}`-weighted mass of the unit disc (the integrand vanishes at `0` by the `rpow` convention). -/
def wDiscMass (γ : ℝ) (ν : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ z in ball 0 1, ENNReal.ofReal (‖z‖ ^ (-γ ^ 2)) ∂ν

/-- The punctured unit disc. -/
def pDisc : Set ℂ := ball 0 1 ∩ {0}ᶜ

lemma isOpen_pDisc : IsOpen pDisc := isOpen_ball.inter isOpen_compl_singleton

lemma isBounded_pDisc : Bornology.IsBounded pDisc := isBounded_ball.subset inter_subset_left

lemma zero_notMem_pDisc : (0 : ℂ) ∉ pDisc := fun h => h.2 rfl

lemma continuous_openBump_mul_weight (γ : ℝ) (n : ℕ) :
    Continuous fun z : ℂ => openBump pDisc n z * ‖z‖ ^ (-γ ^ 2) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z = 0
  · subst hz
    have h0 : (0 : ℂ) ∉ tsupport (openBump pDisc n) := fun h =>
      zero_notMem_pDisc (tsupport_openBump_subset pDisc n h)
    have hev : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 0] fun z => openBump pDisc n z * ‖z‖ ^ (-γ ^ 2) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h0] with w hw
      rw [hw, Pi.zero_apply, zero_mul]
    exact continuousAt_const.congr hev
  · have hG : ContinuousAt (fun z : ℂ => ‖z‖ ^ (-γ ^ 2)) z :=
      continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.2 hz))
    exact (continuous_openBump pDisc n).continuousAt.mul hG

lemma wDiscMass_eq_iSup {γ : ℝ} (hγ : 0 < γ) (ν : Measure ℂ) :
    wDiscMass γ ν = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (openBump pDisc n z * ‖z‖ ^ (-γ ^ 2)) ∂ν := by
  have hUc : pDiscᶜ.Nonempty := ⟨0, zero_notMem_pDisc⟩
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (openBump pDisc n z * ‖z‖ ^ (-γ ^ 2)))
    (fun n => ENNReal.measurable_ofReal.comp
      (continuous_openBump_mul_weight γ n).measurable)
    (fun m n hmn z => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (openBump_mono pDisc z hmn)
      (Real.rpow_nonneg (norm_nonneg _) _))), wDiscMass, ← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun z => ?_
  have hsplit : ∀ n, ENNReal.ofReal (openBump pDisc n z * ‖z‖ ^ (-γ ^ 2)) =
      ENNReal.ofReal (openBump pDisc n z) * ENNReal.ofReal (‖z‖ ^ (-γ ^ 2)) := fun n =>
    ENNReal.ofReal_mul (openBump_nonneg _ _ _)
  simp_rw [hsplit]
  rw [← ENNReal.iSup_mul, iSup_openBump isOpen_pDisc hUc]
  by_cases hz0 : z = 0
  · subst hz0
    have hγ2 : -γ ^ 2 ≠ 0 := by have := pow_pos hγ 2; linarith
    rw [norm_zero, Real.zero_rpow hγ2, ENNReal.ofReal_zero, mul_zero]
    by_cases h : (0 : ℂ) ∈ ball (0 : ℂ) 1
    · rw [indicator_of_mem h, norm_zero, Real.zero_rpow hγ2, ENNReal.ofReal_zero]
    · rw [indicator_of_notMem h]
  · by_cases hb : z ∈ ball (0 : ℂ) 1
    · rw [indicator_of_mem hb, indicator_of_mem (show z ∈ pDisc from ⟨hb, hz0⟩), Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hb, indicator_of_notMem (fun h : z ∈ pDisc => hb h.1), zero_mul]

/-- **The weighted mass is a.e.-measurable.** -/
theorem aemeasurable_wDiscMass (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) {μ : Ω → Measure ℂ}
    (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) : AEMeasurable (fun ω => wDiscMass γ (μ ω)) P := by
  simp_rw [wDiscMass_eq_iSup hγ]
  exact AEMeasurable.iSup fun n => aemeasurable_lintegral_ofReal hH hHm hμ
    (continuous_openBump_mul_weight γ n) ((hasCompactSupport_openBump isBounded_pDisc n).mul_right)
    fun z => mul_nonneg (openBump_nonneg _ _ _) (Real.rpow_nonneg (norm_nonneg _) _)

/-! ### Dyadic annuli -/

lemma radius_eq_rpow (n : ℕ) : QuantumZipper.radius n = (2⁻¹ : ℝ) ^ (n : ℝ) := by
  rw [Real.rpow_natCast]; rfl

lemma qzRadius_le_one (n : ℕ) : QuantumZipper.radius n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-- `wDiscMass ≤ ∑ₙ 2^{(n+1)γ²} μ(B_{2^{-n}})`. -/
lemma wDiscMass_le_tsum {γ : ℝ} (hγ : 0 < γ) (ν : Measure ℂ) :
    wDiscMass γ ν ≤ ∑' n : ℕ, ENNReal.ofReal (QuantumZipper.radius (n + 1) ^ (-γ ^ 2)) *
      ν (ball 0 (QuantumZipper.radius n)) := by
  set F : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (-γ ^ 2))
  set A : ℕ → Set ℂ := fun n => ball 0 (QuantumZipper.radius n) \ ball 0 (QuantumZipper.radius (n + 1))
  have hγ2 : -γ ^ 2 ≠ 0 := by have := pow_pos hγ 2; linarith
  have hcover : ball (0 : ℂ) 1 ⊆ {0} ∪ ⋃ n, A n := by
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    refine Or.inr (mem_iUnion.2 ?_)
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hlt : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    -- the largest `n` with `‖z‖ < 2^{-n}`
    have hex : ∃ n : ℕ, ¬ ‖z‖ < QuantumZipper.radius (n + 1) := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2⁻¹ : ℝ) < 1)
      exact ⟨n, fun h => by
        have : QuantumZipper.radius (n + 1) ≤ QuantumZipper.radius n :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
        exact absurd hn (not_lt.2 (le_of_lt (h.trans_le this)))⟩
    classical
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos'
      · rw [h0]; simpa [QuantumZipper.radius] using hlt
      · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hpos'.ne'
        have := Nat.find_min hex (show m < Nat.find hex by omega)
        rw [not_not] at this
        rw [hm]
        exact this
    · rw [mem_ball_zero_iff]
      exact Nat.find_spec hex
  have hA : ∀ n, ∫⁻ z in A n, F z ∂ν ≤
      ENNReal.ofReal (QuantumZipper.radius (n + 1) ^ (-γ ^ 2)) * ν (ball 0 (QuantumZipper.radius n)) := by
    intro n
    calc ∫⁻ z in A n, F z ∂ν ≤ ∫⁻ _z in A n, ENNReal.ofReal (QuantumZipper.radius (n + 1) ^ (-γ ^ 2)) ∂ν := by
          refine setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun z hz => ?_
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (QuantumZipper.radius_pos _) ?_
            (by nlinarith [sq_nonneg γ]))
          have := hz.2
          rw [mem_ball_zero_iff, not_lt] at this
          exact this
      _ = ENNReal.ofReal (QuantumZipper.radius (n + 1) ^ (-γ ^ 2)) * ν (A n) := setLIntegral_const _ _
      _ ≤ _ := by gcongr; exact sdiff_subset
  calc wDiscMass γ ν ≤ ∫⁻ z in {0} ∪ ⋃ n, A n, F z ∂ν := lintegral_mono_set hcover
    _ ≤ ∫⁻ z in {0}, F z ∂ν + ∫⁻ z in ⋃ n, A n, F z ∂ν := lintegral_union_le _ _ _
    _ ≤ 0 + ∑' n, ∫⁻ z in A n, F z ∂ν := by
        gcongr
        · rw [lintegral_singleton]
          simp only [F, norm_zero, Real.zero_rpow hγ2, ENNReal.ofReal_zero, zero_mul, le_refl]
        · exact lintegral_iUnion_le _ _
    _ ≤ _ := by rw [zero_add]; exact ENNReal.tsum_le_tsum hA

/-! ### Summation: subadditivity and Minkowski -/

/-- Subadditivity of `x ↦ x^p` (`p ≤ 1`) under the expectation of a series. -/
lemma lintegral_tsum_rpow_le_of_le_one {x : ℕ → Ω → ℝ≥0∞} (hx : ∀ n, AEMeasurable (x n) P) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫⁻ ω, (∑' n, x n ω) ^ p ∂P ≤ ∑' n, ∫⁻ ω, x n ω ^ p ∂P := by
  have hS : ∀ N, ∀ ω, (∑ n ∈ range N, x n ω) ^ p ≤ ∑ n ∈ range N, x n ω ^ p := by
    intro N ω
    induction N with
    | zero => simp [ENNReal.zero_rpow_of_pos hp0]
    | succ N ih =>
      rw [sum_range_succ, sum_range_succ]
      exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add ih le_rfl)
  calc ∫⁻ ω, (∑' n, x n ω) ^ p ∂P
      = ∫⁻ ω, liminf (fun N => (∑ n ∈ range N, x n ω) ^ p) atTop ∂P := by
        refine lintegral_congr fun ω => ?_
        exact ((((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
          (ENNReal.tendsto_nat_tsum fun n => x n ω)).liminf_eq).symm
    _ ≤ liminf (fun N => ∫⁻ ω, (∑ n ∈ range N, x n ω) ^ p ∂P) atTop :=
        lintegral_liminf_le' fun N => (Finset.aemeasurable_fun_sum _ fun n _ => hx n).pow_const p
    _ ≤ ∑' n, ∫⁻ ω, x n ω ^ p ∂P := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
        calc ∫⁻ ω, (∑ n ∈ range N, x n ω) ^ p ∂P ≤ ∫⁻ ω, ∑ n ∈ range N, x n ω ^ p ∂P :=
              lintegral_mono fun ω => hS N ω
          _ = ∑ n ∈ range N, ∫⁻ ω, x n ω ^ p ∂P :=
              lintegral_finsetSum' _ fun n _ => (hx n).pow_const p
          _ ≤ _ := ENNReal.sum_le_tsum _

/-- **Minkowski's inequality for series** (`p ≥ 1`). -/
lemma lintegral_tsum_rpow_le_of_one_le {x : ℕ → Ω → ℝ≥0∞} (hx : ∀ n, AEMeasurable (x n) P) {p : ℝ}
    (hp1 : 1 ≤ p) :
    ∫⁻ ω, (∑' n, x n ω) ^ p ∂P ≤ (∑' n, (∫⁻ ω, x n ω ^ p ∂P) ^ (1 / p)) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp1
  set T := ∑' n, (∫⁻ ω, x n ω ^ p ∂P) ^ (1 / p)
  have hS : ∀ N, (∫⁻ ω, (∑ n ∈ range N, x n ω) ^ p ∂P) ^ (1 / p) ≤
      ∑ n ∈ range N, (∫⁻ ω, x n ω ^ p ∂P) ^ (1 / p) := by
    intro N
    induction N with
    | zero => simp [ENNReal.zero_rpow_of_pos hp0, hp0]
    | succ N ih =>
      simp_rw [sum_range_succ]
      exact (ENNReal.lintegral_Lp_add_le (f := fun ω => ∑ n ∈ range N, x n ω) (g := x N)
        (Finset.aemeasurable_fun_sum _ fun n _ => hx n) (hx N) hp1).trans (add_le_add ih le_rfl)
  calc ∫⁻ ω, (∑' n, x n ω) ^ p ∂P
      = ∫⁻ ω, liminf (fun N => (∑ n ∈ range N, x n ω) ^ p) atTop ∂P := by
        refine lintegral_congr fun ω => ?_
        exact ((((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
          (ENNReal.tendsto_nat_tsum fun n => x n ω)).liminf_eq).symm
    _ ≤ liminf (fun N => ∫⁻ ω, (∑ n ∈ range N, x n ω) ^ p ∂P) atTop :=
        lintegral_liminf_le' fun N => (Finset.aemeasurable_fun_sum _ fun n _ => hx n).pow_const p
    _ ≤ T ^ p := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
        exact (ENNReal.rpow_inv_le_iff hp0).1 (by
          rw [← one_div]; exact (hS N).trans (ENNReal.sum_le_tsum _))

/-! ### The moment bound -/

/-- `2^{-(n+1)(−a)} 2^{−n b} = 2^a (2^{a−b})^n`, in terms of `QuantumZipper.radius`. -/
lemma radius_rpow_mul_radius_rpow (a b : ℝ) (n : ℕ) :
    QuantumZipper.radius (n + 1) ^ (-a) * QuantumZipper.radius n ^ b =
      (2 : ℝ) ^ a * ((2⁻¹ : ℝ) ^ (b - a)) ^ n := by
  have h2 : (0 : ℝ) < 2⁻¹ := by norm_num
  rw [radius_eq_rpow, radius_eq_rpow, ← Real.rpow_mul h2.le, ← Real.rpow_mul h2.le, ← Real.rpow_add h2,
    ← Real.rpow_natCast, ← Real.rpow_mul h2.le, show (2 : ℝ) ^ a = (2⁻¹ : ℝ) ^ (-a) by
      rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv], ← Real.rpow_add h2]
  congr 1
  push_cast
  ring

/-- `∑ₙ ofReal(c ρⁿ) < ∞` for `0 ≤ ρ < 1`. -/
lemma tsum_ofReal_mul_pow_lt_top {c ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑' n : ℕ, ENNReal.ofReal (c * ρ ^ n) < ⊤ := by
  have e : ∀ n : ℕ, ENNReal.ofReal (c * ρ ^ n) ≤ ENNReal.ofReal |c| * ENNReal.ofReal ρ ^ n := fun n => by
    rw [← ENNReal.ofReal_pow hρ0, ← ENNReal.ofReal_mul (abs_nonneg c)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg hρ0 n))
  refine (ENNReal.tsum_le_tsum e).trans_lt ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 ?_))
  exact ENNReal.ofReal_lt_one.2 hρ1

/-- **[16, Lemma A.3] for `α = γ`**: `E[(∫_{B_1} |z|^{−γ²} dμ)^p] < ∞` for `0 < p < 4/γ² − 1`. -/
theorem lintegral_wDiscMass_rpow_lt_top (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) {μ : Ω → Measure ℂ}
    (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) {p : ℝ} (hp0 : 0 < p) (hp : p < 4 / γ ^ 2 - 1) :
    ∫⁻ ω, wDiscMass γ (μ ω) ^ p ∂P < ⊤ := by
  have hP := hH.isProbabilityMeasure
  have hγ2 : 0 < γ ^ 2 := pow_pos hγ 2
  have hp' : p < 4 / γ ^ 2 := by linarith
  -- `pγ² < 4 − γ²`
  have hpγ : p * γ ^ 2 < 4 - γ ^ 2 := by
    have := (lt_div_iff₀ hγ2).1 (show p + 1 < 4 / γ ^ 2 by linarith)
    nlinarith
  set ζ := p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2 with hζ
  have hζpos : 0 ≤ ζ := by
    have : ζ = p * (2 + γ ^ 2 / 2 - p * γ ^ 2 / 2) := by rw [hζ]; ring
    rw [this]; exact mul_nonneg hp0.le (by nlinarith)
  -- the ball moments `E μ(B_{2^{-n}})^p ≤ C₁ 2^{-nζ}`
  obtain ⟨C, hC, hball⟩ := exists_lintegral_ball_origin_rpow_le hH hHm hγ hμ hp0 hp'
  set M₁ := ∫⁻ ω, μ ω (ball 0 1) ^ p ∂P
  have hM₁ : M₁ < ⊤ := lintegral_ball_one_rpow_lt_top hH hHm hγ hμ hp0 hp'
  set C₁ := C + M₁ * ENNReal.ofReal ((64 : ℝ) ^ ζ)
  have hC₁ : C₁ < ⊤ := ENNReal.add_lt_top.2 ⟨hC, ENNReal.mul_lt_top hM₁ ENNReal.ofReal_lt_top⟩
  have ha : ∀ n : ℕ, ∫⁻ ω, μ ω (ball 0 (QuantumZipper.radius n)) ^ p ∂P ≤
      C₁ * ENNReal.ofReal (QuantumZipper.radius n ^ ζ) := by
    intro n
    have hr := QuantumZipper.radius_pos n
    rcases le_or_gt 6 n with h6 | h6
    · have hr64 : QuantumZipper.radius n ≤ 1 / 64 := by
        calc QuantumZipper.radius n ≤ QuantumZipper.radius 6 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
          _ = 1 / 64 := by norm_num [QuantumZipper.radius]
      exact (hball _ hr hr64).trans (by gcongr; exact le_self_add)
    · have h64 : 1 ≤ (64 : ℝ) ^ ζ * QuantumZipper.radius n ^ ζ := by
        rw [← Real.mul_rpow (by norm_num) hr.le]
        refine Real.one_le_rpow ?_ hζpos
        have : QuantumZipper.radius 6 ≤ QuantumZipper.radius n :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) h6.le
        have h6' : QuantumZipper.radius 6 = 1 / 64 := by norm_num [QuantumZipper.radius]
        rw [h6'] at this
        linarith
      calc ∫⁻ ω, μ ω (ball 0 (QuantumZipper.radius n)) ^ p ∂P ≤ M₁ :=
            lintegral_mono fun ω => ENNReal.rpow_le_rpow
              (measure_mono (ball_subset_ball (qzRadius_le_one n))) hp0.le
        _ ≤ M₁ * ENNReal.ofReal ((64 : ℝ) ^ ζ) * ENNReal.ofReal (QuantumZipper.radius n ^ ζ) := by
            rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            exact le_mul_of_one_le_right' (ENNReal.one_le_ofReal.2 h64)
        _ ≤ C₁ * ENNReal.ofReal (QuantumZipper.radius n ^ ζ) := by gcongr; exact le_add_self
  -- the series
  set c : ℕ → ℝ := fun n => QuantumZipper.radius (n + 1) ^ (-γ ^ 2)
  have hc0 : ∀ n, 0 ≤ c n := fun n => Real.rpow_nonneg (QuantumZipper.radius_pos _).le _
  set x : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (c n) * μ ω (ball 0 (QuantumZipper.radius n))
  have hx : ∀ n, AEMeasurable (x n) P := fun n =>
    (aemeasurable_measure_ball hH hHm hμ 0 _).const_mul _
  have hle : ∫⁻ ω, wDiscMass γ (μ ω) ^ p ∂P ≤ ∫⁻ ω, (∑' n, x n ω) ^ p ∂P :=
    lintegral_mono fun ω => ENNReal.rpow_le_rpow (wDiscMass_le_tsum hγ (μ ω)) hp0.le
  have hxn : ∀ n, ∫⁻ ω, x n ω ^ p ∂P ≤
      ENNReal.ofReal (c n) ^ p * (C₁ * ENNReal.ofReal (QuantumZipper.radius n ^ ζ)) := by
    intro n
    simp only [x]
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
    gcongr
    exact ha n
  refine hle.trans_lt ?_
  rcases le_or_gt p 1 with hp1 | hp1
  · -- subadditivity
    refine (lintegral_tsum_rpow_le_of_le_one hx hp0 hp1).trans_lt ?_
    refine (ENNReal.tsum_le_tsum hxn).trans_lt ?_
    have e : ∀ n : ℕ, ENNReal.ofReal (c n) ^ p * (C₁ * ENNReal.ofReal (QuantumZipper.radius n ^ ζ)) =
        C₁ * ENNReal.ofReal ((2 : ℝ) ^ (p * γ ^ 2) * ((2⁻¹ : ℝ) ^ (ζ - p * γ ^ 2)) ^ n) := by
      intro n
      rw [ENNReal.ofReal_rpow_of_nonneg (hc0 n) hp0.le, mul_left_comm, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (hc0 n) _), ← radius_rpow_mul_radius_rpow]
      congr 3
      simp only [c]
      rw [← Real.rpow_mul (QuantumZipper.radius_pos _).le]
      ring_nf
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top hC₁ (tsum_ofReal_mul_pow_lt_top (by positivity) ?_)
    refine Real.rpow_lt_one (by norm_num) (by norm_num) ?_
    rw [hζ]
    nlinarith
  · -- Minkowski
    refine (lintegral_tsum_rpow_le_of_one_le hx hp1.le).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg hp0.le (ne_of_lt ?_))
    have hq : 0 < 1 / p := one_div_pos.2 hp0
    have hxn' : ∀ n, (∫⁻ ω, x n ω ^ p ∂P) ^ (1 / p) ≤ C₁ ^ (1 / p) *
        ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2) * ((2⁻¹ : ℝ) ^ (ζ / p - γ ^ 2)) ^ n) := by
      intro n
      refine (ENNReal.rpow_le_rpow (hxn n) hq.le).trans (le_of_eq ?_)
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
        ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (QuantumZipper.radius_pos _).le _) hq.le,
        mul_left_comm, ← ENNReal.ofReal_mul (hc0 n), ← Real.rpow_mul (QuantumZipper.radius_pos _).le,
        ← radius_rpow_mul_radius_rpow, mul_one_div]
    refine (ENNReal.tsum_le_tsum hxn').trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le hC₁.ne)
      (tsum_ofReal_mul_pow_lt_top (by positivity) ?_)
    refine Real.rpow_lt_one (by norm_num) (by norm_num) ?_
    rw [sub_pos, lt_div_iff₀ hp0, hζ]
    nlinarith

end MatedCRTHarmonic.GMCFacts
