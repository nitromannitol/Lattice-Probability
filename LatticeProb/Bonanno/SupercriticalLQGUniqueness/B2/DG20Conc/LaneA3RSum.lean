/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RSum at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RHit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RRate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundMeas

 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

attribute [local instance] Classical.propDecidable

universe u

theorem laneFineStar_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n) :
    laneFineStar Q W P K n ≤ mΩ := by
  unfold laneFineStar
  refine sup_le ?_ (iSup₂_le fun b _ => ?_)
  · exact (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW hKn).meas).comap_le
  · exact (measurable_pi_iff.mpr (T20B.blkKn_spec hW Q hKn b).2.1).comap_le

theorem laneCEventualHit_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K m : ℕ) (b : ℤ × ℤ)
    (h : ∀ j, MeasurableSet (laneCHits γ j n K m b)) :
    MeasurableSet (laneCEventualHit γ n K m b) := by
  have e : laneCEventualHit γ n K m b = ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), laneCHits γ j n K m b := by
    ext ω
    simp [laneCEventualHit]
  rw [e]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => h j

theorem laneA3HitWeight_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K : ℕ) (b : ℤ × ℤ)
    (h : ∀ j, MeasurableSet (laneCHits γ j n K (laneBCoarseIndex Q K) b)) :
    AEMeasurable (laneA3HitWeight P W hW Q ξ γ n K b) P := by
  have hL : Measurable (fun ω => rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1)) :=
    measurable_crossLenIn (rectAB 1 1).isCompact_toSet
      (isPsiVersion_psiMN hW (Nat.zero_le n)).cont (isPsiVersion_psiMN hW (Nat.zero_le n)).meas
  exact ((laneC_aemeasurable_psi_aroundDist P W hW Q ξ n K (laneBCoarseIndex Q K) b).div
    hL.aemeasurable).indicator (laneCEventualHit_measurableSet γ n K _ b h)

 

theorem laneA3R_around_le_of_good {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) (n K : ℕ)
    (b : ℤ × ℤ) {T : ℝ} (hT : 0 < T) (ω : Ω)
    (hlow : ω ∉ j1RoundCutLowerEvent ξ Q W P K n (laneBCoarseIndex Q K) T
      (lambdaN ξ W P (n - K)) b)
    (hup : ω ∉ j1RoundCutUpperEvent ξ Q W P hW K n (laneBCoarseIndex Q K) T
      (lambdaN ξ W P (n - K)) b) :
    laneA3Around P W hW Q ξ n K b ω ≤
      ENNReal.ofReal (T ^ 2) * laneA3Across P W Q ξ n K b ω := by
  set e := ENNReal.ofReal (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω))
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hetop : e ≠ ⊤ := ENNReal.ofReal_ne_top
  set x := (2 : ℝ)⁻¹ ^ K * lambdaN ξ W P (n - K)
  have hx : 0 ≤ x := mul_nonneg (by positivity) (lambdaN_pos hW (n - K)).le
  have h1 : e * laneA3Around P W hW Q ξ n K b ω ≤ ENNReal.ofReal (T * x) := not_lt.mp hup
  have h2 : ENNReal.ofReal (T⁻¹ * x) ≤ e * laneA3Across P W Q ξ n K b ω := not_lt.mp hlow
  have hsplit : ENNReal.ofReal (T * x) = ENNReal.ofReal (T ^ 2) * ENNReal.ofReal (T⁻¹ * x) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg T)]
    congr 1
    field_simp
  have h3 : e * laneA3Around P W hW Q ξ n K b ω ≤
      e * (ENNReal.ofReal (T ^ 2) * laneA3Across P W Q ξ n K b ω) := by
    calc e * laneA3Around P W hW Q ξ n K b ω ≤ ENNReal.ofReal (T * x) := h1
      _ = ENNReal.ofReal (T ^ 2) * ENNReal.ofReal (T⁻¹ * x) := hsplit
      _ ≤ ENNReal.ofReal (T ^ 2) * (e * laneA3Across P W Q ξ n K b ω) := mul_le_mul' le_rfl h2
      _ = e * (ENNReal.ofReal (T ^ 2) * laneA3Across P W Q ξ n K b ω) := by ring
  calc laneA3Around P W hW Q ξ n K b ω
      = (e⁻¹ * e) * laneA3Around P W hW Q ξ n K b ω := by
        rw [ENNReal.inv_mul_cancel he0 hetop, one_mul]
    _ = e⁻¹ * (e * laneA3Around P W hW Q ξ n K b ω) := by ring
    _ ≤ e⁻¹ * (e * (ENNReal.ofReal (T ^ 2) * laneA3Across P W Q ξ n K b ω)) :=
        mul_le_mul' le_rfl h3
    _ = ENNReal.ofReal (T ^ 2) * laneA3Across P W Q ξ n K b ω := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel he0 hetop, one_mul]

 
theorem laneA3R_weight_sum_le_of_good {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (hε : Q.ε₀ ≤ 1) (ξ : ℝ)
    (n K : ℕ) (hK : 8 ≤ K) (γ : ℕ → ℕ → Ω → ℝ → ℂ)
    (hγ : ∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j))
    {T : ℝ} (hT : 0 < T) (ω : Ω)
    (hgood : ∀ b ∈ laneSourceIdx Q K,
      ω ∉ j1RoundCutLowerEvent ξ Q W P K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)) b ∧
      ω ∉ j1RoundCutUpperEvent ξ Q W P hW K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)) b) :
    ∑ b ∈ laneSourceIdx Q K, laneA3HitWeight P W hW Q ξ γ n K b ω ≤
      ENNReal.ofReal (T ^ 2) *
        (((4 * 2 ^ laneBCoarseIndex Q K + 1) ^ 2 : ℕ) : ℝ≥0∞) := by
  set L := rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) with hLdef
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hL0 : L ≠ 0 := (rectLen_pos (ξ := ξ) (rectAB 1 1) (by simp [rectAB, MarkedRect.crossWidth])
    (hψ.cont ω)).ne'
  have hLtop : L ≠ ⊤ := rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) (hψ.cont ω)
  set N := (((4 * 2 ^ laneBCoarseIndex Q K + 1) ^ 2 : ℕ) : ℝ≥0∞)
  set c := ENNReal.ofReal (T ^ 2)
  set x : ℤ × ℤ → ℝ≥0∞ := fun b =>
    (laneCEventualHit γ n K (laneBCoarseIndex Q K) b).indicator (laneA3Across P W Q ξ n K b) ω
  have hb : ∀ b ∈ laneSourceIdx Q K, laneA3HitWeight P W hW Q ξ γ n K b ω ≤ c * L⁻¹ * x b := by
    intro b hbI
    unfold laneA3HitWeight
    simp only [x]
    by_cases hF : ω ∈ laneCEventualHit γ n K (laneBCoarseIndex Q K) b
    · rw [indicator_of_mem hF, indicator_of_mem hF, ENNReal.div_eq_inv_mul]
      have h := laneA3R_around_le_of_good hW Q ξ n K b hT ω (hgood b hbI).1 (hgood b hbI).2
      calc L⁻¹ * laneA3Around P W hW Q ξ n K b ω ≤ L⁻¹ * (c * laneA3Across P W Q ξ n K b ω) :=
            mul_le_mul' le_rfl h
        _ = c * L⁻¹ * laneA3Across P W Q ξ n K b ω := by ring
    · rw [indicator_of_notMem hF, indicator_of_notMem hF]
      simp
  have hsum := laneA3_across_sum_le Q hε ξ P W n K hK γ hγ ω
  calc ∑ b ∈ laneSourceIdx Q K, laneA3HitWeight P W hW Q ξ γ n K b ω
      ≤ ∑ b ∈ laneSourceIdx Q K, c * L⁻¹ * x b := Finset.sum_le_sum hb
    _ = c * L⁻¹ * ∑ b ∈ laneSourceIdx Q K, x b := (Finset.mul_sum _ _ _).symm
    _ ≤ c * L⁻¹ * ∑ b ∈ T20B.nearIdx K, x b :=
        mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset (laneSourceIdx_subset_nearIdx Q K))
    _ ≤ c * L⁻¹ * (N * L) := mul_le_mul' le_rfl hsum
    _ = c * N * (L⁻¹ * L) := by ring
    _ = c * N := by rw [ENNReal.inv_mul_cancel hL0 hLtop, mul_one]

 
theorem laneA3R_card_le (Q : PsiParams) (hε : Q.ε₀ ≤ 1 / 2) {K : ℕ} (hK : 2 ≤ K) :
    (((4 * 2 ^ laneBCoarseIndex Q K + 1) ^ 2 : ℕ) : ℝ) ≤ 81 * K := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hlo := (laneB_coarseIndex_radius Q K hK).1
  set m := laneBCoarseIndex Q K
  have h2m : (2 : ℝ) ^ ((m : ℝ) - 1) = (2 : ℝ) ^ m / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  rw [h2m] at hlo
  have hKe1 : (1 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ := Real.one_le_rpow hK1 Q.ε₀_pos.le
  have hbase : (4 * (2 : ℝ) ^ m + 1) ≤ 9 * (K : ℝ) ^ Q.ε₀ := by linarith
  have hsq : ((K : ℝ) ^ Q.ε₀) ^ 2 ≤ K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (K : ℝ) ^ (Q.ε₀ * ((2 : ℕ) : ℝ)) ≤ (K : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK1 (by push_cast; linarith)
      _ = K := Real.rpow_one _
  push_cast
  calc (4 * (2 : ℝ) ^ m + 1) ^ 2 ≤ (9 * (K : ℝ) ^ Q.ε₀) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hbase 2
    _ = 81 * ((K : ℝ) ^ Q.ε₀) ^ 2 := by ring
    _ ≤ 81 * K := by linarith

 
theorem laneA3_sum_condHit_L2_le.{v} :
  ∀ (Q : PsiParams), Q.ε₀ < 1 / 100 → ∀ (ξ : ℝ), 0 < ξ → ∀ p : ℝ,
  0 < p → p < 2⁻¹ → J1FixedPAt.{v} Q ξ p → ∀ C : ℝ, 0 ≤ C →
  ∃ A : ℝ, ∃ K₀ : ℕ, 0 < A ∧
    ∀ {Ω : Type v} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ),
      K₀ ≤ K → K ≤ n →
      LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
        Real.exp (C * Real.sqrt (K : ℝ)) →
    ∀ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) →
      (∀ j : ℕ, ∀ b : ℤ × ℤ,
        MeasurableSet (laneCHits γ j n K (laneBCoarseIndex Q K) b)) →
      (∫⁻ ω, (∑ b ∈ laneSourceIdx Q K,
          ∫⁻ x, laneA3HitWeight P W hW Q ξ γ n K b x
            ∂(condExpKernel P (laneFineStar Q W P K n) ω)) ^ (2 : ℝ) ∂P) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (A * (K : ℝ) * Real.exp ((K : ℝ) ^ (2 / 3 : ℝ))) := by
  intro Q hε ξ hξ p hp hp2 hJ C hC
  obtain ⟨C₀, c₀, KJ, hC₀, hc₀, hJr⟩ := j1FixedPAt_roundCut Q ξ p hJ C hC
  obtain ⟨KR, hKR1, hKR⟩ := laneA3R_tail_rate hC₀ hc₀ Q.ε₀_pos hε
  refine ⟨162, max 8 (max KJ KR), by norm_num, ?_⟩
  intro Ω _ _ P _ W hW n K hK hKn hH γ hγ hhits
  have hK8 : 8 ≤ K := (le_max_left _ _).trans hK
  have hKJ : KJ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hKR' : KR ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hε1 : Q.ε₀ ≤ 1 := by linarith
  set I := laneSourceIdx Q K
  set Ncard : ℕ := (4 * 2 ^ laneBCoarseIndex Q K + 1) ^ 2 with hNcard
  have hm := laneFineStar_le hW Q hKn
  set κ := condExpKernel P (laneFineStar Q W P K n)
  set Y : ℤ × ℤ → Ω → ℝ≥0∞ := fun b => laneA3HitWeight P W hW Q ξ γ n K b
  have hYae : ∀ b, AEMeasurable (Y b) P := fun b =>
    laneA3HitWeight_aemeasurable P W hW Q ξ γ n K b (fun j => hhits j b)
  set Yh : ℤ × ℤ → Ω → ℝ≥0∞ := fun b => (hYae b).mk (Y b)
  have hYhm : ∀ b, Measurable (Yh b) := fun b => (hYae b).measurable_mk
  have hYeq : ∀ b, Y b =ᵐ[P] Yh b := fun b => (hYae b).ae_eq_mk
  set Zh : Ω → ℝ≥0∞ := fun ω => ∑ b ∈ I, Yh b ω
  have hZhm : Measurable Zh := Finset.measurable_sum _ fun b _ => hYhm b
  set Z : Ω → ℝ≥0∞ := fun ω => ∑ b ∈ I, Y b ω
  have hZeq : Z =ᵐ[P] Zh := by
    filter_upwards [(Filter.eventually_all_finset I).2 fun b _ => hYeq b] with ω hω
    exact Finset.sum_congr rfl hω
  
  have hstep1 : ∀ᵐ ω ∂P, ∑ b ∈ I, ∫⁻ x, Y b x ∂(κ ω) = ∫⁻ x, Zh x ∂(κ ω) := by
    have hb : ∀ b ∈ I, ∀ᵐ ω ∂P, ∫⁻ x, Y b x ∂(κ ω) = ∫⁻ x, Yh b x ∂(κ ω) := by
      intro b _
      filter_upwards [laneC_conditional_lintegral_mono_ae P hm (hYeq b).le,
        laneC_conditional_lintegral_mono_ae P hm (hYeq b).symm.le] with ω h1 h2
      exact le_antisymm h1 h2
    filter_upwards [(Filter.eventually_all_finset I).2 hb] with ω hω
    rw [Finset.sum_congr rfl hω, lintegral_finset_sum I fun b _ => hYhm b]
  
  have hstep2 : ∫⁻ ω, (∑ b ∈ I, ∫⁻ x, Y b x ∂(κ ω)) ^ (2 : ℝ) ∂P ≤
      ∫⁻ x, Zh x ^ (2 : ℝ) ∂P := by
    calc ∫⁻ ω, (∑ b ∈ I, ∫⁻ x, Y b x ∂(κ ω)) ^ (2 : ℝ) ∂P
        = ∫⁻ ω, (∫⁻ x, Zh x ∂(κ ω)) ^ (2 : ℝ) ∂P :=
          lintegral_congr_ae (hstep1.mono fun ω h => by simp only [h])
      _ ≤ ∫⁻ x, Zh x ^ (2 : ℝ) ∂P := laneA3R_cond_sq_le P hm hZhm
  
  set x₀ := (K : ℝ) ^ (2 / 3 : ℝ) with hx₀
  have hx₀0 : 0 ≤ x₀ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hNpos : (0 : ℝ) < Ncard := by
    have : 0 < Ncard := by rw [hNcard]; positivity
    exact_mod_cast this
  have htail : ∀ t, x₀ < t →
      2 * Real.exp (2 * t) * (P {ω | ENNReal.ofReal (Ncard * Real.exp t) ≤ Zh ω}).toReal ≤
        Real.exp (-t) := by
    intro t ht
    obtain ⟨hrange, hrate⟩ := hKR K hKR' t ht
    set T := Real.exp (t / 4) with hT
    have hTpos : 0 < T := Real.exp_pos _
    have ht0 : 0 < t := lt_of_le_of_lt hx₀0 ht
    obtain ⟨hlowP, hupP⟩ := hJr P W hW K n hKJ hKn hH T hrange
    set Lo := {ω | ∃ b ∈ laneSourceIdx Q K, ω ∈ j1RoundCutLowerEvent ξ Q W P K n
      (laneBCoarseIndex Q K) T (lambdaN ξ W P (n - K)) b}
    set Up := {ω | ∃ b ∈ laneSourceIdx Q K, ω ∈ j1RoundCutUpperEvent ξ Q W P hW K n
      (laneBCoarseIndex Q K) T (lambdaN ξ W P (n - K)) b}
    have hsub : {ω | ENNReal.ofReal (Ncard * Real.exp t) ≤ Z ω} ⊆ Lo ∪ Up := by
      intro ω hω
      by_contra hnot
      simp only [mem_union, not_or, Lo, Up, mem_setOf_eq, not_exists, not_and] at hnot
      have hgood : ∀ b ∈ laneSourceIdx Q K,
          ω ∉ j1RoundCutLowerEvent ξ Q W P K n (laneBCoarseIndex Q K) T
            (lambdaN ξ W P (n - K)) b ∧
          ω ∉ j1RoundCutUpperEvent ξ Q W P hW K n (laneBCoarseIndex Q K) T
            (lambdaN ξ W P (n - K)) b := fun b hb => ⟨hnot.1 b hb, hnot.2 b hb⟩
      have hle := laneA3R_weight_sum_le_of_good hW Q hε1 ξ n K hK8 γ hγ hTpos ω hgood
      have hT2 : T ^ 2 = Real.exp (t / 2) := by
        rw [hT, ← Real.exp_nat_mul]; congr 1; ring
      have hlt : ENNReal.ofReal (T ^ 2) * (Ncard : ℝ≥0∞) <
          ENNReal.ofReal (Ncard * Real.exp t) := by
        rw [show (Ncard : ℝ≥0∞) = ENNReal.ofReal (Ncard : ℝ) by simp,
          ← ENNReal.ofReal_mul (sq_nonneg T)]
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        rw [hT2, mul_comm]
        apply mul_lt_mul_of_pos_left _ hNpos
        exact Real.exp_lt_exp.mpr (by linarith)
      exact absurd (hω.trans hle) (not_le.mpr hlt)
    have hPle : P {ω | ENNReal.ofReal (Ncard * Real.exp t) ≤ Zh ω} ≤
        ENNReal.ofReal (C₀ * (5 : ℝ) ^ K * Real.exp
            (-c₀ * (Real.log T) ^ 2 / (K : ℝ) ^ (3 * Q.ε₀))) +
          ENNReal.ofReal (C₀ * (5 : ℝ) ^ K * Real.exp
            (-c₀ * (Real.log T) ^ 2 / ((K : ℝ) ^ (3 * Q.ε₀) * Real.log (Real.log T)))) := by
      calc P {ω | ENNReal.ofReal (Ncard * Real.exp t) ≤ Zh ω}
          ≤ P {ω | ENNReal.ofReal (Ncard * Real.exp t) ≤ Z ω} :=
            measure_mono_ae (hZeq.mono fun ω h hs => by
              simp only [mem_setOf_eq] at hs ⊢; rw [h]; exact hs)
        _ ≤ P (Lo ∪ Up) := measure_mono hsub
        _ ≤ P Lo + P Up := measure_union_le _ _
        _ ≤ _ := add_le_add hlowP hupP
    have hlogT : Real.log T = t / 4 := Real.log_exp _
    rw [hlogT] at hPle
    have hreal := ENNReal.toReal_mono (by finiteness) hPle
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hreal
    calc 2 * Real.exp (2 * t) * (P {ω | ENNReal.ofReal (Ncard * Real.exp t) ≤ Zh ω}).toReal
        ≤ 2 * Real.exp (2 * t) *
          (C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 / (K : ℝ) ^ (3 * Q.ε₀)) +
            C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 /
              ((K : ℝ) ^ (3 * Q.ε₀) * Real.log (t / 4)))) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ ≤ Real.exp (-t) := hrate
  have hstep3 := laneA3R_sq_lintegral_le_of_tail hZhm hNpos hx₀0 htail
  
  have hcard := laneA3R_card_le Q (by linarith) (show 2 ≤ K by omega)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hfinal : (Ncard : ℝ) ^ 2 * (Real.exp (2 * x₀) + 1) ≤
      (162 * (K : ℝ) * Real.exp x₀) ^ 2 := by
    have he : 1 ≤ Real.exp (2 * x₀) := Real.one_le_exp (by positivity)
    have hex : Real.exp (2 * x₀) = Real.exp x₀ ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hN2 : (Ncard : ℝ) ^ 2 ≤ (81 * K) ^ 2 := pow_le_pow_left₀ hNpos.le hcard 2
    calc (Ncard : ℝ) ^ 2 * (Real.exp (2 * x₀) + 1) ≤ (81 * K) ^ 2 * (2 * Real.exp (2 * x₀)) :=
          mul_le_mul hN2 (by linarith) (by positivity) (by positivity)
      _ ≤ (162 * (K : ℝ) * Real.exp x₀) ^ 2 := by
          rw [hex]; nlinarith [sq_nonneg ((K : ℝ) * Real.exp x₀)]
  calc (∫⁻ ω, (∑ b ∈ I, ∫⁻ x, Y b x ∂(κ ω)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((Ncard : ℝ) ^ 2 * (Real.exp (2 * x₀) + 1))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hstep2.trans hstep3) (by norm_num)
    _ ≤ (ENNReal.ofReal ((162 * (K : ℝ) * Real.exp x₀) ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hfinal) (by norm_num)
    _ = ENNReal.ofReal (162 * (K : ℝ) * Real.exp x₀) := by
        rw [ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end SupercriticalLQGUniqueness.B2.DG20Conc
