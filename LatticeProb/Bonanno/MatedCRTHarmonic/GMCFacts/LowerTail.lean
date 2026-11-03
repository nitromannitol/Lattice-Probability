/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.LowerTail at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.NegMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Version
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Fin

/-!
# [GHM15, Lemma 3.12]: the lower tail of the LQG mass of a ball

**Target** (`GMSLemma27.GMCLowerTail γ`, consumed by the proof of [18] Lemma 2.8): for `0 < γ < 2`, every whole-plane
GFF circle-average process `H` (`IsGFFCircleAverage`) with LQG measure `μ` (`IsLQGAreaOf`), every `s` and `c > 0` there
is `δ₀ > 0` with

  `P(μ(B_ε(z)) < δ ε^{2+γ²/2} e^{γ h_ε(z)}) ≤ c δ^s` for all `δ ∈ (0, δ₀)`, `z ∈ ℂ`, `ε ∈ (0, 1)`

([GHM15] = Gwynne–Holden–Miller, arXiv 1512.01223v5, Lemma 3.12).

**Proof** (`gmcLowerTail_holds`). The paper reduces by the coordinate change (3.15)–(3.16) to `P(μ_h(𝔻) < δ)` for a
normalized whole-plane GFF and bounds that by the Markov decomposition (3.17)–(3.19) and [DS11, Lemma 4.5]. We use the
same coordinate change in covariance form and all negative moments instead of [DS11, Lemma 4.5]:
1. **measurable version** (`Version.lean`): wlog every `H r z` is measurable;
2. **finite levels** (`measure_sq_small_le`): on the dyadic square `Q` of side `a = 2^{-m} ∈ (ε/8, ε/4]` centred at
   `z`, `μ_{2^{-(m+k)}}(Q) = ε^{2+γ²/2} e^{γ h_ε(z)} · S_k` with `S_k = ε^{-2} ∫_Q (r/ε)^{γ²/2} e^{γ(h_r − h_ε(z))}`,
   and `E[S_k^p] ≤ C` uniformly (`NegMoment.exists_lintegral_sq_rpow_le`), so Markov gives `P(S_k < δ) ≤ C δ^{−p}`;
3. **limit** (`measure_ball_small_le`): a plateau function `f` with `𝟙_Q ≤ f ≤ 𝟙_{B_ε(z)}` (LQGMetric's `plat`);
   on the a.s. event of vague convergence, `μ(B_ε(z)) < T` forces `∫ f dμ < T`, hence `μ_{2^{-(m+k)}}(Q) < T` for all
   large `k`; so the small-mass event lies a.s. in `⋃_N ⋂_{k ≥ N} {S_k < δ}`, of probability `≤ C δ^{−p}`;
4. choose `p = −(|s| + 1)` and `δ₀ = min(1, c/(C + 1))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter Topology
open LQGMetric.DGMC LQGMetric.DGMC.Neg3
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

lemma dyadicRadius_eq_radius (k : ℕ) : GMSLemma27.dyadicRadius k = QuantumZipper.radius k := by
  rw [GMSLemma27.dyadicRadius, QuantumZipper.radius, zpow_neg, zpow_natCast, inv_pow]

/-- A measure with a continuous real density is finite on compact sets. -/
lemma isFiniteMeasureOnCompacts_withDensity_ofReal {g : ℂ → ℝ} (hg : Continuous g) :
    IsFiniteMeasureOnCompacts ((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (g z)) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (g z) ≤ ∫⁻ _z in K, ENNReal.ofReal M :=
        setLIntegral_mono measurable_const fun z hz =>
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa using hM z hz))
    _ = ENNReal.ofReal M * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- The circle-average approximations of the LQG measure are locally finite. -/
lemma isLocallyFiniteMeasure_lqgApprox (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) (k : ℕ)
    (ω : Ω) : IsLocallyFiniteMeasure (GMSLemma27.lqgApprox γ H k ω) := by
  have hr : 0 < GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have := isFiniteMeasureOnCompacts_withDensity_ofReal
    (g := fun z => GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω))
    (continuous_const.mul ((hH.continuous _ hr ω).const_smul γ).rexp)
  exact inferInstanceAs (IsLocallyFiniteMeasure ((volume : Measure ℂ).withDensity _))

/-- A dyadic side `2^{-m} ∈ (ε/8, ε/4]` for `0 < ε ≤ 4`. -/
lemma exists_radius_mem {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 4) :
    ∃ m : ℕ, QuantumZipper.radius m ≤ ε / 4 ∧ ε / 8 < QuantumZipper.radius m := by
  classical
  have hex : ∃ m : ℕ, QuantumZipper.radius m ≤ ε / 4 := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    exact ⟨m, hm.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hs
  · rw [h0, show QuantumZipper.radius 0 = 1 by simp [QuantumZipper.radius]]
    linarith
  · have hmin := Nat.find_min hex (show (Nat.find hex).pred < Nat.find hex by omega)
    push Not at hmin
    rw [hs, show QuantumZipper.radius ((Nat.find hex).pred + 1) =
      QuantumZipper.radius (Nat.find hex).pred / 2 by
        simp only [QuantumZipper.radius, pow_succ]; ring]
    linarith

omit [MeasurableSpace Ω] in
/-- The approximation on the square factors as `ε^{2+γ²/2} e^{γ h_ε(z)}` times the normalized mass. -/
lemma lqgApprox_sq_eq (γ : ℝ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (m k : ℕ) (ω : Ω) :
    GMSLemma27.lqgApprox γ H (m + k) ω (sqQ (sqCorner z (QuantumZipper.radius m)) m) =
      ENNReal.ofReal (ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω)) *
        (ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ (sqCorner z (QuantumZipper.radius m)) m,
          nDens γ H z ε (QuantumZipper.radius (m + k)) w ω) := by
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  rw [GMSLemma27.lqgApprox, withDensity_apply _ (measurableSet_sqQ _ _), dyadicRadius_eq_radius,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  simp only [nDens]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_add hε, Real.div_rpow hr.le hε.le, Real.rpow_two]
  have h1 : Real.exp (γ * H r w ω) = Real.exp (γ * H ε z ω) * Real.exp (γ * (H r w ω - H ε z ω)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : (0 : ℝ) < ε ^ (γ ^ 2 / 2) := Real.rpow_pos_of_pos hε _
  rw [h1]
  field_simp
  rfl

/-- **Finite levels**: the normalized approximation on the square is small with probability `≤ C δ^{−p}`, uniformly
in `z`, `ε`, `m` (side in `(ε/8, ε/2]`) and `k`. -/
theorem measure_sq_small_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ε : ℝ) (m k : ℕ), 0 < ε → QuantumZipper.radius m ≤ ε / 2 →
      ε / 8 < QuantumZipper.radius m → ∀ δ : ℝ, 0 < δ →
        P {ω | GMSLemma27.lqgApprox γ H (m + k) ω (sqQ (sqCorner z (QuantumZipper.radius m)) m) <
          ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))} ≤
          C * ENNReal.ofReal (δ ^ (-p)) := by
  obtain ⟨C, hC, hbound⟩ := exists_lintegral_sq_rpow_le hH hHm hγ hγ2 hp
  refine ⟨C, hC, fun z ε m k hε ha ha' δ hδ => ?_⟩
  set Q := sqQ (sqCorner z (QuantumZipper.radius m)) m
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  set S : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in Q, nDens γ H z ε r w ω
  have hjm := measurable_uncurry_coord hH hHm hr
  have hSm : Measurable S := by
    refine Measurable.const_mul ?_ _
    have hd : Measurable (fun q : ℂ × Ω => nDens γ H z ε r q.1 q.2) :=
      ENNReal.measurable_ofReal.comp (((hjm.sub ((hHm ε z).comp measurable_snd)).const_mul
        γ).exp.const_mul _)
    exact hd.lintegral_prod_left'
  have hδpos : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have hδ' : ENNReal.ofReal δ ^ p ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h => absurd h hδpos.ne', fun h => absurd h ENNReal.ofReal_ne_top⟩
  have hδ'' : ENNReal.ofReal δ ^ p ≠ ⊤ := by
    rw [Ne, ENNReal.rpow_eq_top_iff]
    push Not
    exact ⟨fun h => absurd h hδpos.ne', fun h => absurd h ENNReal.ofReal_ne_top⟩
  have hsub : {ω | GMSLemma27.lqgApprox γ H (m + k) ω Q <
      ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))} ⊆
      {ω | ENNReal.ofReal δ ^ p ≤ S ω ^ p} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [lqgApprox_sq_eq γ z hε m k ω] at hω
    have hc : 0 < ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω) :=
      mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
    have e : ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω)) =
        ENNReal.ofReal (ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω)) * ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_mul hc.le]
      congr 1
      ring
    rw [e] at hω
    have hS : S ω < ENNReal.ofReal δ :=
      (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top).1 hω
    exact ennrpow_anti hp.le hS.le
  calc P {ω | GMSLemma27.lqgApprox γ H (m + k) ω Q <
        ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))}
      ≤ P {ω | ENNReal.ofReal δ ^ p ≤ S ω ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, S ω ^ p ∂P) / ENNReal.ofReal δ ^ p :=
        meas_ge_le_lintegral_div (hSm.pow_const p).aemeasurable hδ' hδ''
    _ ≤ C / ENNReal.ofReal δ ^ p := ENNReal.div_le_div_right (hbound z ε m k hε ha ha') _
    _ = C * ENNReal.ofReal (δ ^ (-p)) := by
        rw [div_eq_mul_inv, ← ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos hδ]

/-- For a locally finite measure `ν` and the plateau `f` (`0 ≤ f ≤ 1`, compact support): `ofReal (∫ f dν)` is the
lintegral of `ofReal ∘ f`. -/
lemma ofReal_integral_plat {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (∫ w, plat x ρ w ∂ν) = ∫⁻ w, ENNReal.ofReal (plat x ρ w) ∂ν := by
  have hcs : HasCompactSupport (plat x ρ) :=
    (isCompact_closedBall x (ρ / 2)).of_isClosed_subset (isClosed_tsupport _) (tsupport_plat hρ)
  exact ofReal_integral_eq_lintegral_ofReal ((continuous_plat x ρ).integrable_of_hasCompactSupport hcs)
    (Eventually.of_forall fun w => plat_nonneg x ρ w)

/-- **Limit**: the small-mass event of the LQG measure of `B_ε(z)` has probability `≤ C δ^{−p}`, uniformly in `z`,
`ε ∈ (0, 4]`, `δ > 0`. -/
theorem measure_ball_small_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0)
    {μ : Ω → Measure ℂ} (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ε : ℝ), 0 < ε → ε ≤ 4 → ∀ δ : ℝ, 0 < δ →
      P {ω | μ ω (ball z ε) < ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))} ≤
        C * ENNReal.ofReal (δ ^ (-p)) := by
  obtain ⟨C, hC, hfin⟩ := measure_sq_small_le hH hHm hγ hγ2 hp
  refine ⟨C, hC, fun z ε hε hε4 δ hδ => ?_⟩
  obtain ⟨m, ha, ha'⟩ := exists_radius_mem hε hε4
  set a := QuantumZipper.radius m with ha_def
  have hrm : 0 < a := QuantumZipper.radius_pos m
  set Q := sqQ (sqCorner z a) m
  have h4a : 0 < 4 * a := by positivity
  set f : ℂ → ℝ := plat z (4 * a)
  have hfc : Continuous f := continuous_plat _ _
  have hfs : HasCompactSupport f :=
    (isCompact_closedBall z (4 * a / 2)).of_isClosed_subset (isClosed_tsupport _) (tsupport_plat h4a)
  have hfQ : ∀ w ∈ Q, f w = 1 := fun w hw => by
    obtain ⟨y, hy, rfl⟩ := eq_of_mem_sqQ hw
    refine plat_eq_one h4a ?_
    have := norm_sqPoint_sub_le z hrm.le (cell0_subset_unitSq hy)
    linarith
  have hfB : ∀ w ∉ ball z ε, f w = 0 := fun w hw => by
    refine plat_eq_zero h4a ?_
    rw [mem_ball, dist_eq_norm, not_lt] at hw
    linarith
  -- `ν(Q) ≤ ofReal (∫ f dν) ≤ ν(B_ε(z))` for locally finite `ν`
  have hup : ∀ (ν : Measure ℂ) [IsLocallyFiniteMeasure ν],
      ENNReal.ofReal (∫ w, f w ∂ν) ≤ ν (ball z ε) := fun ν _ => by
    rw [ofReal_integral_plat z h4a, ← lintegral_indicator_one measurableSet_ball]
    refine lintegral_mono fun w => ?_
    by_cases hw : w ∈ ball z ε
    · rw [indicator_of_mem hw, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (plat_le_one _ _ _)
    · rw [show plat z (4 * a) w = 0 from hfB w hw, ENNReal.ofReal_zero]
      exact zero_le
  have hlow : ∀ (ν : Measure ℂ) [IsLocallyFiniteMeasure ν],
      ν Q ≤ ENNReal.ofReal (∫ w, f w ∂ν) := fun ν _ => by
    rw [ofReal_integral_plat z h4a, ← lintegral_indicator_one (measurableSet_sqQ _ _)]
    refine lintegral_mono fun w => ?_
    by_cases hw : w ∈ Q
    · rw [indicator_of_mem hw, Pi.one_apply]
      show 1 ≤ ENNReal.ofReal (f w)
      rw [hfQ w hw, ENNReal.ofReal_one]
    · rw [indicator_of_notMem hw]
      exact zero_le
  set A : ℕ → Set Ω := fun k => {ω | GMSLemma27.lqgApprox γ H (m + k) ω Q <
    ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))}
  set B : ℕ → Set Ω := fun N => ⋂ k, ⋂ (_ : N ≤ k), A k
  have hBmono : Monotone B := fun N N' hNN' ω hω => by
    simp only [B, mem_iInter] at hω ⊢
    exact fun k hk => hω k (hNN'.trans hk)
  -- the small-mass event lies a.s. in `⋃_N ⋂_{k ≥ N} A_k`
  have hsub : {ω | μ ω (ball z ε) <
      ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))} ≤ᵐ[P] ⋃ N, B N := by
    filter_upwards [hμ] with ω ⟨hlf, hconv⟩ hE
    have hE' : μ ω (ball z ε) < ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) *
        Real.exp (γ * H ε z ω)) := hE
    set T := δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω)
    have hT : 0 < T := mul_pos (mul_pos hδ (Real.rpow_pos_of_pos hε _)) (Real.exp_pos _)
    have h1 : ∫ w, f w ∂(μ ω) < T :=
      (ENNReal.ofReal_lt_ofReal_iff hT).1 ((hup (μ ω)).trans_lt hE')
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hconv f hfc hfs).eventually_lt_const h1)
    refine mem_iUnion.2 ⟨N, ?_⟩
    simp only [B, mem_iInter]
    intro k hk
    have := isLocallyFiniteMeasure_lqgApprox hH γ (m + k) ω
    exact (hlow _).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hT).2 (hN (m + k) (by omega)))
  calc P {ω | μ ω (ball z ε) <
        ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))}
      ≤ P (⋃ N, B N) := measure_mono_ae hsub
    _ = ⨆ N, P (B N) := hBmono.measure_iUnion
    _ ≤ C * ENNReal.ofReal (δ ^ (-p)) := iSup_le fun N =>
        (measure_mono (iInter₂_subset N le_rfl)).trans
          (hfin z ε m N hε (ha.trans (by linarith)) ha' δ hδ)

/-- **[GHM15, Lemma 3.12]** , in the form `GMCLowerTail`, for every
`γ ∈ (0, 2)`. -/
theorem gmcLowerTail_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : GMSLemma27.GMCLowerTail γ := by
  intro Ω _ P H μ hH hμ s c hc
  obtain ⟨H', hH', hH'm, hae⟩ := exists_measurable_version hH
  have hdr : ∀ k, 0 < GMSLemma27.dyadicRadius k := fun k => by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have happrox : ∀ᵐ ω ∂P, ∀ k, GMSLemma27.lqgApprox γ H' k ω = GMSLemma27.lqgApprox γ H k ω := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hae _ (hdr k)] with ω hω
    simp only [GMSLemma27.lqgApprox, hω]
  have hμ' : GMSLemma27.IsLQGAreaOf γ H' μ P := by
    filter_upwards [hμ, happrox] with ω h1 h2
    exact ⟨h1.1, fun f hf hfs => by simp only [h2]; exact h1.2 f hf hfs⟩
  set p : ℝ := -(|s| + 1) with hp_def
  have hp : p < 0 := by have := abs_nonneg s; linarith
  obtain ⟨C, hC, hbound⟩ := measure_ball_small_le hH' hH'm hγ hγ2 hp hμ'
  set K := C.toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  refine ⟨min 1 (c / (K + 1)), lt_min one_pos (by positivity), fun δ hδ z ε hε => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le (min_le_left _ _)
  have hδc : δ < c / (K + 1) := hδ.2.trans_le (min_le_right _ _)
  have hev : P {ω | μ ω (ball z ε) <
        ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))} =
      P {ω | μ ω (ball z ε) <
        ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H' ε z ω))} := by
    refine measure_congr ?_
    filter_upwards [hae ε hε.1] with ω hω
    rw [hω z]
  have hb := hbound z ε hε.1 (by linarith [hε.2]) δ hδ0
  rw [hev]
  have hCK : C = ENNReal.ofReal K := (ENNReal.ofReal_toReal hC.ne).symm
  rw [hCK, ← ENNReal.ofReal_mul hK] at hb
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hb).trans ?_
  have e : -p = |s| + 1 := by rw [hp_def, neg_neg]
  rw [e]
  have hs : 1 ≤ |s| - s + 1 := by linarith [le_abs_self s]
  calc K * δ ^ (|s| + 1) = K * δ ^ (|s| - s + 1) * δ ^ s := by
        rw [mul_assoc, ← Real.rpow_add hδ0]
        congr 2
        ring
    _ ≤ K * δ * δ ^ s := by
        gcongr
        calc δ ^ (|s| - s + 1) ≤ δ ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hs
          _ = δ := Real.rpow_one δ
    _ ≤ c * δ ^ s := by
        gcongr
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < K + 1)).1 hδc
        nlinarith

end MatedCRTHarmonic.GMCFacts
