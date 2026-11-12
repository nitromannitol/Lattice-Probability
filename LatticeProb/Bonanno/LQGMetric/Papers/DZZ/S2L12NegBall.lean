/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L12NegBall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12NegCmp

/-!
# Scaled negative moments of ball masses, explicit constants (P2-NEGMOMU)

Copies of `Neg3.exists_lintegral_areaApprox_sqQ_rpow_le` (GMCMomentNeg3Sq.lean) and
`lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg` (GMCMomentNeg3Fin.lean) in which the bound
`C₀` on the Riemann sums `nM` is a hypothesis instead of an existential, so that the final bound
`E μ(B(x,ρ))^p ≤ (4^{-m})^p C₀` is explicit. Route: Berestycki–Powell arXiv:2404.16642, proof of
Theorem `T:negmom` (`GMCproperties.tex` l. 1719–1745, "by Fatou"), as in the library files.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset Topology
open scoped ENNReal NNReal

namespace LQGMetric

namespace DZZ

open DGMC DGMC.Neg3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- `Neg3.exists_lintegral_areaApprox_sqQ_rpow_le` with the bound `C₀` on `E nM^p` as input. -/
theorem negU_lintegral_areaApprox_sqQ_rpow_le (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ p : ℝ} (hp : p < 0) {K : Set ℂ} (hKU : K ⊆ openSquare) {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) {C₀ : ℝ}
    (hC₀ : ∀ (k j : ℕ) (v : ℂ), k ≤ j → (∀ i ∈ grid j, cpt j i + v ∈ unitSq) →
      ∫ ω, nM γ X z₀ m k j v ω ^ p ∂P ≤ C₀) (k : ℕ) :
    ∫⁻ ω, areaApprox γ (X ω) (m + k) (sqQ z₀ m) ^ p ∂P ≤
      ENNReal.ofReal ((radius m ^ 2) ^ p * C₀) := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  set a := radius m
  have ha : 0 < a := radius_pos m
  set j := k
  set r := radius (m + k)
  have hr : 0 < r := radius_pos _
  have hra : r ≤ a := by
    simp only [r, a, radius_add]
    exact mul_le_of_le_one_right ha.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hQm := measurableSet_sqQ z₀ m
  set F : Ω → ℂ → ℝ≥0∞ := fun ω z =>
    ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * sU X (m + k) z ω))
  have hFm : ∀ ω, Measurable (F ω) := fun ω => ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((((measurable_sU hX (m + k)).comp
      (measurable_id.prodMk measurable_const)).const_mul γ).exp))
  have hsubH : sqQ z₀ m ⊆ H := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := eq_of_mem_sqQ hz
    exact (hKU (hQ w (cell0_subset_unitSq hw) (mem_closedBall_self (by positivity)))).2.2.1
  have hA : ∀ ω, areaApprox γ (X ω) (m + k) (sqQ z₀ m) = ∫⁻ z in sqQ z₀ m, F ω z := fun ω => by
    rw [areaApprox, withDensity_apply _ hQm, Measure.restrict_restrict hQm,
      inter_eq_left.2 hsubH]
    rfl
  set W : ℂ → Ω → ℝ≥0∞ := fun t ω => ∑ i ∈ grid j,
    ENNReal.ofReal (a ^ 2 * (4 : ℝ)⁻¹ ^ j) * F ω (z₀ + a • cellMap j i t)
  have h2 : ∀ ω, ∫⁻ t in cell0, W t ω ≤ areaApprox γ (X ω) (m + k) (sqQ z₀ m) := fun ω =>
    (lintegral_W_le_sqQ (F ω) (hFm ω) z₀ m j).trans_eq (hA ω).symm
  have hWm : Measurable (fun q : ℂ × Ω => W q.1 q.2) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((((measurable_sU hX (m + k)).comp
        ((measurable_const.add (((measurable_cellMap j i).comp measurable_fst).const_smul a)).prodMk
          measurable_snd)).const_mul γ).exp)))
  -- the bound for a fixed offset
  have hpoint : ∀ t ∈ cell0, ∫⁻ ω, W t ω ^ p ∂P ≤ ENNReal.ofReal ((a ^ 2) ^ p * C₀) := by
    intro t ht
    set v := vOff j t
    have hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq := fun i hi => by
      rw [← cellMap_eq]
      exact cell0_subset_unitSq (cell_subset_cell0 hi ((cellMap_mem_cell_iff j i t).2 ht))
    have hB2 : ∀ i ∈ grid j, closedBall (z₀ + a • (cpt j i + v)) (2 * radius (m + k)) ⊆
        openSquare := fun i hi =>
      ((closedBall_subset_closedBall (by linarith)).trans (hQ _ (hv i hi))).trans hKU
    have hall : ∀ i ∈ grid j, ∀ᵐ ω ∂P, sU X (m + k) (z₀ + a • cellMap j i t) ω =
        X ω (foldedCircle (z₀ + a • (cpt j i + v)) r) := fun i hi => by
      rw [cellMap_eq]; exact avgReg_ae_eq hX (hB2 i hi)
    have hae : ∀ᵐ ω ∂P, W t ω = ENNReal.ofReal (a ^ 2 * nM γ X z₀ m k j v ω) := by
      filter_upwards [(Filter.eventually_all_finset (grid j)).2 hall] with ω hω
      simp only [W, F, nM]
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      refine sum_congr rfl fun i hi => ?_
      rw [hω i hi, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    have hint := integrable_nM_rpow hX hKU hQ γ hp.le k j hv
    have hpos : ∀ ω, 0 < nM γ X z₀ m k j v ω := fun ω =>
      Finset.sum_pos (fun _ _ => by positivity) (grid_nonempty j)
    calc ∫⁻ ω, W t ω ^ p ∂P
        = ∫⁻ ω, ENNReal.ofReal ((a ^ 2) ^ p * nM γ X z₀ m k j v ω ^ p) ∂P := by
          refine lintegral_congr_ae (hae.mono fun ω h => ?_)
          show W t ω ^ p = _
          rw [h, ENNReal.ofReal_rpow_of_pos (mul_pos (by positivity) (hpos ω)),
            Real.mul_rpow (by positivity) (hpos ω).le]
      _ = ENNReal.ofReal (∫ ω, (a ^ 2) ^ p * nM γ X z₀ m k j v ω ^ p ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (Eventually.of_forall fun ω => by
              have := Real.rpow_nonneg (hpos ω).le p
              positivity)).symm
      _ ≤ ENNReal.ofReal ((a ^ 2) ^ p * C₀) := by
          rw [integral_const_mul]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (hC₀ k j v le_rfl hv) (by positivity))
  calc ∫⁻ ω, areaApprox γ (X ω) (m + k) (sqQ z₀ m) ^ p ∂P
      ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω) ^ p ∂P :=
        lintegral_mono fun ω => ennrpow_anti hp.le (h2 ω)
    _ ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω ^ p) ∂P := lintegral_mono fun ω =>
        rpow_lintegral_le_of_neg (hWm.comp (measurable_id.prodMk measurable_const)).aemeasurable hp
    _ = ∫⁻ t in cell0, ∫⁻ ω, W t ω ^ p ∂P :=
        lintegral_lintegral_swap ((hWm.comp (measurable_snd.prodMk measurable_fst)).pow_const
          p).aemeasurable
    _ ≤ ∫⁻ (_t : ℂ) in cell0, ENNReal.ofReal ((a ^ 2) ^ p * C₀) :=
        setLIntegral_mono' measurableSet_cell0 hpoint
    _ = ENNReal.ofReal ((a ^ 2) ^ p * C₀) := by rw [setLIntegral_const, volume_cell0, mul_one]

/-- `lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg` at a given level `m` with
`4 · 2^{-m} ≤ ρ/2`, with the bound `C₀` on `E nM^p` for squares inside `B̄(x, ρ/2)` as input:
`E μ(B(x,ρ))^p ≤ (4^{-m})^p C₀`. -/
theorem negU_lintegral_ball_rpow_le (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hB : Metric.ball x ρ ⊆ openSquare) (hp : p < 0) {m : ℕ} (hma : 4 * radius m ≤ ρ / 2)
    {C₀ : ℝ} (hC₀ : ∀ z₀ : ℂ,
      (∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ closedBall x (ρ / 2)) →
      ∀ (k j : ℕ) (v : ℂ), k ≤ j → (∀ i ∈ grid j, cpt j i + v ∈ unitSq) →
        ∫ ω, nM γ X z₀ m k j v ω ^ p ∂P ≤ C₀) :
    ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ^ p ∂P ≤
      ENNReal.ofReal ((radius m ^ 2) ^ p * C₀) := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  -- the square
  set a := radius m
  have ha : 0 < a := radius_pos m
  set c : ℂ := ⟨1 / 2, 1 / 2⟩
  set z₀ : ℂ := x - a • c
  set K := closedBall x (ρ / 2)
  have hKU : K ⊆ openSquare := (closedBall_subset_ball (by linarith)).trans hB
  have hdist : ∀ w ∈ unitSq, ‖(z₀ + a • w) - x‖ ≤ a := fun w ⟨w1, w2, w3, w4⟩ => by
    have e : (z₀ + a • w) - x = a • (w - c) := by simp only [z₀, smul_sub]; abel
    rw [e, norm_smul, Real.norm_of_nonneg ha.le]
    refine mul_le_of_le_one_right ha.le ((Complex.norm_le_abs_re_add_abs_im _).trans ?_)
    simp only [Complex.sub_re, Complex.sub_im, c]
    have h1 : |w.re - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |w.im - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hQ : ∀ w ∈ unitSq, closedBall (z₀ + a • w) (2 * a) ⊆ K := fun w hw =>
    closedBall_subset_closedBall' (by rw [dist_eq_norm]; linarith [hdist w hw])
  have hCk := negU_lintegral_areaApprox_sqQ_rpow_le hX hp hKU hQ (hC₀ z₀ hQ)
  -- finiteness of the approximations on `K`
  obtain ⟨n, hn⟩ := exists_nat_ge (2 / ρ)
  set T := sqIn (1 / ((n : ℝ) + 2))
  have hKT : K ⊆ T := (ball_sub_sqIn hρ hB).trans fun z ⟨z1, z2, z3, z4⟩ => by
    have : 1 / ((n : ℝ) + 2) ≤ ρ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hρ] at hn
      nlinarith
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨k₁, hk₁⟩ := exists_radius_le (show 0 < 1 / ((n : ℝ) + 2) by positivity)
  have hfin : ∀ᵐ ω ∂P, ∀ k, k₁ ≤ k → areaApprox γ (X ω) k T < ⊤ := by
    rw [ae_all_iff]; intro k
    by_cases hk : k₁ ≤ k
    · filter_upwards [ae_areaApprox_sqIn_lt_top hX γ n k (by
        have := hk₁ k hk; have := radius_pos k; linarith)] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hk
  -- the pointwise bound
  set f := plat x ρ
  have hfc : Continuous f := continuous_plat x ρ
  have hfts : tsupport f ⊆ K := tsupport_plat hρ
  have hfcs : HasCompactSupport f := (isCompact_closedBall x (ρ / 2)).of_isClosed_subset
    (isClosed_tsupport _) hfts
  have hfK : ∀ z, z ∉ K → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport
    fun h => hz (hfts h)
  have hQf : ∀ z ∈ sqQ z₀ m, f z = 1 := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := eq_of_mem_sqQ hz
    exact plat_eq_one hρ ((hdist w (cell0_subset_unitSq hw)).trans (by linarith))
  set g : ℕ → Ω → ℝ≥0∞ := fun k ω => areaApprox γ (X ω) (m + k) (sqQ z₀ m) ^ p
  have hgm : ∀ k, Measurable (g k) := fun k =>
    ((Measure.measurable_coe (measurableSet_sqQ z₀ m)).comp
      ((measurable_areaApprox γ _).comp (measurable_field hX))).pow_const p
  have hpt : ∀ᵐ ω ∂P, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ^ p ≤
      liminf (fun k => g k ω) atTop := by
    filter_upwards [ae_isVagueLimitOn_qAreaMeasureOn_openSquare hX hγ hγ2, hfin] with ω hv hω
    set μ := qAreaMeasureOn γ (X ω) openSquare
    have hT := hv.2.2 f hfc hfcs (hfts.trans hKU)
    set L := ENNReal.ofReal (∫ z, f z ∂μ)
    have h1 : L ≤ μ (ball x ρ) := by
      refine (ofReal_integral_le_lintegral (μ := μ) (plat_nonneg x ρ)).trans ?_
      rw [← lintegral_indicator_one measurableSet_ball]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ ball x ρ
      · rw [indicator_of_mem hz, Pi.one_apply, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (plat_le_one x ρ z)
      · have : z ∉ K := fun h => hz (closedBall_subset_ball (by linarith) h)
        rw [show plat x ρ z = 0 from hfK z this, ENNReal.ofReal_zero]; exact zero_le
    have hlim : Tendsto (fun k => ENNReal.ofReal (∫ z, f z ∂(areaApprox γ (X ω) (m + k))) ^ p)
        atTop (𝓝 (L ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp ((ENNReal.continuous_ofReal.tendsto _).comp
        (hT.comp (tendsto_atTop_mono (fun k => Nat.le_add_left k m) tendsto_id)))
    have hle : ∀ᶠ k in atTop, ENNReal.ofReal (∫ z, f z ∂(areaApprox γ (X ω) (m + k))) ^ p ≤
        g k ω := by
      filter_upwards [eventually_ge_atTop k₁] with k hk
      refine ennrpow_anti hp.le ?_
      have hfinK : areaApprox γ (X ω) (m + k) K < ⊤ :=
        (measure_mono hKT).trans_lt (hω (m + k) (by omega))
      have hint : Integrable f (areaApprox γ (X ω) (m + k)) := by
        have hg : Integrable (K.indicator fun _ => (1 : ℝ)) (areaApprox γ (X ω) (m + k)) :=
          (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
            (integrableOn_const hfinK.ne)
        refine hg.mono' hfc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (plat_nonneg x ρ z)]
          exact plat_le_one x ρ z
        · rw [hfK z hz, indicator_of_notMem hz, norm_zero]
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (plat_nonneg x ρ)),
        ← lintegral_indicator_one (measurableSet_sqQ z₀ m)]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ sqQ z₀ m
      · rw [indicator_of_mem hz, Pi.one_apply, hQf z hz, ENNReal.ofReal_one]
      · rw [indicator_of_notMem hz]; exact zero_le
    calc μ (ball x ρ) ^ p ≤ L ^ p := ennrpow_anti hp.le h1
      _ = liminf (fun k => ENNReal.ofReal (∫ z, f z ∂(areaApprox γ (X ω) (m + k))) ^ p) atTop :=
          hlim.liminf_eq.symm
      _ ≤ liminf (fun k => g k ω) atTop := liminf_le_liminf hle
  calc ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ^ p ∂P
      ≤ ∫⁻ ω, liminf (fun k => g k ω) atTop ∂P := lintegral_mono_ae hpt
    _ ≤ liminf (fun k => ∫⁻ ω, g k ω ∂P) atTop := lintegral_liminf_le hgm
    _ ≤ ENNReal.ofReal ((a ^ 2) ^ p * C₀) := liminf_le_of_frequently_le' (Frequently.of_forall hCk)

end DZZ

end LQGMetric
