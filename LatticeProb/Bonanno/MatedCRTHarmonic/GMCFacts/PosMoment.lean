/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.PosMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.NegMoment

/-!
# Uniform positive moments of the recentred GMC approximations on small squares

For a whole-plane GFF circle-average process `H` (measurable coordinates), `0 < γ < 2` and `1 < q < 4/γ²`, there is a
constant `C` such that for every centre `z`, scale `ε > 0`, dyadic side `a = 2^{-m} ∈ (ε/8, ε/2]` and level `k`,

  `E[(ε^{-2} ∫_Q (2^{-(m+k)}/ε)^{γ²/2} e^{γ (h_{2^{-(m+k)}}(w) − h_ε(z))} dw)^q] ≤ C`

(`exists_lintegral_sq_rpow_le_pos`), the positive counterpart of `NegMoment.exists_lintegral_sq_rpow_le`: the moments of
GMC are finite below `4/γ²` (Kahane 1985; Rhodes–Vargas arXiv:1305.6221 Thm 2.11; Berestycki–Powell arXiv:2404.16642
Thm 3.23), here uniformly over the recentred, rescaled family. Route: Kahane's inequality (convex `x ↦ x^q`) against the
reference family (`NegMoment.integral_rM_rpow_le`), LQGMetric's `LogCorr.exists_uniform_moment`, the direct covering of
the square by the offset Riemann sums (`lintegral_sqQ_le_W`), Jensen (LQGMetric `DGMC.rpow_lintegral_le`) and Tonelli.
This is the moment input of [16] Lemma A.3 ("(A.6) By [RV14a, Theorem 2.11]").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter
open LQGMetric.DGMC LQGMetric.DGMC.Neg3
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-- The level-`j` dyadic cells cover `[0,1)²`. -/
lemma cell0_subset_iUnion_cell (j : ℕ) : cell0 ⊆ ⋃ i ∈ grid j, cell j i := by
  intro t ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine mem_iUnion₂.2 ⟨cellIdx j t, mem_grid.2 ⟨?_, ?_⟩, mem_cell_cellIdx j h1 h3⟩
  · rw [cellIdx, Nat.floor_lt (by positivity)]
    push_cast
    have : (0 : ℝ) < 2 ^ j := by positivity
    nlinarith
  · rw [cellIdx, Nat.floor_lt (by positivity)]
    push_cast
    have : (0 : ℝ) < 2 ^ j := by positivity
    nlinarith

/-- **The direct covering**: the square integral is at most the offset-averaged Riemann sums. -/
theorem lintegral_sqQ_le_W (F : ℂ → ℝ≥0∞) (hF : Measurable F) (z₀ : ℂ) (m j : ℕ) :
    ∫⁻ z in sqQ z₀ m, F z ≤ ∫⁻ t in cell0, ∑ i ∈ grid j,
      ENNReal.ofReal (QuantumZipper.radius m ^ 2 * (4 : ℝ)⁻¹ ^ j) *
        F (z₀ + QuantumZipper.radius m • cellMap j i t) := by
  set Hf : ℂ → ℝ≥0∞ := fun w => F (z₀ + QuantumZipper.radius m • w)
  have hH : Measurable Hf := hF.comp (by fun_prop)
  rw [lintegral_sqQ F hF z₀ m]
  have hm : ∀ i ∈ grid j, Measurable fun t => ENNReal.ofReal (QuantumZipper.radius m ^ 2 *
      (4 : ℝ)⁻¹ ^ j) * F (z₀ + QuantumZipper.radius m • cellMap j i t) := fun i _ =>
    (hH.comp (measurable_cellMap j i)).const_mul _
  rw [lintegral_finsetSum _ hm]
  calc ENNReal.ofReal (QuantumZipper.radius m ^ 2) * ∫⁻ w in cell0, Hf w
      ≤ ENNReal.ofReal (QuantumZipper.radius m ^ 2) * ∫⁻ z in ⋃ i ∈ grid j, cell j i, Hf z := by
        gcongr
        exact cell0_subset_iUnion_cell j
    _ = ∑ i ∈ grid j, ENNReal.ofReal (QuantumZipper.radius m ^ 2) * ∫⁻ z in cell j i, Hf z := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset (pairwiseDisjoint_cell j)
          (fun i _ => measurableSet_cell j i)]
    _ = ∑ i ∈ grid j, ∫⁻ t in cell0, ENNReal.ofReal (QuantumZipper.radius m ^ 2 *
          (4 : ℝ)⁻¹ ^ j) * F (z₀ + QuantumZipper.radius m • cellMap j i t) := by
        refine sum_congr rfl fun i _ => ?_
        rw [lintegral_cell Hf hH j i, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← lintegral_const_mul _ (f := fun t => Hf (cellMap j i t)) (hH.comp (measurable_cellMap j i))]

/-- **Uniform positive moments of the Riemann sums** (`1 < q < 4/γ²`). -/
theorem exists_uniform_pos_moment_rM (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ} (hγ : 0 < γ) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ, ∀ (z : ℂ) (ε : ℝ) (m k j : ℕ) (v : ℂ), 0 < ε → QuantumZipper.radius m ≤ ε / 2 →
      ε / 8 < QuantumZipper.radius m → k ≤ j → (∀ i ∈ grid j, cpt j i + v ∈ unitSq) →
        ∫ ω, rM γ H z ε m k j v ω ^ q ∂P ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (logCorr_refZ hH hHm γ).exists_uniform_moment (by positivity) hq1 hq
  refine ⟨Real.exp (q * (q - 1) * (3 * γ ^ 2 * Real.log 2) / 2) * C₀,
    fun z ε m k j v hε ha ha' hkj hv => ?_⟩
  refine (integral_rM_rpow_le hH z hε ha ha' (Or.inr hq1.le) k j hv).trans ?_
  gcongr
  exact hC₀ k j hkj

/-- `rM^q` is integrable for `q ≥ 1` (power mean inequality and Gaussian exponential moments). -/
lemma integrable_rM_rpow_pos (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (m k j : ℕ) (v : ℂ)
    {q : ℝ} (hq : 1 ≤ q) : Integrable (fun ω => rM γ H z ε m k j v ω ^ q) P := by
  have hP := hH.isProbabilityMeasure
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  set pt : ℕ × ℕ → ℂ := fun i => sqCorner z (QuantumZipper.radius m) +
    QuantumZipper.radius m • (cpt j i + v)
  set K := (r / ε) ^ (γ ^ 2 / 2)
  have hK : 0 < K := Real.rpow_pos_of_pos (div_pos hr hε) _
  -- each term is integrable
  have hterm : ∀ i, Integrable (fun ω => (K * Real.exp (γ * (H r (pt i) ω - H ε z ω))) ^ q) P := by
    intro i
    have hg : HasGaussianLaw (fun ω => γ * (H r (pt i) ω - H ε z ω)) P :=
      (isGaussianProcess_recentred hH γ hε z (fun _ : Unit => r) (fun _ => hr)
        (fun _ => pt i)).hasGaussianLaw_eval ()
    obtain ⟨h1, -⟩ := integral_exp_mul_of_hasGaussianLaw hg (integral_recentred hH γ hε hr z (pt i)) q
    refine (h1.const_mul (K ^ q)).congr (Eventually.of_forall fun ω => ?_)
    simp only
    rw [Real.mul_rpow hK.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  have hmeas := measurable_rM hHm γ z ε m k j v
  refine Integrable.mono' (integrable_finsetSum (grid j) fun i _ => (hterm i).const_mul ((4 : ℝ)⁻¹ ^ j))
    (hmeas.pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (rM_pos (H := H) γ z hε m k j v ω).le _)]
  have hw : ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j = 1 := by
    rw [sum_const, nsmul_eq_mul, card_grid_mul]
  have := Real.rpow_arith_mean_le_arith_mean_rpow (s := grid j) (fun _ => (4 : ℝ)⁻¹ ^ j)
    (fun i => K * Real.exp (γ * (H r (pt i) ω - H ε z ω))) (fun _ _ => by positivity) hw
    (fun i _ => by positivity) hq
  exact this

/-- **Uniform positive moments of the normalized approximation on the square of side `2^{-m}` centred at `z`**
(`1 < q < 4/γ²`). -/
theorem exists_lintegral_sq_rpow_le_pos (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ} (hγ : 0 < γ) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ε : ℝ) (m k : ℕ), 0 < ε → QuantumZipper.radius m ≤ ε / 2 →
      ε / 8 < QuantumZipper.radius m →
        ∫⁻ ω, (ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ (sqCorner z (QuantumZipper.radius m)) m,
          nDens γ H z ε (QuantumZipper.radius (m + k)) w ω) ^ q ∂P ≤ C := by
  have hP := hH.isProbabilityMeasure
  obtain ⟨C₀, hC₀⟩ := exists_uniform_pos_moment_rM hH hHm hγ hq1 hq
  set C₁ := max C₀ 0
  refine ⟨ENNReal.ofReal C₁, ENNReal.ofReal_lt_top, fun z ε m k hε ha ha' => ?_⟩
  set a := QuantumZipper.radius m with ha_def
  have hrm : 0 < a := QuantumZipper.radius_pos m
  set z₀ := sqCorner z a
  set j := k
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hjm : Measurable (fun q : ℂ × Ω => H r q.1 q.2) := measurable_uncurry_coord hH hHm hr
  set F : Ω → ℂ → ℝ≥0∞ := fun ω w => nDens γ H z ε r w ω
  have hFm : ∀ ω, Measurable (F ω) := fun ω => ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((((hjm.comp (measurable_id.prodMk measurable_const)).sub
      measurable_const).const_mul γ).exp))
  set W : ℂ → Ω → ℝ≥0∞ := fun t ω => ENNReal.ofReal (ε⁻¹ ^ 2) * ∑ i ∈ grid j,
    ENNReal.ofReal (a ^ 2 * (4 : ℝ)⁻¹ ^ j) * F ω (z₀ + a • cellMap j i t)
  have h2 : ∀ ω, ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ z₀ m, F ω w ≤ ∫⁻ t in cell0, W t ω :=
    fun ω => by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul_right (lintegral_sqQ_le_W (F ω) (hFm ω) z₀ m j) _
  have hWm : Measurable (fun q : ℂ × Ω => W q.1 q.2) := by
    have hterm : ∀ i, Measurable (fun q : ℂ × Ω => F q.2 (z₀ + a • cellMap j i q.1)) := fun i => by
      have hA : Measurable (fun q : ℂ × Ω => H r (z₀ + a • cellMap j i q.1) q.2) :=
        hjm.comp ((measurable_const.add (((measurable_cellMap j i).comp
          measurable_fst).const_smul a)).prodMk measurable_snd)
      have hB : Measurable (fun q : ℂ × Ω => H ε z q.2) := (hHm ε z).comp measurable_snd
      exact ENNReal.measurable_ofReal.comp (((hA.sub hB).const_mul γ).exp.const_mul _)
    exact (Finset.measurable_sum _ fun i _ => (hterm i).const_mul _).const_mul _
  have hWeq : ∀ t ω, W t ω = ENNReal.ofReal ((a / ε) ^ 2 * rM γ H z ε m k j (vOff j t) ω) := by
    intro t ω
    have e : (a / ε) ^ 2 * rM γ H z ε m k j (vOff j t) ω = ε⁻¹ ^ 2 * ∑ i ∈ grid j,
        (a ^ 2 * (4 : ℝ)⁻¹ ^ j) * ((r / ε) ^ (γ ^ 2 / 2) *
          Real.exp (γ * (H r (z₀ + a • cellMap j i t) ω - H ε z ω))) := by
      simp only [rM, Finset.mul_sum, cellMap_eq, z₀, a, r]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        have := Real.rpow_pos_of_pos (div_pos hr hε) (γ ^ 2 / 2)
        positivity)]
    simp only [W, F, nDens]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ENNReal.ofReal_mul (by positivity)).symm
  have hpoint : ∀ t ∈ cell0, ∫⁻ ω, W t ω ^ q ∂P ≤ ENNReal.ofReal C₁ := by
    intro t ht
    set v := vOff j t
    have hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq := fun i hi => by
      rw [← cellMap_eq]
      exact cell0_subset_unitSq (cell_subset_cell0 hi ((cellMap_mem_cell_iff j i t).2 ht))
    have hint := integrable_rM_rpow_pos hH hHm γ z hε m k j v hq1.le
    have hb : ∫ ω, rM γ H z ε m k j v ω ^ q ∂P ≤ C₀ := hC₀ z ε m k j v hε ha ha' le_rfl hv
    have hae0 : ((a / ε) ^ 2) ^ q ≤ 1 := by
      refine Real.rpow_le_one (by positivity) ?_ (by linarith)
      rw [div_pow, div_le_one (by positivity)]
      nlinarith
    calc ∫⁻ ω, W t ω ^ q ∂P
        = ∫⁻ ω, ENNReal.ofReal (((a / ε) ^ 2) ^ q * rM γ H z ε m k j v ω ^ q) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hWeq, ENNReal.ofReal_rpow_of_pos (mul_pos (by positivity)
            (rM_pos (H := H) γ z hε m k j v ω)), Real.mul_rpow (by positivity)
            (rM_pos (H := H) γ z hε m k j v ω).le]
      _ = ENNReal.ofReal (∫ ω, ((a / ε) ^ 2) ^ q * rM γ H z ε m k j v ω ^ q ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (Eventually.of_forall fun ω => by
              have := Real.rpow_nonneg (rM_pos (H := H) γ z hε m k j v ω).le q
              positivity)).symm
      _ ≤ ENNReal.ofReal C₁ := by
          rw [integral_const_mul]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ((a / ε) ^ 2) ^ q * ∫ ω, rM γ H z ε m k j v ω ^ q ∂P
              ≤ 1 * max C₀ 0 := mul_le_mul hae0 (hb.trans (le_max_left _ _))
                (integral_nonneg fun ω => Real.rpow_nonneg (rM_pos (H := H) γ z hε m k j v ω).le _)
                zero_le_one
            _ = C₁ := one_mul _
  calc ∫⁻ ω, (ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ z₀ m, F ω w) ^ q ∂P
      ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω) ^ q ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (h2 ω) (by linarith)
    _ ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω ^ q) ∂P :=
        lintegral_mono fun ω =>
          rpow_lintegral_le (hWm.comp (measurable_id.prodMk measurable_const)).aemeasurable hq1
    _ = ∫⁻ t in cell0, ∫⁻ ω, W t ω ^ q ∂P :=
        lintegral_lintegral_swap ((hWm.comp (measurable_snd.prodMk measurable_fst)).pow_const
          q).aemeasurable
    _ ≤ ∫⁻ (_t : ℂ) in cell0, ENNReal.ofReal C₁ :=
        setLIntegral_mono' measurableSet_cell0 hpoint
    _ = ENNReal.ofReal C₁ := by rw [setLIntegral_const, volume_cell0, mul_one]

end MatedCRTHarmonic.GMCFacts
