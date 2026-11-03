/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg3Sq at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Cov
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Cmp

/-!
# Negative moments of `areaApprox` on a small square (P2-NEGMOM2, step 3)

`Neg3.exists_lintegral_areaApprox_sqQ_rpow_le`: for `0 < γ < 2`, `p < 0` and a square
`Q = z₀ + 2^{-m}[0,1)²` whose `2·2^{-m}`-neighbourhood lies in a compact convex `K ⊆ 𝕍`,
`sup_k E areaApprox_{m+k}(Q)^p < ∞`.

Route (mirror image of `uniform_moment_areaApprox_sqIn`, GMCMomentPos2Fin.lean): the reversed
covering `areaApprox_{m+k}(Q) ≥ ∫_{t ∈ [0,1)²} W_t` (`lintegral_W_le_sqQ`), Jensen for `x ↦ x^p`
(`rpow_lintegral_le_of_neg`), Tonelli, and for each offset `t`: `W_t = 4^{-m} nM` a.s.
(`avgReg_ae_eq`) with the uniform bound `exists_uniform_neg_moment_nM`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

namespace Neg3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

lemma integrable_nM_rpow (hX : IsZeroBoundaryGFFOn openSquare X P) {K : Set ℂ}
    (hKU : K ⊆ openSquare) {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) (γ : ℝ) {p : ℝ}
    (hp : p ≤ 0) (k j : ℕ) {v : ℂ} (hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq) :
    Integrable (fun ω => nM γ X z₀ m k j v ω ^ p) P := by
  set r := radius (m + k)
  have hr : 0 < r := radius_pos _
  have hi₀ : ((0 : ℕ), (0 : ℕ)) ∈ grid j := mem_grid.2 ⟨by positivity, by positivity⟩
  set pt := z₀ + radius m • (cpt j (0, 0) + v)
  have hB : closedBall pt r ⊆ openSquare := (closedBall_sub_of_hQ hQ (hv _ hi₀) k).trans hKU
  have hg := hX.gaussian.hasGaussianLaw_eval (admC hr hB)
  obtain ⟨h1, -⟩ := integral_exp_mul_of_hasGaussianLaw hg (integral_circle hX hr hB) (p * γ)
  have hmeas : Measurable (fun ω => nM γ X z₀ m k j v ω) :=
    Finset.measurable_sum _ fun i _ =>
      (((hX.measurable_coord _).const_mul γ).exp.const_mul _).const_mul _
  refine Integrable.mono' (h1.const_mul (((4 : ℝ)⁻¹ ^ j * r ^ (γ ^ 2 / 2)) ^ p))
    (hmeas.pow_const p).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have hle : (4 : ℝ)⁻¹ ^ j * (r ^ (γ ^ 2 / 2) * Real.exp (γ * X ω (foldedCircle pt r))) ≤
      nM γ X z₀ m k j v ω :=
    Finset.single_le_sum (f := fun i => (4 : ℝ)⁻¹ ^ j * (r ^ (γ ^ 2 / 2) *
      Real.exp (γ * X ω (foldedCircle (z₀ + radius m • (cpt j i + v)) r))))
      (fun _ _ => by positivity) hi₀
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans (by positivity) hle) _)]
  refine (Real.rpow_le_rpow_of_nonpos (by positivity) hle hp).trans (le_of_eq ?_)
  rw [← mul_assoc, Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2; change _ = p * γ * X ω (foldedCircle pt r); ring

/-- **uniform negative moments of `areaApprox` on the square** -/
theorem exists_lintegral_areaApprox_sqQ_rpow_le (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0) {K : Set ℂ} (hKU : K ⊆ openSquare)
    (hKc : Convex ℝ K) (hKk : IsCompact K) {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℕ,
      ∫⁻ ω, areaApprox γ (X ω) (m + k) (sqQ z₀ m) ^ p ∂P ≤ C := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  obtain ⟨C₀, hC₀⟩ := exists_uniform_neg_moment_nM hX hγ hγ2 hp hKU hKc hKk hQ
  set a := radius m
  have ha : 0 < a := radius_pos m
  refine ⟨ENNReal.ofReal ((a ^ 2) ^ p * C₀), ENNReal.ofReal_lt_top, fun k => ?_⟩
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

end Neg3

end DGMC

end LQGMetric
