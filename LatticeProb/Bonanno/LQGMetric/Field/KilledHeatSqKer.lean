/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSqKer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqOpen
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatCK
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen7
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen5
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen3
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KHSQ4, target `KilledHeatSq.killedHeat_sqOpen`)

* `integral_killedHeat_sqMode` (K): `∫ p_Q(t; z, w) φ_p(w) dw = e^{−λ_p t/2} φ_p(z)` for `z ∈ Q`,
  from optional stopping `integral_stayGrid_sqMode`, `stayGrid_ae_eq` and the density
  statement `lintegral_killedHeat_eq`.
* `integral_sqDirKernel_sqMode`: the same identity for the image-series kernel `p^D_Q`
  (termwise integration of `hasSum_sqDirKernel_sine`, orthogonality `integral_sqOpen_sqMode_mul`).
* `ae_killedHeat_eq` (C, a.e.): both kernels have the same sine coefficients, so by Parseval
  (`hasSum_sqCoef_parseval`) their difference integrates to `0` against every test function of
  `Q`, hence vanishes a.e. (mathlib `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
* **`killedHeat_sqOpen`** (pointwise): Chapman–Kolmogorov at `t/2 + t/2` for both kernels
  (`killedHeat_chapmanKolmogorov`, `integral_sqDirKernel_mul`).

Sources: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, §4.3 and Problem 2.8.8;
Feller II §X.5 (eigenfunction expansion of the killed kernel). The assembly is own elementary
work (DEVIATIONS entry KHSQ4-1 proposed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeatSq

open KilledHeat HeatSq

/-- **(K)** `∫ p_Q(t; z, w) φ_p(w) dw = e^{−λ_p t/2} φ_p(z)` for `z ∈ Q`, `t ≠ 0`. -/
theorem integral_killedHeat_sqMode {a L : ℝ} (hL : 0 < L) (p : ℕ × ℕ) {z : ℂ}
    (hz : z ∈ sqOpen a L) {t : ℝ≥0} (ht : t ≠ 0) :
    ∫ w, killedHeat (sqOpen a L) t z w * sqMode a L p w = sqDecay L t p * sqMode a L p z := by
  have hB := isPlanarBM_planarBM
  have hQo := isOpen_sqOpen a L
  set S := stayAll (sqOpen a L) planarBM z t with hS
  set g : Ω2 → ℂ := fun ω ↦ z + planarBM t ω with hg_def
  have hg : AEMeasurable g P2 := aemeasurable_const.add (aemeasurable_B hB t)
  have hSm : NullMeasurableSet S P2 := nullMeasurableSet_stayAll hB hQo z t
  set f : ℂ → ℝ≥0 := fun w ↦ (killedHeat (sqOpen a L) t z w).toNNReal with hf
  have hfm : Measurable f := (measurable_killedHeat_right hQo ht z).real_toNNReal
  have hmeas : volume.withDensity (fun w ↦ (f w : ℝ≥0∞)) = (P2.restrict S).map g := by
    ext E hE
    rw [withDensity_apply _ hE, Measure.map_apply₀ hg.restrict hE.nullMeasurableSet,
      Measure.restrict_apply₀' hSm]
    exact lintegral_killedHeat_eq hQo ht hB z hE
  have e1 : ∫ w, killedHeat (sqOpen a L) t z w * sqMode a L p w =
      ∫ w, sqMode a L p w ∂(volume.withDensity fun w ↦ (f w : ℝ≥0∞)) := by
    rw [integral_withDensity_eq_integral_smul hfm]
    refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (killedHeat_nonneg _ _ _ _)]
  rw [e1, hmeas, integral_map hg.restrict (continuous_sqMode a L p).aestronglyMeasurable,
    Measure.restrict_congr_set (stayGrid_ae_eq hB hz ht).symm,
    ← integral_indicator₀ (nullMeasurableSet_stayGrid hB (measurableSet_sqOpen a L) z t),
    ← integral_stayGrid_sqMode hB hL p hz t]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  by_cases hω : ω ∈ stayGrid (sqOpen a L) planarBM z t
  · simp [Set.indicator_of_mem hω, hg_def]
  · simp [Set.indicator_of_notMem hω]

/-- `∫_Q p^D_Q(s; z, y) φ_p(y) dy = e^{−λ_p s/2} φ_p(z)`. -/
theorem integral_sqDirKernel_sqMode {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (p : ℕ × ℕ) (z : ℂ) :
    ∫ y, (sqOpen a L).indicator (fun y ↦ sqDirKernel a L s z y) y * sqMode a L p y =
      sqDecay L s p * sqMode a L p z := by
  by_cases hp : p.1 = 0 ∨ p.2 = 0
  · have h0 : ∀ y, sqMode a L p y = 0 := by
      intro y; unfold sqMode sinMode; rcases hp with h | h <;> simp [h]
    simp [h0]
  push Not at hp
  have hQ := measurableSet_sqOpen a L
  set I : ℂ → ℝ := (sqOpen a L).indicator (fun _ ↦ (1 : ℝ)) with hI
  have hg : Integrable I :=
    (integrableOn_const (volume_sqOpen_ne_top a L)).integrable_indicator hQ
  have hIabs : ∀ y, |I y| ≤ 1 := fun y ↦ by
    by_cases hy : y ∈ sqOpen a L <;> simp [hI, hy]
  have h := hasSum_integral_of_le_mul
    (F := fun q y ↦ 4 / L ^ 2 * sqDecay L s q * (sqMode a L q z * sqMode a L q y) *
      (I y * sqMode a L p y))
    (G := fun y ↦ (sqOpen a L).indicator (fun y ↦ sqDirKernel a L s z y) y * sqMode a L p y)
    (g := I) (c := fun q ↦ 4 / L ^ 2 * sqDecay L s q)
    ((summable_sqDecay hs hL).mul_left _) hg (fun q ↦ ?_) (fun q y ↦ ?_) (fun y ↦ ?_)
  · have hval : ∀ q, ∫ y, 4 / L ^ 2 * sqDecay L s q * (sqMode a L q z * sqMode a L q y) *
        (I y * sqMode a L p y) = if q = p then sqDecay L s p * sqMode a L p z else 0 := by
      intro q
      have e : (fun y ↦ 4 / L ^ 2 * sqDecay L s q * (sqMode a L q z * sqMode a L q y) *
          (I y * sqMode a L p y)) = fun y ↦ (4 / L ^ 2 * sqDecay L s q * sqMode a L q z) *
          (sqOpen a L).indicator (fun y ↦ sqMode a L q y * sqMode a L p y) y := by
        funext y
        by_cases hy : y ∈ sqOpen a L <;> simp [hI, hy] <;> ring
      rw [e, integral_const_mul, integral_indicator hQ, integral_sqOpen_sqMode_mul hL hp.1 hp.2]
      split_ifs with hqp
      · subst hqp; field_simp; ring
      · rw [mul_zero]
    simp only [hval] at h
    exact h.unique (hasSum_ite_eq p _)
  · exact (Measurable.mul (measurable_const.mul (measurable_const.mul
      (continuous_sqMode a L q).measurable)) ((measurable_const.indicator hQ).mul
      (continuous_sqMode a L p).measurable)).aestronglyMeasurable
  · rw [abs_mul, abs_mul (I y)]
    calc _ ≤ 4 / L ^ 2 * sqDecay L s q * (|I y| * 1) :=
          mul_le_mul (abs_sqDirKernel_term_le a L s hL q z y)
            (mul_le_mul_of_nonneg_left (abs_sqMode_le _ _ _ _) (abs_nonneg _))
            (by positivity) (by have := sqDecay_pos L s q; positivity)
      _ = _ := by rw [mul_one]
  · have h1 := (hasSum_sqDirKernel_sine (a := a) hs hL z y).mul_right (I y * sqMode a L p y)
    have e : (sqOpen a L).indicator (fun y ↦ sqDirKernel a L s z y) y * sqMode a L p y =
        sqDirKernel a L s z y * (I y * sqMode a L p y) := by
      by_cases hy : y ∈ sqOpen a L
      · rw [hI, Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
      · rw [hI, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; ring
    rw [e]
    exact h1

lemma integrable_mul_sqMode {a L : ℝ} {ρ : ℂ → ℝ} (hρm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) (p : ℕ × ℕ) :
    Integrable fun z ↦ ρ z * sqMode a L p z :=
  integrable_of_bdd_sq (hρm.mul (continuous_sqMode a L p).measurable)
    (fun z ↦ by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_sqMode_le _ _ _ _)).trans (hC z))
    (fun z hz ↦ by rw [h0 z hz, zero_mul])

/-- **(C, a.e.)** `p_Q(t; z, ·) = 1_Q p^D_Q(t; z, ·)` a.e., for `z ∈ Q` and `t ≠ 0`. -/
theorem ae_killedHeat_eq {a L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z ∈ sqOpen a L) {t : ℝ≥0}
    (ht : t ≠ 0) : ∀ᵐ w, killedHeat (sqOpen a L) t z w =
      (sqOpen a L).indicator (fun w ↦ sqDirKernel a L t z w) w := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hQo := isOpen_sqOpen a L
  have hQ := measurableSet_sqOpen a L
  set D : ℂ → ℝ := (sqOpen a L).indicator (fun w ↦ sqDirKernel a L t z w) with hD
  set k : ℂ → ℝ := fun w ↦ killedHeat (sqOpen a L) t z w with hk
  have hkm : Measurable k := measurable_killedHeat_right hQo ht z
  have hDm : Measurable D := (measurable_sqDirKernel_right' ht' hL z).indicator hQ
  set C2 : ℝ := ∑' q, 4 / L ^ 2 * sqDecay L t q
  have hK : ∀ y, |sqDirKernel a L t z y| ≤ C2 := by
    intro y
    have hs := hasSum_sqDirKernel_sine (a := a) ht' hL z y
    have hc := ((summable_sqDecay ht' hL).mul_left (4 / L ^ 2)).hasSum
    rw [abs_le]
    exact ⟨hasSum_le (fun q ↦ neg_le_of_abs_le (abs_sqDirKernel_term_le a L t hL q z y)) hc.neg hs,
      hasSum_le (fun q ↦ (le_abs_self _).trans (abs_sqDirKernel_term_le a L t hL q z y)) hs hc⟩
  have hC2 : 0 ≤ C2 := (abs_nonneg _).trans (hK 0)
  have hkb : ∀ w, |k w| ≤ (2 * Real.pi * t)⁻¹ := fun w ↦ by
    rw [abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
    exact (killedHeat_le_heatKernel _ _ _ _).trans (heatKernel_le_inv _ ht'.le _ _)
  have hDb : ∀ w, |D w| ≤ C2 := fun w ↦ by
    by_cases hw : w ∈ sqOpen a L
    · rw [hD, Set.indicator_of_mem hw]; exact hK w
    · rw [hD, Set.indicator_of_notMem hw, abs_zero]; exact hC2
  have hk0 : ∀ w ∉ sqOpen a L, k w = 0 := fun w hw ↦
    killedHeat_eq_zero_of_not_mem_right hQo ht z hw
  have hD0 : ∀ w ∉ sqOpen a L, D w = 0 := fun w hw ↦ by rw [hD, Set.indicator_of_notMem hw]
  set h : ℂ → ℝ := fun w ↦ k w - D w with hh
  have hm : Measurable h := hkm.sub hDm
  have hbd : ∀ w, |h w| ≤ (2 * Real.pi * t)⁻¹ + C2 := fun w ↦
    (abs_sub _ _).trans (add_le_add (hkb w) (hDb w))
  have h0 : ∀ w ∉ sqOpen a L, h w = 0 := fun w hw ↦ by simp [hh, hk0 w hw, hD0 w hw]
  have hcoef : ∀ q, sqCoef a L h q = 0 := by
    intro q
    unfold sqCoef
    simp only [hh, sub_mul]
    rw [integral_sub (integrable_mul_sqMode hkm hkb hk0 q) (integrable_mul_sqMode hDm hDb hD0 q),
      hk, integral_killedHeat_sqMode hL q hz ht, hD, integral_sqDirKernel_sqMode ht' hL q z,
      sub_self]
  have hint : Integrable h := integrable_of_bdd_sq hm hbd h0
  have hae := hQo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hint.locallyIntegrable.locallyIntegrableOn _)
    (fun g hg hgc hgs ↦ by
      have hP := hasSum_sqCoef_parseval hL (f := g) ⟨hg, hgc, hgs⟩ hm hbd h0
      simp only [hcoef, mul_zero] at hP
      simpa [smul_eq_mul] using hP.unique hasSum_zero)
  filter_upwards [hae] with w hw
  by_cases hwQ : w ∈ sqOpen a L
  · exact sub_eq_zero.mp (hw hwQ)
  · exact (hk0 w hwQ).trans (hD0 w hwQ).symm

/-- **The killed heat kernel of the open square is the image-series Dirichlet kernel**:
`p_Q(t; z, w) = p^D_Q(t; z, w)` for `z, w ∈ Q = (a, a+L)²`, `t > 0`. -/
theorem killedHeat_sqOpen {a L : ℝ} (hL : 0 < L) (t : ℝ≥0) (ht : t ≠ 0) (z w : ℂ)
    (hz : z ∈ sqOpen a L) (hw : w ∈ sqOpen a L) :
    killedHeat (sqOpen a L) t z w = sqDirKernel a L t z w := by
  have hQo := isOpen_sqOpen a L
  have hQ := measurableSet_sqOpen a L
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ≥0, r = t / 2 := ⟨_, rfl⟩
  have hr : r ≠ 0 := by rw [hr_def]; exact div_ne_zero ht two_ne_zero
  have hr' : (0 : ℝ) < r := lt_of_le_of_ne (NNReal.coe_nonneg r) (Ne.symm (by exact_mod_cast hr))
  have htr : r + r = t := by rw [hr_def]; exact add_halves t
  have hCK := killedHeat_chapmanKolmogorov hQo hr hr z w
  rw [htr] at hCK
  rw [hCK]
  calc ∫ y, killedHeat (sqOpen a L) r z y * killedHeat (sqOpen a L) r y w
      = ∫ y, (sqOpen a L).indicator
          (fun y ↦ sqDirKernel a L r z y * sqDirKernel a L r y w) y := by
        refine integral_congr_ae ?_
        filter_upwards [ae_killedHeat_eq hL hz hr, ae_killedHeat_eq hL hw hr] with y hy1 hy2
        rw [killedHeat_symm hQo r y w, hy1, hy2]
        by_cases hy : y ∈ sqOpen a L
        · simp [Set.indicator_of_mem hy, sqDirKernel_symm hr' hL w y]
        · simp [Set.indicator_of_notMem hy]
    _ = ∫ y in sqOpen a L, sqDirKernel a L r z y * sqDirKernel a L r y w := integral_indicator hQ
    _ = sqDirKernel a L ((r : ℝ) + r) z w := integral_sqDirKernel_mul hr' hr' hL z w
    _ = sqDirKernel a L t z w := by rw [← NNReal.coe_add, htr]

end KilledHeatSq
end LQGMetric
