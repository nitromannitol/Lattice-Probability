/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127A6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127A5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108R1
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGreen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N1: `Δ G_U(y, ·) = −2π δ_y` against test functions (packet P-127A)

* `integral_killedHeat_mul_sub_eq`: for open `U`, `g ∈ C_c^∞(U)` (`QuantumZipper.zeroSpace U`),
  `t > 0`: `∫ p_U(t; z, x) g(x) dx − g(z) = ½ ∫₀ᵗ ∫ p_U(u; z, x) Δg(x) dx du`
  (the killed heat equation in weak form; `HeatA.open_identity` and the density statement
  `KilledHeat.lintegral_killedHeat_eq`).
* **`killedGreen_lap`**: for bounded open `U`, `∫ G_U(y, x) Δg(x) dx = −2π g(y)` for every `y`,
  where `G_U = π ∫₀^∞ p_U` (`KilledHeat.killedGreen`): Fubini, `t → ∞` with `p_U(t) ≤ R²/(π t²)`
  (`KilledHeat.killedHeat_le_rpow`).

Source: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*,
arXiv:2404.16642: Definition 1.11 (`G^D_0 = ∫₀^∞ p^D_t dt`, txt l. 862–869), Proposition 1.18(3)
(`Δ G^D_0(x, ·) = −δ_x`, eq. (1.21), txt l. 1101–1114) and its heat-equation proof sketch
"`∂_t p^D_t = Δ p^D_t`, integrate in time, `p^D_∞ = 0`" (txt l. 1175–1186), which is the argument
formalized here. Normalization: BP's Brownian motion has generator `Δ`, ours `½Δ`
(`heatKernel s` has variance `s` per coordinate), so `killedGreen = π ∫ p_U = 2π G^D_0`
(BP Remark 1.12) and `Δ killedGreen(y, ·) = −2π δ_y`. The time derivative is replaced by Dynkin's
formula on dyadic grids (DEC-127 N1): the grid-time Markov argument of
`KilledHeatSq.integral_stayUpTo_sqMode` (KilledHeatSqStop/SqLim) with `HeatA.dynkin_past`
(planar copy of QZ `Dynkin.dynkin_additive`) in place of the sine modes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Laplacian Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat KilledHeatSq HeatA

/-- `E[φ(z + B_u); τ_U > u] = ∫ p_U(u; z, x) φ(x) dx` (from `lintegral_killedHeat_eq`). -/
lemma integral_stayAll_eq_killedHeat {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ}
    {P : Measure Ω} (hB : IsPlanarBM B P) {U : Set ℂ} (hU : IsOpen U) {u : ℝ≥0} (hu : u ≠ 0)
    (z : ℂ) {φ : ℂ → ℝ} (hφ : Continuous φ) :
    ∫ ω, (stayAll U B z u).indicator 1 ω * φ (z + B u ω) ∂P = ∫ x, killedHeat U u z x * φ x := by
  have := hB.gauss.isProbabilityMeasure
  set S := stayAll U B z u with hS
  set gf : Ω → ℂ := fun ω ↦ z + B u ω with hgf
  have hg : AEMeasurable gf P := aemeasurable_const.add (aemeasurable_B hB u)
  have hSm : NullMeasurableSet S P := nullMeasurableSet_stayAll hB hU z u
  set f : ℂ → ℝ≥0 := fun w ↦ (killedHeat U u z w).toNNReal with hf
  have hfm : Measurable f := (measurable_killedHeat_right hU hu z).real_toNNReal
  have hmeas : volume.withDensity (fun w ↦ (f w : ℝ≥0∞)) = (P.restrict S).map gf := by
    ext E hE
    rw [withDensity_apply _ hE, Measure.map_apply₀ hg.restrict hE.nullMeasurableSet,
      Measure.restrict_apply₀' hSm]
    exact lintegral_killedHeat_eq hU hu hB z hE
  have e1 : ∫ x, killedHeat U u z x * φ x =
      ∫ x, φ x ∂(volume.withDensity fun w ↦ (f w : ℝ≥0∞)) := by
    rw [integral_withDensity_eq_integral_smul hfm]
    refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (killedHeat_nonneg _ _ _ _)]
  rw [e1, hmeas, integral_map hg.restrict hφ.aestronglyMeasurable, ← integral_indicator₀ hSm]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  by_cases hω : ω ∈ S
  · simp [Set.indicator_of_mem hω, hgf]
  · simp [Set.indicator_of_notMem hω]

/-- **The killed heat equation tested against `g ∈ C_c^∞(U)`** (DEC-127 N1, finite time). -/
theorem integral_killedHeat_mul_sub_eq {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℝ}
    (hg : g ∈ QuantumZipper.zeroSpace U) (z : ℂ) {t : ℝ≥0} (ht : 0 < t) :
    (∫ x, killedHeat U t z x * g x) - g z =
      1 / 2 * ∫ u in (0 : ℝ)..t, ∫ x, killedHeat U u.toNNReal z x * Δ g x := by
  have hB := isPlanarBM_planarBM
  have hid := open_identity hB hU hg z ht
  have hgc : Continuous g := hg.1.continuous
  obtain ⟨C, hC, -, -, -, hL2⟩ := exists_bounds hg.1 hg.2.1
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hL2).continuous
  rw [integral_stayAll_eq_killedHeat hB hU ht.ne' z hgc] at hid
  rw [hid]
  congr 1
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu ↦ ?_)
  rw [Set.uIoc_of_le t.coe_nonneg] at hu
  exact integral_stayAll_eq_killedHeat hB hU (Real.toNNReal_pos.mpr hu.1).ne' z hΔc

lemma integrable_killedHeat_right {U : Set ℂ} (hU : IsOpen U) {s : ℝ} (hs : 0 < s) (y : ℂ) :
    Integrable (fun x ↦ killedHeat U s.toNNReal y x) := by
  refine ⟨(measurable_killedHeat_right hU (Real.toNNReal_pos.mpr hs).ne' y).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ killedHeat_nonneg _ _ _ _)]
  exact (lintegral_killedHeat_le_one hs y).trans_lt ENNReal.one_lt_top

lemma integral_killedHeat_le_one' {U : Set ℂ} (hU : IsOpen U) {s : ℝ} (hs : 0 < s) (y : ℂ) :
    ∫ x, killedHeat U s.toNNReal y x ≤ 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ killedHeat_nonneg _ _ _ _)
    (integrable_killedHeat_right hU hs y).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact lintegral_killedHeat_le_one hs y)

/-- **DEC-127 N1** (`Δ_x G_U(y, x) = −2π δ_y` against `C_c^∞(U)`; BP Prop. 1.18 for
`G_U = π ∫₀^∞ p_U`): for a bounded open `U` and `g ∈ C_c^∞(U)`,
`∫ G_U(y, x) Δg(x) dx = −2π g(y)` for every `y ∈ ℂ`. -/
theorem killedGreen_lap {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {g : ℂ → ℝ}
    (hg : g ∈ QuantumZipper.zeroSpace U) (y : ℂ) :
    ∫ x, killedGreen U y x * Δ g x = -(2 * Real.pi) * g y := by
  obtain ⟨R, hR0, hUR⟩ := hUb.subset_ball_lt 0 0
  obtain ⟨C, hC, -, -, h2, hL2⟩ := exists_bounds hg.1 hg.2.1
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hL2).continuous
  have hΔb := abs_lap_le h2
  have hΔcs : HasCompactSupport (Δ g) := QuantumZipper.K3.hasCompactSupport_laplacian_K3 hg.2.1
  have hΔi : Integrable (Δ g) := hΔc.integrable_of_hasCompactSupport hΔcs
  have hgi : Integrable g := hg.1.continuous.integrable_of_hasCompactSupport hg.2.1
  set M : ℝ := R ^ 2 / Real.pi with hM
  have hM0 : 0 ≤ M := by positivity
  set H : ℂ × ℝ → ℝ := fun p ↦ killedHeat U p.2.toNNReal y p.1 * Δ g p.1 with hH
  have hHm : Measurable H :=
    (measurable_killedHeat_comp hU measurable_snd measurable_const measurable_fst).mul
      (hΔc.measurable.comp measurable_fst)
  have hpb : ∀ s, 0 < s → ∀ x, killedHeat U s.toNNReal y x ≤ M * s ^ (-2 : ℝ) := fun s hs x ↦
    killedHeat_le_rpow hR0.le hUR hs y x
  have hsl : ∀ s, 0 < s → Integrable (fun x ↦ H (x, s)) := fun s hs ↦
    hΔi.bdd_mul (c := M * s ^ (-2 : ℝ))
      (measurable_killedHeat_right hU (Real.toNNReal_pos.mpr hs).ne' y).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]; exact hpb s hs x)
  have hnH : ∀ s x, ‖H (x, s)‖ = killedHeat U s.toNNReal y x * |Δ g x| := fun s x ↦ by
    simp only [hH, Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
  have b1 : ∀ s, 0 < s → ∫ x, ‖H (x, s)‖ ≤ 2 * C := fun s hs ↦ by
    calc ∫ x, ‖H (x, s)‖ ≤ ∫ x, 2 * C * killedHeat U s.toNNReal y x :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
            ((integrable_killedHeat_right hU hs y).const_mul _) (ae_of_all _ fun x ↦ by
              show ‖H (x, s)‖ ≤ 2 * C * killedHeat U s.toNNReal y x
              rw [hnH, mul_comm]
              exact mul_le_mul_of_nonneg_right (hΔb x) (killedHeat_nonneg _ _ _ _))
      _ = 2 * C * ∫ x, killedHeat U s.toNNReal y x := integral_const_mul _ _
      _ ≤ 2 * C * 1 := mul_le_mul_of_nonneg_left (integral_killedHeat_le_one' hU hs y)
            (by positivity)
      _ = 2 * C := mul_one _
  have b2 : ∀ s, 0 < s → ∫ x, ‖H (x, s)‖ ≤ M * (∫ x, |Δ g x|) * s ^ (-2 : ℝ) := fun s hs ↦ by
    calc ∫ x, ‖H (x, s)‖ ≤ ∫ x, M * s ^ (-2 : ℝ) * |Δ g x| :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
            (hΔi.abs.const_mul _) (ae_of_all _ fun x ↦ by
              show ‖H (x, s)‖ ≤ M * s ^ (-2 : ℝ) * |Δ g x|
              rw [hnH]
              exact mul_le_mul_of_nonneg_right (hpb s hs x) (abs_nonneg _))
      _ = M * (∫ x, |Δ g x|) * s ^ (-2 : ℝ) := by rw [integral_const_mul]; ring
  have hmeasN : AEStronglyMeasurable (fun s ↦ ∫ x, ‖H (x, s)‖) (volume.restrict (Ioi (0 : ℝ))) :=
    (hHm.norm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℂ))).aestronglyMeasurable
  have hint : Integrable (fun s ↦ ∫ x, ‖H (x, s)‖) (volume.restrict (Ioi (0 : ℝ))) := by
    have hnn : ∀ s, 0 ≤ ∫ x, ‖H (x, s)‖ := fun s ↦ integral_nonneg fun _ ↦ norm_nonneg _
    change IntegrableOn (fun s ↦ ∫ x, ‖H (x, s)‖) (Ioi (0 : ℝ)) volume
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_const (C := 2 * C) (by simp)).mono' (hmeasN.mono_set Ioc_subset_Ioi_self) ?_
      refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn s)]
      exact b1 s hs.1
    · refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
        (M * ∫ x, |Δ g x|)).mono' (hmeasN.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn s)]
      have := b2 s (zero_lt_one.trans hs)
      linarith
  have hHi : Integrable H ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_prod_iff' hHm.aestronglyMeasurable).mpr
      ⟨(ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ hsl s hs, hint⟩
  have eL : ∀ x, killedGreen U y x * Δ g x = Real.pi * ∫ s in Ioi (0 : ℝ), H (x, s) := fun x ↦ by
    simp only [killedGreen, hH]
    rw [integral_mul_const]
    ring
  rw [integral_congr_ae (ae_of_all _ eL), integral_const_mul,
    integral_integral_swap (f := fun x s ↦ H (x, s)) hHi]
  set F : ℝ → ℝ := fun s ↦ ∫ x, H (x, s) with hF
  have hFi : IntegrableOn F (Ioi 0) := hHi.integral_prod_right
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hFi hb
  have hval : ∀ n : ℕ, ∫ s in (0 : ℝ)..((n : ℝ) + 1), F s =
      2 * ((∫ x, killedHeat U ((n : ℝ) + 1).toNNReal y x * g x) - g y) := by
    intro n
    have := integral_killedHeat_mul_sub_eq hU hg y (t := ((n : ℝ) + 1).toNNReal)
      (Real.toNNReal_pos.mpr (by positivity))
    rw [Real.coe_toNNReal _ (by positivity)] at this
    rw [this]
    simp only [hF, hH]
    ring
  have hp0 : Tendsto (fun n : ℕ ↦ ∫ x, killedHeat U ((n : ℝ) + 1).toNNReal y x * g x) atTop
      (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ ↦ M * ((n : ℝ) + 1) ^ (-2 : ℝ) * ∫ x, |g x|) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp hb).const_mul M
      simpa using this.mul_const (∫ x, |g x|)
    refine squeeze_zero_norm (fun n ↦ ?_) hr
    have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ x, ‖killedHeat U ((n : ℝ) + 1).toNNReal y x * g x‖
        ≤ ∫ x, M * ((n : ℝ) + 1) ^ (-2 : ℝ) * |g x| :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) (hgi.abs.const_mul _)
            (ae_of_all _ fun x ↦ by
              show ‖killedHeat U ((n : ℝ) + 1).toNNReal y x * g x‖ ≤
                M * ((n : ℝ) + 1) ^ (-2 : ℝ) * |g x|
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
              exact mul_le_mul_of_nonneg_right (hpb _ hs x) (abs_nonneg _))
      _ = M * ((n : ℝ) + 1) ^ (-2 : ℝ) * ∫ x, |g x| := integral_const_mul _ _
  have h2lim : Tendsto (fun n : ℕ ↦ ∫ s in (0 : ℝ)..((n : ℝ) + 1), F s) atTop
      (𝓝 (2 * (0 - g y))) := by
    simp only [hval]
    exact (hp0.sub_const (g y)).const_mul 2
  have := tendsto_nhds_unique hlim h2lim
  rw [this]
  ring

end ZBM
end CONF
end LQGMetric
