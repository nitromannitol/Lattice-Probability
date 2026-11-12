/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffCV at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffKolm
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Third
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyLogCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A continuous version of the heat-smoothed zero-boundary GFF on a square (DFGPS L2.8, (a1))

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:879–881) applies DDDF Theorem 1 (2)
(`Blueprint.DDDFThm1_2`) to `h̊ * p_{ε²/2}`, where `h̊` is the zero-boundary GFF on `(-1,2)²`.
`DDDFThm1_2` is stated for a continuous version `Y` of `x ↦ Xh (p_{δ/2}(x − ·) 1_D)`
(`Blueprint.heatBdd`). DDDF (DD:160) treats `p_{δ/2} * h` as a continuous function without
comment; we prove the existence of such a version (own standard argument, Kolmogorov):

* `map_sub_zbExt` : increments of `Xh` are centred Gaussians, variance `Q(ρ,ρ) − 2Q(ρ,σ) + Q(σ,σ)`;
* `zbVar_sq_le` : on a square `D = (a, a+L)²`, this variance is `Q(ρ−σ, ρ−σ) ≤ (2L²/π) 4C ∫|ρ−σ|`
  for `|ρ − σ| ≤ C` (spectral form `HeatSq.zeroGFFTestCov_sqOpen_spectral`, Green weights
  `≤ 8/π`, and the Bessel-type bound of `HeatSq.summable_sqCoef_sq`);
* `exists_heat_contVersion_sq` : Kolmogorov (`exists_contVersion_of_gaussIncr`), with the heat
  kernel's `L²` Lipschitz bound `HeatSq.integral_sq_heatKernel_sub_le'` (and `|u| ≤ u²/2ε + ε/2`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open QuantumZipper QuantumZipper.K3 HeatSq Blueprint

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the difference of two elements of `BddOn U` -/
def bddSub {U : Set ℂ} (ρ σ : BddOn U) : BddOn U :=
  ⟨fun z => ρ.1 z - σ.1 z, by
    obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
    obtain ⟨hm', ⟨C', hC'⟩, h0'⟩ := σ.2
    refine ⟨hm.sub hm', ⟨C + C', fun z => (abs_sub _ _).trans (add_le_add (hC z) (hC' z))⟩,
      fun z hz => by simp [h0 z hz, h0' z hz]⟩⟩

/-- **Gaussian increments** of the extended zero-boundary GFF. -/
theorem map_sub_zbExt [IsProbabilityMeasure P] {D : TopologicalSpace.Opens ℂ}
    {Xh : BddOn (D : Set ℂ) → Ω → ℝ} (hX : IsZBGFFProcessExt D Xh P) (ρ σ : BddOn (D : Set ℂ)) :
    P.map (fun ω => Xh ρ ω - Xh σ ω) = gaussianReal 0
      (zeroGFFTestCov D ρ.1 ρ.1 - 2 * zeroGFFTestCov D ρ.1 σ.1 +
        zeroGFFTestCov D σ.1 σ.1).toNNReal := by
  have hG := hX.gaussian.hasGaussianLaw_fun_sub (s := ρ) (t := σ)
  rw [hG.map_eq_gaussianReal]
  have h2 : ∀ τ, MemLp (Xh τ) 2 P := fun τ => (hX.gaussian.hasGaussianLaw_eval τ).memLp_two
  congr 1
  · rw [integral_sub ((h2 ρ).integrable one_le_two) ((h2 σ).integrable one_le_two),
      hX.centered, hX.centered, sub_zero]
  · rw [variance_fun_sub (h2 ρ) (h2 σ), ← covariance_self (hX.measurable ρ).aemeasurable,
      ← covariance_self (hX.measurable σ).aemeasurable, hX.covariance_eq, hX.covariance_eq,
      hX.covariance_eq]

lemma greenWeight_le (p : ℕ × ℕ) : greenWeight p ≤ 8 / π := by
  unfold greenWeight
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) with h | h
  · rw [← h, mul_zero, div_zero]; positivity
  · have h1 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos p.1 with h1 | h1
      · rcases Nat.eq_zero_or_pos p.2 with h2 | h2
        · simp [h1, h2] at h
        · have : (1 : ℝ) ≤ p.2 := by exact_mod_cast h2
          nlinarith [sq_nonneg (p.1 : ℝ)]
      · have : (1 : ℝ) ≤ p.1 := by exact_mod_cast h1
        nlinarith [sq_nonneg (p.2 : ℝ)]
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8) (by positivity : 0 < π * 1)
      (mul_le_mul_of_nonneg_left h1 pi_pos.le)
    simpa using this

/-- Bessel-type bound (from the proof of `HeatSq.summable_sqCoef_sq`). -/
lemma tsum_sqCoef_sq_le {a L : ℝ} (hL : 0 < L) {ρ : ℂ → ℝ} (hρm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) :
    ∑' p, 4 / L ^ 2 * sqCoef a L ρ p ^ 2 ≤ ∫ x, |ρ x| * (4 * C) := by
  have hρ := integrable_of_bdd_sq hρm hC h0
  set M := ∫ x, |ρ x| * (4 * C)
  have key : ∀ F : Finset (ℕ × ℕ), ∑ p ∈ F, 4 / L ^ 2 * sqCoef a L ρ p ^ 2 ≤ M := by
    intro F
    have hc : Continuous fun s : ℝ =>
        ∑ p ∈ F, 4 / L ^ 2 * sqDecay L s p * (sqCoef a L ρ p * sqCoef a L ρ p) := by
      unfold sqDecay modeDecay; fun_prop
    have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have e0 : (∑ p ∈ F, 4 / L ^ 2 * sqDecay L 0 p * (sqCoef a L ρ p * sqCoef a L ρ p)) =
        ∑ p ∈ F, 4 / L ^ 2 * sqCoef a L ρ p ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [sqDecay, modeDecay, mul_zero, zero_mul, Real.exp_zero]; ring
    rw [e0] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    refine (sum_le_hasSum F (fun p _ => ?_)
      (hasSum_integral_sqDirKernel (a := a) hs hL hρ hρ)).trans
      ((le_abs_self _).trans (abs_integral_integral_sqDirKernel_le hs hL hρ hC h0))
    have := sqDecay_pos L s p
    rw [← sq]; positivity
  exact Summable.tsum_le_of_sum_le
    ((summable_sqCoef_sq hL hρm hC h0).mul_left (4 / L ^ 2)) key

/-- **Variance bound on a square**: `Q(ρ,ρ) − 2Q(ρ,σ) + Q(σ,σ) ≤ (2L²/π) ∫ |ρ−σ| · 4C`. -/
theorem zbVar_sq_le {a L : ℝ} (hL : 0 < L) (ρ σ : BddOn (sqOpen a L)) {C : ℝ}
    (hC : ∀ z, |ρ.1 z - σ.1 z| ≤ C) :
    zeroGFFTestCov (sqOpens a L) ρ.1 ρ.1 - 2 * zeroGFFTestCov (sqOpens a L) ρ.1 σ.1 +
        zeroGFFTestCov (sqOpens a L) σ.1 σ.1 ≤
      2 * L ^ 2 / π * ∫ x, |ρ.1 x - σ.1 x| * (4 * C) := by
  set f := bddSub ρ σ
  have hρi := integrable_of_bdd_sq ρ.2.1 ρ.2.2.1.choose_spec ρ.2.2.2
  have hσi := integrable_of_bdd_sq σ.2.1 σ.2.2.1.choose_spec σ.2.2.2
  have hlin : ∀ p, sqCoef a L f.1 p = sqCoef a L ρ.1 p - sqCoef a L σ.1 p := fun p => by
    unfold sqCoef
    rw [← integral_sub]
    · congr 1; funext z; simp only [f, bddSub]; ring
    · exact hρi.mul_bdd (continuous_sqMode a L p).aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact abs_sqMode_le a L p z)
    · exact hσi.mul_bdd (continuous_sqMode a L p).aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact abs_sqMode_le a L p z)
  have h1 := zeroGFFTestCov_sqOpen_spectral hL ρ ρ
  have h2 := zeroGFFTestCov_sqOpen_spectral hL ρ σ
  have h3 := zeroGFFTestCov_sqOpen_spectral hL σ σ
  have hf : HasSum (fun p => greenWeight p * sqCoef a L f.1 p ^ 2)
      (zeroGFFTestCov (sqOpens a L) ρ.1 ρ.1 - 2 * zeroGFFTestCov (sqOpens a L) ρ.1 σ.1 +
        zeroGFFTestCov (sqOpens a L) σ.1 σ.1) := by
    refine ((h1.sub (h2.mul_left 2)).add h3).congr_fun fun p => ?_
    rw [hlin]; ring
  have hs := (summable_sqCoef_sq hL f.2.1 hC f.2.2.2).mul_left (8 / π)
  have hle := hasSum_le (fun p => mul_le_mul_of_nonneg_right (greenWeight_le p) (sq_nonneg _))
    hf hs.hasSum
  refine hle.trans ?_
  have hb := tsum_sqCoef_sq_le hL f.2.1 hC f.2.2.2
  rw [tsum_mul_left] at hb ⊢
  have e : (8 / π) * ∑' p, sqCoef a L f.1 p ^ 2 =
      2 * L ^ 2 / π * (4 / L ^ 2 * ∑' p, sqCoef a L f.1 p ^ 2) := by
    field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- the heat density `p_s(x − ·) 1_U` (`s > 0`, `U` measurable) -/
lemma heatBdd_val {U : Set ℂ} (hU : MeasurableSet U) {s : ℝ} (hs : 0 < s) (x : ℂ) :
    (heatBdd U s x).1 = U.indicator (fun w => heatKernel s x w) := by
  have hcond : Measurable (U.indicator fun w => heatKernel s x w) ∧
      (∃ C : ℝ, ∀ z, |U.indicator (fun w => heatKernel s x w) z| ≤ C) ∧
      ∀ z ∉ U, U.indicator (fun w => heatKernel s x w) z = 0 := by
    refine ⟨(continuous_heatKernel s x).measurable.indicator hU, ⟨(2 * π * s)⁻¹, fun z => ?_⟩,
      fun z hz => indicator_of_notMem hz _⟩
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz, abs_of_nonneg (heatKernel_nonneg s hs.le x z)]
      exact KilledHeat.heatKernel_le_inv s hs.le x z
    · rw [indicator_of_notMem hz, abs_zero]; positivity
  unfold heatBdd
  exact congrArg Subtype.val (dif_pos hcond)

lemma abs_indicator_heat_sub_le {U : Set ℂ} {s : ℝ} (hs : 0 < s) (x x' z : ℂ) :
    |U.indicator (fun w => heatKernel s x w) z - U.indicator (fun w => heatKernel s x' w) z| ≤
      (2 * π * s)⁻¹ := by
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz, indicator_of_mem hz, abs_sub_le_iff]
    have h1 := heatKernel_nonneg s hs.le x z
    have h2 := heatKernel_nonneg s hs.le x' z
    have h3 := KilledHeat.heatKernel_le_inv s hs.le x z
    have h4 := KilledHeat.heatKernel_le_inv s hs.le x' z
    constructor <;> linarith
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, sub_zero, abs_zero]; positivity

/-- `L¹` Lipschitz bound of the heat density on the square (from the `L²` bound
`HeatSq.integral_sq_heatKernel_sub_le'` and `|u| ≤ u²/(2ε) + ε/2`, `ε = |x − x'|`). -/
lemma integral_abs_heat_sub_le {a L s : ℝ} (hL : 0 < L) (hs : 0 < s) (x x' : ℂ) :
    ∫ z, |(sqOpen a L).indicator (fun w => heatKernel s x w) z -
        (sqOpen a L).indicator (fun w => heatKernel s x' w) z| ≤
      ‖x - x'‖ * ((16 * π * s ^ 2)⁻¹ + L ^ 2 / 2) := by
  rcases eq_or_ne x x' with rfl | hne
  · simp
  set ε := ‖x - x'‖ with hεdef
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set g : ℂ → ℝ := fun z => heatKernel s x z - heatKernel s x' z with hg
  have hgi : Integrable (fun z => g z ^ 2) := integrable_sq_heatKernel_sub hs x x'
  have hU := measurableSet_sqOpen a L
  have hci : IntegrableOn (fun _ : ℂ => ε / 2) (sqOpen a L) :=
    integrableOn_const (volume_sqOpen_ne_top a L)
  have hRi : Integrable ((sqOpen a L).indicator fun z => g z ^ 2 / (2 * ε) + ε / 2) :=
    ((hgi.div_const _).integrableOn.add hci).integrable_indicator hU
  calc _ ≤ ∫ z, (sqOpen a L).indicator (fun z => g z ^ 2 / (2 * ε) + ε / 2) z := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hRi
          (ae_of_all _ fun z => ?_)
        by_cases hz : z ∈ sqOpen a L
        · simp only [indicator_of_mem hz]
          show |g z| ≤ _
          rw [show g z ^ 2 / (2 * ε) + ε / 2 = (g z ^ 2 + ε ^ 2) / (2 * ε) by field_simp,
            le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (|g z| - ε), sq_abs (g z)]
        · simp [indicator_of_notMem hz]
    _ = ∫ z in sqOpen a L, (g z ^ 2 / (2 * ε) + ε / 2) := integral_indicator hU
    _ = (∫ z in sqOpen a L, g z ^ 2 / (2 * ε)) + ∫ z in sqOpen a L, ε / 2 :=
        integral_add (hgi.div_const _).integrableOn hci
    _ ≤ (∫ z, g z ^ 2) / (2 * ε) + L ^ 2 * (ε / 2) := by
        gcongr ?_ + ?_
        · rw [integral_div]
          exact div_le_div_of_nonneg_right
            (setIntegral_le_integral hgi (ae_of_all _ fun z => sq_nonneg _)) (by positivity)
        · rw [setIntegral_const, smul_eq_mul, Measure.real, volume_sqOpen a L hL.le,
            ENNReal.toReal_ofReal (by positivity)]
    _ ≤ (ε ^ 2 / (8 * π * s ^ 2)) / (2 * ε) + L ^ 2 * (ε / 2) := by
        gcongr; exact integral_sq_heatKernel_sub_le' hs x x'
    _ = ε * ((16 * π * s ^ 2)⁻¹ + L ^ 2 / 2) := by field_simp; ring

/-- **Continuous version, fixed time** `s > 0`. -/
theorem exists_heat_contVersion_sq_of_pos [IsProbabilityMeasure P] {a L : ℝ} (hL : 0 < L)
    {Xh : BddOn (sqOpens a L : Set ℂ) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens a L) Xh P)
    {s : ℝ} (hs : 0 < s) :
    ∃ Y : ℂ → Ω → ℝ, IsContVersion (fun x => Xh (heatBdd (sqOpens a L) s x)) Y P := by
  set C : ℝ := (2 * π * s)⁻¹
  set K : ℝ := (16 * π * s ^ 2)⁻¹ + L ^ 2 / 2
  refine exists_contVersion_of_gaussIncr (fun x => hX.measurable _)
    (c := 2 * L ^ 2 / π * (4 * C) * K) (by positivity) fun x x' => ?_
  refine ⟨_, map_sub_zbExt hX _ _, ?_⟩
  rw [Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  have hU : MeasurableSet (sqOpens a L : Set ℂ) := measurableSet_sqOpen a L
  have hb : ∀ z, |(heatBdd (sqOpens a L) s x).1 z - (heatBdd (sqOpens a L) s x').1 z| ≤ C :=
    fun z => by
      rw [heatBdd_val hU hs, heatBdd_val hU hs]
      exact abs_indicator_heat_sub_le hs x x' z
  refine (zbVar_sq_le hL _ _ hb).trans ?_
  rw [integral_mul_const]
  have hI : ∫ z, |(heatBdd (sqOpens a L) s x).1 z - (heatBdd (sqOpens a L) s x').1 z| ≤
      ‖x - x'‖ * K := by
    rw [heatBdd_val hU hs, heatBdd_val hU hs]
    exact integral_abs_heat_sub_le (a := a) hL hs x x'
  have h4C : 0 ≤ 4 * C := by positivity
  calc 2 * L ^ 2 / π * ((∫ z, |(heatBdd (sqOpens a L) s x).1 z -
        (heatBdd (sqOpens a L) s x').1 z|) * (4 * C))
      ≤ 2 * L ^ 2 / π * ((‖x - x'‖ * K) * (4 * C)) := by gcongr
    _ = 2 * L ^ 2 / π * (4 * C) * K * ‖x - x'‖ := by ring

/-- **Continuous version of the heat-smoothed zero-boundary GFF on a square** (the hypothesis
`IsContVersion` of `Blueprint.DDDFThm1_2`, for `D = (a, a+L)²`). -/
theorem exists_heat_contVersion_sq [IsProbabilityMeasure P] {a L : ℝ} (hL : 0 < L)
    {Xh : BddOn (sqOpens a L : Set ℂ) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens a L) Xh P) :
    ∃ Y : ℝ → ℂ → Ω → ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens a L) (δ / 2) x)) (Y δ) P := by
  have h : ∀ δ : ℝ, ∃ Y : ℂ → Ω → ℝ, 0 < δ →
      IsContVersion (fun x => Xh (heatBdd (sqOpens a L) (δ / 2) x)) Y P := fun δ => by
    by_cases hδ : 0 < δ
    · obtain ⟨Y, hY⟩ := exists_heat_contVersion_sq_of_pos hL hX (half_pos hδ)
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨0, fun h => absurd h hδ⟩
  choose Y hY using h
  exact ⟨Y, fun δ hδ => hY δ hδ.1⟩

end LQGMetric.DFGPS
