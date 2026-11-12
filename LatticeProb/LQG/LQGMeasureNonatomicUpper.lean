import LatticeProb.LQG.LQGMeasureNonatomic
import LatticeProb.LQG.LQGBallMassUpperDyadic
import LatticeProb.LQG.LQGMassFatou
import LatticeProb.LQG.GMCRatioLimitMeasure
import LatticeProb.LQG.LQGMeasureExistenceProved

/-!
# Non-atomicity of the LQG measure from the upper tail of ball masses

The γ-LQG area measure `μ_h` of `h = h^ℂ - α₀ log|·|`, for a whole-plane Gaussian free field `h^ℂ`, `0 < γ < 2` and
`α₀ < Q_γ`, almost surely has no atoms (Duplantier-Sheffield 2011; Rhodes-Vargas, arXiv:1305.6221, Section 2).

The argument needs only the upper tail of the masses of small balls, which follows from the positive moments
`E[μ(B(0,1/4))^p] < ∞` for `p < 4/γ²` (`ballMassPosMoment_of_lt`, `ballMassUpperTail_of_posMoment`):
* in the unit square, with polynomially high probability every ball of radius `ε^β` centred there has mass at most
  `ε` (`polyHighProb_ballMass_upper`), so by Borel-Cantelli along `ε = 2^{-k}` no point of the square is an atom;
* the translates `h^ℂ(· + b) - h^ℂ_1(b)`, `b ∈ ℤ + iℤ`, are whole-plane GFFs whose LQG measures are constant multiples of
  the translates of `μ_h` (`wholePlaneGFFAffineInvariance_lp`, `isLQGMeasureOfField_affine`), so no point of the plane
  is an atom when `α₀ = 0`;
* for general `α₀`, off the origin `μ_h` is absolutely continuous with respect to the measure at `α₀ = 0`
  (`singularWeightStep_lp`), and the origin is not an atom (`ae_origin_nonatomic_of_stronger_existence`).

The lower tail of ball masses (negative moments) is not used.
-/

universe u

namespace LatticeProb.LQG.LQGMeasureNonatomicUpper

open MeasureTheory Metric Filter Set LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped ENNReal

/-- A random measure on `ℂ` with the single-ball upper tail of the γ-LQG measure has, almost surely, no atom in the
closed unit square. -/
theorem ae_singleton_eq_zero_of_ballMassUpperTail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {μ : Ω → Measure ℂ} (hup : BallMassUpperTail P γ μ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ ω {z} = 0 := by
  have hβu : 2 / (2 - γ) ^ 2 < 2 / (2 - γ) ^ 2 + 1 := lt_add_one _
  filter_upwards [polyHighProb_ae_eventually_dyadic (polyHighProb_ballMass_upper hup hγ2 hβu)]
    with ω hω z hz
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k)) atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hle : ∀ᶠ k : ℕ in atTop, μ ω {z} ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) := by
    filter_upwards [hω] with k hk
    have hr : (0 : ℝ) < ((2 : ℝ)⁻¹ ^ k) ^ (2 / (2 - γ) ^ 2 + 1) := by positivity
    exact (measure_mono (singleton_subset_iff.2 (mem_ball_self hr))).trans (hk z hz)
  exact le_antisymm (ge_of_tendsto ht hle) zero_le

/-- The candidate LQG measure of the translated field `h^ℂ(· + b) - h^ℂ_1(b)` charges `{z - b}` with the mass of `{z}`
times a positive factor. -/
theorem affineMeasure_one_singleton {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ)
    (b z : ℂ) (ω : Ω) :
    affineMeasure γ hcirc μ₀ 1 b ω {z - b} =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ‖(1 : ℂ)‖ b + lqgQ γ * Real.log ‖(1 : ℂ)‖)))) * μ₀ ω {z} := by
  have hm : Measurable fun x : ℂ => (x - b) / 1 := (measurable_id.sub_const b).div_const 1
  simp only [affineMeasure, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply hm (measurableSet_singleton _)]
  congr 2
  ext x
  simp

/-- **No atoms at `α₀ = 0`.** For a whole-plane GFF and `0 < γ < 2`, the γ-LQG measure of `h^ℂ` almost surely has no
atom. -/
theorem ae_singleton_eq_zero_of_isWholePlaneGFF {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ₀ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, μ₀ ω {z} = 0 := by
  have hPos : BallMassPosMoment.{u} γ (2 / γ) := by
    refine ballMassPosMoment_of_lt hγ.ne' ?_ ?_
    · rw [le_div_iff₀ hγ]; linarith
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hγ]; nlinarith
  have hCC : LQGMeasureCoordChangeLP P γ 0 hC hcirc := lqgMeasureCoordChangeLP_zero P γ hC hcirc
  have key : ∀ b : ℤ × ℤ, ∀ᵐ ω ∂P, ∀ w ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      affineMeasure γ hcirc μ₀ 1 ((b.1 : ℂ) + (b.2 : ℂ) * Complex.I) ω {w} = 0 := by
    intro b
    have hGb := AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG 1 one_ne_zero
      ((b.1 : ℂ) + (b.2 : ℂ) * Complex.I)
    have hMb := isLQGMeasureOfField_affine hCC hG hγ hγ2 hμ₀ one_ne_zero ((b.1 : ℂ) + (b.2 : ℂ) * Complex.I)
    have hMb' : IsLQGMeasure P γ (affineCircle hcirc 1 ((b.1 : ℂ) + (b.2 : ℂ) * Complex.I))
        (affineMeasure γ hcirc μ₀ 1 ((b.1 : ℂ) + (b.2 : ℂ) * Complex.I)) := by
      simpa only [IsLQGMeasureOfField, fieldCircleAverage_zero_lp] using hMb
    exact ae_singleton_eq_zero_of_ballMassUpperTail
      (ballMassUpperTail_of_posMoment hγ hγ2 hGb hMb' hPos) hγ2
  filter_upwards [ae_all_iff.2 key] with ω hω z
  have h1 : (z - (((⌊z.re⌋ : ℤ) : ℂ) + ((⌊z.im⌋ : ℤ) : ℂ) * Complex.I)).re = Int.fract z.re := by
    simp
  have h2 : (z - (((⌊z.re⌋ : ℤ) : ℂ) + ((⌊z.im⌋ : ℤ) : ℂ) * Complex.I)).im = Int.fract z.im := by
    simp
  have hw : z - (((⌊z.re⌋ : ℤ) : ℂ) + ((⌊z.im⌋ : ℤ) : ℂ) * Complex.I) ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    rw [Complex.mem_reProdIm, h1, h2]
    exact ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
  have h := hω (⌊z.re⌋, ⌊z.im⌋) _ hw
  rw [affineMeasure_one_singleton] at h
  exact (mul_eq_zero.1 h).resolve_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

/-- **The γ-LQG measure is non-atomic**, for every insertion `α₀`: for a whole-plane GFF, `0 < γ < 2` and `α₀ < Q_γ`,
almost surely the γ-LQG measure of `h^ℂ - α₀ log|·|` has no atom (Duplantier-Sheffield 2011, Rhodes-Vargas
arXiv:1305.6221). -/
theorem lqgMeasureNonatomicLP_holds {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : LQGMeasureNonatomicLP P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hα μ hμ
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistenceLP_proved P γ 0 hC hcirc hG hγ hγ2 hQ
  let β : ℝ := (α₀ + lqgQ γ) / 2
  have hαβ : α₀ < β := by dsimp [β]; linarith
  have hβ : β < lqgQ γ := by dsimp [β]; linarith
  filter_upwards [LQGMeasureNonatomicOrigin.ae_origin_nonatomic_of_stronger_existence P γ α₀ β hγ hγ2 hαβ hβ
      hC hcirc (lqgMeasureExistenceLP_proved P γ β hC hcirc) μ hG hμ,
    singularWeightStep_lp γ α₀ hγ hγ2 hα Ω P hC hcirc μ μ₀ hG hμ hμ₀,
    ae_singleton_eq_zero_of_isWholePlaneGFF hγ hγ2 hG hμ₀] with ω h0 hweight hno z
  by_cases hz : z = 0
  · simpa [hz] using h0
  have heq := congrArg (fun ν : Measure ℂ => ν {z}) hweight
  rw [Measure.restrict_apply (measurableSet_singleton z),
    Measure.restrict_apply (measurableSet_singleton z)] at heq
  have hs : ({z} : Set ℂ) ∩ ({0} : Set ℂ)ᶜ = {z} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, by simpa [hx] using hz⟩
  rw [hs] at heq
  rw [heq]
  exact (withDensity_absolutelyContinuous (μ₀ ω) _) (hno z)

end LatticeProb.LQG.LQGMeasureNonatomicUpper
