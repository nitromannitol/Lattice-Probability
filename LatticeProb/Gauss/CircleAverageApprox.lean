import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.Gauss.CameronMartinDerived

/-! # Circle-density approximants of the whole-plane GFF circle averages

Adapted from the Section 8 circle-density chain of Bou-Rabee and Gwynne in the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]: smooth annular bumps `circleDensity`, their local, radial and logarithmic-potential estimates. The definitions are transcribed from that formalization (namespace `LatticeProb.Gauss`); the test-function combination lemma is adapted from its basic test-function lemmas; the integrability lemmas come from `LatticeProb.Gauss.CameronMartinDerived`. The joint centred circle version of the local circle-density statement is not transcribed (it is not used by the approximant chain).
-/

-- ===== Circle density

/-! # Smooth annular approximations

Smooth radial bumps around a circle have positive, translation-invariant mass.
-/

open MeasureTheory Set Metric
open scoped ContDiff

namespace LatticeProb.Gauss
theorem IsTestFunction.const_mul_add_const_mul {U : Set ℂ} {χ φ : ℂ → ℝ} (hχ : IsTestFunction U χ)
    (hφ : IsTestFunction U φ) (c s : ℝ) : IsTestFunction U (fun x => c * χ x + s * φ x) := by
  obtain ⟨hχd, hχc, hχU⟩ := hχ
  obtain ⟨hφd, hφc, hφU⟩ := hφ
  have hK : IsCompact (tsupport χ ∪ tsupport φ) := hχc.union hφc
  have hsub : Function.support (fun x => c * χ x + s * φ x) ⊆ tsupport χ ∪ tsupport φ := by
    intro x hx
    by_contra hx'
    rw [mem_union, not_or] at hx'
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'.1, image_eq_zero_of_notMem_tsupport hx'.2])
  refine ⟨(hχd.const_smul c |>.add (hφd.const_smul s)), ?_, ?_⟩
  · exact HasCompactSupport.intro hK fun x hx => by
      by_contra h
      exact hx (hsub (Function.mem_support.2 h))
  · exact (closure_minimal hsub (isClosed_tsupport χ |>.union (isClosed_tsupport φ))).trans
      (union_subset hχU hφU)


/-- A smooth bump in squared radius, supported in an annulus around the circle. -/
noncomputable def circleRadiusBump (r δ : ℝ) (hδ : 0 < δ) : ContDiffBump (r ^ 2) where
  rIn := δ / 2
  rOut := δ
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- The annular bump centered at `z`. -/
noncomputable def circleDensity (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) : ℝ :=
  circleRadiusBump r δ hδ (‖x - z‖ ^ 2)

/-- The annular density is smooth, including on the diagonal. -/
theorem circleDensity_contDiff (r δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    ContDiff ℝ ∞ (circleDensity r δ hδ z) := by
  exact (circleRadiusBump r δ hδ).contDiff.comp
    ((contDiff_id.sub contDiff_const).norm_sq ℝ)

/-- The support lies in the prescribed squared-radius annulus. -/
theorem circleDensity_support (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ)
    (hx : x ∈ Function.support (circleDensity r δ hδ z)) :
    |‖x - z‖ ^ 2 - r ^ 2| < δ := by
  have h : ‖x - z‖ ^ 2 ∈ ball (r ^ 2) δ := by
    have hm : ‖x - z‖ ^ 2 ∈ Function.support (circleRadiusBump r δ hδ) := hx
    rw [(circleRadiusBump r δ hδ).support_eq] at hm
    exact hm
  simpa [mem_ball, Real.dist_eq] using h

/-- Every such density has compact support. -/
theorem circleDensity_hasCompactSupport {r : ℝ} (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) : HasCompactSupport (circleDensity r δ hδ z) := by
  have hsub : tsupport (circleDensity r δ hδ z) ⊆ closedBall z (r + δ + 1) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have h := circleDensity_support r δ hδ z x hx
    have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
    rw [abs_lt] at h
    rw [mem_closedBall, dist_eq_norm]
    nlinarith [sq_nonneg (‖x - z‖ - (r + δ + 1)), sq_nonneg δ]
  exact (isCompact_closedBall z (r + δ + 1)).of_isClosed_subset (isClosed_tsupport _) hsub

/-- The support of a narrow bump lies within `η` of the circle in radius. -/
theorem circleDensity_support_radius {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z x : ℂ)
    (hx : x ∈ Function.support (circleDensity r δ hδ z)) :
    |‖x - z‖ - r| < η := by
  have h := circleDensity_support r δ hδ z x hx
  have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
  rw [abs_lt] at h ⊢
  constructor
  · by_contra hc
    have hf : 0 ≤ (r - ‖x - z‖ - η) * (r + ‖x - z‖) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ η by nlinarith) hn]
  · by_contra hc
    have hf : 0 ≤ (‖x - z‖ - r - η) * (r + ‖x - z‖) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ η by nlinarith) hn]

/-- A sufficiently narrow squared-radius bump is supported in an enlarged disk. -/
theorem circleDensity_tsupport_subset_closedBall {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z : ℂ) :
    tsupport (circleDensity r δ hδ z) ⊆ closedBall z (r + η) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have h := circleDensity_support r δ hδ z x hx
  have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
  rw [abs_lt] at h
  rw [mem_closedBall, dist_eq_norm]
  nlinarith [sq_nonneg (‖x - z‖ - r)]

/-- A narrow density is a test function whenever the enlarged disk is local. -/
theorem circleDensity_isTestFunction {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    (z : ℂ) (U : Set ℂ) (hU : closedBall z (r + η) ⊆ U) :
    IsTestFunction U (circleDensity r δ hδ z) :=
  ⟨circleDensity_contDiff r δ hδ z, circleDensity_hasCompactSupport hr.le hδ z,
    (circleDensity_tsupport_subset_closedBall hr hδ hwidth z).trans hU⟩

/-- The density is nonnegative and equals one at each point of its circle. -/
theorem circleDensity_nonneg (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) :
    0 ≤ circleDensity r δ hδ z x := (circleRadiusBump r δ hδ).nonneg

theorem circleDensity_eq_one {r : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (z x : ℂ) (hx : dist x z = r) : circleDensity r δ hδ z x = 1 := by
  apply (circleRadiusBump r δ hδ).one_of_mem_closedBall
  simp [mem_closedBall, ← dist_eq_norm, hx, circleRadiusBump]
  positivity

/-- The mass of an annular density is strictly positive. -/
theorem circleDensity_integral_pos {r : ℝ} (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) : 0 < ∫ x, circleDensity r δ hδ z x := by
  apply (circleDensity_contDiff r δ hδ z).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (circleDensity_hasCompactSupport hr hδ z) (circleDensity_nonneg r δ hδ z)
    (x := z + (r : ℂ))
  rw [circleDensity_eq_one hδ z _]
  · norm_num
  · simp [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Translating the center does not change the mass. -/
theorem circleDensity_integral_eq (r δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    (∫ x, circleDensity r δ hδ z x) = ∫ x, circleDensity r δ hδ 0 x := by
  simpa [circleDensity] using
    (integral_sub_right_eq_self (fun x : ℂ => circleRadiusBump r δ hδ (‖x‖ ^ 2)) z)

/-- Dividing by the common positive mass gives a probability density. -/
theorem circleDensity_normalized_integral {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z : ℂ) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x) = 1 := by
  rw [integral_const_mul, circleDensity_integral_eq r δ hδ z,
    inv_mul_cancel₀ (ne_of_gt (circleDensity_integral_pos hr hδ 0))]

/-- The difference of normalized annular densities is a local zero-integral
 test function. The two circles need a common local buffer. -/
theorem circleDensity_normalized_difference_test {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z : ℂ) (U : Set ℂ)
    (hz : closedBall z (r + η) ⊆ U) (h0 : closedBall 0 (r + η) ⊆ U) :
    let m := ∫ x, circleDensity r δ hδ 0 x
    let φ := fun x => m⁻¹ * circleDensity r δ hδ z x - m⁻¹ * circleDensity r δ hδ 0 x
    IsTestFunction U φ ∧ ∫ x, φ x = 0 := by
  dsimp only
  let m := ∫ x, circleDensity r δ hδ 0 x
  have hztest := circleDensity_isTestFunction hr hδ hwidth z U hz
  have h0test := circleDensity_isTestFunction hr hδ hwidth 0 U h0
  constructor
  · simpa only [sub_eq_add_neg, neg_mul] using
      hztest.const_mul_add_const_mul h0test m⁻¹ (-m⁻¹)
  · have hzi : Integrable (circleDensity r δ hδ z) volume := (circleDensity_contDiff r δ hδ z).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ z)
    have h0i : Integrable (circleDensity r δ hδ 0) volume := (circleDensity_contDiff r δ hδ 0).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ 0)
    rw [integral_sub (hzi.const_mul _) (h0i.const_mul _), integral_const_mul,
      integral_const_mul, circleDensity_integral_eq r δ hδ z, sub_self]

end LatticeProb.Gauss

-- ===== Local circle density

/-! # Local circle-density approximations

A disk around the origin inherits the local containment of a disk of the same
radius, and both disks can be enlarged by a common positive amount.
-/

open MeasureTheory Set Metric Filter
open scoped Topology

namespace LatticeProb.Gauss

/-- If a disk is contained in a centered ball, then the concentric disk of the
same radius is contained in that ball as well. -/
theorem closedBall_zero_subset_of_closedBall_subset {r ε : ℝ} (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) : closedBall (0 : ℂ) r ⊆ ball 0 ε := by
  intro x hx
  have hxnorm : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
  have hp : z + x ∈ ball (0 : ℂ) ε := hz (by
    rw [mem_closedBall, dist_eq_norm]
    simpa using hxnorm)
  have hm : z - x ∈ ball (0 : ℂ) ε := hz (by
    rw [mem_closedBall, dist_eq_norm]
    simpa using hxnorm)
  have hp' : ‖z + x‖ < ε := by simpa [mem_ball, dist_zero_right] using hp
  have hm' : ‖z - x‖ < ε := by simpa [mem_ball, dist_zero_right] using hm
  have h := norm_sub_le (z + x) (z - x)
  have heq : (z + x) - (z - x) = (2 : ℂ) * x := by ring
  rw [heq, norm_mul] at h
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo] at h
  rw [mem_ball, dist_zero_right]
  nlinarith

/-- A compact disk contained in an open set can be enlarged slightly while
remaining in the open set. -/
theorem exists_enlarged_closedBall_subset_open {r : ℝ} (hr : 0 ≤ r) (z : ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hz : closedBall z r ⊆ U) :
    ∃ η > 0, closedBall z (r + η) ⊆ U := by
  obtain ⟨η, hη, hsub⟩ := (isCompact_closedBall z r).exists_cthickening_subset_open hU hz
  refine ⟨η, hη, ?_⟩
  simpa [cthickening_closedBall hη.le hr, add_comm] using hsub

/-- Both circles have a common buffer inside the field's local domain. -/
theorem exists_common_circle_buffer {r ε : ℝ} (hr : 0 ≤ r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ η > 0, closedBall z (r + η) ⊆ ball 0 ε ∧
      closedBall (0 : ℂ) (r + η) ⊆ ball 0 ε := by
  obtain ⟨ηz, hηz, hz'⟩ := exists_enlarged_closedBall_subset_open hr z isOpen_ball hz
  obtain ⟨η0, hη0, h0'⟩ := exists_enlarged_closedBall_subset_open hr 0 isOpen_ball
    (closedBall_zero_subset_of_closedBall_subset z hz)
  refine ⟨min ηz η0, lt_min hηz hη0, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith [min_le_left ηz η0])).trans hz'
  · have hsub : closedBall (0 : ℂ) (r + min ηz η0) ⊆ closedBall 0 (r + η0) :=
      closedBall_subset_closedBall (by linarith [min_le_right ηz η0])
    exact hsub.trans h0'

/-- The annular widths used to approximate a circle. -/
noncomputable def circleDensityWidth (r η : ℝ) (n : ℕ) : ℝ :=
  r * η / ((n : ℝ) + 1)

theorem circleDensityWidth_pos {r η : ℝ} (hr : 0 < r) (hη : 0 < η) (n : ℕ) :
    0 < circleDensityWidth r η n := by
  unfold circleDensityWidth
  positivity

theorem circleDensityWidth_tendsto_zero (r η : ℝ) :
    Tendsto (circleDensityWidth r η) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => r * η / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Explicit local zero-integral tests built from annular densities, with widths
converging to zero. This leaves convergence of their logarithmic energy open. -/
theorem exists_local_circleDensity_tests {r ε : ℝ} (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ (η : ℝ) (hη : 0 < η),
      let δ := circleDensityWidth r η
      let hδ := circleDensityWidth_pos hr hη
      let φ := fun n x =>
        (∫ y, circleDensity r (δ n) (hδ n) 0 y)⁻¹ * circleDensity r (δ n) (hδ n) z x -
        (∫ y, circleDensity r (δ n) (hδ n) 0 y)⁻¹ * circleDensity r (δ n) (hδ n) 0 x
      Tendsto δ atTop (𝓝 0) ∧
      (∀ n, IsTestFunction (ball 0 ε) (φ n) ∧ ∫ x, φ n x = 0) ∧
      (∀ n x, x ∈ Function.support (circleDensity r (δ n) (hδ n) z) →
        |‖x - z‖ - r| < η / ((n : ℝ) + 1)) ∧
      (∀ n x, x ∈ Function.support (circleDensity r (δ n) (hδ n) 0) →
        |‖x‖ - r| < η / ((n : ℝ) + 1)) := by
  obtain ⟨η, hη, hz', h0'⟩ := exists_common_circle_buffer hr.le z hz
  refine ⟨η, hη, circleDensityWidth_tendsto_zero r η, ?_, ?_, ?_⟩
  · intro n
    have hwidth : circleDensityWidth r η n ≤ r * η := by
      unfold circleDensityWidth
      apply div_le_self (mul_nonneg hr.le hη.le)
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    exact circleDensity_normalized_difference_test hr (circleDensityWidth_pos hr hη n)
      hwidth z (ball 0 ε) hz' h0'
  · intro n x hx
    apply circleDensity_support_radius hr (circleDensityWidth_pos hr hη n) _ z x hx
    simp only [circleDensityWidth]
    ring_nf
    exact le_rfl
  · intro n x hx
    have h := circleDensity_support_radius hr (circleDensityWidth_pos hr hη n)
      (η := η / ((n : ℝ) + 1)) (by simp [circleDensityWidth, div_eq_mul_inv, mul_assoc]) 0 x hx
    simpa using h

/-- Difference of the normalized annular densities at `z` and at the origin. -/
noncomputable def circleDensityDifference (r η : ℝ) (hr : 0 < r) (hη : 0 < η)
    (z : ℂ) (n : ℕ) (x : ℂ) : ℝ :=
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x -
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ 0 x
end LatticeProb.Gauss

-- ===== Radial circle density

/-! # Radial mass of annular approximations

Polar coordinates identify the radial mass of the normalized annular bumps.
-/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real

namespace LatticeProb.Gauss

/-- Integrating a radial function on the plane gives its polar radial integral. -/
theorem integral_radial (f : ℝ → ℝ) (z : ℂ) :
    (∫ x : ℂ, f ‖x - z‖) = 2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * f ρ := by
  have htrans : (∫ x : ℂ, f ‖x - z‖) = ∫ x : ℂ, f ‖x‖ := by
    simpa using (integral_sub_right_eq_self (fun x : ℂ => f ‖x‖) z)
  rw [htrans, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
  calc
    _ = (∫ ρ in Ioi (0 : ℝ), ρ * f |ρ|) * ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
      simp
    _ = 2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * f ρ := by
      have hvol : (∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
        rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter]
        simp [Real.pi_nonneg, ← two_mul]
      rw [hvol, mul_comm]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ρ hρ
      simp [abs_of_pos (show 0 < ρ from hρ)]

/-- Radial mass profile associated with a normalized annular density. -/
noncomputable def circleDensityRadialWeight (r δ : ℝ) (hδ : 0 < δ) (ρ : ℝ) : ℝ :=
  2 * Real.pi * (∫ x, circleDensity r δ hδ 0 x)⁻¹ *
    (ρ * circleRadiusBump r δ hδ (ρ ^ 2))

/-- The radial mass profile has total mass one on the positive half-line. -/
theorem circleDensityRadialWeight_integral {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ) = 1 := by
  simp_rw [circleDensityRadialWeight]
  rw [integral_const_mul]
  have h : (∫ x, circleDensity r δ hδ 0 x) =
      2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * circleRadiusBump r δ hδ (ρ ^ 2) := by
    simpa [circleDensity] using integral_radial (fun t => circleRadiusBump r δ hδ (t ^ 2)) 0
  have hm := ne_of_gt (circleDensity_integral_pos hr hδ 0)
  calc
    _ = (∫ x, circleDensity r δ hδ 0 x)⁻¹ *
        (2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * circleRadiusBump r δ hδ (ρ ^ 2)) := by ring
    _ = 1 := by rw [← h, inv_mul_cancel₀ hm]

/-- The radial mass profile is nonnegative at positive radii. -/
theorem circleDensityRadialWeight_nonneg (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ circleDensityRadialWeight r δ hδ ρ := by
  unfold circleDensityRadialWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    (inv_nonneg.mpr (circleDensity_integral_pos hr hδ 0).le))
    (mul_nonneg hρ (circleRadiusBump r δ hδ).nonneg)

/-- The radial weight vanishes outside the annulus of the original density. -/
theorem circleDensityRadialWeight_support_radius {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : circleDensityRadialWeight r δ hδ ρ ≠ 0) : |ρ - r| < η := by
  have hb : circleRadiusBump r δ hδ (ρ ^ 2) ≠ 0 := by
    intro hz
    apply h
    simp [circleDensityRadialWeight, hz]
  have hd : (ρ : ℂ) ∈ Function.support (circleDensity r δ hδ 0) := by
    simpa [circleDensity, abs_of_nonneg hρ] using hb
  have := circleDensity_support_radius hr hδ hwidth 0 (ρ : ℂ) hd
  simpa [abs_of_nonneg hρ] using this

/-- The radial weight is integrable on positive radii. -/
theorem circleDensityRadialWeight_integrableOn {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    IntegrableOn (circleDensityRadialWeight r δ hδ) (Ioi (0 : ℝ)) := by
  have hc : Continuous (circleDensityRadialWeight r δ hδ) := by
    unfold circleDensityRadialWeight
    exact continuous_const.mul (continuous_id.mul
      ((circleRadiusBump r δ hδ).continuous.comp (continuous_id.pow 2)))
  let M : ℝ := r + δ + 1
  have hi : IntegrableOn (circleDensityRadialWeight r δ hδ) (Icc 0 M) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  refine hi.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro ρ hρ
  have hρpos : 0 < ρ := hρ.1
  have hρM : M < ρ := by
    by_contra hn
    exact hρ.2 ⟨hρpos.le, le_of_not_gt hn⟩
  by_contra hn
  have hb : circleRadiusBump r δ hδ (ρ ^ 2) ≠ 0 := by
    intro hz
    apply hn
    simp [circleDensityRadialWeight, hz]
  have hd : (ρ : ℂ) ∈ Function.support (circleDensity r δ hδ 0) := by
    simpa [circleDensity, abs_of_pos hρpos] using hb
  have hs := circleDensity_support r δ hδ 0 (ρ : ℂ) hd
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos] at hs
  have hs' := (abs_lt.mp hs).2
  dsimp [M] at hρM
  nlinarith [sq_nonneg δ, sq_nonneg r]

/-- Integration of a radial observable against the normalized annular density
reduces to integration against its radial mass profile. -/
theorem integral_normalized_circleDensity_radial (r δ : ℝ) (hδ : 0 < δ)
    (z : ℂ) (f : ℝ → ℝ) :
    (∫ x : ℂ, (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleDensity r δ hδ z x * f ‖x - z‖) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * f ρ := by
  have h := integral_radial
    (fun ρ => (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleRadiusBump r δ hδ (ρ ^ 2) * f ρ) z
  simp only [circleDensity] at h ⊢
  rw [h, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  simp only [circleDensityRadialWeight, circleDensity, sub_zero]
  ring

/-- The angular integral on the polar-coordinate interval is the circle
average multiplied by the interval length. -/
theorem integral_circleMap_eq_circleAverage (f : ℂ → ℝ) (z : ℂ) (ρ : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap z ρ θ)) =
      2 * Real.pi * Real.circleAverage f z ρ := by
  have h := Real.circleAverage_eq_integral_add (f := f) (c := z) (R := ρ) (-Real.pi)
  change Real.circleAverage f z ρ = (2 * Real.pi)⁻¹ •
    ∫ θ in (0 : ℝ)..2 * Real.pi, (fun t => f (circleMap z ρ t)) (θ + -Real.pi) at h
  rw [intervalIntegral.integral_comp_add_right (fun t => f (circleMap z ρ t)) (-Real.pi)] at h
  have heq : 2 * Real.pi + -Real.pi = Real.pi := by ring
  simp only [zero_add, heq, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_nonneg]),
    integral_Ioc_eq_integral_Ioo] at h
  rw [h]
  field_simp

/-- A continuous observable integrated against an annular density is a radial
mixture of its circle averages. -/
theorem integral_circleDensity_eq_circleAverage {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (z : ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    (∫ x, circleDensity r δ hδ z x * f x) =
      2 * Real.pi * ∫ ρ in Ioi (0 : ℝ),
        ρ * circleRadiusBump r δ hδ (ρ ^ 2) * Real.circleAverage f z ρ := by
  let g : ℝ × ℝ → ℝ := fun p =>
    p.1 * circleRadiusBump r δ hδ (p.1 ^ 2) * f (circleMap z p.1 p.2)
  have hc : Continuous g := by
    dsimp only [g, circleMap]
    apply (continuous_fst.mul ((circleRadiusBump r δ hδ).continuous.comp
      (continuous_fst.pow 2))).mul
    apply hf.comp
    fun_prop
  let M : ℝ := r + δ + 1
  have hint : IntegrableOn g (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hi : IntegrableOn g (Icc 0 M ×ˢ Icc (-Real.pi) Real.pi) :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hi.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨ρ, θ⟩ ⟨⟨hρ, hθ⟩, hn⟩
    change 0 < ρ at hρ
    have hρM : M < ρ := by
      by_contra hnot
      exact hn ⟨⟨hρ.le, le_of_not_gt hnot⟩, ⟨hθ.1.le, hθ.2.le⟩⟩
    have hb : circleRadiusBump r δ hδ (ρ ^ 2) = 0 := by
      by_contra hb
      have hd : (ρ : ℂ) ∈ Function.support (circleDensity r δ hδ 0) := by
        simpa [circleDensity, abs_of_pos hρ] using hb
      have hs := circleDensity_support r δ hδ 0 (ρ : ℂ) hd
      simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hs
      have hs' := (abs_lt.mp hs).2
      dsimp [M] at hρM
      nlinarith [sq_nonneg δ, sq_nonneg r]
    simp [g, hb]
  have htrans : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ u : ℂ, circleDensity r δ hδ z (u + z) * f (u + z) := by
    simpa using (integral_sub_right_eq_self
      (fun u : ℂ => circleDensity r δ hδ z (u + z) * f (u + z)) z)
  have hpolar : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, g p := by
    rw [htrans, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    change 0 < ρ at hρ
    have hcircle : (Complex.polarCoord.symm (ρ, θ) + z) = circleMap z ρ θ := by
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, add_comm]
    simp only [g, smul_eq_mul, hcircle, circleDensity, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hρ]
    ring
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
  rw [hpolar, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  change (∫ θ in Ioo (-Real.pi) Real.pi,
    ρ * circleRadiusBump r δ hδ (ρ ^ 2) * f (circleMap z ρ θ)) = _
  rw [integral_const_mul, integral_circleMap_eq_circleAverage]
  ring

/-- The normalized annular density is the mixture of circle measures with
its normalized radial mass profile. -/
theorem integral_normalized_circleDensity_eq_circleAverage {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z : ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x * f x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        Real.circleAverage f z ρ := by
  have heq : (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleDensity r δ hδ z x * f x) =
      (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
        ∫ x, circleDensity r δ hδ z x * f x := by
    simp_rw [mul_assoc, integral_const_mul]
  rw [heq, integral_circleDensity_eq_circleAverage hr hδ z hf, ← integral_const_mul,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  simp only [circleDensityRadialWeight]
  ring

end LatticeProb.Gauss

-- ===== Logarithmic potential of circle densities

/-! # Logarithmic potential of a circle

Averaging the logarithmic kernel on a circle removes its point singularity.
-/

open MeasureTheory Set Metric Filter
open scoped Topology Real

namespace LatticeProb.Gauss

/-- The logarithmic potential of a circle is the logarithm of the larger of
its radius and the distance to its center. -/
theorem circleAverage_log_norm_sub_eq_log_max {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (fun y => Real.log ‖y - x‖) z r =
      Real.log (max r ‖z - x‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
  by_cases hx : ‖z - x‖ ≤ r
  · have hratio : |r⁻¹ * ‖z - x‖| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))]
      exact (inv_mul_le_one₀ hr).2 hx
    rw [(Real.posLog_eq_zero_iff _).2 hratio, add_zero, max_eq_left hx]
  · have hxr : r < ‖z - x‖ := lt_of_not_ge hx
    have hxn : ‖z - x‖ ≠ 0 := ne_of_gt (hr.trans hxr)
    have hratio : 1 ≤ |r⁻¹ * ‖z - x‖| := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))]
      exact (one_le_inv_mul₀ hr).2 hxr.le
    rw [Real.posLog_eq_log hratio, Real.log_mul (inv_ne_zero hr.ne') hxn,
      Real.log_inv, max_eq_right hxr.le]
    ring

/-- The averaged logarithmic kernel is continuous even when the point lies on
the circle. -/
theorem continuous_circleAverage_log_norm_sub {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun x : ℂ => Real.circleAverage (fun y => Real.log ‖y - x‖) z r) := by
  have heq : (fun x : ℂ => Real.circleAverage (fun y => Real.log ‖y - x‖) z r) =
      fun x => Real.log (max r ‖z - x‖) := by
    funext x
    exact circleAverage_log_norm_sub_eq_log_max hr z x
  rw [heq]
  exact (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
    (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))

/-- For a point inside or on a circle, its logarithmic potential is constant. -/
theorem circleAverage_log_norm_sub_of_dist_le {r : ℝ} (hr : 0 < r) (z x : ℂ)
    (hx : dist x z ≤ r) :
    Real.circleAverage (fun y => Real.log ‖y - x‖) z r = Real.log r := by
  rw [circleAverage_log_norm_sub_eq_log_max hr, max_eq_left]
  simpa [dist_eq_norm, norm_sub_rev] using hx

/-- The continuous normalization term in the whole-plane covariance kernel. -/
noncomputable def wholePlaneNormalization (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)

theorem continuous_wholePlaneNormalization : Continuous wholePlaneNormalization := by
  unfold wholePlaneNormalization
  exact (continuous_norm.max continuous_const).log
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))

/-- Circle averaging the whole-plane covariance gives a continuous logarithmic
potential, with the diagonal ignored only inside the circle integral. -/
theorem circleAverage_wholePlaneCov_eq {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) z r =
      wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
        Real.log (max r ‖z - x‖) := by
  have hnorm : CircleIntegrable wholePlaneNormalization z r :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable hr.le
  have heq : Real.circleAverage (fun y => wholePlaneCov x y) z r =
      Real.circleAverage (fun y => wholePlaneNormalization x + wholePlaneNormalization y -
        Real.log ‖y - x‖) z r := by
    apply Real.circleAverage_congr_codiscreteWithin _ hr.ne'
    filter_upwards [compl_singleton_mem_codiscreteWithin x] with y hyx
    have hne : y ≠ x := by simpa using hyx
    have hdist : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
    have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    have hy : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    rw [wholePlaneCov, wholePlaneNormalization, wholePlaneNormalization,
      Real.log_div (mul_ne_zero hx hy) hdist, Real.log_mul hx hy, norm_sub_rev]
  rw [heq]
  change Real.circleAverage (((fun _ : ℂ => wholePlaneNormalization x) +
    wholePlaneNormalization) - (fun y => Real.log ‖y - x‖)) z r = _
  rw [Real.circleAverage_sub
    ((circleIntegrable_const (wholePlaneNormalization x) z r).add hnorm)
    (circleIntegrable_log_norm_sub_const r),
    Real.circleAverage_add (circleIntegrable_const _ _ _) hnorm,
    Real.circleAverage_const, circleAverage_log_norm_sub_eq_log_max hr]

/-- The circle-averaged whole-plane covariance is continuous in the other point. -/
theorem continuous_circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun x : ℂ => Real.circleAverage (fun y => wholePlaneCov x y) z r) := by
  have heq : (fun x : ℂ => Real.circleAverage (fun y => wholePlaneCov x y) z r) =
      fun x => wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
        Real.log (max r ‖z - x‖) := by
    funext x
    exact circleAverage_wholePlaneCov_eq hr z x
  rw [heq]
  exact (continuous_wholePlaneNormalization.add continuous_const).sub
    ((continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))))

/-- The excess of the circle's logarithmic potential is uniformly controlled
inside a slightly enlarged disk. -/
theorem circle_log_potential_excess_bound {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (z x : ℂ) (hx : x ∈ closedBall z (r + η)) :
    0 ≤ Real.log (max r ‖z - x‖) - Real.log r ∧
      Real.log (max r ‖z - x‖) - Real.log r ≤ Real.log (r + η) - Real.log r := by
  have hn : ‖z - x‖ ≤ r + η := by
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hx
  have hmax : max r ‖z - x‖ ≤ r + η := max_le (by linarith) hn
  constructor
  · linarith [Real.log_le_log hr (le_max_left r ‖z - x‖)]
  · linarith [Real.log_le_log (lt_of_lt_of_le hr (le_max_left r ‖z - x‖)) hmax]

/-- A compactly supported probability density in the enlarged disk has at most
the corresponding logarithmic-potential excess. -/
theorem integral_circle_log_potential_excess_bound {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (z : ℂ) (g : ℂ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : 0 ≤ g) (hgm : ∫ x, g x = 1)
    (hgs : tsupport g ⊆ closedBall z (r + η)) :
    0 ≤ ∫ x, g x * (Real.log (max r ‖z - x‖) - Real.log r) ∧
      (∫ x, g x * (Real.log (max r ‖z - x‖) - Real.log r)) ≤
        Real.log (r + η) - Real.log r := by
  let E : ℂ → ℝ := fun x => Real.log (max r ‖z - x‖) - Real.log r
  let b := Real.log (r + η) - Real.log r
  have hE : Continuous E := by
    apply Continuous.sub _ continuous_const
    exact (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))
  have hgi : Integrable g volume := hg.integrable_of_hasCompactSupport hgc
  have hEi : Integrable (fun x => g x * E x) volume :=
    (hg.mul hE).integrable_of_hasCompactSupport hgc.mul_right
  have hbi : Integrable (fun x => g x * b) volume := hgi.mul_const b
  have hnonneg : ∀ x, 0 ≤ g x * E x := by
    intro x
    apply mul_nonneg (hgn x)
    dsimp [E]
    linarith [Real.log_le_log hr (le_max_left r ‖z - x‖)]
  constructor
  · exact integral_nonneg hnonneg
  · calc
      (∫ x, g x * E x) ≤ ∫ x, g x * b := by
        apply integral_mono hEi hbi
        intro x
        by_cases hx : g x = 0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left _ (hgn x)
          exact (circle_log_potential_excess_bound hr hη z x
            (hgs (subset_closure hx))).2
      _ = b := by rw [integral_mul_const, hgm, one_mul]

/-- The same-center logarithmic potential excess of the normalized annular
densities tends to zero. -/
theorem circleDensity_log_potential_excess_tendsto_zero {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) :
    Tendsto (fun n : ℕ => ∫ x,
      ((∫ y, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x) *
      (Real.log (max r ‖z - x‖) - Real.log r)) atTop (𝓝 0) := by
  have hηlim : Tendsto (fun n : ℕ => η / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hradd : Tendsto (fun n : ℕ => r + η / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).add hηlim
  have hbound : Tendsto (fun n : ℕ => Real.log (r + η / ((n : ℝ) + 1)) - Real.log r)
      atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log hr.ne').tendsto.comp hradd).sub_const (Real.log r)
  apply squeeze_zero _ _ hbound
  all_goals
    intro n
    let δ := circleDensityWidth r η n
    let hδ := circleDensityWidth_pos hr hη n
    let g : ℂ → ℝ := fun x => (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
    have hg : Continuous g := continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous
    have hgc : HasCompactSupport g := (circleDensity_hasCompactSupport hr.le hδ z).mul_left
    have hgn : 0 ≤ g := fun x => mul_nonneg
      (inv_nonneg.mpr (circleDensity_integral_pos hr.le hδ 0).le)
      (circleDensity_nonneg r δ hδ z x)
    have hgm : ∫ x, g x = 1 := circleDensity_normalized_integral hr.le hδ z
    have hwidth : δ ≤ r * (η / ((n : ℝ) + 1)) := by
      dsimp [δ, circleDensityWidth]
      simp [div_eq_mul_inv, mul_assoc]
    have hgs : tsupport g ⊆ closedBall z (r + η / ((n : ℝ) + 1)) := by
      refine tsupport_mul_subset_right.trans ?_
      exact circleDensity_tsupport_subset_closedBall hr hδ hwidth z
    have h := integral_circle_log_potential_excess_bound hr (by positivity) z g hg hgc hgn hgm hgs
    first | exact h.1 | exact h.2

end LatticeProb.Gauss

-- ===== Continuous limit of circle densities (lemma circleDensityRadialWeight_integral_sub_le only)
open MeasureTheory Set Metric Filter Real
open scoped Topology
namespace LatticeProb.Gauss
/-- A normalized radial weight integrates a continuous function close to its
value at the limiting radius when the weight is supported nearby. -/
theorem circleDensityRadialWeight_integral_sub_le {r δ η ε : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hclose : ∀ ρ, |ρ - r| < η → |g ρ - g r| ≤ ε) :
    |(∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * g ρ) - g r| ≤ ε := by
  let W := circleDensityRadialWeight r δ hδ
  have hW : Continuous W := by
    dsimp [W, circleDensityRadialWeight]
    exact continuous_const.mul (continuous_id.mul
      ((circleRadiusBump r δ hδ).continuous.comp (continuous_id.pow 2)))
  have hi : IntegrableOn (fun ρ => W ρ * g ρ) (Ioi (0 : ℝ)) := by
    have hc : IntegrableOn (fun ρ => W ρ * g ρ) (Icc (r - η) (r + η)) :=
      (hW.mul hg).continuousOn.integrableOn_compact isCompact_Icc
    refine hc.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro ρ hρ
    by_cases hw : W ρ = 0
    · simp [hw]
    · have hn := circleDensityRadialWeight_support_radius hr hδ hwidth
        (show 0 ≤ ρ from le_of_lt hρ.1) hw
      rw [abs_lt] at hn
      exact (hρ.2 ⟨by linarith [hn.1], by linarith [hn.2]⟩).elim
  have hwi : IntegrableOn W (Ioi (0 : ℝ)) := circleDensityRadialWeight_integrableOn hr.le hδ
  have hwm : (∫ ρ in Ioi (0 : ℝ), W ρ) = 1 := circleDensityRadialWeight_integral hr.le hδ
  have hl : g r - ε ≤ ∫ ρ in Ioi (0 : ℝ), W ρ * g ρ := by
    calc
      _ = ∫ ρ in Ioi (0 : ℝ), W ρ * (g r - ε) := by
        rw [integral_mul_const, hwm, one_mul]
      _ ≤ _ := by
        apply integral_mono_ae (hwi.mul_const _) hi
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have h := hclose ρ (circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw)
          rw [abs_le] at h
          linarith [h.1]
  have hu : (∫ ρ in Ioi (0 : ℝ), W ρ * g ρ) ≤ g r + ε := by
    calc
      _ ≤ ∫ ρ in Ioi (0 : ℝ), W ρ * (g r + ε) := by
        apply integral_mono_ae hi (hwi.mul_const _)
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have h := hclose ρ (circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw)
          rw [abs_le] at h
          linarith [h.2]
      _ = _ := by rw [integral_mul_const, hwm, one_mul]
  rw [abs_le]
  constructor <;> linarith

end LatticeProb.Gauss
