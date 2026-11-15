import LatticeProb.Prob.BrownianWedgeSurvivalPolynomial
import LatticeProb.Analysis.WedgeRadiusPower
import LatticeProb.Analysis.WedgeRadiusAdmissible

/-! # Small-distance Brownian wedge survival -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A subcritical one-time wedge survival bound at small normalized distance. -/
theorem brownian_wedge_survival_small :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {θ p q a : ℝ} (n : ℕ), 0 < θ → θ < Real.pi → 0 < p → p * θ < Real.pi →
      0 < a → a < 1 → q ≤ (1 - a) * p → q ≤ 2 * a * n →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : Euc 2}
        {B : ℝ≥0 → Ω → Euc 2}, IsBrownianSpace 2 x B P →
        ∀ t : ℝ≥0, 0 < (t : ℝ) →
        let d := ‖x‖ / Real.sqrt (t : ℝ)
        0 < d → d < δ →
        let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
        let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
          CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
        x ∈ closure W →
        P.real {ω | ∀ s ≤ t, B s ω ∈ W} ≤
          ((Real.cos (p * (θ / 2)))⁻¹ * (2 : ℝ) ^ p +
            C * ((n.factorial : ℝ) / c ^ n)) * d ^ q := by
  obtain ⟨C, c, hC, hc, hbound⟩ := brownian_wedge_survival_polynomial
  refine ⟨C, c, hC, hc, ?_⟩
  intro θ p q a n hθ0 hθπ hp hpθ ha ha1 hq1 hq2
  obtain ⟨δ, hδ, hδ1, hδsmall⟩ := exists_intermediate_radius_threshold ha ha1
  refine ⟨δ, hδ, ?_⟩
  intro Ω mΩ P x B hB t ht
  dsimp only
  intro hd hdδ hx
  let d : ℝ := ‖x‖ / Real.sqrt (t : ℝ)
  let u : ℝ := d ^ a / 2
  let r : ℝ := Real.sqrt (t : ℝ) * u
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 ht
  have hs2 : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := Real.sq_sqrt ht.le
  have hd1 : d ≤ 1 := le_trans hdδ.le hδ1
  have hu : 0 < u := by dsimp [u]; positivity
  have hr : 0 < r := mul_pos hs hu
  obtain ⟨hdu, hu1⟩ := hδsmall hd hdδ
  change d ≤ u at hdu
  change 4 * u ^ 2 ≤ 1 at hu1
  have hxr : ‖x‖ ≤ r := by
    have hd_eq : d * Real.sqrt (t : ℝ) = ‖x‖ := by
      dsimp [d]; field_simp
    calc
      ‖x‖ = d * Real.sqrt (t : ℝ) := hd_eq.symm
      _ ≤ u * Real.sqrt (t : ℝ) := mul_le_mul_of_nonneg_right hdu hs.le
      _ = r := by dsimp [r]; ring
  have hrt : 4 * r ^ 2 ≤ (t : ℝ) := by
    calc
      4 * r ^ 2 = (4 * u ^ 2) * (Real.sqrt (t : ℝ)) ^ 2 := by dsimp [r]; ring
      _ ≤ 1 * (Real.sqrt (t : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hu1 (sq_nonneg _)
      _ = (t : ℝ) := by rw [one_mul, hs2]
  have hratio : ‖x‖ / r = d / u := by
    dsimp [r, d]
    field_simp
  have htime : 4 * r ^ 2 / (t : ℝ) = 4 * u ^ 2 := by
    apply (div_eq_iff (ne_of_gt ht)).2
    calc
      4 * r ^ 2 = (4 * u ^ 2) * (Real.sqrt (t : ℝ)) ^ 2 := by dsimp [r]; ring
      _ = (4 * u ^ 2) * (t : ℝ) := by rw [hs2]
  obtain ⟨hpow, hrem⟩ := intermediate_radius_power_bounds hd hd1 n hq1 hq2
  have hcos : 0 < Real.cos (p * (θ / 2)) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
  have hc' : 0 ≤ C * ((n.factorial : ℝ) / c ^ n) := by positivity
  have h := hbound hB hθ0 hθπ hp hpθ hr t hrt hxr n hx
  rw [hratio, htime] at h
  calc
    _ ≤ (Real.cos (p * (θ / 2)))⁻¹ * (d / u) ^ p +
        C * ((n.factorial : ℝ) / c ^ n) * (4 * u ^ 2) ^ n := h
    _ ≤ (Real.cos (p * (θ / 2)))⁻¹ * ((2 : ℝ) ^ p * d ^ q) +
        C * ((n.factorial : ℝ) / c ^ n) * d ^ q :=
      add_le_add (mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hcos.le))
        (mul_le_mul_of_nonneg_left hrem hc')
    _ = _ := by ring

end LatticeProb
