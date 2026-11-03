/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg3Fam at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2GFF
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqTRL
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg2All

/-!
# Negative moments on a small square: the comparison family (P2-NEGMOM2, steps 1–2)

For the zero-boundary GFF `h` on `𝕍 = (0,1)²`, a dyadic square `Q = z₀ + 2^{-m}[0,1]²` whose
`2·2^{-m}`-neighbourhood lies in a compact convex `K ⊆ 𝕍`:

* `Neg3.logCorr_bZ` : the family `Z_n(y) = γ h_{2^{-(m+n)}}(z₀ + 2^{-m} y)` (`Neg3.bZ`, `y` clamped
  to `[0,1]²`) is `γ²`-log-correlated on `[0,1]²` (`LogCorr`), from the two-sided bound
  `circleCov_two_sided` on `K`;
* `Neg3.exists_uniform_neg_moment_nM` : for `p < 0` the Riemann sums
  `nM_{k,j}(v) = ∑_{i ∈ grid j} 4^{-j} 2^{-(m+k)γ²/2} e^{γ h_{2^{-(m+k)}}(z₀ + 2^{-m}(c_i + v))}`
  of `areaApprox_{m+k}` on `Q` (cell centres `c_i` shifted by `v`) have `E nM^p ≤ C` uniformly in
  `k ≤ j` and `v`.

Route: Berestycki–Powell arXiv:2404.16642, `GMCproperties.tex` l. 1211–1218 (eq. (encadrKahane)):
Kahane's inequality (convex `x ↦ x^p`, `p < 0`) comparing `γ h_r` at the shifted points with
`Z_k` at the cell centres plus an independent `N(0, 2γ²c_K)`; the normalisation
`r^{γ²/2} e^{γ h} ≥ e^{−γ²c_K/2} e^{γ h − γ² Var h/2}` uses the *lower* variance bound
`Var h_r(z) ≥ −log r − c_K` on `K`. Then the uniform discrete negative moments
`LogCorr.exists_uniform_neg_moment` (BP Theorem `T:negmom`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

namespace Neg3

/-- clamp to `[0,1]²` -/
def clampC (y : ℂ) : ℂ := ⟨clampU y.re, clampU y.im⟩

lemma clampC_mem (y : ℂ) : clampC y ∈ unitSq :=
  ⟨(clampU_mem _).1, (clampU_mem _).2, (clampU_mem _).1, (clampU_mem _).2⟩

lemma clampC_eq {y : ℂ} (hy : y ∈ unitSq) : clampC y = y := by
  obtain ⟨a, b, c, d⟩ := hy
  apply Complex.ext <;> simp [clampC, clampU_eq a b, clampU_eq c d]

lemma radius_add (m n : ℕ) : radius (m + n) = radius m * (2 : ℝ)⁻¹ ^ n := by
  simp only [radius, pow_add]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- the comparison family on the square `z₀ + 2^{-m}[0,1]²` -/
def bZ (γ : ℝ) (X : Ω → Measure ℂ → ℝ) (z₀ : ℂ) (m n : ℕ) (y : ℂ) (ω : Ω) : ℝ :=
  γ * X ω (foldedCircle (z₀ + radius m • clampC y) (radius (m + n)))

lemma closedBall_sub_of_hQ {K : Set ℂ} {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) {w : ℂ}
    (hw : w ∈ unitSq) (n : ℕ) : closedBall (z₀ + radius m • w) (radius (m + n)) ⊆ K := by
  refine (closedBall_subset_closedBall ?_).trans (hQ w hw)
  rw [radius_add]
  have h1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 < radius m := radius_pos m
  nlinarith

lemma norm_smul_sub (a : ℝ) (ha : 0 ≤ a) (z₀ x y : ℂ) :
    ‖(z₀ + a • x) - (z₀ + a • y)‖ = a * ‖x - y‖ := by
  rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg ha]

/-- **the square family is `γ²`-log-correlated** -/
theorem logCorr_bZ (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) {K : Set ℂ}
    (hKU : K ⊆ openSquare) (hKc : Convex ℝ K) (hKk : IsCompact K) {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) :
    ∃ c : ℝ, LogCorr (bZ γ X z₀ m) P (γ ^ 2) c := by
  obtain ⟨cK, hcK⟩ := circleCov_two_sided hKU hKc hKk
  have hB : ∀ n x, closedBall (z₀ + radius m • clampC x) (radius (m + n)) ⊆ K := fun n x =>
    closedBall_sub_of_hQ hQ (clampC_mem x) n
  have hrm : 0 < radius m := radius_pos m
  refine ⟨γ ^ 2 * (cK + |Real.log (radius m)|), ⟨fun n => ?_, fun n x => ?_, fun n x => ?_,
    fun n x y hx hy => ?_⟩⟩
  · exact (hX.gaussian.comp_right fun x : ℂ => admC (radius_pos _) ((hB n x).trans hKU)).smul
      fun _ => γ
  · exact (hX.measurable_coord _).const_mul γ
  · show ∫ ω, γ * X ω (foldedCircle (z₀ + radius m • clampC x) (radius (m + n))) ∂P = 0
    rw [integral_const_mul, integral_circle hX (radius_pos _) ((hB n x).trans hKU), mul_zero]
  · show |cov[fun ω => γ * X ω (foldedCircle (z₀ + radius m • clampC x) (radius (m + n))),
      fun ω => γ * X ω (foldedCircle (z₀ + radius m • clampC y) (radius (m + n))); P] +
        γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ _
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have h := hcK hX (radius_pos (m + n)) (hB n x) (hB n y)
    have hL : Real.log (max (radius (m + n))
        ‖(z₀ + radius m • clampC x) - (z₀ + radius m • clampC y)‖) =
        Real.log (radius m) + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖) := by
      rw [norm_smul_sub _ hrm.le, clampC_eq hx, clampC_eq hy, radius_add,
        ← mul_max_of_nonneg _ _ hrm.le,
        Real.log_mul hrm.ne' (lt_max_of_lt_left (by positivity)).ne']
    rw [hL] at h
    set C := cov[fun ω => X ω (foldedCircle (z₀ + radius m • clampC x) (radius (m + n))),
      fun ω => X ω (foldedCircle (z₀ + radius m • clampC y) (radius (m + n))); P]
    have : |C + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ cK + |Real.log (radius m)| := by
      have := abs_le.1 h
      have := neg_abs_le (Real.log (radius m))
      have := le_abs_self (Real.log (radius m))
      rw [abs_le]; constructor <;> linarith
    rw [show γ * (γ * C) + γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖) =
      γ ^ 2 * (C + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)) by ring, abs_mul,
      abs_of_nonneg (sq_nonneg γ)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg γ)

/-- the Riemann sum of `areaApprox_{m+k}` on the square at level `j`, offset `v` -/
def nM (γ : ℝ) (X : Ω → Measure ℂ → ℝ) (z₀ : ℂ) (m k j : ℕ) (v : ℂ) (ω : Ω) : ℝ :=
  ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j * (radius (m + k) ^ (γ ^ 2 / 2) *
    Real.exp (γ * X ω (foldedCircle (z₀ + radius m • (cpt j i + v)) (radius (m + k)))))

lemma grid_nonempty (j : ℕ) : (grid j).Nonempty :=
  ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩

end Neg3

end DGMC

end LQGMetric
