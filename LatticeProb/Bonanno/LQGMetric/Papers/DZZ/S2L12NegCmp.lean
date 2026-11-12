/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L12NegCmp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Fin

/-!
# Scaled negative moments on a small square: Kahane comparison with a reference square (P2-NEGMOMU)

Input of DZZ Lemma 2.12, lower half (`LBM_LGDarXiv.tex` l. 750–755): negative moments of the
LQG mass of a ball `B(w, s)` with polynomial dependence on `s`.

The library bound `Neg3.exists_uniform_neg_moment_nM` hides how its constant depends on the
level `m` of the square `Q = z₀ + 2^{-m}[0,1]²` (through the `LogCorr` constant of `Neg3.bZ`,
`γ²(c_K + |log 2^{-m}|)`). Here this dependence is made explicit, following Berestycki–Powell
arXiv:2404.16642, `GMCproperties.tex` l. 1211–1218 (Kahane's inequality with an added constant
covariance, i.e. an independent Gaussian of variance `≈ γ² m log 2`):

* `negU_logCorr_bZ` : `bZ γ X z₀ m` is `γ²`-log-correlated with the explicit constant
  `γ²(c_K + |log 2^{-m}|)` (the proof of `Neg3.logCorr_bZ`, with the constant kept);
* `negU_integral_gM_rpow_le` : Kahane comparison of two `β`-log-correlated families (constants
  `c`, `c'`): `E gM_n(Z)^q ≤ e^{q(q-1)(c+c')/2} E gM_n(Z')^q` for `q ≤ 0`;
* `negU_integral_nM_rpow_le` : `E nM_{k,j}(v)^p ≤ D_m C₁` with `D_m` explicit in `m`, where `C₁`
  bounds the negative moments of a fixed reference square.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DZZ

open DGMC DGMC.Neg3

/-- **Kahane comparison of two log-correlated families** (BP l. 1211–1218): for `q ≤ 0`,
`E gM_n(Z)^q ≤ e^{q(q-1)(c+c')/2} E gM_n(Z')^q`. -/
theorem negU_integral_gM_rpow_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {Z : ℕ → ℂ → Ω → ℝ} {Z' : ℕ → ℂ → Ω' → ℝ} {β c c' : ℝ}
    (hZ : LogCorr Z P β c) (hZ' : LogCorr Z' P' β c') {q : ℝ} (hq : q ≤ 0) (n j : ℕ) :
    ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P ≤
      Real.exp (q * (q - 1) * (c + c') / 2) * ∫ ω, gM (Z' n) P' j (grid j) ω ^ q ∂P' := by
  have hne : Nonempty ↥(grid j) := DGMC.grid_nonempty j
  have h0 : (0 : ℂ) ∈ unitSq := by simp [unitSq]
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hZ.cov n 0 0 h0 h0)
  have hc0' : 0 ≤ c' := (abs_nonneg _).trans (hZ'.cov n 0 0 h0 h0)
  have hXv : HasGaussianLaw (fun ω (i : ↥(grid j)) => Z n (cpt j i) ω) P :=
    hasGaussianLaw_fintype (hZ.gauss n) (fun i : ↥(grid j) => cpt j i)
  have hYv : HasGaussianLaw (fun ω (i : ↥(grid j)) => Z' n (cpt j i) ω) P' :=
    hasGaussianLaw_fintype (hZ'.gauss n) (fun i : ↥(grid j) => cpt j i)
  have hcov : ∀ a b : ↥(grid j),
      cov[fun ω => Z n (cpt j a) ω, fun ω => Z n (cpt j b) ω; P] ≤
      cov[fun ω => Z' n (cpt j a) ω, fun ω => Z' n (cpt j b) ω; P'] +
        ((⟨c + c', by linarith⟩ : ℝ≥0) : ℝ) := by
    intro a b
    show _ ≤ _ + (c + c')
    have h1 := abs_le.1 (hZ.cov n _ _ (cpt_mem_unitSq a.2) (cpt_mem_unitSq b.2))
    have h2 := abs_le.1 (hZ'.cov n _ _ (cpt_mem_unitSq a.2) (cpt_mem_unitSq b.2))
    linarith [h1.2, h2.1]
  have hKa := Kahane.kahane_rpow_le_add_const (Or.inl hq)
    (p := fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) (fun _ => by positivity) hXv hYv
    (fun i => hZ.mean n _) (fun i => hZ'.mean n _) _ hcov
  have hX : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => Z n (cpt j i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => Z n (cpt j i) ω) ω i; P] / 2)) ^ q) =
      fun ω => gM (Z n) P j (grid j) ω ^ q := by
    funext ω
    rw [gM, ← Finset.sum_coe_sort (grid j)]
  have hY : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => Z' n (cpt j i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => Z' n (cpt j i) ω) ω i; P'] / 2)) ^ q) =
      fun ω => gM (Z' n) P' j (grid j) ω ^ q := by
    funext ω
    rw [gM, ← Finset.sum_coe_sort (grid j)]
  rw [hX, hY] at hKa
  exact hKa

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **`bZ` is log-correlated with an explicit constant** `γ²(c_K + |log 2^{-m}|)` (the proof of
`Neg3.logCorr_bZ`, keeping the constant). -/
theorem negU_logCorr_bZ (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) {K : Set ℂ}
    (hKU : K ⊆ openSquare) {cK : ℝ}
    (hK : ∀ {z w : ℂ} {r : ℝ}, 0 < r → closedBall z r ⊆ K → closedBall w r ⊆ K →
      |cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w r); P] +
        Real.log (max r ‖z - w‖)| ≤ cK)
    {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) :
    LogCorr (bZ γ X z₀ m) P (γ ^ 2) (γ ^ 2 * (cK + |Real.log (radius m)|)) := by
  have hB : ∀ n x, closedBall (z₀ + radius m • clampC x) (radius (m + n)) ⊆ K := fun n x =>
    closedBall_sub_of_hQ hQ (clampC_mem x) n
  have hrm : 0 < radius m := radius_pos m
  refine ⟨fun n => ?_, fun n x => ?_, fun n x => ?_, fun n x y hx hy => ?_⟩
  · exact (hX.gaussian.comp_right fun x : ℂ => admC (radius_pos _) ((hB n x).trans hKU)).smul
      fun _ => γ
  · exact (hX.measurable_coord _).const_mul γ
  · show ∫ ω, γ * X ω (foldedCircle (z₀ + radius m • clampC x) (radius (m + n))) ∂P = 0
    rw [integral_const_mul, integral_circle hX (radius_pos _) ((hB n x).trans hKU), mul_zero]
  · show |cov[fun ω => γ * X ω (foldedCircle (z₀ + radius m • clampC x) (radius (m + n))),
      fun ω => γ * X ω (foldedCircle (z₀ + radius m • clampC y) (radius (m + n))); P] +
        γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ _
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have h := hK (radius_pos (m + n)) (hB n x) (hB n y)
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

/-- **Negative moments of the Riemann sums on a level-`m` square, explicit in `m`**: Kahane
comparison with the cell-centre family (`Neg3.integral_nM_rpow_le`), then with a fixed
reference square `z₁ + 2^{-m₁}[0,1]²` (`negU_integral_gM_rpow_le`), whose negative moments
are bounded by `C₁`. -/
theorem negU_integral_nM_rpow_le (hX : IsZeroBoundaryGFFOn openSquare X P) {γ p : ℝ}
    (hp : p ≤ 0) {K : Set ℂ} (hKU : K ⊆ openSquare) {cK : ℝ} (hcK : 0 ≤ cK)
    (hK : ∀ {z w : ℂ} {r : ℝ}, 0 < r → closedBall z r ⊆ K → closedBall w r ⊆ K →
      |cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w r); P] +
        Real.log (max r ‖z - w‖)| ≤ cK)
    {z₁ : ℂ} {m₁ : ℕ} {c₁ C₁ : ℝ} (hc₁ : LogCorr (bZ γ X z₁ m₁) P (γ ^ 2) c₁)
    (hC₁ : ∀ k j : ℕ, k ≤ j → ∫ ω, gM (bZ γ X z₁ m₁ k) P j (grid j) ω ^ p ∂P ≤ C₁)
    {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K)
    (k j : ℕ) (hkj : k ≤ j) {v : ℂ} (hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq) :
    ∫ ω, nM γ X z₀ m k j v ω ^ p ∂P ≤
      Real.exp (-(γ ^ 2 * cK / 2)) ^ p * (Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK) / 2) *
        (Real.exp (p * (p - 1) * (γ ^ 2 * (cK + |Real.log (radius m)|) + c₁) / 2) * C₁)) := by
  have hc := negU_logCorr_bZ hX γ hKU hK hQ
  refine (integral_nM_rpow_le hX hKU hcK hK hQ hc hp k j hv).trans ?_
  gcongr
  exact (negU_integral_gM_rpow_le hc hc₁ hp k j).trans
    (mul_le_mul_of_nonneg_left (hC₁ k j hkj) (Real.exp_pos _).le)

end DZZ

end LQGMetric
