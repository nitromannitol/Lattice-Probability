/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Strip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′: the shape of `S_ρ = G(D̄_ρ)` (node S12a, the parts used)

With `k = (1−ρ²)/(1+ρ²)` and `w = u + iv`, `|v| < π/2`:
`|T(w)| ≤ ρ ⇔ cos v ≥ k cosh u`. Hence over `|u| ≤ U₀` (where `k cosh U₀ < 1`), `S_ρ` is the
region `|v| ≤ g(u) := arccos(k cosh u)` between the two graphs `v = ±g(u)`, whose points are
`G(ρ e^{±iθ})` with `θ ∈ [θ₁, π − θ₁]`, `θ₁ = arccos c₀`,
`c₀ = (Q−1)/(Q+1) · (1+ρ²)/(2ρ)`, `Q = e^{2U₀}`. Own elementary computation (D-DDDF-14).
-/

namespace LQGMetric.DDDF.L12

open Set Real

/-- The profile `g(u) = arccos(k cosh u)` of `S_ρ`. -/
noncomputable def gProf (k u : ℝ) : ℝ := Real.arccos (k * Real.cosh u)

lemma two_exp_mul_cosh (u : ℝ) : 2 * Real.exp u * Real.cosh u = Real.exp u ^ 2 + 1 := by
  rw [Real.cosh_eq, Real.exp_neg]; field_simp

/-- `cos v ≥ k cosh u ⇒ |T(u+iv)| ≤ ρ`. -/
theorem norm_sT_le {ρ : ℝ} (hρ0 : 0 < ρ) {w : ℂ} (hw : |w.im| < π / 2)
    (hc : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh w.re ≤ Real.cos w.im) : ‖sT w‖ ≤ ρ := by
  obtain ⟨-, -, hn⟩ := sT_parts w hw
  have hE := Real.exp_pos w.re
  have hcp := cos_pos_of_abs_lt hw
  have h2 := two_exp_mul_cosh w.re
  have key : (1 - ρ ^ 2) * (Real.exp w.re ^ 2 + 1) ≤
      2 * Real.exp w.re * Real.cos w.im * (1 + ρ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * Real.exp w.re * (1 + ρ ^ 2))
    have e : (1 - ρ ^ 2) * (2 * Real.exp w.re * Real.cosh w.re) = 2 * Real.exp w.re *
        (1 + ρ ^ 2) * ((1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh w.re) := by field_simp
    rw [← h2]; linarith
  have hD : 0 < Real.exp w.re ^ 2 + 2 * Real.exp w.re * Real.cos w.im + 1 := by positivity
  have : Complex.normSq (sT w) ≤ ρ ^ 2 := by
    rw [hn, div_le_iff₀ hD]; nlinarith
  rw [Complex.normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (sT w)]

/-- On the boundary graphs: `cos v = k cosh u ⇒ |T(u+iv)| = ρ`, and the bound on `Re T`. -/
theorem sT_on_boundary {ρ U₀ : ℝ} (hρ0 : 0 < ρ) {w : ℂ} (hw : |w.im| < π / 2)
    (hu : |w.re| ≤ U₀)
    (hc : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh w.re = Real.cos w.im) :
    ‖sT w‖ = ρ ∧ |(sT w).re| ≤
      (Real.exp (2 * U₀) - 1) / (Real.exp (2 * U₀) + 1) * ((1 + ρ ^ 2) / (2 * ρ)) * ρ := by
  obtain ⟨hre, -, hn⟩ := sT_parts w hw
  set E := Real.exp w.re
  set Q := Real.exp (2 * U₀)
  have hE : 0 < E := Real.exp_pos _
  have hcp := cos_pos_of_abs_lt hw
  have h2 := two_exp_mul_cosh w.re
  have key : (1 - ρ ^ 2) * (E ^ 2 + 1) = 2 * E * Real.cos w.im * (1 + ρ ^ 2) := by
    have e : (1 - ρ ^ 2) * (2 * E * Real.cosh w.re) = 2 * E *
        (1 + ρ ^ 2) * ((1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh w.re) := by field_simp
    rw [hc] at e; rw [← h2]; linarith
  have hD : 0 < E ^ 2 + 2 * E * Real.cos w.im + 1 := by positivity
  have hDe : E ^ 2 + 2 * E * Real.cos w.im + 1 = (E ^ 2 + 1) * 2 / (1 + ρ ^ 2) := by
    field_simp; linarith
  refine ⟨?_, ?_⟩
  · have : Complex.normSq (sT w) = ρ ^ 2 := by
      rw [hn, div_eq_iff hD.ne']; linear_combination key
    rw [Complex.normSq_eq_norm_sq] at this
    nlinarith [norm_nonneg (sT w)]
  · have hEQ : E ^ 2 ≤ Q := by
      rw [← Real.exp_nat_mul]; push_cast
      exact Real.exp_le_exp.2 (by linarith [le_abs_self w.re])
    have hQE : 1 ≤ Q * E ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast
      exact Real.one_le_exp (by linarith [neg_abs_le w.re])
    have hQ : 0 < Q := Real.exp_pos _
    have habs : |E ^ 2 - 1| * (Q + 1) ≤ (Q - 1) * (E ^ 2 + 1) := by
      rcases abs_cases (E ^ 2 - 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    rw [hre, abs_div, abs_of_pos hD, div_le_iff₀ hD, hDe]
    have : (Q - 1) / (Q + 1) * ((1 + ρ ^ 2) / (2 * ρ)) * ρ * ((E ^ 2 + 1) * 2 / (1 + ρ ^ 2)) =
        (Q - 1) * (E ^ 2 + 1) / (Q + 1) := by field_simp
    rw [this, le_div_iff₀ (by linarith)]; exact habs

/-- A point of the circle `|ζ| = ρ` in the upper half-plane with `|Re ζ| ≤ c₀ ρ` is
`ρ e^{iθ}` with `θ ∈ [arccos c₀, π − arccos c₀]`. -/
theorem exists_angle {ρ c₀ : ℝ} (hρ0 : 0 < ρ) {ζ : ℂ} (hn : ‖ζ‖ = ρ) (hi : 0 ≤ ζ.im)
    (hr : |ζ.re| ≤ c₀ * ρ) :
    ∃ θ ∈ Icc (Real.arccos c₀) (π - Real.arccos c₀), ζ = (ρ : ℂ) * Complex.exp (θ * Complex.I) := by
  have hζ : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hn; linarith
  refine ⟨Complex.arg ζ, ?_, ?_⟩
  · have h0 : 0 ≤ Complex.arg ζ := Complex.arg_nonneg_iff.2 hi
    have hπ := Complex.arg_le_pi ζ
    have hcos : Real.cos (Complex.arg ζ) = ζ.re / ρ := by rw [Complex.cos_arg hζ, hn]
    have hb : |Real.cos (Complex.arg ζ)| ≤ c₀ := by
      rw [hcos, abs_div, abs_of_pos hρ0, div_le_iff₀ hρ0]; exact hr
    have e := Real.arccos_cos h0 hπ
    constructor
    · rw [← e]; exact antitone_arccos (le_trans (le_abs_self _) hb)
    · rw [← Real.arccos_neg, ← e]; apply antitone_arccos
      linarith [neg_abs_le (Real.cos (Complex.arg ζ))]
  · rw [← hn]; exact (Complex.norm_mul_exp_arg_mul_I ζ).symm

end LQGMetric.DDDF.L12
