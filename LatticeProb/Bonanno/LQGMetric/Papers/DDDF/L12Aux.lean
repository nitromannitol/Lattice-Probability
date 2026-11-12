/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Aux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Tgt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′: auxiliary choices (parameter `ρ`, arc subdivision, Möbius estimates)

Own elementary arguments (decision D-B4, D-DDDF-14): the choice of `ρ` close to `1`, the
subdivision of the angle range `[θ₁, π − θ₁]` into `m` equal pieces (DF: "divide the marked arcs
into `m` subarcs of, say, equal length", `LiouvilleMetricStarScale.tex` l. 646), and the uniform
Lipschitz estimate showing that `mob` moves a whole piece next to `±ρ` (S12b).
-/

namespace LQGMetric.DDDF.L12

open Set Real Metric Filter Topology

/-- Choice of `ρ`: the source profile is defined over `|u| ≤ U₀`, the angle threshold is `< 1`,
and `G` sends a `(1−ρ)`-neighbourhood of `±ρ` beyond `Re = ±X`. -/
theorem exists_rho (U₀ X : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1 ∧
      cZero ρ U₀ < 1 ∧ Real.exp X ≤ ρ / (1 - ρ) := by
  have h1 : ∀ᶠ ρ in 𝓝 (1 : ℝ), (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1 := by
    have hc : ContinuousAt (fun ρ : ℝ => (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀) 1 :=
      ContinuousAt.mul (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
        continuousAt_const
    exact Filter.Tendsto.eventually_lt_const (by norm_num) hc.tendsto
  have hQ : 0 < Real.exp (2 * U₀) := Real.exp_pos _
  have h2 : ∀ᶠ ρ in 𝓝 (1 : ℝ), cZero ρ U₀ < 1 := by
    have hc : ContinuousAt (fun ρ : ℝ => cZero ρ U₀) 1 := by
      unfold cZero
      exact ContinuousAt.mul continuousAt_const
        (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
    refine Filter.Tendsto.eventually_lt_const ?_ hc.tendsto
    simp only [cZero]
    rw [show (1 + (1 : ℝ) ^ 2) / (2 * 1) = 1 by norm_num, mul_one, div_lt_one (by linarith)]
    linarith
  have h3 : ∀ᶠ ρ in 𝓝 (1 : ℝ), Real.exp X / (1 + Real.exp X) < ρ := by
    apply lt_mem_nhds
    rw [div_lt_one (by positivity)]; linarith
  have h4 : ∀ᶠ ρ in 𝓝 (1 : ℝ), 0 < ρ := lt_mem_nhds one_pos
  obtain ⟨ρ, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ :=
    ((((h1.and h2).and h3).and h4).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Iio 1)).exists
  refine ⟨ρ, h4, h5, h1, h2, ?_⟩
  have h5' : (0 : ℝ) < 1 - ρ := by linarith [show ρ < 1 from h5]
  rw [le_div_iff₀ h5']
  rw [div_lt_iff₀ (by positivity)] at h3
  nlinarith

/-- Subdivision of `[a, a + mΔ]` into `m` pieces. -/
theorem exists_piece {m : ℕ} (hm : 1 ≤ m) {a Δ θ : ℝ} (hΔ : 0 ≤ Δ)
    (hθ : θ ∈ Icc a (a + m * Δ)) :
    ∃ i : Fin m, θ ∈ Icc (a + (i : ℕ) * Δ) (a + ((i : ℕ) + 1) * Δ) := by
  rcases hΔ.eq_or_lt with h0 | h0
  · refine ⟨⟨0, hm⟩, ?_⟩
    rw [← h0] at hθ ⊢; simp only [mul_zero, add_zero] at hθ ⊢; exact hθ
  · set n := ⌊(θ - a) / Δ⌋₊
    have hq : 0 ≤ (θ - a) / Δ := div_nonneg (by linarith [hθ.1]) h0.le
    refine ⟨⟨min n (m - 1), by omega⟩, ?_, ?_⟩
    · have h1 : ((min n (m - 1) : ℕ) : ℝ) ≤ (θ - a) / Δ :=
        (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hq)
      rw [le_div_iff₀ h0] at h1; simp only; linarith
    · simp only
      rcases le_or_gt n (m - 1) with hn | hn
      · rw [min_eq_left hn]
        have := Nat.lt_floor_add_one ((θ - a) / Δ)
        rw [div_lt_iff₀ h0] at this; linarith
      · rw [min_eq_right hn.le, Nat.cast_sub hm, Nat.cast_one, sub_add_cancel]
        exact hθ.2

lemma norm_exp_sub_exp_le (θ φ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ ≤ |θ - φ| := by
  have : Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I) =
      Complex.exp (φ * Complex.I) * (Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact (norm_exp_I_mul_ofReal_sub_one_le).trans (by rw [Real.norm_eq_abs])

lemma norm_mobR_le {ρ β κ : ℝ} (hρ0 : 0 < ρ) (hβ : |Real.sin β| < Real.cos β) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ ρ) : ‖mobR ρ β κ ζ‖ ≤ ρ := by
  have h1 : ‖ζ / ρ‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ0.le, div_le_one hρ0]; exact hζ
  rw [mobR, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
  have := norm_mob_le_one (κ := κ) hβ h1
  nlinarith

/-- S12b, the estimate: a point `ρe^{iθ}` is moved within `ρ L |θ − φ|` of `ρ · mob(e^{iφ})`. -/
theorem mobR_near {ρ β κ θ φ L : ℝ} (hρ0 : 0 < ρ) (hβ : |Real.sin β| < Real.cos β)
    (hL : 2 / (Real.cos β - |Real.sin β|) ≤ L) :
    ‖mobR ρ β κ ((ρ : ℂ) * Complex.exp (θ * Complex.I)) -
        (ρ : ℂ) * mob β κ (Complex.exp (φ * Complex.I))‖ ≤ ρ * (L * |θ - φ|) := by
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ0.ne'
  rw [mobR, mul_div_cancel_left₀ _ hρc, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hρ0.le]
  gcongr
  calc _ ≤ 2 / (Real.cos β - |Real.sin β|) *
        ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ :=
        norm_mob_sub_le hβ (Complex.norm_exp_ofReal_mul_I θ).le
          (Complex.norm_exp_ofReal_mul_I φ).le
    _ ≤ L * |θ - φ| := mul_le_mul hL (norm_exp_sub_exp_le θ φ) (norm_nonneg _)
        ((div_pos two_pos (by linarith)).le.trans hL)

/-- Real and imaginary parts of `F(α(G ζ)) = e + (b'/π) G(M ζ)`. -/
lemma F_parts (a' b' : ℝ) (ξ : ℂ) :
    (((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) + ((b' / π : ℝ) : ℂ) * sG ξ).re =
        a' / 2 + b' / π * (sG ξ).re ∧
      (((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) + ((b' / π : ℝ) : ℂ) * sG ξ).im =
        b' / 2 + b' / π * (sG ξ).im := by
  constructor <;> simp

end LQGMetric.DDDF.L12
