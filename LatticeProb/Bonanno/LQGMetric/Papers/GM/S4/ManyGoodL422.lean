/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodL422 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGood
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# GM Lemma 4.22, deterministic core: chaining Hölder bounds around a circle

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.22
(`lem-holder-balls0`, statement l. 2527–2535, proof l. 2541–2565): "We can cover
`∂B_{2λ₄ε𝕣}(z)` by a `λ₄`-dependent constant number of Euclidean balls … By summing
(4.40) over all such balls …, the `D_h(·,·; 𝓑^•_{s_{k+1}} ∖ cl B_{ε𝕣}(z))`-diameter of
`∂B_{2λ₄ε𝕣}(z)` is at most a constant times `ε^χ 𝔠_𝕣 e^{ξh_𝕣(𝕫)}`."

We follow GM's covering argument with consecutive points `u_j` of the circle at mutual distance
`≤ e/4` (`e = ε𝕣`) along the arc from `u₀` to `u` (`N = ⌈8πρ/e⌉` steps, `ρ = 2λ₄e`) in place
of GM's balls `B_{e/2}(w)`: the Hölder upper bound of `ℰ_𝕣` (condition 3) is the internal bound
`D(u,v; B_{2|u−v|}(u)) ≤ (|u−v|/𝕣)^χ S`, and `B_{2|u−v|}(u) ⊆ B_{e/2}(u)` avoids
`cl B_e(z)` because `ρ ≥ 2e` (`λ₄ ≥ 1`). (GM's bound (4.40) for `u, v ∈ B_{e/2}(w)` inside
`B_e(w)` does not follow literally from condition 3, whose balls `B_{2|u−v|}(u)` can leave
`B_e(w)`; the consecutive-point version avoids this.)

* `gm_internal_chain` — `d(f 0, f N) ≤ N b` if consecutive internal distances are `≤ b`.
* `gm_L4_22_circle` — the deterministic core: if `D(𝕫, u₀; V) ≤ T` for one point `u₀` of the
  circle `∂B_ρ(z)` and `B_{e/2}(u) ⊆ Y` for every `u` on the circle, then every `u` on the circle
  has `D(𝕫, u; V) ≤ T + N (e/(4𝕣))^χ S`, `V = Y ∖ cl B_e(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- chaining internal distances -/
theorem gm_internal_chain (D : ContMetric) (V : Set ℂ) (f : ℕ → ℂ) (b : ℝ≥0∞) (N : ℕ)
    (hN : 1 ≤ N) (hf : ∀ j < N, D.internal V (f j) (f (j + 1)) ≤ b) :
    D.internal V (f 0) (f N) ≤ N * b := by
  induction N, hN using Nat.le_induction with
  | base => simpa using hf 0 one_pos
  | succ n hn ih =>
    have h1 := ih (fun j hj => hf j (by omega))
    have h2 := hf n (by omega)
    calc D.internal V (f 0) (f (n + 1))
        ≤ D.internal V (f 0) (f n) + D.internal V (f n) (f (n + 1)) :=
          MetricGeometry.internalEDist_triangle _ _ _ _
      _ ≤ n * b + b := add_le_add h1 h2
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * b := by push_cast; ring

/-- `‖e^{ia} − e^{ib}‖ ≤ |a − b|` -/
theorem gm_norm_exp_I_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have h : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
      Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))

theorem gm_internal_anti (D : ContMetric) {U V : Set ℂ} (hUV : U ⊆ V) (x y : ℂ) :
    D.internal V x y ≤ D.internal U x y :=
  MetricGeometry.internalEDist_anti (image_mono hUV) _ _

theorem gm_internal_self (D : ContMetric) {V : Set ℂ} {x : ℂ} (hx : x ∈ V) :
    D.internal V x x = 0 :=
  MetricGeometry.internalEDist_self (mem_image_of_mem _ hx)

/-- **GM Lemma 4.22, deterministic core** (l. 2549–2565): chaining the Hölder bound around the
circle `∂B_ρ(z)`, `ρ ≥ 2e`, inside `V = Y ∖ cl B_e(z)`. -/
theorem gm_L4_22_circle (D : ContMetric) {z 𝕫 u₀ : ℂ} {ρ e 𝕣 χ S T : ℝ} {Y : Set ℂ}
    (he : 0 < e) (hρ : 2 * e ≤ ρ) (h𝕣 : 0 < 𝕣) (hχ : 0 < χ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hHol : ∀ u ∈ sphere z ρ, ∀ v ∈ sphere z ρ, u ≠ v → ‖u - v‖ ≤ e / 4 →
      D.internal (ball u (2 * ‖u - v‖)) u v ≤ ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ χ * S))
    (hY : ∀ u ∈ sphere z ρ, ball u (e / 2) ⊆ Y)
    (hu₀ : u₀ ∈ sphere z ρ) (h0 : D.internal (Y \ closedBall z e) 𝕫 u₀ ≤ ENNReal.ofReal T) :
    ∀ u ∈ sphere z ρ, D.internal (Y \ closedBall z e) 𝕫 u ≤
      ENNReal.ofReal (T + ⌈8 * Real.pi * ρ / e⌉₊ * ((e / 4 / 𝕣) ^ χ * S)) := by
  intro u hu
  set V := Y \ closedBall z e with hV
  have hρ0 : 0 < ρ := by linarith
  set N := ⌈8 * Real.pi * ρ / e⌉₊ with hN
  have hNpos : 0 < (N : ℝ) := by
    have : 0 < 8 * Real.pi * ρ / e := by positivity
    exact this.trans_le (Nat.le_ceil _)
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  -- angles
  set θ₀ := Complex.arg (u₀ - z)
  set θ₁ := Complex.arg (u - z)
  have hpolar : ∀ x ∈ sphere z ρ,
      x = z + (ρ : ℂ) * Complex.exp (Complex.I * (Complex.arg (x - z) : ℂ)) := by
    intro x hx
    rw [mem_sphere_iff_norm] at hx
    have := Complex.norm_mul_exp_arg_mul_I (x - z)
    rw [hx, mul_comm Complex.I] at *
    rw [this]; ring
  set f : ℕ → ℂ := fun j =>
    z + (ρ : ℂ) * Complex.exp (Complex.I * ((θ₀ + j * (θ₁ - θ₀) / N : ℝ) : ℂ)) with hf
  have hf0 : f 0 = u₀ := by
    simp only [hf, CharP.cast_eq_zero, zero_mul, zero_div, add_zero]
    exact (hpolar u₀ hu₀).symm
  have hfN : f N = u := by
    simp only [hf]
    rw [mul_div_cancel_left₀ _ hNpos.ne', add_sub_cancel]
    exact (hpolar u hu).symm
  have hfs : ∀ j, f j ∈ sphere z ρ := by
    intro j
    rw [mem_sphere_iff_norm]
    simp only [hf, add_sub_cancel_left, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hθ : |θ₁ - θ₀| ≤ 2 * Real.pi := by
    have h1 := Complex.neg_pi_lt_arg (u - z)
    have h2 := Complex.arg_le_pi (u - z)
    have h3 := Complex.neg_pi_lt_arg (u₀ - z)
    have h4 := Complex.arg_le_pi (u₀ - z)
    rw [abs_le]; constructor <;> linarith
  have hstep_d : ∀ j, ‖f j - f (j + 1)‖ ≤ e / 4 := by
    intro j
    have : f j - f (j + 1) = (ρ : ℂ) * (Complex.exp (Complex.I * ((θ₀ + j * (θ₁ - θ₀) / N : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((θ₀ + ((j + 1 : ℕ) : ℝ) * (θ₁ - θ₀) / N : ℝ) : ℂ))) := by
      simp only [hf]; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    refine (mul_le_mul_of_nonneg_left (gm_norm_exp_I_sub_le _ _) hρ0.le).trans ?_
    have hdiff : θ₀ + j * (θ₁ - θ₀) / N - (θ₀ + ((j + 1 : ℕ) : ℝ) * (θ₁ - θ₀) / N) =
        -((θ₁ - θ₀) / N) := by push_cast; ring
    rw [hdiff, abs_neg, abs_div, abs_of_pos hNpos]
    have hNge : 8 * Real.pi * ρ / e ≤ N := Nat.le_ceil _
    rw [div_le_iff₀ he] at hNge
    rw [mul_div_assoc', div_le_iff₀ hNpos]
    nlinarith [Real.pi_pos, abs_nonneg (θ₁ - θ₀)]
  have hball : ∀ x ∈ sphere z ρ, ball x (e / 2) ⊆ V := by
    intro x hx y hy
    refine ⟨hY x hx hy, fun hyc => ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hyc
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_sphere_iff_norm] at hx
    have : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev x y] at this
    linarith
  have hstep : ∀ j < N, D.internal V (f j) (f (j + 1)) ≤
      ENNReal.ofReal ((e / 4 / 𝕣) ^ χ * S) := by
    intro j _
    by_cases hj : f j = f (j + 1)
    · rw [← hj, gm_internal_self D (hball _ (hfs j) (mem_ball_self (by linarith)))]
      exact zero_le
    · have hd := hstep_d j
      have hpos : 0 < ‖f j - f (j + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hj)
      refine (gm_internal_anti D ?_ _ _).trans ((hHol _ (hfs j) _ (hfs (j + 1)) hj hd).trans ?_)
      · exact (ball_subset_ball (by linarith)).trans (hball _ (hfs j))
      · apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hS
        apply Real.rpow_le_rpow (by positivity) _ hχ.le
        exact div_le_div_of_nonneg_right hd h𝕣.le
  have hchain := gm_internal_chain D V f _ N hN1 hstep
  rw [hf0, hfN] at hchain
  calc D.internal V 𝕫 u ≤ D.internal V 𝕫 u₀ + D.internal V u₀ u :=
        MetricGeometry.internalEDist_triangle _ _ _ _
    _ ≤ ENNReal.ofReal T + N * ENNReal.ofReal ((e / 4 / 𝕣) ^ χ * S) := add_le_add h0 hchain
    _ = _ := by
        rw [ENNReal.ofReal_add hT (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

end LQGMetric.GM
