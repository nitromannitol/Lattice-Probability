import Mathlib
import LatticeProb.Prob.MvbeRegularClass

/-!
# Bentkus smoothing for a regular class (Raic, Lemma 2.1)

Packet P9 of the staged formalisation of Raic's Theorem 1.3 (A multivariate Berry-Esseen theorem
with explicit constants, arXiv:1802.06475).  For a regular class `C : MvbeRegularClass m κ`
(assumptions (A1)-(A8)), `A ∈ C.cls` and `ε > 0`:

* `mvbeG`: Raic's profile `g` (`1` on `(-∞, 0]`, `1 - 2x²` on `[0, 1/2]`, `2 (1 - x)²` on
  `[1/2, 1]`, `0` on `[1, ∞)`); `mvbeG_spec` collects its properties (`C¹`, `|g'| ≤ 2`, `g'`
  `4`-Lipschitz, `|g'(t)| ≤ 4t`, `1 - g(t) ≤ 2t²`).
* `MvbeRegularClass.smoothOuter C A ε = g (ρ_A / ε)` is `f_A^{ε}`; `MvbeRegularClass.smoothInner`
  is `f_A^{-ε}` (`0` if `A^{-ε|ρ} = ∅`, `f_{A^{-ε|ρ}}^{ε}` otherwise, `1` if `A^{-ε|ρ} = ℝ^d`).
* `MvbeRegularClass.raic_lemma_2_1` bundles Lemma 2.1 (1)-(5); the pieces are
  `smoothOuter_*`, `smoothInner_*` (values, `C¹`, `‖∇f‖ ≤ 2/ε`, `∇f` is `4(1+κ)/ε²`-Lipschitz,
  level sets in `cls ∪ {∅, ℝ^d}`, sandwich `1_A ≤ f_A^{ε} ≤ 1_{A^{ε|ρ}}`,
  `1_{A^{-ε|ρ}} ≤ f_A^{-ε} ≤ 1_A`) and the second-derivative support statements
  `ae_iteratedFDeriv_two_*`, `ae_norm_iteratedFDeriv_two_*_le`.

**Extra hypothesis `MvbeNegOpen C`.**  (A1)-(A8) as stated do *not* imply that `g (ρ_A / ε)` is
`C¹` (see `MvbeNegOpen`); one needs that each `{ρ_A < 0}` is open, e.g. `ρ_A` continuous.  This
holds for the rounded orthants (`mvbeRoundedRegularClass_negOpen`).  Everything else comes from
(A2)-(A4), (A7), (A8).

**Second derivative.**  The statement "`∇²f = 0` outside `A^{ε|ρ} \ A`" is true only almost
everywhere: for the class of closed balls `B(c, s)` with `ρ = ‖· - c‖ - s`, the set `A = {c}` has
`f = 1 - 2‖· - c‖²/ε²` near `c ∈ A`, so `∇²f(c) ≠ 0`.  The proof of the a.e. statement uses
Lebesgue's density theorem (`mvbe_fderiv_eq_zero_of_density`).
-/

open MeasureTheory Filter Topology Asymptotics Metric
open scoped Pointwise

namespace LatticeProb

section Profile

/-- **Raic's piecewise quadratic profile** `g` (Lemma 2.1): `g = 1` on `(-∞, 0]`, `1 - 2x²` on
`[0, 1/2]`, `2 (1 - x)²` on `[1/2, 1]` and `0` on `[1, ∞)`, written in the smooth-friendly form
`g x = 1 - 2 (x₊)² + 4 ((x - 1/2)₊)² - 2 ((x - 1)₊)²`. -/
noncomputable def mvbeG (x : ℝ) : ℝ :=
  1 - 2 * max x 0 ^ 2 + 4 * max (x - 1 / 2) 0 ^ 2 - 2 * max (x - 1) 0 ^ 2

/-- The derivative `g'` of the profile `mvbeG`: `0` on `(-∞, 0]`, `-4x` on `[0, 1/2]`, `-4 (1 - x)`
on `[1/2, 1]`, `0` on `[1, ∞)`. -/
noncomputable def mvbeGd (x : ℝ) : ℝ :=
  -(4 * max x 0) + 8 * max (x - 1 / 2) 0 - 4 * max (x - 1) 0

theorem mvbeG_of_nonpos {x : ℝ} (hx : x ≤ 0) : mvbeG x = 1 := by
  have h1 : max x 0 = 0 := max_eq_right hx
  have h2 : max (x - 1 / 2) 0 = 0 := max_eq_right (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  rw [mvbeG, h1, h2, h3]
  ring

theorem mvbeG_of_Icc_zero_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    mvbeG x = 1 - 2 * x ^ 2 := by
  have h2 : max (x - 1 / 2) 0 = 0 := max_eq_right (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  rw [mvbeG, max_eq_left h0, h2, h3]
  ring

theorem mvbeG_of_Icc_half_one {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 1) :
    mvbeG x = 2 * (1 - x) ^ 2 := by
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  rw [mvbeG, max_eq_left (by linarith : (0 : ℝ) ≤ x),
    max_eq_left (by linarith : (0 : ℝ) ≤ x - 1 / 2), h3]
  ring

theorem mvbeG_of_one_le {x : ℝ} (hx : 1 ≤ x) : mvbeG x = 0 := by
  rw [mvbeG, max_eq_left (by linarith : (0 : ℝ) ≤ x),
    max_eq_left (by linarith : (0 : ℝ) ≤ x - 1 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ x - 1)]
  ring

theorem mvbeGd_of_nonpos {x : ℝ} (hx : x ≤ 0) : mvbeGd x = 0 := by
  have h1 : max x 0 = 0 := max_eq_right hx
  have h2 : max (x - 1 / 2) 0 = 0 := max_eq_right (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  rw [mvbeGd, h1, h2, h3]
  ring

theorem mvbeGd_of_Icc_zero_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    mvbeGd x = -(4 * x) := by
  have h2 : max (x - 1 / 2) 0 = 0 := max_eq_right (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  rw [mvbeGd, max_eq_left h0, h2, h3]
  ring

theorem mvbeGd_of_Icc_half_one {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 1) :
    mvbeGd x = -(4 * (1 - x)) := by
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  rw [mvbeGd, max_eq_left (by linarith : (0 : ℝ) ≤ x),
    max_eq_left (by linarith : (0 : ℝ) ≤ x - 1 / 2), h3]
  ring

theorem mvbeGd_of_one_le {x : ℝ} (hx : 1 ≤ x) : mvbeGd x = 0 := by
  rw [mvbeGd, max_eq_left (by linarith : (0 : ℝ) ≤ x),
    max_eq_left (by linarith : (0 : ℝ) ≤ x - 1 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ x - 1)]
  ring

theorem mvbeG_cases (x : ℝ) :
    x ≤ 0 ∨ (0 ≤ x ∧ x ≤ 1 / 2) ∨ (1 / 2 ≤ x ∧ x ≤ 1) ∨ 1 ≤ x := by
  rcases le_total x 0 with h | h
  · exact Or.inl h
  rcases le_total x (1 / 2) with h' | h'
  · exact Or.inr (Or.inl ⟨h, h'⟩)
  rcases le_total x 1 with h'' | h''
  · exact Or.inr (Or.inr (Or.inl ⟨h', h''⟩))
  · exact Or.inr (Or.inr (Or.inr h''))

/-- `g` is differentiable with derivative `mvbeGd` everywhere. -/
theorem mvbeG_hasDerivAt (x : ℝ) : HasDerivAt mvbeG (mvbeGd x) x := by
  have h0 := mvbe_hasDerivAt_sq_max x
  have h1 : HasDerivAt (fun r : ℝ => (max (r - 1 / 2) 0) ^ 2) (2 * max (x - 1 / 2) 0) x :=
    HasDerivAt.comp_sub_const x (1 / 2) (mvbe_hasDerivAt_sq_max (x - 1 / 2))
  have h2 : HasDerivAt (fun r : ℝ => (max (r - 1) 0) ^ 2) (2 * max (x - 1) 0) x :=
    HasDerivAt.comp_sub_const x 1 (mvbe_hasDerivAt_sq_max (x - 1))
  have h := (((hasDerivAt_const x (1 : ℝ)).sub (h0.const_mul 2)).add (h1.const_mul 4)).sub
    (h2.const_mul 2)
  refine h.congr_deriv ?_
  unfold mvbeGd
  ring


theorem mvbeG_nonneg (x : ℝ) : 0 ≤ mvbeG x := by
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeG_of_nonpos h]; norm_num
  · rw [mvbeG_of_Icc_zero_half h0 h1]; nlinarith
  · rw [mvbeG_of_Icc_half_one h0 h1]; positivity
  · rw [mvbeG_of_one_le h]

theorem mvbeG_le_one (x : ℝ) : mvbeG x ≤ 1 := by
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeG_of_nonpos h]
  · rw [mvbeG_of_Icc_zero_half h0 h1]; nlinarith [sq_nonneg x]
  · rw [mvbeG_of_Icc_half_one h0 h1]; nlinarith
  · rw [mvbeG_of_one_le h]; norm_num

theorem mvbeGd_nonpos (x : ℝ) : mvbeGd x ≤ 0 := by
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeGd_of_nonpos h]
  · rw [mvbeGd_of_Icc_zero_half h0 h1]; linarith
  · rw [mvbeGd_of_Icc_half_one h0 h1]; linarith
  · rw [mvbeGd_of_one_le h]

/-- `|g'| ≤ 2`. -/
theorem mvbeGd_abs_le (x : ℝ) : |mvbeGd x| ≤ 2 := by
  rw [abs_of_nonpos (mvbeGd_nonpos x)]
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeGd_of_nonpos h]; norm_num
  · rw [mvbeGd_of_Icc_zero_half h0 h1]; linarith
  · rw [mvbeGd_of_Icc_half_one h0 h1]; linarith
  · rw [mvbeGd_of_one_le h]; norm_num

/-- `|g'(t)| ≤ 4 t` for `t ≥ 0`: the estimate used against the `1 / min ρ` factor of (A8). -/
theorem mvbeGd_abs_le_mul {x : ℝ} (hx : 0 ≤ x) : |mvbeGd x| ≤ 4 * x := by
  rw [abs_of_nonpos (mvbeGd_nonpos x)]
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeGd_of_nonpos h]; linarith
  · rw [mvbeGd_of_Icc_zero_half h0 h1]; linarith
  · rw [mvbeGd_of_Icc_half_one h0 h1]; linarith
  · rw [mvbeGd_of_one_le h]; linarith

theorem mvbeGd_eq_min (x : ℝ) : mvbeGd x = -4 * max 0 (min x (1 - x)) := by
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeGd_of_nonpos h, min_eq_left (by linarith), max_eq_left h]; ring
  · rw [mvbeGd_of_Icc_zero_half h0 h1, min_eq_left (by linarith), max_eq_right h0]; ring
  · rw [mvbeGd_of_Icc_half_one h0 h1, min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [mvbeGd_of_one_le h, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

/-- **`g'` is Lipschitz with constant 4** (`M₂(g) = 4`). -/
theorem mvbeGd_sub_abs_le (x y : ℝ) : |mvbeGd x - mvbeGd y| ≤ 4 * |x - y| := by
  rw [mvbeGd_eq_min, mvbeGd_eq_min]
  have h1 : |min x (1 - x) - min y (1 - y)| ≤ |x - y| := by
    refine (abs_min_sub_min_le_max x (1 - x) y (1 - y)).trans ?_
    refine max_le le_rfl ?_
    rw [show (1 - x) - (1 - y) = -(x - y) by ring, abs_neg]
  have h2 : |max 0 (min x (1 - x)) - max 0 (min y (1 - y))| ≤ |x - y| := by
    rw [max_comm 0 (min x (1 - x)), max_comm 0 (min y (1 - y))]
    exact (abs_max_sub_max_le_abs _ _ _).trans h1
  calc |-4 * max 0 (min x (1 - x)) - -4 * max 0 (min y (1 - y))|
      = 4 * |max 0 (min x (1 - x)) - max 0 (min y (1 - y))| := by
        rw [show -4 * max 0 (min x (1 - x)) - -4 * max 0 (min y (1 - y))
            = -4 * (max 0 (min x (1 - x)) - max 0 (min y (1 - y))) by ring, abs_mul]
        norm_num
    _ ≤ 4 * |x - y| := by linarith

/-- The key quadratic inequality `1 - g(t) ≤ 2 t²` for `t ≥ 0`, which gives differentiability of
`g (ρ / ε)` across `{ρ = 0}`. -/
theorem mvbeG_one_sub_le {x : ℝ} (hx : 0 ≤ x) : 1 - mvbeG x ≤ 2 * x ^ 2 := by
  rcases mvbeG_cases x with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h
  · rw [mvbeG_of_nonpos h]; nlinarith [sq_nonneg x]
  · rw [mvbeG_of_Icc_zero_half h0 h1]; linarith
  · rw [mvbeG_of_Icc_half_one h0 h1]; nlinarith [sq_nonneg (2 * x - 1)]
  · rw [mvbeG_of_one_le h]; nlinarith

theorem mvbeG_differentiable : Differentiable ℝ mvbeG :=
  fun x => (mvbeG_hasDerivAt x).differentiableAt

theorem mvbeG_deriv (x : ℝ) : deriv mvbeG x = mvbeGd x := (mvbeG_hasDerivAt x).deriv

theorem mvbeGd_continuous : Continuous mvbeGd := by
  unfold mvbeGd
  fun_prop

/-- **(1) The profile `g` is `C¹`** (its derivative is `mvbeGd`, see `mvbeG_hasDerivAt`). The
remaining properties are `mvbeG_nonneg`, `mvbeG_le_one`, `mvbeGd_abs_le` (`|g'| ≤ 2`),
`mvbeGd_sub_abs_le` (`g'` is `4`-Lipschitz), `mvbeG_of_nonpos` and `mvbeG_of_one_le`. -/
theorem mvbeG_contDiff : ContDiff ℝ 1 mvbeG := by
  rw [contDiff_one_iff_deriv]
  refine ⟨mvbeG_differentiable, ?_⟩
  have : deriv mvbeG = mvbeGd := funext mvbeG_deriv
  rw [this]
  exact mvbeGd_continuous

/-- `g` is `2`-Lipschitz (`M₁(g) = 2`). -/
theorem mvbeG_sub_abs_le (x y : ℝ) : |mvbeG x - mvbeG y| ≤ 2 * |x - y| := by
  have hL : LipschitzWith 2 mvbeG := by
    refine lipschitzWith_of_nnnorm_deriv_le mvbeG_differentiable fun t => ?_
    rw [mvbeG_deriv]
    have := mvbeGd_abs_le t
    rw [← NNReal.coe_le_coe]
    simpa using this
  have := hL.dist_le_mul x y
  simpa [Real.dist_eq] using this

/-- Level sets of `g`: for `u ∈ (0, 1)` there is `s ∈ (0, 1)` with `{t | u ≤ g t} = (-∞, s]`. -/
theorem mvbeG_levelSet {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ t : ℝ, u ≤ mvbeG t ↔ t ≤ s := by
  rcases le_or_gt (1 / 2) u with hu | hu
  · set s : ℝ := √((1 - u) / 2) with hs
    have hpos : 0 < (1 - u) / 2 := by linarith
    have hs2 : s ^ 2 = (1 - u) / 2 := Real.sq_sqrt hpos.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos
    have hshalf : s ≤ 1 / 2 := by nlinarith
    refine ⟨s, hs0, by linarith, fun t => ?_⟩
    rcases mvbeG_cases t with h | ⟨h0', h1'⟩ | ⟨h0', h1'⟩ | h
    · rw [mvbeG_of_nonpos h]; constructor <;> intro _ <;> linarith
    · rw [mvbeG_of_Icc_zero_half h0' h1']
      rw [← sq_le_sq₀ h0' hs0.le, hs2]
      constructor <;> intro _ <;> linarith
    · rw [mvbeG_of_Icc_half_one h0' h1']
      constructor
      · intro hh; nlinarith
      · intro hh; nlinarith
    · rw [mvbeG_of_one_le h]; constructor <;> intro _ <;> linarith
  · set r : ℝ := √(u / 2) with hr
    have hpos : 0 < u / 2 := by linarith
    have hr2 : r ^ 2 = u / 2 := Real.sq_sqrt hpos.le
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hrhalf : r < 1 / 2 := by nlinarith
    refine ⟨1 - r, by linarith, by linarith, fun t => ?_⟩
    rcases mvbeG_cases t with h | ⟨h0', h1'⟩ | ⟨h0', h1'⟩ | h
    · rw [mvbeG_of_nonpos h]; constructor <;> intro _ <;> linarith
    · rw [mvbeG_of_Icc_zero_half h0' h1']
      constructor <;> intro _ <;> nlinarith
    · rw [mvbeG_of_Icc_half_one h0' h1']
      have h1t : 0 ≤ 1 - t := by linarith
      have hiff : u ≤ 2 * (1 - t) ^ 2 ↔ r ^ 2 ≤ (1 - t) ^ 2 := by
        rw [hr2]; constructor <;> intro _ <;> linarith
      rw [hiff, sq_le_sq₀ hr0.le h1t]
      constructor <;> intro _ <;> linarith
    · rw [mvbeG_of_one_le h]; constructor <;> intro _ <;> linarith

/-- **(1) The profile `g`**: `g` is `C¹`; `0 ≤ g ≤ 1`; `|g'| ≤ 2`; `g'` is `4`-Lipschitz;
`g = 1` on `(-∞, 0]`; `g = 0` on `[1, ∞)`; `|g'(t)| ≤ 4 t` for `t ≥ 0`; and the quadratic bound
`1 - g(t) ≤ 2 t²` for `t ≥ 0` (which gives differentiability of `g (ρ / ε)` across `{ρ = 0}`). -/
theorem mvbeG_spec :
    ContDiff ℝ 1 mvbeG ∧ (∀ x, 0 ≤ mvbeG x ∧ mvbeG x ≤ 1) ∧ (∀ x, |deriv mvbeG x| ≤ 2) ∧
    (∀ x y, |deriv mvbeG x - deriv mvbeG y| ≤ 4 * |x - y|) ∧ (∀ x, x ≤ 0 → mvbeG x = 1) ∧
    (∀ x, 1 ≤ x → mvbeG x = 0) ∧ (∀ x, 0 ≤ x → |deriv mvbeG x| ≤ 4 * x) ∧
    (∀ x, 0 ≤ x → 1 - mvbeG x ≤ 2 * x ^ 2) := by
  refine ⟨mvbeG_contDiff, fun x => ⟨mvbeG_nonneg x, mvbeG_le_one x⟩, fun x => ?_, fun x y => ?_,
    fun x hx => mvbeG_of_nonpos hx, fun x hx => mvbeG_of_one_le hx, fun x hx => ?_,
    fun x hx => mvbeG_one_sub_le hx⟩
  · rw [mvbeG_deriv]; exact mvbeGd_abs_le x
  · rw [mvbeG_deriv, mvbeG_deriv]; exact mvbeGd_sub_abs_le x y
  · rw [mvbeG_deriv]; exact mvbeGd_abs_le_mul hx

end Profile

theorem mvbe_iteratedFDeriv_two_const {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    iteratedFDeriv ℝ 2 (fun _ : EuclideanSpace ℝ (Fin m) => c) x = 0 := by
  rw [iteratedFDeriv_const_of_ne two_ne_zero]
  rfl

theorem mvbe_norm_le_indicator {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} {a : ℝ} {T : Set (EuclideanSpace ℝ (Fin m))}
    (hb : ‖iteratedFDeriv ℝ 2 f x‖ ≤ a) (hz : x ∉ T → iteratedFDeriv ℝ 2 f x = 0) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ a * T.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ T
  · rw [Set.indicator_of_mem hx, mul_one]
    exact hb
  · rw [Set.indicator_of_notMem hx, mul_zero, hz hx, norm_zero]

section Density

/-- **Derivative vanishes at density points.**  If `F = 0` on `S`, `x ∈ S`, and `S` has Lebesgue
density `1` at `x`, then `fderiv ℝ F x = 0` (junk value `0` if `F` is not differentiable at
`x`). -/
theorem mvbe_fderiv_eq_zero_of_density {m : ℕ} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : EuclideanSpace ℝ (Fin m) → G} {S : Set (EuclideanSpace ℝ (Fin m))}
    {x : EuclideanSpace ℝ (Fin m)} (hxS : x ∈ S) (hF : ∀ y ∈ S, F y = 0)
    (hdens : Tendsto (fun r => volume (S ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    fderiv ℝ F x = 0 := by
  classical
  by_cases hd : DifferentiableAt ℝ F x
  swap
  · exact fderiv_zero_of_not_differentiableAt hd
  by_contra hL
  set L := fderiv ℝ F x with hLdef
  have hFx : F x = 0 := hF x hxS
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hL (ContinuousLinearMap.ext hcon)
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hLv : 0 < ‖L v‖ := norm_pos_iff.2 hv
  set η : ℝ := ‖L v‖ / (2 * ‖v‖) with hη
  have hηpos : 0 < η := by positivity
  set K : Set (EuclideanSpace ℝ (Fin m)) := {w | η * ‖w‖ < ‖L w‖} with hK
  have hKopen : IsOpen K :=
    isOpen_lt (continuous_const.mul continuous_norm) (continuous_norm.comp L.continuous)
  have hlo := hd.hasFDerivAt.isLittleO
  have hev : ∀ᶠ y in 𝓝 x, ‖F y - F x - L (y - x)‖ ≤ η * ‖y - x‖ := hlo.def hηpos
  obtain ⟨r₀, hr₀, hr₀'⟩ := Metric.eventually_nhds_iff.1 hev
  -- notation
  set N : ENNReal := volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) with hN
  set P : ENNReal := volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1 ∩ K) with hP
  have hNpos : 0 < N := measure_ball_pos _ _ one_pos
  have hNtop : N ≠ ⊤ := measure_ball_lt_top.ne
  -- the cone has positive relative measure
  have hPpos : 0 < P := by
    refine IsOpen.measure_pos _ (isOpen_ball.inter hKopen) ?_
    refine ⟨(1 / (2 * ‖v‖)) • v, ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
      norm_num
    · show η * ‖(1 / (2 * ‖v‖)) • v‖ < ‖L ((1 / (2 * ‖v‖)) • v)‖
      rw [map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : η * (1 / (2 * ‖v‖) * ‖v‖) < 1 / (2 * ‖v‖) * ‖L v‖ := by
        rw [hη]
        field_simp
        nlinarith
      exact this
  -- key measure inequality for small radii
  have hkey : ∀ r : ℝ, 0 < r → r < r₀ →
      volume (S ∩ closedBall x r) / volume (closedBall x r) + P / N ≤ 1 := by
    intro r hr hrr
    have hw0 : ENNReal.ofReal (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ≠ 0 := by
      simp [hr]
    have hwtop : ENNReal.ofReal (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    set w : ENNReal := ENNReal.ofReal (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) with hw
    have hcb : volume (closedBall x r) = w * N := Measure.addHaar_closedBall volume x hr.le
    -- the cone piece
    have hsubc : Continuous (fun y : EuclideanSpace ℝ (Fin m) => y - x) :=
      continuous_id.sub continuous_const
    set T : Set (EuclideanSpace ℝ (Fin m)) :=
      (fun y => y - x) ⁻¹' ball (0 : EuclideanSpace ℝ (Fin m)) r ∩ (fun y => y - x) ⁻¹' K
      with hT
    have hTmeas : MeasurableSet T :=
      (isOpen_ball.preimage hsubc).measurableSet.inter (hKopen.preimage hsubc).measurableSet
    have hTsub : T ⊆ closedBall x r := fun y hy => by
      have := hy.1
      simp only [Set.mem_preimage, mem_ball, dist_zero_right] at this
      rw [mem_closedBall, dist_eq_norm]; exact this.le
    have hTmeasure : volume T = w * P := by
      have h1 : T = (fun y => y + -x) ⁻¹' (ball (0 : EuclideanSpace ℝ (Fin m)) r ∩ K) := by
        ext y
        simp only [hT, Set.mem_inter_iff, Set.mem_preimage, sub_eq_add_neg]
      have h2 : ball (0 : EuclideanSpace ℝ (Fin m)) r ∩ K
          = r • (ball (0 : EuclideanSpace ℝ (Fin m)) 1 ∩ K) := by
        ext y
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
        simp only [Set.mem_inter_iff, mem_ball, dist_zero_right, hK, Set.mem_setOf_eq, map_smul,
          norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rw [inv_mul_lt_iff₀ hr]; simpa using h1
          · have := mul_lt_mul_of_pos_left h2 (inv_pos.2 hr)
            calc η * (r⁻¹ * ‖y‖) = r⁻¹ * (η * ‖y‖) := by ring
              _ < r⁻¹ * ‖L y‖ := this
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rw [inv_mul_lt_iff₀ hr] at h1; simpa using h1
          · have h3 : r⁻¹ * (η * ‖y‖) < r⁻¹ * ‖L y‖ := by
              calc r⁻¹ * (η * ‖y‖) = η * (r⁻¹ * ‖y‖) := by ring
                _ < r⁻¹ * ‖L y‖ := h2
            exact lt_of_mul_lt_mul_left h3 (inv_pos.2 hr).le
      rw [h1, measure_preimage_add_right, h2, Measure.addHaar_smul, abs_of_pos (by positivity)]
    have hdisj : Disjoint (S ∩ closedBall x r) T := by
      refine Set.disjoint_left.2 fun y hyS hyT => ?_
      have hyd : dist y x < r₀ := by
        have := mem_closedBall.1 hyS.2
        linarith
      have h1 := hr₀' hyd
      rw [hF y hyS.1, hFx, zero_sub_zero, zero_sub, norm_neg] at h1
      exact absurd hyT.2 (not_lt.2 h1)
    have hsum : volume (S ∩ closedBall x r) + w * P ≤ w * N := by
      rw [← hTmeasure, ← measure_union hdisj hTmeas, ← hcb]
      exact measure_mono (Set.union_subset Set.inter_subset_right hTsub)
    rw [hcb]
    have hq : P / N = (w * P) / (w * N) := (ENNReal.mul_div_mul_left P N hw0 hwtop).symm
    rw [hq, ENNReal.div_add_div_same]
    exact ENNReal.div_le_of_le_mul (by simpa using hsum)
  -- pass to the limit
  have hlim := hdens.add_const (P / N)
  have hle : (1 : ENNReal) + P / N ≤ 1 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    exact hkey r hr.1 hr.2
  have hq0 : P / N = 0 := by
    have : (1 : ENNReal) + P / N ≤ 1 + 0 := by simpa using hle
    exact le_antisymm ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 this) zero_le
  rw [ENNReal.div_eq_zero_iff] at hq0
  rcases hq0 with h0 | h0
  · exact hPpos.ne' h0
  · exact hNtop h0


/-- If `F` vanishes on a measurable set `S`, then `fderiv F` vanishes at almost every point of
`S` (Lebesgue's density theorem). -/
theorem mvbe_ae_fderiv_eq_zero_on {m : ℕ} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : EuclideanSpace ℝ (Fin m) → G} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : MeasurableSet S) (hF : ∀ y ∈ S, F y = 0) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))), x ∈ S → fderiv ℝ F x = 0 := by
  have h := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (EuclideanSpace ℝ (Fin m))) S
  rw [ae_restrict_iff' hS] at h
  filter_upwards [h] with x hx hxS
  exact mvbe_fderiv_eq_zero_of_density hxS hF (hx hxS)

end Density

section Smooth

variable {m : ℕ}

/-- The analytic content of Raic's (A4), (A7), (A8) for a single function `ρ = ρ_A`, plus the
openness of `{ρ < 0}` (which holds when `ρ` is continuous). -/
structure MvbeDistLike (κ : ℝ) (ρ : EuclideanSpace ℝ (Fin m) → ℝ) : Prop where
  kappa_nonneg : 0 ≤ κ
  neg_open : IsOpen {x | ρ x < 0}
  nonexp : ∀ x y, 0 ≤ ρ x → 0 ≤ ρ y → |ρ x - ρ y| ≤ ‖x - y‖
  differentiableAt : ∀ x, 0 < ρ x → DifferentiableAt ℝ ρ x
  gradient_sub_le : ∀ x y, 0 < ρ x → 0 < ρ y →
    ‖gradient ρ x - gradient ρ y‖ ≤ κ * ‖x - y‖ / min (ρ x) (ρ y)

/-- The smoothing `f = g (ρ / ε)`. -/
noncomputable def mvbeSmooth (ρ : EuclideanSpace ℝ (Fin m) → ℝ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  mvbeG (ρ x / ε)

theorem mvbe_iteratedFDeriv_two_eq_zero {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} (h : fderiv ℝ (fderiv ℝ f) x = 0) :
    iteratedFDeriv ℝ 2 f x = 0 := by
  ext v
  rw [iteratedFDeriv_two_apply, h]
  simp

theorem mvbe_norm_iteratedFDeriv_two (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ :=
  (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 1)).symm.trans
    (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f))

/-- A function with `|f y - f x| ≤ C ‖y - x‖²` is differentiable at `x` with derivative `0`. -/
theorem mvbe_hasFDerivAt_zero_of_sq_bound {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} {C : ℝ} (h : ∀ y, ‖f y - f x‖ ≤ C * ‖y - x‖ ^ 2) :
    HasFDerivAt f (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun v : EuclideanSpace ℝ (Fin m) =>
      f (x + v) - f x - (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) v)
      =O[𝓝 0] fun v => ‖v‖ ^ 2 := by
    refine IsBigO.of_bound C (Eventually.of_forall fun v => ?_)
    have := h (x + v)
    simp only [zero_apply, sub_zero, add_sub_cancel_left] at this ⊢
    rw [Real.norm_eq_abs (‖v‖ ^ 2), abs_of_nonneg (sq_nonneg _)]
    exact this
  exact h1.trans_isLittleO (isLittleO_norm_pow_id (by norm_num))

namespace MvbeDistLike

variable {κ : ℝ} {ρ : EuclideanSpace ℝ (Fin m) → ℝ} (h : MvbeDistLike κ ρ) {ε : ℝ}

include h in
theorem isOpen_pos : IsOpen {x | 0 < ρ x} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  exact ((h.differentiableAt x hx).continuousAt.eventually (lt_mem_nhds hx))

include h in
/-- `‖∇ρ‖ ≤ 1` on `{ρ > 0}`, from non-expansiveness (A7). -/
theorem norm_fderiv_le {x : EuclideanSpace ℝ (Fin m)} (hx : 0 < ρ x) : ‖fderiv ℝ ρ x‖ ≤ 1 := by
  have hL : LipschitzOnWith 1 ρ {y | 0 < ρ y} := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have := h.nonexp a b (le_of_lt ha) (le_of_lt hb)
    simpa [Real.dist_eq, dist_eq_norm] using this
  have := norm_fderiv_le_of_lipschitzOn ℝ (h.isOpen_pos.mem_nhds hx) hL
  simpa using this

theorem smooth_eq_one {x : EuclideanSpace ℝ (Fin m)} (hε : 0 < ε) (hx : ρ x ≤ 0) :
    mvbeSmooth ρ ε x = 1 :=
  mvbeG_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hε.le)

theorem smooth_eq_zero {x : EuclideanSpace ℝ (Fin m)} (hε : 0 < ε) (hx : ε ≤ ρ x) :
    mvbeSmooth ρ ε x = 0 :=
  mvbeG_of_one_le ((one_le_div hε).2 hx)

theorem smooth_nonneg (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ mvbeSmooth ρ ε x :=
  mvbeG_nonneg _

theorem smooth_le_one (x : EuclideanSpace ℝ (Fin m)) : mvbeSmooth ρ ε x ≤ 1 :=
  mvbeG_le_one _

include h in
/-- On `{ρ > 0}`, `f = g (ρ / ε)` has derivative `(g'(ρ/ε) / ε) ∇ρ`. -/
theorem smooth_hasFDerivAt_pos {x : EuclideanSpace ℝ (Fin m)} (hx : 0 < ρ x) :
    HasFDerivAt (mvbeSmooth ρ ε) ((mvbeGd (ρ x / ε) / ε) • fderiv ℝ ρ x) x := by
  have hρ : HasFDerivAt ρ (fderiv ℝ ρ x) x := (h.differentiableAt x hx).hasFDerivAt
  have hρ' : HasFDerivAt (fun y => ρ y / ε) (ε⁻¹ • fderiv ℝ ρ x) x := by
    have := hρ.const_smul ε⁻¹
    refine this.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun y => by simp [div_eq_inv_mul]
  have := (mvbeG_hasDerivAt (ρ x / ε)).comp_hasFDerivAt x hρ'
  exact this.congr_fderiv (by rw [smul_smul, div_eq_mul_inv (mvbeGd (ρ x / ε)) ε])

include h in
/-- At a point with `ρ ≤ 0` the smoothing `f = g (ρ / ε)` is differentiable with derivative `0`.
For `ρ x < 0` this uses the openness of `{ρ < 0}`; for `ρ x = 0` the quadratic inequality
`1 - g t ≤ 2 t²` together with the non-expansiveness (A7) of `ρ` on `{ρ ≥ 0}`. -/
theorem smooth_hasFDerivAt_nonpos {x : EuclideanSpace ℝ (Fin m)} (hε : 0 < ε) (hx : ρ x ≤ 0) :
    HasFDerivAt (mvbeSmooth ρ ε) (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) x := by
  rcases hx.lt_or_eq with hx | hx
  · have hev : ∀ᶠ y in 𝓝 x, ρ y < 0 := h.neg_open.mem_nhds hx
    have : mvbeSmooth ρ ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with y hy using smooth_eq_one hε hy.le
    exact (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq this
  · refine mvbe_hasFDerivAt_zero_of_sq_bound (C := 2 / ε ^ 2) fun y => ?_
    have hfx : mvbeSmooth ρ ε x = 1 := smooth_eq_one hε hx.le
    rw [hfx]
    by_cases hy : ρ y ≤ 0
    · rw [smooth_eq_one hε hy]
      simp only [sub_self, norm_zero]
      positivity
    · have hy' : 0 < ρ y := not_le.1 hy
      have hρy : ρ y ≤ ‖y - x‖ := by
        have := h.nonexp y x hy'.le hx.ge
        rw [hx, sub_zero, abs_of_pos hy'] at this
        exact this
      have h1 : 1 - mvbeG (ρ y / ε) ≤ 2 * (ρ y / ε) ^ 2 :=
        mvbeG_one_sub_le (div_nonneg hy'.le hε.le)
      have h2 : ‖mvbeSmooth ρ ε y - 1‖ = 1 - mvbeG (ρ y / ε) := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [smooth_le_one (ρ := ρ) (ε := ε) y] :
          mvbeSmooth ρ ε y - 1 ≤ 0)]
        unfold mvbeSmooth
        ring
      rw [h2]
      have h3 : ρ y / ε ≤ ‖y - x‖ / ε := div_le_div_of_nonneg_right hρy hε.le
      calc 1 - mvbeG (ρ y / ε) ≤ 2 * (ρ y / ε) ^ 2 := h1
        _ ≤ 2 * (‖y - x‖ / ε) ^ 2 := by gcongr
        _ = 2 / ε ^ 2 * ‖y - x‖ ^ 2 := by field_simp

include h in
theorem fderiv_smooth_nonpos {x : EuclideanSpace ℝ (Fin m)} (hε : 0 < ε) (hx : ρ x ≤ 0) :
    fderiv ℝ (mvbeSmooth ρ ε) x = 0 :=
  (h.smooth_hasFDerivAt_nonpos hε hx).fderiv

include h in
theorem fderiv_smooth_pos {x : EuclideanSpace ℝ (Fin m)} (hx : 0 < ρ x) :
    fderiv ℝ (mvbeSmooth ρ ε) x = (mvbeGd (ρ x / ε) / ε) • fderiv ℝ ρ x :=
  (h.smooth_hasFDerivAt_pos hx).fderiv

include h in
/-- `f = g (ρ / ε)` is differentiable everywhere. -/
theorem differentiable_smooth (hε : 0 < ε) : Differentiable ℝ (mvbeSmooth ρ ε) := fun x => by
  rcases le_or_gt (ρ x) 0 with hx | hx
  · exact (h.smooth_hasFDerivAt_nonpos hε hx).differentiableAt
  · exact (h.smooth_hasFDerivAt_pos hx).differentiableAt

include h in
theorem norm_fderiv_smooth_le_rho (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)} (hx : 0 < ρ x) :
    ‖fderiv ℝ (mvbeSmooth ρ ε) x‖ ≤ 4 * ρ x / ε ^ 2 := by
  rw [h.fderiv_smooth_pos hx, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hε]
  calc |mvbeGd (ρ x / ε)| / ε * ‖fderiv ℝ ρ x‖ ≤ (4 * (ρ x / ε)) / ε * 1 := by
        gcongr
        · exact mvbeGd_abs_le_mul (div_nonneg hx.le hε.le)
        · exact h.norm_fderiv_le hx
    _ = 4 * ρ x / ε ^ 2 := by field_simp

include h in
/-- **`M₁ f ≤ 2 / ε`**: the gradient of `f = g (ρ / ε)` has norm at most `2 / ε`. -/
theorem norm_fderiv_smooth_le (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (mvbeSmooth ρ ε) x‖ ≤ 2 / ε := by
  rcases le_or_gt (ρ x) 0 with hx | hx
  · rw [h.fderiv_smooth_nonpos hε hx, norm_zero]
    positivity
  · rw [h.fderiv_smooth_pos hx, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hε]
    calc |mvbeGd (ρ x / ε)| / ε * ‖fderiv ℝ ρ x‖ ≤ 2 / ε * 1 := by
          gcongr
          · exact mvbeGd_abs_le _
          · exact h.norm_fderiv_le hx
      _ = 2 / ε := mul_one _

include h in
/-- Raic's estimate on `{ρ > 0}` (case `ρ y ≤ ρ x`): `‖∇f x - ∇f y‖ ≤ 4 (1 + κ) ε⁻² ‖x - y‖`. -/
theorem fderiv_smooth_sub_le_of_le (hε : 0 < ε) {x y : EuclideanSpace ℝ (Fin m)}
    (hx : 0 < ρ x) (hy : 0 < ρ y) (hyx : ρ y ≤ ρ x) :
    ‖fderiv ℝ (mvbeSmooth ρ ε) x - fderiv ℝ (mvbeSmooth ρ ε) y‖
      ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ := by
  have hdecomp : fderiv ℝ (mvbeSmooth ρ ε) x - fderiv ℝ (mvbeSmooth ρ ε) y
      = ((mvbeGd (ρ x / ε) - mvbeGd (ρ y / ε)) / ε) • fderiv ℝ ρ x
        + (mvbeGd (ρ y / ε) / ε) • (fderiv ℝ ρ x - fderiv ℝ ρ y) := by
    rw [h.fderiv_smooth_pos hx, h.fderiv_smooth_pos hy]
    module
  have hg : ‖fderiv ℝ ρ x - fderiv ℝ ρ y‖ = ‖gradient ρ x - gradient ρ y‖ := by
    simp only [gradient, ← map_sub, LinearIsometryEquiv.norm_map]
  have hgrad : ‖fderiv ℝ ρ x - fderiv ℝ ρ y‖ ≤ κ * ‖x - y‖ / ρ y := by
    rw [hg]
    have := h.gradient_sub_le x y hx hy
    rwa [min_eq_right hyx] at this
  have hab : |ρ x / ε - ρ y / ε| ≤ ‖x - y‖ / ε := by
    rw [← sub_div, abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right (h.nonexp x y hx.le hy.le) hε.le
  have hN : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hT1 : ‖((mvbeGd (ρ x / ε) - mvbeGd (ρ y / ε)) / ε) • fderiv ℝ ρ x‖
      ≤ 4 * ‖x - y‖ / ε ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hε]
    calc |mvbeGd (ρ x / ε) - mvbeGd (ρ y / ε)| / ε * ‖fderiv ℝ ρ x‖
        ≤ (4 * (‖x - y‖ / ε)) / ε * 1 := by
          gcongr
          · exact (mvbeGd_sub_abs_le _ _).trans (by gcongr)
          · exact h.norm_fderiv_le hx
      _ = 4 * ‖x - y‖ / ε ^ 2 := by field_simp
  have hT2 : ‖(mvbeGd (ρ y / ε) / ε) • (fderiv ℝ ρ x - fderiv ℝ ρ y)‖
      ≤ 4 * κ * ‖x - y‖ / ε ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hε]
    calc |mvbeGd (ρ y / ε)| / ε * ‖fderiv ℝ ρ x - fderiv ℝ ρ y‖
        ≤ (4 * (ρ y / ε)) / ε * (κ * ‖x - y‖ / ρ y) := by
          gcongr
          exact mvbeGd_abs_le_mul (div_nonneg hy.le hε.le)
      _ = 4 * κ * ‖x - y‖ / ε ^ 2 := by field_simp
  rw [hdecomp]
  calc _ ≤ ‖((mvbeGd (ρ x / ε) - mvbeGd (ρ y / ε)) / ε) • fderiv ℝ ρ x‖
        + ‖(mvbeGd (ρ y / ε) / ε) • (fderiv ℝ ρ x - fderiv ℝ ρ y)‖ := norm_add_le _ _
    _ ≤ 4 * ‖x - y‖ / ε ^ 2 + 4 * κ * ‖x - y‖ / ε ^ 2 := add_le_add hT1 hT2
    _ = 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ := by ring

include h in
/-- If `ρ x ≤ 0 < ρ y`, the segment from `x` to `y` contains a point `z` with `ρ z = 0`
(connectedness of the segment and openness of `{ρ < 0}` and `{ρ > 0}`). -/
theorem exists_rho_eq_zero_on_segment {x y : EuclideanSpace ℝ (Fin m)} (hx : ρ x ≤ 0)
    (hy : 0 < ρ y) : ∃ z ∈ segment ℝ x y, ρ z = 0 := by
  rcases hx.lt_or_eq with hx | hx
  · by_contra hne
    push Not at hne
    have hdisj : Disjoint {z | ρ z < 0} {z | 0 < ρ z} := by
      refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
      exact absurd (lt_trans (show 0 < ρ z from hz2) (show ρ z < 0 from hz1)) (lt_irrefl _)
    have hsub : segment ℝ x y ⊆ {z | ρ z < 0} ∪ {z | 0 < ρ z} := fun z hz =>
      (lt_or_gt_of_ne (hne z hz)).imp id id
    rcases (convex_segment x y).isPreconnected.subset_or_subset h.neg_open h.isOpen_pos hdisj
      hsub with hs | hs
    · exact absurd (hs (right_mem_segment ℝ x y)) (not_lt.2 hy.le)
    · exact absurd (hs (left_mem_segment ℝ x y)) (not_lt.2 hx.le)
  · exact ⟨x, left_mem_segment ℝ x y, hx⟩

theorem norm_sub_le_of_mem_segment {x y z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ segment ℝ x y) :
    ‖y - z‖ ≤ ‖y - x‖ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  have hb' : b = 1 - a := by linarith
  subst hb'
  have : y - (a • x + (1 - a) • y) = a • (y - x) := by module
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

include h in
/-- **`M₂ f ≤ 4 (1 + κ) / ε²`**: `∇f` is Lipschitz with constant `4 (1 + κ) / ε²` on all of `E`.
(Raic's proof: the estimate on `{ρ > 0}` via (A7), (A8) and `|g'(t)| ≤ 4t`, and the points
`x` with `ρ x ≤ 0` via a zero of `ρ` on the segment.) -/
theorem fderiv_smooth_sub_le (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (mvbeSmooth ρ ε) x - fderiv ℝ (mvbeSmooth ρ ε) y‖
      ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ := by
  have hK : 4 / ε ^ 2 ≤ 4 * (1 + κ) / ε ^ 2 := by
    have := h.kappa_nonneg
    gcongr
    linarith
  -- the mixed case, `ρ x ≤ 0 < ρ y`
  have mixed : ∀ x y : EuclideanSpace ℝ (Fin m), ρ x ≤ 0 → 0 < ρ y →
      ‖fderiv ℝ (mvbeSmooth ρ ε) x - fderiv ℝ (mvbeSmooth ρ ε) y‖
        ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ := by
    intro x y hx hy
    obtain ⟨z, hz, hz0⟩ := h.exists_rho_eq_zero_on_segment hx hy
    have hρy : ρ y ≤ ‖y - x‖ := by
      have h1 := h.nonexp y z hy.le hz0.ge
      rw [hz0, sub_zero, abs_of_pos hy] at h1
      exact h1.trans (norm_sub_le_of_mem_segment hz)
    rw [h.fderiv_smooth_nonpos hε hx, zero_sub, norm_neg]
    calc ‖fderiv ℝ (mvbeSmooth ρ ε) y‖ ≤ 4 * ρ y / ε ^ 2 := h.norm_fderiv_smooth_le_rho hε hy
      _ ≤ 4 * ‖y - x‖ / ε ^ 2 := by gcongr
      _ = 4 / ε ^ 2 * ‖x - y‖ := by rw [norm_sub_rev]; ring
      _ ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ := by gcongr
  rcases le_or_gt (ρ x) 0 with hx | hx
  · rcases le_or_gt (ρ y) 0 with hy | hy
    · rw [h.fderiv_smooth_nonpos hε hx, h.fderiv_smooth_nonpos hε hy, sub_self, norm_zero]
      have := h.kappa_nonneg
      positivity
    · exact mixed x y hx hy
  · rcases le_or_gt (ρ y) 0 with hy | hy
    · rw [norm_sub_rev, norm_sub_rev x y]
      exact mixed y x hy hx
    · rcases le_total (ρ y) (ρ x) with hyx | hxy
      · exact h.fderiv_smooth_sub_le_of_le hε hx hy hyx
      · rw [norm_sub_rev, norm_sub_rev x y]
        exact h.fderiv_smooth_sub_le_of_le hε hy hx hxy

include h in
theorem lipschitzWith_fderiv_smooth (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (4 * (1 + κ) / ε ^ 2)) (fderiv ℝ (mvbeSmooth ρ ε)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hκ := h.kappa_nonneg
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  exact h.fderiv_smooth_sub_le hε x y

include h in
/-- **`f = g (ρ / ε)` is `C¹`** (differentiable everywhere, with continuous, indeed Lipschitz,
gradient), including across `∂A = {ρ = 0}`. -/
theorem contDiff_smooth (hε : 0 < ε) : ContDiff ℝ 1 (mvbeSmooth ρ ε) := by
  rw [contDiff_one_iff_fderiv]
  exact ⟨h.differentiable_smooth hε, (h.lipschitzWith_fderiv_smooth hε).continuous⟩

include h in
/-- `f = g (ρ / ε)` is `(2 / ε)`-Lipschitz. -/
theorem smooth_sub_abs_le (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin m)) :
    |mvbeSmooth ρ ε x - mvbeSmooth ρ ε y| ≤ 2 / ε * ‖x - y‖ := by
  have hL : LipschitzWith (Real.toNNReal (2 / ε)) (mvbeSmooth ρ ε) := by
    refine lipschitzWith_of_nnnorm_fderiv_le (h.differentiable_smooth hε) fun z => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    exact h.norm_fderiv_smooth_le hε z
  have := hL.dist_le_mul x y
  rwa [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm] at this

include h in
/-- Near a point with `ρ < 0` or `ρ > ε` the gradient `∇f` vanishes identically. -/
theorem fderiv_smooth_eventuallyEq_zero (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ρ x < 0 ∨ ε < ρ x) :
    fderiv ℝ (mvbeSmooth ρ ε) =ᶠ[𝓝 x] fun _ => (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := by
  rcases hx with hx | hx
  · have hev : ∀ᶠ y in 𝓝 x, ρ y < 0 := h.neg_open.mem_nhds hx
    filter_upwards [hev] with y hy using h.fderiv_smooth_nonpos hε hy.le
  · have hpos : 0 < ρ x := lt_trans hε hx
    have hev : ∀ᶠ y in 𝓝 x, ε < ρ y :=
      (h.differentiableAt x hpos).continuousAt.eventually (lt_mem_nhds hx)
    filter_upwards [hev] with y hy
    have hy0 : 0 < ρ y := lt_trans hε hy
    rw [h.fderiv_smooth_pos hy0, mvbeGd_of_one_le ((one_le_div hε).2 hy.le), zero_div, zero_smul]

include h in
/-- The gradient `∇f` vanishes outside `{0 < ρ < ε}`. -/
theorem fderiv_smooth_eq_zero_of_not_mem (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ¬ (0 < ρ x ∧ ρ x < ε)) : fderiv ℝ (mvbeSmooth ρ ε) x = 0 := by
  rcases le_or_gt (ρ x) 0 with h0 | h0
  · exact h.fderiv_smooth_nonpos hε h0
  · have hε' : ε ≤ ρ x := by
      by_contra hc
      exact hx ⟨h0, not_le.1 hc⟩
    rw [h.fderiv_smooth_pos h0, mvbeGd_of_one_le ((one_le_div hε).2 hε'), zero_div, zero_smul]

include h in
/-- `‖∇²f‖ ≤ 4 (1 + κ) / ε²` at every point (with the convention `∇²f = 0` where `∇f` is not
differentiable). -/
theorem norm_iteratedFDeriv_two_smooth_le (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    ‖iteratedFDeriv ℝ 2 (mvbeSmooth ρ ε) x‖ ≤ 4 * (1 + κ) / ε ^ 2 := by
  have hκ := h.kappa_nonneg
  rw [mvbe_norm_iteratedFDeriv_two]
  have := norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) (h.lipschitzWith_fderiv_smooth hε)
  rwa [Real.coe_toNNReal _ (by positivity)] at this

include h in
/-- Where `ρ < 0` or `ρ > ε`, the second derivative of `f` vanishes (`∇f` is locally `0`). -/
theorem iteratedFDeriv_two_smooth_eq_zero_of_far (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ρ x < 0 ∨ ε < ρ x) : iteratedFDeriv ℝ 2 (mvbeSmooth ρ ε) x = 0 := by
  refine mvbe_iteratedFDeriv_two_eq_zero ?_
  rw [(h.fderiv_smooth_eventuallyEq_zero hε hx).fderiv_eq, fderiv_fun_const]
  rfl

include h in
/-- **Second-derivative support, almost everywhere.**  For Lebesgue-a.e. `x` outside
`{0 < ρ < ε}`, `∇²f (x) = 0`.  (Lebesgue's density theorem for the measurable set
`{ρ ≤ 0} ∪ {ρ ≥ ε}` on which `∇f` vanishes.) -/
theorem ae_iteratedFDeriv_two_smooth_eq_zero (hε : 0 < ε) (hρ : Measurable ρ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ¬ (0 < ρ x ∧ ρ x < ε) → iteratedFDeriv ℝ 2 (mvbeSmooth ρ ε) x = 0 := by
  have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin m) | ¬ (0 < ρ x ∧ ρ x < ε)} :=
    ((measurableSet_lt measurable_const hρ).inter (measurableSet_lt hρ measurable_const)).compl
  filter_upwards [mvbe_ae_fderiv_eq_zero_on (F := fderiv ℝ (mvbeSmooth ρ ε)) hS
    (fun y hy => h.fderiv_smooth_eq_zero_of_not_mem hε hy)] with x hx hxS
  exact mvbe_iteratedFDeriv_two_eq_zero (hx hxS)

include h in
/-- **`‖∇²f‖ ≤ 4 (1 + κ) ε⁻² 1_{0 < ρ < ε}` almost everywhere.** -/
theorem ae_norm_iteratedFDeriv_two_smooth_le (hε : 0 < ε) (hρ : Measurable ρ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ‖iteratedFDeriv ℝ 2 (mvbeSmooth ρ ε) x‖
        ≤ 4 * (1 + κ) / ε ^ 2 * {y | 0 < ρ y ∧ ρ y < ε}.indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [h.ae_iteratedFDeriv_two_smooth_eq_zero hε hρ] with x hx
  by_cases hxm : 0 < ρ x ∧ ρ x < ε
  · rw [Set.indicator_of_mem (show x ∈ {y | 0 < ρ y ∧ ρ y < ε} from hxm), mul_one]
    exact h.norm_iteratedFDeriv_two_smooth_le hε x
  · rw [hx hxm, norm_zero, Set.indicator_of_notMem (show x ∉ {y | 0 < ρ y ∧ ρ y < ε} from hxm),
      mul_zero]

end MvbeDistLike

end Smooth

section ClassLevel

variable {m : ℕ} {κ : ℝ}

/-- **Extra regularity hypothesis** on a regular class: each `{ρ_A < 0}` (`A ∈ cls`) is open.
It holds as soon as each `ρ_A` is continuous (`mvbeNegOpen_of_continuous`), in particular for the
signed-distance classes.  It is needed for the `C¹` property of the smoothing `g (ρ_A / ε)` at
points with `ρ_A < 0`.  It cannot be derived from (A1)-(A8): a class of closed balls
`B(c, s)` (`s ≥ 0`) with `ρ_{B(c,s)} = ‖· - c‖ - s` for `s > 0` and `ρ_{{c}}(c) = -1`,
`ρ_{{c}}(y) = 1 + ψ(‖y - c‖)` otherwise (`ψ(r) = r²/2` on `[0, 1]`, `r - 1/2` after) satisfies
(A1)-(A8) with `κ = 2`, but then `g (ρ_{{c}} / ε)` is the indicator of the point `c` for `ε < 1`
(this counterexample is not formalised here). -/
def MvbeNegOpen (C : MvbeRegularClass m κ) : Prop :=
  ∀ A ∈ C.cls, IsOpen {x | C.rho A x < 0}

theorem mvbeNegOpen_of_continuous (C : MvbeRegularClass m κ)
    (hc : ∀ A ∈ C.cls, Continuous (C.rho A)) : MvbeNegOpen C :=
  fun A hA => isOpen_lt (hc A hA) continuous_const

/-- (A4), (A7), (A8) and the openness of `{ρ_A < 0}` give the analytic hypotheses on `ρ_A`. -/
theorem MvbeRegularClass.distLike (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) : MvbeDistLike κ (C.rho A) where
  kappa_nonneg := C.kappa_nonneg
  neg_open := hneg A hA
  nonexp := C.a7 A hA
  differentiableAt := C.a8_differentiableAt A hA
  gradient_sub_le := C.a8_gradient_sub_le A hA

/-- Raic's `f_A^{+ε} = g (ρ_A / ε)`. -/
noncomputable def MvbeRegularClass.smoothOuter (C : MvbeRegularClass m κ)
    (A : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  mvbeSmooth (C.rho A) ε

namespace MvbeRegularClass

variable (C : MvbeRegularClass m κ) {A : Set (EuclideanSpace ℝ (Fin m))} {ε : ℝ}

/-- **(2), values**: `0 ≤ f ≤ 1`, `f = 1` on `A`, `f = 0` off `A^{ε|ρ}`. -/
theorem smoothOuter_mem_Icc (A : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ C.smoothOuter A ε x ∧ C.smoothOuter A ε x ≤ 1 :=
  ⟨mvbeG_nonneg _, mvbeG_le_one _⟩

theorem smoothOuter_eq_one (hA : A ∈ C.cls) (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ A) : C.smoothOuter A ε x = 1 :=
  mvbeG_of_nonpos (div_nonpos_of_nonpos_of_nonneg (C.a4_nonpos A hA x hx) hε.le)

theorem smoothOuter_eq_zero (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∉ mvbeLayer C.rho A ε) : C.smoothOuter A ε x = 0 :=
  mvbeG_of_one_le ((one_le_div hε).2 (le_of_lt (not_le.1 hx)))

theorem smoothOuter_eq_zero_of_ge (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ε ≤ C.rho A x) : C.smoothOuter A ε x = 0 :=
  mvbeG_of_one_le ((one_le_div hε).2 hx)

/-- **(2), regularity**: `f_A^{+ε}` is `C¹`. -/
theorem contDiff_smoothOuter (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε) :
    ContDiff ℝ 1 (C.smoothOuter A ε) :=
  (C.distLike hneg hA).contDiff_smooth hε

/-- **(2), `M₁ f ≤ 2 / ε`**. -/
theorem norm_fderiv_smoothOuter_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ (C.smoothOuter A ε) x‖ ≤ 2 / ε :=
  (C.distLike hneg hA).norm_fderiv_smooth_le hε x

/-- **(2), `M₂ f ≤ 4 (1 + κ) / ε²`**: `∇f_A^{+ε}` is Lipschitz with constant `4 (1 + κ) / ε²`. -/
theorem fderiv_smoothOuter_sub_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (C.smoothOuter A ε) x - fderiv ℝ (C.smoothOuter A ε) y‖
      ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ :=
  (C.distLike hneg hA).fderiv_smooth_sub_le hε x y

theorem lipschitzWith_fderiv_smoothOuter (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (4 * (1 + κ) / ε ^ 2)) (fderiv ℝ (C.smoothOuter A ε)) :=
  (C.distLike hneg hA).lipschitzWith_fderiv_smooth hε

/-- **(3), level sets**: for `u ∈ (0, 1)`, `{f ≥ u} = A^{(ε s)|ρ}` for some `s ∈ (0, 1)`. -/
theorem smoothOuter_levelSet (hε : 0 < ε) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ {x | u ≤ C.smoothOuter A ε x} = mvbeLayer C.rho A (ε * s) := by
  obtain ⟨s, hs0, hs1, hs⟩ := mvbeG_levelSet hu0 hu1
  refine ⟨s, hs0, hs1, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, mvbeLayer]
  unfold smoothOuter mvbeSmooth
  rw [hs, div_le_iff₀ hε, mul_comm]

/-- **(3), level sets**: `{x | u ≤ f_A^{+ε} x} ∈ A ∪ {∅, ℝ^d}` for `u ∈ (0, 1)` (by (A2)). -/
theorem smoothOuter_levelSet_mem (hA : A ∈ C.cls) (hε : 0 < ε) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) : {x | u ≤ C.smoothOuter A ε x} ∈ C.cls ∪ {∅, Set.univ} := by
  obtain ⟨s, -, -, hs⟩ := C.smoothOuter_levelSet (A := A) hε hu0 hu1
  rw [hs]
  exact C.a2 A hA _

/-- **(4), sandwich**: `1_A ≤ f_A^{+ε}`. -/
theorem indicator_le_smoothOuter (hA : A ∈ C.cls) (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin m)) :
    A.indicator (fun _ => (1 : ℝ)) x ≤ C.smoothOuter A ε x := by
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, C.smoothOuter_eq_one hA hε hx]
  · rw [Set.indicator_of_notMem hx]
    exact (C.smoothOuter_mem_Icc A ε x).1

/-- **(4), sandwich**: `f_A^{+ε} ≤ 1_{A^{ε|ρ}}`. -/
theorem smoothOuter_le_indicator (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    C.smoothOuter A ε x ≤ (mvbeLayer C.rho A ε).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ mvbeLayer C.rho A ε
  · rw [Set.indicator_of_mem hx]
    exact (C.smoothOuter_mem_Icc A ε x).2
  · rw [Set.indicator_of_notMem hx, C.smoothOuter_eq_zero hε hx]

open Classical in
/-- Raic's `f_A^{-ε}`: `0` if `A^{-ε|ρ} = ∅`, and `f_{A^{-ε|ρ}}^{+ε}` otherwise; in the one
remaining case `A^{-ε|ρ} = ℝ^d ∉ cls` (then `A = ℝ^d`) it is `1`. -/
noncomputable def smoothInner (C : MvbeRegularClass m κ) (A : Set (EuclideanSpace ℝ (Fin m)))
    (ε : ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  if mvbeLayer C.rho A (-ε) = ∅ then fun _ => 0
  else if mvbeLayer C.rho A (-ε) ∈ C.cls then C.smoothOuter (mvbeLayer C.rho A (-ε)) ε
  else fun _ => 1

/-- The three cases in the definition of `f_A^{-ε}`. -/
theorem smoothInner_cases (hA : A ∈ C.cls) (ε : ℝ) :
    (mvbeLayer C.rho A (-ε) = ∅ ∧ C.smoothInner A ε = fun _ => 0) ∨
    (mvbeLayer C.rho A (-ε) ≠ ∅ ∧ mvbeLayer C.rho A (-ε) ∈ C.cls ∧
      C.smoothInner A ε = C.smoothOuter (mvbeLayer C.rho A (-ε)) ε) ∨
    (mvbeLayer C.rho A (-ε) = Set.univ ∧ mvbeLayer C.rho A (-ε) ∉ C.cls ∧
      C.smoothInner A ε = fun _ => 1) := by
  by_cases h1 : mvbeLayer C.rho A (-ε) = ∅
  · exact Or.inl ⟨h1, by simp [smoothInner, h1]⟩
  · by_cases h2 : mvbeLayer C.rho A (-ε) ∈ C.cls
    · exact Or.inr (Or.inl ⟨h1, h2, by simp [smoothInner, h1, h2]⟩)
    · refine Or.inr (Or.inr ⟨?_, h2, by simp [smoothInner, h1, h2]⟩)
      rcases C.a2 A hA (-ε) with h | h
      · exact absurd h h2
      · rcases h with h | h
        · exact absurd h h1
        · exact h

theorem smoothInner_mem_Icc (hA : A ∈ C.cls) (ε : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ C.smoothInner A ε x ∧ C.smoothInner A ε x ≤ 1 := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact ⟨le_rfl, zero_le_one⟩
  · exact C.smoothOuter_mem_Icc _ ε x
  · exact ⟨zero_le_one, le_rfl⟩

/-- **(3), values**: `f_A^{-ε} = 1` on `A^{-ε|ρ}`. -/
theorem smoothInner_eq_one (hA : A ∈ C.cls) (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ mvbeLayer C.rho A (-ε)) : C.smoothInner A ε x = 1 := by
  rcases C.smoothInner_cases hA ε with ⟨h0, -⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩
  · rw [h0] at hx; exact absurd hx (Set.notMem_empty x)
  · rw [h]
    exact C.smoothOuter_eq_one hB hε (A := mvbeLayer C.rho A (-ε)) hx
  · rw [h]

/-- **(3), values**: `f_A^{-ε} = 0` off `A` (this uses (A3) and (A4)). -/
theorem smoothInner_eq_zero (hA : A ∈ C.cls) (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∉ A) : C.smoothInner A ε x = 0 := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨hne, hB, h⟩ | ⟨hU, -, h⟩
  · rw [h]
  · rw [h]
    refine C.smoothOuter_eq_zero_of_ge hε ?_
    rcases C.a3 A hA ε hε with h3 | h3
    · exact absurd h3 hne
    · by_contra hlt
      exact hx (h3 (not_le.1 hlt))
  · exfalso
    have h1 : x ∈ mvbeLayer C.rho A (-ε) := by rw [hU]; trivial
    have h2 := C.a4_nonneg A hA x hx
    have h3 : C.rho A x ≤ -ε := h1
    linarith

/-- **(3), regularity**: `f_A^{-ε}` is `C¹`. -/
theorem contDiff_smoothInner (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε) :
    ContDiff ℝ 1 (C.smoothInner A ε) := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact contDiff_const
  · exact C.contDiff_smoothOuter hneg hB hε
  · exact contDiff_const

/-- **(3), `M₁ f ≤ 2 / ε`** for `f_A^{-ε}`. -/
theorem norm_fderiv_smoothInner_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ (C.smoothInner A ε) x‖ ≤ 2 / ε := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · rw [fderiv_fun_const]; simp only [Pi.zero_apply, norm_zero]; positivity
  · exact C.norm_fderiv_smoothOuter_le hneg hB hε x
  · rw [fderiv_fun_const]; simp only [Pi.zero_apply, norm_zero]; positivity

/-- **(3), `M₂ f ≤ 4 (1 + κ) / ε²`** for `f_A^{-ε}`. -/
theorem fderiv_smoothInner_sub_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (C.smoothInner A ε) x - fderiv ℝ (C.smoothInner A ε) y‖
      ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖ := by
  have hκ := C.kappa_nonneg
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · rw [fderiv_fun_const]; simp only [Pi.zero_apply, sub_self, norm_zero]; positivity
  · exact C.fderiv_smoothOuter_sub_le hneg hB hε x y
  · rw [fderiv_fun_const]; simp only [Pi.zero_apply, sub_self, norm_zero]; positivity

/-- **(3), level sets**: for `u ∈ (0, 1)`, `{x | u ≤ f_A^{-ε} x} ∈ A ∪ {∅, ℝ^d}`. -/
theorem smoothInner_levelSet_mem (hA : A ∈ C.cls) (hε : 0 < ε) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) : {x | u ≤ C.smoothInner A ε x} ∈ C.cls ∪ {∅, Set.univ} := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · have : {x : EuclideanSpace ℝ (Fin m) | u ≤ (fun _ => (0 : ℝ)) x} = ∅ := by
      ext x; simp [not_le.2 hu0]
    rw [this]; exact Or.inr (Or.inl rfl)
  · exact C.smoothOuter_levelSet_mem hB hε hu0 hu1
  · have : {x : EuclideanSpace ℝ (Fin m) | u ≤ (fun _ => (1 : ℝ)) x} = Set.univ := by
      ext x; simp [hu1.le]
    rw [this]; exact Or.inr (Or.inr rfl)

/-- **(4), sandwich**: `1_{A^{-ε|ρ}} ≤ f_A^{-ε}`. -/
theorem indicator_le_smoothInner (hA : A ∈ C.cls) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    (mvbeLayer C.rho A (-ε)).indicator (fun _ => (1 : ℝ)) x ≤ C.smoothInner A ε x := by
  by_cases hx : x ∈ mvbeLayer C.rho A (-ε)
  · rw [Set.indicator_of_mem hx, C.smoothInner_eq_one hA hε hx]
  · rw [Set.indicator_of_notMem hx]
    exact (C.smoothInner_mem_Icc hA ε x).1

/-- **(4), sandwich**: `f_A^{-ε} ≤ 1_A`. -/
theorem smoothInner_le_indicator (hA : A ∈ C.cls) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    C.smoothInner A ε x ≤ A.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    exact (C.smoothInner_mem_Icc hA ε x).2
  · rw [Set.indicator_of_notMem hx, C.smoothInner_eq_zero hA hε hx]

/-- Second-derivative support, sharp form: `∇²f_A^{+ε} = 0` a.e. outside `{0 < ρ_A < ε}`. -/
theorem ae_iteratedFDeriv_two_smoothOuter_core (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ¬ (0 < C.rho A x ∧ C.rho A x < ε) → iteratedFDeriv ℝ 2 (C.smoothOuter A ε) x = 0 :=
  (C.distLike hneg hA).ae_iteratedFDeriv_two_smooth_eq_zero hε (C.measurable_rho A hA)

/-- **(3), second-derivative support** for `f_A^{+ε}`: for Lebesgue-a.e. `x ∉ A^{ε|ρ} \ A`,
`∇²f (x) = 0` (`iteratedFDeriv ℝ 2 f x = 0`; this is also true, by convention, where `∇f` is not
differentiable).  The pointwise statement is false at the (null) set of points of `A` where
`ρ = 0` and `∇f` happens to be differentiable with non-zero derivative, e.g. the centre of a
ball of radius `0`. -/
theorem ae_iteratedFDeriv_two_smoothOuter (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      x ∉ mvbeLayer C.rho A ε \ A → iteratedFDeriv ℝ 2 (C.smoothOuter A ε) x = 0 := by
  filter_upwards [C.ae_iteratedFDeriv_two_smoothOuter_core hneg hA hε] with x hx hxn
  refine hx fun ⟨h0, h1⟩ => hxn ⟨h1.le, fun hxA => ?_⟩
  exact absurd (C.a4_nonpos A hA x hxA) (not_le.2 h0)

/-- The global bound `‖∇²f_A^{+ε}‖ ≤ 4 (1 + κ) / ε²`. -/
theorem norm_iteratedFDeriv_two_smoothOuter_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    ‖iteratedFDeriv ℝ 2 (C.smoothOuter A ε) x‖ ≤ 4 * (1 + κ) / ε ^ 2 :=
  (C.distLike hneg hA).norm_iteratedFDeriv_two_smooth_le hε x

/-- **(3), `‖∇²f_A^{+ε}‖ ≤ 4 (1 + κ) ε⁻² 1_{A^{ε|ρ} \ A}` almost everywhere.** -/
theorem ae_norm_iteratedFDeriv_two_smoothOuter_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ‖iteratedFDeriv ℝ 2 (C.smoothOuter A ε) x‖
        ≤ 4 * (1 + κ) / ε ^ 2 * (mvbeLayer C.rho A ε \ A).indicator (fun _ => (1 : ℝ)) x := by
  have hκ := C.kappa_nonneg
  filter_upwards [C.ae_iteratedFDeriv_two_smoothOuter hneg hA hε] with x hx
  exact mvbe_norm_le_indicator (C.norm_iteratedFDeriv_two_smoothOuter_le hneg hA hε x) hx

/-- **(3), second-derivative support** for `f_A^{-ε}`: for Lebesgue-a.e. `x ∉ A \ A^{-ε|ρ}`,
`∇²f (x) = 0`. -/
theorem ae_iteratedFDeriv_two_smoothInner (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      x ∉ A \ mvbeLayer C.rho A (-ε) → iteratedFDeriv ℝ 2 (C.smoothInner A ε) x = 0 := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨hne, hB, h⟩ | ⟨-, -, h⟩
  · exact Eventually.of_forall fun x _ => by rw [h]; exact mvbe_iteratedFDeriv_two_const 0 x
  · rw [h]
    filter_upwards [C.ae_iteratedFDeriv_two_smoothOuter_core hneg hB hε] with x hx hxn
    refine hx fun ⟨h0, h1⟩ => hxn ⟨?_, fun hxB => ?_⟩
    · rcases C.a3 A hA ε hε with h3 | h3
      · exact absurd h3 hne
      · exact h3 h1
    · exact absurd (C.a4_nonpos _ hB x hxB) (not_le.2 h0)
  · exact Eventually.of_forall fun x _ => by rw [h]; exact mvbe_iteratedFDeriv_two_const 1 x

/-- The global bound `‖∇²f_A^{-ε}‖ ≤ 4 (1 + κ) / ε²`. -/
theorem norm_iteratedFDeriv_two_smoothInner_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    ‖iteratedFDeriv ℝ 2 (C.smoothInner A ε) x‖ ≤ 4 * (1 + κ) / ε ^ 2 := by
  have hκ := C.kappa_nonneg
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · rw [mvbe_iteratedFDeriv_two_const, norm_zero]; positivity
  · exact C.norm_iteratedFDeriv_two_smoothOuter_le hneg hB hε x
  · rw [mvbe_iteratedFDeriv_two_const, norm_zero]; positivity

/-- **(3), `‖∇²f_A^{-ε}‖ ≤ 4 (1 + κ) ε⁻² 1_{A \ A^{-ε|ρ}}` almost everywhere.** -/
theorem ae_norm_iteratedFDeriv_two_smoothInner_le (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ‖iteratedFDeriv ℝ 2 (C.smoothInner A ε) x‖
        ≤ 4 * (1 + κ) / ε ^ 2 * (A \ mvbeLayer C.rho A (-ε)).indicator (fun _ => (1 : ℝ)) x := by
  have hκ := C.kappa_nonneg
  filter_upwards [C.ae_iteratedFDeriv_two_smoothInner hneg hA hε] with x hx
  exact mvbe_norm_le_indicator (C.norm_iteratedFDeriv_two_smoothInner_le hneg hA hε x) hx

/-- For `x ∉ A^{ε|ρ}` the second derivative of `f_A^{+ε}` vanishes (pointwise, not only a.e.). -/
theorem iteratedFDeriv_two_smoothOuter_eq_zero_of_notMem_layer (hneg : MvbeNegOpen C)
    (hA : A ∈ C.cls) (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∉ mvbeLayer C.rho A ε) : iteratedFDeriv ℝ 2 (C.smoothOuter A ε) x = 0 :=
  (C.distLike hneg hA).iteratedFDeriv_two_smooth_eq_zero_of_far hε (Or.inr (not_le.1 hx))

/-- Where `ρ_A < 0` (in particular on the interior of `A`) the second derivative of `f_A^{+ε}`
vanishes (pointwise). -/
theorem iteratedFDeriv_two_smoothOuter_eq_zero_of_neg (hneg : MvbeNegOpen C) (hA : A ∈ C.cls)
    (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin m)} (hx : C.rho A x < 0) :
    iteratedFDeriv ℝ 2 (C.smoothOuter A ε) x = 0 :=
  (C.distLike hneg hA).iteratedFDeriv_two_smooth_eq_zero_of_far hε (Or.inl hx)

/-- **Raic's Lemma 2.1** (Bentkus smoothing) for a regular class (under the extra hypothesis
`MvbeNegOpen C`): for every `A ∈ cls` and `ε > 0` there are `fp = f_A^{ε}` and `fm = f_A^{-ε}`
with (1) `0 ≤ f ≤ 1`, (2) `fp = 1` on `A`, `fp = 0` off `A^{ε|ρ}`, (3) `fm = 1` on `A^{-ε|ρ}`,
`fm = 0` off `A`, (4) `f` is `C¹`, `M₁ f ≤ 2 / ε` and `∇f` is `4 (1 + κ) / ε²`-Lipschitz, and
(5) `{f ≥ u} ∈ cls ∪ {∅, ℝ^d}` for `u ∈ (0, 1)`. -/
theorem raic_lemma_2_1 (hneg : MvbeNegOpen C) (hA : A ∈ C.cls) (hε : 0 < ε) :
    ∃ fp fm : EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ x, 0 ≤ fp x ∧ fp x ≤ 1) ∧ (∀ x, 0 ≤ fm x ∧ fm x ≤ 1) ∧
      (∀ x ∈ A, fp x = 1) ∧ (∀ x, x ∉ mvbeLayer C.rho A ε → fp x = 0) ∧
      (∀ x ∈ mvbeLayer C.rho A (-ε), fm x = 1) ∧ (∀ x, x ∉ A → fm x = 0) ∧
      ContDiff ℝ 1 fp ∧ ContDiff ℝ 1 fm ∧
      (∀ x, ‖fderiv ℝ fp x‖ ≤ 2 / ε) ∧ (∀ x, ‖fderiv ℝ fm x‖ ≤ 2 / ε) ∧
      (∀ x y, ‖fderiv ℝ fp x - fderiv ℝ fp y‖ ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ fm x - fderiv ℝ fm y‖ ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖) ∧
      (∀ u, 0 < u → u < 1 → {x | u ≤ fp x} ∈ C.cls ∪ {∅, Set.univ}) ∧
      (∀ u, 0 < u → u < 1 → {x | u ≤ fm x} ∈ C.cls ∪ {∅, Set.univ}) :=
  ⟨C.smoothOuter A ε, C.smoothInner A ε, C.smoothOuter_mem_Icc A ε, C.smoothInner_mem_Icc hA ε,
    fun _ hx => C.smoothOuter_eq_one hA hε hx, fun _ hx => C.smoothOuter_eq_zero hε hx,
    fun _ hx => C.smoothInner_eq_one hA hε hx, fun _ hx => C.smoothInner_eq_zero hA hε hx,
    C.contDiff_smoothOuter hneg hA hε, C.contDiff_smoothInner hneg hA hε,
    C.norm_fderiv_smoothOuter_le hneg hA hε, C.norm_fderiv_smoothInner_le hneg hA hε,
    C.fderiv_smoothOuter_sub_le hneg hA hε, C.fderiv_smoothInner_sub_le hneg hA hε,
    fun _ h0 h1 => C.smoothOuter_levelSet_mem hA hε h0 h1,
    fun _ h0 h1 => C.smoothInner_levelSet_mem hA hε h0 h1⟩

end MvbeRegularClass


/-- The class of rounded orthants satisfies the extra hypothesis (its `ρ_A` are continuous), so
`raic_lemma_2_1` applies to it with `κ = 1`. -/
theorem mvbeRoundedRegularClass_negOpen (m : ℕ) [NeZero m] :
    MvbeNegOpen (mvbeRoundedRegularClass m) := by
  refine mvbeNegOpen_of_continuous _ ?_
  rintro A ⟨h, s, hs, rfl⟩
  have : (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) = mvbeRhoRound h s :=
    funext (mvbeRoundedRegularClass_rho hs)
  rw [this]
  exact (mvbeRho_continuous h).sub continuous_const

end ClassLevel

end LatticeProb
