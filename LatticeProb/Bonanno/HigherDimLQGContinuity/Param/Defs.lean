/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGContinuity.Param.Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGContinuity.Frozen.XiRange

/-!
# The exponent function `ϕ`, the gap, the subcritical set and `γ ↦ d/γ + γ/2` (packet PAR)

Blueprint `a:def-phi` (Part A §1; [C] (1.5), p. 2, l. 74–81, and (2.4)). With `Q = distExp d`:

* `phiXi d ξ = ξ Q(ξ)` for `ξ > 0` and `1` for `ξ ≤ 0` (the honest value `ϕ(0) = 1`; `Q` is not
  defined at `0`, and `ξ Q(ξ) → 1` as `ξ ↓ 0`, `Param/Lipschitz.lean`);
* `gapXi d ξ = ϕ(ξ) - √(2d) ξ` (the gap of (2.4));
* `subcritSet d = {ξ > 0 : √(2d) < Q(ξ)}` (so `xiRange d = insert 0 (subcritSet d)`, by `rfl`);
* `gammaQ d γ = d/γ + γ/2` (the right-hand side of (1.5)).

Elementary facts only; the probabilistic input is in `Param/Lipschitz.lean` and `Param/Upper.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- `ϕ(ξ) = ξ Q(ξ)` for `ξ > 0`, and `ϕ(ξ) = 1` for `ξ ≤ 0` (blueprint `a:def-phi`). -/
def phiXi (d : ℕ) (ξ : ℝ) : ℝ := if 0 < ξ then ξ * distExp d ξ else 1

/-- The gap `g(ξ) = ϕ(ξ) - √(2d) ξ` of (2.4). -/
def gapXi (d : ℕ) (ξ : ℝ) : ℝ := phiXi d ξ - Real.sqrt (2 * d) * ξ

/-- The subcritical set `{ξ > 0 : √(2d) < Q(ξ)}`. -/
def subcritSet (d : ℕ) : Set ℝ := {ξ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ}

/-- `G(γ) = d/γ + γ/2`, the right-hand side of (1.5). -/
def gammaQ (d : ℕ) (γ : ℝ) : ℝ := (d : ℝ) / γ + γ / 2

theorem phiXi_of_pos {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ) : phiXi d ξ = ξ * distExp d ξ := by
  simp only [phiXi, hξ, ite_true]

theorem phiXi_of_nonpos {d : ℕ} {ξ : ℝ} (hξ : ξ ≤ 0) : phiXi d ξ = 1 := by
  simp only [phiXi, not_lt.2 hξ, ite_false]

@[simp] theorem phiXi_zero (d : ℕ) : phiXi d 0 = 1 := phiXi_of_nonpos le_rfl

/-- `ϕ(ξ) = ϕ(max ξ 0)`. -/
theorem phiXi_max_zero (d : ℕ) (ξ : ℝ) : phiXi d (max ξ 0) = phiXi d ξ := by
  rcases le_or_gt ξ 0 with h | h
  · rw [max_eq_right h, phiXi_zero, phiXi_of_nonpos h]
  · rw [max_eq_left h.le]

theorem distExp_eq_phiXi_div {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ) : distExp d ξ = phiXi d ξ / ξ := by
  rw [phiXi_of_pos hξ, mul_div_cancel_left₀ _ hξ.ne']

@[simp] theorem gapXi_zero (d : ℕ) : gapXi d 0 = 1 := by
  simp [gapXi]

/-- For `ξ > 0`, `g(ξ) = ξ (Q(ξ) - √(2d))`. -/
theorem gapXi_of_pos {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    gapXi d ξ = ξ * (distExp d ξ - Real.sqrt (2 * d)) := by
  rw [gapXi, phiXi_of_pos hξ]
  ring

/-- For `ξ > 0`, `Q(ξ) = √(2d) + g(ξ)/ξ`. -/
theorem distExp_eq_sqrt_add_gapXi_div {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    distExp d ξ = Real.sqrt (2 * d) + gapXi d ξ / ξ := by
  rw [gapXi_of_pos hξ, mul_div_cancel_left₀ _ hξ.ne']
  ring

theorem xiRange_eq_insert_subcritSet (d : ℕ) : xiRange d = insert 0 (subcritSet d) := rfl

/-- For `ξ > 0`: `ξ` is subcritical iff the gap is positive. -/
theorem mem_subcritSet_iff_gapXi_pos {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    ξ ∈ subcritSet d ↔ 0 < gapXi d ξ := by
  rw [gapXi_of_pos hξ]
  change 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ ↔ _
  constructor
  · rintro ⟨-, h⟩
    exact mul_pos hξ (sub_pos.2 h)
  · intro h
    exact ⟨hξ, sub_pos.1 (pos_of_mul_pos_right h hξ.le)⟩

/-- `d/γ + γ/2 - s = (γ - s)² / (2γ)` whenever `s² = 2d`. -/
theorem par_div_add_half_sub_eq {d s γ : ℝ} (hγ : 0 < γ) (hs : s ^ 2 = 2 * d) :
    d / γ + γ / 2 - s = (γ - s) ^ 2 / (2 * γ) := by
  rw [eq_div_iff (by positivity)]
  field_simp
  linear_combination (-1 : ℝ) * hs

/-- `G(γ) - √(2d) = (γ - √(2d))² / (2γ)`. -/
theorem gammaQ_sub_sqrt {d : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    gammaQ d γ - Real.sqrt (2 * d) = (γ - Real.sqrt (2 * d)) ^ 2 / (2 * γ) :=
  par_div_add_half_sub_eq hγ (Real.sq_sqrt (by positivity))

/-- `√(2d) < G(γ)` for `0 < γ < √(2d)`. -/
theorem sqrt_lt_gammaQ {d : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγs : γ < Real.sqrt (2 * d)) :
    Real.sqrt (2 * d) < gammaQ d γ := by
  have h := gammaQ_sub_sqrt (d := d) hγ
  have hpos : 0 < (γ - Real.sqrt (2 * d)) ^ 2 / (2 * γ) :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hγs.ne)) (by positivity)
  linarith

/-- `G` is strictly decreasing on `(0, √(2d))`. -/
theorem gammaQ_strictAntiOn (d : ℕ) :
    StrictAntiOn (gammaQ d) (Ioo 0 (Real.sqrt (2 * d))) := by
  intro a ha b hb hab
  have hs : Real.sqrt (2 * d) ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  have hab' : a * b < 2 * d := by
    have h1 : a * b < Real.sqrt (2 * d) * Real.sqrt (2 * d) :=
      mul_lt_mul'' ha.2 hb.2 ha.1.le hb.1.le
    nlinarith
  have hpos : 0 < a * b := mul_pos ha.1 hb.1
  have ha0 : a ≠ 0 := ha.1.ne'
  have hb0 : b ≠ 0 := hb.1.ne'
  rw [gammaQ, gammaQ, ← sub_pos]
  have heq : (d : ℝ) / a + a / 2 - ((d : ℝ) / b + b / 2) =
      (b - a) * (2 * d - a * b) / (2 * (a * b)) := by
    field_simp
    ring
  rw [heq]
  exact div_pos (mul_pos (sub_pos.2 hab) (sub_pos.2 hab')) (by positivity)

/-- The inverse of `G`: for `y > √(2d)`, `γ = y - √(y² - 2d) ∈ (0, √(2d))` and `G(γ) = y`. -/
theorem exists_gammaQ_eq {d : ℕ} (hd : 1 ≤ d) {y : ℝ} (hy : Real.sqrt (2 * d) < y) :
    ∃ γ ∈ Ioo 0 (Real.sqrt (2 * d)), gammaQ d γ = y := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set s := Real.sqrt (2 * d) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs : s ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  have hy0 : 0 < y := hs0.trans hy
  have hdisc : 0 ≤ y ^ 2 - 2 * d := by nlinarith
  set r := Real.sqrt (y ^ 2 - 2 * d) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : r ^ 2 = y ^ 2 - 2 * d := Real.sq_sqrt hdisc
  have hry : r < y := by nlinarith
  have hγ0 : 0 < y - r := sub_pos.2 hry
  have hγs : y - r < s := by nlinarith
  refine ⟨y - r, ⟨hγ0, hγs⟩, ?_⟩
  rw [gammaQ]
  have hprod : (y - r) * (y + r) = 2 * d := by nlinarith
  field_simp
  nlinarith

end HigherDimLQGContinuity
