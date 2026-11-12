/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingODE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4, node B3: integration of Carleman's inequality (`CarlemanODEStmt`)

Plan: `handoff/LW-BEURLING.md`. Own first-order comparison replacing Garnett–Marshall,
*Harmonic Measure*, App. G, (G.6), p. 482 (which needs `ϕ(0) = 0`):

* `I'' ≥ 0` and `0 ≤ I ≤ M` on `(−∞, T)` ⇒ `I' ≥ 0` (a negative slope would make `I` unbounded
  to the left), so `I` is nondecreasing.
* `R = (I' + I)² e^{−t} / I` has `R' = e^{−t} (I' + I)(2 I I'' − I² − I'²)/I² ≥ 0`, so
  `(I' + I)/√I ≥ √(I a) e^{(t−a)/2}` on `[a, b]`.
* `W = √I e^{t/2} − c e^t`, `c = √(I a) e^{−a/2}/2`, has `W' ≥ 0`, which gives
  `√(I b) ≥ √(I a) e^{(b−a)/2}/2`, i.e. `I a ≤ 4 e^{a−b} I b`.
-/

noncomputable section

open Set

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Monotonicity from a nonnegative derivative on a closed interval. -/
lemma lwb_le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hd : ∀ x ∈ Icc s t, HasDerivAt f (f' x) x) (h0 : ∀ x ∈ Icc s t, 0 ≤ f' x) : f s ≤ f t := by
  have hmono : MonotoneOn f (Icc s t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc s t)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [(hd x (interior_subset hx)).deriv]; exact h0 x (interior_subset hx))
  exact hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- **B3** (`CarlemanODEStmt`). -/
theorem carlemanODEStmt_holds : CarlemanODEStmt := by
  intro I I1 I2 T M a hI hI1 hbd hI2 hineq
  have hI1mono : ∀ s t, s ≤ t → t < T → I1 s ≤ I1 t := fun s t hst htT =>
    lwb_le_of_hasDerivAt_nonneg hst (fun x hx => hI1 x (lt_of_le_of_lt hx.2 htT))
      (fun x hx => hI2 x (lt_of_le_of_lt hx.2 htT))
  -- `I' ≥ 0`
  have hI1nn : ∀ t, t < T → 0 ≤ I1 t := by
    intro t₀ ht₀
    by_contra hneg
    push Not at hneg
    obtain ⟨c, hc⟩ : ∃ c, c = -I1 t₀ := ⟨_, rfl⟩
    have hcpos : 0 < c := by rw [hc]; linarith
    have hM0 : 0 ≤ M := (hbd t₀ ht₀).1.trans (hbd t₀ ht₀).2
    obtain ⟨s, hs_def⟩ : ∃ s, s = t₀ - (M + 1) / c := ⟨_, rfl⟩
    have hq : 0 ≤ (M + 1) / c := div_nonneg (by linarith) hcpos.le
    have hs : s ≤ t₀ := by rw [hs_def]; linarith
    have key : (fun x => -(I x - x * I1 t₀)) s ≤ (fun x => -(I x - x * I1 t₀)) t₀ :=
      lwb_le_of_hasDerivAt_nonneg (f := fun x => -(I x - x * I1 t₀))
        (f' := fun x => -(I1 x - I1 t₀)) (s := s) (t := t₀) hs
        (fun x hx => ((hI x (lt_of_le_of_lt hx.2 ht₀)).sub (hasDerivAt_mul_const (I1 t₀))).neg)
        (fun x hx => by have := hI1mono x t₀ hx.2 ht₀; linarith)
    simp only at key
    have e1 : (t₀ - s) * c = M + 1 := by
      rw [hs_def]; field_simp; ring
    have e2 : s * I1 t₀ - t₀ * I1 t₀ = (t₀ - s) * c := by rw [hc]; ring
    have hIs := (hbd s (lt_of_le_of_lt hs ht₀)).2
    have hIt := (hbd t₀ ht₀).1
    linarith
  have hmono : MonotoneOn I (Iio T) := fun s _ t ht hst =>
    lwb_le_of_hasDerivAt_nonneg hst (fun x hx => hI x (lt_of_le_of_lt hx.2 ht))
      (fun x hx => hI1nn x (lt_of_le_of_lt hx.2 ht))
  refine ⟨hmono, fun b hab hbT => ?_⟩
  have haT : a < T := lt_of_le_of_lt hab hbT
  have hIb0 := (hbd b hbT).1
  rcases (hbd a haT).1.eq_or_lt with ha0 | hpos
  · rw [← ha0]; positivity
  have hTt : ∀ t ∈ Icc a b, t < T := fun t ht => lt_of_le_of_lt ht.2 hbT
  have hIpos : ∀ t ∈ Icc a b, 0 < I t := fun t ht =>
    lt_of_lt_of_le hpos (hmono haT (hTt t ht) ht.1)
  -- Step 1: `R = (I' + I)² e^{−t} / I` is nondecreasing on `[a, b]`.
  have hR : ∀ t ∈ Icc a b, (I1 a + I a) * (I1 a + I a) * Real.exp (-a) / I a ≤
      (I1 t + I t) * (I1 t + I t) * Real.exp (-t) / I t := by
    intro t ht
    refine lwb_le_of_hasDerivAt_nonneg (f := fun t => (I1 t + I t) * (I1 t + I t) *
      Real.exp (-t) / I t) (f' := fun x => Real.exp (-x) * (I1 x + I x) *
        (2 * I x * I2 x - I x ^ 2 - I1 x ^ 2) / I x ^ 2) ht.1 (fun x hx => ?_) (fun x hx => ?_)
    · have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans ht.2⟩
      have h1 : HasDerivAt (fun t => I1 t + I t) (I2 x + I1 x) x :=
        (hI1 x (hTt x hx')).add (hI x (hTt x hx'))
      have h3 : HasDerivAt (fun t => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
        (hasDerivAt_neg x).exp
      have h4 : HasDerivAt (fun t => (I1 t + I t) * (I1 t + I t) * Real.exp (-t))
          (((I2 x + I1 x) * (I1 x + I x) + (I1 x + I x) * (I2 x + I1 x)) * Real.exp (-x) +
            (I1 x + I x) * (I1 x + I x) * (Real.exp (-x) * -1)) x := (h1.mul h1).mul h3
      exact (HasDerivAt.fun_div h4 (hI x (hTt x hx')) (hIpos x hx').ne').congr_deriv (by ring)
    · have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans ht.2⟩
      have hIx := hIpos x hx'
      have hfx : 0 ≤ I1 x + I x := add_nonneg (hI1nn x (hTt x hx')) hIx.le
      have hq := hineq x hx'.1 (hTt x hx')
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hfx) (by linarith)
  have hRa : I a * Real.exp (-a) ≤
      (I1 a + I a) * (I1 a + I a) * Real.exp (-a) / I a := by
    rw [le_div_iff₀ hpos]
    have h1 : 0 ≤ I1 a := hI1nn a haT
    have he := Real.exp_pos (-a)
    have : I a * I a ≤ (I1 a + I a) * (I1 a + I a) := by nlinarith
    nlinarith
  -- Step 2: `W = √I e^{t/2} − c e^t` is nondecreasing on `[a, b]`.
  set p := Real.sqrt (I a) with hp
  have hp0 : 0 < p := Real.sqrt_pos.2 hpos
  have hpp : p * p = I a := Real.mul_self_sqrt hpos.le
  set c := p * Real.exp (-(a / 2)) / 2 with hc
  have hW : (fun t => Real.sqrt (I t) * Real.exp (t / 2) - c * Real.exp t) a ≤
      (fun t => Real.sqrt (I t) * Real.exp (t / 2) - c * Real.exp t) b := by
    refine lwb_le_of_hasDerivAt_nonneg
      (f := fun t => Real.sqrt (I t) * Real.exp (t / 2) - c * Real.exp t)
      (f' := fun x => (I1 x + I x) / (2 * Real.sqrt (I x)) * Real.exp (x / 2) - c * Real.exp x)
      hab (fun x hx => ?_) (fun x hx => ?_)
    · have hs := (hI x (hTt x hx)).sqrt (hIpos x hx).ne'
      have he : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
        ((hasDerivAt_id x).div_const 2).exp
      set q := Real.sqrt (I x) with hq
      have hq0 : 0 < q := Real.sqrt_pos.2 (hIpos x hx)
      have hqq : q * q = I x := Real.mul_self_sqrt (hIpos x hx).le
      refine ((hs.mul he).sub ((Real.hasDerivAt_exp x).const_mul c)).congr_deriv ?_
      calc I1 x / (2 * q) * Real.exp (x / 2) + q * (Real.exp (x / 2) * (1 / 2)) -
            c * Real.exp x = (I1 x + q * q) / (2 * q) * Real.exp (x / 2) - c * Real.exp x := by
            field_simp
        _ = _ := by rw [hqq]
    · have hIx := hIpos x hx
      set q := Real.sqrt (I x) with hq
      have hq0 : 0 < q := Real.sqrt_pos.2 hIx
      have hqq : q * q = I x := Real.mul_self_sqrt hIx.le
      have hRx := (hRa.trans (hR x hx))
      -- `(I1 + I)/q ≥ p e^{(x−a)/2}`
      set E := Real.exp ((x - a) / 2) with hE
      have hE0 : 0 < E := Real.exp_pos _
      have hEE : E * E * Real.exp (-x) = Real.exp (-a) := by
        rw [hE, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hsq : (p * E) * (p * E) * q * q ≤ (I1 x + I x) * (I1 x + I x) := by
        have h1 : I a * Real.exp (-a) * I x ≤ (I1 x + I x) * (I1 x + I x) * Real.exp (-x) := by
          rw [le_div_iff₀ hIx] at hRx; exact hRx
        have h2 : (p * E) * (p * E) * q * q * Real.exp (-x) =
            I a * Real.exp (-a) * I x := by
          rw [← hpp, ← hqq, ← hEE]; ring
        have hex := Real.exp_pos (-x)
        nlinarith
      have hfx : 0 ≤ I1 x + I x := add_nonneg (hI1nn x (hTt x hx)) hIx.le
      have hlin : p * E * q ≤ I1 x + I x := by
        by_contra hlt
        push Not at hlt
        have : (I1 x + I x) * (I1 x + I x) < (p * E * q) * (p * E * q) :=
          mul_self_lt_mul_self hfx hlt
        nlinarith
      have hxe : Real.exp (x / 2) * E = Real.exp x * Real.exp (-(a / 2)) := by
        rw [hE, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hgoal : c * Real.exp x ≤ (I1 x + I x) / (2 * q) * Real.exp (x / 2) := by
        have h2q : 0 < 2 * q := by positivity
        have lhs_eq : c * Real.exp x = (p * E * q) / (2 * q) * Real.exp (x / 2) := by
          calc c * Real.exp x = p / 2 * (Real.exp x * Real.exp (-(a / 2))) := by rw [hc]; ring
            _ = p / 2 * (Real.exp (x / 2) * E) := by rw [hxe]
            _ = (p * E * q) / (2 * q) * Real.exp (x / 2) := by field_simp
        rw [lhs_eq]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlin h2q.le)
          (Real.exp_pos _).le
      linarith [hgoal]
  simp only at hW
  have hWa : p * Real.exp (a / 2) - c * Real.exp a = p * Real.exp (a / 2) / 2 := by
    rw [hc]
    have : Real.exp (-(a / 2)) * Real.exp a = Real.exp (a / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (-(p / 2)) * this
  rw [hWa] at hW
  -- conclude
  have hb2 : c * Real.exp b ≤ Real.sqrt (I b) * Real.exp (b / 2) := by
    have := mul_pos hp0 (Real.exp_pos (a / 2))
    linarith
  set r := Real.sqrt (I b) with hr
  have hrr : r * r = I b := Real.mul_self_sqrt hIb0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- `p e^{(b−a)/2} ≤ 2 r`
  have hkey : p * Real.exp ((b - a) / 2) ≤ 2 * r := by
    have he : c * Real.exp b = p * Real.exp ((b - a) / 2) / 2 * Real.exp (b / 2) := by
      rw [hc, mul_div_assoc]
      have : Real.exp (-(a / 2)) * Real.exp b = Real.exp ((b - a) / 2) * Real.exp (b / 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      linear_combination (p / 2) * this
    rw [he] at hb2
    have := le_of_mul_le_mul_right hb2 (Real.exp_pos (b / 2))
    linarith
  have hsq : (p * Real.exp ((b - a) / 2)) * (p * Real.exp ((b - a) / 2)) ≤ (2 * r) * (2 * r) :=
    mul_self_le_mul_self (by positivity) hkey
  have hEb : Real.exp ((b - a) / 2) * Real.exp ((b - a) / 2) * Real.exp (a - b) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
  have hexp := Real.exp_pos (a - b)
  have : I a = p * p * (Real.exp ((b - a) / 2) * Real.exp ((b - a) / 2) * Real.exp (a - b)) := by
    rw [hEb, hpp]; ring
  rw [this, ← hrr]
  nlinarith

end LWFar
end Thm18Asm
end QuantumZipper
