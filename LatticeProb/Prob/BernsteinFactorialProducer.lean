/-
# The raw-factorial conditional-exponential producer

`LatticeProb.condExp_exp_le_of_factorial` (`Prob/BernsteinSteps.lean`) bounds the conditional
exponential moment of a centred increment `X` by the **constant** Bernstein exponent
`exp (lam^2 v / (2 (1 - a lam)))`, from per-increment factorial-moment bounds.  The `Parking`
clause 2 hypothesis, however, is a bound on the *sum over the increments* of the conditional
absolute moments,

  `∑_{i=1}^k E[|ξ_i|^q | F_{i-1}] ≤ (q!/2) a^{q-2} v`   a.s. for every `q ≥ 2`,

which does not by itself bound a single increment by `(q!/2) a^{q-2} v`.  What the supermartingale
consumer needs instead is a per-increment exponent `d_λ(i)` that is *summable* over `i`.  This file
supplies that exponent and the matching conditional-exponential bound:

  `E[e^{λ X} | m] ≤ᵐ exp (∑_{q≥2} (λ^q/q!) E[|X|^q | m])`.

The exponent is the increment's own conditional moment series, so summing over the increments and
invoking the raw factorial bound gives `∑_i d_λ(i) ≤ λ²v/(2(1-aλ))`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinSteps

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **Deterministic factorial-series comparison.**  If `f` and `g` are summable, `g` vanishes at
`0` and `1`, `f 0 ≤ 1`, `f 1 ≤ 0`, and `f q ≤ g q` for `q ≥ 2`, then
`∑' f q ≤ exp (∑' g q)`. -/
private theorem tsum_le_exp_of_majorant {f g : ℕ → ℝ} (hs : Summable f) (hg : Summable g)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hf0 : f 0 ≤ 1) (hf1 : f 1 ≤ 0)
    (hf : ∀ q : ℕ, 2 ≤ q → f q ≤ g q) :
    ∑' q, f q ≤ Real.exp (∑' q, g q) := by
  have hsplit : ∑' q, f q = f 0 + f 1 + ∑' q, f (q + 2) := by
    rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
    ring
  have hgsplit : ∑' q, g (q + 2) = ∑' q, g q := by
    rw [hg.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hg).tsum_eq_zero_add, hg0, hg1]
    ring
  have htail : ∑' q, f (q + 2) ≤ ∑' q, g (q + 2) :=
    Summable.tsum_le_tsum (fun i => hf (i + 2) (by omega))
      ((summable_nat_add_iff 2).mpr hs) ((summable_nat_add_iff 2).mpr hg)
  rw [hsplit]
  calc f 0 + f 1 + ∑' q, f (q + 2)
      ≤ 1 + 0 + ∑' q, g (q + 2) := by linarith [add_le_add hf0 hf1, htail]
    _ = 1 + ∑' q, g q := by rw [hgsplit]; ring
    _ ≤ Real.exp (∑' q, g q) := by linarith [Real.add_one_le_exp (∑' q, g q)]

/-- **The raw-factorial conditional-exponential producer, one increment.**  For an increment `X`
with conditional mean `E[X | m] =ᵐ 0` and summable conditional absolute-moment series, the
conditional exponential moment is bounded by the exponential of the increment's own conditional
moment series

  `E[e^{λ X} | m] ≤ᵐ exp (∑_{q≥2} (λ^q/q!) E[|X|^q | m])`.

This is the exponent the supermartingale consumer sums over the increments; unlike
`condExp_exp_le_of_factorial` it produces a per-increment exponent `d_λ(i)` rather than a constant.
The hypotheses `hsumm`/`hg`/`hsum` are the summability/integrability that the raw factorial bound
supplies when the increments are `a`-subexponential; `hintf`/`hintg` are the integrable absolute
moments the `Parking` type already carries. -/
theorem condExp_exp_le_of_momentSeries {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hX : Measurable[m₀] X)
    (hmean : μ[X | m] =ᵐ[μ] 0)
    (hintf : ∀ q : ℕ, Integrable (fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ)) μ)
    (hintg : ∀ q : ℕ,
      Integrable (fun ω' => (lam ^ q / (Nat.factorial q : ℝ)) * |X ω'| ^ q) μ)
    (hsumm : ∀ᵐ ω ∂μ, Summable (fun q : ℕ =>
      (μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω))
    (hg : ∀ᵐ ω ∂μ, Summable (fun q : ℕ =>
      if q < 2 then 0
      else (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω))
    (hsum : ∑' q : ℕ, ∫⁻ ω, ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ ≠ ∞) :
    μ[fun ω => Real.exp (lam * X ω) | m] ≤ᵐ[μ] fun ω =>
      Real.exp (∑' q : ℕ, if q < 2 then 0
        else (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω) := by
  have hinter := condExp_exp_eq_tsum' hm hX lam hsum
  -- the `q = 0` and `q = 1` terms
  have h0 : μ[fun ω' => (lam * X ω') ^ 0 / (Nat.factorial 0 : ℝ) | m] ≤ᵐ[μ]
      fun _ => 1 := by
    have hfun : (fun ω' => (lam * X ω') ^ 0 / (Nat.factorial 0 : ℝ)) = fun _ => (1 : ℝ) := by
      funext ω'; simp
    rw [hfun, condExp_const hm 1]
  have h1 : μ[fun ω' => (lam * X ω') ^ 1 / (Nat.factorial 1 : ℝ) | m] ≤ᵐ[μ]
      fun _ => 0 := by
    have hfun : (fun ω' => (lam * X ω') ^ 1 / (Nat.factorial 1 : ℝ))
        = fun ω' => lam * X ω' := by
      funext ω'; simp
    rw [hfun]
    have hsm : μ[fun ω' => lam * X ω' | m] =ᵐ[μ] fun ω => lam * (μ[X | m]) ω := by
      change μ[lam • X | m] =ᵐ[μ] lam • (μ[X | m])
      exact condExp_smul (μ := μ) lam X m
    filter_upwards [hsm, hmean] with ω hsmω hmeanω
    rw [hsmω, hmeanω]
    simp
  -- the `q ≥ 2` terms
  have hterm : ∀ q : ℕ, 2 ≤ q →
      μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m] ≤ᵐ[μ]
      fun ω => (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω := by
    intro q _
    have hpt : ∀ ω', (lam * X ω') ^ q / (Nat.factorial q : ℝ)
        ≤ (lam ^ q / (Nat.factorial q : ℝ)) * |X ω'| ^ q := by
      intro ω'
      have h1 : (lam * X ω') ^ q = lam ^ q * X ω' ^ q := by rw [mul_pow]
      have h2 : X ω' ^ q ≤ |X ω'| ^ q := by
        calc X ω' ^ q ≤ |X ω' ^ q| := le_abs_self _
          _ = |X ω'| ^ q := abs_pow _ _
      rw [h1, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (pow_nonneg hlam q))
        (Nat.cast_nonneg _)
    have hstep1 : μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m] ≤ᵐ[μ]
        μ[fun ω' => (lam ^ q / (Nat.factorial q : ℝ)) * |X ω'| ^ q | m] :=
      condExp_mono (hintf q) (hintg q) (Eventually.of_forall hpt)
    have hsm : μ[fun ω' => (lam ^ q / (Nat.factorial q : ℝ)) * |X ω'| ^ q | m] =ᵐ[μ]
        fun ω => (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω := by
      change μ[(lam ^ q / (Nat.factorial q : ℝ)) • (fun ω' => |X ω'| ^ q) | m]
        =ᵐ[μ] (lam ^ q / (Nat.factorial q : ℝ)) • μ[fun ω' => |X ω'| ^ q | m]
      exact condExp_smul (μ := μ) (lam ^ q / (Nat.factorial q : ℝ))
        (fun ω' => |X ω'| ^ q) m
    exact hstep1.trans hsm.le
  have hterm_ae : ∀ᵐ ω ∂μ, ∀ q : ℕ, 2 ≤ q →
      (μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω
        ≤ (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 2 ≤ q
    · filter_upwards [hterm q hq] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall (fun _ h => absurd h hq)
  filter_upwards [hinter, h0, h1, hterm_ae, hsumm, hg] with
    ω hinterω h0ω h1ω htermω hsummω hgω
  rw [hinterω]
  refine tsum_le_exp_of_majorant hsummω hgω ?_ ?_ h0ω h1ω ?_
  · simp
  · simp
  · intro q hq
    rw [if_neg (by omega : ¬ q < 2)]
    exact htermω q hq

end LatticeProb
