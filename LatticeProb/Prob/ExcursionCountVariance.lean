import LatticeProb.Prob.ExcursionCountSecondMoment
import LatticeProb.Prob.ExcursionCountGeometricTail

/-!
# The variance of the excursion count of Brownian motion is at most its mean

For a path `f : ℝ≥0 → ℝ`, `pathExcursionCount f b ε` is the number of excursions of `f` above its running minimum,
of length larger than `ε`, completed before the first passage of `f` strictly below `f 0 - b`. For a real Brownian
motion `B` with continuous paths, `b ≥ 0` and `ε > 0`, writing `J = pathExcursionCount B b ε`,

  `E [J²] ≤ E J + (E J)²`,  that is, `Var J ≤ E J`.

The proof splits the level `b` into `n` blocks of length `h = b / n`. The mean `m(c) = E J(c)` is additive in the
level and the second moment `s(c) = E J(c)²` satisfies `s(a + b) = s(a) + 2 m(a) m(b) + s(b)` (strong Markov property
at the first passage). Hence `s(b) + n m(h)² = n s(h) + m(b)²`. For one block,
`s(h) = m(h) + E[J(h)(J(h) - 1)] ≤ m(h) + 2 q² / (1 - q)²` with `q = P(J(h) ≥ 1) ≤ m(h) = m(b) / n`, so that
`s(b) ≤ m(b) + m(b)² + 8 m(b)² / n` for large `n`; let `n → ∞`.

* `moments_natCast_add_one_mul`: the block identities for an additive mean and a split second moment;
* `le_add_sq_of_moments`: the resulting bound `s(b) ≤ m(b) + m(b)²`, for abstract moment functions;
* `lintegral_pathExcursionCount_sq_le`: the bound for the excursion count of Brownian motion.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- An elementary bound: if `0 ≤ q`, `q n ≤ M` and `2 M ≤ n`, then `n · 2 q² / (1 - q)² ≤ 8 M² / n`. -/
theorem mul_two_sq_div_sq_le {q M n : ℝ} (hq0 : 0 ≤ q) (hn : 0 < n) (hqM : q * n ≤ M) (hM : 2 * M ≤ n) :
    n * (2 * q ^ 2 / (1 - q) ^ 2) ≤ 8 * M ^ 2 / n := by
  have hq : q ≤ 1 / 2 := by
    have h : q * n ≤ 1 / 2 * n := by linarith
    exact le_of_mul_le_mul_right h hn
  have h1 : 1 / 4 ≤ (1 - q) ^ 2 := by nlinarith
  have h2 : 2 * q ^ 2 / (1 - q) ^ 2 ≤ 8 * q ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg q]
  have hqn : 0 ≤ q * n := mul_nonneg hq0 hn.le
  have h3 : (q * n) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hqn hqM 2
  rw [le_div_iff₀ hn]
  calc n * (2 * q ^ 2 / (1 - q) ^ 2) * n ≤ n * (8 * q ^ 2) * n := by gcongr
    _ = 8 * (q * n) ^ 2 := by ring
    _ ≤ 8 * M ^ 2 := by gcongr

/-- **Block identities.** Let `m, s : ℝ → ℝ≥0∞` with `m (a + b) = m a + m b` and
`s (a + b) = s a + 2 m a m b + s b` for `a, b ≥ 0`. Then for `h ≥ 0` and `n : ℕ`, with `N = n + 1`:
`m (N h) = N m h` and `s (N h) + N (m h)² = N s h + (N m h)²`. -/
theorem moments_natCast_add_one_mul (m s : ℝ → ℝ≥0∞)
    (hm : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → m (a + b) = m a + m b)
    (hs : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → s (a + b) = s a + 2 * (m a * m b) + s b) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    m (((n : ℝ) + 1) * h) = ((n : ℝ≥0∞) + 1) * m h ∧
      s (((n : ℝ) + 1) * h) + ((n : ℝ≥0∞) + 1) * m h ^ 2 =
        ((n : ℝ≥0∞) + 1) * s h + (((n : ℝ≥0∞) + 1) * m h) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : (((n + 1 : ℕ) : ℝ) + 1) * h = ((n : ℝ) + 1) * h + h := by push_cast; ring
    have hnh : 0 ≤ ((n : ℝ) + 1) * h := mul_nonneg (by positivity) hh
    have hm' : m ((((n + 1 : ℕ) : ℝ) + 1) * h) = (((n + 1 : ℕ) : ℝ≥0∞) + 1) * m h := by
      rw [hL, hm _ _ hnh hh, ih.1]
      push_cast
      ring
    refine ⟨hm', ?_⟩
    rw [hL, hs _ _ hnh hh, ih.1]
    calc s (((n : ℝ) + 1) * h) + 2 * (((n : ℝ≥0∞) + 1) * m h * m h) + s h +
          (((n + 1 : ℕ) : ℝ≥0∞) + 1) * m h ^ 2
        = (s (((n : ℝ) + 1) * h) + ((n : ℝ≥0∞) + 1) * m h ^ 2) +
            (2 * (((n : ℝ≥0∞) + 1) * m h * m h) + s h + m h ^ 2) := by
          push_cast
          ring
      _ = (((n : ℝ≥0∞) + 1) * s h + (((n : ℝ≥0∞) + 1) * m h) ^ 2) +
            (2 * (((n : ℝ≥0∞) + 1) * m h * m h) + s h + m h ^ 2) := by rw [ih.2]
      _ = (((n + 1 : ℕ) : ℝ≥0∞) + 1) * s h + ((((n + 1 : ℕ) : ℝ≥0∞) + 1) * m h) ^ 2 := by
          push_cast
          ring

/-- **Second moment at most mean plus squared mean, from the block identities.** Let `m, s : ℝ → ℝ≥0∞` be as in
`moments_natCast_add_one_mul` and `q : ℝ → ℝ` with `0 ≤ q h ≤ (m h).toReal` and
`s h ≤ m h + 2 q(h)² / (1 - q(h))²` for `h ≥ 0`. If `m b < ∞` for some `b ≥ 0`, then `s b ≤ m b + (m b)²`. -/
theorem le_add_sq_of_moments (m s : ℝ → ℝ≥0∞) (q : ℝ → ℝ)
    (hm : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → m (a + b) = m a + m b)
    (hs : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → s (a + b) = s a + 2 * (m a * m b) + s b)
    (hq0 : ∀ h, 0 ≤ q h) (hqm : ∀ h, 0 ≤ h → q h ≤ (m h).toReal)
    (hsq : ∀ h, 0 ≤ h → s h ≤ m h + ENNReal.ofReal (2 * q h ^ 2 / (1 - q h) ^ 2))
    {b : ℝ} (hb : 0 ≤ b) (hmb : m b ≠ ⊤) :
    s b ≤ m b + m b ^ 2 := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set M := (m b).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hδ' : (0 : ℝ) < δ := hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * M) (8 * M ^ 2 / δ))
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set h := b / ((n : ℝ) + 1) with hh_def
  have hh : 0 ≤ h := div_nonneg hb hn1.le
  have hNh : ((n : ℝ) + 1) * h = b := by
    rw [hh_def]
    field_simp
  obtain ⟨h1, h2⟩ := moments_natCast_add_one_mul m s hm hs hh n
  rw [hNh] at h1 h2
  have hmh : m h ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by positivity)] at h1
    exact hmb h1
  have hMq : q h * ((n : ℝ) + 1) ≤ M := by
    rw [hM_def, h1, ENNReal.toReal_mul, mul_comm]
    have : ((n : ℝ≥0∞) + 1).toReal = (n : ℝ) + 1 := by
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top, ENNReal.toReal_natCast,
        ENNReal.toReal_one]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hqm h hh) hn1.le
  have h2M : 2 * M ≤ (n : ℝ) + 1 := by linarith [le_max_left (2 * M) (8 * M ^ 2 / δ)]
  have hkey := mul_two_sq_div_sq_le (hq0 h) hn1 hMq h2M
  have hsmall : 8 * M ^ 2 / ((n : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ hn1]
    have := le_max_right (2 * M) (8 * M ^ 2 / δ)
    have h8 : 8 * M ^ 2 / δ < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hδ'] at h8
    linarith
  have hE : ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (2 * q h ^ 2 / (1 - q h) ^ 2) ≤ (δ : ℝ≥0∞) := by
    have hc : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [hc, ← ENNReal.ofReal_mul hn1.le, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hkey.trans hsmall)
  calc s b ≤ s b + ((n : ℝ≥0∞) + 1) * m h ^ 2 := le_self_add
    _ = ((n : ℝ≥0∞) + 1) * s h + m b ^ 2 := by rw [h2, ← h1]
    _ ≤ ((n : ℝ≥0∞) + 1) * (m h + ENNReal.ofReal (2 * q h ^ 2 / (1 - q h) ^ 2)) + m b ^ 2 := by
        gcongr
        exact hsq h hh
    _ = m b + ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (2 * q h ^ 2 / (1 - q h) ^ 2) + m b ^ 2 := by
        rw [mul_add, ← h1]
    _ ≤ m b + δ + m b ^ 2 := by gcongr
    _ = m b + m b ^ 2 + δ := add_right_comm _ _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The variance of the excursion count is at most its mean.** For a real Brownian motion `B` with continuous
paths, `b ≥ 0` and `ε > 0`, the number `J` of excursions above the running minimum of length larger than `ε`
completed before the first passage below `B 0 - b` satisfies `E [J²] ≤ E J + (E J)²`. -/
theorem lintegral_pathExcursionCount_sq_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 ≤ b) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P ≤
      ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P +
        (∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) ^ 2 := by
  have hpt : ∀ x : ℕ, (x : ℝ≥0∞) ^ 2 = x + ((x * (x - 1) : ℕ) : ℝ≥0∞) := by
    intro x
    rcases x with _ | k
    · simp
    · rw [Nat.add_sub_cancel]
      push_cast
      ring
  have hmarkov : ∀ c : ℝ, P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) c ε} ≤
      ∫⁻ ω, (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) ∂P := by
    intro c
    have hS := measurableSet_le_pathExcursionCount hm hcont c hε 1
    rw [← lintegral_indicator_one hS]
    refine lintegral_mono (Set.indicator_le fun ω hω => ?_)
    rw [Pi.one_apply]
    exact_mod_cast hω
  refine le_add_sq_of_moments (fun c => ∫⁻ ω, (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) ∂P)
    (fun c => ∫⁻ ω, (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) ^ 2 ∂P)
    (fun c => (P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) c ε}).toReal)
    (fun a b ha hb => lintegral_pathExcursionCount_add hB hm hcont ha hb hε)
    (fun a b ha hb => lintegral_pathExcursionCount_add_sq hB hm hcont ha hb hε)
    (fun _ => ENNReal.toReal_nonneg)
    (fun c hc => ENNReal.toReal_mono (lintegral_pathExcursionCount_lt_top hB hm hcont hc hε).ne (hmarkov c))
    (fun c hc => ?_) hb (lintegral_pathExcursionCount_lt_top hB hm hcont hb hε).ne
  have hmeas : Measurable fun ω => (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) :=
    measurable_from_nat.comp (measurable_pathExcursionCount hm hcont c hε)
  show ∫⁻ ω, (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) ^ 2 ∂P ≤
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) ∂P +
      ENNReal.ofReal (2 * (P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) c ε}).toReal ^ 2 /
        (1 - (P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) c ε}).toReal) ^ 2)
  simp_rw [hpt]
  rw [lintegral_add_left hmeas]
  exact add_le_add le_rfl (lintegral_pathExcursionCount_mul_pred_le hB hm hcont hc hε)

end LatticeProb.LadderSet
