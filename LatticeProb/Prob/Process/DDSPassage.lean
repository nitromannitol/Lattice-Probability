import LatticeProb.Prob.Process.BDGSquare

/-!
# The characteristic-function bound from the exact stopped dyadic skeleton

Ported from the vertex-reinforced walk development. For a real continuous martingale `M` from `0`
with quadratic covariation `Q` at a deterministic time `T` and every `q ≥ 0`, the bound
`|E e^{i M_T} - e^{-q/2}| ≤ ½ E |Q - q|` follows from two inputs: the stopped dyadic skeleton with
exact square sum (`StoppedDyadicSkeletonExact`), built here from the optional stopping, stopping
time, path and full-sum components of the Burkholder–Davis–Gundy modules, and the discrete
characteristic-function bound for martingales with bounded increments (`DiscreteCFBound`).
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process.BdgUpperContinuous

noncomputable section

/-! ### The characteristic-function bound from the dyadic skeleton -/

/-- **Discrete characteristic-function bound, bounded increments.** For a discrete real martingale
`Z` from `0` whose increments are at most `b ≤ 1` on `i < N`, and every `q ≥ 0`,
`|E e^{i Z_N} - e^{-q/2}| ≤ ½ E |∑_{i<N} (Z_{i+1} - Z_i)² - q| + 4 b (1 + q)`. -/
def DiscreteCFBound : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ) {b q : ℝ},
    0 < b → b ≤ 1 → 0 ≤ q → Martingale Z 𝒢 P → (∀ ω, Z 0 ω = 0) →
    (∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) →
      ‖∫ ω, Complex.exp (Complex.I * ((Z N ω : ℝ) : ℂ)) ∂P -
          Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
        2⁻¹ * ∫ ω, |∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 - q| ∂P + 4 * b * (1 + q)

/-- **The stopped dyadic skeleton with exact square sum.**  This is `StoppedDyadicSkeleton` with
its last clause strengthened: on the event where the paths oscillate by less than `b` at the scale
`T / 2^n` and the realized covariation `rc_n` is at most `L`, the stopped skeleton agrees with the
path at the terminal time and, in addition, the sum of its squared increments equals `rc_n`.

The strengthening is needed for the characteristic-function bound.  The discrete bound controls
`E |∑ (Z_{i+1} - Z_i)² - q|`, which can be compared with `E |Q - q|` only if the square sum of the
skeleton is bounded below as well as above by `rc_n`; with the upper bound alone the square sum
may be much smaller than `rc_n` on the good event, and the passage to the limit fails.

The clause holds because, on the event of the last clause, the stopping time is never triggered, so
`Z_i = M_{t_i}` for every `i ≤ 2^n` and the square sum is `rc_n` by definition. -/
def StoppedDyadicSkeletonExact : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0),
    Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
    ∀ (n : ℕ) {b L : ℝ}, 0 < b → 0 ≤ L →
      ∃ (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ),
        Martingale Z 𝒢 P ∧ (∀ ω, Z 0 ω = 0) ∧
        (∀ i, i < 2 ^ n → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) ∧
        (∀ ω, ∑ i ∈ Finset.range (2 ^ n), (Z (i + 1) ω - Z i ω) ^ 2 ≤
          min (LatticeProb.Process.realizedCovar M T n ω 0 0 + b ^ 2) (L + 2 * b ^ 2)) ∧
        (∀ ω, (∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n →
            |M s ω 0 - M t ω 0| < b) →
          LatticeProb.Process.realizedCovar M T n ω 0 0 ≤ L →
          Z (2 ^ n) ω = M T ω 0 ∧
          ∑ i ∈ Finset.range (2 ^ n), (Z (i + 1) ω - Z i ω) ^ 2 =
            LatticeProb.Process.realizedCovar M T n ω 0 0)

end

end LatticeProb.Process.BdgUpperContinuous

namespace LatticeProb.Process.BdgUpperContinuous.DdsPassage

noncomputable section

/-! ### The continuous-time passage for the characteristic-function bound -/

/-- The characteristic-function integrand `x ↦ e^{i x}`. -/
def cfe (x : ℝ) : ℂ := Complex.exp (Complex.I * ((x : ℝ) : ℂ))

lemma norm_cfe (x : ℝ) : ‖cfe x‖ = 1 := Complex.norm_exp_I_mul_ofReal x

lemma continuous_cfe : Continuous cfe := by
  unfold cfe; fun_prop

lemma measurable_cfe : Measurable cfe := continuous_cfe.measurable

lemma norm_cfe_sub_le (x y : ℝ) : ‖cfe x - cfe y‖ ≤ 2 := by
  calc ‖cfe x - cfe y‖ ≤ ‖cfe x‖ + ‖cfe y‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_cfe, norm_cfe]; norm_num

lemma integrable_cfe {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) : Integrable (fun ω => cfe (X ω)) P :=
  Integrable.of_bound (measurable_cfe.comp hX).aestronglyMeasurable 1
    (Eventually.of_forall fun _ => (norm_cfe _).le)

lemma ofReal_norm_integral_cfe_sub_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y S : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hS : Measurable S) {q β K : ℝ} (hβ : 0 ≤ β) (hK : ∀ ω, |S ω - q| ≤ K)
    (hD : ‖∫ ω, cfe (X ω) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      2⁻¹ * ∫ ω, |S ω - q| ∂P + β) :
    ENNReal.ofReal ‖∫ ω, cfe (Y ω) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      ∫⁻ ω, ENNReal.ofReal (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2 + β) ∂P := by
  have hXi := integrable_cfe (P := P) hX
  have hYi := integrable_cfe (P := P) hY
  have hF1m : Measurable fun ω => ‖cfe (Y ω) - cfe (X ω)‖ :=
    ((measurable_cfe.comp hY).sub (measurable_cfe.comp hX)).norm
  have hF1 : Integrable (fun ω => ‖cfe (Y ω) - cfe (X ω)‖) P :=
    Integrable.of_bound hF1m.aestronglyMeasurable 2
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_cfe_sub_le _ _)
  have hF2m : Measurable fun ω => |S ω - q| := (hS.sub_const q).abs
  have hF2 : Integrable (fun ω => |S ω - q|) P :=
    Integrable.of_bound hF2m.aestronglyMeasurable K
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hK ω)
  have hF2' : Integrable (fun ω => |S ω - q| / 2) P := hF2.div_const 2
  have hsum : Integrable (fun ω => ‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2 + β) P :=
    (hF1.add hF2').add (integrable_const β)
  have hint : ∫ ω, (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2 + β) ∂P =
      ∫ ω, ‖cfe (Y ω) - cfe (X ω)‖ ∂P + 2⁻¹ * ∫ ω, |S ω - q| ∂P + β := by
    have e1 : ∫ ω, (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2 + β) ∂P =
        ∫ ω, (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2) ∂P + ∫ _ω, β ∂P :=
      integral_add (hF1.add hF2') (integrable_const β)
    have e2 : ∫ ω, (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2) ∂P =
        ∫ ω, ‖cfe (Y ω) - cfe (X ω)‖ ∂P + ∫ ω, |S ω - q| / 2 ∂P :=
      integral_add hF1 hF2'
    rw [e1, e2, integral_div, integral_const]
    simp [div_eq_inv_mul]
  have hreal : ‖∫ ω, cfe (Y ω) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      ∫ ω, (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2 + β) ∂P := by
    rw [hint]
    have h1 : ‖∫ ω, cfe (Y ω) ∂P - ∫ ω, cfe (X ω) ∂P‖ ≤ ∫ ω, ‖cfe (Y ω) - cfe (X ω)‖ ∂P := by
      rw [← integral_sub hYi hXi]
      exact norm_integral_le_integral_norm _
    have h2 := norm_sub_le_norm_sub_add_norm_sub (∫ ω, cfe (Y ω) ∂P) (∫ ω, cfe (X ω) ∂P)
      (Complex.exp ((-(q / 2) : ℝ) : ℂ))
    linarith
  calc _ ≤ ENNReal.ofReal (∫ ω, (‖cfe (Y ω) - cfe (X ω)‖ + |S ω - q| / 2 + β) ∂P) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := ofReal_integral_eq_lintegral_ofReal hsum
        (Eventually.of_forall fun ω => by positivity)

/-- Reverse Fatou step.  If measurable functions `h j` on a probability space are bounded by a
finite constant, every `h j` has integral at least `x`, and `limsup_j h j ≤ g` almost everywhere,
then `x ≤ ∫ g`. -/
lemma le_lintegral_of_limsup_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℕ → Ω → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hm : ∀ j, Measurable (h j)) (hb : ∀ j ω, h j ω ≤ c) {g : Ω → ℝ≥0∞}
    (hg : ∀ᵐ ω ∂P, limsup (fun j => h j ω) atTop ≤ g ω) {x : ℝ≥0∞}
    (hx : ∀ j, x ≤ ∫⁻ ω, h j ω ∂P) : x ≤ ∫⁻ ω, g ω ∂P := by
  have hfin : ∫⁻ _ω, c ∂P ≠ ∞ := by simp [hc]
  calc x = limsup (fun _ : ℕ => x) atTop := (limsup_const x).symm
    _ ≤ limsup (fun j => ∫⁻ ω, h j ω ∂P) atTop := limsup_le_limsup (Eventually.of_forall hx)
    _ ≤ ∫⁻ ω, limsup (fun j => h j ω) atTop ∂P :=
        limsup_lintegral_le (fun _ => c) hm (fun j => Eventually.of_forall (hb j)) hfin
    _ ≤ ∫⁻ ω, g ω ∂P := lintegral_mono_ae hg

/-- Pointwise: if `x j = Y` eventually then `‖e^{iY} - e^{i x j}‖ → 0`. -/
lemma tendsto_norm_cfe_sub {Y : ℝ} {x : ℕ → ℝ} (h : ∀ᶠ j in atTop, x j = Y) :
    Tendsto (fun j => ‖cfe Y - cfe (x j)‖) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with j hj
  rw [hj, sub_self, norm_zero]

/-- Pointwise: if `s j = r j` eventually and `r j → Q'`, then
`|s j - q| / 2 + β → |Q' - q| / 2 + β`. -/
lemma tendsto_abs_sub_half {q β Q' : ℝ} {s r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 Q'))
    (hs : ∀ᶠ j in atTop, s j = r j) :
    Tendsto (fun j => |s j - q| / 2 + β) atTop (𝓝 (|Q' - q| / 2 + β)) := by
  have h1 : Tendsto (fun j => |r j - q| / 2 + β) atTop (𝓝 (|Q' - q| / 2 + β)) :=
    ((hr.sub_const q).abs.div_const 2).add_const β
  refine h1.congr' ?_
  filter_upwards [hs] with j hj
  rw [hj]

/-- Pointwise limit of the integrand on the event where the skeleton is exact. -/
lemma tendsto_integrand_of_lt {Y q β Q' : ℝ} {x s r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 Q'))
    (hx : ∀ᶠ j in atTop, x j = Y) (hs : ∀ᶠ j in atTop, s j = r j) :
    Tendsto (fun j => ENNReal.ofReal (‖cfe Y - cfe (x j)‖ + |s j - q| / 2 + β)) atTop
      (𝓝 (ENNReal.ofReal (|Q' - q| / 2 + β))) := by
  have h1 := (tendsto_norm_cfe_sub hx).add (tendsto_abs_sub_half (q := q) (β := β) hr hs)
  rw [zero_add] at h1
  have h2 : Tendsto (fun j => ‖cfe Y - cfe (x j)‖ + |s j - q| / 2 + β) atTop
      (𝓝 (|Q' - q| / 2 + β)) := h1.congr (fun j => by ring)
  exact (ENNReal.continuous_ofReal.tendsto _).comp h2

/-- The bound `|s - q| ≤ L + 2 + q` for `0 ≤ s ≤ L + 2`. -/
lemma abs_sub_le_of_bounds {s q L : ℝ} (hq : 0 ≤ q) (hL : 0 ≤ L) (hs0 : 0 ≤ s)
    (hsL : s ≤ L + 2) : |s - q| ≤ L + 2 + q := by
  rw [abs_le]; constructor <;> linarith

/-- Uniform bound for the integrand, valid everywhere. -/
lemma integrand_le_const {Y x s q β L : ℝ} (hq : 0 ≤ q) (hL : 0 ≤ L) (hs0 : 0 ≤ s)
    (hsL : s ≤ L + 2) :
    ‖cfe Y - cfe x‖ + |s - q| / 2 + β ≤ β + (L / 2 + q / 2 + 3) := by
  have h1 := norm_cfe_sub_le Y x
  have h2 := abs_sub_le_of_bounds hq hL hs0 hsL
  linarith

/-- The per-level inequality with the truncation.  Let `Y` be the limit value and
`X j, S j` the terminal value and square sum of the `j`-th skeleton; assume the discrete bound at
every level, convergence of `rc j → Q'`, and that on `{Q' < L}` eventually `X j = Y` and
`S j = rc j`.  Then the characteristic function of `Y` is within the stated integral of
`e^{-q/2}`. -/
lemma ofReal_norm_integral_cfe_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) {Q' : Ω → ℝ}
    {X S rc : ℕ → Ω → ℝ} (hX : ∀ j, Measurable (X j)) (hS : ∀ j, Measurable (S j))
    (hrc : ∀ᵐ ω ∂P, Tendsto (fun j => rc j ω) atTop (𝓝 (Q' ω)))
    {q β L : ℝ} (hq : 0 ≤ q) (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hS0 : ∀ j ω, 0 ≤ S j ω) (hSL : ∀ j ω, S j ω ≤ L + 2)
    (hD : ∀ j, ‖∫ ω, cfe (X j ω) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      2⁻¹ * ∫ ω, |S j ω - q| ∂P + β)
    (hgood : ∀ᵐ ω ∂P, Q' ω < L → ∀ᶠ j in atTop, X j ω = Y ω ∧ S j ω = rc j ω) :
    ENNReal.ofReal ‖∫ ω, cfe (Y ω) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      ∫⁻ ω, (ENNReal.ofReal (|Q' ω - q| / 2 + β) +
        {ω | L ≤ Q' ω}.indicator (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3)) ω) ∂P := by
  refine le_lintegral_of_limsup_le (h := fun j ω =>
      ENNReal.ofReal (‖cfe (Y ω) - cfe (X j ω)‖ + |S j ω - q| / 2 + β))
    (c := ENNReal.ofReal (β + (L / 2 + q / 2 + 3))) ENNReal.ofReal_ne_top ?_ ?_ ?_ ?_
  · intro j
    exact ((((measurable_cfe.comp hY).sub (measurable_cfe.comp (hX j))).norm.add
      (((hS j).sub_const q).abs.div_const 2)).add_const β).ennreal_ofReal
  · intro j ω
    exact ENNReal.ofReal_le_ofReal
      (integrand_le_const hq hL (hS0 j ω) (hSL j ω))
  · filter_upwards [hrc, hgood] with ω hr hg
    by_cases hlt : Q' ω < L
    · have hx : ∀ᶠ j in atTop, X j ω = Y ω := (hg hlt).mono fun j h => h.1
      have hs : ∀ᶠ j in atTop, S j ω = rc j ω := (hg hlt).mono fun j h => h.2
      have hlim := tendsto_integrand_of_lt (q := q) (β := β) (Y := Y ω) (x := fun j => X j ω)
        (s := fun j => S j ω) (r := fun j => rc j ω) hr hx hs
      rw [hlim.limsup_eq]
      exact le_self_add
    · have hmem : ω ∈ {ω | L ≤ Q' ω} := not_lt.1 hlt
      have hle : limsup (fun j => ENNReal.ofReal (‖cfe (Y ω) - cfe (X j ω)‖ +
          |S j ω - q| / 2 + β)) atTop ≤ ENNReal.ofReal (β + (L / 2 + q / 2 + 3)) :=
        limsup_le_of_le (h := Eventually.of_forall fun j => ENNReal.ofReal_le_ofReal
          (integrand_le_const hq hL (hS0 j ω) (hSL j ω)))
      refine hle.trans ?_
      rw [Set.indicator_of_mem hmem]
      have h1 := le_abs_self (Q' ω - q)
      have h2 := abs_nonneg (Q' ω - q)
      have hLQ : L ≤ Q' ω := hmem
      calc ENNReal.ofReal (β + (L / 2 + q / 2 + 3))
          ≤ ENNReal.ofReal ((|Q' ω - q| / 2 + β) + (|Q' ω - q| / 2 + q + 3)) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ _ := ENNReal.ofReal_add_le
  · intro j
    exact ofReal_norm_integral_cfe_sub_le (hX j) hY (hS j) (K := L + 2 + q) hβ
      (fun ω => abs_sub_le_of_bounds hq hL (hS0 j ω) (hSL j ω)) (hD j)

/-- Half of a nonnegative real number, in `ℝ≥0∞`. -/
lemma ofReal_half (a : ℝ) : ENNReal.ofReal (a / 2) = 2⁻¹ * ENNReal.ofReal a := by
  have h : a / 2 = 2⁻¹ * a := by ring
  rw [h, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]

/-- Splitting the right-hand side of the per-level inequality into the main term, the constant
`β` and the tail term. -/
lemma lintegral_rhs_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Q' : Ω → ℝ} (hQ' : Measurable Q') (q β L : ℝ) :
    ∫⁻ ω, (ENNReal.ofReal (|Q' ω - q| / 2 + β) +
        {ω | L ≤ Q' ω}.indicator (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3)) ω) ∂P ≤
      2⁻¹ * ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P + ENNReal.ofReal β +
        ∫⁻ ω, {ω | L ≤ Q' ω}.indicator
          (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3)) ω ∂P := by
  have hm1 : Measurable fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + β) :=
    ((((hQ'.sub_const q).abs).div_const 2).add_const β).ennreal_ofReal
  rw [lintegral_add_left hm1]
  have hmain : ∫⁻ ω, ENNReal.ofReal (|Q' ω - q| / 2 + β) ∂P ≤
      2⁻¹ * ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P + ENNReal.ofReal β := by
    calc ∫⁻ ω, ENNReal.ofReal (|Q' ω - q| / 2 + β) ∂P
        ≤ ∫⁻ ω, (2⁻¹ * ENNReal.ofReal |Q' ω - q| + ENNReal.ofReal β) ∂P := by
          refine lintegral_mono fun ω => ?_
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ofReal_half]
      _ = 2⁻¹ * ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P + ENNReal.ofReal β := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul _ ((hQ'.sub_const q).abs.ennreal_ofReal),
            lintegral_const, measure_univ, mul_one]
  exact add_le_add hmain le_rfl

/-- The integral over the tail event tends to `0`: if `∫ |Q' - q|` is finite and
`L k → ∞`, then `∫_{L k ≤ Q'} (|Q' - q| / 2 + q + 3) → 0`.  Dominated convergence with the
integrable bound `|Q' - q| / 2 + q + 3`; the indicators vanish pointwise for large `k`. -/
lemma tendsto_lintegral_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Q' : Ω → ℝ} (hQ' : Measurable Q') {q : ℝ}
    (hA : ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P ≠ ∞) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun k => ∫⁻ ω, {ω | L k ≤ Q' ω}.indicator
      (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3)) ω ∂P) atTop (𝓝 0) := by
  have hdm : Measurable fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3) :=
    ((((hQ'.sub_const q).abs).div_const 2).add_const q |>.add_const 3).ennreal_ofReal
  have hfin : ∫⁻ ω, ENNReal.ofReal (|Q' ω - q| / 2 + q + 3) ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω => ?_ :
      ∫⁻ ω, ENNReal.ofReal (|Q' ω - q| / 2 + q + 3) ∂P ≤
        ∫⁻ ω, (2⁻¹ * ENNReal.ofReal |Q' ω - q| + ENNReal.ofReal (q + 3)) ∂P)
    · rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul _ ((hQ'.sub_const q).abs.ennreal_ofReal),
        lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hA, ENNReal.ofReal_ne_top⟩
    · have h : |Q' ω - q| / 2 + q + 3 = |Q' ω - q| / 2 + (q + 3) := by ring
      rw [h]
      refine ENNReal.ofReal_add_le.trans ?_
      rw [ofReal_half]
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun k ω => {ω | L k ≤ Q' ω}.indicator
      (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3)) ω)
    (f := fun _ => 0) (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3))
    (fun k => hdm.indicator (measurableSet_le measurable_const hQ'))
    (fun k => Eventually.of_forall fun ω => Set.indicator_le_self _ _ ω) hfin ?_
  · simpa using hlim
  · refine Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hL.eventually_gt_atTop (Q' ω)] with k hk
    rw [Set.indicator_of_notMem (by simpa using hk)]

/-- Removing the localisation and the bound on the increments.  If for every
`b ∈ (0, 1]` and every `k`, `x ≤ A' + ofReal (4 b (1 + q)) + tail k` with `tail k → 0`, then
`x ≤ A'`. -/
lemma le_of_forall_b_tail {x A' : ℝ≥0∞} {tail : ℕ → ℝ≥0∞} (htail : Tendsto tail atTop (𝓝 0))
    {q : ℝ}
    (h : ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ k, x ≤ A' + ENNReal.ofReal (4 * b * (1 + q)) + tail k) :
    x ≤ A' := by
  have h1 : ∀ b : ℝ, 0 < b → b ≤ 1 → x ≤ A' + ENNReal.ofReal (4 * b * (1 + q)) := by
    intro b hb hb1
    have := ge_of_tendsto (htail.const_add (A' + ENNReal.ofReal (4 * b * (1 + q))))
      (Eventually.of_forall (h b hb hb1))
    simpa using this
  have hcont : Continuous fun b : ℝ => 4 * b * (1 + q) := by fun_prop
  have hb0 : Tendsto (fun b : ℝ => ENNReal.ofReal (4 * b * (1 + q))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h2 : Tendsto (fun b : ℝ => 4 * b * (1 + q)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.tendsto_ofReal h2
  have hlim := hb0.const_add A'
  have := ge_of_tendsto hlim (by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with b hb
    exact h1 b hb.1 hb.2)
  simpa using this

/-! ### The skeleton with exact square sum, and the per-level inequality -/


/-- The skeleton with exact square sum is in particular a `StoppedDyadicSkeleton`. -/
theorem stoppedDyadicSkeleton_of_exact (h : StoppedDyadicSkeletonExact) :
    StoppedDyadicSkeleton := by
  intro Ω _ P _ ℱ M T hM hcont h0 n b L hb hL
  obtain ⟨𝒢, Z, h1, h2, h3, h4, h5⟩ := h P ℱ M T hM hcont h0 n hb hL
  exact ⟨𝒢, Z, h1, h2, h3, h4, fun ω hω hrc => (h5 ω hω hrc).1⟩

/-- The `0`-coordinate of a one-dimensional continuous-time martingale is a measurable function
at every time. -/
lemma measurable_coord_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → Fin 1 → ℝ}
    (hM : Martingale M ℱ P) (t : ℝ≥0) : Measurable fun ω => M t ω 0 :=
  (measurable_pi_apply 0).comp (((hM.stronglyMeasurable t).mono (ℱ.le t)).measurable)

/-- Each realized covariation `rc_n` is measurable. -/
lemma measurable_realizedCovar_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → Fin 1 → ℝ}
    (hM : Martingale M ℱ P) (T : ℝ≥0) (n : ℕ) :
    Measurable fun ω => LatticeProb.Process.realizedCovar M T n ω 0 0 := by
  simp only [LatticeProb.Process.realizedCovar]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact ((measurable_coord_zero hM _).sub (measurable_coord_zero hM _)).mul
    ((measurable_coord_zero hM _).sub (measurable_coord_zero hM _))

/-- **The per-level inequality for a continuous martingale.**  Let `rc (ns j) → Q'` almost everywhere along a
strictly increasing sequence of levels.  For `b ∈ (0, 1]` and `L ≥ 0`, apply the exact stopped
skeleton at level `ns j` and the discrete bound to each of them; on `{Q' < L}` the skeleton agrees
with `M_T` and has square sum `rc (ns j)` for all large `j`.  Then `E e^{i M_T}` is within
`∫ (|Q' - q| / 2 + 4 b (1 + q)) + ∫_{L ≤ Q'} (|Q' - q| / 2 + q + 3)` of `e^{-q/2}`. -/
lemma key_bL (hS : StoppedDyadicSkeletonExact) (hD : DiscreteCFBound)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
    (hM : Martingale M ℱ P) (hcont : ∀ ω, Continuous fun t => M t ω) (h0 : ∀ ω, M 0 ω = 0)
    {ns : ℕ → ℕ} (hns : StrictMono ns) {Q' : Ω → ℝ}
    (hae' : ∀ᵐ ω ∂P, Tendsto (fun j => LatticeProb.Process.realizedCovar M T (ns j) ω 0 0) atTop (𝓝 (Q' ω)))
    {q b L : ℝ} (hq : 0 ≤ q) (hb : 0 < b) (hb1 : b ≤ 1) (hL : 0 ≤ L) :
    ENNReal.ofReal ‖∫ ω, cfe (M T ω 0) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      ∫⁻ ω, (ENNReal.ofReal (|Q' ω - q| / 2 + 4 * b * (1 + q)) +
        {ω | L ≤ Q' ω}.indicator (fun ω => ENNReal.ofReal (|Q' ω - q| / 2 + q + 3)) ω) ∂P := by
  have hSn := fun n : ℕ => hS P ℱ M T hM hcont h0 n hb hL
  choose 𝒢 Z hZ using hSn
  have hZm : ∀ n i, Measurable (Z n i) := fun n i =>
    (((hZ n).1.stronglyMeasurable i).mono ((𝒢 n).le i)).measurable
  refine ofReal_norm_integral_cfe_le (measurable_coord_zero hM T)
    (X := fun j ω => Z (ns j) (2 ^ ns j) ω)
    (S := fun j ω => ∑ i ∈ Finset.range (2 ^ ns j), (Z (ns j) (i + 1) ω - Z (ns j) i ω) ^ 2)
    (rc := fun j ω => LatticeProb.Process.realizedCovar M T (ns j) ω 0 0)
    (fun j => hZm _ _) (fun j => ?_) hae' hq (by positivity) hL (fun j ω => ?_)
    (fun j ω => ?_) (fun j => ?_) ?_
  · exact Finset.measurable_sum _ fun i _ => ((hZm _ _).sub (hZm _ _)).pow_const 2
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · have h1 := (hZ (ns j)).2.2.2.1 ω
    have h2 : 2 * b ^ 2 ≤ 2 := by nlinarith
    exact (h1.trans (min_le_right _ _)).trans (by linarith)
  · exact hD P (𝒢 (ns j)) (Z (ns j)) (2 ^ ns j) hb hb1 hq (hZ (ns j)).1 (hZ (ns j)).2.1
      (hZ (ns j)).2.2.1
  · filter_upwards [hae'] with ω hω hlt
    have h1 : ∀ᶠ j in atTop, LatticeProb.Process.realizedCovar M T (ns j) ω 0 0 ≤ L :=
      (hω.eventually (gt_mem_nhds hlt)).mono fun j hj => hj.le
    have hcontω : Continuous fun t => M t ω 0 := (continuous_apply 0).comp (hcont ω)
    have h2 : ∀ᶠ j in atTop, ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
        |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ (ns j) → |M s ω 0 - M t ω 0| < b :=
      hns.tendsto_atTop.eventually (eventually_modulus_lt hcontω T hb)
    filter_upwards [h1, h2] with j hj1 hj2
    exact (hZ (ns j)).2.2.2.2 ω hj2 hj1

/-- **The characteristic-function bound from the stopped skeleton with exact square
sum and the discrete bound.**  For a real continuous martingale `M` from `0` with
`HasQuadCovar P M T Q` and every `q ≥ 0`,
`|E e^{i M_T} - e^{-q/2}| ≤ ½ E |Q - q|`.

Proof.  If `E |Q - q| = ∞` there is nothing to prove.  Otherwise fix `b ∈ (0, 1]` and let
`L → ∞` along `L k = k + q + 1`.  Along a subsequence `rc (ns j) → Q` almost surely; the key
per-level inequality (`key_bL`) bounds the left side by `½ E |Q - q| + 4 b (1 + q)` plus the
integral of `|Q - q| / 2 + q + 3` over `{L k ≤ Q}`, which tends to `0` by dominated convergence
(`tendsto_lintegral_tail`); then `b → 0` (`le_of_forall_b_tail`). -/
theorem dambisDubinsSchwarz_of_skeleton_exact (hS : StoppedDyadicSkeletonExact)
    (hD : DiscreteCFBound) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
      (Q : Ω → Fin 1 → Fin 1 → ℝ),
      Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
      LatticeProb.Process.HasQuadCovar P M T Q → ∀ q : ℝ, 0 ≤ q →
        ENNReal.ofReal ‖∫ ω, Complex.exp (Complex.I * ((M T ω 0 : ℝ) : ℂ)) ∂P -
            Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
          2⁻¹ * ∫⁻ ω, ENNReal.ofReal |Q ω 0 0 - q| ∂P := by
  intro Ω _ P _ ℱ M T Q hM hcont h0 hQ q hq
  by_cases hinf : ∫⁻ ω, ENNReal.ofReal |Q ω 0 0 - q| ∂P = ⊤
  · rw [hinf]; simp
  have hQ0 := hasQuadCovar_coord hQ
  obtain ⟨ns, hns, hae⟩ := hQ0.exists_seq_tendsto_ae
  have hQm : AEMeasurable (fun ω => Q ω 0 0) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun j => (measurable_realizedCovar_zero hM T (ns j)).aemeasurable) hae
  obtain ⟨Q', hQ'm, hQQ'⟩ := hQm
  have hae' : ∀ᵐ ω ∂P,
      Tendsto (fun j => LatticeProb.Process.realizedCovar M T (ns j) ω 0 0) atTop (𝓝 (Q' ω)) := by
    filter_upwards [hae, hQQ'] with ω h1 h2
    have h2' : Q ω 0 0 = Q' ω := h2
    rw [h2'] at h1
    exact h1
  have hA : ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P = ∫⁻ ω, ENNReal.ofReal |Q ω 0 0 - q| ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hQQ'] with ω h
    have h' : Q ω 0 0 = Q' ω := h
    rw [h']
  rw [← hA]
  have hAfin : ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P ≠ ⊤ := hA ▸ hinf
  have hLt : Tendsto (fun k : ℕ => (k : ℝ) + q + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have htail := tendsto_lintegral_tail (P := P) hQ'm hAfin hLt
  refine le_of_forall_b_tail (q := q) (A' := 2⁻¹ * ∫⁻ ω, ENNReal.ofReal |Q' ω - q| ∂P) htail ?_
  intro b hb hb1 k
  have hLk : (0 : ℝ) ≤ (k : ℝ) + q + 1 := by positivity
  have h1 := key_bL hS hD P ℱ M T hM hcont h0 hns hae' hq hb hb1 hLk
  have h2 := lintegral_rhs_le (P := P) hQ'm q (4 * b * (1 + q)) ((k : ℝ) + q + 1)
  exact h1.trans h2

end

end LatticeProb.Process.BdgUpperContinuous.DdsPassage

namespace LatticeProb.Process.BdgUpperContinuous.ExactAssembly

noncomputable section


/-- **The stopped dyadic skeleton with exact square sum, from its four components**: optional
stopping for continuous martingales, the localising time being a stopping time, the path
bookkeeping of the skeleton, and the full-sum identity on the good event. -/
theorem stoppedDyadicSkeletonExact_of_components
    (hOST : LatticeProb.Process.StoppedSkeleton.ContinuousStoppedMartingale)
    (hStop : LatticeProb.Process.StoppedSkeleton.SkeletonStopIsStoppingTime)
    (hPath : LatticeProb.Process.StoppedSkeleton.SkeletonPathFacts)
    (hFull : LatticeProb.Process.StoppedSkeleton.SkeletonFullSum) : StoppedDyadicSkeletonExact := by
  intro Ω _ P _ ℱ M T hM hcont h0 n b L hb hL
  let X : ℝ≥0 → Ω → ℝ := fun t ω => M t ω 0
  have hX : Martingale X ℱ P := LowerAssembly.martingale_coord_zero hM
  have hXcont : ∀ ω, Continuous fun t => X t ω :=
    fun ω => (continuous_apply (0 : Fin 1)).comp (hcont ω)
  have hτ := hStop ℱ X hX.1 hXcont T n b L
  have hY := hOST P ℱ X _ hX hXcont hτ
  let g : ℕ → ℝ≥0 := fun k => LatticeProb.Process.StoppedSkeleton.gridT T n (min k (2 ^ n))
  have hg : Monotone g := LowerAssembly.cappedGridT_monotone T n
  let 𝒢 : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨fun k => ℱ (g k), fun _ _ hij => ℱ.mono (hg hij), fun k => ℱ.le _⟩
  refine ⟨𝒢, fun k ω => LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L k,
    ⟨fun k => hY.1 (g k), fun i j hij => hY.2 (g i) (g j) (hg hij)⟩, ?_, ?_, ?_, ?_⟩
  · intro ω
    have h := (hPath (fun t => X t ω) (hXcont ω) T n hb hL).1
    show LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L 0 = 0
    rw [h]
    show M 0 ω 0 = 0
    simp [h0 ω]
  · intro i hi ω
    exact (hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.1 i hi
  · intro ω
    have h := (hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.2.1
    rw [LatticeProb.Process.StoppedSkeleton.realizedCovar_eq_gridSq]
    exact h
  · intro ω hmod hrc
    rw [LatticeProb.Process.StoppedSkeleton.realizedCovar_eq_gridSq] at hrc ⊢
    exact ⟨(hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.2.2 hmod hrc,
      hFull (fun t => X t ω) (hXcont ω) T n hb hL hmod hrc⟩

end

end LatticeProb.Process.BdgUpperContinuous.ExactAssembly

namespace LatticeProb.Process.BdgUpperContinuous

noncomputable section

/-- **The stopped dyadic skeleton with exact square sum** exists: optional stopping for continuous
martingales, the stopping-time property of the localising time, the path bookkeeping and the
full-sum identity on the good event assemble to the skeleton whose square sum is exactly the
realized covariation on the good event. -/
theorem stoppedDyadicSkeletonExact_holds : StoppedDyadicSkeletonExact :=
  ExactAssembly.stoppedDyadicSkeletonExact_of_components
    (LatticeProb.Process.StoppedSkeleton.ContinuousOST.continuousStoppedMartingale_of_countable
      LatticeProb.Process.StoppedSkeleton.CountableOST.countableRangeStoppedIntegral_holds)
    LatticeProb.Process.StoppedSkeleton.StoppingTime.skeletonStopIsStoppingTime_holds
    LatticeProb.Process.StoppedSkeleton.PathFacts.skeletonPathFacts_holds
    LatticeProb.Process.StoppedSkeleton.FullSum.skeletonFullSum_holds

end

end LatticeProb.Process.BdgUpperContinuous
