import Mathlib
import LatticeProb.Prob.LevyProkhorovLipschitz

/-!
# Replacing the walk laws by the law field in an atomic pairing

Let `s` be a finite index set with weights `c x ≥ 0` and points `p x ∈ ℂ`, let `Q x` be laws on a
path space `Ω` and `P : ℂ → ProbabilityMeasure Ω` a law field. For a time-`t` evaluation `e : Ω → ℂ`
(`e X = X t` on the path space) and bounded `f, ψ : ℂ → ℝ` and a bounded Lipschitz `g : ℂ → ℝ`, this
file bounds the cost of replacing `Q x` by `P (p x)` in the atomic pairing
`Σ_{x ∈ s} c x f(p x) ψ(p x) E_{Q x}[g(e X)]`.

The Lévy–Prokhorov distance needs a pseudometric on the path space. The integrand `X ↦ g (e X)` is
controlled through the truncation inequality `min 1 |e X - e Y| ≤ Λ d(X, Y)`; for the local uniform
metric `d` on `C(ℝ≥0, ℂ)` with `d(X, Y) ≥ e^{-T} (1 ∧ sup_{[0,T]} |X - Y|)` and the evaluation at a
time `t ≤ T`, it holds with `Λ = e^T`; it also holds with `Λ` a Lipschitz constant of `e`
(`min_one_dist_le_of_lipschitzWith`).

## Main results

* `abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_abs_le`: for `|F| ≤ C_F` and `F`
  `L`-Lipschitz, `|∫ F dμ - ∫ F dν| ≤ (L + 2 C_F) a` when the Lévy–Prokhorov distance of `μ, ν` is
  `< a`.
* `lipschitzWith_comp_of_min_one_dist_le`: under the truncation inequality, `X ↦ g (e X)` is
  `max K (2 C_g) Λ`-Lipschitz.
* `levyProkhorovEvalBound K C_g Λ a = (max K (2 C_g) Λ + 2 C_g) a`, the resulting bound of
  `|E_μ[g(e X)] - E_ν[g(e X)]|`, and `tendsto_levyProkhorovEvalBound`: it tends to `0` as `a → 0⁺`.
* `abs_sum_mul_integral_sub_sum_mul_integral_le`: replacing `Q x` by `P (p x)` in the atomic pairing
  costs at most `C_f C_ψ B Σ_{x ∈ s, ψ(p x) ≠ 0} c x`, with `B = levyProkhorovEvalBound K C_g Λ a`,
  when `Q x` and `P (p x)` are at Lévy–Prokhorov distance `< a` for every `x ∈ s` with `ψ(p x) ≠ 0`.
* `atomicMeasure s c p = Σ_{x ∈ s} c x δ_{p x}`, `integral_atomicMeasure_mul`: the second pairing is
  `∫ f(z) E_{P z}[g(e X)] ψ(z) dν(z)` with `ν = atomicMeasure s c p`, and
  `atomicMeasure_real_support`: `ν(supp ψ) = Σ_{x ∈ s, ψ(p x) ≠ 0} c x`.
* `abs_sum_mul_integral_sub_integral_atomicMeasure_le`: the combined bound
  `|Σ_x c x f(p x) ψ(p x) E_{Q x}[g(e X)] - ∫ f(z) E_{P z}[g(e X)] ψ(z) dν(z)| ≤ C_f C_ψ B ν(supp ψ)`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LatticeProb

/-! ### Bounded Lipschitz functionals and the Lévy–Prokhorov distance -/

/-- If `|F| ≤ C_F`, `F` is `L`-Lipschitz and the Lévy–Prokhorov distance of the probability
measures `μ, ν` is `< a`, then `|∫ F dμ - ∫ F dν| ≤ (L + 2 C_F) a`. -/
theorem abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_abs_le {Ω : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a : ℝ} (ha : 0 < a)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal a) {F : Ω → ℝ} {CF : ℝ}
    (hFb : ∀ X, |F X| ≤ CF) {L : ℝ≥0} (hFL : LipschitzWith L F) :
    |∫ X, F X ∂μ - ∫ X, F X ∂ν| ≤ (L + 2 * CF) * a := by
  have hne : Nonempty Ω := by
    rcases isEmpty_or_nonempty Ω with h | h
    · exact absurd (Measure.eq_zero_of_isEmpty μ) (IsProbabilityMeasure.ne_zero μ)
    · exact h
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hFb (Classical.arbitrary Ω))
  let Fb : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨F, hFL.continuous⟩ (2 * CF)
    (fun X Y => by
      show dist (F X) (F Y) ≤ 2 * CF
      rw [Real.dist_eq]
      have h1 := abs_le.mp (hFb X)
      have h2 := abs_le.mp (hFb Y)
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have hnorm : ‖Fb‖ ≤ CF := (BoundedContinuousFunction.norm_le hCF).mpr (fun X => by
    show ‖F X‖ ≤ CF
    rw [Real.norm_eq_abs]
    exact hFb X)
  have hL : LipschitzWith L Fb := hFL
  have h := abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_lipschitz μ ν ha hμν Fb hL
  calc |∫ X, F X ∂μ - ∫ X, F X ∂ν| = |∫ X, Fb X ∂μ - ∫ X, Fb X ∂ν| := rfl
    _ ≤ (L + 2 * ‖Fb‖) * a := h
    _ ≤ (L + 2 * CF) * a := mul_le_mul_of_nonneg_right (by linarith) ha.le

/-- A bounded Lipschitz function is controlled by the truncated distance: if `|g| ≤ C_g` and `g` is
`K`-Lipschitz, then `|g z - g w| ≤ max K (2 C_g) · min 1 d(z, w)`. -/
theorem dist_le_max_mul_min_one_of_lipschitzWith {E : Type*} [PseudoMetricSpace E] {g : E → ℝ}
    {Cg : ℝ} (hgb : ∀ z, |g z| ≤ Cg) {K : ℝ≥0} (hgl : LipschitzWith K g) (z w : E) :
    dist (g z) (g w) ≤ max (K : ℝ) (2 * Cg) * min 1 (dist z w) := by
  have h1 : dist (g z) (g w) ≤ K * dist z w := hgl.dist_le_mul z w
  have h2 : dist (g z) (g w) ≤ 2 * Cg := by
    rw [Real.dist_eq]
    have hz := abs_le.mp (hgb z)
    have hw := abs_le.mp (hgb w)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases le_total (dist z w) 1 with h | h
  · rw [min_eq_right h]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
  · rw [min_eq_left h, mul_one]
    exact h2.trans (le_max_right _ _)

/-- A `Λ`-Lipschitz map satisfies the truncation inequality `min 1 d(e X, e Y) ≤ Λ d(X, Y)`. -/
theorem min_one_dist_le_of_lipschitzWith {Ω E : Type*} [PseudoMetricSpace Ω] [PseudoMetricSpace E]
    {e : Ω → E} {Λ : ℝ≥0} (he : LipschitzWith Λ e) (X Y : Ω) :
    min 1 (dist (e X) (e Y)) ≤ Λ * dist X Y :=
  (min_le_right _ _).trans (he.dist_le_mul X Y)

/-- **Truncation.** If `min 1 d(e X, e Y) ≤ Λ d(X, Y)` for all `X, Y`, `|g| ≤ C_g` and `g` is
`K`-Lipschitz, then `X ↦ g (e X)` is `max K (2 C_g) Λ`-Lipschitz. For the evaluation at a time
`t ≤ T` and a path metric with `d(X, Y) ≥ e^{-T} (1 ∧ sup_{[0,T]} |X - Y|)`, take `Λ = e^T`. -/
theorem lipschitzWith_comp_of_min_one_dist_le {Ω E : Type*} [PseudoMetricSpace Ω]
    [PseudoMetricSpace E] {g : E → ℝ} {Cg : ℝ} (hgb : ∀ z, |g z| ≤ Cg) {K : ℝ≥0}
    (hgl : LipschitzWith K g) {e : Ω → E} {Λ : ℝ≥0}
    (he : ∀ X Y, min 1 (dist (e X) (e Y)) ≤ Λ * dist X Y) :
    LipschitzWith (Real.toNNReal (max (K : ℝ) (2 * Cg) * Λ)) (fun X => g (e X)) := by
  refine LipschitzWith.of_dist_le_mul fun X Y => ?_
  have hM : 0 ≤ max (K : ℝ) (2 * Cg) := (NNReal.coe_nonneg K).trans (le_max_left _ _)
  rw [Real.coe_toNNReal _ (mul_nonneg hM Λ.coe_nonneg), mul_assoc]
  exact (dist_le_max_mul_min_one_of_lipschitzWith hgb hgl (e X) (e Y)).trans
    (mul_le_mul_of_nonneg_left (he X Y) hM)

/-- The bound `(max K (2 C_g) Λ + 2 C_g) a` of `|E_μ[g(e X)] - E_ν[g(e X)]|` for laws `μ, ν` at
Lévy–Prokhorov distance `< a`, a `K`-Lipschitz `g` with `|g| ≤ C_g` and an evaluation `e` with
`min 1 d(e X, e Y) ≤ Λ d(X, Y)`: the bound `(L + 2 ‖F‖) a` of
`abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_lipschitz` for `F = g ∘ e`, with the
Lipschitz constant `L = max K (2 C_g) Λ` of `lipschitzWith_comp_of_min_one_dist_le` and `‖F‖ ≤ C_g`. -/
noncomputable def levyProkhorovEvalBound (K : ℝ≥0) (Cg : ℝ) (Λ : ℝ≥0) (a : ℝ) : ℝ :=
  (max (K : ℝ) (2 * Cg) * Λ + 2 * Cg) * a

/-- `levyProkhorovEvalBound K C_g Λ a → 0` as `a → 0⁺`. -/
theorem tendsto_levyProkhorovEvalBound (K : ℝ≥0) (Cg : ℝ) (Λ : ℝ≥0) :
    Tendsto (levyProkhorovEvalBound K Cg Λ) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (levyProkhorovEvalBound K Cg Λ) := by
    show Continuous fun a : ℝ => (max (K : ℝ) (2 * Cg) * Λ + 2 * Cg) * a
    exact continuous_const.mul continuous_id
  have h0 : levyProkhorovEvalBound K Cg Λ 0 = 0 := by
    simp [levyProkhorovEvalBound]
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [h0] at h

/-- Per atom: if the Lévy–Prokhorov distance of `μ, ν` is `< a`, then
`|E_μ[g(e X)] - E_ν[g(e X)]| ≤ levyProkhorovEvalBound K C_g Λ a`. -/
theorem abs_integral_comp_sub_integral_comp_le_levyProkhorovEvalBound {Ω E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] [PseudoMetricSpace E]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a : ℝ} (ha : 0 < a)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal a) {g : E → ℝ} {Cg : ℝ}
    (hgb : ∀ z, |g z| ≤ Cg) {K : ℝ≥0} (hgl : LipschitzWith K g) {e : Ω → E} {Λ : ℝ≥0}
    (he : ∀ X Y, min 1 (dist (e X) (e Y)) ≤ Λ * dist X Y) :
    |∫ X, g (e X) ∂μ - ∫ X, g (e X) ∂ν| ≤ levyProkhorovEvalBound K Cg Λ a := by
  have hM : 0 ≤ max (K : ℝ) (2 * Cg) * Λ :=
    mul_nonneg ((NNReal.coe_nonneg K).trans (le_max_left _ _)) Λ.coe_nonneg
  have h := abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_abs_le μ ν ha hμν
    (fun X => hgb (e X)) (lipschitzWith_comp_of_min_one_dist_le hgb hgl he)
  rw [Real.coe_toNNReal _ hM] at h
  rw [levyProkhorovEvalBound]
  exact h

/-! ### Replacing the laws in the atomic pairing -/

/-- **Replacement of the walk laws by the law field in the atomic pairing.** Let `c x ≥ 0`,
`|f| ≤ C_f`, `|ψ| ≤ C_ψ`, `|g| ≤ C_g` with `g` `K`-Lipschitz, and `min 1 d(e X, e Y) ≤ Λ d(X, Y)`. If
`Q x` and `P (p x)` are at Lévy–Prokhorov distance `< a` for every `x ∈ s` with `ψ (p x) ≠ 0`, then
`|Σ_x c x f(p x) ψ(p x) E_{Q x}[g(e X)] - Σ_x c x f(p x) ψ(p x) E_{P (p x)}[g(e X)]|
  ≤ C_f C_ψ B Σ_{x ∈ s, ψ(p x) ≠ 0} c x` with `B = levyProkhorovEvalBound K C_g Λ a`. -/
theorem abs_sum_mul_integral_sub_sum_mul_integral_le {Ω E ι : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] [PseudoMetricSpace E] (s : Finset ι)
    {c : ι → ℝ} (hc : ∀ x, 0 ≤ c x) (p : ι → ℂ) (Q : ι → ProbabilityMeasure Ω)
    (P : ℂ → ProbabilityMeasure Ω) {f ψ : ℂ → ℝ} {Cf Cψ : ℝ} (hfb : ∀ z, |f z| ≤ Cf)
    (hψb : ∀ z, |ψ z| ≤ Cψ) {g : E → ℝ} {Cg : ℝ} (hgb : ∀ z, |g z| ≤ Cg) {K : ℝ≥0}
    (hgl : LipschitzWith K g) {e : Ω → E} {Λ : ℝ≥0}
    (he : ∀ X Y, min 1 (dist (e X) (e Y)) ≤ Λ * dist X Y) {a : ℝ} (ha : 0 < a)
    (hQP : ∀ x ∈ s, ψ (p x) ≠ 0 →
      levyProkhorovEDist (Q x : Measure Ω) (P (p x) : Measure Ω) < ENNReal.ofReal a) :
    |∑ x ∈ s, c x * f (p x) * ψ (p x) * ∫ X, g (e X) ∂(Q x : Measure Ω)
        - ∑ x ∈ s, c x * f (p x) * ψ (p x) * ∫ X, g (e X) ∂(P (p x) : Measure Ω)|
      ≤ Cf * Cψ * levyProkhorovEvalBound K Cg Λ a * ∑ x ∈ s with ψ (p x) ≠ 0, c x := by
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hfb 0)
  have hCψ : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  by_cases hψ : ψ (p x) = 0
  · simp [hψ]
  · simp only [ne_eq, hψ, not_false_eq_true, ↓reduceIte]
    have hI := abs_integral_comp_sub_integral_comp_le_levyProkhorovEvalBound (Q x : Measure Ω)
      (P (p x) : Measure Ω) ha (hQP x hx hψ) hgb hgl he
    have e1 : c x * f (p x) * ψ (p x) * ∫ X, g (e X) ∂(Q x : Measure Ω)
        - c x * f (p x) * ψ (p x) * ∫ X, g (e X) ∂(P (p x) : Measure Ω)
        = c x * (f (p x) * (ψ (p x) * (∫ X, g (e X) ∂(Q x : Measure Ω)
          - ∫ X, g (e X) ∂(P (p x) : Measure Ω)))) := by ring
    rw [e1, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hc x)]
    calc c x * (|f (p x)| * (|ψ (p x)| * |∫ X, g (e X) ∂(Q x : Measure Ω)
          - ∫ X, g (e X) ∂(P (p x) : Measure Ω)|))
        ≤ c x * (Cf * (Cψ * levyProkhorovEvalBound K Cg Λ a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hfb _) (mul_le_mul (hψb _) hI (abs_nonneg _) hCψ)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCf) (hc x)
      _ = Cf * Cψ * levyProkhorovEvalBound K Cg Λ a * c x := by ring

/-! ### The atomic measure -/

/-- The atomic measure `Σ_{x ∈ s} c x δ_{p x}` on `ℂ`. -/
noncomputable def atomicMeasure {ι : Type*} (s : Finset ι) (c : ι → ℝ) (p : ι → ℂ) : Measure ℂ :=
  ∑ x ∈ s, ENNReal.ofReal (c x) • Measure.dirac (p x)

/-- For nonnegative weights, `∫ H d(Σ_{x ∈ s} c x δ_{p x}) = Σ_{x ∈ s} c x H(p x)`, for every
`H : ℂ → ℝ`. -/
theorem integral_atomicMeasure {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ x, 0 ≤ c x)
    (p : ι → ℂ) (H : ℂ → ℝ) :
    ∫ z, H z ∂(atomicMeasure s c p) = ∑ x ∈ s, c x * H (p x) := by
  have hint : ∀ x ∈ s, Integrable H (ENNReal.ofReal (c x) • Measure.dirac (p x)) := by
    intro x _
    have h1 : Integrable (fun _ : ℂ => H (p x)) (Measure.dirac (p x)) := integrable_const _
    exact (h1.congr (ae_eq_dirac H).symm).smul_measure ENNReal.ofReal_ne_top
  rw [atomicMeasure, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc x), smul_eq_mul]

/-- **The second pairing as an integral against the atomic measure.** With
`ν = Σ_{x ∈ s} c x δ_{p x}`, `∫ f(z) u(z) ψ(z) dν(z) = Σ_{x ∈ s} c x f(p x) ψ(p x) u(p x)`; with
`u z = E_{P z}[g(e X)]` this is the second sum of `abs_sum_mul_integral_sub_sum_mul_integral_le`. -/
theorem integral_atomicMeasure_mul {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ x, 0 ≤ c x)
    (p : ι → ℂ) (f u ψ : ℂ → ℝ) :
    ∫ z, f z * u z * ψ z ∂(atomicMeasure s c p) = ∑ x ∈ s, c x * f (p x) * ψ (p x) * u (p x) := by
  rw [integral_atomicMeasure s hc p]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The mass of the support of `ψ` under `Σ_{x ∈ s} c x δ_{p x}` is `Σ_{x ∈ s, ψ(p x) ≠ 0} c x`. -/
theorem atomicMeasure_real_support {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ x, 0 ≤ c x)
    (p : ι → ℂ) (ψ : ℂ → ℝ) :
    (atomicMeasure s c p).real (Function.support ψ) = ∑ x ∈ s with ψ (p x) ≠ 0, c x := by
  have hfin : ∀ x ∈ s,
      (ENNReal.ofReal (c x) • Measure.dirac (p x)) (Function.support ψ) ≠ ∞ := by
    intro x _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [measureReal_def, atomicMeasure, Measure.finsetSum_apply, ENNReal.toReal_sum hfin,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hψ : ψ (p x) = 0
  · simp [Measure.dirac_apply, hψ]
  · simp [hψ, ENNReal.toReal_ofReal (hc x)]

/-- **Replacement in the atomic form.** With `ν = Σ_{x ∈ s} c x δ_{p x}` and the hypotheses of
`abs_sum_mul_integral_sub_sum_mul_integral_le`,
`|Σ_x c x f(p x) ψ(p x) E_{Q x}[g(e X)] - ∫ f(z) E_{P z}[g(e X)] ψ(z) dν(z)| ≤ C_f C_ψ B ν(supp ψ)`
with `B = levyProkhorovEvalBound K C_g Λ a`. -/
theorem abs_sum_mul_integral_sub_integral_atomicMeasure_le {Ω E ι : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] [PseudoMetricSpace E] (s : Finset ι)
    {c : ι → ℝ} (hc : ∀ x, 0 ≤ c x) (p : ι → ℂ) (Q : ι → ProbabilityMeasure Ω)
    (P : ℂ → ProbabilityMeasure Ω) {f ψ : ℂ → ℝ} {Cf Cψ : ℝ} (hfb : ∀ z, |f z| ≤ Cf)
    (hψb : ∀ z, |ψ z| ≤ Cψ) {g : E → ℝ} {Cg : ℝ} (hgb : ∀ z, |g z| ≤ Cg) {K : ℝ≥0}
    (hgl : LipschitzWith K g) {e : Ω → E} {Λ : ℝ≥0}
    (he : ∀ X Y, min 1 (dist (e X) (e Y)) ≤ Λ * dist X Y) {a : ℝ} (ha : 0 < a)
    (hQP : ∀ x ∈ s, ψ (p x) ≠ 0 →
      levyProkhorovEDist (Q x : Measure Ω) (P (p x) : Measure Ω) < ENNReal.ofReal a) :
    |∑ x ∈ s, c x * f (p x) * ψ (p x) * ∫ X, g (e X) ∂(Q x : Measure Ω)
        - ∫ z, f z * (∫ X, g (e X) ∂(P z : Measure Ω)) * ψ z ∂(atomicMeasure s c p)|
      ≤ Cf * Cψ * levyProkhorovEvalBound K Cg Λ a
          * (atomicMeasure s c p).real (Function.support ψ) := by
  have h1 : ∫ z, f z * (∫ X, g (e X) ∂(P z : Measure Ω)) * ψ z ∂(atomicMeasure s c p)
      = ∑ x ∈ s, c x * f (p x) * ψ (p x) * ∫ X, g (e X) ∂(P (p x) : Measure Ω) :=
    integral_atomicMeasure_mul s hc p f (fun z => ∫ X, g (e X) ∂(P z : Measure Ω)) ψ
  rw [h1, atomicMeasure_real_support s hc p ψ]
  exact abs_sum_mul_integral_sub_sum_mul_integral_le s hc p Q P hfb hψb hgb hgl he ha hQP

end LatticeProb
