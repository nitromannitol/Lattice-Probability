/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RandomBracketLindeberg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.UnstoppedContinuousLindeberg
import LatticeProb.Bonanno.ReflectedGMS.Limit.CompensatedCylinderIdentity

/-!
# Uniform tails of the realized quadratic sum of a random-bracket martingale

`UnstoppedContinuousLindeberg` proves the Lindeberg condition for a martingale whose square is
compensated by the *deterministic* bracket `C u`.  This file is its random-bracket mirror for the
one estimate that survives the passage to a random bracket: **uniform tails of the realized
quadratic sum**

`Q_n = ∑_{i<n} (M t_{i+1} - M t_i)²`  (uniform partition of `[s, t]`),

for a square-integrable martingale `M` with `M * M - B` a martingale, `B` a.e. monotone on
`[s, t]` and `B t - B s ≤ K` a.e.  The cap sets `A_i = gridCapSet M g c i` of
`UnstoppedContinuousLindeberg` are reused verbatim; every `C (b - u) P(A)` of that file becomes
`∫_A (B b - B u)`, which is `≥ 0` by monotonicity and `≤ K P(A)`.

* `integral_mul_increment_sq_eq_bracket`, `setIntegral_increment_sq_eq_bracket`,
  `setIntegral_increment_sq_split_bracket` — the bracket identity tested against the past,
  obtained from `CompensatedCylinderIdentity.integral_mul_compensated_sq_increment_eq_zero`.
* `sum_setIntegral_exit_step_le_of_bracket`, `gridCap_exit_measure_sq_le_of_bracket` — the
  disjoint exit-step estimate and the sharp grid maximal inequality.
* `capped_quadratic_sq_integral_le_of_bracket` — the partition-uniform `L²` bound
  `E[(∑ᵢ Qᵢ^cap)²] ≤ 4c²K + 2K²` (cross terms by conditioning at the left end of the later
  increment, organised through `(∑ fᵢ)² = ∑ᵢ (2 (∑_{j<i} fⱼ) fᵢ + fᵢ fᵢ)`).
* `integral_max_realizedQuadraticSum_sub_le` — the one-partition tail bound
  `∫ (Q_n - λ)⁺ ≤ (4c²K + 2K²)/λ + 4 ∫ ((M t - M s)² - m)⁺ + (4m + K) K / c²`.
* `exists_uniform_realizedQuadraticSum_tail` — **the family statement**: bounded bracket
  increments plus uniform square tails of the TERMINAL increment `M t - M s` give uniform tails
  of `Q_n`, uniformly in `n` and eventually along the family.
* `lindebergSum_le_integral_max_add` — the reduction inequality
  `lindebergSum ≤ ∫ (Q_n - λ)⁺ + λ P(some increment exceeds δ)`, and
  `sq_mul_measureReal_bigIncrementSet_le_lindebergSum` — its converse direction for the
  increment event (`δ² P(big) ≤ lindebergSum`).

## ⚠ The terminal-tail premise is necessary: bounded brackets alone do NOT suffice

A bounded bracket gives no uniformity of the square tails across a family.  The compensated
Poisson martingales `N_k r = θ_k (Π_k r - r / θ_k²)` (jumps `θ_k → ∞`, rate `θ_k⁻²`) all have
the deterministic bracket `r`, yet for `n` large `Q_n ≈ θ_k² Π_k[s, t]`, so
`∫ (Q_n - λ)⁺ → (t - s)` as `k → ∞` for every fixed `λ`; the probability of a large increment
still tends to `0`.  So uniform quadratic tails are *not* a generic consequence of a bounded
(even deterministic) bracket, and the family theorem here carries the uniform tail of the
terminal square `(N_k t - N_k s)²` as its one non-structural premise.  That premise is also
necessary for the CLT this feeds (convergence in law plus convergence of second moments forces
it), and the project already has a producer shape for it:
`ActualArrayLocalizerBounds.uniform_tail_sq_increment_of_threshold_localizers` (jump bound +
bounded bracket).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

section RandomBracket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝔽 : Filtration ℝ≥0 mΩ} {M B : ℝ≥0 → Ω → ℝ}

/-! ### The bracket identity tested against the past -/

/-- **The random-bracket identity tested against a bounded past weight.**  For a
square-integrable martingale `M` with `M * M - B` a martingale, `a ≤ b` and a bounded
`𝔽 a`-measurable `G`: `∫ G (M b - M a)² = ∫ G (B b - B a)`. -/
theorem integral_mul_increment_sq_eq_bracket [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {a b : ℝ≥0} (hab : a ≤ b)
    {G : Ω → ℝ} (hG : StronglyMeasurable[𝔽 a] G) {D : ℝ} (hGb : ∀ ω, |G ω| ≤ D) :
    (∫ ω, G ω * (M b ω - M a ω) ^ 2 ∂P) = ∫ ω, G ω * (B b ω - B a ω) ∂P := by
  have hD2 : Integrable (fun ω => (M b ω - M a ω) ^ 2) P :=
    integrable_increment_sq_of_memLp h2 a b
  have hdB : Integrable (fun ω => B b ω - B a ω) P :=
    (integrable_bracket_of_square_martingale hC h2 b).sub
      (integrable_bracket_of_square_martingale hC h2 a)
  have hGm : AEStronglyMeasurable G P := (hG.mono (𝔽.le a)).aestronglyMeasurable
  have hGbd : ∀ᵐ ω ∂P, ‖G ω‖ ≤ D :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb ω
  have h1 : Integrable (fun ω => G ω * (M b ω - M a ω) ^ 2) P := hD2.bdd_mul hGm hGbd
  have h1' : Integrable (fun ω => G ω * (B b ω - B a ω)) P := hdB.bdd_mul hGm hGbd
  have hz := integral_mul_compensated_sq_increment_eq_zero hM hC h2 hab hG hGb
  have hsplit : (∫ ω, G ω * ((M b ω - M a ω) ^ 2 - (B b ω - B a ω)) ∂P)
      = (∫ ω, G ω * (M b ω - M a ω) ^ 2 ∂P) - ∫ ω, G ω * (B b ω - B a ω) ∂P := by
    rw [← integral_sub h1 h1']
    refine integral_congr_ae ?_
    filter_upwards with ω
    ring
  linarith

/-- The unweighted bracket identity `∫ (M b - M a)² = ∫ (B b - B a)`. -/
theorem integral_increment_sq_eq_bracket [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {a b : ℝ≥0} (hab : a ≤ b) :
    (∫ ω, (M b ω - M a ω) ^ 2 ∂P) = ∫ ω, (B b ω - B a ω) ∂P := by
  have h := integral_mul_increment_sq_eq_bracket hM hC h2 hab (G := fun _ => (1 : ℝ))
    stronglyMeasurable_const (D := 1) (fun _ => by simp)
  simpa only [one_mul] using h

/-- **The random-bracket identity on a past event.**  For `A ∈ 𝔽 a` and `a ≤ b`:
`∫_A (M b - M a)² = ∫_A (B b - B a)`. -/
theorem setIntegral_increment_sq_eq_bracket [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {a b : ℝ≥0} (hab : a ≤ b)
    {A : Set Ω} (hA : MeasurableSet[𝔽 a] A) :
    (∫ ω in A, (M b ω - M a ω) ^ 2 ∂P) = ∫ ω in A, (B b ω - B a ω) ∂P := by
  have hA' : MeasurableSet A := 𝔽.le a _ hA
  have hG : StronglyMeasurable[𝔽 a] (A.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hA
  have hGb : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω, abs_one, le_refl]
    · simp only [Set.indicator_of_notMem hω, abs_zero, zero_le_one]
  have key := integral_mul_increment_sq_eq_bracket hM hC h2 hab hG hGb
  have hconv : ∀ f : Ω → ℝ,
      (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * f ω ∂P) = ∫ ω in A, f ω ∂P := by
    intro f
    rw [← integral_indicator hA']
    refine integral_congr_ae ?_
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω, one_mul]
    · simp only [Set.indicator_of_notMem hω, zero_mul]
  rw [hconv (fun ω => (M b ω - M a ω) ^ 2), hconv (fun ω => B b ω - B a ω)] at key
  exact key

/-- **Set-integral orthogonality split with a random bracket.**  For `a ≤ u ≤ b` and
`A ∈ 𝔽 u`: `∫_A (M b - M a)² = ∫_A (B b - B u) + ∫_A (M u - M a)²`.  This is the random-bracket
copy of `UnstoppedContinuousLindeberg.setIntegral_increment_sq_split`. -/
theorem setIntegral_increment_sq_split_bracket [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {a u b : ℝ≥0} (hau : a ≤ u) (hub : u ≤ b)
    {A : Set Ω} (hA : MeasurableSet[𝔽 u] A) :
    (∫ ω in A, (M b ω - M a ω) ^ 2 ∂P)
      = (∫ ω in A, (B b ω - B u ω) ∂P) + ∫ ω in A, (M u ω - M a ω) ^ 2 ∂P := by
  have hA' : MeasurableSet A := 𝔽.le u _ hA
  have hI1 : Integrable (fun ω => (M u ω - M a ω) ^ 2) P :=
    integrable_increment_sq_of_memLp h2 a u
  have hI2 : Integrable (fun ω => (M b ω - M u ω) ^ 2) P :=
    integrable_increment_sq_of_memLp h2 u b
  have hI3 : Integrable (fun ω => 2 * ((M u ω - M a ω) * (M b ω - M u ω))) P :=
    (((h2 u).sub (h2 a)).integrable_mul ((h2 b).sub (h2 u))).const_mul 2
  have hI13 : Integrable
      (fun ω => (M u ω - M a ω) ^ 2 + 2 * ((M u ω - M a ω) * (M b ω - M u ω))) P :=
    hI1.add hI3
  have hcross : (∫ ω in A, (M u ω - M a ω) * (M b ω - M u ω) ∂P) = 0 := by
    have hZ : StronglyMeasurable[𝔽 u] (A.indicator fun ω => M u ω - M a ω) :=
      ((hM.stronglyMeasurable u).sub
        ((hM.stronglyMeasurable a).mono (𝔽.mono hau))).indicator hA
    have hZ2 : MemLp (A.indicator fun ω => M u ω - M a ω) 2 P :=
      ((h2 u).sub (h2 a)).indicator hA'
    have h0 := integral_mul_increment_eq_zero hM h2 hub hZ hZ2
    rw [← integral_indicator hA']
    refine (integral_congr_ae ?_).trans h0
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω, zero_mul]
  have hexp : (∫ ω in A, (M b ω - M a ω) ^ 2 ∂P)
      = ∫ ω in A, ((M u ω - M a ω) ^ 2 + 2 * ((M u ω - M a ω) * (M b ω - M u ω))
          + (M b ω - M u ω) ^ 2) ∂P :=
    setIntegral_congr_fun hA' (fun ω _ => by ring)
  rw [hexp, integral_add hI13.integrableOn hI2.integrableOn,
    integral_add hI1.integrableOn hI3.integrableOn, integral_const_mul, hcross,
    setIntegral_increment_sq_eq_bracket hM hC h2 hub hA]
  ring

/-! ### The disjoint exit-step estimate and the grid maximal inequality -/

/-- **Exit-step estimate with a random bracket.**  The random-bracket copy of
`UnstoppedContinuousLindeberg.sum_setIntegral_exit_step_le`: the dropped term
`∫_{exit step} (B (g n) - B (g (i+1)))` is nonnegative by monotonicity of the bracket along the
grid. -/
theorem sum_setIntegral_exit_step_le_of_bracket [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {g : ℕ → ℝ≥0} (hg : Monotone g) {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (hBg : ∀ᵐ ω ∂P, ∀ i j, i ≤ j → j ≤ n → B (g i) ω ≤ B (g j) ω) :
    (∑ i ∈ Finset.range n, ∫ ω in gridCapSet M g c i \ gridCapSet M g c (i + 1),
        (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P)
      ≤ ∫ ω in (gridCapSet M g c n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
  classical
  set A : ℕ → Set Ω := fun i => gridCapSet M g c i with hA
  have hAmeas : ∀ i, MeasurableSet (A i) := fun i =>
    𝔽.le (g i) _ (measurableSet_gridCapSet hM hg c i)
  have hXint : Integrable (fun ω => (M (g n) ω - M (g 0) ω) ^ 2) P :=
    integrable_increment_sq_of_memLp h2 (g 0) (g n)
  -- step 1: on each exit step the terminal increment dominates
  have hstep : ∀ i ∈ Finset.range n,
      (∫ ω in A i \ A (i + 1), (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P)
        ≤ ∫ ω in A i \ A (i + 1), (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    have hset : MeasurableSet[𝔽 (g (i + 1))] (A i \ A (i + 1)) :=
      MeasurableSet.diff
        (𝔽.mono (hg (Nat.le_succ i)) _ (measurableSet_gridCapSet hM hg c i))
        (measurableSet_gridCapSet hM hg c (i + 1))
    have hsplit := setIntegral_increment_sq_split_bracket hM hC h2
      (a := g 0) (u := g (i + 1)) (b := g n)
      (hg (Nat.zero_le (i + 1))) (hg hi') hset
    have hnn : 0 ≤ ∫ ω in A i \ A (i + 1), (B (g n) ω - B (g (i + 1)) ω) ∂P := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_of_ae hBg] with ω hω
      exact sub_nonneg.2 (hω (i + 1) n hi' le_rfl)
    linarith [hsplit]
  -- step 2: the indicators telescope
  have hind : ∀ i,
      (∫ ω in A i \ A (i + 1), (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
        = (∫ ω in A i, (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
          - ∫ ω in A (i + 1), (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
    intro i
    have hsub : A (i + 1) ⊆ A i := gridCapSet_subset M g c (Nat.le_succ i)
    have hOn : IntegrableOn (fun ω => (M (g n) ω - M (g 0) ω) ^ 2) (A i) P :=
      hXint.integrableOn
    have hsum := integral_inter_add_sdiff (μ := P) (hAmeas (i + 1)) hOn
    rw [Set.inter_eq_self_of_subset_right hsub] at hsum
    linarith
  have htele : (∑ i ∈ Finset.range n,
      (∫ ω in A i \ A (i + 1), (M (g n) ω - M (g 0) ω) ^ 2 ∂P))
      = (∫ ω in A 0, (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
        - ∫ ω in A n, (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
    rw [Finset.sum_congr rfl fun i _ => hind i]
    exact Finset.sum_range_sub'
      (fun i => ∫ ω in A i, (M (g n) ω - M (g 0) ω) ^ 2 ∂P) n
  have hA0 : A 0 = (Set.univ : Set Ω) := gridCapSet_zero M g hc
  have hcompl : (∫ ω in A n, (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
      + (∫ ω in (A n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
      = ∫ ω, (M (g n) ω - M (g 0) ω) ^ 2 ∂P :=
    integral_add_compl (hAmeas n) hXint
  calc (∑ i ∈ Finset.range n, ∫ ω in A i \ A (i + 1),
        (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P)
      ≤ ∑ i ∈ Finset.range n, ∫ ω in A i \ A (i + 1),
          (M (g n) ω - M (g 0) ω) ^ 2 ∂P := Finset.sum_le_sum hstep
    _ = (∫ ω in A 0, (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
          - ∫ ω in A n, (M (g n) ω - M (g 0) ω) ^ 2 ∂P := htele
    _ = ∫ ω in (A n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
        rw [hA0, setIntegral_univ]
        linarith

/-- **Sharp grid maximal inequality with a random bracket**:
`c² P(A_nᶜ) ≤ ∫_{A_nᶜ} (M (g n) - M (g 0))²`.  Random-bracket copy of
`UnstoppedContinuousLindeberg.gridCap_exit_measure_sq_le`. -/
theorem gridCap_exit_measure_sq_le_of_bracket [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {g : ℕ → ℝ≥0} (hg : Monotone g) {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (hBg : ∀ᵐ ω ∂P, ∀ i j, i ≤ j → j ≤ n → B (g i) ω ≤ B (g j) ω) :
    c ^ 2 * P.real ((gridCapSet M g c n)ᶜ)
      ≤ ∫ ω in (gridCapSet M g c n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
  classical
  set A : ℕ → Set Ω := fun i => gridCapSet M g c i with hA
  have hAmeas : ∀ i, MeasurableSet (A i) := fun i =>
    𝔽.le (g i) _ (measurableSet_gridCapSet hM hg c i)
  have hconst : Integrable (fun _ : Ω => c ^ 2) P := integrable_const _
  have hmeasure : (∑ i ∈ Finset.range n, c ^ 2 * P.real (A i \ A (i + 1)))
      = c ^ 2 * P.real ((A n)ᶜ) := by
    have hcc : ∀ S : Set Ω, (∫ _ω in S, c ^ 2 ∂P) = c ^ 2 * P.real S := by
      intro S
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hind : ∀ i, (∫ _ω in A i \ A (i + 1), c ^ 2 ∂P)
        = (∫ _ω in A i, c ^ 2 ∂P) - ∫ _ω in A (i + 1), c ^ 2 ∂P := by
      intro i
      have hsub : A (i + 1) ⊆ A i := gridCapSet_subset M g c (Nat.le_succ i)
      have hOn : IntegrableOn (fun _ : Ω => c ^ 2) (A i) P := hconst.integrableOn
      have hsum := integral_inter_add_sdiff (μ := P) (hAmeas (i + 1)) hOn
      rw [Set.inter_eq_self_of_subset_right hsub] at hsum
      linarith
    have htele : (∑ i ∈ Finset.range n, (∫ _ω in A i \ A (i + 1), c ^ 2 ∂P))
        = (∫ _ω in A 0, c ^ 2 ∂P) - ∫ _ω in A n, c ^ 2 ∂P := by
      rw [Finset.sum_congr rfl fun i _ => hind i]
      exact Finset.sum_range_sub' (fun i => ∫ _ω in A i, c ^ 2 ∂P) n
    have hcompl : (∫ _ω in A n, c ^ 2 ∂P) + (∫ _ω in (A n)ᶜ, c ^ 2 ∂P)
        = ∫ _ω : Ω, c ^ 2 ∂P := integral_add_compl (hAmeas n) hconst
    have hA0 : A 0 = (Set.univ : Set Ω) := gridCapSet_zero M g hc
    have hfinal : (∑ i ∈ Finset.range n, (∫ _ω in A i \ A (i + 1), c ^ 2 ∂P))
        = ∫ _ω in (A n)ᶜ, c ^ 2 ∂P := by
      rw [htele, hA0, setIntegral_univ]
      linarith
    calc (∑ i ∈ Finset.range n, c ^ 2 * P.real (A i \ A (i + 1)))
        = ∑ i ∈ Finset.range n, (∫ _ω in A i \ A (i + 1), c ^ 2 ∂P) :=
          Finset.sum_congr rfl fun i _ => (hcc _).symm
      _ = ∫ _ω in (A n)ᶜ, c ^ 2 ∂P := hfinal
      _ = c ^ 2 * P.real ((A n)ᶜ) := hcc _
  have hterm : ∀ i ∈ Finset.range n,
      c ^ 2 * P.real (A i \ A (i + 1))
        ≤ ∫ ω in A i \ A (i + 1), (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P := by
    intro i _
    have hmeasSet : MeasurableSet (A i \ A (i + 1)) := (hAmeas i).diff (hAmeas (i + 1))
    have hpt : ∀ ω ∈ A i \ A (i + 1),
        c ^ 2 ≤ (M (g (i + 1)) ω - M (g 0) ω) ^ 2 := by
      intro ω hω
      exact (sq_le_of_mem_exit_step hω).1
    have hle : (∫ _ω in A i \ A (i + 1), c ^ 2 ∂P)
        ≤ ∫ ω in A i \ A (i + 1), (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P := by
      refine setIntegral_mono_on (integrable_const _).integrableOn ?_ hmeasSet hpt
      exact (integrable_increment_sq_of_memLp h2 (g 0) (g (i + 1))).integrableOn
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at hle
  calc c ^ 2 * P.real ((A n)ᶜ)
      = ∑ i ∈ Finset.range n, c ^ 2 * P.real (A i \ A (i + 1)) := hmeasure.symm
    _ ≤ ∑ i ∈ Finset.range n, ∫ ω in A i \ A (i + 1),
          (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P := Finset.sum_le_sum hterm
    _ ≤ ∫ ω in (A n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P :=
        sum_setIntegral_exit_step_le_of_bracket hM hC h2 hg hc hBg

/-! ### The partition-uniform `L²` bound for the capped quadratic sum -/

/-- The square of a sum, telescoped along its partial sums with every earlier term on the left:
`(∑_{i<n} fᵢ)² = ∑_{i<n} (2 ((∑_{j<i} fⱼ) fᵢ) + fᵢ fᵢ)`. -/
theorem sq_sum_range_eq_sum_partial_mul (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) ^ 2
      = ∑ i ∈ Finset.range n, (2 * ((∑ j ∈ Finset.range i, f j) * f i) + f i * f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    ring

/-- **Partition-uniform `L²` bound for the capped realized quadratic sum, random bracket.**
With `Qᵢ = cappedIncrementSq M g c i ≤ 4c²` and `Sᵢ = ∑_{j<i} Qⱼ` (measurable at `g i`):
`E[S_n²] = ∑ᵢ (2 E[Sᵢ Qᵢ] + E[Qᵢ²])`, `E[Sᵢ Qᵢ] ≤ E[Sᵢ ΔBᵢ]` by conditioning at `g i`,
`E[Qᵢ²] ≤ 4c² E[ΔBᵢ]`, and `∑ᵢ (2Sᵢ + 4c²) ΔBᵢ ≤ (2 S_n + 4c²) K` pointwise. -/
theorem capped_quadratic_sq_integral_le_of_bracket [IsProbabilityMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {g : ℕ → ℝ≥0} (hg : Monotone g) {c : ℝ} (hc : 0 ≤ c)
    {K : ℝ} (hK : 0 ≤ K) {n : ℕ}
    (hBg : ∀ᵐ ω ∂P, ∀ i j, i ≤ j → j ≤ n → B (g i) ω ≤ B (g j) ω)
    (hBK : ∀ᵐ ω ∂P, B (g n) ω - B (g 0) ω ≤ K) :
    Integrable (fun ω => (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 ∂P)
        ≤ 4 * c ^ 2 * K + 2 * K ^ 2 := by
  classical
  have hQ0 : ∀ i ω, 0 ≤ cappedIncrementSq M g c i ω := fun i ω =>
    cappedIncrementSq_nonneg M g c i ω
  have hQb : ∀ i ω, cappedIncrementSq M g c i ω ≤ 4 * c ^ 2 := fun i ω =>
    cappedIncrementSq_le_bound hc M g i ω
  have hQint : ∀ i, Integrable (cappedIncrementSq M g c i) P := fun i =>
    integrable_cappedIncrementSq hM hg hc i
  have hS0 : ∀ i ω, 0 ≤ ∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω :=
    fun i ω => Finset.sum_nonneg fun j _ => hQ0 j ω
  have hSb : ∀ i ω, |∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω| ≤ 4 * c ^ 2 * i := by
    intro i ω
    rw [abs_of_nonneg (hS0 i ω)]
    calc (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
        ≤ ∑ _j ∈ Finset.range i, 4 * c ^ 2 := Finset.sum_le_sum fun j _ => hQb j ω
      _ = 4 * c ^ 2 * i := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hSbn : ∀ i, ∀ᵐ ω ∂P, ‖∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω‖
      ≤ 4 * c ^ 2 * i := fun i =>
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hSb i ω
  have hSsm : ∀ i, StronglyMeasurable[𝔽 (g i)]
      (fun ω => ∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω) := by
    intro i
    refine Finset.stronglyMeasurable_fun_sum (Finset.range i) (fun j hj => ?_)
    exact (stronglyMeasurable_cappedIncrementSq hM hg c j).mono
      (𝔽.mono (hg (Nat.succ_le_of_lt (Finset.mem_range.1 hj))))
  have hSm : ∀ i, AEStronglyMeasurable
      (fun ω => ∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω) P := fun i =>
    ((hSsm i).mono (𝔽.le (g i))).aestronglyMeasurable
  have hΔint : ∀ i, Integrable (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) P :=
    fun i => integrable_increment_sq_of_memLp h2 (g i) (g (i + 1))
  have hBint : ∀ r, Integrable (B r) P := fun r =>
    integrable_bracket_of_square_martingale hC h2 r
  have hΔBint : ∀ i, Integrable (fun ω => B (g (i + 1)) ω - B (g i) ω) P := fun i =>
    (hBint _).sub (hBint _)
  have hSQint : ∀ i, Integrable (fun ω => (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
      * cappedIncrementSq M g c i ω) P := fun i =>
    (hQint i).bdd_mul (hSm i) (hSbn i)
  have hSΔint : ∀ i, Integrable (fun ω => (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
      * (M (g (i + 1)) ω - M (g i) ω) ^ 2) P := fun i =>
    (hΔint i).bdd_mul (hSm i) (hSbn i)
  have hSΔBint : ∀ i, Integrable (fun ω => (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
      * (B (g (i + 1)) ω - B (g i) ω)) P := fun i =>
    (hΔBint i).bdd_mul (hSm i) (hSbn i)
  -- the bracket identity for one increment
  have hvar : ∀ i, (∫ ω, (M (g (i + 1)) ω - M (g i) ω) ^ 2 ∂P)
      = ∫ ω, (B (g (i + 1)) ω - B (g i) ω) ∂P := fun i =>
    integral_increment_sq_eq_bracket hM hC h2 (hg (Nat.le_succ i))
  -- cross terms: condition at the left end of the later increment
  have hcross : ∀ i, (∫ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
        * cappedIncrementSq M g c i ω ∂P)
      ≤ ∫ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
          * (B (g (i + 1)) ω - B (g i) ω) ∂P := by
    intro i
    have hle : (∫ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
          * cappedIncrementSq M g c i ω ∂P)
        ≤ ∫ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (M (g (i + 1)) ω - M (g i) ω) ^ 2 ∂P :=
      integral_mono (hSQint i) (hSΔint i) fun ω =>
        mul_le_mul_of_nonneg_left (cappedIncrementSq_le_sq M g c i ω) (hS0 i ω)
    rwa [integral_mul_increment_sq_eq_bracket hM hC h2 (hg (Nat.le_succ i)) (hSsm i)
      (hSb i)] at hle
  -- diagonal terms: the cap
  have hdiag : ∀ i, (∫ ω, cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω ∂P)
      ≤ 4 * c ^ 2 * ∫ ω, (B (g (i + 1)) ω - B (g i) ω) ∂P := by
    intro i
    have h1 : (∫ ω, cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω ∂P)
        ≤ ∫ ω, 4 * c ^ 2 * cappedIncrementSq M g c i ω ∂P :=
      integral_mono (integrable_cappedIncrementSq_mul hM hg hc i i) ((hQint i).const_mul _)
        fun ω => mul_le_mul_of_nonneg_right (hQb i ω) (hQ0 i ω)
    have h1' : (∫ ω, cappedIncrementSq M g c i ω ∂P)
        ≤ ∫ ω, (M (g (i + 1)) ω - M (g i) ω) ^ 2 ∂P :=
      integral_mono (hQint i) (hΔint i) fun ω => cappedIncrementSq_le_sq M g c i ω
    rw [integral_const_mul] at h1
    rw [hvar i] at h1'
    calc (∫ ω, cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω ∂P)
        ≤ 4 * c ^ 2 * ∫ ω, cappedIncrementSq M g c i ω ∂P := h1
      _ ≤ 4 * c ^ 2 * ∫ ω, (B (g (i + 1)) ω - B (g i) ω) ∂P :=
          mul_le_mul_of_nonneg_left h1' (by positivity)
  -- the pointwise expansion
  have hexpand : ∀ ω, (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2
      = ∑ i ∈ Finset.range n,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * cappedIncrementSq M g c i ω)
          + cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω) :=
    fun ω => sq_sum_range_eq_sum_partial_mul (fun i => cappedIncrementSq M g c i ω) n
  have htermint : ∀ i, Integrable (fun ω =>
      2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω) * cappedIncrementSq M g c i ω)
        + cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω) P := fun i =>
    ((hSQint i).const_mul 2).add (integrable_cappedIncrementSq_mul hM hg hc i i)
  have hsumint : Integrable (fun ω => ∑ i ∈ Finset.range n,
      (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
        * cappedIncrementSq M g c i ω)
      + cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω)) P :=
    integrable_finsetSum _ fun i _ => htermint i
  have hint : Integrable (fun ω => (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2) P :=
    hsumint.congr (Eventually.of_forall fun ω => (hexpand ω).symm)
  refine ⟨hint, ?_⟩
  -- step 1: expand and split the integral
  have hstep1 : (∫ ω, (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 ∂P)
      = ∑ i ∈ Finset.range n,
          (2 * (∫ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
              * cappedIncrementSq M g c i ω ∂P)
            + ∫ ω, cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω ∂P) := by
    have e1 : (∫ ω, (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 ∂P)
        = ∫ ω, ∑ i ∈ Finset.range n,
            (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
              * cappedIncrementSq M g c i ω)
            + cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω) ∂P :=
      integral_congr_ae (Eventually.of_forall hexpand)
    rw [e1, integral_finsetSum _ fun i _ => htermint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_add ((hSQint i).const_mul 2) (integrable_cappedIncrementSq_mul hM hg hc i i),
      integral_const_mul]
  -- step 2: condition the cross terms, cap the diagonal
  have hWint : ∀ i, Integrable (fun ω =>
      2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
        * (B (g (i + 1)) ω - B (g i) ω))
      + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)) P := fun i =>
    ((hSΔBint i).const_mul 2).add ((hΔBint i).const_mul _)
  have hstep2 : (∑ i ∈ Finset.range n,
          (2 * (∫ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
              * cappedIncrementSq M g c i ω ∂P)
            + ∫ ω, cappedIncrementSq M g c i ω * cappedIncrementSq M g c i ω ∂P))
      ≤ ∑ i ∈ Finset.range n, ∫ ω,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (B (g (i + 1)) ω - B (g i) ω))
          + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)) ∂P := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_add ((hSΔBint i).const_mul 2) ((hΔBint i).const_mul _), integral_const_mul,
      integral_const_mul]
    have h1 := hcross i
    have h2' := hdiag i
    linarith
  have hstep3 : (∑ i ∈ Finset.range n, ∫ ω,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (B (g (i + 1)) ω - B (g i) ω))
          + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)) ∂P)
      = ∫ ω, ∑ i ∈ Finset.range n,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (B (g (i + 1)) ω - B (g i) ω))
          + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)) ∂P :=
    (integral_finsetSum _ fun i _ => hWint i).symm
  -- step 3: the pointwise bracket bound
  have hΔB0 : ∀ᵐ ω ∂P, ∀ i, i < n → 0 ≤ B (g (i + 1)) ω - B (g i) ω := by
    filter_upwards [hBg] with ω hω i hi
    exact sub_nonneg.2 (hω i (i + 1) (Nat.le_succ i) hi)
  have htele : ∀ ω, ∑ i ∈ Finset.range n, (B (g (i + 1)) ω - B (g i) ω)
      = B (g n) ω - B (g 0) ω := fun ω => Finset.sum_range_sub (fun i => B (g i) ω) n
  have hSle : ∀ i, i ≤ n → ∀ ω, (∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
      ≤ ∑ j ∈ Finset.range n, cappedIncrementSq M g c j ω := fun i hi ω =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hi)
      (fun j _ _ => hQ0 j ω)
  have hpt : ∀ᵐ ω ∂P, (∑ i ∈ Finset.range n,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (B (g (i + 1)) ω - B (g i) ω))
          + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)))
      ≤ 2 * K * (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) + 4 * c ^ 2 * K := by
    filter_upwards [hΔB0, hBK] with ω h0 hK'
    have hSn0 : 0 ≤ ∑ j ∈ Finset.range n, cappedIncrementSq M g c j ω := hS0 n ω
    calc (∑ i ∈ Finset.range n,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (B (g (i + 1)) ω - B (g i) ω))
          + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)))
        ≤ ∑ i ∈ Finset.range n,
            (2 * (∑ j ∈ Finset.range n, cappedIncrementSq M g c j ω) + 4 * c ^ 2)
              * (B (g (i + 1)) ω - B (g i) ω) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i < n := Finset.mem_range.1 hi
          have hd := h0 i hi'
          have hs := mul_le_mul_of_nonneg_right (hSle i hi'.le ω) hd
          nlinarith
      _ = (2 * (∑ j ∈ Finset.range n, cappedIncrementSq M g c j ω) + 4 * c ^ 2)
            * (B (g n) ω - B (g 0) ω) := by
          rw [← Finset.mul_sum, htele ω]
      _ ≤ (2 * (∑ j ∈ Finset.range n, cappedIncrementSq M g c j ω) + 4 * c ^ 2) * K :=
          mul_le_mul_of_nonneg_left hK' (by linarith [hSn0, sq_nonneg c])
      _ = 2 * K * (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) + 4 * c ^ 2 * K := by
          ring
  -- step 4: the mean of the capped sum is at most `K`
  have hSnint : Integrable (fun ω => ∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) P :=
    integrable_finsetSum _ fun i _ => hQint i
  have hBnint : Integrable (fun ω => B (g n) ω - B (g 0) ω) P := (hBint _).sub (hBint _)
  have hmeanS : (∫ ω, ∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω ∂P) ≤ K := by
    rw [integral_finsetSum _ fun i _ => hQint i]
    calc ∑ i ∈ Finset.range n, ∫ ω, cappedIncrementSq M g c i ω ∂P
        ≤ ∑ i ∈ Finset.range n, ∫ ω, (B (g (i + 1)) ω - B (g i) ω) ∂P := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← hvar i]
          exact integral_mono (hQint i) (hΔint i) fun ω => cappedIncrementSq_le_sq M g c i ω
      _ = ∫ ω, (B (g n) ω - B (g 0) ω) ∂P := by
          rw [← integral_finsetSum _ fun i _ => hΔBint i]
          exact integral_congr_ae (Eventually.of_forall htele)
      _ ≤ ∫ _ω, K ∂P := integral_mono_ae hBnint (integrable_const K) hBK
      _ = K := by rw [integral_const, probReal_univ, one_smul]
  have hfinal : (∫ ω, ∑ i ∈ Finset.range n,
          (2 * ((∑ j ∈ Finset.range i, cappedIncrementSq M g c j ω)
            * (B (g (i + 1)) ω - B (g i) ω))
          + 4 * c ^ 2 * (B (g (i + 1)) ω - B (g i) ω)) ∂P)
      ≤ ∫ ω, (2 * K * (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) + 4 * c ^ 2 * K) ∂P :=
    integral_mono_ae (integrable_finsetSum _ fun i _ => hWint i)
      ((hSnint.const_mul _).add (integrable_const _)) hpt
  rw [integral_add (hSnint.const_mul _) (integrable_const _), integral_const_mul, integral_const,
    probReal_univ, one_smul] at hfinal
  have hK2 : 2 * K * (∫ ω, ∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω ∂P) ≤ 2 * K * K :=
    mul_le_mul_of_nonneg_left hmeanS (by linarith)
  rw [hstep1]
  linarith [hstep2, hstep3, hfinal, hK2]

/-! ### The one-partition tail estimate -/

/-- Elementary: `(q - λ)⁺ ≤ s²/λ + a + b` whenever `q ≤ s + a + b` with `s, a, b ≥ 0`, `λ > 0`. -/
theorem max_sub_le_sq_div_add {q s a b lam : ℝ} (hq : q ≤ s + a + b) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 < lam) :
    max (q - lam) 0 ≤ s ^ 2 / lam + a + b := by
  have h1 : s - lam ≤ s ^ 2 / lam := by
    rw [le_div_iff₀ hlam]
    nlinarith [sq_nonneg (s - lam), mul_nonneg hs hlam.le]
  have h2 : 0 ≤ s ^ 2 / lam := div_nonneg (sq_nonneg _) hlam.le
  refine max_le ?_ ?_ <;> linarith

/-- **One-partition quadratic tail estimate along a grid, random bracket.**  The capped part
is handled by the `L²` bound and `(x - λ)⁺ ≤ x²/λ`, the exit steps by the exit-step estimate,
and the already-exited part by the set-integral bracket identity. -/
theorem integral_max_grid_quadratic_sub_le [IsProbabilityMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {g : ℕ → ℝ≥0} (hg : Monotone g) {c : ℝ} (hc : 0 ≤ c)
    {K : ℝ} (hK : 0 ≤ K) {n : ℕ}
    (hBg : ∀ᵐ ω ∂P, ∀ i j, i ≤ j → j ≤ n → B (g i) ω ≤ B (g j) ω)
    (hBK : ∀ᵐ ω ∂P, B (g n) ω - B (g 0) ω ≤ K) {lam : ℝ} (hlam : 0 < lam) :
    (∫ ω, max ((∑ i ∈ Finset.range n, (M (g (i + 1)) ω - M (g i) ω) ^ 2) - lam) 0 ∂P)
      ≤ (4 * c ^ 2 * K + 2 * K ^ 2) / lam
        + 4 * (∫ ω in (gridCapSet M g c n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P)
        + K * P.real ((gridCapSet M g c n)ᶜ) := by
  classical
  have hAmeas : ∀ i, MeasurableSet (gridCapSet M g c i) := fun i =>
    𝔽.le (g i) _ (measurableSet_gridCapSet hM hg c i)
  have hΔint : ∀ i, Integrable (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) P :=
    fun i => integrable_increment_sq_of_memLp h2 (g i) (g (i + 1))
  have hBint : ∀ r, Integrable (B r) P := fun r =>
    integrable_bracket_of_square_martingale hC h2 r
  have hΔBint : ∀ i, Integrable (fun ω => B (g (i + 1)) ω - B (g i) ω) P := fun i =>
    (hBint _).sub (hBint _)
  have hSq := capped_quadratic_sq_integral_le_of_bracket hM hC h2 hg hc hK hBg hBK
  have hT2int : Integrable (fun ω => ∑ i ∈ Finset.range n,
      Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
        (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω) P :=
    integrable_finsetSum _ fun i _ => (hΔint i).indicator ((hAmeas i).diff (hAmeas (i + 1)))
  have hT3int : Integrable (fun ω => ∑ i ∈ Finset.range n,
      Set.indicator (gridCapSet M g c i)ᶜ
        (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω) P :=
    integrable_finsetSum _ fun i _ => (hΔint i).indicator (hAmeas i).compl
  -- the pointwise three-way split
  have hpt : ∀ ω, max ((∑ i ∈ Finset.range n, (M (g (i + 1)) ω - M (g i) ω) ^ 2) - lam) 0
      ≤ (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 / lam
        + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω)
        + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i)ᶜ
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω) := by
    intro ω
    have hsplit : ∀ i, (M (g (i + 1)) ω - M (g i) ω) ^ 2
        ≤ cappedIncrementSq M g c i ω
          + Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
              (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω
          + Set.indicator (gridCapSet M g c i)ᶜ
              (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω := by
      intro i
      have hn1 : 0 ≤ Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
          (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
      have hn2 : 0 ≤ Set.indicator (gridCapSet M g c i)ᶜ
          (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
      have hn0 := cappedIncrementSq_nonneg M g c i ω
      by_cases h1 : ω ∈ gridCapSet M g c (i + 1)
      · have hc' : cappedIncrementSq M g c i ω = (M (g (i + 1)) ω - M (g i) ω) ^ 2 := by
          rw [cappedIncrementSq, Set.indicator_of_mem h1]
        linarith
      · by_cases h0 : ω ∈ gridCapSet M g c i
        · have hmem : ω ∈ gridCapSet M g c i \ gridCapSet M g c (i + 1) := ⟨h0, h1⟩
          rw [Set.indicator_of_mem hmem]
          linarith
        · have hmem : ω ∈ (gridCapSet M g c i)ᶜ := h0
          rw [Set.indicator_of_mem hmem]
          linarith
    have hQsum : (∑ i ∈ Finset.range n, (M (g (i + 1)) ω - M (g i) ω) ^ 2)
        ≤ (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω)
          + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
              (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω)
          + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i)ᶜ
              (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hsplit i
    exact max_sub_le_sq_div_add hQsum
      (Finset.sum_nonneg fun i _ => cappedIncrementSq_nonneg M g c i ω)
      (Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
      (Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω) hlam
  -- integrate
  have hQint' : Integrable (fun ω => ∑ i ∈ Finset.range n, (M (g (i + 1)) ω - M (g i) ω) ^ 2) P :=
    integrable_finsetSum _ fun i _ => hΔint i
  have hmaxint : Integrable (fun ω =>
      max ((∑ i ∈ Finset.range n, (M (g (i + 1)) ω - M (g i) ω) ^ 2) - lam) 0) P :=
    (hQint'.sub (integrable_const lam)).pos_part
  have hS2div : Integrable (fun ω =>
      (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 / lam) P :=
    hSq.1.div_const lam
  have hS2T2 : Integrable (fun ω =>
      (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 / lam
        + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω)) P := hS2div.add hT2int
  have hmono : (∫ ω, max ((∑ i ∈ Finset.range n, (M (g (i + 1)) ω - M (g i) ω) ^ 2) - lam) 0 ∂P)
      ≤ ∫ ω, ((∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 / lam
        + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω)
        + (∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i)ᶜ
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω)) ∂P :=
    integral_mono hmaxint (hS2T2.add hT3int) hpt
  rw [integral_add hS2T2 hT3int, integral_add hS2div hT2int, integral_div] at hmono
  -- the capped part
  have hcap : (∫ ω, (∑ i ∈ Finset.range n, cappedIncrementSq M g c i ω) ^ 2 ∂P) / lam
      ≤ (4 * c ^ 2 * K + 2 * K ^ 2) / lam := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hSq.2 (inv_nonneg.2 hlam.le)
  -- the exit steps
  have hT2 : (∫ ω, ∑ i ∈ Finset.range n,
        Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
          (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω ∂P)
      ≤ 4 * ∫ ω in (gridCapSet M g c n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P := by
    rw [integral_finsetSum _ fun i _ =>
      (hΔint i).indicator ((hAmeas i).diff (hAmeas (i + 1)))]
    have hterm : ∀ i ∈ Finset.range n,
        (∫ ω, Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω ∂P)
          ≤ 4 * ∫ ω in gridCapSet M g c i \ gridCapSet M g c (i + 1),
              (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P := by
      intro i _
      rw [integral_indicator ((hAmeas i).diff (hAmeas (i + 1))), ← integral_const_mul]
      refine setIntegral_mono_on (hΔint i).integrableOn
        ((integrable_increment_sq_of_memLp h2 (g 0) (g (i + 1))).const_mul 4).integrableOn
        ((hAmeas i).diff (hAmeas (i + 1))) ?_
      intro ω hω
      exact (sq_le_of_mem_exit_step hω).2
    calc (∑ i ∈ Finset.range n, ∫ ω,
          Set.indicator (gridCapSet M g c i \ gridCapSet M g c (i + 1))
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω ∂P)
        ≤ ∑ i ∈ Finset.range n, 4 * ∫ ω in gridCapSet M g c i \ gridCapSet M g c (i + 1),
            (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P := Finset.sum_le_sum hterm
      _ = 4 * ∑ i ∈ Finset.range n, ∫ ω in gridCapSet M g c i \ gridCapSet M g c (i + 1),
            (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∂P := by rw [Finset.mul_sum]
      _ ≤ 4 * ∫ ω in (gridCapSet M g c n)ᶜ, (M (g n) ω - M (g 0) ω) ^ 2 ∂P :=
          mul_le_mul_of_nonneg_left
            (sum_setIntegral_exit_step_le_of_bracket hM hC h2 hg hc hBg) (by norm_num)
  -- the already-exited part
  have hT3 : (∫ ω, ∑ i ∈ Finset.range n, Set.indicator (gridCapSet M g c i)ᶜ
          (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω ∂P)
      ≤ K * P.real ((gridCapSet M g c n)ᶜ) := by
    rw [integral_finsetSum _ fun i _ => (hΔint i).indicator (hAmeas i).compl]
    have hres : ∀ i, Integrable (fun ω => B (g (i + 1)) ω - B (g i) ω)
        (P.restrict (gridCapSet M g c n)ᶜ) := fun i => (hΔBint i).restrict
    have hterm : ∀ i ∈ Finset.range n,
        (∫ ω, Set.indicator (gridCapSet M g c i)ᶜ
            (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω ∂P)
          ≤ ∫ ω in (gridCapSet M g c n)ᶜ, (B (g (i + 1)) ω - B (g i) ω) ∂P := by
      intro i hi
      have hi' : i < n := Finset.mem_range.1 hi
      rw [integral_indicator (hAmeas i).compl,
        setIntegral_increment_sq_eq_bracket hM hC h2 (hg (Nat.le_succ i))
          (measurableSet_gridCapSet hM hg c i).compl]
      refine setIntegral_mono_set (hres i) ?_ ?_
      · filter_upwards [ae_restrict_of_ae hBg] with ω hω
        exact sub_nonneg.2 (hω i (i + 1) (Nat.le_succ i) hi')
      · exact LE.le.eventuallySubset
          (Set.compl_subset_compl.2 (gridCapSet_subset M g c hi'.le))
    calc (∑ i ∈ Finset.range n, ∫ ω, Set.indicator (gridCapSet M g c i)ᶜ
          (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2) ω ∂P)
        ≤ ∑ i ∈ Finset.range n,
            ∫ ω in (gridCapSet M g c n)ᶜ, (B (g (i + 1)) ω - B (g i) ω) ∂P :=
          Finset.sum_le_sum hterm
      _ = ∫ ω in (gridCapSet M g c n)ᶜ, (B (g n) ω - B (g 0) ω) ∂P := by
          rw [← integral_finsetSum _ fun i _ => hres i]
          exact integral_congr_ae
            (Eventually.of_forall fun ω => Finset.sum_range_sub (fun i => B (g i) ω) n)
      _ ≤ ∫ _ω in (gridCapSet M g c n)ᶜ, K ∂P := by
          have hBn : Integrable (fun ω => B (g n) ω - B (g 0) ω) P := (hBint _).sub (hBint _)
          exact integral_mono_ae hBn.restrict (integrable_const K) (ae_restrict_of_ae hBK)
      _ = K * P.real ((gridCapSet M g c n)ᶜ) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  linarith

/-! ### The realized quadratic sum along the uniform partition -/

/-- The realized quadratic sum of `N` along the uniform partition of `[s, t]` into `n`
pieces. -/
noncomputable def realizedQuadraticSum (N : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    (N (uniformPartition s t n (i + 1)) ω - N (uniformPartition s t n i) ω) ^ 2

/-- The event that some increment of `N` along the uniform partition of `[s, t]` into `n`
pieces exceeds `δ` in absolute value. -/
def bigIncrementSet (N : ℝ≥0 → Ω → ℝ) (δ : ℝ) (s t : ℝ≥0) (n : ℕ) : Set Ω :=
  ⋃ i ∈ Finset.range n,
    {ω | δ < |N (uniformPartition s t n (i + 1)) ω - N (uniformPartition s t n i) ω|}

theorem measurableSet_bigIncrementSet {N : ℝ≥0 → Ω → ℝ} (hNm : ∀ v, Measurable (N v))
    (δ : ℝ) (s t : ℝ≥0) (n : ℕ) : MeasurableSet (bigIncrementSet N δ s t n) :=
  Finset.measurableSet_biUnion _ fun i _ =>
    measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((hNm _).sub (hNm _)))

/-- Splitting a set integral of a function at a level `m` into a tail and a bulk part. -/
theorem setIntegral_le_integral_max_sub_add [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Integrable f P) {E : Set Ω} (hE : MeasurableSet E) (m : ℝ) :
    (∫ ω in E, f ω ∂P) ≤ (∫ ω, max (f ω - m) 0 ∂P) + m * P.real E := by
  have hpt : ∀ ω, E.indicator f ω
      ≤ max (f ω - m) 0 + m * E.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simp only [Set.indicator_of_mem hω, mul_one]
      have := le_max_left (f ω - m) 0
      linarith
    · simp only [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact le_max_right _ _
  have hmax : Integrable (fun ω => max (f ω - m) 0) P :=
    (hf.sub (integrable_const m)).pos_part
  have hind : Integrable (E.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hE
  have hle : (∫ ω, E.indicator f ω ∂P)
      ≤ ∫ ω, (max (f ω - m) 0 + m * E.indicator (fun _ => (1 : ℝ)) ω) ∂P :=
    integral_mono (hf.indicator hE) (hmax.add (hind.const_mul m)) hpt
  rw [integral_indicator hE, integral_add hmax (hind.const_mul m), integral_const_mul,
    integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] at hle
  exact hle

/-- **One-partition tail bound for the realized quadratic sum, random bracket.**  For every
cap level `c > 0`, truncation `λ > 0` and terminal level `m ≥ 0`,

`∫ (Q_n - λ)⁺ ≤ (4c²K + 2K²)/λ + 4 ∫ ((M t - M s)² - m)⁺ + (4m + K) K / c²`,

uniformly in `n`. -/
theorem integral_max_realizedQuadraticSum_sub_le [IsProbabilityMeasure P]
    (hM : Martingale M 𝔽 P) (hC : Martingale (fun r ω => M r ω * M r ω - B r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {s t : ℝ≥0} (hst : s ≤ t)
    (hBm : ∀ᵐ ω ∂P, MonotoneOn (fun v => B v ω) (Set.Icc s t))
    {K : ℝ} (hK : 0 ≤ K) (hBK : ∀ᵐ ω ∂P, B t ω - B s ω ≤ K)
    {c lam m : ℝ} (hc : 0 ≤ c) (hc2 : 0 < c ^ 2) (hlam : 0 < lam) (hm : 0 ≤ m) (n : ℕ) :
    (∫ ω, max (realizedQuadraticSum M s t n ω - lam) 0 ∂P)
      ≤ (4 * c ^ 2 * K + 2 * K ^ 2) / lam
        + 4 * (∫ ω, max ((M t ω - M s ω) ^ 2 - m) 0 ∂P)
        + (4 * m + K) * (K / c ^ 2) := by
  classical
  have hmaxnn : 0 ≤ ∫ ω, max ((M t ω - M s ω) ^ 2 - m) 0 ∂P :=
    integral_nonneg fun ω => le_max_right _ _
  have hlast : 0 ≤ (4 * m + K) * (K / c ^ 2) :=
    mul_nonneg (by linarith) (div_nonneg hK hc2.le)
  have hfirst : 0 ≤ (4 * c ^ 2 * K + 2 * K ^ 2) / lam :=
    div_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c)) hK)
      (mul_nonneg (by norm_num) (sq_nonneg K))) hlam.le
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : ∀ ω, max (realizedQuadraticSum M s t 0 ω - lam) 0 = 0 := by
      intro ω
      simp only [realizedQuadraticSum, Finset.range_zero, Finset.sum_empty, zero_sub]
      exact max_eq_right (by linarith)
    simp only [hzero, integral_zero]
    linarith
  have hn0 : n ≠ 0 := hn.ne'
  have hg : Monotone (uniformPartition s t n) := uniformPartition_mono s t n
  have hg0 : uniformPartition s t n 0 = s := uniformPartition_zero s t n
  have hgn : uniformPartition s t n n = t := uniformPartition_self hn0 hst
  have hgmem : ∀ i, i ≤ n → uniformPartition s t n i ∈ Set.Icc s t := fun i hi =>
    ⟨hg0.symm.le.trans (hg (Nat.zero_le i)), (hg hi).trans hgn.le⟩
  have hBg : ∀ᵐ ω ∂P, ∀ i j, i ≤ j → j ≤ n →
      B (uniformPartition s t n i) ω ≤ B (uniformPartition s t n j) ω := by
    filter_upwards [hBm] with ω hω i j hij hjn
    exact hω (hgmem i (hij.trans hjn)) (hgmem j hjn) (hg hij)
  have hBK' : ∀ᵐ ω ∂P,
      B (uniformPartition s t n n) ω - B (uniformPartition s t n 0) ω ≤ K := by
    filter_upwards [hBK] with ω hω
    rw [hgn, hg0]
    exact hω
  have hbound := integral_max_grid_quadratic_sub_le hM hC h2 hg hc hK hBg hBK' hlam
  have hexit := gridCap_exit_measure_sq_le_of_bracket hM hC h2 hg hc hBg
  rw [hgn, hg0] at hbound hexit
  have hEmeas : MeasurableSet (gridCapSet M (uniformPartition s t n) c n)ᶜ :=
    (𝔽.le _ _ (measurableSet_gridCapSet hM hg c n)).compl
  have hXint : Integrable (fun ω => (M t ω - M s ω) ^ 2) P :=
    integrable_increment_sq_of_memLp h2 s t
  have hEle : (∫ ω in (gridCapSet M (uniformPartition s t n) c n)ᶜ, (M t ω - M s ω) ^ 2 ∂P)
      ≤ ∫ ω, (M t ω - M s ω) ^ 2 ∂P :=
    setIntegral_le_integral hXint (Eventually.of_forall fun _ => sq_nonneg _)
  have hXval : (∫ ω, (M t ω - M s ω) ^ 2 ∂P) ≤ K := by
    rw [integral_increment_sq_eq_bracket hM hC h2 hst]
    have hBts : Integrable (fun ω => B t ω - B s ω) P :=
      (integrable_bracket_of_square_martingale hC h2 t).sub
        (integrable_bracket_of_square_martingale hC h2 s)
    calc (∫ ω, (B t ω - B s ω) ∂P) ≤ ∫ _ω, K ∂P :=
          integral_mono_ae hBts (integrable_const K) hBK
      _ = K := by rw [integral_const, probReal_univ, one_smul]
  have hPE : P.real (gridCapSet M (uniformPartition s t n) c n)ᶜ ≤ K / c ^ 2 := by
    rw [le_div_iff₀ hc2]
    linarith [hexit, hEle, hXval]
  have hEtail := setIntegral_le_integral_max_sub_add hXint hEmeas m
  have h4 : (4 * m + K) * P.real (gridCapSet M (uniformPartition s t n) c n)ᶜ
      ≤ (4 * m + K) * (K / c ^ 2) :=
    mul_le_mul_of_nonneg_left hPE (by linarith)
  have hQeq : (∫ ω, max (realizedQuadraticSum M s t n ω - lam) 0 ∂P)
      = ∫ ω, max ((∑ i ∈ Finset.range n, (M (uniformPartition s t n (i + 1)) ω
          - M (uniformPartition s t n i) ω) ^ 2) - lam) 0 ∂P := rfl
  rw [hQeq]
  linarith [hbound, hEtail, h4]

/-! ### The family statement -/

/-- **Uniform tails of the realized quadratic sums of a family of random-bracket martingales.**
If every `N k` is a square-integrable martingale with `N k * N k - B k` a martingale, `B k`
a.e. monotone on `[s, t]` with `B k t - B k s ≤ K`, and the TERMINAL squares
`(N k t - N k s)²` have uniformly small tails eventually along `l`, then the realized quadratic
sums have uniformly small tails, uniformly in the partition size `n` and eventually along `l`.

The terminal-tail premise cannot be dropped (see the module docstring). -/
theorem exists_uniform_realizedQuadraticSum_tail [IsProbabilityMeasure P]
    {ι : Type*} {l : Filter ι}
    {𝔽 : ι → Filtration ℝ≥0 mΩ} {N B : ι → ℝ≥0 → Ω → ℝ}
    (hN : ∀ k, Martingale (N k) (𝔽 k) P)
    (hC : ∀ k, Martingale (fun r ω => N k r ω * N k r ω - B k r ω) (𝔽 k) P)
    (h2 : ∀ k r, MemLp (N k r) 2 P) {s t : ℝ≥0} (hst : s ≤ t)
    (hBm : ∀ k, ∀ᵐ ω ∂P, MonotoneOn (fun v => B k v ω) (Set.Icc s t))
    {K : ℝ} (hK : 0 ≤ K) (hBK : ∀ k, ∀ᵐ ω ∂P, B k t ω - B k s ω ≤ K)
    (htail : ∀ γ : ℝ, 0 < γ → ∃ m : ℝ, ∀ᶠ k in l,
      ∫ ω, max ((N k t ω - N k s ω) ^ 2 - m) 0 ∂P ≤ γ) :
    ∀ γ : ℝ, 0 < γ → ∃ lam : ℝ, 0 < lam ∧ ∀ᶠ k in l, ∀ n : ℕ,
      ∫ ω, max (realizedQuadraticSum (N k) s t n ω - lam) 0 ∂P ≤ γ := by
  intro γ hγ
  obtain ⟨m, hm⟩ := htail (γ / 16) (by linarith)
  obtain ⟨m', hm'0, hm'm⟩ : ∃ m' : ℝ, 0 ≤ m' ∧ m ≤ m' :=
    ⟨max m 0, le_max_right _ _, le_max_left _ _⟩
  have hV0 : 0 ≤ (4 * m' + K) * K := mul_nonneg (by linarith) hK
  obtain ⟨c, hc0, hc2, hcV⟩ := exists_cap_level hV0 hγ
  have hBd0 : 0 ≤ 4 * c ^ 2 * K + 2 * K ^ 2 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c)) hK)
      (mul_nonneg (by norm_num) (sq_nonneg K))
  obtain ⟨lam, hlam, hBlam⟩ := exists_truncation_level hBd0 hγ
  refine ⟨lam, hlam, ?_⟩
  filter_upwards [hm] with k hk n
  have hbound := integral_max_realizedQuadraticSum_sub_le (hN k) (hC k) (h2 k) hst (hBm k) hK
    (hBK k) hc0 hc2 hlam hm'0 n
  have hXint : Integrable (fun ω => (N k t ω - N k s ω) ^ 2) P :=
    integrable_increment_sq_of_memLp (h2 k) s t
  have htail' : (∫ ω, max ((N k t ω - N k s ω) ^ 2 - m') 0 ∂P)
      ≤ ∫ ω, max ((N k t ω - N k s ω) ^ 2 - m) 0 ∂P :=
    integral_mono (hXint.sub (integrable_const m')).pos_part
      (hXint.sub (integrable_const m)).pos_part fun ω =>
        max_le_max (sub_le_sub_left hm'm _) le_rfl
  have hlast : (4 * m' + K) * (K / c ^ 2) = (4 * m' + K) * K / c ^ 2 := by ring
  rw [hlast] at hbound
  linarith

/-! ### The reduction inequality and its converse -/

/-- **The Lindeberg reduction inequality.**  Off the event that some increment exceeds `δ`
every Lindeberg indicator vanishes; on it the summands are dominated by the realized quadratic
sum `Q_n ≤ (Q_n - λ)⁺ + λ`. -/
theorem lindebergSum_le_integral_max_add [IsFiniteMeasure P] {N : ℝ≥0 → Ω → ℝ}
    (hNm : ∀ v, Measurable (N v)) (h2 : ∀ v, MemLp (N v) 2 P) (δ : ℝ) (s t : ℝ≥0) (n : ℕ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    lindebergSum P N δ s t n
      ≤ (∫ ω, max (realizedQuadraticSum N s t n ω - lam) 0 ∂P)
        + lam * P.real (bigIncrementSet N δ s t n) := by
  classical
  have hEi : ∀ i, MeasurableSet {ω | δ < |N (uniformPartition s t n (i + 1)) ω
      - N (uniformPartition s t n i) ω|} := fun i =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hNm _).sub (hNm _)))
  have hbig : MeasurableSet (bigIncrementSet N δ s t n) :=
    measurableSet_bigIncrementSet hNm δ s t n
  have hI : ∀ i, Integrable (Set.indicator {ω | δ < |N (uniformPartition s t n (i + 1)) ω
      - N (uniformPartition s t n i) ω|} (fun ω => (N (uniformPartition s t n (i + 1)) ω
        - N (uniformPartition s t n i) ω) ^ 2)) P := fun i =>
    (integrable_increment_sq_of_memLp h2 _ _).indicator (hEi i)
  have hQint : Integrable (fun ω => realizedQuadraticSum N s t n ω) P := by
    unfold realizedQuadraticSum
    exact integrable_finsetSum _ fun i _ => integrable_increment_sq_of_memLp h2 _ _
  have hmaxint : Integrable (fun ω => max (realizedQuadraticSum N s t n ω - lam) 0) P :=
    (hQint.sub (integrable_const lam)).pos_part
  have hind : Integrable ((bigIncrementSet N δ s t n).indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hbig
  have hpt : ∀ ω, (∑ i ∈ Finset.range n, Set.indicator
        {ω | δ < |N (uniformPartition s t n (i + 1)) ω - N (uniformPartition s t n i) ω|}
        (fun ω => (N (uniformPartition s t n (i + 1)) ω
          - N (uniformPartition s t n i) ω) ^ 2) ω)
      ≤ max (realizedQuadraticSum N s t n ω - lam) 0
        + lam * (bigIncrementSet N δ s t n).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ bigIncrementSet N δ s t n
    · simp only [Set.indicator_of_mem hω, mul_one]
      have h1 : (∑ i ∈ Finset.range n, Set.indicator
            {ω | δ < |N (uniformPartition s t n (i + 1)) ω - N (uniformPartition s t n i) ω|}
            (fun ω => (N (uniformPartition s t n (i + 1)) ω
              - N (uniformPartition s t n i) ω) ^ 2) ω)
          ≤ realizedQuadraticSum N s t n ω := by
        unfold realizedQuadraticSum
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : ω ∈ {ω | δ < |N (uniformPartition s t n (i + 1)) ω
            - N (uniformPartition s t n i) ω|}
        · exact le_of_eq (Set.indicator_of_mem hi _)
        · rw [Set.indicator_of_notMem hi]
          exact sq_nonneg _
      have h2' := le_max_left (realizedQuadraticSum N s t n ω - lam) 0
      linarith
    · simp only [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hzero : ∀ i ∈ Finset.range n, Set.indicator
          {ω | δ < |N (uniformPartition s t n (i + 1)) ω - N (uniformPartition s t n i) ω|}
          (fun ω => (N (uniformPartition s t n (i + 1)) ω
            - N (uniformPartition s t n i) ω) ^ 2) ω = 0 := by
        intro i hi
        refine Set.indicator_of_notMem (fun hmem => hω ?_) _
        exact Set.mem_iUnion₂.2 ⟨i, hi, hmem⟩
      rw [Finset.sum_eq_zero hzero]
      exact le_max_right _ _
  have hle : (∫ ω, ∑ i ∈ Finset.range n, Set.indicator
        {ω | δ < |N (uniformPartition s t n (i + 1)) ω - N (uniformPartition s t n i) ω|}
        (fun ω => (N (uniformPartition s t n (i + 1)) ω
          - N (uniformPartition s t n i) ω) ^ 2) ω ∂P)
      ≤ ∫ ω, (max (realizedQuadraticSum N s t n ω - lam) 0
        + lam * (bigIncrementSet N δ s t n).indicator (fun _ => (1 : ℝ)) ω) ∂P :=
    integral_mono (integrable_finsetSum _ fun i _ => hI i)
      (hmaxint.add (hind.const_mul lam)) hpt
  rw [integral_finsetSum _ fun i _ => hI i, integral_add hmaxint (hind.const_mul lam),
    integral_const_mul, integral_indicator_const (1 : ℝ) hbig, smul_eq_mul, mul_one] at hle
  rw [lindebergSum_eq]
  exact hle

end RandomBracket

end ReflectedGMS.MartingaleLimit
