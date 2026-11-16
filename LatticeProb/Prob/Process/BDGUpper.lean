import LatticeProb.Prob.Process.QuadraticVariation
import LatticeProb.Prob.Process.BDGFreedman
import LatticeProb.Prob.StoppingDyadic

/-!
# Upper half of the continuous Burkholder–Davis–Gundy inequality

Ported from the vertex-reinforced walk development. The statement `BdgUpperAt` of the upper bound
`E |M_T|^p ≤ C E Q^{p/2}` for a continuous martingale `M` from zero with quadratic covariation `Q`,
the reduction of the continuous statement to the discrete peeling bound, and the skeleton
approximation of a continuous path by its dyadic values. The stopped-skeleton lemmas it uses are in
`LatticeProb.Process.StoppedSkeleton`.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process.BdgUpperContinuous

noncomputable section

/-! ### The statement being reduced -/

/-- The upper half of the Burkholder–Davis–Gundy statement at the exponent `p`: there is
`C > 0` such that `E |M_T|^p ≤ C E Q^{p/2}` for every real continuous martingale `M` from `0` whose
quadratic covariation at the deterministic time `T` is `Q` (`LatticeProb.Process.HasQuadCovar`). -/
def BdgUpperAt (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
      (Q : Ω → Fin 1 → Fin 1 → ℝ),
      Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
      LatticeProb.Process.HasQuadCovar P M T Q →
        ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ≤
          ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P

/-- The upper half of the Burkholder–Davis–Gundy statement: `BdgUpperAt p` for every
`p > 1`.  It is the second conjunct of the Burkholder–Davis–Gundy statement. -/
def BurkholderDavisGundyUpper : Prop :=
  ∀ p : ℝ, 1 < p → BdgUpperAt p

/-- `HasQuadCovar` read in the `(0, 0)` coordinate: the dyadic sums of squared increments converge
in probability to `Q 0 0`.  This is all that `HasQuadCovar` is used for. -/
lemma hasQuadCovar_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : ℝ≥0 → Ω → Fin 1 → ℝ}
    {T : ℝ≥0} {Q : Ω → Fin 1 → Fin 1 → ℝ} (hQ : LatticeProb.Process.HasQuadCovar P M T Q) :
    TendstoInMeasure P (fun n ω => LatticeProb.Process.realizedCovar M T n ω 0 0) atTop (fun ω => Q ω 0 0) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hQ ε hε)
    (fun n => zero_le) (fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine hω.trans ?_
  exact (edist_le_pi_edist _ _ 0).trans (edist_le_pi_edist _ _ 0)

/-! ### The discrete ingredients -/

/-- **Discrete Burkholder bound with a bounded-increment term, terminal form, exponent `p`.**
Every discrete real martingale `Z` from `0` whose increments are at most `b` in absolute value on
`i < N` satisfies
`E |Z_N|^p ≤ C_p (E (∑_{i<N} (Z_{i+1} - Z_i)²)^{p/2} + b^p)`.

True: for `p ≥ 2` it follows from the peeling bound (Burkholder–Rosenthal form, proved in this
file) and the Garsia–Lenglart comparison `PredictableCompensatorLp`, see
`discreteBurkholderBoundedAt_of_ge_two`; for `1 < p < 2` it follows from Burkholder's square
function inequality `BurkholderLowIndex`, see `discreteBurkholderBoundedAt_of_lt_two` (the term
`b^p` is not needed there).  The term `b^p` is an artifact of the peeling route and is harmless
for the continuous-time passage, where `b → 0`.  It cannot be removed from the peeling bound
itself for `p > 2`, which is stated with the predictable variance: a one-step martingale equal to
`±B` with probability `ε/2` each has `E |Z_1|^p = B^p ε` and `(E Z_1²)^{p/2} = (B² ε)^{p/2}`. -/
def DiscreteBurkholderBoundedAt (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ) {b : ℝ}, 0 < b →
      Martingale Z 𝒢 P → (∀ ω, Z 0 ω = 0) →
      (∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) →
        ∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P ≤
          ENNReal.ofReal C *
            (∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
              + ENNReal.ofReal (b ^ p))

/-- **Garsia–Neveu comparison of the predictable and the optional square function in `Lᵠ`,
`q ≥ 1`.**  For a discrete martingale `X` with increments bounded by `b`, the predictable
compensator `condQvar X n = ∑_{i<n} E[(X_{i+1} - X_i)² | ℱ_i]` of the optional square function
`∑_{i<n} (X_{i+1} - X_i)²` satisfies
`E (condQvar X n)^q ≤ q^q E (∑_{i<n} (X_{i+1} - X_i)²)^q`.

True, and proved below (`predictableCompensatorLp_holds`): this is the Garsia–Neveu /
Lenglart–Lépingle–Pratelli inequality `E A_n^q ≤ q^q E B_n^q` for the predictable compensator `A`
of an increasing adapted process `B`, `q ≥ 1`.  Proof: `A_{k+1}` is `ℱ_k`-measurable,
`A_n^q ≤ q ∑_k A_{k+1}^{q-1} (A_{k+1} - A_k)` by convexity,
`E[A_{k+1}^{q-1} E[a_k | ℱ_k]] = E[A_{k+1}^{q-1} a_k] ≤ E[A_n^{q-1} a_k]`, summation and Hölder give
`E A_n^q ≤ q (E A_n^q)^{1-1/q} (E B_n^q)^{1/q}`, and `E A_n^q < ∞` since the increments are bounded.
It is the step that turns the predictable variance in the peeling bound into the optional square
function that the quadratic covariation controls. -/
def PredictableCompensatorLp : Prop :=
  ∀ q : ℝ, 1 ≤ q →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (n : ℕ) {b : ℝ}, 0 < b →
      Martingale X ℱ P → (∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b) →
        ∫⁻ ω, ENNReal.ofReal (LatticeProb.Process.condQvar P ℱ X n ω) ^ q ∂P ≤
          ENNReal.ofReal (q ^ q) *
            ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range n, (X (i + 1) ω - X i ω) ^ 2) ^ q ∂P

/-- **`DiscreteBurkholderBoundedAt p` for `p ≥ 2`** from the peeling bound
(`LatticeProb.Process.RandomizedFreedman.peelingSummationBound_holds`, proved) and
`PredictableCompensatorLp` at `q = p / 2`. -/
theorem discreteBurkholderBoundedAt_of_ge_two (hA : PredictableCompensatorLp) {p : ℝ}
    (hp : 2 ≤ p) : DiscreteBurkholderBoundedAt p := by
  obtain ⟨C₀, hC₀, h₀⟩ := LatticeProb.Process.RandomizedFreedman.peelingSummationBound_holds p hp
  have hq1 : 1 ≤ p / 2 := by linarith
  have hqq : 1 ≤ (p / 2) ^ (p / 2) := Real.one_le_rpow hq1 (by linarith)
  refine ⟨C₀ * (p / 2) ^ (p / 2), by positivity, ?_⟩
  intro Ω _ P _ 𝒢 Z N b hb hM h0 hinc
  have d1 : ∀ k : ℕ, P {ω | condQvar P 𝒢 Z N ω < (2 : ℝ) ^ k} ≤
      P {ω | condQvar P 𝒢 Z N ω < (2 : ℝ) ^ (k + 1)} := by
    intro k
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_lt_of_le hω (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))
  have d2 : ∀ k : ℕ, {ω | condQvar P 𝒢 Z N ω ≤ (2 : ℝ) ^ (k + 1)} ⊆
      {ω | condQvar P 𝒢 Z N ω < (2 : ℝ) ^ (k + 2)} := by
    intro k ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt hω (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self _))
  have hpeel := h₀ P 𝒢 Z N hb hM h0 hinc d1 d2
  have hcomp := hA (p / 2) hq1 P 𝒢 Z N hb hM hinc
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((p / 2) ^ (p / 2)) := by
    simpa using ENNReal.ofReal_le_ofReal hqq
  calc ∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P
      ≤ ENNReal.ofReal C₀ * (∫⁻ ω, ENNReal.ofReal (condQvar P 𝒢 Z N ω) ^ (p / 2) ∂P
          + ENNReal.ofReal (b ^ p)) := hpeel
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal ((p / 2) ^ (p / 2)) *
          ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
          + ENNReal.ofReal ((p / 2) ^ (p / 2)) * ENNReal.ofReal (b ^ p)) := by
        gcongr
        exact le_mul_of_one_le_left zero_le hone
    _ = ENNReal.ofReal (C₀ * (p / 2) ^ (p / 2)) *
          (∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
            + ENNReal.ofReal (b ^ p)) := by
        rw [ENNReal.ofReal_mul hC₀.le]
        ring

/-- Tangent-line inequality for `t ↦ t ^ q`, `q ≥ 1`: `x^q - y^q ≤ q x^(q-1) (x - y)` for
`0 ≤ y ≤ x`. -/
lemma rpow_sub_rpow_le {q : ℝ} (hq : 1 ≤ q) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ q - y ^ q ≤ q * x ^ (q - 1) * (x - y) := by
  rcases eq_or_lt_of_le (hy.trans hxy) with hx | hx
  · have hy0 : y = 0 := le_antisymm (hx ▸ hxy) hy
    subst hy0
    rw [← hx]
    have hq0 : q ≠ 0 := by linarith
    simp [Real.zero_rpow hq0]
  · have hs : -1 ≤ y / x - 1 := by
      have : 0 ≤ y / x := div_nonneg hy hx.le
      linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hq
    have h1 : 1 + (y / x - 1) = y / x := by ring
    rw [h1, Real.div_rpow hy hx.le] at hb
    have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx _
    have h3 : x ^ q * (1 + q * (y / x - 1)) ≤ y ^ q := by
      have := mul_le_mul_of_nonneg_left hb hxq.le
      rwa [mul_div_cancel₀ _ hxq.ne'] at this
    have h2 : x ^ q = x ^ (q - 1) * x := by
      rw [← Real.rpow_add_one hx.ne']
      congr 1
      ring
    have h4 : x ^ q * (y / x - 1) = x ^ (q - 1) * (y - x) := by
      rw [h2]
      field_simp
    have h5 : x ^ q * (1 + q * (y / x - 1)) = x ^ q + q * (x ^ (q - 1) * (y - x)) := by
      rw [mul_add, mul_one, mul_left_comm, h4]
    nlinarith [h3, h5]

/-- For a bounded measurable `ℱ i`-measurable `g`, pairing with the squared increment or with the
one-step conditional variance gives the same integral. -/
lemma integral_mul_sq_eq_integral_mul_incVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) {b : ℝ} {i : ℕ} (hinc : ∀ ω, |X (i + 1) ω - X i ω| ≤ b)
    {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ i] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * (X (i + 1) ω - X i ω) ^ 2 ∂P =
      ∫ ω, g ω * LatticeProb.Process.RandomizedFreedman.incVar P ℱ X i ω ∂P := by
  have hXm : ∀ j, Measurable (X j) := fun j =>
    ((hM.stronglyMeasurable j).mono (ℱ.le j)).measurable
  have hdm : Measurable (fun ω => X (i + 1) ω - X i ω) := (hXm (i + 1)).sub (hXm i)
  have hIq : Integrable (fun ω => (X (i + 1) ω - X i ω) ^ 2) P := by
    refine LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le (C := b ^ 2) (hdm.pow_const 2) fun ω => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hinc ω)).1 (abs_le.mp (hinc ω)).2
  have hIh : Integrable (fun ω => g ω * (X (i + 1) ω - X i ω) ^ 2) P :=
    hIq.bdd_mul (hg.mono (ℱ.le i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgb ω)
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := ℱ i) hg
    (g := fun ω => (X (i + 1) ω - X i ω) ^ 2) (by exact hIh) hIq
  calc ∫ ω, g ω * (X (i + 1) ω - X i ω) ^ 2 ∂P
      = ∫ ω, P[g * (fun ω => (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω ∂P :=
        (integral_condExp (ℱ.le i)).symm
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with ω e1
        rw [e1]
        rfl

/-- For a bounded measurable nonnegative `f`, `E (ofReal f)^q = ofReal (E f^q)`. -/
lemma lintegral_ofReal_rpow_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (h0 : ∀ ω, 0 ≤ f ω)
    (hC : ∀ ω, f ω ≤ C) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ q ∂P = ENNReal.ofReal (∫ ω, f ω ^ q ∂P) := by
  have hI : Integrable (fun ω => f ω ^ q) P := by
    refine LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le (C := C ^ q) (hf.pow_const q) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (h0 ω) _)]
    exact Real.rpow_le_rpow (h0 ω) (hC ω) hq
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (h0 ω) _)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (h0 ω) hq]

/-- The real-variable end of the Garsia–Neveu argument: from `J ≤ q H` and
`H ≤ J^{1-1/q} K^{1/q}` conclude `J ≤ q^q K`. -/
lemma garsia_final {q J K H : ℝ} (hq : 1 < q) (hJ0 : 0 ≤ J) (hK0 : 0 ≤ K)
    (hH : H ≤ J ^ (1 - q⁻¹) * K ^ q⁻¹) (hJH : J ≤ q * H) : J ≤ q ^ q * K := by
  have hq0 : 0 < q := by linarith
  rcases eq_or_lt_of_le hJ0 with hJ | hJ
  · rw [← hJ]
    positivity
  · have h1 : J ≤ q * (J ^ (1 - q⁻¹) * K ^ q⁻¹) :=
      hJH.trans (mul_le_mul_of_nonneg_left hH hq0.le)
    have hJe : J = J ^ q⁻¹ * J ^ (1 - q⁻¹) := by
      rw [← Real.rpow_add hJ]
      simp
    have hpos : 0 < J ^ (1 - q⁻¹) := Real.rpow_pos_of_pos hJ _
    have h2 : J ^ q⁻¹ ≤ q * K ^ q⁻¹ := by
      have h3 : J ^ q⁻¹ * J ^ (1 - q⁻¹) ≤ (q * K ^ q⁻¹) * J ^ (1 - q⁻¹) := by
        calc J ^ q⁻¹ * J ^ (1 - q⁻¹) = J := hJe.symm
          _ ≤ q * (J ^ (1 - q⁻¹) * K ^ q⁻¹) := h1
          _ = (q * K ^ q⁻¹) * J ^ (1 - q⁻¹) := by ring
      exact le_of_mul_le_mul_right h3 hpos
    have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hJ.le _) h2 hq0.le
    rw [Real.rpow_inv_rpow hJ.le hq0.ne', Real.mul_rpow hq0.le (Real.rpow_nonneg hK0 _),
      Real.rpow_inv_rpow hK0 hq0.ne'] at h3
    exact h3

/-- **`PredictableCompensatorLp` holds.**  Garsia–Neveu: the predictable compensator of the sum of
squared increments is controlled in `Lᵠ` by the sum of squared increments with constant `q^q`.
The proof is the one in the docstring of `PredictableCompensatorLp`, run on the bounded version
`max 0 (min (incVar) b²)` of the one-step conditional variances (equal to them almost surely). -/
theorem predictableCompensatorLp_holds : PredictableCompensatorLp := by
  intro q hq Ω _ P _ ℱ X n b hb hM hinc
  have hq0 : 0 < q := by linarith
  have hXm : ∀ j, Measurable (X j) := fun j =>
    ((hM.stronglyMeasurable j).mono (ℱ.le j)).measurable
  set V : ℕ → Ω → ℝ := fun i => LatticeProb.Process.RandomizedFreedman.incVar P ℱ X i with hV
  set W : ℕ → Ω → ℝ := fun i ω => max 0 (min (V i ω) (b ^ 2)) with hW
  have hb2 : 0 ≤ b ^ 2 := by positivity
  have hW0 : ∀ i ω, 0 ≤ W i ω := fun i ω => le_max_left _ _
  have hWb : ∀ i ω, W i ω ≤ b ^ 2 := fun i ω => max_le hb2 (min_le_right _ _)
  have hW_sm : ∀ i, StronglyMeasurable[ℱ i] (W i) := fun i => by
    have h : Measurable[ℱ i] (V i) :=
      (stronglyMeasurable_condExp (m := ℱ i) (μ := P)
        (f := fun ω => (X (i + 1) ω - X i ω) ^ 2)).measurable
    exact (measurable_const.max (h.min measurable_const)).stronglyMeasurable
  have hWae : ∀ᵐ ω ∂P, ∀ i, i < n → W i ω = V i ω := by
    filter_upwards [LatticeProb.Process.RandomizedFreedman.incVar_ae_bounds P ℱ X hM hinc] with ω hω i hi
    obtain ⟨h1, h2⟩ := hω i hi
    simp only [hW]
    rw [min_eq_left h2, max_eq_right h1]
  set A : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range k, W i ω with hA
  set a : ℕ → Ω → ℝ := fun i ω => (X (i + 1) ω - X i ω) ^ 2 with ha
  set B : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range k, a i ω with hB'
  have hA0 : ∀ k ω, 0 ≤ A k ω := fun k ω => Finset.sum_nonneg fun i _ => hW0 i ω
  have hAb : ∀ k ω, A k ω ≤ k * b ^ 2 := fun k ω => by
    calc A k ω ≤ ∑ i ∈ Finset.range k, b ^ 2 := Finset.sum_le_sum fun i _ => hWb i ω
      _ = k * b ^ 2 := by simp
  have hAsucc : ∀ k ω, A (k + 1) ω = A k ω + W k ω := fun k ω => Finset.sum_range_succ _ _
  have hAmono : ∀ k m, k ≤ m → ∀ ω, A k ω ≤ A m ω := fun k m hkm ω =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkm)
      (fun i _ _ => hW0 i ω)
  have hAm : ∀ k, Measurable (A k) := fun k =>
    Finset.measurable_sum _ fun i _ =>
      ((hW_sm i).mono (ℱ.le i)).measurable
  have hAsm : ∀ k, StronglyMeasurable[ℱ k] (A (k + 1)) := fun k => by
    have h : Measurable[ℱ k] (A (k + 1)) :=
      Finset.measurable_sum _ fun i hi =>
        ((hW_sm i).mono (ℱ.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).measurable
    exact h.stronglyMeasurable
  have ha0 : ∀ i ω, 0 ≤ a i ω := fun i ω => sq_nonneg _
  have hab : ∀ i, i < n → ∀ ω, a i ω ≤ b ^ 2 := fun i hi ω =>
    sq_le_sq' (abs_le.mp (hinc i hi ω)).1 (abs_le.mp (hinc i hi ω)).2
  have ham : ∀ i, Measurable (a i) := fun i => ((hXm (i + 1)).sub (hXm i)).pow_const 2
  have hB0 : ∀ k ω, 0 ≤ B k ω := fun k ω => Finset.sum_nonneg fun i _ => ha0 i ω
  have hBb : ∀ k, k ≤ n → ∀ ω, B k ω ≤ k * b ^ 2 := fun k hk ω => by
    calc B k ω ≤ ∑ i ∈ Finset.range k, b ^ 2 :=
          Finset.sum_le_sum fun i hi => hab i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk) ω
      _ = k * b ^ 2 := by simp
  have hBm : ∀ k, Measurable (B k) := fun k => Finset.measurable_sum _ fun i _ => ham i
  -- pointwise tangent bound
  have hpt : ∀ ω, A n ω ^ q ≤ q * ∑ k ∈ Finset.range n, A (k + 1) ω ^ (q - 1) * W k ω := by
    intro ω
    have hq0' : q ≠ 0 := hq0.ne'
    have htel : A n ω ^ q = ∑ k ∈ Finset.range n, (A (k + 1) ω ^ q - A k ω ^ q) := by
      rw [Finset.sum_range_sub (fun k => A k ω ^ q) n]
      have : A 0 ω = 0 := by simp [hA]
      rw [this, Real.zero_rpow hq0', sub_zero]
    rw [htel, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := rpow_sub_rpow_le hq (hA0 k ω) (hAmono k (k + 1) (Nat.le_succ k) ω)
    have h' : A (k + 1) ω - A k ω = W k ω := by rw [hAsucc]; ring
    rw [h'] at h
    linarith
  -- integrability facts
  have hgm : ∀ k, StronglyMeasurable[ℱ k] (fun ω => A (k + 1) ω ^ (q - 1)) := fun k => by
    have h : Measurable[ℱ k] (A (k + 1)) := (hAsm k).measurable
    exact (h.pow_const (q - 1)).stronglyMeasurable
  have hgb : ∀ k ω, |A (k + 1) ω ^ (q - 1)| ≤ ((k + 1 : ℕ) * b ^ 2) ^ (q - 1) := fun k ω => by
    rw [abs_of_nonneg (Real.rpow_nonneg (hA0 _ ω) _)]
    exact Real.rpow_le_rpow (hA0 _ ω) (hAb _ ω) (by linarith)
  have hWm : ∀ k, Measurable (W k) := fun k => ((hW_sm k).mono (ℱ.le k)).measurable
  have hI1 : ∀ k, Integrable (fun ω => A (k + 1) ω ^ (q - 1) * W k ω) P := fun k => by
    refine LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le
      (C := ((k + 1 : ℕ) * b ^ 2) ^ (q - 1) * b ^ 2)
      (((hAm (k + 1)).pow_const _).mul (hWm k)) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (hW0 k ω)]
    exact mul_le_mul (hgb k ω) (hWb k ω) (hW0 k ω) (Real.rpow_nonneg (by positivity) _)
  have hI2 : ∀ k, k < n → Integrable (fun ω => A (k + 1) ω ^ (q - 1) * a k ω) P := fun k hk => by
    refine LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le
      (C := ((k + 1 : ℕ) * b ^ 2) ^ (q - 1) * b ^ 2)
      (((hAm (k + 1)).pow_const _).mul (ham k)) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (ha0 k ω)]
    exact mul_le_mul (hgb k ω) (hab k hk ω) (ha0 k ω) (Real.rpow_nonneg (by positivity) _)
  have hI3 : ∀ k, k < n → Integrable (fun ω => A n ω ^ (q - 1) * a k ω) P := fun k hk => by
    refine LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le
      (C := ((n : ℝ) * b ^ 2) ^ (q - 1) * b ^ 2)
      (((hAm n).pow_const _).mul (ham k)) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (ha0 k ω)]
    exact mul_le_mul
      (by rw [abs_of_nonneg (Real.rpow_nonneg (hA0 _ ω) _)]
          exact Real.rpow_le_rpow (hA0 _ ω) (hAb _ ω) (by linarith))
      (hab k hk ω) (ha0 k ω) (Real.rpow_nonneg (by positivity) _)
  have hid : ∀ k, k < n → ∫ ω, A (k + 1) ω ^ (q - 1) * W k ω ∂P =
      ∫ ω, A (k + 1) ω ^ (q - 1) * a k ω ∂P := by
    intro k hk
    have h1 := integral_mul_sq_eq_integral_mul_incVar P ℱ X hM (hinc k hk) (hgm k) (hgb k)
    calc ∫ ω, A (k + 1) ω ^ (q - 1) * W k ω ∂P
        = ∫ ω, A (k + 1) ω ^ (q - 1) * LatticeProb.Process.RandomizedFreedman.incVar P ℱ X k ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hWae] with ω hω
          rw [hω k hk]
      _ = ∫ ω, A (k + 1) ω ^ (q - 1) * a k ω ∂P := h1.symm
  have hAqI : Integrable (fun ω => A n ω ^ q) P := by
    refine LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le (C := ((n : ℝ) * b ^ 2) ^ q)
      ((hAm n).pow_const q) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (hA0 _ ω) _)]
    exact Real.rpow_le_rpow (hA0 _ ω) (hAb _ ω) hq0.le
  have hsumI : Integrable (fun ω => q * ∑ k ∈ Finset.range n, A (k + 1) ω ^ (q - 1) * W k ω) P :=
    (integrable_finsetSum _ fun k _ => hI1 k).const_mul q
  have hmain : ∫ ω, A n ω ^ q ∂P ≤ q * ∫ ω, A n ω ^ (q - 1) * B n ω ∂P := by
    calc ∫ ω, A n ω ^ q ∂P
        ≤ ∫ ω, q * ∑ k ∈ Finset.range n, A (k + 1) ω ^ (q - 1) * W k ω ∂P :=
          integral_mono hAqI hsumI hpt
      _ = q * ∑ k ∈ Finset.range n, ∫ ω, A (k + 1) ω ^ (q - 1) * W k ω ∂P := by
          rw [integral_const_mul, integral_finsetSum _ fun k _ => hI1 k]
      _ = q * ∑ k ∈ Finset.range n, ∫ ω, A (k + 1) ω ^ (q - 1) * a k ω ∂P := by
          congr 1
          exact Finset.sum_congr rfl fun k hk => hid k (Finset.mem_range.mp hk)
      _ ≤ q * ∑ k ∈ Finset.range n, ∫ ω, A n ω ^ (q - 1) * a k ω ∂P := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) hq0.le
          have hk' := Finset.mem_range.mp hk
          refine integral_mono (hI2 k hk') (hI3 k hk') fun ω => ?_
          refine mul_le_mul_of_nonneg_right ?_ (ha0 k ω)
          exact Real.rpow_le_rpow (hA0 _ ω) (hAmono (k + 1) n hk' ω) (by linarith)
      _ = q * ∫ ω, A n ω ^ (q - 1) * B n ω ∂P := by
          congr 1
          rw [← integral_finsetSum _ fun k hk => hI3 k (Finset.mem_range.mp hk)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [hB', Finset.mul_sum]
  -- the Lᵠ conclusion
  have hK0 : 0 ≤ ∫ ω, B n ω ^ q ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (hB0 _ ω) _
  have hJ0 : 0 ≤ ∫ ω, A n ω ^ q ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (hA0 _ ω) _
  have hreal : ∫ ω, A n ω ^ q ∂P ≤ q ^ q * ∫ ω, B n ω ^ q ∂P := by
    rcases eq_or_lt_of_le hq with hq1 | hq1
    · have hq1' : q = 1 := hq1.symm
      have hdiff : q - 1 = 0 := by linarith
      have h1 : ∫ ω, A n ω ^ (q - 1) * B n ω ∂P = ∫ ω, B n ω ^ q ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show A n ω ^ (q - 1) * B n ω = B n ω ^ q
        rw [hdiff, Real.rpow_zero, one_mul, hq1', Real.rpow_one]
      rw [h1, hq1'] at hmain
      simpa [hq1'] using hmain
    · have hpq : (q.conjExponent).HolderConjugate q := (Real.HolderConjugate.conjExponent hq1).symm
      have hp'pos : 0 < q.conjExponent := hpq.pos
      have hf0 : 0 ≤ᵐ[P] fun ω => A n ω ^ (q - 1) :=
        Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hA0 _ ω) _
      have hg0 : 0 ≤ᵐ[P] B n := Filter.Eventually.of_forall fun ω => hB0 _ ω
      have hfL : MemLp (fun ω => A n ω ^ (q - 1)) (ENNReal.ofReal q.conjExponent) P := by
        refine MemLp.of_bound ((hAm n).pow_const _).aestronglyMeasurable (((n : ℝ) * b ^ 2) ^ (q - 1))
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hA0 _ ω) _)]
        exact Real.rpow_le_rpow (hA0 _ ω) (hAb _ ω) (by linarith)
      have hgL : MemLp (B n) (ENNReal.ofReal q) P := by
        refine MemLp.of_bound (hBm n).aestronglyMeasurable ((n : ℝ) * b ^ 2)
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hB0 _ ω)]
        exact hBb n le_rfl ω
      have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hfL hgL
      have hpow : ∀ ω, (A n ω ^ (q - 1)) ^ q.conjExponent = A n ω ^ q := fun ω => by
        rw [← Real.rpow_mul (hA0 _ ω)]
        congr 1
        unfold Real.conjExponent
        field_simp
      simp only [hpow, one_div] at hH
      have hinv : q.conjExponent⁻¹ = 1 - q⁻¹ := by
        have := hpq.inv_add_inv_eq_one
        linarith
      rw [hinv] at hH
      exact garsia_final hq1 hJ0 hK0 hH hmain
  -- conversion to the statement
  have hlhs : ∫⁻ ω, ENNReal.ofReal (LatticeProb.Process.condQvar P ℱ X n ω) ^ q ∂P =
      ENNReal.ofReal (∫ ω, A n ω ^ q ∂P) := by
    rw [← lintegral_ofReal_rpow_eq (hAm n) (hA0 n) (hAb n) hq0.le]
    refine lintegral_congr_ae ?_
    filter_upwards [hWae] with ω hω
    have : LatticeProb.Process.condQvar P ℱ X n ω = A n ω := by
      show ∑ i ∈ Finset.range n, LatticeProb.Process.RandomizedFreedman.incVar P ℱ X i ω = _
      exact Finset.sum_congr rfl fun i hi => (hω i (Finset.mem_range.mp hi)).symm
    rw [this]
  have hrhs : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range n, (X (i + 1) ω - X i ω) ^ 2) ^ q ∂P =
      ENNReal.ofReal (∫ ω, B n ω ^ q ∂P) :=
    lintegral_ofReal_rpow_eq (hBm n) (hB0 n) (hBb n le_rfl) hq0.le
  rw [hlhs, hrhs, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal
/-! ### The continuous-time step -/

/-- **Localisation of a continuous martingale on its dyadic skeleton (the continuous-time step).**
Let `M` be a real continuous martingale from `0`, for an arbitrary filtration indexed by `ℝ≥0`
(no usual conditions), let `T` be a deterministic time, `n` a dyadic level, `b > 0`, `L ≥ 0`, and
write `rc_n ω = realizedCovar M T n ω 0 0` for the sum of squared increments over the `2^n` dyadic
intervals of `[0, T]`.  Then there are a discrete filtration `𝒢` and a discrete real martingale `Z`
from `0` such that

* every increment `Z_{i+1} - Z_i`, `i < 2^n`, is at most `b` in absolute value;
* `∑_{i < 2^n} (Z_{i+1} - Z_i)² ≤ min (rc_n + b²) (L + 2 b²)` pointwise;
* `Z_{2^n} ω = M_T ω` at every `ω` with `rc_n ω ≤ L` such that
  `|M_s ω - M_t ω| < b` whenever `s, t ∈ [0, T]` and `|s - t| ≤ T / 2^n`.

True.  Take `t_k = T k / 2^n`, `𝒢_k = ℱ_{t_{min(k, 2^n)}}`, `Z_k = M_{t_{min(k, 2^n)} ∧ ρ}`, where
`ρ` is the first of the two times: the first `t ≤ T` with `|M_t - M_{t_k}| ≥ b` for the dyadic
interval `[t_k, t_{k+1}]` containing `t`, and the first grid time `t_k` with
`∑_{i<k} (M_{t_{i+1}} - M_{t_i})² > L`.  `ρ` is a stopping time of `ℱ` (on each dyadic interval
it is the hitting time of a closed set by a continuous adapted process, and the grid time is a
discrete stopping time).  `Z` is a martingale by optional stopping of the continuous, hence
right-continuous, martingale `M` at the bounded stopping time `ρ ∧ T` (dyadic approximation of
`ρ` from above and right-continuity of paths), and is bounded by `2^n b`.  Before `ρ` every
increment on the current interval is below `b`, and at an interval-exit hit it equals `b` by
continuity, which gives the first item.  The sum of squares of the stopped increments consists of
full increments up to the last full interval before `ρ` (at most the first partial sum exceeding
`L`, that is at most `L + b²`, and at most `rc_n`) and of at most one partial increment of size at
most `b`, which gives the second item.  On the event of the third item `ρ` is never triggered, so
`Z_{2^n} = M_T`.

This is the only genuinely continuous-time input of the upper half.  It does not mention the
quadratic covariation `Q`: `Q` enters only through `HasQuadCovar`, read as convergence in
probability of the sums `rc_n`.

Where the content lies.  Only the oscillation stop is continuous-time: with `ρ_b` the first time
`|M_t - M_{t_k}| ≥ b` on a dyadic interval, one needs (1) `ρ_b` is an `ℱ`-stopping time (hitting a
closed set with a continuous adapted process, expressed through a countable dense set of times), and
(2) `t ↦ M_{t ∧ ρ_b}` is again a martingale (optional stopping for right-continuous martingales,
Karatzas–Shreve, Brownian Motion and Stochastic Calculus, Section 1.3.C, via dyadic approximation of `ρ_b`).  The stop at the first grid
time with running sum above `L` is a discrete stopping time of the skeleton, so the discrete
optional stopping theorem covers it, and the three items are deterministic path bookkeeping.
Mathlib has optional sampling only for stopping times with countable range
(`MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp`) and no optional stopping for
continuous-time hitting times; that is why this statement is carried as a named proposition. -/
def StoppedDyadicSkeleton : Prop :=
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
          LatticeProb.Process.realizedCovar M T n ω 0 0 ≤ L → Z (2 ^ n) ω = M T ω 0)

/-! ### The passage from the stopped skeleton to the upper half -/

/-- Uniform continuity on `[0, T]`: for fixed `b > 0` the modulus condition of
`StoppedDyadicSkeleton` holds for all large levels `n`. -/
lemma eventually_modulus_lt {f : ℝ≥0 → ℝ} (hf : Continuous f) (T : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n →
      |f s - f t| < b := by
  have huc : UniformContinuousOn f (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc b hb
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((T : ℝ) / δ) (one_lt_two : (1 : ℝ) < 2)
  filter_upwards [eventually_ge_atTop m] with n hn s t hs ht hst
  have h2 : (T : ℝ) / δ < 2 ^ n := hm.trans_le (pow_le_pow_right₀ (by norm_num) hn)
  have hlt : |(s : ℝ) - t| < δ := by
    calc _ ≤ (T : ℝ) / 2 ^ n := hst
      _ < δ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at h2
        linarith
  have := hδ' s ⟨zero_le, hs⟩ t ⟨zero_le, ht⟩ (by rwa [NNReal.dist_eq])
  simpa [Real.dist_eq] using this

/-- `(x + y) ^ q ≤ 2 ^ q (x ^ q + y ^ q)` in `ℝ≥0∞` for `q ≥ 0`. -/
lemma add_rpow_le_two_rpow_mul {q : ℝ} (hq : 0 ≤ q) (x y : ℝ≥0∞) :
    (x + y) ^ q ≤ 2 ^ q * (x ^ q + y ^ q) := by
  have h1 : x + y ≤ 2 * max x y := by
    calc x + y ≤ max x y + max x y := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max x y := (two_mul _).symm
  calc (x + y) ^ q ≤ (2 * max x y) ^ q := ENNReal.rpow_le_rpow h1 hq
    _ = 2 ^ q * (max x y) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
    _ ≤ 2 ^ q * (x ^ q + y ^ q) := by
      gcongr
      rcases le_total x y with h | h
      · rw [max_eq_right h]; exact le_add_self
      · rw [max_eq_left h]; exact le_self_add

/-- **The upper half at one exponent from the stopped skeleton.**  If the discrete Burkholder
bound with a bounded-increment term holds at `p > 1` and the stopped dyadic skeleton exists, then
`E |M_T|^p ≤ C 2^{p/2} E Q^{p/2}` for every continuous martingale `M` from `0` with
`HasQuadCovar P M T Q`.

Proof.  Fix `b > 0` and `L ∈ ℕ`.  Let `Z^n` be the stopped skeleton of level `n`.  By the discrete
bound, `E |Z^n_{2^n}|^p ≤ C (E (min (rc_n + b²) (L + 2 b²))^{p/2} + b^p)`.  Along a subsequence
`rc_{n_j} → Q` almost surely (`HasQuadCovar` is convergence in probability).  On `{Q < L}`, almost
surely, `rc_{n_j} ≤ L` and the modulus condition holds for all large `j` (uniform continuity of
the paths), so `Z^{n_j}_{2^{n_j}} = M_T` eventually; Fatou gives
`E 1_{Q < L} |M_T|^p ≤ liminf_j E |Z^{n_j}_{2^{n_j}}|^p`.  The truncated squares are bounded by
`(L + 2 b²)^{p/2}`, so bounded convergence replaces them by those of `Q`; the elementary bound
`(x + y)^q ≤ 2^q (x^q + y^q)` removes the truncation, and `b → 0`, `L → ∞` (monotone convergence)
finish.  No uniform integrability of the sums `rc_n` is used. -/
theorem bdgUpperAt_of_stopped {p : ℝ} (hp : 1 < p) (hDB : DiscreteBurkholderBoundedAt p)
    (hS : StoppedDyadicSkeleton) : BdgUpperAt p := by
  obtain ⟨C, hC, hDB'⟩ := hDB
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / 2 := by positivity
  refine ⟨C * 2 ^ (p / 2), by positivity, ?_⟩
  intro Ω _ P _ ℱ M T Q hM hcont h0 hQ
  have hMeas : ∀ t, Measurable (fun ω => M t ω 0) := fun t =>
    (measurable_pi_apply 0).comp (((hM.stronglyMeasurable t).mono (ℱ.le t)).measurable)
  have hrc_meas : ∀ n, Measurable (fun ω => LatticeProb.Process.realizedCovar M T n ω 0 0) := by
    intro n
    simp only [LatticeProb.Process.realizedCovar]
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact ((hMeas _).sub (hMeas _)).mul ((hMeas _).sub (hMeas _))
  have hQ0 := hasQuadCovar_coord hQ
  obtain ⟨ns, hns, hae⟩ := hQ0.exists_seq_tendsto_ae
  have hQm : AEMeasurable (fun ω => Q ω 0 0) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun j => (hrc_meas (ns j)).aemeasurable) hae
  obtain ⟨Q', hQ'm, hQQ'⟩ := hQm
  have hae' : ∀ᵐ ω ∂P,
      Tendsto (fun j => LatticeProb.Process.realizedCovar M T (ns j) ω 0 0) atTop (𝓝 (Q' ω)) := by
    filter_upwards [hae, hQQ'] with ω h1 h2
    have h2' : Q ω 0 0 = Q' ω := h2
    rw [h2'] at h1
    exact h1
  have key : ∀ (L : ℕ) (b : ℝ), 0 < b →
      ∫⁻ ω, {ω | Q' ω < (L : ℝ)}.indicator (fun ω => ‖M T ω 0‖ₑ ^ p) ω ∂P ≤
        ENNReal.ofReal C * ((2 : ℝ≥0∞) ^ (p / 2) * ∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P
          + ((2 : ℝ≥0∞) ^ (p / 2) + 1) * ENNReal.ofReal (b ^ p)) := by
    intro L b hb
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hSn := fun n : ℕ => hS P ℱ M T hM hcont h0 n hb hL0
    choose 𝒢 Z hZ using hSn
    set f : ℕ → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal |Z (ns j) (2 ^ ns j) ω| ^ p with hf
    set g : ℕ → Ω → ℝ≥0∞ := fun j ω =>
      ENNReal.ofReal (min (LatticeProb.Process.realizedCovar M T (ns j) ω 0 0 + b ^ 2) (L + 2 * b ^ 2)) ^
        (p / 2) with hg
    have hf_meas : ∀ j, Measurable (f j) := fun j => by
      have h1 : Measurable (Z (ns j) (2 ^ ns j)) :=
        (((hZ (ns j)).1.stronglyMeasurable _).mono ((𝒢 (ns j)).le _)).measurable
      exact (h1.abs.ennreal_ofReal).pow_const p
    have hg_meas : ∀ j, Measurable (g j) := fun j =>
      ((((hrc_meas (ns j)).add_const _).min measurable_const).ennreal_ofReal).pow_const _
    have hfg : ∀ j, ∫⁻ ω, f j ω ∂P ≤
        ENNReal.ofReal C * (∫⁻ ω, g j ω ∂P + ENNReal.ofReal (b ^ p)) := by
      intro j
      refine (hDB' P (𝒢 (ns j)) (Z (ns j)) (2 ^ ns j) hb (hZ (ns j)).1 (hZ (ns j)).2.1
        (hZ (ns j)).2.2.1).trans ?_
      gcongr with ω
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ((hZ (ns j)).2.2.2.1 ω)) hq0.le
    have hbound_fin : ∫⁻ ω, ENNReal.ofReal (L + 2 * b ^ 2) ^ (p / 2) ∂P ≠ ∞ := by
      rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top
    set G : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (min (Q' ω + b ^ 2) (L + 2 * b ^ 2)) ^ (p / 2) with hG
    have hgG : Tendsto (fun j => ∫⁻ ω, g j ω ∂P) atTop (𝓝 (∫⁻ ω, G ω ∂P)) := by
      refine tendsto_lintegral_of_dominated_convergence
        (fun _ => ENNReal.ofReal (L + 2 * b ^ 2) ^ (p / 2)) hg_meas ?_ hbound_fin ?_
      · intro j
        refine Eventually.of_forall fun ω => ?_
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (min_le_right _ _)) hq0.le
      · filter_upwards [hae'] with ω hω
        have hcont' : Continuous fun x : ℝ =>
            ENNReal.ofReal (min (x + b ^ 2) (L + 2 * b ^ 2)) ^ (p / 2) :=
          ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp
            ((continuous_id.add continuous_const).min continuous_const))
        exact (hcont'.tendsto _).comp hω
    have hlow : ∀ᵐ ω ∂P, {ω | Q' ω < (L : ℝ)}.indicator (fun ω => ‖M T ω 0‖ₑ ^ p) ω ≤
        liminf (fun j => f j ω) atTop := by
      filter_upwards [hae'] with ω hω
      by_cases hlt : Q' ω < (L : ℝ)
      · rw [Set.indicator_of_mem (show ω ∈ {ω | Q' ω < (L : ℝ)} from hlt)]
        have h1 : ∀ᶠ j in atTop, LatticeProb.Process.realizedCovar M T (ns j) ω 0 0 ≤ L :=
          (hω.eventually (gt_mem_nhds hlt)).mono fun j hj => hj.le
        have hcontω : Continuous fun t => M t ω 0 := (continuous_apply 0).comp (hcont ω)
        have h2 : ∀ᶠ j in atTop, ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
            |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ (ns j) → |M s ω 0 - M t ω 0| < b :=
          hns.tendsto_atTop.eventually (eventually_modulus_lt hcontω T hb)
        have h3 : ∀ᶠ j in atTop, f j ω = ‖M T ω 0‖ₑ ^ p := by
          filter_upwards [h1, h2] with j hj1 hj2
          simp only [hf]
          rw [(hZ (ns j)).2.2.2.2 ω hj2 hj1, ← Real.enorm_eq_ofReal_abs]
        have h4 : Tendsto (fun j => f j ω) atTop (𝓝 (‖M T ω 0‖ₑ ^ p)) :=
          tendsto_const_nhds.congr' (h3.mono fun j hj => hj.symm)
        rw [h4.liminf_eq]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | Q' ω < (L : ℝ)} from hlt)]
        exact zero_le
    have hRlim : Tendsto
        (fun j => ENNReal.ofReal C * (∫⁻ ω, g j ω ∂P + ENNReal.ofReal (b ^ p))) atTop
        (𝓝 (ENNReal.ofReal C * (∫⁻ ω, G ω ∂P + ENNReal.ofReal (b ^ p)))) :=
      ENNReal.Tendsto.const_mul (hgG.add_const _) (Or.inr ENNReal.ofReal_ne_top)
    have hbp : ENNReal.ofReal (b ^ 2) ^ (p / 2) = ENNReal.ofReal (b ^ p) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1
      push_cast
      ring
    have hGle : ∫⁻ ω, G ω ∂P ≤ (2 : ℝ≥0∞) ^ (p / 2) *
        (∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P + ENNReal.ofReal (b ^ p)) := by
      calc ∫⁻ ω, G ω ∂P
          ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (p / 2) *
              (ENNReal.ofReal (Q' ω) ^ (p / 2) + ENNReal.ofReal (b ^ p)) ∂P := by
            refine lintegral_mono fun ω => ?_
            have h1 : ENNReal.ofReal (min (Q' ω + b ^ 2) (L + 2 * b ^ 2)) ≤
                ENNReal.ofReal (Q' ω) + ENNReal.ofReal (b ^ 2) :=
              (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans ENNReal.ofReal_add_le
            calc G ω ≤ (ENNReal.ofReal (Q' ω) + ENNReal.ofReal (b ^ 2)) ^ (p / 2) :=
                  ENNReal.rpow_le_rpow h1 hq0.le
              _ ≤ (2 : ℝ≥0∞) ^ (p / 2) *
                  (ENNReal.ofReal (Q' ω) ^ (p / 2) + ENNReal.ofReal (b ^ 2) ^ (p / 2)) :=
                  add_rpow_le_two_rpow_mul hq0.le _ _
              _ = _ := by rw [hbp]
        _ = (2 : ℝ≥0∞) ^ (p / 2) *
              (∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P + ENNReal.ofReal (b ^ p)) := by
            rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)),
              lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    calc ∫⁻ ω, {ω | Q' ω < (L : ℝ)}.indicator (fun ω => ‖M T ω 0‖ₑ ^ p) ω ∂P
        ≤ ∫⁻ ω, liminf (fun j => f j ω) atTop ∂P := lintegral_mono_ae hlow
      _ ≤ liminf (fun j => ∫⁻ ω, f j ω ∂P) atTop := lintegral_liminf_le hf_meas
      _ ≤ liminf (fun j => ENNReal.ofReal C *
            (∫⁻ ω, g j ω ∂P + ENNReal.ofReal (b ^ p))) atTop :=
          liminf_le_liminf (Eventually.of_forall hfg)
      _ = ENNReal.ofReal C * (∫⁻ ω, G ω ∂P + ENNReal.ofReal (b ^ p)) := hRlim.liminf_eq
      _ ≤ ENNReal.ofReal C * ((2 : ℝ≥0∞) ^ (p / 2) *
            (∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P + ENNReal.ofReal (b ^ p))
            + ENNReal.ofReal (b ^ p)) := by gcongr
      _ = _ := by ring
  have hb0 : Tendsto (fun b : ℝ => ENNReal.ofReal (b ^ p)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : ContinuousAt (fun b : ℝ => b ^ p) 0 :=
      Real.continuousAt_rpow_const 0 p (Or.inr hp0.le)
    have h2 : Tendsto (fun b : ℝ => b ^ p) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hp0.ne'] using h1.tendsto
    have h3 := ENNReal.tendsto_ofReal
      (h2.mono_left nhdsWithin_le_nhds : Tendsto (fun b : ℝ => b ^ p) (𝓝[>] 0) (𝓝 0))
    simpa using h3
  have key2 : ∀ L : ℕ,
      ∫⁻ ω, {ω | Q' ω < (L : ℝ)}.indicator (fun ω => ‖M T ω 0‖ₑ ^ p) ω ∂P ≤
        ENNReal.ofReal C * ((2 : ℝ≥0∞) ^ (p / 2) * ∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P) := by
    intro L
    have hlim : Tendsto (fun b : ℝ => ENNReal.ofReal C * ((2 : ℝ≥0∞) ^ (p / 2) *
        ∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P
          + ((2 : ℝ≥0∞) ^ (p / 2) + 1) * ENNReal.ofReal (b ^ p))) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal C * ((2 : ℝ≥0∞) ^ (p / 2) *
          ∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P + ((2 : ℝ≥0∞) ^ (p / 2) + 1) * 0))) := by
      refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
      refine Tendsto.const_add _ ?_
      exact ENNReal.Tendsto.const_mul hb0 (Or.inr (by simp))
    have := ge_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun b hb => key L b (Set.mem_Ioi.1 hb))
    simpa using this
  have hFm : Measurable fun ω => ‖M T ω 0‖ₑ ^ p := ((hMeas T).enorm).pow_const p
  have hsup : ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P =
      ⨆ L : ℕ, ∫⁻ ω, {ω | Q' ω < (L : ℝ)}.indicator (fun ω => ‖M T ω 0‖ₑ ^ p) ω ∂P := by
    rw [← lintegral_iSup]
    · congr 1
      funext ω
      refine le_antisymm ?_ (iSup_le fun L => Set.indicator_le_self _ _ ω)
      obtain ⟨L, hL⟩ := exists_nat_gt (Q' ω)
      refine le_iSup_of_le L ?_
      rw [Set.indicator_of_mem (show ω ∈ {ω | Q' ω < (L : ℝ)} from hL)]
    · intro L
      exact hFm.indicator (measurableSet_lt hQ'm measurable_const)
    · intro L L' hLL' ω
      have hsub : {ω | Q' ω < (L : ℝ)} ⊆ {ω | Q' ω < (L' : ℝ)} := by
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        exact lt_of_lt_of_le hω (Nat.cast_le.2 hLL')
      exact Set.indicator_le_indicator_of_subset (f := fun ω => ‖M T ω 0‖ₑ ^ p) hsub
        (fun a => zero_le) ω
  have hI : ∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hQQ'] with ω h
    have h' : Q ω 0 0 = Q' ω := h
    rw [h']
  calc ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P
      = ⨆ L : ℕ, ∫⁻ ω, {ω | Q' ω < (L : ℝ)}.indicator (fun ω => ‖M T ω 0‖ₑ ^ p) ω ∂P := hsup
    _ ≤ ENNReal.ofReal C * ((2 : ℝ≥0∞) ^ (p / 2) * ∫⁻ ω, ENNReal.ofReal (Q' ω) ^ (p / 2) ∂P) :=
        iSup_le key2
    _ = ENNReal.ofReal (C * 2 ^ (p / 2)) * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P := by
        rw [hI, ENNReal.ofReal_mul hC.le, ← mul_assoc,
          ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

/-! ### The implications -/

/-- `DiscreteBurkholderBoundedAt p` for every `p ≥ 2`, unconditionally. -/
theorem discreteBurkholderBoundedAt_ge_two {p : ℝ} (hp : 2 ≤ p) : DiscreteBurkholderBoundedAt p :=
  discreteBurkholderBoundedAt_of_ge_two predictableCompensatorLp_holds hp

/-- **The upper half for `p ≥ 2`** from the proved peeling bound and Garsia–Neveu comparison and
the stopped skeleton (`StoppedDyadicSkeleton`). -/
theorem bdgUpperAt_ge_two (hS : StoppedDyadicSkeleton) {p : ℝ} (hp : 2 ≤ p) : BdgUpperAt p :=
  bdgUpperAt_of_stopped (by linarith) (discreteBurkholderBoundedAt_ge_two hp) hS

/-- Concavity of `t ↦ t ^ θ`, `0 ≤ θ ≤ 1`, in the form
`θ (y - x) y^(θ-1) ≤ y^θ - x^θ` for `x, y > 0`. -/
lemma weight_diff_le {x y θ : ℝ} (hx : 0 < x) (hy : 0 < y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * ((y - x) * y ^ (θ - 1)) ≤ y ^ θ - x ^ θ := by
  have hs : -1 ≤ x / y - 1 := by
    have : 0 ≤ x / y := div_nonneg hx.le hy.le
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hθ0 hθ1
  have h1 : 1 + (x / y - 1) = x / y := by ring
  rw [h1, Real.div_rpow hx.le hy.le] at hb
  have hyθ : 0 < y ^ θ := Real.rpow_pos_of_pos hy _
  have h3 : x ^ θ ≤ y ^ θ * (1 + θ * (x / y - 1)) := by
    have := mul_le_mul_of_nonneg_left hb hyθ.le
    rwa [mul_div_cancel₀ _ hyθ.ne'] at this
  have h2 : y ^ θ = y ^ (θ - 1) * y := by
    rw [← Real.rpow_add_one hy.ne']
    congr 1
    ring
  have h4 : y ^ θ * (x / y - 1) = y ^ (θ - 1) * (x - y) := by
    rw [h2]
    field_simp
  have h5 : y ^ θ * (1 + θ * (x / y - 1)) = y ^ θ + θ * (y ^ (θ - 1) * (x - y)) := by
    rw [mul_add, mul_one, mul_left_comm, h4]
  nlinarith [h3, h5]

/-- A step of the weighted sum of squares: if `0 < x ≤ y ≤ 2 x` and `0 < θ ≤ 1`, then
`x^(θ-1) (y - x) ≤ (2^(1-θ) / θ) (y^θ - x^θ)`. -/
lemma weight_step_le {x y θ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy2 : y ≤ 2 * x) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    x ^ (θ - 1) * (y - x) ≤ 2 ^ (1 - θ) / θ * (y ^ θ - x ^ θ) := by
  have hy : 0 < y := hx.trans_le hxy
  have h1 : x ^ (θ - 1) ≤ 2 ^ (1 - θ) * y ^ (θ - 1) := by
    have h2 : y / 2 ≤ x := by linarith
    have h3 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < y / 2) h2
      (by linarith : θ - 1 ≤ 0)
    rw [Real.div_rpow hy.le (by norm_num)] at h3
    have h4 : (2 : ℝ) ^ (1 - θ) = ((2 : ℝ) ^ (θ - 1))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]
      congr 1
      ring
    rw [h4, mul_comm, ← div_eq_mul_inv]
    exact h3
  have hA := weight_diff_le hx hy hθ0.le hθ1
  calc x ^ (θ - 1) * (y - x) ≤ (2 ^ (1 - θ) * y ^ (θ - 1)) * (y - x) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = 2 ^ (1 - θ) / θ * (θ * ((y - x) * y ^ (θ - 1))) := by
        field_simp
    _ ≤ 2 ^ (1 - θ) / θ * (y ^ θ - x ^ θ) :=
        mul_le_mul_of_nonneg_left hA (by positivity)

/-- Summation of `weight_step_le` along a positive sequence whose steps at most double: the sum
`∑_{k<N} a_k^(θ-1) (a_{k+1} - a_k)` is at most `(2^(1-θ) / θ) (a_N^θ - a_0^θ)`. -/
lemma sum_weight_step_le {a : ℕ → ℝ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hpos : ∀ k, 0 < a k)
    (N : ℕ) (hmono : ∀ k, k < N → a k ≤ a (k + 1)) (hdbl : ∀ k, k < N → a (k + 1) ≤ 2 * a k) :
    ∑ k ∈ Finset.range N, a k ^ (θ - 1) * (a (k + 1) - a k) ≤
      2 ^ (1 - θ) / θ * (a N ^ θ - a 0 ^ θ) := by
  calc ∑ k ∈ Finset.range N, a k ^ (θ - 1) * (a (k + 1) - a k)
      ≤ ∑ k ∈ Finset.range N, 2 ^ (1 - θ) / θ * (a (k + 1) ^ θ - a k ^ θ) :=
        Finset.sum_le_sum fun k hk =>
          weight_step_le (hpos k) (hmono k (Finset.mem_range.mp hk))
            (hdbl k (Finset.mem_range.mp hk)) hθ0 hθ1
    _ = 2 ^ (1 - θ) / θ * ∑ k ∈ Finset.range N, (a (k + 1) ^ θ - a k ^ θ) :=
        (Finset.mul_sum _ _ _).symm
    _ = 2 ^ (1 - θ) / θ * (a N ^ θ - a 0 ^ θ) := by
        rw [Finset.sum_range_sub (fun k => a k ^ θ)]

/-- Young's inequality in the form used for the weighted square function: for `1 < p < 2` and
`a > 0`, `|t|^p ≤ (p/2) (t² a^(p/2 - 1)) + (1 - p/2) a^(p/2)`. -/
lemma abs_rpow_le_young {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (t : ℝ) {a : ℝ} (ha : 0 < a) :
    |t| ^ p ≤ p / 2 * (t ^ 2 * a ^ (p / 2 - 1)) + (1 - p / 2) * a ^ (p / 2) := by
  have hθ0 : 0 < p / 2 := by linarith
  have hθ1 : 0 ≤ 1 - p / 2 := by linarith
  have hA : 0 ≤ t ^ 2 * a ^ (p / 2 - 1) := mul_nonneg (sq_nonneg t) (Real.rpow_nonneg ha.le _)
  have hB : 0 ≤ a ^ (p / 2) := Real.rpow_nonneg ha.le _
  have key := Real.geom_mean_le_arith_mean2_weighted hθ0.le hθ1 hA hB (by ring)
  have h1 : (t ^ 2) ^ (p / 2) = |t| ^ p := by
    rw [← sq_abs t, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg t)]
    congr 1
    ring
  have e : (t ^ 2 * a ^ (p / 2 - 1)) ^ (p / 2) * (a ^ (p / 2)) ^ (1 - p / 2) = |t| ^ p := by
    rw [Real.mul_rpow (sq_nonneg t) (Real.rpow_nonneg ha.le _), h1,
      ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le, mul_assoc, ← Real.rpow_add ha]
    have : (p / 2 - 1) * (p / 2) + p / 2 * (1 - p / 2) = 0 := by ring
    rw [this, Real.rpow_zero, mul_one]
  rw [← e]
  exact key

/-- Pointwise telescoping with a nonincreasing weight: for a real sequence `z` with `z 0 = 0` and
`w (k+1) ≤ w k`, `z_n² w_n ≤ ∑_{k<n} (2 (w_k z_k) (z_{k+1} - z_k) + w_k (z_{k+1} - z_k)²)`. -/
lemma sq_mul_weight_le {z w : ℕ → ℝ} (hz0 : z 0 = 0) (hw : ∀ k, w (k + 1) ≤ w k) (n : ℕ) :
    z n ^ 2 * w n ≤ ∑ k ∈ Finset.range n,
      (2 * (w k * z k) * (z (k + 1) - z k) + w k * (z (k + 1) - z k) ^ 2) := by
  induction n with
  | zero => simp [hz0]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : z (n + 1) ^ 2 * w (n + 1) ≤ z (n + 1) ^ 2 * w n :=
      mul_le_mul_of_nonneg_left (hw n) (sq_nonneg _)
    have h2 : z (n + 1) ^ 2 * w n = z n ^ 2 * w n +
        (2 * (w n * z n) * (z (n + 1) - z n) + w n * (z (n + 1) - z n) ^ 2) := by ring
    linarith

/-- A discrete martingale from `0` with increments at most `b` on `i < N` satisfies
`|Z_k| ≤ k b` for `k ≤ N`. -/
lemma abs_le_mul_of_increments {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ}
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) (ω : Ω) :
    ∀ k, k ≤ N → |Z k ω| ≤ k * b := by
  intro k
  induction k with
  | zero => intro _; simp [hZ0]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hinc k (by omega) ω
    have h3 : |Z (k + 1) ω| ≤ |Z k ω| + |Z (k + 1) ω - Z k ω| := by
      calc |Z (k + 1) ω| = |Z k ω + (Z (k + 1) ω - Z k ω)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    push_cast
    linarith

/-- For a bounded `ℱ i`-measurable `g`, `g (X_{i+1} - X_i)` is integrable and has integral `0`. -/
lemma integral_mul_diff_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) (i : ℕ) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ i] g) {C : ℝ}
    (hgb : ∀ ω, |g ω| ≤ C) :
    Integrable (fun ω => g ω * (X (i + 1) ω - X i ω)) P ∧
      ∫ ω, g ω * (X (i + 1) ω - X i ω) ∂P = 0 := by
  have hdI : Integrable (fun ω => X (i + 1) ω - X i ω) P :=
    (hM.integrable (i + 1)).sub (hM.integrable i)
  have hIh : Integrable (fun ω => g ω * (X (i + 1) ω - X i ω)) P :=
    hdI.bdd_mul (hg.mono (ℱ.le i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgb ω)
  refine ⟨hIh, ?_⟩
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := ℱ i) hg
    (g := fun ω => X (i + 1) ω - X i ω) (by exact hIh) hdI
  have h2 := LatticeProb.Process.RandomizedFreedman.condExp_diff_ae_zero hM i
  calc ∫ ω, g ω * (X (i + 1) ω - X i ω) ∂P
      = ∫ ω, P[g * (fun ω => X (i + 1) ω - X i ω) | ℱ i] ω ∂P :=
        (integral_condExp (ℱ.le i)).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h1, h2] with ω e1 e2
        rw [e1]
        show g ω * P[fun ω => X (i + 1) ω - X i ω | ℱ i] ω = 0
        rw [e2]
        simp
    _ = 0 := integral_zero _ _

/-- **Weighted telescoping bound for `1 < p < 2`.**  Let `Z` be a discrete martingale from `0` with
increments at most `b` in absolute value on `i < N`, and let `S k = ∑_{i<k} (Z_{i+1} - Z_i)²`.
Then `E |Z_N|^p ≤ (2^(1-p/2) + (1 - p/2) + 1) (E (S N)^(p/2) + b^p)`.

The proof applies the weight `w_k = (S k + b²)^(p/2 - 1)` to the square `Z_k²`: the telescoping
sum `Z_N² w_N ≤ ∑ w_k (2 Z_k d_k + d_k²)` has centered cross terms, and the diagonal terms are
bounded by concavity of `t ↦ t^(p/2)`; Young's inequality with exponents `2/p` and `1/(1 - p/2)`
turns `E Z_N² w_N` into a bound for `E |Z_N|^p`. -/
theorem integral_abs_rpow_le_of_lt_two {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ)
    (S : ℕ → Ω → ℝ) (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {b : ℝ} (hb : 0 < b) (hM : Martingale Z 𝒢 P) (hZ0 : ∀ ω, Z 0 ω = 0)
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∫ ω, |Z N ω| ^ p ∂P ≤ (2 ^ (1 - p / 2) + (1 - p / 2) + 1) *
      (∫ ω, S N ω ^ (p / 2) ∂P + b ^ p) := by
  have hθ0 : 0 < p / 2 := by linarith
  have hθ1 : p / 2 < 1 := by linarith
  have hZm : ∀ j, Measurable (Z j) := fun j =>
    ((hM.stronglyMeasurable j).mono (𝒢.le j)).measurable
  have hS0 : ∀ k ω, 0 ≤ S k ω := fun k ω => by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSzero : ∀ ω, S 0 ω = 0 := fun ω => by rw [hS]; simp
  have hSsucc : ∀ k ω, S (k + 1) ω = S k ω + (Z (k + 1) ω - Z k ω) ^ 2 := fun k ω => by
    rw [hS, hS, Finset.sum_range_succ]
  have hd2 : ∀ k, k < N → ∀ ω, (Z (k + 1) ω - Z k ω) ^ 2 ≤ b ^ 2 := fun k hk ω =>
    sq_le_sq' (abs_le.mp (hinc k hk ω)).1 (abs_le.mp (hinc k hk ω)).2
  have hSle : ∀ ω, S N ω ≤ N * b ^ 2 := fun ω => by
    rw [hS]
    calc ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 ≤ ∑ i ∈ Finset.range N, b ^ 2 :=
          Finset.sum_le_sum fun i hi => hd2 i (Finset.mem_range.mp hi) ω
      _ = N * b ^ 2 := by simp
  have hSm : ∀ k, Measurable (S k) := by
    intro k
    have : S k = fun ω => ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2 := funext (hS k)
    rw [this]
    exact Finset.measurable_sum _ fun i _ => ((hZm (i + 1)).sub (hZm i)).pow_const 2
  have hSF : ∀ k, Measurable[𝒢 k] (S k) := by
    intro k
    have : S k = fun ω => ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2 := funext (hS k)
    rw [this]
    refine Finset.measurable_sum _ fun i hi => ?_
    have hi' : i + 1 ≤ k := Finset.mem_range.mp hi
    have h1 : Measurable[𝒢 k] (Z (i + 1)) :=
      ((hM.stronglyMeasurable (i + 1)).mono (𝒢.mono hi')).measurable
    have h2 : Measurable[𝒢 k] (Z i) :=
      ((hM.stronglyMeasurable i).mono (𝒢.mono (by omega))).measurable
    exact (h1.sub h2).pow_const 2
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Ω → ℝ, ∀ k ω, w k ω = (S k ω + b ^ 2) ^ (p / 2 - 1) :=
    ⟨fun k ω => (S k ω + b ^ 2) ^ (p / 2 - 1), fun _ _ => rfl⟩
  have hapos : ∀ k ω, 0 < S k ω + b ^ 2 := fun k ω => by
    have := hS0 k ω
    positivity
  have hwpos : ∀ k ω, 0 < w k ω := fun k ω => by
    rw [hw]
    exact Real.rpow_pos_of_pos (hapos k ω) _
  have hwle : ∀ k ω, w k ω ≤ (b ^ 2) ^ (p / 2 - 1) := fun k ω => by
    rw [hw]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hS0 k ω]) (by linarith)
  have hwanti : ∀ k ω, w (k + 1) ω ≤ w k ω := fun k ω => by
    rw [hw, hw]
    refine Real.rpow_le_rpow_of_nonpos (hapos k ω) ?_ (by linarith)
    rw [hSsucc]
    nlinarith [sq_nonneg (Z (k + 1) ω - Z k ω)]
  have hwm : ∀ k, Measurable (w k) := by
    intro k
    have : w k = fun ω => (S k ω + b ^ 2) ^ (p / 2 - 1) := funext (hw k)
    rw [this]
    exact ((hSm k).add_const _).pow_const _
  have hwF : ∀ k, Measurable[𝒢 k] (w k) := by
    intro k
    have : w k = fun ω => (S k ω + b ^ 2) ^ (p / 2 - 1) := funext (hw k)
    rw [this]
    exact ((hSF k).add_const _).pow_const _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 ^ (1 - p / 2) / (p / 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (Real.rpow_nonneg (by norm_num) _) hθ0.le
  have hθK : p / 2 * K = 2 ^ (1 - p / 2) := by
    rw [hK]
    field_simp
  have hb2p : (b ^ 2) ^ (p / 2) = b ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    congr 1
    ring
  -- the diagonal terms
  have hdiag : ∀ ω, ∑ k ∈ Finset.range N, w k ω * (Z (k + 1) ω - Z k ω) ^ 2 ≤
      K * S N ω ^ (p / 2) := by
    intro ω
    have hsum : ∑ k ∈ Finset.range N, (S k ω + b ^ 2) ^ (p / 2 - 1) *
          (S (k + 1) ω + b ^ 2 - (S k ω + b ^ 2)) ≤
        2 ^ (1 - p / 2) / (p / 2) * ((S N ω + b ^ 2) ^ (p / 2) - (S 0 ω + b ^ 2) ^ (p / 2)) :=
      sum_weight_step_le (a := fun k => S k ω + b ^ 2) hθ0 hθ1.le (fun k => hapos k ω) N
        (fun k hk => by
          show S k ω + b ^ 2 ≤ S (k + 1) ω + b ^ 2
          rw [hSsucc]
          linarith [sq_nonneg (Z (k + 1) ω - Z k ω)])
        (fun k hk => by
          show S (k + 1) ω + b ^ 2 ≤ 2 * (S k ω + b ^ 2)
          rw [hSsucc]
          linarith [hS0 k ω, hd2 k hk ω])
    calc ∑ k ∈ Finset.range N, w k ω * (Z (k + 1) ω - Z k ω) ^ 2
        = ∑ k ∈ Finset.range N, (S k ω + b ^ 2) ^ (p / 2 - 1) *
            (S (k + 1) ω + b ^ 2 - (S k ω + b ^ 2)) :=
          Finset.sum_congr rfl fun k _ => by rw [hw, hSsucc]; ring
      _ ≤ 2 ^ (1 - p / 2) / (p / 2) *
            ((S N ω + b ^ 2) ^ (p / 2) - (S 0 ω + b ^ 2) ^ (p / 2)) := hsum
      _ ≤ K * S N ω ^ (p / 2) := by
          rw [← hK]
          refine mul_le_mul_of_nonneg_left ?_ hK0
          rw [hSzero ω, zero_add]
          have h2 := Real.rpow_add_le_add_rpow (hS0 N ω) (sq_nonneg b) hθ0.le hθ1.le
          rw [hb2p] at h2
          linarith
  -- pointwise telescoping
  have htel : ∀ ω, Z N ω ^ 2 * w N ω ≤
      ∑ k ∈ Finset.range N, 2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω) +
        K * S N ω ^ (p / 2) := by
    intro ω
    have h : Z N ω ^ 2 * w N ω ≤ ∑ k ∈ Finset.range N,
        (2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω) + w k ω * (Z (k + 1) ω - Z k ω) ^ 2) :=
      sq_mul_weight_le (z := fun k => Z k ω) (w := fun k => w k ω) (hZ0 ω)
        (fun k => hwanti k ω) N
    rw [Finset.sum_add_distrib] at h
    linarith [hdiag ω]
  -- the cross terms
  have hTint : ∀ k, k < N →
      Integrable (fun ω => 2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω)) P ∧
        ∫ ω, 2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω) ∂P = 0 := by
    intro k hk
    have hZk : Measurable[𝒢 k] (Z k) := (hM.stronglyMeasurable k).measurable
    have hgF : StronglyMeasurable[𝒢 k] (fun ω => 2 * (w k ω * Z k ω)) :=
      (measurable_const.mul ((hwF k).mul hZk)).stronglyMeasurable
    have hgb : ∀ ω, |2 * (w k ω * Z k ω)| ≤ 2 * ((b ^ 2) ^ (p / 2 - 1) * (k * b)) := by
      intro ω
      have h1 := hwle k ω
      have h2 := abs_le_mul_of_increments hZ0 hinc ω k hk.le
      have h3 := hwpos k ω
      rw [abs_mul, abs_mul, abs_of_pos h3, abs_two]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)) (by norm_num)
    exact integral_mul_diff_eq_zero P 𝒢 Z hM k hgF hgb
  have hTsumInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range N, 2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω)) P :=
    integrable_finsetSum _ fun k hk => (hTint k (Finset.mem_range.mp hk)).1
  have hTsum0 : ∫ ω, ∑ k ∈ Finset.range N,
      2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω) ∂P = 0 := by
    rw [integral_finsetSum _ fun k hk => (hTint k (Finset.mem_range.mp hk)).1]
    exact Finset.sum_eq_zero fun k hk => (hTint k (Finset.mem_range.mp hk)).2
  have hSpowInt : Integrable (fun ω => S N ω ^ (p / 2)) P :=
    LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le (C := (N * b ^ 2) ^ (p / 2))
      ((hSm N).pow_const _) fun ω => by
        rw [abs_of_nonneg (Real.rpow_nonneg (hS0 N ω) _)]
        exact Real.rpow_le_rpow (hS0 N ω) (hSle ω) hθ0.le
  have hZNb : ∀ ω, Z N ω ^ 2 ≤ (N * b) ^ 2 := fun ω => by
    have := abs_le_mul_of_increments hZ0 hinc ω N le_rfl
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  have hQint : Integrable (fun ω => Z N ω ^ 2 * w N ω) P :=
    LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le (C := (N * b) ^ 2 * (b ^ 2) ^ (p / 2 - 1))
      (((hZm N).pow_const 2).mul (hwm N)) fun ω => by
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hwpos N ω).le)]
        exact mul_le_mul (hZNb ω) (hwle N ω) (hwpos N ω).le (sq_nonneg _)
  have hQle : ∫ ω, Z N ω ^ 2 * w N ω ∂P ≤ K * ∫ ω, S N ω ^ (p / 2) ∂P := by
    calc ∫ ω, Z N ω ^ 2 * w N ω ∂P
        ≤ ∫ ω, (∑ k ∈ Finset.range N, 2 * (w k ω * Z k ω) * (Z (k + 1) ω - Z k ω) +
            K * S N ω ^ (p / 2)) ∂P :=
          integral_mono hQint (hTsumInt.add (hSpowInt.const_mul K)) fun ω => htel ω
      _ = 0 + K * ∫ ω, S N ω ^ (p / 2) ∂P := by
          rw [integral_add hTsumInt (hSpowInt.const_mul K), hTsum0, integral_const_mul]
      _ = K * ∫ ω, S N ω ^ (p / 2) ∂P := zero_add _
  -- Young's inequality, pointwise
  have hyoung : ∀ ω, |Z N ω| ^ p ≤
      p / 2 * (Z N ω ^ 2 * w N ω) + (1 - p / 2) * (S N ω ^ (p / 2) + b ^ p) := by
    intro ω
    have h1 := abs_rpow_le_young hp1 hp2 (Z N ω) (hapos N ω)
    rw [← hw] at h1
    have h2 : (S N ω + b ^ 2) ^ (p / 2) ≤ S N ω ^ (p / 2) + b ^ p := by
      have := Real.rpow_add_le_add_rpow (hS0 N ω) (sq_nonneg b) hθ0.le hθ1.le
      rwa [hb2p] at this
    have h3 : 0 ≤ 1 - p / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hAbsInt : Integrable (fun ω => |Z N ω| ^ p) P :=
    LatticeProb.Process.RandomizedFreedman.integrable_of_abs_le (C := (N * b) ^ p)
      ((hZm N).abs.pow_const p) fun ω => by
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _)
          (abs_le_mul_of_increments hZ0 hinc ω N le_rfl) (by linarith)
  have hJ0 : 0 ≤ ∫ ω, S N ω ^ (p / 2) ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (hS0 N ω) _
  have hB0 : 0 ≤ b ^ p := Real.rpow_nonneg hb.le _
  have h2r : 0 ≤ (2 : ℝ) ^ (1 - p / 2) := Real.rpow_nonneg (by norm_num) _
  have hRint : Integrable (fun ω => S N ω ^ (p / 2) + b ^ p) P :=
    hSpowInt.add (integrable_const _)
  calc ∫ ω, |Z N ω| ^ p ∂P
      ≤ ∫ ω, (p / 2 * (Z N ω ^ 2 * w N ω) + (1 - p / 2) * (S N ω ^ (p / 2) + b ^ p)) ∂P :=
        integral_mono hAbsInt ((hQint.const_mul _).add (hRint.const_mul _)) hyoung
    _ = p / 2 * ∫ ω, Z N ω ^ 2 * w N ω ∂P +
          (1 - p / 2) * (∫ ω, S N ω ^ (p / 2) ∂P + b ^ p) := by
        rw [integral_add (hQint.const_mul _) (hRint.const_mul _), integral_const_mul,
          integral_const_mul, integral_add hSpowInt (integrable_const _)]
        simp
    _ ≤ p / 2 * (K * ∫ ω, S N ω ^ (p / 2) ∂P) +
          (1 - p / 2) * (∫ ω, S N ω ^ (p / 2) ∂P + b ^ p) := by
        have := mul_le_mul_of_nonneg_left hQle hθ0.le
        linarith
    _ = 2 ^ (1 - p / 2) * ∫ ω, S N ω ^ (p / 2) ∂P +
          (1 - p / 2) * (∫ ω, S N ω ^ (p / 2) ∂P + b ^ p) := by
        rw [← mul_assoc, hθK]
    _ ≤ (2 ^ (1 - p / 2) + (1 - p / 2) + 1) * (∫ ω, S N ω ^ (p / 2) ∂P + b ^ p) := by
        nlinarith [mul_nonneg h2r hB0, hJ0, hB0]

/-- **The discrete Burkholder bound with a bounded-increment term holds for `1 < p < 2`.**  The
constant is `2^(1 - p/2) + (1 - p/2) + 1`; the proof is the weighted telescoping bound
`integral_abs_rpow_le_of_lt_two`, with the real integrals converted to `ℝ≥0∞`-valued integrals
of nonnegative bounded functions by `lintegral_ofReal_rpow_eq`. -/
theorem discreteBurkholderBoundedAt_lt_two_holds {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    DiscreteBurkholderBoundedAt p := by
  have hr : 0 < 1 - p / 2 := by linarith
  have h2r : 0 < (2 : ℝ) ^ (1 - p / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < (2 : ℝ) ^ (1 - p / 2) + (1 - p / 2) + 1 := by linarith
  refine ⟨2 ^ (1 - p / 2) + (1 - p / 2) + 1, hC, ?_⟩
  intro Ω _ P _ 𝒢 Z N b hb hM hZ0 hinc
  have hZm : ∀ j, Measurable (Z j) := fun j =>
    ((hM.stronglyMeasurable j).mono (𝒢.le j)).measurable
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → ℝ, ∀ k ω,
      S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2 :=
    ⟨fun k ω => ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2, fun _ _ => rfl⟩
  have hS0 : ∀ ω, 0 ≤ S N ω := fun ω => by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSle : ∀ ω, S N ω ≤ N * b ^ 2 := fun ω => by
    rw [hS]
    calc ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 ≤ ∑ i ∈ Finset.range N, b ^ 2 :=
          Finset.sum_le_sum fun i hi =>
            sq_le_sq' (abs_le.mp (hinc i (Finset.mem_range.mp hi) ω)).1
              (abs_le.mp (hinc i (Finset.mem_range.mp hi) ω)).2
      _ = N * b ^ 2 := by simp
  have hSm : Measurable (S N) := by
    have : S N = fun ω => ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 := funext (hS N)
    rw [this]
    exact Finset.measurable_sum _ fun i _ => ((hZm (i + 1)).sub (hZm i)).pow_const 2
  have hcore := integral_abs_rpow_le_of_lt_two P 𝒢 Z N S hS hb hM hZ0 hinc hp1 hp2
  have hp0 : 0 ≤ p := by linarith
  have hlhs : ∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P = ENNReal.ofReal (∫ ω, |Z N ω| ^ p ∂P) :=
    lintegral_ofReal_rpow_eq (P := P) (f := fun ω => |Z N ω|) (hZm N).abs (fun ω => abs_nonneg _)
      (C := N * b) (fun ω => abs_le_mul_of_increments hZ0 hinc ω N le_rfl) hp0
  have hrhs : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
      = ENNReal.ofReal (∫ ω, S N ω ^ (p / 2) ∂P) := by
    have h := lintegral_ofReal_rpow_eq (P := P) (f := S N) hSm hS0 (C := N * b ^ 2) hSle
      (q := p / 2) (by linarith)
    simpa only [hS] using h
  have hJ0 : 0 ≤ ∫ ω, S N ω ^ (p / 2) ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (hS0 ω) _
  have hB0 : 0 ≤ b ^ p := Real.rpow_nonneg hb.le _
  rw [hlhs, hrhs, ← ENNReal.ofReal_add hJ0 hB0, ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal hcore

/-- The upper half of the Burkholder–Davis–Gundy statement at an exponent `1 < p < 2` follows from
`StoppedDyadicSkeleton` alone. -/
theorem bdgUpperAt_lt_two_of_skeleton (hS : StoppedDyadicSkeleton) {p : ℝ} (hp1 : 1 < p)
    (hp2 : p < 2) : BdgUpperAt p :=
  bdgUpperAt_of_stopped hp1 (discreteBurkholderBoundedAt_lt_two_holds hp1 hp2) hS

/-- **The upper half of the Burkholder–Davis–Gundy statement from `StoppedDyadicSkeleton`.**  For
`p ≥ 2` this is `bdgUpperAt_ge_two`; for `1 < p < 2` it is `bdgUpperAt_lt_two_of_skeleton`. -/
theorem bdgUpper_of_skeleton (hS : StoppedDyadicSkeleton) : BurkholderDavisGundyUpper := by
  intro p hp
  by_cases h2 : 2 ≤ p
  · exact bdgUpperAt_ge_two hS h2
  · exact bdgUpperAt_lt_two_of_skeleton hS hp (lt_of_not_ge h2)

end

end LatticeProb.Process.BdgUpperContinuous


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The stopped dyadic skeleton: shared definitions and the four component statements

The continuous-time step `StoppedDyadicSkeleton` of the upper Burkholder–Davis–Gundy bound is split
into four independent statements about the objects defined here:

* `CountableRangeStoppedIntegral`: optional stopping for stopping times with countably many values;
* `ContinuousStoppedMartingale`: a continuous martingale stopped at any stopping time is a
  martingale (dyadic approximation of the stopping time from above, uniform integrability of
  conditional expectations, Vitali);
* `SkeletonStopIsStoppingTime`: the localising time `skelStop` read along the paths of a continuous
  adapted process is a stopping time;
* `SkeletonPathFacts`: the deterministic path bookkeeping of the stopped skeleton `skelVal`.
-/

namespace LatticeProb.Process.StoppedSkeleton

noncomputable section

/-- The dyadic grid time `t_k = T k / 2^n`, written exactly as in `LatticeProb.Process.realizedCovar`. -/
def gridT (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := T * ((k : ℕ) / 2 ^ n : ℝ≥0)

/-- The running sum of squared grid increments `∑_{i<k} (f t_{i+1} - f t_i)²` of a path. -/
def gridSq (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (f (gridT T n (i + 1)) - f (gridT T n i)) ^ 2

open Classical in
/-- The first time in the grid interval `[t_k, t_{k+1}]` at which the path is at distance at least
`b` from its value at `t_k`, or `⊤` if there is none. -/
def oscHit (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b : ℝ) (k : ℕ) : WithTop ℝ≥0 :=
  if ∃ s : ℝ≥0, gridT T n k ≤ s ∧ s ≤ gridT T n (k + 1) ∧ b ≤ |f s - f (gridT T n k)| then
    ((sInf {s : ℝ≥0 | gridT T n k ≤ s ∧ s ≤ gridT T n (k + 1) ∧
      b ≤ |f s - f (gridT T n k)|} : ℝ≥0) : WithTop ℝ≥0)
  else ⊤

/-- The oscillation stop: the first oscillation hit over the `2^n` grid intervals. -/
def oscStop (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b : ℝ) : WithTop ℝ≥0 :=
  (Finset.range (2 ^ n)).inf (oscHit f T n b)

open Classical in
/-- The grid stop: the first grid time `t_k`, `k ≤ 2^n`, at which the running sum of squared grid
increments exceeds `L`, or `⊤` if there is none. -/
def gridStop (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (L : ℝ) : WithTop ℝ≥0 :=
  (Finset.range (2 ^ n + 1)).inf fun k =>
    if L < gridSq f T n k then ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) else ⊤

/-- The localising time of the skeleton: the earlier of the oscillation stop and the grid stop. -/
def skelStop (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) : WithTop ℝ≥0 :=
  min (oscStop f T n b) (gridStop f T n L)

/-- The stopped skeleton at the grid index `k` (capped at `2^n`): the path at the time
`min t_{min k 2^n} (skelStop f)`. Written in the form of `MeasureTheory.stoppedProcess`, so that
`skelVal (fun t => X t ω) T n b L k = stoppedProcess X τ (gridT T n (min k (2 ^ n))) ω` by `rfl`
for `τ ω = skelStop (fun t => X t ω) T n b L`. -/
def skelVal (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) (k : ℕ) : ℝ :=
  f (min ((gridT T n (min k (2 ^ n)) : ℝ≥0) : WithTop ℝ≥0) (skelStop f T n b L)).untopA

/-- **Optional stopping at a stopping time with countably many values.** For a real martingale `X`
indexed by `ℝ≥0` and a stopping time `σ` with countable range, the stopped process has equal set
integrals at the times `s ≤ t` over every event of `ℱ s`. -/
def CountableRangeStoppedIntegral : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ) (σ : Ω → WithTop ℝ≥0),
    Martingale X ℱ P → IsStoppingTime ℱ σ → (Set.range σ).Countable →
    ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∫ ω in A, stoppedProcess X σ t ω ∂P = ∫ ω in A, stoppedProcess X σ s ω ∂P

/-- **A continuous martingale stopped at a stopping time is a martingale.** -/
def ContinuousStoppedMartingale : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0),
    Martingale X ℱ P → (∀ ω, Continuous fun t => X t ω) → IsStoppingTime ℱ τ →
      Martingale (stoppedProcess X τ) ℱ P

/-- **The localising time is a stopping time** for every continuous strongly adapted real
process. -/
def SkeletonStopIsStoppingTime : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ),
    StronglyAdapted ℱ X → (∀ ω, Continuous fun t => X t ω) →
    ∀ (T : ℝ≥0) (n : ℕ) (b L : ℝ),
      IsStoppingTime ℱ fun ω => skelStop (fun t => X t ω) T n b L

/-- **The path bookkeeping of the stopped skeleton.** For a continuous path `f`, `b > 0` and
`L ≥ 0`: the skeleton starts at `f 0`; each of its first `2^n` increments is at most `b`; the sum of
their squares is at most `min (gridSq f T n (2^n) + b²) (L + 2 b²)`; and if the path oscillates by
less than `b` over every pair of times in `[0, T]` at distance at most `T / 2^n` and the full sum of
squared grid increments is at most `L`, then the skeleton ends at `f T`. -/
def SkeletonPathFacts : Prop :=
  ∀ (f : ℝ≥0 → ℝ), Continuous f → ∀ (T : ℝ≥0) (n : ℕ) {b L : ℝ}, 0 < b → 0 ≤ L →
    skelVal f T n b L 0 = f 0 ∧
    (∀ i, i < 2 ^ n → |skelVal f T n b L (i + 1) - skelVal f T n b L i| ≤ b) ∧
    (∑ i ∈ Finset.range (2 ^ n), (skelVal f T n b L (i + 1) - skelVal f T n b L i) ^ 2 ≤
      min (gridSq f T n (2 ^ n) + b ^ 2) (L + 2 * b ^ 2)) ∧
    ((∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n → |f s - f t| < b) →
      gridSq f T n (2 ^ n) ≤ L → skelVal f T n b L (2 ^ n) = f T)

/-- The stopped-process form of `skelVal`, by definition. -/
theorem skelVal_eq_stoppedProcess {Ω : Type} (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ)
    (k : ℕ) (ω : Ω) :
    skelVal (fun t => X t ω) T n b L k =
      stoppedProcess X (fun ω => skelStop (fun t => X t ω) T n b L) (gridT T n (min k (2 ^ n)))
        ω :=
  rfl

/-- `realizedCovar` in the `(0, 0)` coordinate is the full sum of squared grid increments. -/
theorem realizedCovar_eq_gridSq {Ω : Type} (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0) (n : ℕ)
    (ω : Ω) : LatticeProb.Process.realizedCovar M T n ω 0 0 = gridSq (fun t => M t ω 0) T n (2 ^ n) := by
  simp only [LatticeProb.Process.realizedCovar, gridSq, gridT, sq]

end

end LatticeProb.Process.StoppedSkeleton

namespace LatticeProb.Process.StoppedSkeleton.CountableOST

noncomputable section

section CountableOST

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {σ : Ω → WithTop ℝ≥0} {X : ℝ≥0 → Ω → ℝ}

/-- Capping a stopping time at the constant time `t` keeps it a stopping time. -/
theorem isStoppingTime_capAt (hσ : IsStoppingTime ℱ σ) (t : ℝ≥0) :
    IsStoppingTime ℱ fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω) :=
  (isStoppingTime_const ℱ t).min hσ

omit [MeasurableSpace Ω] in
/-- Capping a stopping time with countable range at a constant time keeps the range countable. -/
theorem countable_range_capAt (hσc : (Set.range σ).Countable) (t : ℝ≥0) :
    (Set.range fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω)).Countable :=
  (hσc.image fun x => min ((t : ℝ≥0) : WithTop ℝ≥0) x).mono (by
    rintro _ ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩)

omit [MeasurableSpace Ω] in
/-- The capped stopping time is bounded by the cap. -/
theorem capAt_le (σ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω) ≤ ((t : ℝ≥0) : WithTop ℝ≥0) :=
  min_le_left _ _

omit [MeasurableSpace Ω] in
/-- The capped stopping times are monotone in the cap. -/
theorem capAt_mono (σ : Ω → WithTop ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    min ((s : ℝ≥0) : WithTop ℝ≥0) (σ ω) ≤ min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω) :=
  min_le_min (WithTop.coe_le_coe.2 hst) le_rfl

/-- A martingale evaluated at a countable-range stopping time capped at `t` is the conditional
expectation of the value at time `t` given the stopping-time σ-algebra. -/
theorem stoppedValue_capAt_ae_eq_condExp (hX : Martingale X ℱ P) (hσ : IsStoppingTime ℱ σ)
    (hσc : (Set.range σ).Countable) (t : ℝ≥0) :
    stoppedValue X (fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω)) =ᵐ[P]
      P[X t | (isStoppingTime_capAt hσ t).measurableSpace] :=
  hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (isStoppingTime_capAt hσ t)
    (capAt_le σ t) (countable_range_capAt hσc t)

/-- A martingale evaluated at a countable-range stopping time capped at `t` is integrable. -/
theorem integrable_stoppedValue_capAt (hX : Martingale X ℱ P) (hσ : IsStoppingTime ℱ σ)
    (hσc : (Set.range σ).Countable) (t : ℝ≥0) :
    Integrable (stoppedValue X fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω)) P := by
  have h : Integrable (P[X t | (isStoppingTime_capAt hσ t).measurableSpace]) P :=
    integrable_condExp
  exact h.congr (stoppedValue_capAt_ae_eq_condExp hX hσ hσc t).symm

/-- Optional sampling between the two capped stopping times. -/
theorem stoppedValue_capAt_ae_eq_condExp_capAt (hX : Martingale X ℱ P) (hσ : IsStoppingTime ℱ σ)
    (hσc : (Set.range σ).Countable) {s t : ℝ≥0} (hst : s ≤ t) :
    stoppedValue X (fun ω => min ((s : ℝ≥0) : WithTop ℝ≥0) (σ ω)) =ᵐ[P]
      P[stoppedValue X (fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω)) |
        (isStoppingTime_capAt hσ s).measurableSpace] :=
  hX.stoppedValue_ae_eq_condExp_of_le_of_countable_range (isStoppingTime_capAt hσ t)
    (isStoppingTime_capAt hσ s) (capAt_mono σ hst) (capAt_le σ t) (countable_range_capAt hσc t)
    (countable_range_capAt hσc s)

/-- The event `{s < σ}` intersected with an event of `ℱ s` lies in the σ-algebra of the capped
stopping time at `s`. -/
theorem measurableSet_capAt_inter_gt (hσ : IsStoppingTime ℱ σ) (s : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    MeasurableSet[(isStoppingTime_capAt hσ s).measurableSpace]
      (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) := by
  have hB : MeasurableSet[ℱ s] (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) :=
    hA.inter (hσ.measurableSet_gt s)
  refine ⟨(le_iSup (fun t => ℱ t) s) _ hB, fun i => ?_⟩
  rcases le_or_gt s i with hsi | his
  · exact (ℱ.mono hsi _ hB).inter (isStoppingTime_capAt hσ s i)
  · have hempty : (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) ∩
        {ω | min ((s : ℝ≥0) : WithTop ℝ≥0) (σ ω) ≤ ((i : ℝ≥0) : WithTop ℝ≥0)} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro ω ⟨⟨_, hlt⟩, hle⟩
      have hlt' : ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω := hlt
      have hle' : min ((s : ℝ≥0) : WithTop ℝ≥0) (σ ω) ≤ ((i : ℝ≥0) : WithTop ℝ≥0) := hle
      rw [min_eq_left hlt'.le] at hle'
      exact absurd (WithTop.coe_le_coe.1 hle') (not_le.2 his)
    rw [hempty]
    exact @MeasurableSet.empty _ (ℱ i)

/-- On the event `{s < σ}` of `ℱ s`, the set integrals of the stopped values at `s` and `t`
agree. -/
theorem setIntegral_capAt_gt (hX : Martingale X ℱ P) (hσ : IsStoppingTime ℱ σ)
    (hσc : (Set.range σ).Countable) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω},
        stoppedValue X (fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω)) ω ∂P =
      ∫ ω in A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω},
        stoppedValue X (fun ω => min ((s : ℝ≥0) : WithTop ℝ≥0) (σ ω)) ω ∂P := by
  have hB := measurableSet_capAt_inter_gt hσ s hA
  have hBamb : MeasurableSet (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) :=
    (isStoppingTime_capAt hσ s).measurableSpace_le _ hB
  have hint := integrable_stoppedValue_capAt hX hσ hσc t
  rw [setIntegral_congr_ae hBamb
    ((stoppedValue_capAt_ae_eq_condExp_capAt hX hσ hσc hst).mono fun x hx _ => hx)]
  exact (setIntegral_condExp ((isStoppingTime_capAt hσ s).measurableSpace_le_of_le
    (capAt_le σ s)) hint hB).symm

/-- **Optional stopping at a stopping time with countably many values.** -/
theorem countableRangeStoppedIntegral_holds : CountableRangeStoppedIntegral := by
  intro Ω _ P _ ℱ X σ hX hσ hσc s t hst A hA
  simp only [stoppedProcess_eq_stoppedValue_apply]
  have hBamb : MeasurableSet (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) :=
    ℱ.le s _ (hA.inter (hσ.measurableSet_gt s))
  have hCamb : MeasurableSet (A ∩ {ω | σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0)}) :=
    ℱ.le s _ (hA.inter (hσ.measurableSet_le s))
  have hsplit : A = (A ∩ {ω | σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0)}) ∪
      (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) := by
    ext ω
    constructor
    · intro h
      rcases le_or_gt (σ ω) ((s : ℝ≥0) : WithTop ℝ≥0) with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint (A ∩ {ω | σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0)})
      (A ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    have h1' : σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0) := h1
    have h2' : ((s : ℝ≥0) : WithTop ℝ≥0) < σ ω := h2
    exact (not_le.2 h2') h1'
  have hit := integrable_stoppedValue_capAt hX hσ hσc t
  have his := integrable_stoppedValue_capAt hX hσ hσc s
  have hC : ∫ ω in A ∩ {ω | σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0)},
        stoppedValue X (fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (σ ω)) ω ∂P =
      ∫ ω in A ∩ {ω | σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0)},
        stoppedValue X (fun ω => min ((s : ℝ≥0) : WithTop ℝ≥0) (σ ω)) ω ∂P := by
    refine setIntegral_congr_fun hCamb fun ω hω => ?_
    have h1 : σ ω ≤ ((s : ℝ≥0) : WithTop ℝ≥0) := hω.2
    have h2 : σ ω ≤ ((t : ℝ≥0) : WithTop ℝ≥0) := h1.trans (WithTop.coe_le_coe.2 hst)
    simp only [stoppedValue, min_eq_right h1, min_eq_right h2]
  conv_lhs => rw [hsplit]
  conv_rhs => rw [hsplit]
  rw [setIntegral_union hdisj hBamb hit.integrableOn hit.integrableOn,
    setIntegral_union hdisj hBamb his.integrableOn his.integrableOn, hC,
    setIntegral_capAt_gt hX hσ hσc hst hA]

end CountableOST

end

end LatticeProb.Process.StoppedSkeleton.CountableOST
