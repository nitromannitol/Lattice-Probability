/-
Freedman's inequality for a discrete martingale with bounded increments.

For a real martingale `M` with `M 0 = 0`, increments bounded by `b`, and predictable
quadratic variation `V n = ∑_{i<n} E[(M_{i+1} - M_i)^2 | F_i]` at most `v`,

    P(M n ≥ r) ≤ exp( -r^2 / (2 (v + b r / 3)) ) .

Azuma's inequality, which Mathlib has, replaces `v` by `n b^2` and is too weak when the
quadratic variation is much smaller than the worst case.

The proof is the exponential supermartingale: the conditional moment generating function of
a centred increment bounded by `b` satisfies
`E[e^{λ X} | F] ≤ exp(λ^2 E[X^2|F] / (2(1 - λ b/3)))`, so with
`c = λ^2 / (2(1 - λ b / 3))` the process `exp(λ M_k - c V_k)` has integral at most `1` at
every time; on `{M n ≥ r}` it is at least `exp(λ r - c v)`, and `λ = r / (v + b r / 3)`
optimizes the resulting bound.  The pointwise inequality behind the conditional moment
generating function bound is the one used for Bernstein's inequality for independent
summands.
-/
import Mathlib
import LatticeProb.Prob.Bernstein

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **The conditional Bernstein bound on the moment generating function.**  A centred
increment bounded by `b` has `E[e^{λ X} | m] ≤ exp(λ² E[X²|m] / (2(1 - λb/3)))`. -/
theorem condExp_one_add_linear_quadratic {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [IsFiniteMeasure P] {X : Ω → ℝ} (hXint : Integrable X P)
    (hX2int : Integrable (fun ω => X ω ^ 2) P) (hmean : P[X | m] =ᵐ[P] 0) (lam C : ℝ) :
    P[fun ω => 1 + (lam * X ω + C * X ω ^ 2) | m]
      =ᵐ[P] fun ω => 1 + C * (P[fun ω => X ω ^ 2 | m]) ω := by
  have h1 : P[fun ω => 1 + (lam * X ω + C * X ω ^ 2) | m]
      =ᵐ[P] P[(fun _ => (1 : ℝ)) | m] + P[fun ω => lam * X ω + C * X ω ^ 2 | m] :=
    condExp_add (integrable_const (1 : ℝ)) ((hXint.const_mul lam).add (hX2int.const_mul C)) m
  have h2 : P[fun ω => lam * X ω + C * X ω ^ 2 | m]
      =ᵐ[P] P[fun ω => lam * X ω | m] + P[fun ω => C * X ω ^ 2 | m] :=
    condExp_add (hXint.const_mul lam) (hX2int.const_mul C) m
  have h3 : P[fun ω => lam * X ω | m] =ᵐ[P] fun _ => (0 : ℝ) := by
    have hs := condExp_smul (μ := P) (𝕜 := ℝ) lam X m
    filter_upwards [hs, hmean] with ω hω hω2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hω hω2 ⊢
    show P[lam • X | m] ω = 0
    rw [hω, hω2, mul_zero]
  have h4 : P[fun ω => C * X ω ^ 2 | m] =ᵐ[P] fun ω => C * (P[fun ω => X ω ^ 2 | m]) ω := by
    have hs := condExp_smul (μ := P) (𝕜 := ℝ) C (fun ω => X ω ^ 2) m
    filter_upwards [hs] with ω hω
    show P[C • fun ω => X ω ^ 2 | m] ω = _
    simpa using hω
  filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
  simp only [Pi.add_apply] at e1 e2 ⊢
  rw [e1, condExp_const hm (1 : ℝ), e2, e3, e4]
  ring

/-- **The conditional Bernstein bound on the moment generating function.**  A centred
increment bounded by `b` has `E[e^{λ X} | m] ≤ exp(λ² E[X²|m] / (2(1 - λb/3)))`. -/
theorem condExp_exp_le {m : MeasurableSpace Ω} (hm : m ≤ m0) [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable[m0] X) {b : ℝ} (hb : ∀ ω, |X ω| ≤ b)
    (hmean : P[X | m] =ᵐ[P] 0) {lam : ℝ} (hlam : 0 < lam) (hlb : lam * b < 3) :
    P[fun ω => Real.exp (lam * X ω) | m]
      ≤ᵐ[P] fun ω =>
        Real.exp (lam ^ 2 / (2 * (1 - lam * b / 3)) * (P[fun ω => X ω ^ 2 | m]) ω) := by
  set θ : ℝ := lam * b / 3 with hθdef
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθpos : (0 : ℝ) < 1 - θ := by linarith
  set C : ℝ := lam ^ 2 / (2 * (1 - θ)) with hCdef
  have hXint : Integrable X P := by
    refine Integrable.mono' (integrable_const b) hX.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hb ω
  have hX2int : Integrable (fun ω => X ω ^ 2) P := by
    refine Integrable.mono' (integrable_const (b ^ 2)) (hX.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb ω, abs_nonneg (X ω), sq_abs (X ω)]
  have hexpmeas : Measurable[m0] fun ω => Real.exp (lam * X ω) :=
    Real.measurable_exp.comp (hX.const_mul lam)
  have hexpint : Integrable (fun ω => Real.exp (lam * X ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * b)))
      hexpmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [(abs_le.mp (hb ω)).2, hlam]
  have hrhsint : Integrable (fun ω => 1 + (lam * X ω + C * X ω ^ 2)) P :=
    (integrable_const (1 : ℝ)).add ((hXint.const_mul lam).add (hX2int.const_mul C))
  have hpt : ∀ ω, Real.exp (lam * X ω) ≤ 1 + (lam * X ω + C * X ω ^ 2) := by
    intro ω
    have hu : |lam * X ω| ≤ 3 * θ := by
      rw [abs_mul, abs_of_pos hlam, hθdef]
      nlinarith [hb ω, abs_nonneg (X ω)]
    have h := exp_le_one_add_add_sq_div θ (lam * X ω) hθ1 hu
    have heq : 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - θ))
        = 1 + (lam * X ω + C * X ω ^ 2) := by
      rw [hCdef]; ring
    linarith [h, heq.le, heq.ge]
  have h1 := condExp_mono (m := m) hexpint hrhsint (Filter.Eventually.of_forall hpt)
  have h2 := condExp_one_add_linear_quadratic hm hXint hX2int hmean lam C
  filter_upwards [h1, h2] with ω e1 e2
  have e3 : (1 : ℝ) + C * (P[fun ω => X ω ^ 2 | m]) ω
      ≤ Real.exp (C * (P[fun ω => X ω ^ 2 | m]) ω) := by
    linarith [Real.add_one_le_exp (C * (P[fun ω => X ω ^ 2 | m]) ω)]
  calc P[fun ω => Real.exp (lam * X ω) | m] ω
      ≤ P[fun ω => 1 + (lam * X ω + C * X ω ^ 2) | m] ω := e1
    _ = 1 + C * (P[fun ω => X ω ^ 2 | m]) ω := e2
    _ ≤ Real.exp (C * (P[fun ω => X ω ^ 2 | m]) ω) := e3


/-- The predictable quadratic variation `V k = ∑_{i<k} E[(M_{i+1} - M_i)^2 | F_i]`. -/
noncomputable def condQvar (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, (P[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | ℱ i]) ω

theorem condQvar_succ (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    condQvar P ℱ M (k + 1) ω
      = condQvar P ℱ M k ω + (P[fun ω' => (M (k + 1) ω' - M k ω') ^ 2 | ℱ k]) ω :=
  Finset.sum_range_succ _ k

theorem condQvar_nonneg (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) :
    0 ≤ᵐ[P] condQvar P ℱ M k := by
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ, 0 ≤ (P[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | ℱ i]) ω := by
    refine ae_all_iff.mpr fun i => ?_
    have h := condExp_nonneg (μ := P) (m := ℱ i)
      (f := fun ω' => (M (i + 1) ω' - M i ω') ^ 2)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    filter_upwards [h] with ω hω
    simpa using hω
  filter_upwards [hall] with ω hω
  exact Finset.sum_nonneg fun i _ => hω i

theorem measurable_condQvar (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) :
    Measurable[m0] (condQvar P ℱ M k) :=
  Finset.measurable_sum _ fun i _ =>
    ((stronglyMeasurable_condExp (m := ℱ i)).mono (ℱ.le i)).measurable

theorem stronglyMeasurable_condQvar (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (k j : ℕ) (hkj : k ≤ j + 1) : StronglyMeasurable[ℱ j] (condQvar P ℱ M k) := by
  refine Measurable.stronglyMeasurable (Finset.measurable_sum (m := ℱ j) _ fun i hi => ?_)
  exact ((stronglyMeasurable_condExp (m := ℱ i)).mono
    (ℱ.mono (Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hi) hkj)))).measurable


/-- Increments bounded by `b` from a start at `0` bound `|M j|` by `j b`. -/
theorem abs_le_of_increments {M : ℕ → Ω → ℝ} (hM0 : ∀ ω, M 0 ω = 0) {b : ℝ} {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b) :
    ∀ j, j ≤ n → ∀ ω, |M j ω| ≤ j * b := by
  intro j
  induction j with
  | zero => intro _ ω; simp [hM0 ω]
  | succ j ih =>
      intro hj ω
      have hjn : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have h1 := ih (le_of_lt hjn) ω
      have h2 := hinc j hjn ω
      have h3 : M (j + 1) ω = M j ω + (M (j + 1) ω - M j ω) := by ring
      calc |M (j + 1) ω| = |M j ω + (M (j + 1) ω - M j ω)| := by rw [← h3]
        _ ≤ |M j ω| + |M (j + 1) ω - M j ω| := abs_add_le _ _
        _ ≤ j * b + b := add_le_add h1 h2
        _ = ((j : ℝ) + 1) * b := by ring
        _ = ((j + 1 : ℕ) : ℝ) * b := by push_cast; ring

/-- **The exponential supermartingale.**  With `c = λ²/(2(1-λb/3))`, the process
`exp(λ M_k - c V_k)` has integral at most `1` at every time up to `n`. -/
theorem integral_exp_sub_condQvar_le_one {ℱ : Filtration ℕ m0} [IsProbabilityMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b : ℝ} {n : ℕ} (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {lam : ℝ} (hlam : 0 < lam) (hlb : lam * b < 3) :
    ∀ k, k ≤ n → ∫ ω, Real.exp (lam * M k ω
        - lam ^ 2 / (2 * (1 - lam * b / 3)) * condQvar P ℱ M k ω) ∂P ≤ 1 := by
  have hθpos : (0 : ℝ) < 1 - lam * b / 3 := by linarith
  set c : ℝ := lam ^ 2 / (2 * (1 - lam * b / 3)) with hcdef
  have hcnn : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  have hMmeas : ∀ j, Measurable[m0] (M j) := fun j =>
    ((hmart.stronglyMeasurable j).mono (ℱ.le j)).measurable
  have hMb : ∀ j, j ≤ n → ∀ ω, |M j ω| ≤ j * b := abs_le_of_increments hM0 hinc
  have hZmeas : ∀ j, Measurable[m0]
      (fun ω => Real.exp (lam * M j ω - c * condQvar P ℱ M j ω)) := fun j =>
    Real.measurable_exp.comp (((hMmeas j).const_mul lam).sub
      ((measurable_condQvar P ℱ M j).const_mul c))
  have hZint : ∀ j, j ≤ n → Integrable
      (fun ω => Real.exp (lam * M j ω - c * condQvar P ℱ M j ω)) P := by
    intro j hj
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((j : ℝ) * b))))
      (hZmeas j).aestronglyMeasurable ?_
    filter_upwards [condQvar_nonneg P ℱ M j] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : M j ω ≤ (j : ℝ) * b := (abs_le.mp (hMb j hj ω)).2
    have h2 : 0 ≤ c * condQvar P ℱ M j ω := mul_nonneg hcnn hω
    nlinarith [hlam]
  intro k
  induction k with
  | zero =>
      intro _
      have hone : ∀ ω, Real.exp (lam * M 0 ω - c * condQvar P ℱ M 0 ω) = 1 := by
        intro ω
        rw [hM0 ω, condQvar]
        simp
      simp only [hone]
      simp
  | succ k ih =>
      intro hk1
      have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk1
      have hk : k ≤ n := le_of_lt hkn
      set X : Ω → ℝ := fun ω => M (k + 1) ω - M k ω with hXdef
      have hXmeas : Measurable[m0] X := (hMmeas (k + 1)).sub (hMmeas k)
      have hXb : ∀ ω, |X ω| ≤ b := hinc k hkn
      have hXmean : P[X | ℱ k] =ᵐ[P] 0 := by
        have h3 := condExp_sub (μ := P) (hmart.integrable (k + 1)) (hmart.integrable k) (ℱ k)
        have h1 : P[M (k + 1) | ℱ k] =ᵐ[P] M k := hmart.condExp_ae_eq (Nat.le_succ k)
        have h2 : P[M k | ℱ k] = M k :=
          condExp_of_stronglyMeasurable (ℱ.le k) (hmart.stronglyMeasurable k)
            (hmart.integrable k)
        filter_upwards [h3, h1] with ω e3 e1
        show P[M (k + 1) - M k | ℱ k] ω = 0
        rw [e3]
        simp only [Pi.sub_apply]
        rw [e1, h2, sub_self]
      have hcond := condExp_exp_le (ℱ.le k) hXmeas hXb hXmean hlam hlb
      rw [← hcdef] at hcond
      set g : Ω → ℝ := fun ω => Real.exp (lam * M k ω - c * condQvar P ℱ M (k + 1) ω)
        with hgdef
      have hgSM : StronglyMeasurable[ℱ k] g := by
        refine Measurable.stronglyMeasurable ?_
        exact Real.measurable_exp.comp
          (((hmart.stronglyMeasurable k).measurable.const_mul lam).sub
            ((stronglyMeasurable_condQvar P ℱ M (k + 1) k le_rfl).measurable.const_mul c))
      have hEmeas : Measurable[m0] fun ω => Real.exp (lam * X ω) :=
        Real.measurable_exp.comp (hXmeas.const_mul lam)
      have hEint : Integrable (fun ω => Real.exp (lam * X ω)) P := by
        refine Integrable.mono' (integrable_const (Real.exp (lam * b)))
          hEmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [(abs_le.mp (hXb ω)).2, hlam]
      have hprodeq : (fun ω => Real.exp (lam * M (k + 1) ω - c * condQvar P ℱ M (k + 1) ω))
          = g * fun ω => Real.exp (lam * X ω) := by
        funext ω
        show Real.exp _ = Real.exp _ * Real.exp _
        rw [← Real.exp_add]
        congr 1
        rw [hXdef]
        ring
      have hprodint : Integrable (g * fun ω => Real.exp (lam * X ω)) P := by
        rw [← hprodeq]; exact hZint (k + 1) hk1
      have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ k) hgSM hprodint hEint
      have hstep : P[fun ω => Real.exp (lam * M (k + 1) ω - c * condQvar P ℱ M (k + 1) ω) | ℱ k]
          ≤ᵐ[P] fun ω => Real.exp (lam * M k ω - c * condQvar P ℱ M k ω) := by
        rw [hprodeq]
        filter_upwards [hpull, hcond] with ω e1 e2
        rw [e1]
        simp only [Pi.mul_apply]
        have hgpos : 0 < g ω := Real.exp_pos _
        calc g ω * P[fun ω => Real.exp (lam * X ω) | ℱ k] ω
            ≤ g ω * Real.exp (c * P[fun ω => X ω ^ 2 | ℱ k] ω) := by nlinarith [e2, hgpos]
          _ = Real.exp (lam * M k ω - c * condQvar P ℱ M k ω) := by
              rw [hgdef, ← Real.exp_add, condQvar_succ]
              congr 1
              ring
      calc ∫ ω, Real.exp (lam * M (k + 1) ω - c * condQvar P ℱ M (k + 1) ω) ∂P
          = ∫ ω, P[fun ω => Real.exp (lam * M (k + 1) ω
              - c * condQvar P ℱ M (k + 1) ω) | ℱ k] ω ∂P :=
            (integral_condExp (ℱ.le k)).symm
        _ ≤ ∫ ω, Real.exp (lam * M k ω - c * condQvar P ℱ M k ω) ∂P :=
            integral_mono_ae integrable_condExp (hZint k hk) hstep
        _ ≤ 1 := ih hk


/-- **Freedman's inequality for the upper tail**, with a strictly positive bound on the
quadratic variation. -/
theorem freedman_upper_of_pos {ℱ : Filtration ℕ m0} [IsProbabilityMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b v : ℝ} {n : ℕ} (hb : 0 < b) (hv : 0 < v)
    (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    (hqv : ∀ᵐ ω ∂P, condQvar P ℱ M n ω ≤ v)
    {r : ℝ} (hr : 0 ≤ r) :
    (P {ω | r ≤ M n ω}).toReal ≤ Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))) := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · have h1 : (P {ω | r ≤ M n ω}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have h2 : -(r ^ 2 / (2 * (v + b * r / 3))) = 0 := by rw [← hr0]; simp
    rw [h2, Real.exp_zero]
    exact h1
  set D : ℝ := v + b * r / 3 with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  set lam : ℝ := r / D with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlb : lam * b < 3 := by
    rw [hlamdef, div_mul_eq_mul_div, div_lt_iff₀ hD, hDdef]
    nlinarith
  have hθpos : (0 : ℝ) < 1 - lam * b / 3 := by linarith
  set c : ℝ := lam ^ 2 / (2 * (1 - lam * b / 3)) with hcdef
  have hcnn : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  have hMmeas : ∀ j, Measurable[m0] (M j) := fun j =>
    ((hmart.stronglyMeasurable j).mono (ℱ.le j)).measurable
  have hMb := abs_le_of_increments hM0 hinc n le_rfl
  have hexpint : Integrable (fun ω => Real.exp (lam * M n ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((n : ℝ) * b))))
      (Real.measurable_exp.comp ((hMmeas n).const_mul lam)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (hMb ω)).2, hlam])
  have hZmeas : Measurable[m0] fun ω => Real.exp (lam * M n ω - c * condQvar P ℱ M n ω) :=
    Real.measurable_exp.comp (((hMmeas n).const_mul lam).sub
      ((measurable_condQvar P ℱ M n).const_mul c))
  have hZint : Integrable (fun ω => Real.exp (lam * M n ω - c * condQvar P ℱ M n ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((n : ℝ) * b))))
      hZmeas.aestronglyMeasurable ?_
    filter_upwards [condQvar_nonneg P ℱ M n] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : M n ω ≤ (n : ℝ) * b := (abs_le.mp (hMb ω)).2
    have h2 : 0 ≤ c * condQvar P ℱ M n ω := mul_nonneg hcnn hω
    nlinarith [hlam]
  have hI := integral_exp_sub_condQvar_le_one hmart hM0 hinc hlam hlb n le_rfl
  rw [← hcdef] at hI
  have hmgf : mgf (M n) P lam ≤ Real.exp (c * v) := by
    have h1 : ∀ᵐ ω ∂P, Real.exp (lam * M n ω)
        ≤ Real.exp (c * v) * Real.exp (lam * M n ω - c * condQvar P ℱ M n ω) := by
      filter_upwards [hqv] with ω hω
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [hcnn])
    calc mgf (M n) P lam = ∫ ω, Real.exp (lam * M n ω) ∂P := rfl
      _ ≤ ∫ ω, Real.exp (c * v)
            * Real.exp (lam * M n ω - c * condQvar P ℱ M n ω) ∂P :=
          integral_mono_ae hexpint (hZint.const_mul _) h1
      _ = Real.exp (c * v)
            * ∫ ω, Real.exp (lam * M n ω - c * condQvar P ℱ M n ω) ∂P :=
          integral_const_mul _ _
      _ ≤ Real.exp (c * v) * 1 := by nlinarith [hI, Real.exp_pos (c * v)]
      _ = Real.exp (c * v) := mul_one _
  have hone : 1 - lam * b / 3 = v / D := by
    rw [hlamdef, hDdef]
    field_simp
    ring
  have hcv : c * v = r ^ 2 / (2 * D) := by
    rw [hcdef, hone, hlamdef]
    field_simp
  have hchern := measure_ge_le_exp_mul_mgf (μ := P) (X := M n) (t := lam) r hlam.le hexpint
  have hfin : Real.exp (-lam * r) * Real.exp (c * v) = Real.exp (-(r ^ 2 / (2 * D))) := by
    rw [← Real.exp_add, hcv, hlamdef]
    congr 1
    field_simp
    ring
  calc (P {ω | r ≤ M n ω}).toReal = P.real {ω | r ≤ M n ω} := (measureReal_def P _).symm
    _ ≤ Real.exp (-lam * r) * mgf (M n) P lam := hchern
    _ ≤ Real.exp (-lam * r) * Real.exp (c * v) := by
        have := Real.exp_pos (-lam * r)
        nlinarith [hmgf]
    _ = Real.exp (-(r ^ 2 / (2 * D))) := hfin


/-- **Freedman's inequality for the upper tail.** -/
theorem freedman_upper {ℱ : Filtration ℕ m0} [IsProbabilityMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b v : ℝ} {n : ℕ} (hb : 0 < b) (hv : 0 ≤ v)
    (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    (hqv : ∀ᵐ ω ∂P, condQvar P ℱ M n ω ≤ v)
    {r : ℝ} (hr : 0 ≤ r) :
    (P {ω | r ≤ M n ω}).toReal ≤ Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))) := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · have h1 : (P {ω | r ≤ M n ω}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have h2 : -(r ^ 2 / (2 * (v + b * r / 3))) = 0 := by rw [← hr0]; simp
    rw [h2, Real.exp_zero]
    exact h1
  have key : ∀ ε : ℝ, 0 < ε → (P {ω | r ≤ M n ω}).toReal
      ≤ Real.exp (-(r ^ 2 / (2 * (v + ε + b * r / 3)))) := by
    intro ε hε
    refine freedman_upper_of_pos hmart hM0 hb (by linarith) hinc ?_ hr
    filter_upwards [hqv] with ω hω
    linarith
  have hne : (2 : ℝ) * (v + 0 + b * r / 3) ≠ 0 := by nlinarith
  have hcont : ContinuousAt
      (fun ε : ℝ => Real.exp (-(r ^ 2 / (2 * (v + ε + b * r / 3))))) 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => (2 : ℝ) * (v + ε + b * r / 3)) 0 := by fun_prop
    exact Real.continuous_exp.continuousAt.comp (continuousAt_const.div h1 hne).neg
  have htend : Tendsto (fun ε : ℝ => Real.exp (-(r ^ 2 / (2 * (v + ε + b * r / 3))))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))))) := by
    have h0 : Real.exp (-(r ^ 2 / (2 * (v + (0 : ℝ) + b * r / 3))))
        = Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))) := by norm_num
    rw [← h0]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-- **Freedman's inequality.**  A martingale started at `0` with increments bounded by `b`
and predictable quadratic variation at most `v` satisfies
`P(M n ≤ -r) ≤ exp(-r²/(2(v + b r / 3)))`. -/
theorem freedman [IsProbabilityMeasure P] {n : ℕ} {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hmart : Martingale M ℱ P) (hM0 : M 0 = 0) {b v : ℝ} (hb : 0 < b) (hv : 0 ≤ v)
    (hinc : ∀ i < n, ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    (hqv : ∀ᵐ ω ∂P, ∑ i ∈ Finset.range n,
        (P[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | ℱ i]) ω ≤ v)
    (r : ℝ) (hr : 0 ≤ r) :
    (P {ω | M n ω ≤ -r}).toReal ≤ Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))) := by
  have hM0' : ∀ ω, (-M) 0 ω = 0 := by
    intro ω
    simp only [Pi.neg_apply, hM0, Pi.zero_apply, neg_zero]
  have hinc' : ∀ i, i < n → ∀ ω, |(-M) (i + 1) ω - (-M) i ω| ≤ b := by
    intro i hi ω
    have h := hinc i hi ω
    simp only [Pi.neg_apply]
    calc |(-M (i + 1) ω) - (-M i ω)| = |M (i + 1) ω - M i ω| := by
          rw [show (-M (i + 1) ω) - (-M i ω) = -(M (i + 1) ω - M i ω) by ring, abs_neg]
      _ ≤ b := h
  have hfun : ∀ i : ℕ, (fun ω' => ((-M) (i + 1) ω' - (-M) i ω') ^ 2)
      = fun ω' => (M (i + 1) ω' - M i ω') ^ 2 := by
    intro i
    funext ω'
    simp only [Pi.neg_apply]
    ring
  have hqv' : ∀ᵐ ω ∂P, condQvar P ℱ (-M) n ω ≤ v := by
    filter_upwards [hqv] with ω hω
    show ∑ i ∈ Finset.range n, (P[fun ω' => ((-M) (i + 1) ω' - (-M) i ω') ^ 2 | ℱ i]) ω ≤ v
    simpa only [hfun] using hω
  have hset : {ω | M n ω ≤ -r} = {ω | r ≤ (-M) n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact freedman_upper hmart.neg hM0' hb hv hinc' hqv' hr

end LatticeProb
