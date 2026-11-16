import LatticeProb.Prob.Process.DDSPassage

/-!
# The discrete characteristic-function bound

Ported from the vertex-reinforced walk development. For a discrete real martingale `Z` from `0`
with increments at most `b ≤ 1`, the bound
`|E e^{i Z_N} - e^{-q/2}| ≤ ½ E |∑ (Z_{i+1} - Z_i)² - q| + 4 b (1 + q)` is proved by a telescoping
comparison of the characteristic functions along the martingale (`discreteCFBound_holds`).
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process.BdgUpperContinuous.DdsDiscrete

noncomputable section

/-- The unit complex number `e^{i x}` for real `x`. -/
def expI (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

lemma norm_expI (x : ℝ) : ‖expI x‖ = 1 := Complex.norm_exp_I_mul_ofReal x

lemma expI_add (x y : ℝ) : expI (x + y) = expI x * expI y := by
  unfold expI; rw [← Complex.exp_add]; push_cast; ring_nf

lemma norm_expI_sub_one_le (x : ℝ) : ‖expI x - 1‖ ≤ |x| := by
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)
  simpa [expI] using this

lemma norm_expI_sub_one_sub_le (x : ℝ) : ‖expI x - 1 - Complex.I * x‖ ≤ x ^ 2 / 2 := by
  set f : ℝ → ℂ := fun t => expI (x * t) - 1 - Complex.I * ((x * t : ℝ) : ℂ) with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f (Complex.I * x * expI (x * t) - Complex.I * x) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ)) (x : ℂ) t := by
      have := ((hasDerivAt_id t).const_mul x).ofReal_comp
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => Complex.I * ((x * t : ℝ) : ℂ)) (Complex.I * x) t :=
      h1.const_mul _
    have h3 := h2.cexp
    have h4 := (h3.sub_const 1).sub h2
    exact h4.congr_deriv (by simp only [expI]; ring)
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x ^ 2 * t ^ 2 / 2) (x ^ 2 * t) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (x ^ 2)).div_const 2
    exact this.congr_deriv (by norm_num; ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f)
    (f' := fun t => Complex.I * x * expI (x * t) - Complex.I * x) (a := 0) (b := 1)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt) (B := fun t : ℝ => x ^ 2 * t ^ 2 / 2)
    (B' := fun t => x ^ 2 * t) (by simp [hf, expI]) hB ?_ (x := 1) ⟨zero_le_one, le_rfl⟩
  · simpa [hf] using key
  · intro t ht
    have h0 : 0 ≤ t := ht.1
    have : Complex.I * x * expI (x * t) - Complex.I * x = Complex.I * x * (expI (x * t) - 1) := by ring
    rw [this, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |x| * ‖expI (x * t) - 1‖ ≤ |x| * |x * t| :=
          mul_le_mul_of_nonneg_left (norm_expI_sub_one_le _) (abs_nonneg _)
      _ = x ^ 2 * t := by rw [abs_mul, abs_of_nonneg h0, ← mul_assoc, ← sq_abs x]; ring

/-- The one-step multiplier `e^{i d + d^2/2}`. -/
def stepFactor (d : ℝ) : ℂ := expI d * ((Real.exp (d ^ 2 / 2) : ℝ) : ℂ)

lemma norm_expI_taylor_le {d : ℝ} (hd : |d| ≤ 1) :
    ‖expI d - 1 - Complex.I * d + ((d ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 1 / 4 * |d| ^ 3 := by
  have hx : ‖Complex.I * (d : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hd
  have h := Complex.exp_bound hx (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (Complex.I * (d : ℂ)) ^ m / (m.factorial : ℂ)
      = 1 + Complex.I * d - ((d ^ 2 / 2 : ℝ) : ℂ) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring_nf
    simp [Complex.I_sq]
    ring
  have : expI d - 1 - Complex.I * d + ((d ^ 2 / 2 : ℝ) : ℂ)
      = Complex.exp (Complex.I * d) - ∑ m ∈ Finset.range 3, (Complex.I * (d : ℂ)) ^ m / (m.factorial : ℂ) := by
    rw [hsum]; simp only [expI]; ring
  rw [this]
  refine h.trans ?_
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have : (0 : ℝ) ≤ |d| ^ 3 := by positivity
  norm_num [Nat.factorial]
  nlinarith

lemma norm_stepFactor_sub_le {d : ℝ} (hd : |d| ≤ 1) :
    ‖stepFactor d - 1 - Complex.I * d‖ ≤ 2 * |d| ^ 3 := by
  have hr1 := norm_expI_taylor_le hd
  have h1 := norm_expI_sub_one_le d
  have hx : |d ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have : d ^ 2 ≤ 1 := by nlinarith [abs_nonneg d, sq_abs d]
    linarith
  have hr2 := Real.abs_exp_sub_one_sub_id_le hx
  have hid : stepFactor d - 1 - Complex.I * d
      = (expI d - 1 - Complex.I * d + ((d ^ 2 / 2 : ℝ) : ℂ))
        + expI d * ((Real.exp (d ^ 2 / 2) - 1 - d ^ 2 / 2 : ℝ) : ℂ)
        + (expI d - 1) * ((d ^ 2 / 2 : ℝ) : ℂ) := by
    simp only [stepFactor]; push_cast; ring
  rw [hid]
  have h3 : ‖expI d * ((Real.exp (d ^ 2 / 2) - 1 - d ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 1 / 4 * |d| ^ 3 := by
    rw [norm_mul, norm_expI, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine hr2.trans ?_
    have h4 : (d ^ 2 / 2) ^ 2 = d ^ 4 / 4 := by ring
    rw [h4]
    have : d ^ 4 = |d| ^ 4 := by rw [show d ^ 4 = (d ^ 2) ^ 2 by ring, ← sq_abs d]; ring
    rw [this]
    have h5 : |d| ^ 4 ≤ |d| ^ 3 := by
      have : |d| ^ 4 = |d| ^ 3 * |d| := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) hd
    linarith
  have h6 : ‖(expI d - 1) * ((d ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 * |d| ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖expI d - 1‖ * (d ^ 2 / 2) ≤ |d| * (d ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 / 2 * |d| ^ 3 := by rw [← sq_abs d]; ring
  calc _ ≤ ‖expI d - 1 - Complex.I * d + ((d ^ 2 / 2 : ℝ) : ℂ)‖
        + ‖expI d * ((Real.exp (d ^ 2 / 2) - 1 - d ^ 2 / 2 : ℝ) : ℂ)‖
        + ‖(expI d - 1) * ((d ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add₃_le
    _ ≤ 2 * |d| ^ 3 := by
        have : (0 : ℝ) ≤ |d| ^ 3 := by positivity
        nlinarith


/-! ### The stopped objects, pointwise -/

section Pointwise

variable {Ω : Type*}

/-- The sum of squared increments `∑_{i<k} (Z_{i+1} - Z_i)²`. -/
def sqSum (Z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2

/-- The indicator of `{k < κ}`, where `κ` is the first time the sum of squares reaches `q`
(capped at the horizon): it equals `1` exactly when `sqSum Z j ω < q` for every `j ≤ k`. -/
def stopInd (Z : ℕ → Ω → ℝ) (q : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if ∀ j ≤ k, sqSum Z j ω < q then 1 else 0

/-- The stopped process `Z_{min m κ} = ∑_{k<m} 1_{k<κ} (Z_{k+1} - Z_k)`. -/
def stopZ (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range m, stopInd Z q k ω * (Z (k + 1) ω - Z k ω)

/-- The stopped sum of squares `S_{min m κ} = ∑_{k<m} 1_{k<κ} (Z_{k+1} - Z_k)²`. -/
def stopS (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range m, stopInd Z q k ω * (Z (k + 1) ω - Z k ω) ^ 2

/-- The stopped exponential process `e^{i Z_{min m κ}} e^{S_{min m κ}/2}`. -/
def stopG (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  expI (stopZ Z q m ω) * ((Real.exp (stopS Z q m ω / 2) : ℝ) : ℂ)

lemma stopInd_eq_one_iff (Z : ℕ → Ω → ℝ) (q : ℝ) (k : ℕ) (ω : Ω) :
    stopInd Z q k ω = 1 ↔ ∀ j ≤ k, sqSum Z j ω < q := by
  unfold stopInd
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · simp [h]

lemma stopInd_cases (Z : ℕ → Ω → ℝ) (q : ℝ) (k : ℕ) (ω : Ω) :
    stopInd Z q k ω = 0 ∨ stopInd Z q k ω = 1 := by
  unfold stopInd
  split_ifs <;> simp

lemma stopInd_of_succ {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ} {ω : Ω}
    (h : stopInd Z q (k + 1) ω = 1) : stopInd Z q k ω = 1 := by
  rw [stopInd_eq_one_iff] at h ⊢
  exact fun j hj => h j (by omega)

lemma stopInd_succ_iff (Z : ℕ → Ω → ℝ) (q : ℝ) (k : ℕ) (ω : Ω) :
    stopInd Z q (k + 1) ω = 1 ↔ stopInd Z q k ω = 1 ∧ sqSum Z (k + 1) ω < q := by
  rw [stopInd_eq_one_iff, stopInd_eq_one_iff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h _ le_rfl⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact h1 j (by omega)
    · have : j = k + 1 := by omega
      rw [this]
      exact h2

lemma sqSum_zero (Z : ℕ → Ω → ℝ) (ω : Ω) : sqSum Z 0 ω = 0 := by simp [sqSum]

lemma sqSum_succ (Z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    sqSum Z (k + 1) ω = sqSum Z k ω + (Z (k + 1) ω - Z k ω) ^ 2 := by
  unfold sqSum; rw [Finset.sum_range_succ]

lemma stopZ_zero (Z : ℕ → Ω → ℝ) (q : ℝ) (ω : Ω) : stopZ Z q 0 ω = 0 := by simp [stopZ]

lemma stopS_zero (Z : ℕ → Ω → ℝ) (q : ℝ) (ω : Ω) : stopS Z q 0 ω = 0 := by simp [stopS]

lemma stopZ_succ (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) :
    stopZ Z q (m + 1) ω = stopZ Z q m ω + stopInd Z q m ω * (Z (m + 1) ω - Z m ω) := by
  unfold stopZ; rw [Finset.sum_range_succ]

lemma stopS_succ (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) :
    stopS Z q (m + 1) ω = stopS Z q m ω + stopInd Z q m ω * (Z (m + 1) ω - Z m ω) ^ 2 := by
  unfold stopS; rw [Finset.sum_range_succ]

lemma stopS_nonneg (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) : 0 ≤ stopS Z q m ω := by
  unfold stopS
  refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (sq_nonneg _)
  rcases stopInd_cases Z q k ω with h | h <;> simp [h]

/-- Before the stopping time the stopped process agrees with the process, and the stopped sum of
squares with the sum of squares. -/
lemma stopZ_stopS_of_stopInd {Z : ℕ → Ω → ℝ} {q : ℝ} {ω : Ω} (hZ0 : Z 0 ω = 0) :
    ∀ k, stopInd Z q k ω = 1 → stopZ Z q k ω = Z k ω ∧ stopS Z q k ω = sqSum Z k ω := by
  intro k
  induction k with
  | zero => intro _; simp [stopZ, stopS, sqSum, hZ0]
  | succ k ih =>
    intro h
    have h' := stopInd_of_succ h
    obtain ⟨h1, h2⟩ := ih h'
    rw [stopZ_succ, stopS_succ, sqSum_succ, h', h1, h2]
    constructor <;> ring

lemma sqSum_lt_of_stopInd {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ} {ω : Ω}
    (h : stopInd Z q k ω = 1) : sqSum Z k ω < q :=
  (stopInd_eq_one_iff Z q k ω).1 h k le_rfl

/-- The stopped sum of squares overshoots `q` by at most one step. -/
lemma stopS_le_of_increments {Z : ℕ → Ω → ℝ} {q b : ℝ} {ω : Ω} {N : ℕ} (hq : 0 ≤ q)
    (hZ0 : Z 0 ω = 0) (hinc : ∀ i, i < N → |Z (i + 1) ω - Z i ω| ≤ b) :
    ∀ m, m ≤ N → stopS Z q m ω ≤ q + b ^ 2 := by
  intro m
  induction m with
  | zero => intro _; rw [stopS_zero]; nlinarith [sq_nonneg b]
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    rw [stopS_succ]
    rcases stopInd_cases Z q m ω with h0 | h1
    · rw [h0]; simpa using ih'
    · obtain ⟨_, h2⟩ := stopZ_stopS_of_stopInd hZ0 m h1
      have hlt := sqSum_lt_of_stopInd h1
      have hab := abs_le.1 (hinc m (by omega))
      have hd : (Z (m + 1) ω - Z m ω) ^ 2 ≤ b ^ 2 := sq_le_sq' hab.1 hab.2
      rw [h1, h2]
      nlinarith

/-- If the horizon is reached at or after the stopping time, the stopped sum of squares has
reached `q`. -/
lemma le_stopS_of_stopInd_eq_zero {Z : ℕ → Ω → ℝ} {q : ℝ} {ω : Ω} (hZ0 : Z 0 ω = 0) :
    ∀ m, stopInd Z q m ω = 0 → q ≤ stopS Z q m ω := by
  intro m
  induction m with
  | zero =>
    intro h
    have h1 : ¬ (stopInd Z q 0 ω = 1) := by rw [h]; norm_num
    rw [stopInd_eq_one_iff] at h1
    have hq : ¬ sqSum Z 0 ω < q := fun hlt => h1 fun j hj => by
      obtain rfl : j = 0 := by omega
      exact hlt
    rw [stopS_zero]
    rw [sqSum_zero] at hq
    exact not_lt.1 hq
  | succ m ih =>
    intro h
    have h1 : ¬ (stopInd Z q (m + 1) ω = 1) := by rw [h]; norm_num
    rw [stopInd_succ_iff] at h1
    rw [stopS_succ]
    rcases stopInd_cases Z q m ω with h0 | h1'
    · rw [h0]; simpa using ih h0
    · obtain ⟨_, h2⟩ := stopZ_stopS_of_stopInd hZ0 m h1'
      have hge : q ≤ sqSum Z (m + 1) ω := by
        by_contra hlt
        exact h1 ⟨h1', not_le.1 hlt⟩
      rw [h1', h2, one_mul, ← sqSum_succ]
      exact hge

lemma sqSum_sub_stopS (Z : ℕ → Ω → ℝ) (q : ℝ) (N : ℕ) (ω : Ω) :
    sqSum Z N ω - stopS Z q N ω
      = ∑ k ∈ Finset.range N, (1 - stopInd Z q k ω) * (Z (k + 1) ω - Z k ω) ^ 2 := by
  unfold sqSum stopS
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma stopS_le_sqSum (Z : ℕ → Ω → ℝ) (q : ℝ) (N : ℕ) (ω : Ω) :
    stopS Z q N ω ≤ sqSum Z N ω := by
  have h := sqSum_sub_stopS Z q N ω
  have : 0 ≤ ∑ k ∈ Finset.range N, (1 - stopInd Z q k ω) * (Z (k + 1) ω - Z k ω) ^ 2 := by
    refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (sq_nonneg _)
    rcases stopInd_cases Z q k ω with h | h <;> simp [h]
  linarith

/-- Telescoping for the exponential: the difference between `e^{i Z_m}` and `e^{i Z_{min m κ}}`
is a sum over the steps after the stopping time. -/
lemma expI_sub_stopZ {Z : ℕ → Ω → ℝ} {q : ℝ} {ω : Ω} (hZ0 : Z 0 ω = 0) :
    ∀ m, expI (Z m ω) - expI (stopZ Z q m ω)
      = ∑ k ∈ Finset.range m, (((1 - stopInd Z q k ω : ℝ)) : ℂ) * expI (Z k ω) *
          (expI (Z (k + 1) ω - Z k ω) - 1) := by
  intro m
  induction m with
  | zero => simp [stopZ_zero, hZ0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, stopZ_succ]
    have e1 : expI (Z (m + 1) ω) = expI (Z m ω) * expI (Z (m + 1) ω - Z m ω) := by
      rw [← expI_add]; congr 1; ring
    rcases stopInd_cases Z q m ω with h0 | h1
    · rw [h0, e1]
      simp
      ring
    · obtain ⟨hz, _⟩ := stopZ_stopS_of_stopInd hZ0 m h1
      have e2 : Z m ω + 1 * (Z (m + 1) ω - Z m ω) = Z (m + 1) ω := by ring
      rw [h1, hz, e2]
      simp

/-- Telescoping for the stopped exponential process. -/
lemma stopG_sub_one (Z : ℕ → Ω → ℝ) (q : ℝ) (ω : Ω) :
    ∀ m, stopG Z q m ω - 1
      = ∑ k ∈ Finset.range m, ((stopInd Z q k ω : ℝ) : ℂ) * stopG Z q k ω *
          (stepFactor (Z (k + 1) ω - Z k ω) - 1) := by
  intro m
  induction m with
  | zero => simp [stopG, stopZ_zero, stopS_zero, expI]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    rcases stopInd_cases Z q m ω with h0 | h1
    · unfold stopG
      rw [stopZ_succ, stopS_succ, h0]
      simp
    · unfold stopG stepFactor
      rw [stopZ_succ, stopS_succ, h1, one_mul, one_mul, expI_add]
      have : Real.exp ((stopS Z q m ω + (Z (m + 1) ω - Z m ω) ^ 2) / 2)
          = Real.exp (stopS Z q m ω / 2) * Real.exp ((Z (m + 1) ω - Z m ω) ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      push_cast
      ring

lemma norm_stopG (Z : ℕ → Ω → ℝ) (q : ℝ) (m : ℕ) (ω : Ω) :
    ‖stopG Z q m ω‖ = Real.exp (stopS Z q m ω / 2) := by
  unfold stopG
  rw [norm_mul, norm_expI, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma norm_stopG_le {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ} {ω : Ω} (hZ0 : Z 0 ω = 0)
    (h : stopInd Z q k ω = 1) : ‖stopG Z q k ω‖ ≤ Real.exp (q / 2) := by
  rw [norm_stopG, (stopZ_stopS_of_stopInd hZ0 k h).2]
  exact Real.exp_le_exp.2 (by linarith [sqSum_lt_of_stopInd h])

/-- The scalar inequality behind the first term. -/
lemma pointwise_real {s t q b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hcase : (t = s ∧ s < q) ∨ (q ≤ t ∧ t ≤ q + b ^ 2 ∧ t ≤ s)) :
    (s - t) / 2 + |1 - Real.exp ((t - q) / 2)| ≤ |s - q| / 2 + b := by
  rcases hcase with ⟨rfl, hlt⟩ | ⟨hqt, htb, hts⟩
  · have h1 := Real.add_one_le_exp ((t - q) / 2)
    have h2 : Real.exp ((t - q) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
    linarith
  · have hy0 : 0 ≤ (t - q) / 2 := by linarith
    have hy1 : (t - q) / 2 ≤ b ^ 2 / 2 := by linarith
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    have hyabs : |(t - q) / 2| ≤ 1 := by
      rw [abs_of_nonneg hy0]; linarith
    have h3 := Real.abs_exp_sub_one_sub_id_le hyabs
    have h4 : 1 ≤ Real.exp ((t - q) / 2) := Real.one_le_exp hy0
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h5 := (abs_le.1 h3).2
    have h6 : ((t - q) / 2) ^ 2 ≤ (b ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hy0 hy1 2
    rw [abs_of_nonneg (by linarith : 0 ≤ s - q)]
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) (sub_nonneg.2 hb1)]

end Pointwise


/-! ### Measurability and orthogonality -/

section Measure

/-- For a bounded `ℱ i`-measurable `g`, `g (X_{i+1} - X_i)` is integrable and has integral `0`. -/
lemma integral_mul_increment_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
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

/-- Complex version of `integral_mul_increment_eq_zero`: for a bounded `ℱ i`-measurable complex
`c`, the product `c (X_{i+1} - X_i)` is integrable with integral `0`. -/
lemma integral_complex_mul_increment_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) (i : ℕ) {c : Ω → ℂ} (hc : StronglyMeasurable[ℱ i] c) {C : ℝ}
    (hcb : ∀ ω, ‖c ω‖ ≤ C) :
    Integrable (fun ω => c ω * ((X (i + 1) ω - X i ω : ℝ) : ℂ)) P ∧
      ∫ ω, c ω * ((X (i + 1) ω - X i ω : ℝ) : ℂ) ∂P = 0 := by
  have hre : StronglyMeasurable[ℱ i] (fun ω => (c ω).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hc
  have him : StronglyMeasurable[ℱ i] (fun ω => (c ω).im) :=
    Complex.continuous_im.comp_stronglyMeasurable hc
  obtain ⟨hI1, h1⟩ := integral_mul_increment_eq_zero P ℱ X hM i hre (C := C)
    (fun ω => (Complex.abs_re_le_norm _).trans (hcb ω))
  obtain ⟨hI2, h2⟩ := integral_mul_increment_eq_zero P ℱ X hM i him (C := C)
    (fun ω => (Complex.abs_im_le_norm _).trans (hcb ω))
  have hint : Integrable (fun ω => c ω * ((X (i + 1) ω - X i ω : ℝ) : ℂ)) P := by
    rw [← Integrable.re_im_iff]
    refine ⟨?_, ?_⟩
    · simpa using hI1
    · simpa using hI2
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have h := integral_re hint
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at h
    rw [h1] at h
    simpa using h.symm
  · have h := integral_im hint
    simp only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add] at h
    rw [h2] at h
    simpa using h.symm

/-- The orthogonality of a predictable bounded coefficient against the martingale increments, summed
over the first `N` steps. -/
lemma integrable_integral_orthSum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ)
    (hM : Martingale Z 𝒢 P) (N : ℕ) {C : ℝ} (c : ℕ → Ω → ℂ)
    (hc : ∀ k, StronglyMeasurable[𝒢 k] (c k)) (hcb : ∀ k, k < N → ∀ ω, ‖c k ω‖ ≤ C) :
    Integrable (fun ω => ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ)) P ∧
      ∫ ω, ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ) ∂P = 0 := by
  have hk : ∀ k ∈ Finset.range N,
      Integrable (fun ω => c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ)) P ∧
        ∫ ω, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ) ∂P = 0 := fun k hk' =>
    integral_complex_mul_increment_eq_zero P 𝒢 Z hM k (hc k) (hcb k (Finset.mem_range.1 hk'))
  refine ⟨integrable_finsetSum _ fun k hk' => (hk k hk').1, ?_⟩
  rw [integral_finsetSum _ fun k hk' => (hk k hk').1]
  exact Finset.sum_eq_zero fun k hk' => (hk k hk').2

/-- The sum of squares is measurable for any σ-algebra making the process measurable. -/
lemma measurable_sqSum {Ω : Type*} {m : MeasurableSpace Ω} {Z : ℕ → Ω → ℝ} {j : ℕ}
    (hZ : ∀ i ≤ j, Measurable[m] (Z i)) : Measurable[m] (sqSum Z j) := by
  have h : sqSum Z j = fun ω => ∑ i ∈ Finset.range j, (Z (i + 1) ω - Z i ω) ^ 2 := rfl
  rw [h]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact ((hZ (i + 1) (by omega)).sub (hZ i (by omega))).pow_const 2

lemma measurable_stopInd {Ω : Type*} {m : MeasurableSpace Ω} {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ}
    (hZ : ∀ i ≤ k, Measurable[m] (Z i)) : Measurable[m] (stopInd Z q k) := by
  have hset : MeasurableSet[m] {ω | ∀ j ≤ k, sqSum Z j ω < q} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
      measurableSet_lt (measurable_sqSum fun i hi => hZ i (by omega)) measurable_const
  exact Measurable.ite hset measurable_const measurable_const

lemma measurable_stopZ {Ω : Type*} {m : MeasurableSpace Ω} {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ}
    (hZ : ∀ i ≤ k, Measurable[m] (Z i)) : Measurable[m] (stopZ Z q k) := by
  have h : stopZ Z q k =
      fun ω => ∑ i ∈ Finset.range k, stopInd Z q i ω * (Z (i + 1) ω - Z i ω) := rfl
  rw [h]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact (measurable_stopInd fun j hj => hZ j (by omega)).mul
    ((hZ (i + 1) (by omega)).sub (hZ i (by omega)))

lemma measurable_stopS {Ω : Type*} {m : MeasurableSpace Ω} {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ}
    (hZ : ∀ i ≤ k, Measurable[m] (Z i)) : Measurable[m] (stopS Z q k) := by
  have h : stopS Z q k =
      fun ω => ∑ i ∈ Finset.range k, stopInd Z q i ω * (Z (i + 1) ω - Z i ω) ^ 2 := rfl
  rw [h]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact (measurable_stopInd fun j hj => hZ j (by omega)).mul
    (((hZ (i + 1) (by omega)).sub (hZ i (by omega))).pow_const 2)

lemma continuous_expI : Continuous expI := by
  unfold expI
  fun_prop

lemma measurable_stopG {Ω : Type*} {m : MeasurableSpace Ω} {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ}
    (hZ : ∀ i ≤ k, Measurable[m] (Z i)) : Measurable[m] (stopG Z q k) := by
  have h : stopG Z q k =
      fun ω => expI (stopZ Z q k ω) * ((Real.exp (stopS Z q k ω / 2) : ℝ) : ℂ) := rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · exact continuous_expI.measurable.comp (measurable_stopZ hZ)
  · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_stopS hZ).div_const 2))

/-- Before time `k` the process is `𝒢 k`-measurable. -/
lemma measurable_Z_filtration {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P) (k : ℕ) :
    ∀ i ≤ k, Measurable[𝒢 k] (Z i) := fun i hi =>
  ((hM.stronglyMeasurable i).mono (𝒢.mono hi)).measurable

lemma measurable_Z {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P) (i : ℕ) :
    Measurable (Z i) := ((hM.stronglyMeasurable i).mono (𝒢.le i)).measurable

end Measure

/-! ### The two estimates -/

section Estimates

lemma sqSum_nonneg {Ω : Type*} (Z : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : 0 ≤ sqSum Z N ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqSum_le_of_increments {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ} {ω : Ω}
    (hinc : ∀ i, i < N → |Z (i + 1) ω - Z i ω| ≤ b) : sqSum Z N ω ≤ N * b ^ 2 := by
  unfold sqSum
  calc ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 ≤ ∑ _i ∈ Finset.range N, b ^ 2 :=
        Finset.sum_le_sum fun i hi => by
          have hab := abs_le.1 (hinc i (Finset.mem_range.1 hi))
          exact sq_le_sq' hab.1 hab.2
    _ = N * b ^ 2 := by simp

/-- If `F = R + i Os`, where `Os` is integrable with integral `0`, and `‖R‖ ≤ g`, then
`‖∫ F‖ ≤ ∫ g`. -/
lemma norm_integral_le_of_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F Os R : Ω → ℂ} {g : Ω → ℝ} (hF : Integrable F P)
    (hOs : Integrable Os P) (hOs0 : ∫ ω, Os ω ∂P = 0)
    (hFR : ∀ ω, F ω = R ω + Complex.I * Os ω) (hg : Integrable g P)
    (hRg : ∀ ω, ‖R ω‖ ≤ g ω) : ‖∫ ω, F ω ∂P‖ ≤ ∫ ω, g ω ∂P := by
  have hR : Integrable R P := by
    have h : R = fun ω => F ω - Complex.I * Os ω := by
      funext ω
      rw [hFR ω]
      ring
    rw [h]
    exact hF.sub (hOs.const_mul _)
  have hint : ∫ ω, F ω ∂P = ∫ ω, R ω ∂P := by
    calc ∫ ω, F ω ∂P = ∫ ω, (R ω + Complex.I * Os ω) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hFR)
      _ = ∫ ω, R ω ∂P := by
          rw [integral_add hR (hOs.const_mul _), integral_const_mul, hOs0, mul_zero, add_zero]
  rw [hint]
  exact norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hRg)

/-- One step of the second term: the remainder of `e^{i d + d²/2}` is cubic. -/
lemma norm_stop_term_le {Ω : Type*} {Z : ℕ → Ω → ℝ} {q b : ℝ} {k : ℕ} {ω : Ω}
    (hZ0 : Z 0 ω = 0) (hb1 : b ≤ 1) (hd : |Z (k + 1) ω - Z k ω| ≤ b) :
    ‖((stopInd Z q k ω : ℝ) : ℂ) * stopG Z q k ω *
        (stepFactor (Z (k + 1) ω - Z k ω) - 1 - Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))‖
      ≤ Real.exp (q / 2) * (2 * b) * (stopInd Z q k ω * (Z (k + 1) ω - Z k ω) ^ 2) := by
  rcases stopInd_cases Z q k ω with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    have hG := norm_stopG_le hZ0 h1
    have hs := norm_stepFactor_sub_le (le_trans hd hb1)
    have hd3 : |Z (k + 1) ω - Z k ω| ^ 3 ≤ b * (Z (k + 1) ω - Z k ω) ^ 2 := by
      have h : |Z (k + 1) ω - Z k ω| ^ 3 = |Z (k + 1) ω - Z k ω| * (Z (k + 1) ω - Z k ω) ^ 2 := by
        rw [← sq_abs (Z (k + 1) ω - Z k ω)]; ring
      rw [h]
      exact mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    simp only [Complex.ofReal_one, one_mul, norm_mul]
    calc ‖stopG Z q k ω‖ * ‖stepFactor (Z (k + 1) ω - Z k ω) - 1 -
            Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ)‖
        ≤ Real.exp (q / 2) * (2 * |Z (k + 1) ω - Z k ω| ^ 3) :=
          mul_le_mul hG hs (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (q / 2) * (2 * (b * (Z (k + 1) ω - Z k ω) ^ 2)) := by gcongr
      _ = Real.exp (q / 2) * (2 * b) * (Z (k + 1) ω - Z k ω) ^ 2 := by ring

/-- One step of the first term: the remainder of `e^{i d}` is at most `d²/2`, and it only
counts after the stopping time. -/
lemma norm_stop_term_le' {Ω : Type*} {Z : ℕ → Ω → ℝ} {q : ℝ} {k : ℕ} {ω : Ω} :
    ‖((1 - stopInd Z q k ω : ℝ) : ℂ) * expI (Z k ω) *
        (expI (Z (k + 1) ω - Z k ω) - 1 - Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))‖
      ≤ (1 - stopInd Z q k ω) * ((Z (k + 1) ω - Z k ω) ^ 2 / 2) := by
  rcases stopInd_cases Z q k ω with h0 | h1
  · rw [h0]
    simp only [sub_zero, Complex.ofReal_one, one_mul, norm_mul, norm_expI]
    simpa using norm_expI_sub_one_sub_le (Z (k + 1) ω - Z k ω)
  · rw [h1]
    simp

/-- **Second term.** For a martingale `Z` from `0` with increments at most `b ≤ 1`, the stopped
exponential process satisfies `|E G_κ - 1| ≤ 2 b e^{q/2} (q + b²)`. -/
lemma norm_integral_stopG_sub_one_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ)
    {b q : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hq : 0 ≤ q) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) :
    ‖∫ ω, (stopG Z q N ω - 1) ∂P‖ ≤ 2 * b * Real.exp (q / 2) * (q + b ^ 2) := by
  have hZm := measurable_Z hM
  set c : ℕ → Ω → ℂ := fun k ω => ((stopInd Z q k ω : ℝ) : ℂ) * stopG Z q k ω with hcdef
  have hc : ∀ k, StronglyMeasurable[𝒢 k] (c k) := fun k =>
    ((Complex.measurable_ofReal.comp (measurable_stopInd (measurable_Z_filtration hM k))).mul
      (measurable_stopG (measurable_Z_filtration hM k))).stronglyMeasurable
  have hcb : ∀ k, k < N → ∀ ω, ‖c k ω‖ ≤ Real.exp (q / 2) := by
    intro k _ ω
    rcases stopInd_cases Z q k ω with h0 | h1
    · simp only [hcdef, h0]
      simpa using (Real.exp_pos _).le
    · simp only [hcdef, h1, Complex.ofReal_one, one_mul]
      exact norm_stopG_le (hZ0 ω) h1
  obtain ⟨hOsI, hOs0⟩ := integrable_integral_orthSum P 𝒢 Z hM N c hc hcb
  have hGm : Measurable (stopG Z q N) := measurable_stopG fun i _ => hZm i
  have hSN : ∀ ω, stopS Z q N ω ≤ q + b ^ 2 := fun ω =>
    stopS_le_of_increments hq (hZ0 ω) (fun i hi => hinc i hi ω) N le_rfl
  have hGint : Integrable (stopG Z q N) P :=
    Integrable.of_bound hGm.aestronglyMeasurable (Real.exp ((q + b ^ 2) / 2))
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_stopG]
        exact Real.exp_le_exp.2 (by linarith [hSN ω]))
  have hF : Integrable (fun ω => stopG Z q N ω - 1) P := hGint.sub (integrable_const _)
  have hFR : ∀ ω, stopG Z q N ω - 1 =
      (∑ k ∈ Finset.range N, c k ω * (stepFactor (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))) +
        Complex.I * ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ) := by
    intro ω
    rw [stopG_sub_one, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [hcdef]; ring
  have hRg : ∀ ω, ‖∑ k ∈ Finset.range N, c k ω * (stepFactor (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))‖ ≤
      2 * b * Real.exp (q / 2) * (q + b ^ 2) := by
    intro ω
    calc _ ≤ ∑ k ∈ Finset.range N, ‖c k ω * (stepFactor (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, Real.exp (q / 2) * (2 * b) *
            (stopInd Z q k ω * (Z (k + 1) ω - Z k ω) ^ 2) :=
          Finset.sum_le_sum fun k hk =>
            norm_stop_term_le (hZ0 ω) hb1 (hinc k (Finset.mem_range.1 hk) ω)
      _ = Real.exp (q / 2) * (2 * b) * stopS Z q N ω := by
          rw [← Finset.mul_sum]; rfl
      _ ≤ Real.exp (q / 2) * (2 * b) * (q + b ^ 2) :=
          mul_le_mul_of_nonneg_left (hSN ω) (by positivity)
      _ = 2 * b * Real.exp (q / 2) * (q + b ^ 2) := by ring
  have key := norm_integral_le_of_orth (P := P) (F := fun ω => stopG Z q N ω - 1)
    (Os := fun ω => ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))
    (R := fun ω => ∑ k ∈ Finset.range N, c k ω * (stepFactor (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ)))
    (g := fun _ => 2 * b * Real.exp (q / 2) * (q + b ^ 2)) hF hOsI hOs0 hFR
    (integrable_const _) hRg
  simpa using key

end Estimates

/-! ### The first term and the assembly -/

section Assembly

/-- **First term.** `|E e^{i Z_N} - E [e^{i Z_κ} e^{-(q - S_κ)/2}]| ≤ ½ E |S_N - q| + b`. -/
lemma norm_integral_first_term_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ)
    {b q : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (hq : 0 ≤ q) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) :
    ‖∫ ω, (expI (Z N ω) - ((Real.exp (-(q / 2)) : ℝ) : ℂ) * stopG Z q N ω) ∂P‖ ≤
      2⁻¹ * ∫ ω, |sqSum Z N ω - q| ∂P + b := by
  have hZm := measurable_Z hM
  set c : ℕ → Ω → ℂ := fun k ω => ((1 - stopInd Z q k ω : ℝ) : ℂ) * expI (Z k ω) with hcdef
  have hc : ∀ k, StronglyMeasurable[𝒢 k] (c k) := fun k =>
    ((Complex.measurable_ofReal.comp
        (measurable_const.sub (measurable_stopInd (measurable_Z_filtration hM k)))).mul
      (continuous_expI.measurable.comp (measurable_Z_filtration hM k k le_rfl))).stronglyMeasurable
  have hcb : ∀ k, k < N → ∀ ω, ‖c k ω‖ ≤ 1 := by
    intro k _ ω
    rcases stopInd_cases Z q k ω with h0 | h1
    · simp [hcdef, h0, norm_expI]
    · simp [hcdef, h1]
  obtain ⟨hOsI, hOs0⟩ := integrable_integral_orthSum P 𝒢 Z hM N c hc hcb
  have hSN : ∀ ω, stopS Z q N ω ≤ q + b ^ 2 := fun ω =>
    stopS_le_of_increments hq (hZ0 ω) (fun i hi => hinc i hi ω) N le_rfl
  have hGm : Measurable (stopG Z q N) := measurable_stopG fun i _ => hZm i
  have hGint : Integrable (stopG Z q N) P :=
    Integrable.of_bound hGm.aestronglyMeasurable (Real.exp ((q + b ^ 2) / 2))
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_stopG]
        exact Real.exp_le_exp.2 (by linarith [hSN ω]))
  have hEint : Integrable (fun ω => expI (Z N ω)) P :=
    Integrable.of_bound (continuous_expI.measurable.comp (hZm N)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by rw [norm_expI])
  have hF : Integrable
      (fun ω => expI (Z N ω) - ((Real.exp (-(q / 2)) : ℝ) : ℂ) * stopG Z q N ω) P :=
    hEint.sub (hGint.const_mul _)
  have hFR : ∀ ω, expI (Z N ω) - ((Real.exp (-(q / 2)) : ℝ) : ℂ) * stopG Z q N ω =
      ((∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))) +
        expI (stopZ Z q N ω) * (1 - ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ))) +
        Complex.I * ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ) := by
    intro ω
    have h1 := expI_sub_stopZ (q := q) (hZ0 ω) N
    have h2 : ((Real.exp (-(q / 2)) : ℝ) : ℂ) * stopG Z q N ω =
        expI (stopZ Z q N ω) * ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ) := by
      unfold stopG
      have h : Real.exp (-(q / 2)) * Real.exp (stopS Z q N ω / 2) =
          Real.exp ((stopS Z q N ω - q) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [← h]
      push_cast
      ring
    have h3 : ∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1) =
        (∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))) +
        Complex.I * ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h1' : expI (Z N ω) - expI (stopZ Z q N ω) =
        ∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1) := h1
    have e : expI (Z N ω) - ((Real.exp (-(q / 2)) : ℝ) : ℂ) * stopG Z q N ω =
        (expI (Z N ω) - expI (stopZ Z q N ω)) +
          expI (stopZ Z q N ω) * (1 - ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ)) := by
      rw [h2]; ring
    rw [e, h1', h3]
    ring
  have hSmeas : Measurable (sqSum Z N) := measurable_sqSum fun i _ => hZm i
  have hAbsInt : Integrable (fun ω => |sqSum Z N ω - q|) P :=
    Integrable.of_bound
      (continuous_abs.measurable.comp (hSmeas.sub_const q)).aestronglyMeasurable
      (N * b ^ 2 + q) (Filter.Eventually.of_forall fun ω => by
        have h0 := sqSum_nonneg Z N ω
        have h1 := sqSum_le_of_increments (Z := Z) (b := b) (N := N) (ω := ω)
          (fun i hi => hinc i hi ω)
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_le.2 ⟨by linarith, by linarith⟩)
  have hgInt : Integrable (fun ω => |sqSum Z N ω - q| / 2 + b) P :=
    (hAbsInt.div_const 2).add (integrable_const b)
  have hRg : ∀ ω, ‖(∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))) +
        expI (stopZ Z q N ω) * (1 - ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ))‖ ≤
      |sqSum Z N ω - q| / 2 + b := by
    intro ω
    have hcase : (stopS Z q N ω = sqSum Z N ω ∧ sqSum Z N ω < q) ∨
        (q ≤ stopS Z q N ω ∧ stopS Z q N ω ≤ q + b ^ 2 ∧ stopS Z q N ω ≤ sqSum Z N ω) := by
      rcases stopInd_cases Z q N ω with h0 | h1
      · exact Or.inr ⟨le_stopS_of_stopInd_eq_zero (hZ0 ω) N h0, hSN ω,
          stopS_le_sqSum Z q N ω⟩
      · exact Or.inl ⟨(stopZ_stopS_of_stopInd (hZ0 ω) N h1).2, sqSum_lt_of_stopInd h1⟩
    have hP := pointwise_real hb0 hb1 hcase
    have hsum : ∑ k ∈ Finset.range N, (1 - stopInd Z q k ω) * ((Z (k + 1) ω - Z k ω) ^ 2 / 2)
        = (sqSum Z N ω - stopS Z q N ω) / 2 := by
      rw [sqSum_sub_stopS, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hF2 : ‖expI (stopZ Z q N ω) * (1 - ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ))‖
        = |1 - Real.exp ((stopS Z q N ω - q) / 2)| := by
      rw [norm_mul, norm_expI, one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ ‖∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))‖ +
        ‖expI (stopZ Z q N ω) * (1 - ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ))‖ :=
          norm_add_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (1 - stopInd Z q k ω) * ((Z (k + 1) ω - Z k ω) ^ 2 / 2) +
          |1 - Real.exp ((stopS Z q N ω - q) / 2)| := by
          rw [hF2]
          refine add_le_add ?_ le_rfl
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          exact norm_stop_term_le'
      _ ≤ |sqSum Z N ω - q| / 2 + b := by rw [hsum]; exact hP
  have key := norm_integral_le_of_orth (P := P)
    (F := fun ω => expI (Z N ω) - ((Real.exp (-(q / 2)) : ℝ) : ℂ) * stopG Z q N ω)
    (Os := fun ω => ∑ k ∈ Finset.range N, c k ω * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))
    (R := fun ω => (∑ k ∈ Finset.range N, c k ω * (expI (Z (k + 1) ω - Z k ω) - 1 -
          Complex.I * ((Z (k + 1) ω - Z k ω : ℝ) : ℂ))) +
        expI (stopZ Z q N ω) * (1 - ((Real.exp ((stopS Z q N ω - q) / 2) : ℝ) : ℂ)))
    (g := fun ω => |sqSum Z N ω - q| / 2 + b) hF hOsI hOs0 hFR hgInt hRg
  have hgI : ∫ ω, (|sqSum Z N ω - q| / 2 + b) ∂P = 2⁻¹ * ∫ ω, |sqSum Z N ω - q| ∂P + b := by
    rw [integral_add (hAbsInt.div_const 2) (integrable_const b), integral_div, integral_const]
    simp [div_eq_inv_mul]
  rw [hgI] at key
  exact key

/-- **The discrete characteristic-function estimate.** -/
theorem discrete_cf_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ) {b q : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hq : 0 ≤ q) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) :
    ‖∫ ω, expI (Z N ω) ∂P - Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
      2⁻¹ * ∫ ω, |sqSum Z N ω - q| ∂P + 4 * b * (1 + q) := by
  have hZm := measurable_Z hM
  have hA := norm_integral_first_term_le P 𝒢 Z N hb0 hb1 hq hM hZ0 hinc
  have hB := norm_integral_stopG_sub_one_le P 𝒢 Z N hb0.le hb1 hq hM hZ0 hinc
  have hSN : ∀ ω, stopS Z q N ω ≤ q + b ^ 2 := fun ω =>
    stopS_le_of_increments hq (hZ0 ω) (fun i hi => hinc i hi ω) N le_rfl
  have hGm : Measurable (stopG Z q N) := measurable_stopG fun i _ => hZm i
  have hGint : Integrable (stopG Z q N) P :=
    Integrable.of_bound hGm.aestronglyMeasurable (Real.exp ((q + b ^ 2) / 2))
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_stopG]
        exact Real.exp_le_exp.2 (by linarith [hSN ω]))
  have hEint : Integrable (fun ω => expI (Z N ω)) P :=
    Integrable.of_bound (continuous_expI.measurable.comp (hZm N)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by rw [norm_expI])
  set c0 : ℂ := ((Real.exp (-(q / 2)) : ℝ) : ℂ) with hc0
  have hexp : Complex.exp ((-(q / 2) : ℝ) : ℂ) = c0 := (Complex.ofReal_exp _).symm
  have hident : ∫ ω, expI (Z N ω) ∂P - c0 =
      ∫ ω, (expI (Z N ω) - c0 * stopG Z q N ω) ∂P + c0 * ∫ ω, (stopG Z q N ω - 1) ∂P := by
    rw [integral_sub hEint (hGint.const_mul c0), integral_const_mul,
      integral_sub hGint (integrable_const _), integral_const]
    simp
    ring
  rw [hexp, hident]
  have hc0n : ‖c0‖ = Real.exp (-(q / 2)) := by
    rw [hc0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hprod : Real.exp (-(q / 2)) * Real.exp (q / 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc _ ≤ ‖∫ ω, (expI (Z N ω) - c0 * stopG Z q N ω) ∂P‖ +
        ‖c0 * ∫ ω, (stopG Z q N ω - 1) ∂P‖ := norm_add_le _ _
    _ ≤ (2⁻¹ * ∫ ω, |sqSum Z N ω - q| ∂P + b) +
        Real.exp (-(q / 2)) * (2 * b * Real.exp (q / 2) * (q + b ^ 2)) := by
        refine add_le_add hA ?_
        rw [norm_mul, hc0n]
        exact mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
    _ = (2⁻¹ * ∫ ω, |sqSum Z N ω - q| ∂P + b) + 2 * b * (q + b ^ 2) := by
        have : Real.exp (-(q / 2)) * (2 * b * Real.exp (q / 2) * (q + b ^ 2))
            = (Real.exp (-(q / 2)) * Real.exp (q / 2)) * (2 * b * (q + b ^ 2)) := by ring
        rw [this, hprod, one_mul]
    _ ≤ 2⁻¹ * ∫ ω, |sqSum Z N ω - q| ∂P + 4 * b * (1 + q) := by
        have hb2 : b ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_nonneg hb0.le hq, mul_nonneg hb0.le (sub_nonneg.2 hb2)]

/-- **The discrete characteristic-function bound for martingales with small increments**
(`DiscreteCFBound`). -/
theorem discreteCFBound_holds : DiscreteCFBound := by
  intro Ω _ P _ 𝒢 Z N b q hb0 hb1 hq hM hZ0 hinc
  exact discrete_cf_bound P 𝒢 Z N hb0 hb1 hq hM hZ0 hinc

end Assembly


end

end LatticeProb.Process.BdgUpperContinuous.DdsDiscrete
