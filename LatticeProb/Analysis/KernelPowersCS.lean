import LatticeProb.Prob.CauchySchwarzTsum

/-!
# Diagonal control of symmetric Markov kernel powers

Powers use counting measure and right convolution. Stochasticity supplies all summability
needed for associativity and the Cauchy–Schwarz estimate.
-/

namespace LatticeProb

noncomputable section

variable {X : Type*}

/-- Right convolution of real kernels with respect to counting measure. -/
def kernelComp (A B : X → X → ℝ) (x y : X) : ℝ := ∑' z, A x z * B z y

/-- The identity kernel at time zero and iterated right convolution at positive times. -/
def kernelPow (K : X → X → ℝ) : ℕ → X → X → ℝ
  | 0, x, y => by classical exact if x = y then 1 else 0
  | n + 1, x, y => kernelComp (kernelPow K n) K x y

/-- Convolution preserves nonnegativity. -/
lemma kernelComp_nonneg {A B : X → X → ℝ} (hA : ∀ x y, 0 ≤ A x y)
    (hB : ∀ x y, 0 ≤ B x y) (x y : X) : 0 ≤ kernelComp A B x y :=
  tsum_nonneg fun z => mul_nonneg (hA x z) (hB z y)

/-- The joint summation defining convolution has finite total mass. -/
lemma kernelComp_summable_prod {A B : X → X → ℝ}
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (sA : ∀ x, HasSum (A x) 1) (sB : ∀ x, HasSum (B x) 1) (x : X) :
    Summable (fun p : X × X => A x p.1 * B p.1 p.2) := by
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (hA x p.1) (hB p.1 p.2))).2
  constructor
  · intro z
    exact (sB z).summable.mul_left (A x z)
  · simpa only [tsum_mul_left, (sB _).tsum_eq, mul_one] using (sA x).summable

/-- Convolution of stochastic kernels is stochastic. -/
lemma kernelComp_hasSum {A B : X → X → ℝ}
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (sA : ∀ x, HasSum (A x) 1) (sB : ∀ x, HasSum (B x) 1) (x : X) :
    HasSum (kernelComp A B x) 1 := by
  have h := kernelComp_summable_prod hA hB sA sB x
  have hs : Summable (kernelComp A B x) := h.prod_symm.prod
  apply hs.hasSum_iff.mpr
  change (∑' y, ∑' z, A x z * B z y) = 1
  rw [h.tsum_comm]
  simpa only [tsum_mul_left, (sB _).tsum_eq, mul_one] using (sA x).tsum_eq

/-- Each entry of a nonnegative stochastic kernel is at most one. -/
lemma kernel_entry_le_one {A : X → X → ℝ} (hA : ∀ x y, 0 ≤ A x y)
    (sA : ∀ x, HasSum (A x) 1) (x y : X) : A x y ≤ 1 := by
  simpa only [(sA x).tsum_eq] using (sA x).summable.le_tsum y (fun z _ => hA x z)

/-- Stochastic convolution is associative; the triple summand is dominated by a joint row. -/
lemma kernelComp_assoc {A B C : X → X → ℝ}
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (hC : ∀ x y, 0 ≤ C x y) (sA : ∀ x, HasSum (A x) 1)
    (sB : ∀ x, HasSum (B x) 1) (sC : ∀ x, HasSum (C x) 1) (x y : X) :
    kernelComp (kernelComp A B) C x y = kernelComp A (kernelComp B C) x y := by
  have h : Summable (fun p : X × X => A x p.1 * B p.1 p.2 * C p.2 y) :=
    (kernelComp_summable_prod hA hB sA sB x).of_nonneg_of_le
      (fun p => mul_nonneg (mul_nonneg (hA x p.1) (hB p.1 p.2)) (hC p.2 y))
      (fun p => mul_le_of_le_one_right
        (mul_nonneg (hA x p.1) (hB p.1 p.2)) (kernel_entry_le_one hC sC p.2 y))
  simp only [kernelComp, ← tsum_mul_right, ← tsum_mul_left, ← mul_assoc]
  exact h.tsum_comm

/-- All powers of a nonnegative kernel are nonnegative. -/
lemma kernelPow_nonneg {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (n : ℕ) (x y : X) : 0 ≤ kernelPow K n x y := by
  induction n generalizing x y with
  | zero => simp only [kernelPow]; split <;> norm_num
  | succ n ih => exact kernelComp_nonneg ih hK x y

/-- All powers of a stochastic kernel have rows of total mass one. -/
lemma kernelPow_hasSum {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (n : ℕ) (x : X) : HasSum (kernelPow K n x) 1 := by
  classical
  induction n generalizing x with
  | zero => simpa only [kernelPow, eq_comm] using (hasSum_ite_eq x (1 : ℝ))
  | succ n ih => exact kernelComp_hasSum (kernelPow_nonneg hK n) hK ih sK x

/-- Rows of kernel powers are summable. -/
lemma kernelPow_summable {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (n : ℕ) (x : X) : Summable (kernelPow K n x) :=
  (kernelPow_hasSum hK sK n x).summable

/-- Rows of kernel powers sum to one. -/
lemma kernelPow_tsum {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (n : ℕ) (x : X) : ∑' y, kernelPow K n x y = 1 :=
  (kernelPow_hasSum hK sK n x).tsum_eq

/-- The semigroup identity for stochastic kernel powers. -/
lemma kernelPow_add {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (a b : ℕ) (x y : X) :
    kernelPow K (a + b) x y = ∑' z, kernelPow K a x z * kernelPow K b z y := by
  classical
  induction b generalizing x y with
  | zero => simp [kernelPow, mul_ite]
  | succ b ih =>
    change kernelComp (kernelPow K (a + b)) K x y =
      kernelComp (kernelPow K a) (kernelComp (kernelPow K b) K) x y
    have heq : kernelPow K (a + b) = kernelComp (kernelPow K a) (kernelPow K b) :=
      funext fun u => funext fun v => ih u v
    rw [heq]
    exact kernelComp_assoc (kernelPow_nonneg hK a) (kernelPow_nonneg hK b) hK
      (kernelPow_hasSum hK sK a) (kernelPow_hasSum hK sK b) sK x y

/-- Symmetry is preserved by powers of a symmetric stochastic kernel. -/
lemma kernelPow_symm {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (hS : ∀ x y, K x y = K y x)
    (n : ℕ) (x y : X) : kernelPow K n x y = kernelPow K n y x := by
  classical
  induction n generalizing x y with
  | zero => simp only [kernelPow, eq_comm]
  | succ n ih =>
    have hfirst : kernelPow K 1 = K := by
      funext u v
      simp [kernelPow, kernelComp, ite_mul]
    calc
      kernelPow K (n + 1) x y =
          ∑' z, K x z * kernelPow K n z y := by
        rw [Nat.add_comm n 1, kernelPow_add hK sK, hfirst]
      _ = kernelPow K (n + 1) y x := ?_
    change (∑' z, K x z * kernelPow K n z y) =
      ∑' z, kernelPow K n y z * K z x
    apply tsum_congr
    intro z
    rw [ih z y, hS x z, mul_comm]

/-- Rows of stochastic kernel powers have summable squares. -/
lemma kernelPow_summable_sq {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (n : ℕ) (x : X) :
    Summable (fun z => kernelPow K n x z ^ 2) := by
  apply (kernelPow_summable hK sK n x).of_nonneg_of_le (fun z => sq_nonneg _)
  intro z
  have h0 := kernelPow_nonneg hK n x z
  have h1 := kernel_entry_le_one (kernelPow_nonneg hK n) (kernelPow_hasSum hK sK n) x z
  nlinarith

/-- The squared row norm is the diagonal entry at twice the time. -/
lemma kernelPow_tsum_sq {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (hS : ∀ x y, K x y = K y x)
    (n : ℕ) (x : X) :
    (∑' z, kernelPow K n x z ^ 2) = kernelPow K (2 * n) x x := by
  rw [two_mul, kernelPow_add hK sK]
  apply tsum_congr
  intro z
  rw [kernelPow_symm hK sK hS n z x, pow_two]

/-- Cauchy–Schwarz bounds an off-diagonal power by diagonal powers at doubled times. -/
theorem kernelPow_le_sqrt_diag {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (hS : ∀ x y, K x y = K y x)
    (a b : ℕ) (x y : X) :
    kernelPow K (a + b) x y ≤
      Real.sqrt (kernelPow K (2 * a) x x) * Real.sqrt (kernelPow K (2 * b) y y) := by
  have hab : Summable (fun z => kernelPow K a x z * kernelPow K b y z) := by
    apply (kernelPow_summable hK sK a x).of_nonneg_of_le
      (fun z => mul_nonneg (kernelPow_nonneg hK a x z) (kernelPow_nonneg hK b y z))
    intro z
    exact mul_le_of_le_one_right (kernelPow_nonneg hK a x z)
      (kernel_entry_le_one (kernelPow_nonneg hK b) (kernelPow_hasSum hK sK b) y z)
  have h := tsum_mul_le_sqrt_mul_sqrt (kernelPow K a x) (kernelPow K b y)
    (kernelPow_nonneg hK a x) (kernelPow_nonneg hK b y) hab
    (kernelPow_summable_sq hK sK a x) (kernelPow_summable_sq hK sK b y)
  calc
    kernelPow K (a + b) x y =
        ∑' z, kernelPow K a x z * kernelPow K b y z := by
      rw [kernelPow_add hK sK]
      exact tsum_congr fun z => by rw [kernelPow_symm hK sK hS b z y]
    _ ≤ Real.sqrt (kernelPow K (2 * a) x x) *
        Real.sqrt (kernelPow K (2 * b) y y) := by
      simpa only [kernelPow_tsum_sq hK sK hS] using h

/-- Splitting time into its floor and ceiling halves gives the diagonal power estimate. -/
theorem kernelPow_le_sqrt_diag_half {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (sK : ∀ x, HasSum (K x) 1) (hS : ∀ x y, K x y = K y x)
    (n : ℕ) (x y : X) :
    kernelPow K n x y ≤ Real.sqrt (kernelPow K (2 * (n / 2)) x x) *
      Real.sqrt (kernelPow K (2 * ((n + 1) / 2)) y y) := by
  have hn : n / 2 + (n + 1) / 2 = n := by omega
  simpa only [hn] using kernelPow_le_sqrt_diag hK sK hS (n / 2) ((n + 1) / 2) x y

end

end LatticeProb
