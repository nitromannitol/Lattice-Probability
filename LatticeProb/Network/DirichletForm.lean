/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedWalk/DirichletSpace.lean.
-/
import LatticeProb.Network.Conductance
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Finite-energy functions and the Dirichlet form

Let `G` be a conductance graph. A function `f : V → ℝ` has finite energy when
`G.HasFiniteEnergy f`, that is, when the ordered-pair contributions `c(x,y) (f y - f x) ^ 2` are
summable. This file collects the algebra of such functions:

* `gradSq_add_le`, `gradSq_smul`, `gradSq_neg`, `gradSq_add_const`, `gradSq_sub_const`,
  `gradSq_const`: how the energy summand behaves under the linear operations and under adding
  constants.
* `hasFiniteEnergy_const`, `hasFiniteEnergy_zero`, and the lemmas `HasFiniteEnergy.add`,
  `.smul`, `.neg`, `.sub`, `.add_const`, `.sub_const`: finite-energy functions are closed under
  these operations.
* `Energy_add_const`, `Energy_sub_const`, `Energy_const`, `Energy_neg`: the energy is invariant
  under adding and subtracting constants, and under negation.
* `gradProd`, `dirichletForm`: the Dirichlet form `½ ∑ c(x,y) (f y - f x) (g y - g x)`. It is
  symmetric, it is additive and homogeneous in its first argument, and its diagonal is `Energy`.
* `dirichletSubmodule G a₀`: the finite-energy functions vanishing at `a₀`, as a submodule of
  `V → ℝ`.
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Algebra of finite-energy functions -/

/-- The energy summand of `f + g` is at most twice the sum of the energy summands of `f` and `g`. -/
lemma gradSq_add_le (f g : V → ℝ) (p : V × V) :
    G.gradSq (f + g) p ≤ 2 * G.gradSq f p + 2 * G.gradSq g p := by
  simp only [gradSq, Pi.add_apply]
  have hc := G.c_nonneg p.1 p.2
  nlinarith [mul_nonneg hc (sq_nonneg ((f p.2 - f p.1) - (g p.2 - g p.1)))]

/-- Scaling a function by `a` scales the energy summand by `a ^ 2`. -/
lemma gradSq_smul (a : ℝ) (f : V → ℝ) (p : V × V) :
    G.gradSq (a • f) p = a ^ 2 * G.gradSq f p := by
  simp only [gradSq, Pi.smul_apply, smul_eq_mul]; ring

/-- The energy summand of `-f` equals that of `f`. -/
lemma gradSq_neg (f : V → ℝ) (p : V × V) : G.gradSq (-f) p = G.gradSq f p := by
  simp only [gradSq, Pi.neg_apply]; ring

/-- Adding a constant does not change the gradient. -/
lemma gradSq_add_const (f : V → ℝ) (a : ℝ) (p : V × V) :
    G.gradSq (fun x => f x + a) p = G.gradSq f p := by
  simp only [gradSq]; ring

/-- Subtracting a constant does not change the gradient. -/
lemma gradSq_sub_const (f : V → ℝ) (a : ℝ) (p : V × V) :
    G.gradSq (fun x => f x - a) p = G.gradSq f p := by
  simp only [gradSq]; ring

/-- A constant function has zero energy summand at every ordered pair. -/
lemma gradSq_const (a : ℝ) (p : V × V) : G.gradSq (fun _ => a) p = 0 := by
  simp [gradSq]

/-- Constant functions have finite energy. -/
lemma hasFiniteEnergy_const (a : ℝ) : G.HasFiniteEnergy (fun _ => a) :=
  summable_zero.congr fun p => (G.gradSq_const a p).symm

/-- The zero function has finite energy. -/
lemma hasFiniteEnergy_zero : G.HasFiniteEnergy (0 : V → ℝ) := G.hasFiniteEnergy_const 0

section FiniteEnergyAlgebra

variable {G}

/-- Finite-energy functions are closed under addition. -/
lemma HasFiniteEnergy.add {f g : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) : G.HasFiniteEnergy (f + g) :=
  Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg _ p) (fun p => G.gradSq_add_le f g p)
    ((hf.mul_left 2).add (hg.mul_left 2))

/-- Finite-energy functions are closed under scalar multiplication. -/
lemma HasFiniteEnergy.smul {f : V → ℝ} (hf : G.HasFiniteEnergy f) (a : ℝ) :
    G.HasFiniteEnergy (a • f) :=
  (hf.mul_left (a ^ 2)).congr fun p => (G.gradSq_smul a f p).symm

/-- Finite-energy functions are closed under negation. -/
lemma HasFiniteEnergy.neg {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    G.HasFiniteEnergy (-f) :=
  hf.congr fun p => (G.gradSq_neg f p).symm

/-- Finite-energy functions are closed under subtraction. -/
lemma HasFiniteEnergy.sub {f g : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) : G.HasFiniteEnergy (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- Finite-energy functions are closed under adding a constant. -/
lemma HasFiniteEnergy.add_const {f : V → ℝ} (hf : G.HasFiniteEnergy f) (a : ℝ) :
    G.HasFiniteEnergy (fun x => f x + a) :=
  hf.congr fun p => (G.gradSq_add_const f a p).symm

/-- Finite-energy functions are closed under subtracting a constant. -/
lemma HasFiniteEnergy.sub_const {f : V → ℝ} (hf : G.HasFiniteEnergy f) (a : ℝ) :
    G.HasFiniteEnergy (fun x => f x - a) :=
  hf.congr fun p => (G.gradSq_sub_const f a p).symm

end FiniteEnergyAlgebra

/-- Energy is translation invariant. -/
lemma Energy_add_const (f : V → ℝ) (a : ℝ) : G.Energy (fun x => f x + a) = G.Energy f := by
  unfold Energy
  simp_rw [G.gradSq_add_const f a]

/-- Subtracting a constant does not change the energy. -/
lemma Energy_sub_const (f : V → ℝ) (a : ℝ) : G.Energy (fun x => f x - a) = G.Energy f := by
  unfold Energy
  simp_rw [G.gradSq_sub_const f a]

/-- A constant function has zero energy. -/
lemma Energy_const (a : ℝ) : G.Energy (fun _ => a) = 0 := by
  unfold Energy
  simp_rw [G.gradSq_const a]
  simp

/-- Negation does not change the energy. -/
lemma Energy_neg (f : V → ℝ) : G.Energy (-f) = G.Energy f := by
  unfold Energy
  simp_rw [G.gradSq_neg f]

/-! ### The Dirichlet form -/

/-- The contribution of one ordered pair to the Dirichlet form
`½ ∑ c(x,y)(f y − f x)(g y − g x)`. -/
noncomputable def gradProd (f g : V → ℝ) (p : V × V) : ℝ :=
  G.c p.1 p.2 * ((f p.2 - f p.1) * (g p.2 - g p.1))

/-- On the diagonal, the summand of the Dirichlet form is the energy summand. -/
lemma gradProd_self (f : V → ℝ) (p : V × V) : G.gradProd f f p = G.gradSq f p := by
  simp only [gradProd, gradSq, sq]

/-- The summand of the Dirichlet form is symmetric in its two arguments. -/
lemma gradProd_comm (f g : V → ℝ) (p : V × V) : G.gradProd f g p = G.gradProd g f p := by
  simp only [gradProd, mul_comm]

/-- The summand of the Dirichlet form is additive in its first argument. -/
lemma gradProd_add_left (f g k : V → ℝ) (p : V × V) :
    G.gradProd (f + g) k p = G.gradProd f k p + G.gradProd g k p := by
  simp only [gradProd, Pi.add_apply]; ring

/-- The summand of the Dirichlet form is homogeneous in its first argument. -/
lemma gradProd_smul_left (a : ℝ) (f g : V → ℝ) (p : V × V) :
    G.gradProd (a • f) g p = a * G.gradProd f g p := by
  simp only [gradProd, Pi.smul_apply, smul_eq_mul]; ring

/-- The pointwise Cauchy–Schwarz bound `|c·ab| ≤ c(a² + b²)/2`. -/
lemma abs_gradProd_le (f g : V → ℝ) (p : V × V) :
    |G.gradProd f g p| ≤ (G.gradSq f p + G.gradSq g p) / 2 := by
  simp only [gradProd, gradSq]
  have hc := G.c_nonneg p.1 p.2
  rw [abs_mul, abs_of_nonneg hc, abs_mul]
  have h1 : |f p.2 - f p.1| * |g p.2 - g p.1|
      ≤ ((f p.2 - f p.1) ^ 2 + (g p.2 - g p.1) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f p.2 - f p.1| - |g p.2 - g p.1|), sq_abs (f p.2 - f p.1),
      sq_abs (g p.2 - g p.1)]
  calc G.c p.1 p.2 * (|f p.2 - f p.1| * |g p.2 - g p.1|)
      ≤ G.c p.1 p.2 * (((f p.2 - f p.1) ^ 2 + (g p.2 - g p.1) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = _ := by ring

/-- The Dirichlet form of two finite-energy functions is absolutely summable. -/
lemma summable_gradProd {f g : V → ℝ} (hf : G.HasFiniteEnergy f) (hg : G.HasFiniteEnergy g) :
    Summable (G.gradProd f g) :=
  Summable.of_norm_bounded ((Summable.add hf hg).div_const 2) (fun p => by
    rw [Real.norm_eq_abs]; exact G.abs_gradProd_le f g p)

/-- The Dirichlet form `⟪f, g⟫ = ½ ∑_{(x,y)} c(x,y)(f y − f x)(g y − g x)`, whose quadratic
form is the Dirichlet energy. -/
noncomputable def dirichletForm (f g : V → ℝ) : ℝ := (∑' p : V × V, G.gradProd f g p) / 2

/-- The Dirichlet form of a function with itself is its energy. -/
lemma dirichletForm_self (f : V → ℝ) : G.dirichletForm f f = G.Energy f := by
  unfold dirichletForm Energy
  simp_rw [G.gradProd_self f]

/-- The Dirichlet form is symmetric. -/
lemma dirichletForm_comm (f g : V → ℝ) : G.dirichletForm f g = G.dirichletForm g f := by
  unfold dirichletForm
  simp_rw [G.gradProd_comm f g]

/-- The Dirichlet form is additive in its first argument, for finite-energy functions. -/
lemma dirichletForm_add_left {f g k : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) (hk : G.HasFiniteEnergy k) :
    G.dirichletForm (f + g) k = G.dirichletForm f k + G.dirichletForm g k := by
  unfold dirichletForm
  simp_rw [G.gradProd_add_left f g k]
  rw [(G.summable_gradProd hf hk).tsum_add (G.summable_gradProd hg hk), add_div]

/-- The Dirichlet form is homogeneous in its first argument. -/
lemma dirichletForm_smul_left (a : ℝ) (f g : V → ℝ) :
    G.dirichletForm (a • f) g = a * G.dirichletForm f g := by
  unfold dirichletForm
  simp_rw [G.gradProd_smul_left a f g]
  rw [tsum_mul_left, mul_div_assoc]

/-! ### The finite-energy submodule -/

/-- The finite-energy functions vanishing at `a₀`, as a submodule of `V → ℝ`. -/
def dirichletSubmodule (a₀ : V) : Submodule ℝ (V → ℝ) where
  carrier := {f | G.HasFiniteEnergy f ∧ f a₀ = 0}
  add_mem' := fun {f g} hf hg =>
    ⟨hf.1.add hg.1, by simp only [Pi.add_apply, hf.2, hg.2, add_zero]⟩
  zero_mem' := ⟨G.hasFiniteEnergy_zero, rfl⟩
  smul_mem' := fun a {f} hf => ⟨hf.1.smul a, by simp only [Pi.smul_apply, hf.2, smul_zero]⟩

end ConductanceGraph

end LatticeProb.Network
