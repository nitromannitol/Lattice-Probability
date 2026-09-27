import Mathlib

/-!
# The Gaussian log-Sobolev inequality and the Herbst bound

The Gaussian logarithmic Sobolev inequality and the exponential moment bound it
implies, the classical input from outside the papers that the Gaussian
concentration inequality rests on.

`LatticeProb.GaussianLogSobolev n` is the inequality for the standard Gaussian
product law `γ = Measure.pi fun _ : Fin n => gaussianReal 0 1` on `Fin n → ℝ`:
for a positive `h` with `∫ h ∂γ = 1` whose logarithm is `C`-Lipschitz, the
entropy `∫ h log h ∂γ` is at most `C² / 2`.  It is the Gross/Stam/Bakry–Émery
inequality in the finite-dimensional Gaussian case, read through the Rademacher
bound `‖∇ log h‖ ≤ C`.

`LatticeProb.GaussianHerbstBound n` is the Herbst consequence of it, in the form
the Chernoff step consumes: for an `L`-Lipschitz `f`, the moment generating
function of `f - ∫ f` is at most `exp (λ² L² / 2)` for every `λ > 0`.  The
library proves the passage from this bound to the concentration inequality of
Tsirelson–Ibragimov–Sudakov (`LatticeProb.gaussian_lipschitz_concentration`);
the bound itself is cited.

These are cited results, carried as explicit hypotheses of the theorems that use
them, never as axioms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The Gaussian logarithmic Sobolev inequality** on `Fin n → ℝ`, for the
standard Gaussian product law, in the Herbst form.  Cited from Gross (1975) and
Bakry–Émery (1985). -/
def GaussianLogSobolev (n : ℕ) : Prop :=
  ∀ h : (Fin n → ℝ) → ℝ, (∀ x, 0 < h x) →
    Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1) →
    ∀ C : NNReal, LipschitzWith C (fun x => Real.log (h x)) →
    ∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ (C : ℝ) ^ 2 / 2

/-- **The Herbst exponential moment bound** for a Lipschitz functional of `n`
independent standard Gaussians.  Cited from Gross (1975) through the Herbst
argument; it is the input of the Chernoff step that yields the concentration
inequality of Tsirelson–Ibragimov–Sudakov. -/
def GaussianHerbstBound (n : ℕ) : Prop :=
  ∀ (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L), LipschitzWith ⟨L, hL.le⟩ f →
    ∀ lam : ℝ, 0 < lam →
      ∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        ≤ Real.exp (lam ^ 2 * L ^ 2 / 2)

/-- The `n = 0` case of the Gaussian log-Sobolev inequality: the space is a single point. -/
theorem gaussianLogSobolev_zero : GaussianLogSobolev 0 := by
  intro h hpos hint hintlog hnorm C hLip
  haveI : Subsingleton (Fin 0 → ℝ) := inferInstance
  have h_eq : h = fun _ => h (fun _ => 0) :=
    funext (fun x => congrArg h (Subsingleton.elim x _))
  have h1 : ∫ y, h y ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) = h (fun _ => 0) := by
    rw [h_eq, MeasureTheory.integral_const]
    simp
  have hc : h (fun _ => 0) = 1 := by linarith [hnorm, h1]
  have hconst : ∀ x : Fin 0 → ℝ, h x = 1 := fun x => by rw [h_eq]; exact hc
  have hzero : ∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) = 0 := by
    simp [hconst]
  rw [hzero]
  positivity

/-- The `n = 0` case of the Herbst bound: the space is a single point. -/
theorem gaussianHerbstBound_zero : GaussianHerbstBound 0 := by
  intro f L hL hLip lam hlam
  haveI : Subsingleton (Fin 0 → ℝ) := inferInstance
  have hconst : ∀ x : Fin 0 → ℝ, f x = f (fun _ => 0) :=
    fun x => congrArg f (Subsingleton.elim x _)
  have hzero : ∀ x : Fin 0 → ℝ,
      f x - ∫ y, f y ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) = 0 := by
    intro x
    simp [hconst]
  simp only [hzero, mul_zero, Real.exp_zero]
  have h1 : ∫ x, (1 : ℝ) ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) = 1 := by
    simp
  rw [h1]
  exact Real.one_le_exp (by positivity)

end LatticeProb
