/-
# The `n`-dimensional Ornstein–Uhlenbeck layer for the Gaussian log-Sobolev route

`LatticeProb.GaussianLogSobolev n` (`LatticeProb/External/GaussianLogSobolev.lean`) is the cited
Gaussian log-Sobolev inequality; `Prob/GaussianLogSobolevOU.lean` lands the `n = 1` Ornstein–Uhlenbeck
(Mehler) semigroup `ouSemigroup`, the generator `ouGenerator`, and the named open input
`OUHeatEquation` (`∂_t P_t f = L P_t f` on `ℝ`).

This file continues the route to general `n`.  It defines the `n`-dimensional Mehler semigroup and
generator and proves the **tensorisation of the generator identity**: on functions of a single
coordinate the `n`-dimensional heat equation reduces to the `1`-dimensional `OUHeatEquation`.  The
general case is the single named open input `OUHeatEquationN`.

* `ouSemigroupN n t f x = ∫ z, f (fun i => e^{-t} x_i + √(1 - e^{-2t}) z_i) ∂γ_n(z)`,
  `γ_n = Measure.pi (fun _ : Fin n => gaussianReal 0 1)`;
* `ouGeneratorN n f x = Σ_i (∂_i² f x - x_i ∂_i f x)`, written through `Function.update` and the
  `1`-dimensional `ouGenerator`;
* `ouSemigroupN_zero`, `ouSemigroupN_const`, `ouSemigroupN_const_mul` — the structural identities;
* `ouSemigroupN_comp_eval` — `P_t^{(n)}(g ∘ π_i) = (P_t g) ∘ π_i` (the marginal of the product law);
* `ouGeneratorN_comp_eval` — `L_n (g ∘ π_i) = (L g) ∘ π_i`;
* `OUHeatEquationN n` — the named open input (the general heat equation);
* `ouHeatEquationN_comp_eval` — the tensorisation: the `n`-dimensional heat equation on a
  coordinate function follows from the `1`-dimensional `OUHeatEquation`.

Nothing is conditional on `sorry`; `OUHeatEquationN` is a named `Prop`, never an axiom.
-/
import LatticeProb.Prob.GaussianLogSobolevOU

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

noncomputable section

/-- **The `n`-dimensional Ornstein–Uhlenbeck (Mehler) semigroup**
`P_t f x = ∫ z, f (fun i => e^{-t} x_i + √(1 - e^{-2t}) z_i) ∂γ_n(z)`, where
`γ_n = Measure.pi fun _ : Fin n => gaussianReal 0 1`. -/
def ouSemigroupN (n : ℕ) (t : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∫ z, f (fun i => Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * z i)
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

/-- **The `n`-dimensional Ornstein–Uhlenbeck generator** `L f = Σ_i (∂_i² f - x_i ∂_i f)`,
written through the one-dimensional `ouGenerator` by freezing all coordinates but one. -/
def ouGeneratorN (n : ℕ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ i, ouGenerator (fun y => f (Function.update x i y)) (x i)

/-! ### Structural identities -/

/-- **`P_0` is the identity.** -/
theorem ouSemigroupN_zero (n : ℕ) (f : (Fin n → ℝ) → ℝ) : ouSemigroupN n 0 f = f := by
  funext x
  simp only [ouSemigroupN]
  rw [show (fun z : Fin n → ℝ => f (fun i => Real.exp (-(0 : ℝ)) * x i
        + Real.sqrt (1 - Real.exp (-2 * 0)) * z i)) = fun _ => f x by
      funext z
      congr 1
      funext i
      norm_num]
  simp

/-- **`P_t` preserves constants** (the Mehler kernel is a probability kernel). -/
theorem ouSemigroupN_const (n : ℕ) (t : ℝ) (c : ℝ) :
    ouSemigroupN n t (fun _ => c) = fun _ => c := by
  funext x
  simp only [ouSemigroupN]
  simp

/-- **The Mehler semigroup preserves the constant `1`.** -/
theorem ouSemigroupN_one (n : ℕ) (t : ℝ) :
    ouSemigroupN n t (fun _ => (1 : ℝ)) = fun _ => 1 :=
  ouSemigroupN_const n t 1

/-- **Homogeneity of the Mehler semigroup.** -/
theorem ouSemigroupN_const_mul (n : ℕ) (t c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    ouSemigroupN n t (fun x => c * f x) = fun x => c * ouSemigroupN n t f x := by
  funext x
  simp only [ouSemigroupN]
  rw [← integral_const_mul]

/-! ### Tensorisation -/

/-- **Marginal of the product Gaussian law.**  The `n`-dimensional Mehler semigroup on a function
of one coordinate is the `1`-dimensional semigroup of that coordinate: the other coordinates
integrate out because `Measure.pi` of probability measures has marginal `gaussianReal 0 1`. -/
theorem ouSemigroupN_comp_eval (n : ℕ) (t : ℝ) (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g) :
    ouSemigroupN n t (fun x => g (x i)) = fun x => ouSemigroup t g (x i) := by
  funext x
  simp only [ouSemigroupN, ouSemigroup]
  have hmap : Measure.map (fun z : Fin n → ℝ => z i)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) = gaussianReal 0 1 := by
    rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, Measure.pi_map_eval]
    simp [measure_univ]
  let φ : (Fin n → ℝ) → ℝ := fun z => z i
  have hG : AEStronglyMeasurable (fun y : ℝ => g (Real.exp (-t) * x i
      + Real.sqrt (1 - Real.exp (-2 * t)) * y))
      (Measure.map φ (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    rw [show Measure.map φ (Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = gaussianReal 0 1 from hmap]
    exact (hg.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  have h1 : (∫ z : Fin n → ℝ, g (Real.exp (-t) * x i
        + Real.sqrt (1 - Real.exp (-2 * t)) * z i)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      = ∫ y : ℝ, g (Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * y)
        ∂(Measure.map φ (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
    (integral_map (φ := φ) (hφ := (measurable_pi_apply i).aemeasurable) (hfm := hG)).symm
  rw [h1, show Measure.map φ (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = gaussianReal 0 1 from hmap]

/-- **Tensorisation of the generator.**  The `n`-dimensional generator on a function of one
coordinate is the `1`-dimensional generator of that coordinate: all other partial derivatives
vanish. -/
theorem ouGeneratorN_comp_eval (n : ℕ) (i : Fin n) (g : ℝ → ℝ) :
    ouGeneratorN n (fun x => g (x i)) = fun x => ouGenerator g (x i) := by
  funext x
  simp only [ouGeneratorN]
  have hsum : (∑ j, ouGenerator
        (fun y => (fun x' : Fin n → ℝ => g (x' i)) (Function.update x j y)) (x j))
      = ouGenerator (fun y => (fun x' : Fin n → ℝ => g (x' i))
          (Function.update x i y)) (x i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hji
      have hconst : (fun y : ℝ => (fun x' : Fin n → ℝ => g (x' i))
          (Function.update x j y)) = fun _ => g (x i) := by
        funext y
        change g ((Function.update x j y) i) = g (x i)
        rw [Function.update_of_ne (a := i) (a' := j) (Ne.symm hji) y x]
      rw [hconst]
      simp [ouGenerator]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  congr 1
  funext y
  change g ((Function.update x i y) i) = g y
  rw [Function.update_self]

/-! ### The named open input and its tensorisation -/

/-- **The `n`-dimensional Ornstein–Uhlenbeck heat equation** `∂_t P_t f = L P_t f`, for smooth
compactly supported `f`.  This is the named open input of the general-`n` OU layer, generalising
`OUHeatEquation` from `Prob/GaussianLogSobolevOU.lean`. -/
def OUHeatEquationN (n : ℕ) : Prop :=
  ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∀ t : ℝ, 0 < t → ∀ x : Fin n → ℝ,
      HasDerivAt (fun s => ouSemigroupN n s f x) (ouGeneratorN n (ouSemigroupN n t f) x) t

/-- **The tensorisation of the heat equation.**  On a function of one coordinate, the
`n`-dimensional heat equation is the `1`-dimensional `OUHeatEquation`: the semigroup and the
generator both reduce to their `1`-dimensional counterparts by `ouSemigroupN_comp_eval` and
`ouGeneratorN_comp_eval`.  This is the bounded sub-lemma of the `n`-dimensional OU layer; the
general case is `OUHeatEquationN`. -/
theorem ouHeatEquationN_comp_eval (n : ℕ) (h1 : OUHeatEquation)
    (i : Fin n) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∀ t : ℝ, 0 < t → ∀ x : Fin n → ℝ,
      HasDerivAt (fun s => ouSemigroupN n s (fun x' => g (x' i)) x)
        (ouGeneratorN n (ouSemigroupN n t (fun x' => g (x' i))) x) t := by
  intro t ht x
  have hsem : (fun s => ouSemigroupN n s (fun x' => g (x' i)) x)
      = fun s => ouSemigroup s g (x i) :=
    funext fun s => congrFun (ouSemigroupN_comp_eval n s i g hg.continuous.measurable) x
  have hgen : ouGeneratorN n (ouSemigroupN n t (fun x' => g (x' i))) x
      = ouGenerator (ouSemigroup t g) (x i) := by
    rw [ouSemigroupN_comp_eval n t i g hg.continuous.measurable]
    exact congrFun (ouGeneratorN_comp_eval n i (ouSemigroup t g)) x
  rw [hsem, hgen]
  exact h1 g hg hgc t ht (x i)

/-- **Tensorisation of the semigroup on product functions.**  On a tensor product
`f x = ∏ i, g i (x i)` the `n`-dimensional Mehler semigroup factorises into the product of the
`1`-dimensional semigroups: the product Gaussian law is a product measure, so
`integral_fintype_prod_eq_prod` applies. -/
theorem ouSemigroupN_prod (n : ℕ) (t : ℝ) (g : Fin n → ℝ → ℝ) :
    ouSemigroupN n t (fun x => ∏ i, g i (x i))
      = fun x => ∏ i, ouSemigroup t (g i) (x i) := by
  funext x
  simp only [ouSemigroupN, ouSemigroup]
  rw [show (∫ z : Fin n → ℝ, ∏ i, g i (Real.exp (-t) * x i
        + Real.sqrt (1 - Real.exp (-2 * t)) * z i)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      = ∏ i, ∫ y : ℝ, g i (Real.exp (-t) * x i
        + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂(gaussianReal 0 1) from
    integral_fintype_prod_eq_prod (fun i y => g i (Real.exp (-t) * x i
      + Real.sqrt (1 - Real.exp (-2 * t)) * y))]

end

end LatticeProb
