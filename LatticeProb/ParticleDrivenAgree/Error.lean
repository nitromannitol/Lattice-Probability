/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Error at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
import LatticeProb.ParticleDrivenAgree.Walk

/-!
# The error field, its maximal average, and conditional expectations

The error field `w` of `eq:error-recursion`, its maximal average `w^\star`,
and the conditional expectations given the initial configuration that
Sections 3 and 4 of `parking.tex` use.

- `wErr ω k x` is `w_k(x)`: `w_0 = 0` and `w_{k+1}(x) = (P w_k)(x) +
  ∑_{y ∼ x}(I_{y,x}(U_k(y)) - U_k(y)/(2d))`.
- `wStar ω n x` is `w_n^\star(x) = E_x max_{0 ≤ j ≤ n}|w_{n-j}(X_j)|`, an
  average over the independent walk alone, so it is still a function of the
  realization.
- Conditioning on `η` is integration over the stacks and the uniform variables
  with `η` held fixed, which is what `meanUgiven` and `probGiven` do.  The law
  of the data is a product, so these are versions of the conditional
  expectation and the conditional probability given `η`.
- `shiftConf v` is the translation of a configuration by `v`; a law is
  translation invariant when it is invariant under every `shiftConf`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

/-- The stacks and the uniform variables, with the configuration removed. -/
abbrev Randomness (d : ℕ) : Type := (Site d × ℕ → Site d) × (Label d × ℕ → ℝ)

/-- The law of the stacks and the uniform variables. -/
def stackRankLaw (d : ℕ) : Measure (Randomness d) :=
  (LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d)

/-- The oriented law of the stacks and the uniform variables. -/
def orientedStackRankLaw (d : ℕ) : Measure (Randomness d) :=
  (LatticeProb.orientedStackLaw d).prod (LatticeProb.rankLaw d)

/-- `E[U_n(x) | η]`, the average over the stacks and the uniform variables with
the configuration held fixed. -/
def meanUgiven (d : ℕ) (η : Site d → ℤ) (n : ℕ) (x : Site d) : ℝ :=
  ∫ s, (U ((η, s) : Data d) n x : ℝ) ∂(stackRankLaw d)

/-- `P(E | η)` for an event `E` of the data, in the same sense. -/
def probGiven (d : ℕ) (η : Site d → ℤ) (E : Set (Data d)) : ℝ :=
  ∫ s, Set.indicator E (fun _ => (1 : ℝ)) ((η, s) : Data d) ∂(stackRankLaw d)

/-- The error field `w_k` of `eq:error-recursion`. -/
def wErr {d : ℕ} (ω : Data d) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun x => LatticeProb.walkOp (wErr ω k) x +
      ∑ y ∈ LatticeProb.nbrFinset x,
        ((LatticeProb.arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * d))

/-- `w_n^\star(x) = E_x max_{0 ≤ j ≤ n}|w_{n-j}(X_j)|`. -/
def wStar {d : ℕ} (ω : Data d) (n : ℕ) (x : Site d) : ℝ :=
  ∫ p, ⨆ j ∈ Finset.range (n + 1), |wErr ω (n - j) (walkPath x p j)| ∂(walkLaw d)

/-- The translation of a configuration by `v`. -/
def shiftConf {d : ℕ} (v : Site d) (η : Site d → ℤ) : Site d → ℤ := fun x => η (x + v)

/-- A law of configurations is translation invariant when every translation
preserves it. -/
def TranslationInvariant {d : ℕ} (μ : Measure (Site d → ℤ)) : Prop :=
  ∀ v : Site d, μ.map (shiftConf v) = μ

/-- The law of the data built from a law of configurations. -/
def dataLaw (d : ℕ) (μ : Measure (Site d → ℤ)) : Measure (Data d) :=
  μ.prod (stackRankLaw d)

end LatticeProb.ParticleDrivenAgree

end
