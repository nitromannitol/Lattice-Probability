/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Fin

/-!
# Site percolation on `ℤ^d`: definitions and statements

The `ℤ^d` percolation package that replaces the "duality" used without proof by Ding–Gwynne–Zhuang
(arXiv:2310.03996, Lemma 2.10 and Lemma 3.3, Step 3; audit HA5, finding G1). The definitions and the
statement shapes are those of HA5 (`planning/audits/HA5-inputs-appendixA-DGZ.md`, Details (c),
"The `ℤ^d` percolation package"), copied verbatim; the mathematics is HA5's Details D6–D7.

* lattice notions: `Zd`, `LAdj` (nearest neighbours, `|x - y|₁ = 1`), `SAdj` (`*`-adjacency,
  `|x - y|_∞ = 1`), `WithinInf` (`|x - y|_∞ ≤ r`), `StepIn`, `ConnIn`, `Ext` (the exterior of a
  set contained in a box), `IsClosedCluster`;
* `PoincareMod2` (D7(i)), `ExtBoundaryConn` (D7(ii)), `SurgeryLemma` (D7(iii));
* `ProductBound` (finite-range dependence in product form) and `PeierlsD` (D6(ii));
* the two statements added by packet P-X6 for D6(iii)–(iv): `DiameterBound` (diameters of the
  closed clusters meeting a box) and `EnclosureBound` (a box around a site is open and no closed
  cluster encloses the site), with `Encloses` defined through `Ext`.

The theorems are `poincareMod2` (`Perc/Poincare.lean`), `extBoundaryConn` (`Perc/ExtBoundary.lean`),
`surgeryLemma` (`Perc/Surgery.lean`), `peierlsD` (`Perc/Peierls.lean`), `diameterBound` and
`enclosureBound` (`Perc/Clusters.lean`).
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace HigherDimLFPP

namespace Perc

/-- Sites of `ℤ^d`. -/
abbrev Zd (d : ℕ) : Type := Fin d → ℤ

/-- Nearest-neighbour adjacency (`|x - y|₁ = 1`). -/
def LAdj {d : ℕ} (x y : Zd d) : Prop := ∑ i, |x i - y i| = 1

/-- `*`-adjacency (`|x - y|_∞ = 1`). -/
def SAdj {d : ℕ} (x y : Zd d) : Prop := x ≠ y ∧ ∀ i, |x i - y i| ≤ 1

/-- `|x - y|_∞ ≤ r`. -/
def WithinInf {d : ℕ} (r : ℤ) (x y : Zd d) : Prop := ∀ i, |x i - y i| ≤ r

/-- One step of a path for the adjacency `adj` inside the set `S`. -/
def StepIn {d : ℕ} (S : Set (Zd d)) (adj : Zd d → Zd d → Prop) (x y : Zd d) : Prop :=
  x ∈ S ∧ y ∈ S ∧ adj x y

/-- `S` is connected for `adj`. -/
def ConnIn {d : ℕ} (S : Set (Zd d)) (adj : Zd d → Zd d → Prop) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (StepIn S adj) x y

/-- Exterior of `F ⊆ [-R, R]^d`: points joined to `(R+1, …, R+1)` by an L-path avoiding `F`. -/
def Ext {d : ℕ} (R : ℤ) (F : Set (Zd d)) : Set (Zd d) :=
  {y | Relation.ReflTransGen (StepIn Fᶜ LAdj) y (fun _ => R + 1)}

/-- D7(i): mod-2 discrete Poincaré lemma. -/
def PoincareMod2 (d : ℕ) : Prop :=
  ∀ ω : Zd d → Fin d → ZMod 2,
    (∀ x i j, ω x i + ω (x + Pi.single i 1) j + ω (x + Pi.single j 1) i + ω x j = 0) →
    ∃ φ : Zd d → ZMod 2, ∀ x i, φ (x + Pi.single i 1) - φ x = ω x i

/-- D7(ii): exterior-boundary connectivity. -/
def ExtBoundaryConn (d : ℕ) : Prop :=
  ∀ (R : ℤ) (F : Set (Zd d)), F.Finite → F.Nonempty → (∀ x ∈ F, WithinInf R x 0) →
    ConnIn F SAdj →
    ConnIn {y | y ∈ Ext R F ∧ ∃ f ∈ F, SAdj y f} LAdj

/-- A closed cluster for the set of open sites `O`: a maximal `*`-connected set of closed sites. -/
def IsClosedCluster {d : ℕ} (O C : Set (Zd d)) : Prop :=
  C.Nonempty ∧ C ⊆ Oᶜ ∧ ConnIn C SAdj ∧ ∀ x ∈ C, ∀ y, y ∈ Oᶜ → SAdj x y → y ∈ C

/-- D7(iii): surgery lemma. -/
def SurgeryLemma (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (D : ℕ) (R : ℤ) (γ : List (Zd d)) (u v : Zd d),
    γ.IsChain LAdj → γ.head? = some u → γ.getLast? = some v → u ∈ O → v ∈ O →
    (∀ C, IsClosedCluster O C → (∃ x ∈ γ, x ∈ C) →
      (∀ x ∈ C, ∀ y ∈ C, WithinInf (D : ℤ) x y) ∧ (∀ x ∈ C, WithinInf R x 0) ∧
      u ∈ Ext R C ∧ v ∈ Ext R C) →
    Relation.ReflTransGen
      (StepIn {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf ((D : ℤ) + 1) y x} LAdj) u v

/-- Finite-range dependence in product form (LQGMetric's `hind`). -/
def ProductBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (closed : Zd d → Set Ω) (r : ℤ) : Prop :=
  ∀ S : Finset (Zd d), (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ WithinInf r x y) →
    μ (⋂ x ∈ S, closed x) ≤ ∏ x ∈ S, μ (closed x)

/-- D6(ii): Peierls bound in `ℤ^d`. -/
def PeierlsD (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (closed : Zd d → Set Ω) (r : ℕ)
    (ε θ : ℝ≥0∞), (∀ x, μ (closed x) ≤ ε) → ProductBound μ closed r →
    θ ≤ 1 → ε ≤ θ ^ ((r + 1) ^ d) → (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹ →
    ∀ (x : Zd d) (L : ℕ),
      μ {ω | ∃ γ : List (Zd d), γ.head? = some x ∧ γ.IsChain SAdj ∧ (∀ y ∈ γ, ω ∈ closed y) ∧
        ∃ y ∈ γ, ¬ WithinInf (L : ℤ) y x} ≤ 2⁻¹ ^ L

/-- `C` encloses the site `x` (HA5 D6(iv)): `C` lies in some box `[-R, R]^d`, and `x` is neither in
`C` nor in its exterior `Ext R C`. (For `C ⊆ [-R, R]^d` and `d ≥ 1` the set `Ext R C` does not
depend on the choice of such `R`, so the existential costs nothing; the complement of the event
"some closed cluster encloses `x`" gives `x ∈ C ∨ x ∈ Ext R C` for *every* `R` with
`C ⊆ [-R, R]^d`, which is the form the surgery lemma consumes.) -/
def Encloses {d : ℕ} (C : Set (Zd d)) (x : Zd d) : Prop :=
  ∃ R : ℤ, (∀ y ∈ C, WithinInf R y 0) ∧ x ∉ C ∧ x ∉ Ext R C

/-- D6(iii): diameter bound. With the hypotheses of `PeierlsD`, the probability that some closed
cluster (of the configuration whose closed sites are `{y | ω ∈ closed y}`) meets the box
`B̄_N(x)` and has `ℓ^∞`-diameter `> D` is at most `(2N+1)^d 2^{-⌊D/2⌋}`. -/
def DiameterBound (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (closed : Zd d → Set Ω) (r : ℕ)
    (ε θ : ℝ≥0∞), (∀ x, μ (closed x) ≤ ε) → ProductBound μ closed r →
    θ ≤ 1 → ε ≤ θ ^ ((r + 1) ^ d) → (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹ →
    ∀ (x : Zd d) (N D : ℕ),
      μ {ω | ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ (∃ z ∈ C, WithinInf (N : ℤ) z x) ∧
        ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf (D : ℤ) y y'} ≤ (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2)

/-- D6(iv): enclosure bound (replaces DGZ Lemma 2.10). With the hypotheses of `PeierlsD`, the
probability that the box `B̄_N(x)` contains a closed site, or that some closed cluster encloses
`x`, is at most `(2N+1)^d ε + 2^{-N}`. -/
def EnclosureBound (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (closed : Zd d → Set Ω) (r : ℕ)
    (ε θ : ℝ≥0∞), (∀ x, μ (closed x) ≤ ε) → ProductBound μ closed r →
    θ ≤ 1 → ε ≤ θ ^ ((r + 1) ^ d) → (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹ →
    ∀ (x : Zd d) (N : ℕ),
      μ {ω | (∃ y, WithinInf (N : ℤ) y x ∧ ω ∈ closed y) ∨
        ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ Encloses C x} ≤
        (2 * (N : ℝ≥0∞) + 1) ^ d * ε + 2⁻¹ ^ N

end Perc

end HigherDimLFPP
