/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3D6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4FineHP

/-!
# DZZ Definition 3.6: enclosures of a dyadic box (P2-DZZ3D, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Definition 3.6
(`def-E-delta-B-prime`, l. 920–935) and the remark after it (l. 936–939).

* `DyBox.largeBox b` = `B_large`: the closed box concentric with `B` of side `2 s_B`.
* `boxColl b k` = `𝓑(B, ε)` for `ε = 2^{-k}`: dyadic boxes of side `ε s_B` (all our dyadic boxes
  lie in `𝕍`) lying in `B_large`; `boxCollBdry b k` = `𝓑_∂(B, ε)`: those whose closures meet `∂B`.
* `cellPsi m δ b` = `Ψ_{B,δ}`: the number of cells of `𝓥_δ` contained in `B` touching `∂B`
  (`1` if `B` lies in a cell); `PsiLe m δ b λ` reads `Ψ_{B,δ} ≤ λ` (finite and `≤ λ`).
* `cellPhi μ δ b` = `Φ_{B,δ}`: the least number of (open) Euclidean balls of `μ`-mass `≤ δ²`
  covering `∂B` (`μ` = the LQG measure in DZZ; left as a parameter here).
* `EnclosesBox b U`: "separates `B` from `𝕍 ∩ ∂B_large` in `𝕍`" (l. 938–939): every continuous path
  in `𝕍` from `B` to `∂B_large` meets a box of `U`.
* `HasEnclosure b k good`: a sequence `B'_1, …, B'_d` of neighbouring boxes of `𝓑(B, ε)` in
  `B_large \ B` (interiors disjoint from `B`) enclosing `B`, each satisfying `good`.
* `encEventPsi γ W δ b k λ` = `𝓔_{δ,B,ε,λ}`, `encEventPhi μ δ b k λ` = `𝓔'_{δ,B,ε,λ}`.

Reading (DEVIATIONS): "neighbouring" is `DyBox.Neighbour` (closures share a non-trivial segment,
DZZ l. 937); `B'_i ⊆ B_large \ B` is read up to boundaries (closed boxes; interior of `B'_i`
disjoint from `B`), since closed boxes adjacent to `B` touch `∂B`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `B_large`: the closed box concentric with `B` with side length `2 s_B`. -/
def DyBox.largeBox (b : DyBox) : Set ℂ :=
  {z | |z.re - b.center.re| ≤ b.side ∧ |z.im - b.center.im| ≤ b.side}

/-- `𝓑(B, ε)`, `ε = 2^{-k}`: dyadic boxes of side `ε s_B` lying in `B_large`. -/
def boxColl (b : DyBox) (k : ℕ) : Set DyBox :=
  {b' | b'.n = b.n + k ∧ b'.closedBox ⊆ b.largeBox}

/-- `𝓑_∂(B, ε)`, `ε = 2^{-k}`: dyadic boxes of side `ε s_B` whose closures intersect `∂B`. -/
def boxCollBdry (b : DyBox) (k : ℕ) : Set DyBox :=
  {b' | b'.n = b.n + k ∧ (b'.closedBox ∩ frontier b.closedBox).Nonempty}

open Classical in
/-- `Ψ_{B,δ}`: the number of cells of `𝓥_δ` contained in `B` that touch `∂B`; `1` if `B` is
contained in a cell. -/
def cellPsi (m : DyBox → ℝ) (δ : ℝ) (b : DyBox) : ℕ∞ :=
  if ∃ c, IsCell m δ c ∧ b.closedBox ⊆ c.closedBox then 1 else
    {c | IsCell m δ c ∧ c.closedBox ⊆ b.closedBox ∧
      (c.closedBox ∩ frontier b.closedBox).Nonempty}.encard

/-- `Ψ_{B,δ} ≤ λ`. -/
def PsiLe (m : DyBox → ℝ) (δ : ℝ) (b : DyBox) (lam : ℝ) : Prop :=
  ∃ N : ℕ, cellPsi m δ b = N ∧ (N : ℝ) ≤ lam

/-- A family of boxes encloses `B`: it separates `B` from `𝕍 ∩ ∂B_large` in `𝕍` (DZZ l. 938):
every path in `𝕍` from `B` to `∂B_large` meets one of the boxes. -/
def EnclosesBox (b : DyBox) (U : Set DyBox) : Prop :=
  ∀ p : C(unitInterval, ℂ), (∀ t, p t ∈ dzzV) → p 0 ∈ b.closedBox →
    p 1 ∈ frontier b.largeBox → ∃ t, ∃ b' ∈ U, p t ∈ b'.closedBox

/-- There is a sequence of neighbouring boxes `B'_1, …, B'_d ∈ 𝓑(B, ε)` in `B_large \ B`
enclosing `B`, each satisfying `good` (Definition 3.6). -/
def HasEnclosure (b : DyBox) (k : ℕ) (good : DyBox → Prop) : Prop :=
  ∃ l : List DyBox, l ≠ [] ∧ l.IsChain DyBox.Neighbour ∧
    (∀ b' ∈ l, b' ∈ boxColl b k ∧ Disjoint (interior b'.closedBox) b.closedBox ∧ good b') ∧
    EnclosesBox b {b' | b' ∈ l}

open WhiteNoise

variable {Ω : Type*}

/-- `𝓔_{δ,B,ε,λ}` (`ε = 2^{-k}`), for the approximate LQG of `W`. -/
def encEventPsi (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (b : DyBox) (k : ℕ) (lam : ℝ) : Set Ω :=
  {ω | HasEnclosure b k fun b' => PsiLe (approxLQG γ W ω) δ b' lam}

end DZZ
end LQGMetric
