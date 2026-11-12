/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcI0 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcF

/-!
# D124 packet I0 (walled form): `D'_S` as a function of `𝒳_δ` (P2-DZZI0)

DEC-124 §5 I3 ("I0 adds `coarseLogDOn S` and `logApproxLGDOn_eq_coarseLogDOn`"): the walled
approximate distance `D'_S` (cell paths through a cell family `S`, `approxLGDSetOn`, S3P32K1) is,
on DZZ's `𝒜_δ`, the same function of the coarse field as `D'` (DZZ l. 1567–1569). Same proof as
`logApproxLGD_eq_coarseLogD` (S3ConcF), with `cellGraphOn S`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*}

/-- `log D'_{S,γ,δ,x}(A, B)`: the walled approximate distance read off a coarse path `x`. -/
def coarseLogDOn (S : Set DyBox) (γ κ δ : ℝ) (A B : Set ℂ) (x : CoarseIdx κ δ → ℝ) : ℝ :=
  Real.log ((approxDistSetOn S (coarseMass γ κ δ x) δ A B).toNat : ℝ)

/-- **`D'_S = D'_{S,𝒳_δ}` on `𝒜_δ`** (DZZ l. 1567–1569, walled). -/
theorem logApproxLGDOn_eq_coarseLogDOn [MeasurableSpace Ω] (S : Set DyBox) {γ κ δ : ℝ}
    (hδ : δ ≠ 0) (W : WNSpace → Ω → ℝ) (A B : Set ℂ) (ω : Ω)
    (hω : (fun s => coarseField W κ δ s ω) ∈ CoarseGood γ κ δ) :
    logApproxLGDOn S γ W δ A B ω =
      coarseLogDOn S γ κ δ A B (fun s => coarseField W κ δ s ω) := by
  have hiff := isCell_iff_of_agree (m := approxLQG γ W ω)
    (m' := coarseMass γ κ δ (fun s => coarseField W κ δ s ω)) (s₀ := δ ^ κ) hδ
    (fun b hb => by simp [coarseMass, hb, approxLQG, coarseField_inl])
    (fun b hb => by simp [coarseMass, not_le.2 hb]) hω
  have hg : cellGraphOn S (approxLQG γ W ω) δ =
      cellGraphOn S (coarseMass γ κ δ (fun s => coarseField W κ δ s ω)) δ := by
    ext b b'
    simp only [cellGraphOn, cellGraph, hiff]
  unfold logApproxLGDOn coarseLogDOn approxLGDSetOn approxDistSetOn approxDistOn
  rw [hg]
  simp only [hiff]

end DZZ
end LQGMetric
