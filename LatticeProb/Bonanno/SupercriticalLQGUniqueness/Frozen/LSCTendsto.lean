/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCTendsto at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsExtMetric

/-! Scratch freeze split of SLUMetric.lean:60. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- The convergence criterion of DG Definition 1.2 (DG l. 314–317): the functions `F n` converge
to `f` iff
(i) whenever `p n → q` in `α × α`, `f q ≤ liminf (F n (p n))`; and
(ii) for each `q` there is a sequence `p n → q` with `F n (p n) → f q`. -/
def LSCTendsto {α : Type*} [TopologicalSpace α] (F : ℕ → α × α → EReal) (f : α × α → EReal) : Prop :=
  (∀ (p : ℕ → α × α) (q : α × α), Tendsto p atTop (𝓝 q) →
      f q ≤ liminf (fun n => F n (p n)) atTop) ∧
    ∀ q : α × α, ∃ p : ℕ → α × α, Tendsto p atTop (𝓝 q) ∧
      Tendsto (fun n => F n (p n)) atTop (𝓝 (f q))
end SupercriticalLQGUniqueness
