/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCFunInstTopologicalSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCFun

/-! Scratch freeze split of SLUMetric.lean:73. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- The topology on lower semicontinuous functions (DG Definition 1.2, l. 314–318): a set `V` is
open iff every sequence of lower semicontinuous functions converging in the sense
`LSCTendsto` to an element of `V` lies eventually in `V`. -/
@[reducible, instance] def LSCFun.instTopologicalSpace : TopologicalSpace (LSCFun) where
  IsOpen V := ∀ (F : ℕ → LSCFun) (f : LSCFun),
    LSCTendsto (fun n => (F n).1) f.1 → f ∈ V → ∀ᶠ n in atTop, F n ∈ V
  isOpen_univ _ _ _ _ := Eventually.of_forall fun _ => trivial
  isOpen_inter _ _ hU hV F f hF hf := (hU F f hF hf.1).and (hV F f hF hf.2)
  isOpen_sUnion S hS F f hF hf := by
    obtain ⟨U, hUS, hfU⟩ := Set.mem_sUnion.1 hf
    exact (hS U hUS F f hF hfU).mono fun _ hn => Set.mem_sUnion_of_mem hn hUS
end SupercriticalLQGUniqueness
