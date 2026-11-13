/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SLUMetricAPI at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUSupport
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.LocallyConstant.Basic

 











set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness

 

 

section Criterion

variable {α : Type*} [TopologicalSpace α]

 
theorem LSCTendsto.comp_strictMono {F : ℕ → α × α → EReal} {f : α × α → EReal}
    (hF : LSCTendsto F f) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    LSCTendsto (fun n => F (φ n)) f := by
  classical
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · let p' : ℕ → α × α := fun n => if h : ∃ k, φ k = n then p (Nat.find h) else q
    have hp'φ : ∀ k, p' (φ k) = p k := by
      intro k
      have h : ∃ j, φ j = φ k := ⟨k, rfl⟩
      simp only [p', dite_eq_left h]
      exact congrArg p (hφ.injective (Nat.find_spec h))
    have hp' : Tendsto p' atTop (𝓝 q) := by
      refine tendsto_nhds.2 fun s hs hqs => ?_
      obtain ⟨K, hK⟩ := eventually_atTop.1 (hp (hs.mem_nhds hqs))
      refine eventually_atTop.2 ⟨φ K, fun n hn => ?_⟩
      by_cases h : ∃ k, φ k = n
      · have hk : φ (Nat.find h) = n := Nat.find_spec h
        have hK' : K ≤ Nat.find h := hφ.le_iff_le.1 (hn.trans_eq hk.symm)
        simpa only [p', Set.mem_preimage, dite_eq_left h] using hK _ hK'
      · simpa only [p', Set.mem_preimage, dite_eq_right h] using hqs
    calc f q ≤ liminf (fun n => F n (p' n)) atTop := hF.1 p' q hp'
      _ ≤ liminf (fun n => F n (p' n)) (map φ atTop) :=
          liminf_le_liminf_of_le hφ.tendsto_atTop
      _ = liminf (fun k => F (φ k) (p k)) atTop := by
          rw [← liminf_comp]
          simp only [Function.comp_def, hp'φ]
  · obtain ⟨p, hp, hFp⟩ := hF.2 q
    exact ⟨fun k => p (φ k), hp.comp hφ.tendsto_atTop, hFp.comp hφ.tendsto_atTop⟩

 
end Criterion

 

namespace LSCFun

theorem tendsto_of_lscTendsto {F : ℕ → LSCFun} {f : LSCFun}
    (h : LSCTendsto (fun n => (F n).1) f.1) : Tendsto F atTop (𝓝 f) :=
  tendsto_nhds.2 fun _ hV hfV => hV F f h hfV

 

instance instSequentialSpace : SequentialSpace (LSCFun) where
  isClosed_of_seq s hs := by
    rw [← isOpen_compl_iff]
    intro F f hF hf
    by_contra hne
    rw [not_eventually] at hne
    simp only [Set.mem_compl_iff, not_not] at hne
    obtain ⟨φ, hφ, hFφ⟩ := extraction_of_frequently_atTop hne
    exact hf (hs hFφ (tendsto_of_lscTendsto (hF.comp_strictMono hφ)))

 



end LSCFun

 

namespace LSCMetric

@[ext]
theorem ext {D D' : LSCMetric} (h : ∀ p, D p = D' p) : D = D' :=
  Subtype.ext (funext h)

end LSCMetric


 

end SupercriticalLQGUniqueness
