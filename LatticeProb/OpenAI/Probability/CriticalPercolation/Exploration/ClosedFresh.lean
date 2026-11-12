/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/Exploration/ClosedFresh.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.ClosedFresh in place of OAI.Probability.CriticalPercolation.Exploration.ClosedFresh, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.CompileEmptyReads (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.CriticalPercolation.Model, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphInsert, LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.Score, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Delta, LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.SearchTree, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Potential, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Prob, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.Link, LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterObject, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density;
   the unused declarations `exhaustive_mapTarget`, `mapState_initial`, `search_reads_targetWiring`, `search_target_pivotal_moments`, `contact_second_le_three_mean` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import Mathlib
import LatticeProb.OpenAI.Probability.CriticalPercolation.Model
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphInsert
import LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.Score
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Delta
import LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.SearchTree
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Potential
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Prob
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.Link
import LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterObject
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]





end CriticalPercolation.LazyDFS

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

def ClosedFresh (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E) : Prop :=
  ∀ e ∉ used, r e False = (if e ∈ C then 1 else 1-p) ∧
    r e True = (if e ∈ C then 0 else p)

omit [Fintype E] in
lemma closedFresh_pin (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E)
    (hf : ClosedFresh r p C used) (e : E) (b : Prop) :
    ClosedFresh (pin r e b) p C (insert e used) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ used := by simpa only [Finset.mem_insert,not_or] using hj
  unfold pin
  simp only [Function.update,dite_eq_right hj'.1]
  exact hf j hj'.2

noncomputable def contactScore (T : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => 0
  | .ask e l r => (if e ∈ C then p*delta w F e else 0) +
      if ω e then r.contactScore p C F (pin w e True) ω
      else l.contactScore p C F (pin w e False) ω

noncomputable def terminalProbability (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => prob w F
  | .ask e l r => if ω e then r.terminalProbability F (pin w e True) ω
      else l.terminalProbability F (pin w e False) ω

omit [DecidableEq E] in
lemma contact_mean_step (e : E) (l r : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1) :
    expect v ((.ask e l r : SearchTree E R).contactScore p C F w) =
      (if e ∈ C then p*delta w F e else 0) +
      v e True*expect (pin v e True) (r.contactScore p C F (pin w e True)) +
      v e False*expect (pin v e False) (l.contactScore p C F (pin w e False)) := by
  change expect v (fun ω => (if e ∈ C then p*delta w F e else 0) +
    if ω e then r.contactScore p C F (pin w e True) ω
    else l.contactScore p C F (pin w e False) ω) = _
  rw [expect_add,expect_const v hv]
  erw [expect_prop_ite]
  ring

omit [DecidableEq E] in
lemma terminal_mean_step (e : E) (l r : SearchTree E R) (F : Set E → Prop)
    (w v : E → Prop → ℝ) :
    expect v ((.ask e l r : SearchTree E R).terminalProbability F w) =
      v e True*expect (pin v e True) (r.terminalProbability F (pin w e True)) +
      v e False*expect (pin v e False) (l.terminalProbability F (pin w e False)) := by
  exact expect_prop_ite v e _ _

theorem contact_mean_terminal (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (T.contactScore p C F w) + expect v (T.terminalProbability F w) = prob w F := by
  induction T generalizing used w v with
  | done r =>
    change expect v (fun _ => 0) + expect v (fun _ => prob w F) = prob w F
    rw [expect_zero,expect_const v hv,zero_add]
  | ask e l r hl hr =>
    have he : w e False = 1-p ∧ w e True = p := hf e hT.1
    have hv' := hc e hT.1
    have hl' := hl (insert e used) hT.2.1 (pin w e False) (pin v e False)
      (pin_normalized w hw e False) (pin_normalized v hv e False)
      (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)
    have hr' := hr (insert e used) hT.2.2 (pin w e True) (pin v e True)
      (pin_normalized w hw e True) (pin_normalized v hv e True)
      (fresh_pin w p used hf e True) (closedFresh_pin v p C used hc e True)
    have hs : prob w F = w e False*prob (pin w e False) F +
        w e True*prob (pin w e True) F := expect_split_pin w e _
    rw [contact_mean_step e l r p C F w v hv,terminal_mean_step,hv'.1,hv'.2]
    rw [he.1,he.2] at hs
    by_cases heC : e ∈ C <;> simp only [heC,↓reduceIte,zero_mul,one_mul,add_zero,zero_add]
    · unfold delta
      linear_combination hl' - hs
    · linear_combination (1-p)*hl' + p*hr' - hs

omit [DecidableEq E] in
lemma terminalProbability_nonneg (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (hn : ∀ e b, 0 ≤ w e b) (ω : E → Prop) :
    0 ≤ T.terminalProbability F w ω := by
  induction T generalizing w with
  | done r => exact prob_nonneg w hn F
  | ask e l r hl hr =>
    unfold terminalProbability
    split_ifs
    · exact hr (pin w e True) (pin_nonneg w hn e True)
    · exact hl (pin w e False) (pin_nonneg w hn e False)

theorem contact_mean_le_prob (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hnw : ∀ e b, 0 ≤ w e b) (hnv : ∀ e b, 0 ≤ v e b)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (T.contactScore p C F w) ≤ prob w F := by
  have ht := contact_mean_terminal T used hT p C F w v hw hv hf hc
  have hn := expect_nonneg hnv (terminalProbability_nonneg T F w hnw)
  linarith

omit [DecidableEq E] in
lemma expect_square_add_const (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,expect_const_mul]


end CriticalPercolation.SearchTree

end
end

end OAI
