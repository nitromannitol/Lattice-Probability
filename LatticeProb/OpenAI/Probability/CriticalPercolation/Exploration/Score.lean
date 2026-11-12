/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/Exploration/Score.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.Score in place of OAI.Probability.CriticalPercolation.Exploration.Score, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.PhaseStepCharge (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.SearchTree, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Delta, LatticeProb.OpenAI.Probability.CriticalPercolation.Model, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.Link, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Prob, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Potential, LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterObject, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density;
   the unused declarations `phase_score_bound` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import Mathlib
import LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.SearchTree
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Delta
import LatticeProb.OpenAI.Probability.CriticalPercolation.Model
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.Link
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Prob
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Potential
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

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

noncomputable def score (p : ℝ) (F : Set E → Prop) :
    SearchTree E R → (E → Prop → ℝ) → Set E → ℝ
  | .done _, _, _ => 0
  | .ask e l r, w, ω =>
      (if openPivot F e ω then (1-p)*delta w F e else 0) +
      if ω e then score p F r (pin w e True) ω else score p F l (pin w e False) ω

noncomputable def PhaseAdmissible {V : Type*} (G : BondGraph V E) (s : V) (p : ℝ) :
    SearchTree E R → (E → Prop → ℝ) → Prop
  | .done _, _ => True
  | .ask e l r, w =>
      w e False = 1-p ∧ w e True = p ∧
      (∃ v b, G.ends e = s(v,b) ∧
        ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) ∧
      PhaseAdmissible G s p l (pin w e False) ∧
      PhaseAdmissible G s p r (pin w e True)

lemma expect_prop_ite (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e True f using 1
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e False g using 1
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]


end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def Fresh (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) : Prop :=
  ∀ e ∉ read, w e False = 1-p ∧ w e True = p

def SupportedTails (G : BondGraph V E) (s : V) (w : E → Prop → ℝ)
    (stack : List (Dart V E)) : Prop :=
  ∀ d ∈ stack, ∀ ω, density w ω ≠ 0 → (G.openGraph ω).Reachable s d.1

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma prop_openEdge_reachable (G : BondGraph V E) (ω : Set E)
    {v e t} (he : ω e) (heq : G.ends e = s(v,t)) :
    (G.openGraph ω).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩)

theorem compile_phaseAdmissible_in (G H : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (s : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (w : E → Prop → ℝ)
    (hf : Fresh w p st.read) (ht : SupportedTails H s w stack)
    (hends : ∀ e ∉ st.read, G.ends e = H.ends e) :
    (compile G order B fuel st stack).PhaseAdmissible H s p w := by
  induction fuel generalizing st stack w with
  | zero => trivial
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hhit
    · trivial
    cases stack with
    | nil => trivial
    | cons d rest =>
      dsimp only
      split_ifs with hskip
      · exact ih st rest w hf (fun d hd => ht d (List.mem_cons_of_mem _ hd)) hends
      · have hd : d.2.2 ∉ st.reached ∧ d.2.1 ∉ st.read ∧ d.1 ∈ st.reached ∧
            G.ends d.2.1 = s(d.1,d.2.2) := by
          push Not at hskip
          exact hskip
        have hbits := hf d.2.1 hd.2.1
        have h0 : w d.2.1 False ≠ 0 := by rw [hbits.1]; exact (sub_pos.mpr hp.2).ne'
        have h1 : w d.2.1 True ≠ 0 := by rw [hbits.2]; exact hp.1.ne'
        have htail : ∀ ω, density (pin w d.2.1 False) ω ≠ 0 →
            (H.openGraph ω).Reachable s d.1 := by
          intro ω hω
          exact ht d (List.mem_cons_self) ω (density_pin_old_support w _ False ω h0 hω)
        refine ⟨hbits.1,hbits.2,⟨d.1,d.2.2,(hends d.2.1 hd.2.1).symm.trans hd.2.2.2,htail⟩,?_,?_⟩
        · apply ih (st.closed d.2.1) rest (pin w d.2.1 False)
          · exact fresh_pin w p st.read hf _ False
          · intro c hc ω hω
            exact ht c (List.mem_cons_of_mem _ hc) ω (density_pin_old_support w _ False ω h0 hω)
          · intro j hj
            exact hends j (fun hh => hj (Finset.mem_insert_of_mem hh))
        · apply ih (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest) (pin w d.2.1 True)
          · exact fresh_pin w p st.read hf _ True
          · intro c hc ω hω
            have hω' := density_pin_old_support w _ True ω h1 hω
            rcases List.mem_append.mp hc with hc | hc
            · have hc0 : c.1 = d.2.2 := (of_decide_eq_true (List.mem_filter.mp hc).2).1
              rw [hc0]
              apply (ht d (List.mem_cons_self) ω hω').trans
              apply prop_openEdge_reachable H ω _ ((hends d.2.1 hd.2.1).symm.trans hd.2.2.2)
              have hb := density_pin_support w _ True ω hω
              exact of_eq_true hb
            · exact ht c (List.mem_cons_of_mem _ hc) ω hω'

          · intro j hj
            exact hends j (fun hh => hj (Finset.mem_insert_of_mem hh))

end CriticalPercolation.LazyDFS

end
end

end OAI
