/-
Finite transcripts of dependent independent cells. A transcript stores each index
together with its observed value. Distinct indices give its exact product mass;
adaptively generated transcripts must supply this distinctness in each application.
-/
import LatticeProb.Prob.AdaptiveReads
import Mathlib.Data.List.OfFn


set_option autoImplicit false

namespace LatticeProb.Prob.CellTranscripts

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

noncomputable section

variable {Ω K : Type*} [MeasurableSpace Ω] {A : K → Type*}
variable [∀ q, MeasurableSpace (A q)] [∀ q, MeasurableSingletonClass (A q)]

/-- The event that every index and value in a finite transcript is observed. -/
def cylinder (X : ∀ q, Ω → A q) (l : List (Σ q, A q)) : Set Ω :=
  {ω | ∀ c ∈ l, X c.1 ω = c.2}

omit [∀ q, MeasurableSpace (A q)] [∀ q, MeasurableSingletonClass (A q)] in
/-- A transcript without repeated indices has an injective indexed read map.
The values may live in different alphabets. -/
theorem injective_get_index (l : List (Σ q, A q)) (hl : (l.map Sigma.fst).Nodup) :
    Function.Injective (fun i : Fin l.length => (l.get i).1) := by
  intro i j hij
  have hi := hl.injective_get
  have he : (l.map Sigma.fst).get ⟨i, by simpa only [List.length_map] using i.isLt⟩ =
      (l.map Sigma.fst).get ⟨j, by simpa only [List.length_map] using j.isLt⟩ := by
    simpa only [List.get_eq_getElem, List.getElem_map] using hij
  exact Fin.ext (congrArg (fun a : Fin (l.map Sigma.fst).length => a.val) (hi he))

/-- **Finite dependent transcript mass.** Independent cells with distinct observed
indices have exactly the product of their individual masses. -/
theorem measure_cylinder (P : Measure Ω) (X : ∀ q, Ω → A q)
    (hind : iIndepFun X P) (l : List (Σ q, A q)) (hl : (l.map Sigma.fst).Nodup) :
    P (cylinder X l) =
      ∏ i : Fin l.length, P {ω | X (l.get i).1 ω = (l.get i).2} := by
  have he : cylinder X l = {ω | ∀ i : Fin l.length,
      X (l.get i).1 ω = (l.get i).2} := by
    ext ω
    constructor
    · intro h i
      exact h _ (List.get_mem l i)
    · intro h c hc
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
      exact h i
  rw [he]
  exact AdaptiveReads.measure_finite_reads_of_injective P X hind l.length
    (fun i => (l.get i).1) (injective_get_index l hl) (fun i => (l.get i).2)

end

end LatticeProb.Prob.CellTranscripts
