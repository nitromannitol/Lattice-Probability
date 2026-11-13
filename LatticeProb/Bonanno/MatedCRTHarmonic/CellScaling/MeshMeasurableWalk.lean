/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableWalk at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.GraphMeasurability
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Walk

/-!
# Measurable walk weights for mesh graphs

The candidate dart labels form a fixed countable space, independent of the path. Summing their
measurable active-dart indicators gives a measurable extended-real degree, and hence measurable
weights for each fixed candidate transition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling

abbrev MeshGridEdgeCode := ℤ × ℤ × Bool
abbrev MeshGridDartCode := MeshGridEdgeCode × Bool
def meshGridDartSourceCode (d : MeshGridDartCode) : ℤ :=
  if d.2 then d.1.2.1 else d.1.1

def meshGridDartActiveAt (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ)
    (d : MeshGridDartCode) : Prop :=
  MatedCRT.edgePredicate ε ω d.1 = true ∧ meshGridDartSourceCode d = x

noncomputable def meshGridRawDegree (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ) : ℝ≥0∞ := by
  classical
  exact ∑' d : MeshGridDartCode, if meshGridDartActiveAt ε ω x d then 1 else 0

/-- On locally finite data, the countable-code degree is exactly the edge-end degree of the
frozen mesh graph. -/
theorem meshGridRawDegree_eq_graph_deg (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ) :
    meshGridRawDegree ε ω x =
      ((MatedCRT.graph ε ω hlf).deg x : ℝ≥0∞) := by
  classical
  let G := MatedCRT.graph ε ω hlf
  let A : Set MeshGridDartCode := {d | meshGridDartActiveAt ε ω x d}
  let B : Set G.Dart := {d | G.dsrc d = x}
  have hedge (e : MeshGridEdgeCode) :
      MatedCRT.edgePredicate ε ω e = true ↔ MatedCRT.IsEdge ε ω e := by
    simp [MatedCRT.edgePredicate]
  have hactive (d : G.Dart) :
      meshGridDartActiveAt ε ω x (d.1.1, d.2) ↔ G.dsrc d = x := by
    rcases d with ⟨⟨e, he⟩, b⟩
    change (MatedCRT.edgePredicate ε ω e = true ∧
      (if b then e.2.1 else e.1) = x) ↔ (if b then e.2.1 else e.1) = x
    simp [MatedCRT.edgePredicate, he]
  let f : B → A := fun d =>
    ⟨(d.1.1.1, d.1.2), (hactive d.1).2 d.2⟩
  let g : A → B := fun c =>
    ⟨(⟨c.1.1, (hedge c.1.1).mp c.2.1⟩, c.1.2),
      (hactive (⟨⟨c.1.1, (hedge c.1.1).mp c.2.1⟩, c.1.2⟩ : G.Dart)).mp c.2⟩
  have hfg : Function.LeftInverse g f := by
    intro d
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  have hgf : Function.RightInverse g f := by
    intro c
    apply Subtype.ext
    rfl
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    calc
      a.1 = (g (f a)).1 := congrArg Subtype.val (hfg a).symm
      _ = (g (f b)).1 := congrArg (fun y => (g y).1) hab
      _ = b.1 := congrArg Subtype.val (hfg b)
  have hsurj : Function.Surjective f := by
    intro c
    exact ⟨g c, hgf c⟩
  let eAB : B ≃ A := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hB : B = (G.outDarts x : Set G.Dart) := by
    ext d
    simp [B, Harmonic.mem_outDarts]
  have hBfinite : B.Finite := by
    rw [hB]
    exact (G.outDarts x).finite_toSet
  letI : Fintype B := hBfinite.fintype
  letI : Fintype A := Fintype.ofEquiv B eAB
  have hsum : meshGridRawDegree ε ω x = ∑' c : A, (1 : ℝ≥0∞) := by
    unfold meshGridRawDegree
    have hindicator : (fun d : MeshGridDartCode =>
        if meshGridDartActiveAt ε ω x d then (1 : ℝ≥0∞) else 0) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext d
      by_cases hd : d ∈ A
      · have hactive : meshGridDartActiveAt ε ω x d := by simpa [A] using hd
        rw [if_pos hactive, Set.indicator_of_mem hd]
      · have hactive : ¬ meshGridDartActiveAt ε ω x d := by simpa [A] using hd
        rw [if_neg hactive, Set.indicator_of_notMem hd]
    rw [hindicator, ← tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
  calc
    meshGridRawDegree ε ω x = ∑' c : A, (1 : ℝ≥0∞) := hsum
    _ = (Fintype.card A : ℝ≥0∞) := by simp [tsum_fintype]
    _ = (Fintype.card B : ℝ≥0∞) := by rw [Fintype.card_congr eAB.symm]
    _ = ((G.outDarts x).card : ℝ≥0∞) := by
      let eb : B ≃ {d : G.Dart // d ∈ G.outDarts x} := {
        toFun := fun d => ⟨d.1, (Harmonic.mem_outDarts G).mpr d.2⟩
        invFun := fun d => ⟨d.1, (Harmonic.mem_outDarts G).mp d.2⟩
        left_inv := by intro d; apply Subtype.ext; rfl
        right_inv := by intro d; apply Subtype.ext; rfl }
      rw [Fintype.card_congr eb]
      simp
    _ = ((G.deg x : ℕ) : ℝ≥0∞) := by simp [LFMultigraph.deg]

end MatedCRTHarmonic.CellScaling
