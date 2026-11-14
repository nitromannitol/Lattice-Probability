/- Copied from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableLaw at commit fdb5cad. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableWalkWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling

def meshGridCodeValid (ε : ℝ) (ω : MatedCRT.Path2) : MeshGridStateCode → Prop
  | Sum.inl _ => True
  | Sum.inr d => MatedCRT.edgePredicate ε ω d.1 = true

def meshGridCodePrefixValid (ε : ℝ) (ω : MatedCRT.Path2)
    (n : ℕ) (s : ℕ → MeshGridStateCode) : Prop :=
  ∀ i ≤ n, meshGridCodeValid ε ω (s i)

theorem measurableSet_meshGridCodePrefixValid (ε : ℝ)
    (n : ℕ) (s : ℕ → MeshGridStateCode) :
    MeasurableSet {ω : MatedCRT.Path2 | meshGridCodePrefixValid ε ω n s} := by
  classical
  rw [show {ω : MatedCRT.Path2 | meshGridCodePrefixValid ε ω n s} =
      ⋂ i : ℕ, {ω | i ≤ n → meshGridCodeValid ε ω (s i)} by
        ext ω
        simp [meshGridCodePrefixValid]]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ≤ n
  · cases hcode : s i with
    | inl x => simp [meshGridCodeValid, hi, hcode]
    | inr d =>
      have hm := (MatedCRT.matedCRT_edgePredicate_measurable_holds ε).eval (a := d.1)
      have hEq : {ω : MatedCRT.Path2 | i ≤ n → meshGridCodeValid ε ω (Sum.inr d)} =
          {ω | MatedCRT.edgePredicate ε ω d.1 = true} := by
        ext ω
        simp [meshGridCodeValid, hi]
      rw [hEq]
      exact (measurableSet_singleton true).preimage hm
  · simp [hi]

noncomputable def meshGridDecodeCode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) : MeshGridStateCode →
      (MatedCRT.graph ε ω hlf).State
  | Sum.inl x => Sum.inl x
  | Sum.inr d => by
      classical
      exact if h : MatedCRT.IsEdge ε ω d.1 then Sum.inr (⟨d.1, h⟩, d.2) else Sum.inl 0

theorem meshGridDecodeCode_encode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω)
    (u : (MatedCRT.graph ε ω hlf).State) :
    meshGridDecodeCode ε ω hlf (meshGridEncodeMatedState u) = u := by
  cases u with
  | inl x => rfl
  | inr d =>
    rcases d with ⟨⟨e, he⟩, b⟩
    simp [meshGridDecodeCode, meshGridEncodeMatedState, he, Subtype.mk.injEq]
    rfl

theorem meshGridEncode_decodeCode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (u : MeshGridStateCode)
    (hu : meshGridCodeValid ε ω u) :
    meshGridEncodeMatedState (meshGridDecodeCode ε ω hlf u) = u := by
  cases u with
  | inl x => rfl
  | inr d =>
    have he : MatedCRT.IsEdge ε ω d.1 := by
      simpa [meshGridCodeValid, MatedCRT.edgePredicate] using hu
    simp [meshGridDecodeCode, meshGridEncodeMatedState, he]

theorem meshGridCodeValid_encode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω)
    (u : (MatedCRT.graph ε ω hlf).State) :
    meshGridCodeValid ε ω (meshGridEncodeMatedState u) := by
  cases u with
  | inl x => trivial
  | inr d =>
    rcases d with ⟨⟨e, he⟩, b⟩
    simpa [meshGridCodeValid, meshGridEncodeMatedState, MatedCRT.edgePredicate] using he

/-- A valid fixed code prefix has the cylinder mass computed by its measurable prefix product. -/
theorem meshGridWalkLaw_codeCylinder (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (hvalid : meshGridCodePrefixValid ε ω n s) :
    (MatedCRT.graph ε ω hlf).walkLaw x
      {path | ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} =
      meshGridCodePrefixWeight ε x s n ω := by
  let t : ℕ → (MatedCRT.graph ε ω hlf).State :=
    fun i => meshGridDecodeCode ε ω hlf (s i)
  have hset : {path : ℕ → (MatedCRT.graph ε ω hlf).State |
      ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} =
      {path | ∀ i ≤ n, path i = t i} := by
    ext path
    constructor
    · intro hp i hi
      have h := congrArg (meshGridDecodeCode ε ω hlf) (hp i hi)
      simpa [t, meshGridDecodeCode_encode] using h
    · intro hp i hi
      rw [hp i hi]
      exact meshGridEncode_decodeCode ε ω hlf (s i) (hvalid i hi)
  rw [hset, meshGridWalkLaw_stateCylinder]
  have hs (i : ℕ) (hi : i ≤ n) : meshGridEncodeMatedState (t i) = s i :=
    meshGridEncode_decodeCode ε ω hlf (s i) (hvalid i hi)
  unfold meshGridCodePrefixWeight
  change (if meshGridEncodeMatedState (t 0) = Sum.inl x then
      ∏ i ∈ Finset.range n,
        meshGridCodeTransitionWeight ε (meshGridEncodeMatedState (t i))
          (meshGridEncodeMatedState (t (i + 1))) ω else 0) =
    if s 0 = Sum.inl x then
      ∏ i ∈ Finset.range n, meshGridCodeTransitionWeight ε (s i) (s (i + 1)) ω else 0
  rw [hs 0 (Nat.zero_le n)]
  by_cases hstart : s 0 = Sum.inl x
  · simp only [if_pos hstart]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hs i (Nat.le_of_lt (Finset.mem_range.mp hi)),
      hs (i + 1) (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))]
  · simp [hstart]

theorem meshGridWalkLaw_codeCylinder_invalid (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (hv : ¬meshGridCodePrefixValid ε ω n s) :
    (MatedCRT.graph ε ω hlf).walkLaw x
      {path | ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} = 0 := by
  have hset : {path : ℕ → (MatedCRT.graph ε ω hlf).State |
      ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} = ∅ := by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    apply hv
    intro i hi
    rw [← hp i hi]
    exact meshGridCodeValid_encode ε ω hlf (path i)
  rw [hset, measure_empty]

end MatedCRTHarmonic.CellScaling
