/- Copied from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableLaw at commit fdb5cad;
   selected declarations with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableLawSeries
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurablePrefixEvent

set_option autoImplicit false
set_option linter.deprecated false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling


def meshGridCodePrefixEvent (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) (j : MeshGridPrefixIndex) :
    Set (ℕ → (MatedCRT.graph ε ω hlf).State) :=
  {path | meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η) ∧
    ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i}

theorem measurableSet_meshGridCodePrefixEvent (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) (j : MeshGridPrefixIndex) :
    MeasurableSet (meshGridCodePrefixEvent ε ω hlf η z r j) := by
  classical
  letI : MeasurableSpace MeshGridStateCode := ⊤
  by_cases hg : meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η)
  · have hcyl : MeasurableSet
        {path : ℕ → (MatedCRT.graph ε ω hlf).State |
          ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} := by
      rw [show {path : ℕ → (MatedCRT.graph ε ω hlf).State |
          ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} =
        ⋂ i : ℕ, {path | i ≤ j.1 →
          meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} by ext path; simp]
      apply MeasurableSet.iInter
      intro i
      by_cases hi : i ≤ j.1
      · have hm : Measurable (fun path : ℕ → (MatedCRT.graph ε ω hlf).State =>
            meshGridEncodeMatedState (path i)) :=
          Measurable.of_discrete.comp (measurable_pi_apply i)
        have hEq : {path : ℕ → (MatedCRT.graph ε ω hlf).State |
            i ≤ j.1 → meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} =
            (fun path => meshGridEncodeMatedState (path i)) ⁻¹'
              {meshGridPrefixIndexSeq j i} := by
          ext path
          simp [hi]
        rw [hEq]
        exact (measurableSet_singleton (meshGridPrefixIndexSeq j i)).preimage hm
      · simp [hi]
    simpa [meshGridCodePrefixEvent, hg] using hcyl
  · simp [meshGridCodePrefixEvent, hg]

theorem meshGridCodePrefixEvent_mass (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (x : ℤ) (z : ℂ) (r : ℝ) (j : MeshGridPrefixIndex) :
    (MatedCRT.graph ε ω hlf).walkLaw x
      (meshGridCodePrefixEvent ε ω hlf η z r j) =
      meshGridCodePrefixTerm ε x z r j.1 (meshGridPrefixIndexSeq j) (ω, η) := by
  classical
  by_cases hg : meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η)
  · have hset : meshGridCodePrefixEvent ε ω hlf η z r j =
        {path | ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} := by
      ext path
      simp [meshGridCodePrefixEvent, hg]
    rw [hset]
    by_cases hv : meshGridCodePrefixValid ε ω j.1 (meshGridPrefixIndexSeq j)
    · rw [meshGridWalkLaw_codeCylinder ε ω hlf x j.1 (meshGridPrefixIndexSeq j) hv]
      simp [meshGridCodePrefixTerm, hv, hg]
    · rw [meshGridWalkLaw_codeCylinder_invalid ε ω hlf x j.1 (meshGridPrefixIndexSeq j) hv]
      simp [meshGridCodePrefixTerm, hv]
  · have hset : meshGridCodePrefixEvent ε ω hlf η z r j = ∅ := by
      ext path
      simp [meshGridCodePrefixEvent, hg]
    rw [hset, measure_empty]
    simp [meshGridCodePrefixTerm, hg]

theorem meshGridAnnularEvent_eq_iUnion_prefixEvent (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) :
    {path : ℕ → (MatedCRT.graph ε ω hlf).State |
      (MatedCRT.graph ε ω hlf).AnnularEvent (meshCells ε η) z r
        ((MatedCRT.graph ε ω hlf).vertexPath path)} =
      ⋃ j : MeshGridPrefixIndex, meshGridCodePrefixEvent ε ω hlf η z r j := by
  ext path
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, meshGridCodePrefixEvent]
  constructor
  · intro h
    obtain ⟨n, hg⟩ := (meshGridAnnularEvent_iff_exists_codePrefixGeometry
      ε ω hlf η z r path).mp h
    let j : MeshGridPrefixIndex := ⟨n, fun i => meshGridEncodeMatedState (path i.1)⟩
    have hp (i : ℕ) (hi : i ≤ n) :
        meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i := by
      simp [j, meshGridPrefixIndexSeq_get, hi]
    refine ⟨j, ?_, fun i hi => hp i hi⟩
    exact (meshGridCodePrefixGeometry_congr ε z r n
      (fun i => meshGridEncodeMatedState (path i)) (meshGridPrefixIndexSeq j)
      hp (ω, η)).mp hg
  · rintro ⟨j, hg, hp⟩
    have hg' : meshGridCodePrefixGeometry ε z r j.1
        (fun i => meshGridEncodeMatedState (path i)) (ω, η) :=
      (meshGridCodePrefixGeometry_congr ε z r j.1
        (meshGridPrefixIndexSeq j) (fun i => meshGridEncodeMatedState (path i))
        (fun i hi => (hp i hi).symm) (ω, η)).mp hg
    exact (meshGridAnnularEvent_iff_exists_codePrefixGeometry
      ε ω hlf η z r path).mpr ⟨j.1, hg'⟩

theorem meshGridCodePrefixEvent_pairwiseDisjoint (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) :
    Pairwise (fun j k : MeshGridPrefixIndex =>
      Disjoint (meshGridCodePrefixEvent ε ω hlf η z r j)
        (meshGridCodePrefixEvent ε ω hlf η z r k)) := by
  intro j k hne
  apply Set.disjoint_left.mpr
  intro path hj hk
  change meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η) ∧
    (∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i) at hj
  change meshGridCodePrefixGeometry ε z r k.1 (meshGridPrefixIndexSeq k) (ω, η) ∧
    (∀ i ≤ k.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq k i) at hk
  have hgj : meshGridCodePrefixGeometry ε z r j.1
      (fun i => meshGridEncodeMatedState (path i)) (ω, η) :=
    (meshGridCodePrefixGeometry_congr ε z r j.1 (meshGridPrefixIndexSeq j)
      (fun i => meshGridEncodeMatedState (path i))
      (fun i hi => (hj.2 i hi).symm) (ω, η)).mp hj.1
  have hgk : meshGridCodePrefixGeometry ε z r k.1
      (fun i => meshGridEncodeMatedState (path i)) (ω, η) :=
    (meshGridCodePrefixGeometry_congr ε z r k.1 (meshGridPrefixIndexSeq k)
      (fun i => meshGridEncodeMatedState (path i))
      (fun i hi => (hk.2 i hi).symm) (ω, η)).mp hk.1
  have hnm : j.1 = k.1 := meshGridCodePrefixGeometry_unique ε z r
    (fun i => meshGridEncodeMatedState (path i)) (ω, η) hgj hgk
  cases j with
  | mk n f =>
    cases k with
    | mk m g =>
      dsimp at hnm
      subst m
      have hfg : f = g := by
        funext i
        calc
          f i = meshGridPrefixIndexSeq ⟨n, f⟩ i.1 :=
            (meshGridPrefixIndexSeq_get ⟨n, f⟩ i.1 (Nat.lt_succ_iff.mp i.2)).symm
          _ = meshGridEncodeMatedState (path i.1) := (hj.2 i.1 (Nat.lt_succ_iff.mp i.2)).symm
          _ = meshGridPrefixIndexSeq ⟨n, g⟩ i.1 := hk.2 i.1 (Nat.lt_succ_iff.mp i.2)
          _ = g i := meshGridPrefixIndexSeq_get ⟨n, g⟩ i.1 (Nat.lt_succ_iff.mp i.2)
      exact hne (congrArg (Sigma.mk n) hfg)

/-- The annular-event walk probability is the countable sum of its selected measurable
first-exit prefix weights. -/
theorem meshGridCodeAnnularProbability_eq_walkLaw (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (x : ℤ) (z : ℂ) (r : ℝ) :
    meshGridCodeAnnularProbability ε x z r (ω, η) =
      (MatedCRT.graph ε ω hlf).walkLaw x
        {path | (MatedCRT.graph ε ω hlf).AnnularEvent (meshCells ε η) z r
          ((MatedCRT.graph ε ω hlf).vertexPath path)} := by
  rw [meshGridAnnularEvent_eq_iUnion_prefixEvent ε ω hlf η z r,
    measure_iUnion (meshGridCodePrefixEvent_pairwiseDisjoint ε ω hlf η z r)
      (measurableSet_meshGridCodePrefixEvent ε ω hlf η z r)]
  simp_rw [meshGridCodePrefixEvent_mass ε ω hlf η x z r]
  rfl

end MatedCRTHarmonic.CellScaling
