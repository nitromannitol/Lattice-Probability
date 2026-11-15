/- Copied from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurablePrefix at commit fdb5cad;
   selected declarations with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurablePrefix
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent

set_option autoImplicit false
set_option linter.deprecated false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.CellScaling

/-- The annular event is exactly the union over its finite first-exit prefixes. -/
theorem meshGridAnnularEvent_iff_exists_codePrefixGeometry (ε : ℝ)
    (ω : MatedCRT.Path2) (hlf : MatedCRT.IsLocallyFinite ε ω)
    (η : C(ℝ, ℂ)) (z : ℂ) (r : ℝ)
    (path : ℕ → (MatedCRT.graph ε ω hlf).State) :
    (MatedCRT.graph ε ω hlf).AnnularEvent (meshCells ε η) z r
      ((MatedCRT.graph ε ω hlf).vertexPath path) ↔
    ∃ n : ℕ, meshGridCodePrefixGeometry ε z r n
      (fun i => meshGridEncodeMatedState (path i)) (ω, η) := by
  let G := MatedCRT.graph ε ω hlf
  let J := meshCells ε η
  let X := G.vertexPath path
  have hv (i : ℕ) : meshGridStateVertexCode (meshGridEncodeMatedState (path i)) = X i := by
    exact meshGridStateVertexCode_encode (path i)
  have hdisc (n : ℕ) :
      meshGridCodeDisconnects ε ω
        {y | ∃ i < n, X i = y}
        (verticesMeeting J (sphere z (3 * r / 4)))
        (verticesMeeting J (sphere z (5 * r / 4))) ↔
      G.Disconnects {y | ∃ i < n, X i = y}
        (verticesMeeting J (sphere z (3 * r / 4)))
        (verticesMeeting J (sphere z (5 * r / 4))) := by
    exact meshGridCodeDisconnects_iff_graphDisconnects ε ω hlf
      {y | ∃ i < n, X i = y}
      (verticesMeeting J (sphere z (3 * r / 4)))
      (verticesMeeting J (sphere z (5 * r / 4)))
  have hprefix (n : ℕ) :
      meshGridCodePrefixGeometry ε z r n
          (fun i => meshGridEncodeMatedState (path i)) (ω, η) ↔
        Markov.hitTime (verticesMeeting J (annulus z (r / 2) (3 * r / 2)))ᶜ X = n ∧
          G.Disconnects {y | ∃ i < n, X i = y}
            (verticesMeeting J (sphere z (3 * r / 4)))
            (verticesMeeting J (sphere z (5 * r / 4))) ∧
          ∀ i ≤ n, J (X i) ⊆ annulus z (r / 3) (5 * r / 3) := by
    rw [meshGridCodePrefixGeometry, Markov.hitTime_eq_coe_iff]
    simp only [hv, J, X, Set.mem_compl_iff, verticesMeeting, Set.mem_setOf_eq, not_not]
    constructor
    · rintro ⟨hbefore, hexit, hsep, hstay⟩
      exact ⟨⟨hexit, hbefore⟩, (hdisc n).mp hsep, hstay⟩
    · rintro ⟨⟨hexit, hbefore⟩, hsep, hstay⟩
      exact ⟨hbefore, hexit, (hdisc n).mpr hsep, hstay⟩
  simp only [LFMultigraph.AnnularEvent]
  constructor
  · rintro ⟨n, hn, hd, hs⟩
    exact ⟨n, (hprefix n).mpr ⟨hn, hd, hs⟩⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (hprefix n).mp hn⟩

theorem meshGridCodePrefixGeometry_congr (ε : ℝ) (z : ℂ) (r : ℝ)
    (n : ℕ) (s t : ℕ → MeshGridStateCode)
    (h : ∀ i ≤ n, s i = t i) (d : MatedCRT.Path2 × C(ℝ, ℂ)) :
    meshGridCodePrefixGeometry ε z r n s d ↔
      meshGridCodePrefixGeometry ε z r n t d := by
  have hU : {y | ∃ i < n, meshGridStateVertexCode (s i) = y} =
      {y | ∃ i < n, meshGridStateVertexCode (t i) = y} := by
    ext y
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, hi, by rw [← h i (Nat.le_of_lt hi)]; exact hy⟩
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, hi, by rw [h i (Nat.le_of_lt hi)]; exact hy⟩
  unfold meshGridCodePrefixGeometry
  constructor
  · rintro ⟨hb, he, hd, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [← h i (Nat.le_of_lt hi)]
      exact hb i hi
    · rw [← h n le_rfl]
      exact he
    · rw [← hU]
      exact hd
    · intro i hi
      rw [← h i hi]
      exact hs i hi
  · rintro ⟨hb, he, hd, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [h i (Nat.le_of_lt hi)]
      exact hb i hi
    · rw [h n le_rfl]
      exact he
    · rw [hU]
      exact hd
    · intro i hi
      rw [h i hi]
      exact hs i hi

theorem meshGridCodePrefixGeometry_unique (ε : ℝ) (z : ℂ) (r : ℝ)
    (s : ℕ → MeshGridStateCode) (d : MatedCRT.Path2 × C(ℝ, ℂ))
    {n m : ℕ} (hn : meshGridCodePrefixGeometry ε z r n s d)
    (hm : meshGridCodePrefixGeometry ε z r m s d) : n = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hn.2.1 (hm.1 n hlt)
  · exact hm.2.1 (hn.1 m hgt)

end MatedCRTHarmonic.CellScaling
