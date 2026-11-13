/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.GraphMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsEdge

/-!
# Measurability of the mated-CRT edge predicate

The graph is encoded measurably by its countable Boolean edge predicate. The definition
`MatedCRT.graph` itself takes a local-finiteness proof as an argument and has no graph-valued
measurable-space instance.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

private def clampInterval (a b t : ℝ) : ℝ := max a (min b t)

private theorem continuousPathCoordinate (i : Fin 2) (ω : Path2) :
    Continuous (fun t : ℝ => lrCoord i t ω) := by
  unfold lrCoord
  split_ifs with hi
  · exact continuous_fst.comp ω.continuous
  · exact continuous_snd.comp ω.continuous

private theorem clampInterval_mem {a b t : ℝ} (hab : a ≤ b) :
    clampInterval a b t ∈ Icc a b := by
  constructor
  · exact le_max_left _ _
  · exact (max_le hab (min_le_left _ _))

private theorem intervalInf_eq_rationalInf {X : ℝ → ℝ} (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) :
    intervalInf X a b = sInf (Set.range fun q : ℚ => X (clampInterval a b q)) := by
  let F : ℝ → ℝ := fun t => X (clampInterval a b t)
  have hF : Continuous F := by
    apply hX.comp
    unfold clampInterval
    exact continuous_const.max (continuous_const.min continuous_id)
  have hcompact : IsCompact (X '' Icc a b) := isCompact_Icc.image hX
  have hne : (X '' Icc a b).Nonempty := (nonempty_Icc.mpr hab).image X
  have hsampleSub :
      (Set.range fun q : ℚ => F q) ⊆ X '' Icc a b := by
    rintro z ⟨q, rfl⟩
    exact ⟨clampInterval a b q, clampInterval_mem hab, rfl⟩
  have hsamplesBdd : BddBelow (Set.range fun q : ℚ => F q) :=
    hcompact.bddBelow.mono hsampleSub
  have hsampleLower : ∀ q : ℚ,
      sInf (Set.range fun q : ℚ => F q) ≤ F q := by
    intro q
    exact csInf_le hsamplesBdd ⟨q, rfl⟩
  have hrangeLower : ∀ t ∈ Icc a b,
      sInf (Set.range fun q : ℚ => F q) ≤ X t := by
    intro t ht
    have hdense : DenseRange (fun q : ℚ => (q : ℝ)) := Rat.denseRange_cast
    have himage : F t ∈ closure (F '' Set.range fun q : ℚ => (q : ℝ)) :=
      hF.range_subset_closure_image_dense hdense ⟨t, rfl⟩
    have hclosed : IsClosed (Ici (sInf (Set.range fun q : ℚ => F q))) := isClosed_Ici
    have hsub : F '' Set.range (fun q : ℚ => (q : ℝ)) ⊆
        Ici (sInf (Set.range fun q : ℚ => F q)) := by
      rintro z ⟨q, hq, hz⟩
      obtain ⟨q', rfl⟩ := hq
      subst z
      exact hsampleLower q'
    have hmem := closure_minimal hsub hclosed himage
    have hclamp : clampInterval a b t = t := by
      simp [clampInterval, ht.1, ht.2]
    simpa [F, hclamp] using hmem
  have hfullLower : sInf (X '' Icc a b) ≤
      sInf (Set.range fun q : ℚ => F q) := by
    apply le_csInf (Set.range_nonempty _)
    rintro z ⟨q, rfl⟩
    exact csInf_le hcompact.bddBelow
      ⟨clampInterval a b q, clampInterval_mem hab, rfl⟩
  have hrationalLower :
      sInf (Set.range fun q : ℚ => F q) ≤ sInf (X '' Icc a b) := by
    apply le_csInf hne
    rintro z ⟨t, ht, rfl⟩
    exact hrangeLower t ht
  unfold intervalInf
  change sInf (X '' Icc a b) = sInf (Set.range fun q : ℚ => F q)
  exact hfullLower.antisymm hrationalLower

private theorem measurable_intervalInf_coordinate (i : Fin 2) (a b : ℝ) :
    Measurable (fun ω : Path2 => intervalInf (fun t => lrCoord i t ω) a b) := by
  by_cases hab : a ≤ b
  · have heq : (fun ω : Path2 => intervalInf (fun t => lrCoord i t ω) a b) =
        (fun ω => sInf (Set.range fun q : ℚ => lrCoord i (clampInterval a b q) ω)) := by
      funext ω
      exact intervalInf_eq_rationalInf (continuousPathCoordinate i ω) hab
    rw [heq]
    have hm : Measurable (fun ω : Path2 => sInf
        ((fun q : ℚ => lrCoord i (clampInterval a b q) ω) '' (Set.univ : Set ℚ))) := by
      apply Measurable.sInf (s := (Set.univ : Set ℚ)) Set.countable_univ
      intro q hq
      exact measurable_lrCoord (i, clampInterval a b q)
    simpa only [Set.image_univ] using hm
  · have hba : b < a := lt_of_not_ge hab
    simp [intervalInf, Icc_eq_empty_of_lt hba]

private theorem measurable_sideCond_coordinate (ε : ℝ) (i : Fin 2) (x y : ℤ) :
    MeasurableSet {ω : Path2 | SideCond ε (fun t => lrCoord i t ω) x y} := by
  unfold SideCond
  apply measurableSet_le
  · exact (measurable_intervalInf_coordinate i _ _).max
      (measurable_intervalInf_coordinate i _ _)
  · exact measurable_intervalInf_coordinate i _ _

private theorem measurableSet_isEdge (ε : ℝ) (e : ℤ × ℤ × Bool) :
    MeasurableSet {ω : Path2 | IsEdge ε ω e} := by
  rcases e with ⟨x, y, side⟩
  cases side
  · by_cases hxy : x < y
    · by_cases hsucc : y = x + 1
      · simp [IsEdge, hxy, hsucc]
      · simpa [IsEdge, hxy, hsucc] using
          (by simpa [lrCoord] using measurable_sideCond_coordinate ε 0 x y)
    · simp [IsEdge, hxy]
  · by_cases hxy : x < y
    · by_cases hsucc : y = x + 1
      · simp [IsEdge, hxy, hsucc]
      · simpa [IsEdge, hxy, hsucc] using
          (by simpa [lrCoord] using measurable_sideCond_coordinate ε 1 x y)
    · simp [IsEdge, hxy]

/-- Boolean encoding of the edge relation, with classical decidability for its real inequalities. -/
noncomputable def edgePredicate (ε : ℝ) (ω : Path2) (e : ℤ × ℤ × Bool) : Bool :=
  by
    classical
    exact decide (IsEdge ε ω e)

/-- The edge set of the ε-mated-CRT graph is measurable as a Boolean predicate on the countable
space of labelled candidate edges. -/
theorem matedCRT_edgePredicate_measurable_holds (ε : ℝ) :
    Measurable (fun ω : Path2 => fun e : ℤ × ℤ × Bool => edgePredicate ε ω e) := by
  classical
  apply measurable_pi_iff.mpr
  intro e
  have he := measurableSet_isEdge ε e
  have h : Measurable (fun ω : Path2 => if IsEdge ε ω e then true else false) :=
    Measurable.ite he measurable_const measurable_const
  simpa [edgePredicate] using h

end MatedCRTHarmonic.MatedCRT
