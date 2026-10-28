import LatticeProb.Graph.MatedCRT.PathGraphLemmas
import LatticeProb.Prob.CorrelatedTwoSidedBrownian

/-! # A graph constructed from correlated Brownian paths

The edge events of the path graph are measurable for the product Brownian sample space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace LatticeProb.MatedCRT

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A compact-interval infimum of a continuous process is measurable. -/
theorem measurable_path_infimum (X : Ω → RootedPath)
    (hm : ∀ t : ℝ, Measurable fun ω => (X ω).val t)
    {l u : ℝ} (hlu : l ≤ u) :
    Measurable fun ω => sInf (((X ω).val : ℝ → ℝ) '' Set.Icc l u) := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense (Set.Icc l u)
  letI : Countable D := hD.to_subtype
  have hm' : Measurable fun ω => ⨅ t : D, (X ω).val t.1.1 :=
    Measurable.iInf fun t : D => hm t.1.1
  have heq (ω : Ω) : sInf (((X ω).val : ℝ → ℝ) '' Set.Icc l u) =
      ⨅ t : D, (X ω).val t.1.1 := by
    have hb : BddBelow (Set.range fun t : Set.Icc l u => (X ω).val t.1) := by
      refine ⟨sInf (((X ω).val : ℝ → ℝ) '' Set.Icc l u), ?_⟩
      rintro _ ⟨t, rfl⟩
      exact (isLeast_sInf_image_Icc (X ω) hlu).2 ⟨t.1, t.2, rfl⟩
    have h := hdense.ciInf ((X ω).val.continuous.comp continuous_subtype_val) hb
    change (⨅ t : D, (X ω).val t.1.1) = ⨅ t : Set.Icc l u, (X ω).val t.1 at h
    rw [h]
    simp only [iInf, Set.image_eq_range]
  simpa only [heq] using hm'

/-- The `i`th correlated Brownian sample path, rooted at zero. -/
def brownianRootedPath (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => B t ω)
    (i : Fin 2) (ω : Fin 4 → Ω) : RootedPath :=
  ⟨⟨fun t => correlatedTwoSidedBrownian γ B (t, i) ω,
    correlationTransform_continuous _ _ (continuous_two_sided_brownian_pair B hc) i ω⟩, by
      simp [correlatedTwoSidedBrownian, correlationTransform, two_sided_brownian_pair_zero]⟩

omit [MeasurableSpace Ω] in
/-- Evaluation of a rooted path is evaluation of the correlated Brownian pair. -/
@[simp] theorem brownianRootedPath_apply (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => B t ω)
    (i : Fin 2) (ω : Fin 4 → Ω) (t : ℝ) :
    (brownianRootedPath γ B hc i ω).val t = correlatedTwoSidedBrownian γ B (t, i) ω := rfl

omit [MeasurableSpace Ω] in
/-- The correlated Brownian sample path is continuous at every time. -/
theorem brownianRootedPath_continuous (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => B t ω)
    (i : Fin 2) (ω : Fin 4 → Ω) :
    Continuous fun t => (brownianRootedPath γ B hc i ω).val t :=
  (brownianRootedPath γ B hc i ω).val.continuous

omit [MeasurableSpace Ω] in
/-- Each correlated Brownian sample path vanishes at time zero. -/
theorem brownianRootedPath_zero (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => B t ω)
    (i : Fin 2) (ω : Fin 4 → Ω) : (brownianRootedPath γ B hc i ω).val 0 = 0 :=
  (brownianRootedPath γ B hc i ω).property

/-- The path graph associated with a correlated Brownian sample. -/
def brownianGraph (ε : Set.Ioi (0 : ℝ)) (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => B t ω) (ω : Fin 4 → Ω) :=
  fromPaths ε (brownianRootedPath γ B hc 0 ω) (brownianRootedPath γ B hc 1 ω)

omit [MeasurableSpace Ω] in
/-- The graph incidence rule retains the exact edge label and its ordered endpoints. -/
theorem brownianGraph_isLink_iff (ε : Set.Ioi (0 : ℝ))
    (γ : {x : ℝ // 0 < x ∧ x < 2}) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous fun t => B t ω) (ω : Fin 4 → Ω)
    (e : PotentialEdge ε) (a b : Vertex ε) :
    (brownianGraph ε γ B hc ω).IsLink e a b ↔
      edgeEnabled ε (brownianRootedPath γ B hc 0 ω) (brownianRootedPath γ B hc 1 ω) e ∧
      ((a = e.1.val.1 ∧ b = e.1.val.2) ∨ (a = e.1.val.2 ∧ b = e.1.val.1)) := Iff.rfl

omit [MeasurableSpace Ω] in
/-- An edge in the first slot is present when either coordinate condition holds. -/
theorem brownianGraph_edge_zero (ε : Set.Ioi (0 : ℝ))
    (γ : {x : ℝ // 0 < x ∧ x < 2}) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous fun t => B t ω) (ω : Fin 4 → Ω) (p : OrderedPair ε) :
    (p, 0) ∈ (brownianGraph ε γ B hc ω).edgeSet ↔
      coordinateCondition ε (brownianRootedPath γ B hc 0 ω) p ∨
      coordinateCondition ε (brownianRootedPath γ B hc 1 ω) p :=
  edgeEnabled_zero_iff ε _ _ p

omit [MeasurableSpace Ω] in
/-- The second edge requires both coordinate conditions and a strictly larger gap. -/
theorem brownianGraph_edge_one (ε : Set.Ioi (0 : ℝ))
    (γ : {x : ℝ // 0 < x ∧ x < 2}) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous fun t => B t ω) (ω : Fin 4 → Ω) (p : OrderedPair ε) :
    (p, 1) ∈ (brownianGraph ε γ B hc ω).edgeSet ↔
      ε.val < p.val.2.val - p.val.1.val ∧
      coordinateCondition ε (brownianRootedPath γ B hc 0 ω) p ∧
      coordinateCondition ε (brownianRootedPath γ B hc 1 ω) p :=
  edgeEnabled_one_iff ε _ _ p

/-- Every potential edge defines a measurable event. -/
theorem measurableSet_brownianGraph_edge (ε : Set.Ioi (0 : ℝ))
    (γ : {x : ℝ // 0 < x ∧ x < 2}) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (e : PotentialEdge ε) :
    MeasurableSet {ω | edgeEnabled ε (brownianRootedPath γ B hc 0 ω)
      (brownianRootedPath γ B hc 1 ω) e} := by
  have hmeas (i : Fin 2) (t : ℝ) :
      Measurable fun ω => (brownianRootedPath γ B hc i ω).val t := by
    exact correlationTransform_measurable _ _ (measurable_two_sided_brownian_pair B hm) (t, i)
  have hcond (i : Fin 2) (p : OrderedPair ε) :
      MeasurableSet {ω | coordinateCondition ε (brownianRootedPath γ B hc i ω) p} := by
    have hgap := orderedPair_add_le ε p
    have hε : 0 < ε.val := ε.property
    have h1 := measurable_path_infimum (brownianRootedPath γ B hc i) (hmeas i)
      (l := p.val.1.val - ε.val) (u := p.val.1.val) (by linarith)
    have h2 := measurable_path_infimum (brownianRootedPath γ B hc i) (hmeas i)
      (l := p.val.2.val - ε.val) (u := p.val.2.val) (by linarith)
    have h3 := measurable_path_infimum (brownianRootedPath γ B hc i) (hmeas i)
      (l := p.val.1.val) (u := p.val.2.val - ε.val) (by linarith)
    exact measurableSet_le (h1.max h2) h3
  classical
  have hconst (p : Prop) : MeasurableSet {ω : Fin 4 → Ω | p} := by
    by_cases h : p <;> simp [h]
  unfold edgeEnabled
  exact ((hconst _).inter ((hcond 0 e.1).union (hcond 1 e.1))).union
    ((hconst _).inter ((hconst _).inter
      ((hcond 0 e.1).inter (hcond 1 e.1))))

end LatticeProb.MatedCRT
