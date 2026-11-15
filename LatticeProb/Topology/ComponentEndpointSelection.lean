import LatticeProb.Topology.ComponentIntervalWitness
import LatticeProb.Topology.ProperFiberComponentEndpoints
import LatticeProb.Prob.JointWitnessUniqueSelection

/-! # Measurable selection of component interval endpoints -/

set_option autoImplicit false

open Function MeasureTheory Set

namespace LatticeProb

/-- A full family of proper area-parametrized curve witnesses with common fibres
admits measurable endpoints for its nondegenerate component intervals. -/
theorem exists_measurable_component_endpoints_of_joint_witnesses
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (R : X → ℝ → ℝ → Prop) (s u t : ℝ) {A : Set (X × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, IsProperMap p.2 ∧ Surjective p.2 ∧
      (∀ v w, p.2 v = p.2 w ↔ R p.1 v w) ∧
      p.2 u ∈ interior (p.2 '' Icc s t) ∧
      (∃ ν : Measure ℂ, ∀ v w, v < w →
        ν (p.2 '' Icc v w) = ENNReal.ofReal (w - v)) ∧
      ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
        p.2 '' Icc a b = closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u))) :
    ∃ F : X → ℝ × ℝ, Measurable F ∧ ∀ᵐ p ∂μ,
      s ≤ (F p.1).1 ∧ (F p.1).1 < (F p.1).2 ∧ (F p.1).2 ≤ t ∧
      p.2 '' Icc (F p.1).1 (F p.1).2 =
        closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)) := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  let E : Set ((X × C(ℝ, ℂ)) × (ℝ × ℝ)) := {q |
    s ≤ q.2.1 ∧ q.2.1 < q.2.2 ∧ q.2.2 ≤ t ∧
      q.1.2 '' Icc q.2.1 q.2.2 =
        closure (connectedComponentIn (interior (q.1.2 '' Icc s t)) (q.1.2 u))}
  have hm : Measurable (fun q : (X × C(ℝ, ℂ)) × (ℝ × ℝ) =>
      ((q.1.2, q.1.2 u), q.2)) :=
    ((measurable_snd.comp measurable_fst).prodMk
      ((ContinuousMap.measurable_eval u).comp (measurable_snd.comp measurable_fst))).prodMk
        measurable_snd
  have hE : MeasurableSet E := by
    have hw := (measurableSet_bounded_component_interval s t).preimage hm
    have hl : MeasurableSet {q : (X × C(ℝ, ℂ)) × (ℝ × ℝ) | q.2.1 < q.2.2} :=
      measurableSet_lt (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    convert hw.inter hl using 1
    ext q
    simp only [E, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨ha, hab, hb, he⟩
      exact ⟨⟨ha, le_of_lt hab, hb, he.symm⟩, hab⟩
    · rintro ⟨⟨ha, hab, hb, he⟩, hlt⟩
      exact ⟨ha, hlt, hb, he.symm⟩
  apply exists_measurable_of_unique_joint_witness μ hA hfull hE
  · intro p hp
    obtain ⟨_, _, _, _, _, a, b, ha, hab, hb, he⟩ := hsource p hp
    exact ⟨(a, b), ha, hab, hb, he⟩
  · intro x f g z z' hf hg hz hz'
    obtain ⟨hfp, hfs, hfr, hfu, _, _⟩ := hsource (x, f) hf
    obtain ⟨hgp, hgs, hgr, _, ⟨ν, harea⟩, _⟩ := hsource (x, g) hg
    have hfib : ∀ v w, f v = f w ↔ g v = g w :=
      fun v w => (hfr v w).trans (hgr v w).symm
    have he := endpoints_eq_of_proper_maps_same_fibers_components f g ν hfp hgp hfs hgs
      hfib harea s t u z.1 z.2 z'.1 z'.2 hfu hz.2.1 hz'.2.1 hz.2.2.2 hz'.2.2.2
    exact Prod.ext he.1 he.2

end LatticeProb
