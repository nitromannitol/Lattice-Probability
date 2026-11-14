/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.OpenCrossingLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldComparison
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDist
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal
open LQGMetric (lfppLen)
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem crossLenIn_eq_iInf_exhaustK (ξ : ℝ) (f : ℂ → ℝ)
    (U : Opens ℂ) (A B : Set ℂ) :
    crossLenIn ξ f U A B =
      ⨅ n : ℕ, crossLenIn ξ f (LQGMetric.exhaustK U n) A B := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun n => crossLenIn_mono_domain ξ f
      (LQGMetric.exhaustK_subset U n)
  · apply le_crossLenIn
    intro P hP
    obtain ⟨z, hz, w, hw, hpath, hinside⟩ := hP
    let C : Set ℂ := P '' Icc (0 : ℝ) 1
    have hC : IsCompact C := isCompact_Icc.image_of_continuousOn hpath.continuousOn
    have hCU : C ⊆ U := by
      rintro x ⟨t, ht, rfl⟩
      exact hinside t ht
    obtain ⟨n, hn⟩ := LQGMetric.exists_exhaustK_superset U hC hCU
    calc
      (⨅ n : ℕ, crossLenIn ξ f (LQGMetric.exhaustK U n) A B) ≤
          crossLenIn ξ f (LQGMetric.exhaustK U n) A B :=
            iInf_le (fun j : ℕ => crossLenIn ξ f (LQGMetric.exhaustK U j) A B) n
      _ ≤ lfppLen ξ f P := crossLenIn_le_lfppLen
        ⟨z, hz, w, hw, hpath, fun t ht => hn ⟨t, ht, rfl⟩⟩

 


theorem measurable_crossLenIn_open
    {Ω : Type*} [MeasurableSpace Ω] (ξ : ℝ) (U : Opens ℂ)
    (A B : Set ℂ) (Y : ℂ → Ω → ℝ)
    (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hYm : ∀ z, Measurable (Y z)) :
    Measurable fun ω => crossLenIn ξ (fun z => Y z ω) U A B := by
  have heq : (fun ω => crossLenIn ξ (fun z => Y z ω) U A B) =
      fun ω => ⨅ n : ℕ, crossLenIn ξ (fun z => Y z ω)
        (LQGMetric.exhaustK U n) A B := by
    funext ω
    exact crossLenIn_eq_iInf_exhaustK ξ (fun z => Y z ω) U A B
  rw [heq]
  exact Measurable.iInf fun n => measurable_crossLenIn
    (LQGMetric.exhaustK U n).2 hYc hYm

 


theorem measure_crossLenIn_open_eq
    {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) (P₂ : Measure Ω₂) (ξ : ℝ) (U : Opens ℂ)
    (A B : Set ℂ) {Y : ℂ → Ω → ℝ} {Y₂ : ℂ → Ω₂ → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hYm : ∀ z, Measurable (Y z))
    (hY₂c : ∀ ω, Continuous fun z => Y₂ z ω)
    (hY₂m : ∀ z, Measurable (Y₂ z))
    (hlaw : P.map (fun ω => (Y · ω)) = P₂.map (fun ω => (Y₂ · ω)))
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | crossLenIn ξ (fun z => Y z ω) U A B ∈ S} =
      P₂ {ω | crossLenIn ξ (fun z => Y₂ z ω) U A B ∈ S} := by
  have hgm : Measurable fun f : C(ℂ, ℝ) =>
      crossLenIn ξ (fun z => f z) U A B :=
    measurable_crossLenIn_open ξ U A B (fun z (f : C(ℂ, ℝ)) => f z)
      (fun f => f.continuous) (fun z => ContinuousMap.measurable_eval z)
  have hE : MeasurableSet[MeasurableSpace.comap
      (fun f : C(ℂ, ℝ) => (f : ℂ → ℝ)) MeasurableSpace.pi]
      {f : C(ℂ, ℝ) | crossLenIn ξ (fun z => f z) U A B ∈ S} := by
    rw [← measurableSpace_continuousMap_eq_comap]
    exact hgm hS
  obtain ⟨T, hT, hTE⟩ := hE
  have key : ∀ g : ℂ → ℝ, Continuous g →
      (crossLenIn ξ g U A B ∈ S ↔ g ∈ T) := by
    intro g hg
    have he := congrArg (fun E => (⟨g, hg⟩ : C(ℂ, ℝ)) ∈ E) hTE
    simp only [mem_preimage, ContinuousMap.coe_mk, mem_ofPred_eq, eq_iff_iff] at he
    exact he.symm
  have h1 : {ω | crossLenIn ξ (fun z => Y z ω) U A B ∈ S} =
      (fun ω => (Y · ω)) ⁻¹' T := by
    ext ω
    exact key _ (hYc ω)
  have h2 : {ω | crossLenIn ξ (fun z => Y₂ z ω) U A B ∈ S} =
      (fun ω => (Y₂ · ω)) ⁻¹' T := by
    ext ω
    exact key _ (hY₂c ω)
  rw [h1, h2, ← Measure.map_apply (measurable_pi_iff.2 hYm) hT,
    ← Measure.map_apply (measurable_pi_iff.2 hY₂m) hT, hlaw]

end SupercriticalLQGUniqueness.B2.DG20Pt
