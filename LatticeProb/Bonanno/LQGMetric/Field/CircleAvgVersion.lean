import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Measurable continuous version of the circle averages of a whole-plane GFF

For a whole-plane Gaussian free field `h`, the circle averages `(r, z) ↦ circleAvg (h ω) r z` admit, for
every sample `ω`, a version continuous in `(r, z) ∈ (0, ∞) × ℂ` (Kolmogorov continuity; Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 2011, Section 3). This file packages the normalized version
`(r, z) ↦ circleAvg h r z − circleAvg h 1 0` as a random element `Ω → C((0, ∞) × ℂ, ℝ)`: it is measurable for the
Borel σ-algebra of the continuous functions (Mathlib `ContinuousMap.measurableSpace`), vanishes at `(1, 0)` for
every sample, and agrees almost surely with the normalized circle average at each parameter.
-/

namespace LatticeProb

open MeasureTheory Filter Topology Set LQGMetric

noncomputable section

/-- A map into the continuous functions on a second countable space is almost everywhere measurable as soon as
each evaluation is (Mathlib `ContinuousMap.measurable_iff_eval`). -/
theorem aemeasurable_continuousMap_of_evaluations {X Ω : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace Ω] {P : Measure Ω} {F : Ω → C(X, ℝ)}
    (hF : ∀ x : X, AEMeasurable (fun ω => F ω x) P) : AEMeasurable F P := by
  have hn : NullMeasurable F P := by
    change @Measurable (NullMeasurableSpace Ω P) _ _ _ F
    apply ContinuousMap.measurable_iff_eval.mpr
    intro x
    exact (hF x).nullMeasurable.measurable'
  exact hn.aemeasurable

/-- **Normalized continuous circle-average version.** For a whole-plane GFF `h`, there is a random continuous
function `F : Ω → C((0, ∞) × ℂ, ℝ)`, measurable for the Borel σ-algebra of `C((0, ∞) × ℂ, ℝ)`, with `F ω (1, 0) = 0`
for every sample `ω`, and with `F · p = circleAvg h p.1 p.2 − circleAvg h 1 0` almost surely for every parameter
`p = (r, z)`. -/
theorem exists_measurable_continuous_circleAvg_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    ∃ F : Ω → C(Set.Ioi (0 : ℝ) × ℂ, ℝ), Measurable F ∧
      (∀ ω, F ω ((⟨1, Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : ℝ)), (0 : ℂ)) = 0) ∧
      ∀ p : Set.Ioi (0 : ℝ) × ℂ,
        (fun ω => F ω p) =ᵐ[P] fun ω => circleAvg (h ω) p.1 p.2 - circleAvg (h ω) 1 0 := by
  have : LocallyCompactSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  obtain ⟨H, hHc, hHae⟩ := CircleAvg.exists_continuous_version_circleAvg hh
  -- normalization at `(1, 0)`: `H 1 0` vanishes almost surely, and `G` vanishes there identically
  set G : ℝ → ℂ → Ω → ℝ := fun r z ω => H r z ω - H 1 0 ω with hG_def
  have hGc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2 ω) (Ioi 0 ×ˢ univ) := fun ω =>
    ContinuousOn.sub (hHc ω) continuousOn_const
  have h10 : ∀ᵐ ω ∂P, H 1 0 ω = 0 := by
    filter_upwards [hHae 1 one_pos 0] with ω hω
    rw [hω, sub_self]
  have hGae : ∀ r, 0 < r → ∀ z,
      (fun ω => G r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z - circleAvg (h ω) 1 0 := by
    intro r hr z
    filter_upwards [hHae r hr z, h10] with ω h1 h2
    simp only [hG_def]
    rw [h1, h2, sub_zero]
  have hcirc_meas : ∀ r z, Measurable fun ω => circleAvg (h ω) r z := fun r z =>
    (measurable_circleAvg_left r z).comp hh.measurable
  have hmeas : ∀ p : Set.Ioi (0 : ℝ) × ℂ, AEMeasurable (fun ω => G p.1 p.2 ω) P := by
    rintro ⟨⟨r, hr⟩, z⟩
    have hr' : 0 < r := hr
    exact ((hcirc_meas r z).sub (hcirc_meas 1 0)).aemeasurable.congr (hGae r hr' z).symm
  -- the random continuous function, then a measurable modification of it
  let K : Ω → C(Set.Ioi (0 : ℝ) × ℂ, ℝ) := fun ω =>
    ⟨fun p => G p.1 p.2 ω, continuousOn_univ.mp ((hGc ω).comp
      (continuous_subtype_val.prodMap continuous_id).continuousOn
      (by intro p _; exact ⟨p.1.2, Set.mem_univ _⟩))⟩
  have hKm : AEMeasurable K P := aemeasurable_continuousMap_of_evaluations hmeas
  let L := hKm.mk K
  have hLm : Measurable L := hKm.measurable_mk
  have hLK : K =ᵐ[P] L := hKm.ae_eq_mk
  let q : Set.Ioi (0 : ℝ) × ℂ := ((⟨1, Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : ℝ)), (0 : ℂ))
  refine ⟨fun ω => L ω - ContinuousMap.const _ (L ω q), ?_, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro p
    exact ((ContinuousMap.measurable_eval p).comp hLm).sub
      ((ContinuousMap.measurable_eval q).comp hLm)
  · intro ω
    change L ω q - L ω q = 0
    exact sub_self _
  · intro p
    filter_upwards [hLK, hGae p.1 p.1.2 p.2] with ω hk hg
    have e1 : L ω p = G p.1 p.2 ω := by
      rw [← hk]
      rfl
    have e2 : L ω q = 0 := by
      rw [← hk]
      show H 1 0 ω - H 1 0 ω = 0
      exact sub_self _
    change L ω p - L ω q = _
    rw [e1, e2, sub_zero]
    exact hg

end

end LatticeProb
