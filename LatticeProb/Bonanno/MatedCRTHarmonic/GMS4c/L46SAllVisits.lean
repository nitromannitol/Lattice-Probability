/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.L46SAllVisits at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCount
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SWindow
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimedObservables

/-! The Brownian-chain count of `L46SCount` applies at every visit time. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MoTInput

/-- The coupled finite-region estimate before selecting a first hit. Its
conclusion holds simultaneously at all visits of every point in the test ball. -/
theorem l46s_coupled_bound_all_visits
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ k : ℕ, ∀ {ε : ℝ}, 0 < ε → ∀ (T : ℝ), 0 ≤ T → ∀ (n : ℕ) (ρ : ℝ), ∀ᵐ ω ∂P,
      (ball (0 : ℂ) 1 ⊆ η ω '' Icc (-T) T) →
      (∀ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ →
        locWindow ε (η ω) t ⊆ ball (0 : ℂ) 1) →
      (∀ x ∈ Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1),
        lemma25Degree ε (bm ω) x ≤ (n : ℕ∞)) →
      ∀ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ →
        locDegIn ε (η ω) t ≤ 9 * ((n + 1) ^ (2 * k) : ℕ∞) := by
  obtain ⟨k, hk⟩ := VisitBound.of_bundle D
  refine ⟨k, ?_⟩
  intro ε hε T hT n ρ
  let M := cellModelOfCoupling D hγ
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFinite ε (bm ω) := by
    have hm := MatedCRTHarmonic.ae_isLocallyFinite_holds γ (P.map bm)
      D.boundaryLawBM ε hε
    exact ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hm
  have hvisit := VisitBound.areaParam D hk
  filter_upwards [hlocal, hvisit, ae_peanosphere D, M.ae_area_curve]
    with ω hloc hvis hP harea
  intro hcover hwindow hraw t ht
  have hconf : (η ω : ℝ → ℂ) ⁻¹' ball (0 : ℂ) 1 ⊆ Icc (-T) T :=
    preimage_ball_subset_covered_interval (η ω) harea (by linarith) hcover
  have hD : ∀ v : {x : ℤ // x ∈ Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1)},
      (((graph ε (bm ω) hloc).adj.induce
        (Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1))).neighborSet v).ncard ≤ n := by
    intro v
    apply (l46s_induced_degree_le_multidegree (graph ε (bm ω) hloc) _ v).trans
    have hv := hraw v.val v.property
    rw [lemma25Degree_eq_graph_deg hloc] at hv
    exact_mod_cast hv
  apply locDegIn_le_three_graph_balls hP hε hloc hvis
    (M := T) (R := 1) (t₀ := t)
  · exact hwindow t ht
  · exact hconf
  · exact hD

/-- The finite Brownian-chain bound also controls the all-visit observable
at every point of the test ball. -/
theorem l46s_prime_le_on_good_event
    {ε ρ : ℝ} {c : ℝ → ℂ} {N : ℕ∞}
    (h : ∀ t : ℝ, c t ∈ ball (0 : ℂ) ρ → locDegIn ε c t ≤ N) :
    ∀ z ∈ ball (0 : ℂ) ρ, degreeInPrime ε c z ≤ N := by
  intro z hz
  unfold degreeInPrime
  refine iSup_le fun t => iSup_le fun ht => ?_
  exact h t (ht ▸ hz)

end MatedCRTHarmonic.GMS4c

