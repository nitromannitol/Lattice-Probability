/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.Proposition at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersRouteM
import LatticeProb.Bonanno.MatedCRTHarmonic.WalkSteps.WalkPath

/-!
# Corrected scaled-grid estimate

This module transfers the finite template-itinerary event to the frozen annular event and performs the finite-grid
union bound. The probabilistic and geometric inputs remain named intermediate interfaces in `Interfaces.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

private theorem mesh_eq_inv_pow (k : ℕ) : mesh k = ((2 : ℝ) ^ k)⁻¹ := by
  simp [mesh, zpow_neg, zpow_natCast]

private theorem mesh_pos (k : ℕ) : 0 < mesh k := by
  rw [mesh_eq_inv_pow]
  positivity
private theorem mesh_le_one (k : ℕ) : mesh k ≤ 1 := by
  rw [mesh_eq_inv_pow]
  apply (inv_le_one₀ (by positivity)).2
  exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))

private theorem mesh_antitone : Antitone mesh := by
  intro a b hab
  rw [mesh_eq_inv_pow, mesh_eq_inv_pow]
  apply inv_anti₀ (by positivity)
  gcongr
  norm_num


/-- Intersecting a positive-probability itinerary with the almost-sure finite-exit event preserves its lower bound;
the deterministic adapter then gives the frozen annular event. -/
theorem walkLaw_annularEvent_ge_of_itinerary
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (z : ℂ) (r ρ d p : ℝ) (x : ℤ)
    (hTS : H.TemplateSeparation z r)
    (hdiam : ∀ v, (H.cell v ∩ ball (0 : ℂ) ρ).Nonempty → Metric.diam (H.cell v) ≤ d)
    (hB : ball z (2 * r) ⊆ ball (0 : ℂ) ρ)
    (hsmall : 0 ≤ d ∧ d < r / 12)
    (hx : x ∈ verticesMeeting H.cell (sphere z r))
    (hconn : G.adj.Connected)
    (hItin : ENNReal.ofReal p ≤ G.walkLaw x {ξ | PolarTemplateItinerary H z r (G.vertexPath ξ)}) :
    ENNReal.ofReal p ≤ G.walkLaw x {ξ | G.AnnularEvent H.cell z r (G.vertexPath ξ)} := by
  classical
  let U : Set ℤ := verticesMeeting H.cell (annulus z (r / 2) (3 * r / 2))
  let Exit : Set (ℕ → G.State) := {ξ | Markov.hitTime Uᶜ (G.vertexPath ξ) ≠ ⊤}
  let Itin : Set (ℕ → G.State) := {ξ | PolarTemplateItinerary H z r (G.vertexPath ξ)}
  let Good : Set (ℕ → G.State) := {ξ | ξ ∈ Exit ∧ G.vertexPath ξ 0 = x}
  have hUfin : U.Finite := by
    simpa [U] using verticesMeeting_annulus_finite H z r
  have hExitMass : G.walkLaw x Exit = 1 := by
    simpa [Exit, U] using walkLaw_hitTime_compl_ne_top_of_connected hUfin hconn x
  have hVPmeas : Measurable G.vertexPath := by
    apply measurable_pi_iff.2
    intro n
    exact (Measurable.of_discrete (f := G.stateVertex)).comp (measurable_pi_apply n)
  have hExitMeas : MeasurableSet Exit := by
    have hHit : MeasurableSet {X : ℕ → ℤ | Markov.hitTime Uᶜ X = ⊤} :=
      Markov.measurableSet_hitTime_eq_top MeasurableSet.of_discrete
    have hne : MeasurableSet {X : ℕ → ℤ | Markov.hitTime Uᶜ X ≠ ⊤} := hHit.compl
    exact hne.preimage hVPmeas
  have haeExit : ∀ᵐ ξ ∂G.walkLaw x, ξ ∈ Exit :=
    (ae_iff_measure_eq hExitMeas.nullMeasurableSet).mpr (by rw [hExitMass, measure_univ])
  have haeStart : ∀ᵐ ξ ∂G.walkLaw x, G.vertexPath ξ 0 = x := by
    filter_upwards [MatedCRTHarmonic.WalkSteps.ae_start (G := G) x] with ξ hξ
    change G.stateVertex (ξ 0) = x
    rw [hξ]
    rfl
  have haeGood : ∀ᵐ ξ ∂G.walkLaw x, ξ ∈ Good := by
    filter_upwards [haeExit, haeStart] with ξ hExit hStart
    exact ⟨hExit, hStart⟩
  have hGoodNull : G.walkLaw x Goodᶜ = 0 := ae_iff.mp haeGood
  calc
    ENNReal.ofReal p ≤ G.walkLaw x Itin := by simpa [Itin] using hItin
    _ = G.walkLaw x (Itin ∩ Good) := (measure_inter_conull hGoodNull).symm
    _ ≤ G.walkLaw x {ξ | G.AnnularEvent H.cell z r (G.vertexPath ξ)} := measure_mono (by
      intro ξ hξ
      obtain ⟨hI, hGoodξ⟩ := hξ
      obtain ⟨hExit, hStart⟩ := hGoodξ
      have hXstart : G.vertexPath ξ 0 ∈ verticesMeeting H.cell (sphere z r) := by
        simpa [hStart] using hx
      apply annularEvent_of_polarTemplateItinerary H z r ρ d (G.vertexPath ξ)
        hTS hdiam hB hsmall hXstart (fun j => ?_) hExit hI
      obtain ⟨n, ϑ, α, β, hW, hConf, hSteps⟩ := hI
      exact hSteps j)

/-- Deterministic assembly of the diameter event and all annular itinerary events into the exact frozen v2 event. -/
theorem scaledGridControl_of_good_environment
    (F : RandomCellFamily) (k : ℕ) (q χ β ρ s₀ : ℝ)
    (S : ℕ → Finset (ℤ × ℤ × ℤ))
    (hS : FiniteGridSpecification χ β ρ S)
    (hsmallPow : mesh k ^ (q - β) < 1 / 1000)
    (ω : F.Ω) (hconn : (F.G k ω).adj.Connected)
    (hTS : ∀ z r, 0 < r →
      (∀ x, ((F.H k ω).cell x ∩ closedBall z (2 * r)).Nonempty →
        diam ((F.H k ω).cell x) ≤ r / 1000) → (F.H k ω).TemplateSeparation z r)
    (hgood : ω ∈ GridEnvironmentGood F k q χ ρ s₀ S) :
    (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ
      ((2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))) := by
  classical
  let ε := mesh k
  let p : ℝ := (2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))
  have hgood' : ω ∈ DiameterGood F k q ρ ∧
      ∀ t, t ∈ S k → ω ∈ PolarItineraryGood F k
        (gridCenter (mesh k) χ t) (gridRadius (mesh k) χ t) s₀ := by
    simpa [GridEnvironmentGood] using hgood
  have hdiamClosed : ∀ x, ((F.H k ω).cell x ∩ closedBall (0 : ℂ) ρ).Nonempty →
      diam ((F.H k ω).cell x) ≤ ε ^ q := by
    have h := hgood'.1
    simpa [GridEnvironmentGood, DiameterGood, ε] using h
  have hdiam : ∀ x, ((F.H k ω).cell x ∩ ball (0 : ℂ) ρ).Nonempty →
      diam ((F.H k ω).cell x) ≤ ε ^ q := by
    intro x hx
    rcases hx with ⟨w, hwcell, hwb⟩
    exact hdiamClosed x ⟨w, hwcell, ball_subset_closedBall hwb⟩
  refine ⟨?_, ?_⟩
  · simpa [ε] using hdiam
  · intro m n ℓ hz hrlo hrhi hball x hx
    let t : ℤ × ℤ × ℤ := (m, n, ℓ)
    let z : ℂ := gridCenter ε χ t
    let r : ℝ := gridRadius ε χ t
    have ht : t ∈ S k := by
      apply (hS k m n ℓ).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [z, t, gridCenter, ε] using hz
      · simpa [r, t, gridRadius, ε] using hrlo
      · simpa [r, t, gridRadius, ε] using hrhi
      · simpa [z, r, t, gridCenter, gridRadius, ε] using hball
    have hItin : ω ∈ PolarItineraryGood F k z r s₀ := by
      have h := hgood'.2 t ht
      simpa [GridEnvironmentGood, z, r, t, gridCenter, gridRadius, ε] using h
    have hεpos : 0 < ε := by simpa [ε] using mesh_pos k
    have hpow : ε ^ q = ε ^ β * ε ^ (q - β) := by
      rw [← Real.rpow_add hεpos β (q - β)]
      congr 1
      ring
    have hdnonneg : 0 ≤ ε ^ q := by positivity
    have hrlo' : ε ^ β ≤ r := by simpa [r, t, gridRadius, ε] using hrlo
    have hdsmallRoute : ε ^ q < r / 1000 := by
      rw [hpow]
      have hbetaPos : 0 < ε ^ β := Real.rpow_pos_of_pos hεpos β
      calc
        ε ^ β * ε ^ (q - β) < ε ^ β * (1 / 1000) :=
          mul_lt_mul_of_pos_left hsmallPow hbetaPos
        _ ≤ r / 1000 := by nlinarith [hrlo']
    have hdsmall : ε ^ q < r / 12 := by
      exact lt_of_lt_of_le hdsmallRoute (by nlinarith)
    have hball' : ball z (2 * r) ⊆ ball (0 : ℂ) ρ := by
      simpa [z, r, t, gridCenter, gridRadius, ε] using hball
    have hrouteSmall := routeM_smallCell_of_diameterGood F k ω q r ρ
      hgood'.1 z hball' (le_of_lt hdsmallRoute)
    have hrpos : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos hεpos β) hrlo'
    have hTS' := hTS z r hrpos hrouteSmall
    have hx' : x ∈ verticesMeeting (F.H k ω).cell (sphere z r) := by
      simpa [z, r, t, gridCenter, gridRadius, ε] using hx
    have hItin' : ENNReal.ofReal p ≤ (F.G k ω).walkLaw x
        {ξ | PolarTemplateItinerary (F.H k ω) z r ((F.G k ω).vertexPath ξ)} := by
      have hxGood := hItin x hx'
      simpa [p, z, r, t, gridCenter, gridRadius, ε] using hxGood
    have hAnn := walkLaw_annularEvent_ge_of_itinerary (F.H k ω) z r ρ (ε ^ q) p x
      hTS' (by simpa [ε] using hdiam) hball' ⟨hdnonneg, hdsmall⟩ hx' hconn hItin'
    simpa [p, z, r, t, gridCenter, gridRadius, ε] using hAnn

end MatedCRTHarmonic.CellFamily
