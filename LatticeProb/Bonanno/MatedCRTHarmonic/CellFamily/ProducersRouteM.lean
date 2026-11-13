/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.ProducersRouteM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.Compose

/-!
# Route M producer for the scaled-grid estimate cell-separation interface

The mating-of-trees layer supplies the Peanosphere/G0 package; the deterministic Route M composition turns it into
`CellularEmbedding.TemplateSeparation` whenever the cells near the annulus are sufficiently small.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

private def transferWalk {V : Type*} {G G' : SimpleGraph V}
    (hadj : ∀ ⦃x y⦄, G.Adj x y → G'.Adj x y) {x y : V} :
    G.Walk x y → G'.Walk x y
  | .nil => .nil
  | .cons h w => .cons (hadj h) (transferWalk hadj w)

private theorem transferWalk_support {V : Type*} {G G' : SimpleGraph V}
    (hadj : ∀ ⦃x y⦄, G.Adj x y → G'.Adj x y) {x y : V} (w : G.Walk x y) :
    (transferWalk hadj w).support = w.support := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [transferWalk, ih]

/-- Transfer the Route M separation conclusion across a cell-preserving graph adjacency identification. -/
private theorem templateSeparation_transfer
    {V E E' : Type*} {G : LFMultigraph V E} {G' : LFMultigraph V E'} {o : V}
    (H : CellularEmbedding G o) (H' : CellularEmbedding G' o)
    (hadj : ∀ x y, G.adj.Adj x y ↔ G'.adj.Adj x y)
    (hcell : ∀ x, H.cell x = H'.cell x) {z : ℂ} {r : ℝ}
    (hsep : H'.TemplateSeparation z r) : H.TemplateSeparation z r := by
  intro ϑ n v α β hadjWalk hα0 hβn hαmono hβmono hoverlap hwidth hnear
  have hsep' := hsep ϑ n v α β
    (fun j hj => (hadj (v j) (v (j + 1))).mp (hadjWalk j hj))
    hα0 hβn hαmono hβmono hoverlap hwidth
    (by
      intro j hj s hs w hw
      have hw' : w ∈ H.cell (v j) := by rw [hcell (v j)]; exact hw
      exact hnear j hj s hs w hw')
  intro a ha b hb w
  let w' : G'.adj.Walk a b := transferWalk (fun {x y} h => (hadj x y).mp h) w
  have ha' : a ∈ verticesMeeting H'.cell (Metric.sphere z (3 * r / 4)) := by
    simpa [verticesMeeting, hcell] using ha
  have hb' : b ∈ verticesMeeting H'.cell (Metric.sphere z (5 * r / 4)) := by
    simpa [verticesMeeting, hcell] using hb
  obtain ⟨y, hywalk, hytrace⟩ := hsep' a ha' b hb' w'
  refine ⟨y, ?_, ?_⟩
  · have hsup : w'.support = w.support := by
      change (transferWalk (fun {x y} h => (hadj x y).mp h) w).support = w.support
      exact transferWalk_support _ w
    rw [hsup] at hywalk
    exact hywalk
  · simpa [verticesMeeting, hcell] using hytrace

/-- Route M proves the family-level separation interface from the Peanosphere/G0 input. The small-cell condition is
explicit, since Lemma 2.7 only supplies it at the mesh-dependent annulus scales used in the scaled-grid estimate. -/
theorem templateSeparation_of_peanosphereG0
    (F : RandomCellFamily) (hPG : PeanosphereG0 F) : TemplateSeparation F := by
  intro k
  filter_upwards [hPG k] with ω hω
  rcases hω with ⟨path, η, hloc, H', hP, hG, hadj, hcells, hcell⟩
  intro z r hr hsmall
  have hcell' : H'.cell = fun x : ℤ => η ''
      Set.Icc (mesh k * ((x : ℝ) - 1)) (mesh k * x) := by
    funext x
    exact hcell x
  have hsmall' : ∀ x, (H'.cell x ∩ closedBall z (2 * r)).Nonempty →
      diam (H'.cell x) ≤ r / 1000 := by
    intro x hx
    have hx' : ((F.H k ω).cell x ∩ closedBall z (2 * r)).Nonempty := by
      simpa [hcells x] using hx
    simpa [hcells x] using hsmall x hx'
  apply templateSeparation_transfer (F.H k ω) H' hadj hcells
  exact RouteM.templateSeparation_matedCRT hP hG H' hcell' hr hsmall'

/-- The route theorem's precise deterministic small-cell obligation, obtained from the Lemma 2.7 event whenever the
radius dominates the mesh exponent by the displayed factor. -/
theorem routeM_smallCell_of_diameterGood
    (F : RandomCellFamily) (k : ℕ) (ω : F.Ω) (q r ρ : ℝ)
    (hdiam : ω ∈ DiameterGood F k q ρ)
    (z : ℂ) (hball : ball z (2 * r) ⊆ ball (0 : ℂ) ρ)
    (hr : mesh k ^ q ≤ r / 1000) :
    ∀ x, ((F.H k ω).cell x ∩ closedBall z (2 * r)).Nonempty →
      diam ((F.H k ω).cell x) ≤ r / 1000 := by
  have hmesh : 0 < mesh k := by
    dsimp [mesh]
    positivity
  have hqpos : 0 < mesh k ^ q := Real.rpow_pos_of_pos hmesh q
  have hrpos : 0 < r := by
    have h := lt_of_lt_of_le hqpos hr
    nlinarith
  intro x hx
  have hρpos : 0 < ρ := by
    have hz : z ∈ ball z (2 * r) := by
      rw [Metric.mem_ball]
      simpa using (show dist z z < 2 * r by simp [hrpos])
    have : z ∈ ball (0 : ℂ) ρ := hball hz
    exact lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp this)
  have hclosed : closedBall z (2 * r) ⊆ closedBall (0 : ℂ) ρ := by
    have hcl := closure_mono hball
    rw [closure_ball z (by positivity : 2 * r ≠ 0),
      closure_ball (0 : ℂ) hρpos.ne'] at hcl
    exact hcl
  rcases hx with ⟨w, hwcell, hwdisk⟩
  have hx' : ((F.H k ω).cell x ∩ closedBall (0 : ℂ) ρ).Nonempty :=
    ⟨w, hwcell, hclosed hwdisk⟩
  exact (hdiam x hx').trans hr

end MatedCRTHarmonic.CellFamily
