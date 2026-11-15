import LatticeProb.LQG.BrownianShiftedGridSideStrict
import LatticeProb.LQG.PeanosphereCellEmbedding

/-! # Cellular embeddings for shifted Brownian grids -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- For a fixed positive mesh, almost every correlated Brownian path has a
rooted cellular embedding at almost every in-mesh phase, conditional on a
matching Peanosphere and the indicated curve geometry and area clock. -/
theorem ae_shifted_cellularEmbedding_of_correlatedBM
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ w ∂μ, ∀ (η : C(ℝ, ℂ)) (P : RouteM.Peanosphere w η),
      ∀ᵐ c : ℝ ∂volume, 0 ≤ c → c ≤ ε → η 0 = 0 →
        (∀ a b : ℝ, a < b → (interior (η '' Icc a b)).Nonempty) →
        ∀ (ηL : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ),
          (∀ t, η t = ηL (φ t)) →
          (∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s)) →
          ∃ H : CellularEmbedding (MatedCRT.graph ε
            ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩
            (P.locallyFinite_time_translate hε c)) 0,
            H.cell = fun x : ℤ => (fun t => η (t + c)) ''
              Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  filter_upwards [RouteM.ae_sideStrict_time_translate_of_correlatedBM hμ hε] with w hw
  intro η P
  filter_upwards [hw η P] with c hs
  intro hc0 hcε hη0 hi ηL φ hη hvol
  exact ⟨peanosphereCellularEmbedding hε hc0 hcε hη0 P hs hi φ hη hvol, rfl⟩

end MatedCRTHarmonic.MoTInput
