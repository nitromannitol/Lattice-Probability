import LatticeProb.LQG.CoupledClockedPeanosphereStrict
import LatticeProb.LQG.PeanosphereCellEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-! # Shifted embeddings for a coupled reference clock -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- At a fixed mesh, the common clocked contour and reference curve have a
rooted shifted cellular embedding for almost every independent phase in `[0,1]`. -/
theorem exists_coupled_clocked_cellularEmbedding
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∃ G : Ω → Path2, Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, G ω t = bm ω (ψ t)) ∧
        (∀ t, CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t = ψ t) ∧ RouteM.Peanosphere (G ω) (η₀ ω)) ∧
      ∀ᵐ p ∂P.prod Q, 0 ≤ p.2 → p.2 ≤ 1 →
        let w : Path2 := ⟨fun t => G p.1 (t + ε * p.2),
          (G p.1).continuous.comp (by fun_prop)⟩
        ∃ (hlf : IsLocallyFinite ε w)
          (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
          H.cell = fun x : ℤ => (fun t => η₀ p.1 (t + ε * p.2)) ''
            Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  obtain ⟨G, hG, hclock, hstrict⟩ :=
    exists_coupled_clocked_peanosphere_strict hC hγ hf ε hε Q hQ
  refine ⟨G, hG, hclock, ?_⟩
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  have hclock' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually hclock
  have hi := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually
    (MoTInput.ae_curve_intervals_have_interior hC)
  have ha := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually hC.areaParam₀
  have hs := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually hC.spaceFilling
  filter_upwards [hclock', hi, ha, hs, hstrict] with p hclock hi ha hs hstrict
  intro hθ0 hθ1
  obtain ⟨ψ, hψ0, hcurve, hcontour, hclockeq, hp⟩ := hclock
  obtain ⟨⟨φ, hφ0, hη⟩, _⟩ := ha
  obtain ⟨_, _, hηL0, hvol⟩ := hs
  have hη0 : η₀ p.1 0 = 0 := by rw [hη, hφ0, hηL0]
  have hi₀ : ∀ a b : ℝ, a < b → (interior (η₀ p.1 '' Icc a b)).Nonempty := by
    intro a b hab
    have himage : η₀ p.1 '' Icc a b = η p.1 '' Icc (ψ a) (ψ b) := by
      rw [show (η₀ p.1 : ℝ → ℂ) = (η p.1 : ℝ → ℂ) ∘ ψ from funext hcurve,
        Set.image_comp, ψ.image_Icc]
    rw [himage]
    exact hi (ψ a) (ψ b) (ψ.strictMono hab)
  have hc0 : 0 ≤ ε * p.2 := mul_nonneg hε.le hθ0
  have hcε : ε * p.2 ≤ ε := by nlinarith
  exact ⟨hp.locallyFinite_time_translate hε (ε * p.2),
    MoTInput.peanosphereCellularEmbedding hε hc0 hcε hη0 hp hstrict hi₀ φ hη hvol, rfl⟩

end LatticeProb
