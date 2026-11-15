import LatticeProb.LQG.CoupledClockedPeanosphereStrict
import LatticeProb.LQG.ShiftedWindowInfiniteContact
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimeReconstructionAdapter

/-! # Infinite contact for coupled area-clock cells -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- On one product-full event, each weak side condition for nonconsecutive
shifted cells entails infinitely many common points of the corresponding
area-clock cells. -/
theorem exists_coupled_clocked_infinite_contact
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
      ∀ᵐ p ∂P.prod Q,
        let c := CellScaling.JointScalingO.clock γ
          (coneField (X p.1) (coneRadial γ γ (fun u => B u p.1) (fun u => B' u p.1)))
          (η₀ p.1)
        ∀ (b : Bool) (i j : ℤ), i + 1 < j →
          MatedCRT.SideCond ε
            (fun t => if b then (G p.1 (t + ε * p.2)).2 else (G p.1 (t + ε * p.2)).1)
            i j →
          (η p.1 '' Icc (c (ε * ((i : ℝ) - 1 + p.2))) (c (ε * ((i : ℝ) + p.2))) ∩
            η p.1 '' Icc (c (ε * ((j : ℝ) - 1 + p.2))) (c (ε * ((j : ℝ) + p.2)))).Infinite := by
  obtain ⟨G, hG, hclock, hstrict⟩ :=
    exists_coupled_clocked_peanosphere_strict hC hγ hf ε hε Q hQ
  refine ⟨G, hG, hclock, ?_⟩
  have hc := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually hclock
  have hfin := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually
    (GMS4c.ae_zero_bundle_finite_quantum_visits hC)
  filter_upwards [hc, hfin, hstrict] with p hc hfin hs
  obtain ⟨ψ, _, hη, _, hψ, hp⟩ := hc
  dsimp only
  intro b i j hij hside
  have hwin := hs b i j hij hside
  have hwin' : RouteM.dWinLo ε
      (fun t => if b then (G p.1 (t + ε * p.2)).2 else (G p.1 (t + ε * p.2)).1) i j <
      RouteM.dWinHi ε
      (fun t => if b then (G p.1 (t + ε * p.2)).2 else (G p.1 (t + ε * p.2)).1) i j := by
    simpa only [RouteM.dWinLo, RouteM.dWinHi, ContinuousMap.coe_mk] using hwin
  have h := infinite_clocked_cell_inter_of_strict_window ψ hη hε hij hp hfin b hwin'
  simpa only [hψ] using h

end LatticeProb
