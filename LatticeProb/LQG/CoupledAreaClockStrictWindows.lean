import LatticeProb.LQG.CoupledClockedStrictProduct
import LatticeProb.LQG.CoupledAreaClockCells

/-! # Strict Brownian windows under the coupled area clock -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT LatticeProb.CorrelatedBM
open scoped NNReal

namespace LatticeProb

/-- For a fixed positive mesh and an independent absolutely continuous phase,
strict window comparisons hold on the actual signed area-clock intervals. The
same clock sends the reference cells to their cone-curve interval images. -/
theorem ae_prod_coupled_area_clock_strict_windows
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∀ᵐ p ∂P.prod Q,
      let c := CellScaling.JointScalingO.clock γ
        (coneField (X p.1) (coneRadial γ γ (fun u => B u p.1) (fun u => B' u p.1)))
        (η₀ p.1)
      (∀ j : ℤ, (shiftedCompactCell (η₀ p.1) ε p.2 j : Set ℂ) =
        η p.1 '' Icc (c (ε * ((j : ℝ) - 1 + p.2))) (c (ε * ((j : ℝ) + p.2)))) ∧
      ∀ (k : Fin 2) (i j : ℤ), i + 1 < j →
        let a := ε * ((i : ℝ) - 1 + p.2)
        let b := ε * ((i : ℝ) + p.2)
        let d := ε * ((j : ℝ) - 1 + p.2)
        let e := ε * ((j : ℝ) + p.2)
        let f := fun t => lrCoord k t (bm p.1)
        max (sInf (f '' Icc (c a) (c b))) (sInf (f '' Icc (c d) (c e))) ≤
          sInf (f '' Icc (c b) (c d)) →
        max (sInf (f '' Icc (c a) (c b))) (sInf (f '' Icc (c d) (c e))) <
          sInf (f '' Icc (c b) (c d)) := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨F, G, hF, hG, hclock, hstrict⟩ :=
    exists_coupled_clocked_brownian_strict_product hC hγ hf ε hε Q hQ
  have hgood : ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ,
      (∀ t, η₀ ω t = η ω (ψ t)) ∧ (∀ t, G ω t = bm ω (ψ t)) ∧
      ∀ t, CellScaling.JointScalingO.clock γ
        (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
        (η₀ ω) t = ψ t := by
    filter_upwards [hclock, hC.areaParam,
      MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone hC hγ] with ω hw hp hv
    obtain ⟨ψ, hψ0, hcurve, _, hGψ⟩ := hw
    obtain ⟨μ, hμ⟩ := hv
    have hs0 : ψ.symm 0 = 0 := by rw [OrderIso.symm_apply_eq, hψ0]
    have hcurve' : (fun u => η₀ ω (ψ.symm u)) = (η ω : ℝ → ℂ) := by
      funext u
      rw [hcurve, ψ.apply_symm_apply]
    have harea : ∀ s t : ℝ, s ≤ t → μ ((fun u => η₀ ω (ψ.symm u)) '' Icc s t) =
        ENNReal.ofReal (t - s) := by
      rw [hcurve']
      exact hp.2 μ hμ
    refine ⟨ψ, hcurve, hGψ, ?_⟩
    intro t
    simpa only [OrderIso.symm_symm] using
      (CellScaling.JointScalingO.clock_eq hμ hs0 harea t)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood, hstrict] with p hp hs
  obtain ⟨ψ, hcurve, hGψ, hc⟩ := hp
  constructor
  · intro j
    rw [hc, hc]
    exact shifted_cell_eq_image_reparam (η₀ p.1) (η p.1) ψ hcurve hε p.2 j
  · intro k i j hij
    have hij' : (i : ℝ) + 1 < j := by exact_mod_cast hij
    have hab : ε * ((i : ℝ) - 1 + p.2) ≤ ε * ((i : ℝ) + p.2) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    have hbd : ε * ((i : ℝ) + p.2) ≤ ε * ((j : ℝ) - 1 + p.2) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    have hde : ε * ((j : ℝ) - 1 + p.2) ≤ ε * ((j : ℝ) + p.2) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    have himg (a b : ℝ) : (lrCoordPath k (G p.1)) '' Icc a b =
        (fun t => lrCoord k t (bm p.1)) '' Icc (ψ a) (ψ b) := by
      rw [show (lrCoordPath k (G p.1) : ℝ → ℝ) =
        (fun t => lrCoord k t (bm p.1)) ∘ ψ from funext (fun t => by
          change lrCoord k t (G p.1) = lrCoord k (ψ t) (bm p.1)
          simp only [lrCoord, hGψ t]), image_comp, ψ.image_Icc]
    have h := hs k i j hij
    simp only [uIcc_of_le hab, uIcc_of_le hbd, uIcc_of_le hde, himg] at h
    simpa only [hc] using h

end LatticeProb
