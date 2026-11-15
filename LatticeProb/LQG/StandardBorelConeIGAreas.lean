import LatticeProb.LQG.StandardBorelIGDrivers
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-! # Cone area limits with independent imaginary-geometry drivers

The gamma-cone and zero-cone area limits can be realized simultaneously with
an independent normalized whole-plane GFF and uniform phase.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open QuantumZipper LQGMetric MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic

namespace LatticeProb

/-- A standard Borel realization of independent cone and imaginary-geometry
sources, with the gamma-cone and zero-cone dyadic area limits. -/
theorem exists_cone_ig_area_standardBorel {γ r : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hr : 0 < r) :
    ∃ (P : Measure ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)))
      (B B' : ℝ≥0 → ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)) → ℝ)
      (X H : ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)) → DistC)
      (U : ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)) → ℝ),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsBrownianReal B' P ∧
      IndepFun (pathOf B) (pathOf B') P ∧ IsWholePlaneGFF X P ∧
      IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P ∧
      IsNormalizedWPGFF H P ∧ P.map U = volume[|Ico (0 : ℝ) r] ∧
      IndepFun H U P ∧ IndepFun (fun ω => (H ω, U ω))
        (fun ω => (X ω, pathOf B ω, pathOf B' ω)) P ∧
      ∀ᵐ ω ∂P, ∀ α ∈ ({γ, 0} : Set ℝ),
        CellScaling.IsVagueLimitC
          (CellScaling.lqgAreaApprox γ (CellScaling.coneField (X ω)
            (CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω))))
          (CellScaling.lqgArea γ (CellScaling.coneField (X ω)
            (CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)))) := by
  obtain ⟨P, B, B', X, H, U, hP, hB, hB', hBB, hX, hXB, hH, hU, hHU, hIG⟩ :=
    exists_cone_ig_drivers_standardBorel hr
  let : IsProbabilityMeasure P := hP
  have hlim (α : ℝ) (hα : α < QuantumZipper.Qc γ) :
      ∀ᵐ ω ∂P, CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω))))
        (CellScaling.lqgArea γ (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)))) := by
    exact LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2 hα hX hB hB' hBB
      (MesoModel.FrozenIdentities.indepFun_motConeRadial_of_indep γ α hB hB' hXB)
  have hq : γ < QuantumZipper.Qc γ := MesoModel.FrozenIdentities.lt_lqgQ ⟨hγ, hγ2⟩
  have hq0 : (0 : ℝ) < QuantumZipper.Qc γ := MesoModel.FrozenIdentities.lqgQ_pos hγ
  refine ⟨P, B, B', X, H, U, hP, hB, hB', hBB, hX, hXB, hH, hU, hHU, hIG, ?_⟩
  filter_upwards [hlim γ hq, hlim 0 hq0] with ω hγlim h0lim α hα
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl
  · exact hγlim
  · exact h0lim

end LatticeProb
