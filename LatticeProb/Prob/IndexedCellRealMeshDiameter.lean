import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay

/-! # Cell diameter decay at every real mesh -/

set_option autoImplicit false

noncomputable section

open Set Metric
open ReflectedGMS ReflectedGMS.Spatial

namespace LatticeProb.IndexedCellRealMeshDiameter

/-- Sublinear diameter growth in balls gives uniform small diameters after
rescaling by every sufficiently small positive real mesh. -/
theorem scaled_diam_lt_of_maxDiamHittingBall_sublinear {V : Type*}
    (F : IndexedCells V)
    (hsub : ∀ a : ℝ, 0 < a → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      maxDiamHittingBall F T ≤ ENNReal.ofReal (a * T)) (R : ℝ) :
    ∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) R, ∀ v : V,
        ε⁻¹ • z ∈ (F.cell v : Set Plane) →
          ε * Metric.diam (F.cell v : Set Plane) < η := by
  intro η hη
  let C : ℝ := max R 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right R 0]
  let a : ℝ := η / (2 * C)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨T₀, hT₀, hbound⟩ := hsub a ha
  refine ⟨C / T₀, div_pos hC hT₀, ?_⟩
  intro ε hε hεsmall z hz v hv
  have hT : T₀ ≤ C / ε := by
    apply (le_div_iff₀ hε).2
    have := (lt_div_iff₀ hT₀).1 hεsmall
    nlinarith
  have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hnorm : ‖ε⁻¹ • z‖ ≤ C / ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    have hRC : R ≤ C := by dsimp [C]; linarith [le_max_left R 0]
    calc
      ε⁻¹ * ‖z‖ ≤ ε⁻¹ * C := mul_le_mul_of_nonneg_left (hzR.trans hRC) (le_of_lt (inv_pos.mpr hε))
      _ = C / ε := by ring
  have hhit : Hits F (closedBall (0 : Plane) (C / ε)) v :=
    ⟨ε⁻¹ • z, hv, by simpa [Metric.mem_closedBall, dist_zero_right] using hnorm⟩
  have hmem : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)) ≤
      maxDiamHittingBall F (C / ε) :=
    le_iSup (fun w : {w : V // Hits F (closedBall (0 : Plane) (C / ε)) w} =>
      ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, hhit⟩
  have hdiam : Metric.diam (F.cell v : Set Plane) ≤ a * (C / ε) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hmem.trans (hbound _ hT))
  have hscaled := mul_le_mul_of_nonneg_left hdiam hε.le
  have heq : ε * (a * (C / ε)) = η / 2 := by
    dsimp [a]
    field_simp
  rw [heq] at hscaled
  linarith

end LatticeProb.IndexedCellRealMeshDiameter
