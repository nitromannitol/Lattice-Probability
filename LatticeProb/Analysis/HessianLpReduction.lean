import Mathlib

/-! # Interior Hessian estimates

Reduction statements for local Hessian bounds.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace LatticeProb.PegdenSmart

/-- Interior `L^p` Hessian bound for `2 ≤ p < ∞`: for `w` smooth on the ball
`B(a, r)`, the `L^p` norm of `D²w` on `B(a, r / 2)` is at most a constant (depending on the space,
`μ`, `p`, `a` and `r`) times the `L^p` norm of `Δ w` plus the supremum of `|w|` on `B(a, r)`. -/
def HessianLpStmt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞),
    2 ≤ p → p ≠ ⊤ →
    ∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)))

end LatticeProb.PegdenSmart

namespace HessianAdapter

/-- The Euclidean model space. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ### The target for one pair `(E, μ)` -/

/-- The body of `HessianLpStmt` for one space `E` and one Haar measure `μ`. -/
def Q2At (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (p : ℝ≥0∞), 2 ≤ p → p ≠ ⊤ → ∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)))

theorem hessianLpStmt_iff :
    LatticeProb.PegdenSmart.HessianLpStmt ↔
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], Q2At E μ :=
  Iff.rfl

/-- `Q2At`, only for the functions whose right-hand side is finite. -/
def Q2FinAt (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (p : ℝ≥0∞), 2 ≤ p → p ≠ ⊤ → ∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)) ≠ ⊤ →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)))

/-- A finite right-hand side estimate extends to arbitrary functions. -/
theorem L1_infinite_rhs {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (h : Q2FinAt E μ) : Q2At E μ := by
  intro p hp hpt a r hr
  obtain ⟨C, hC, hbound⟩ := h p hp hpt a r hr
  refine ⟨C + 1, ENNReal.add_ne_top.mpr ⟨hC, by simp⟩, ?_⟩
  intro w hw
  by_cases hf : eLpNorm (Δ w) p (μ.restrict (ball a r)) +
      eLpNorm w ⊤ (μ.restrict (ball a r)) = ⊤
  · rw [hf, ENNReal.mul_top (by simp)]
    exact le_top
  · refine (hbound w hw hf).trans ?_
    gcongr
    exact le_add_of_nonneg_right bot_le

/-- In dimension zero the Hessian vanishes. -/
theorem L2_dim_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (h0 : Module.finrank ℝ E = 0) : Q2FinAt E μ := by
  let : Subsingleton E := Module.finrank_zero_iff.mp h0
  intro p hp hpt a r hr
  refine ⟨0, by simp, ?_⟩
  intro w hw hf
  simp

/-- The estimate on `B(x, ρ/2)` from data on `B(x, 4ρ/3)`, with a constant depending on `p`, `ρ`
and `d` only. -/
def LocalBallStmt (d : ℕ) : Prop :=
  ∀ (p : ℝ≥0∞), 2 ≤ p → p ≠ ⊤ → ∀ ρ : ℝ, 0 < ρ → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ (x : Euc d) (w : Euc d → ℝ), ContDiffOn ℝ ∞ w (ball x (4 * ρ / 3)) →
      eLpNorm (Δ w) p (volume.restrict (ball x (4 * ρ / 3))) +
        eLpNorm w ⊤ (volume.restrict (ball x (4 * ρ / 3))) ≠ ⊤ →
      eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p (volume.restrict (ball x (ρ / 2))) ≤
        K * (eLpNorm (Δ w) p (volume.restrict (ball x (4 * ρ / 3))) +
          eLpNorm w ⊤ (volume.restrict (ball x (4 * ρ / 3))))

/-- The same at `x = 0`, `ρ = 1`. -/
def LocalUnitStmt (d : ℕ) : Prop :=
  ∀ (p : ℝ≥0∞), 2 ≤ p → p ≠ ⊤ → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ w : Euc d → ℝ, ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)) →
      eLpNorm (Δ w) p (volume.restrict (ball (0 : Euc d) (4 / 3))) +
        eLpNorm w ⊤ (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤ →
      eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p
          (volume.restrict (ball (0 : Euc d) (1 / 2))) ≤
        K * (eLpNorm (Δ w) p (volume.restrict (ball (0 : Euc d) (4 / 3))) +
          eLpNorm w ⊤ (volume.restrict (ball (0 : Euc d) (4 / 3))))

/-- The `L²` bound for the Hessian on the model space. -/
def L2HessEucStmt (d : ℕ) : Prop :=
  ∃ C₂ : ℝ≥0∞, C₂ ≠ ⊤ ∧ ∀ w : Euc d → ℝ, ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)) →
    eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) 2 (volume.restrict (ball (0 : Euc d) 1)) ≤
      C₂ * (eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) +
        eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))))

/-- (B2) The energy inequality for a cutoff. -/
def EnergyIneqStmt (d : ℕ) : Prop :=
  ∀ (w θ : Euc d → ℝ), ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)) → ContDiff ℝ ∞ θ →
    HasCompactSupport θ → tsupport θ ⊆ ball (0 : Euc d) (4 / 3) →
    (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → ∀ M : ℝ, (∀ x, ‖fderiv ℝ θ x‖ ≤ M) →
    IntegrableOn (fun x => Δ w x ^ 2) (ball (0 : Euc d) (4 / 3)) →
    IntegrableOn (fun x => w x ^ 2) (ball (0 : Euc d) (4 / 3)) →
    (∫ x in ball (0 : Euc d) (4 / 3), θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2) ≤
      (∫ x in ball (0 : Euc d) (4 / 3), Δ w x ^ 2) +
        (1 + 4 * M ^ 2) * ∫ x in ball (0 : Euc d) (4 / 3), w x ^ 2

/-- (B1) The Hessian identity for a cutoff `η`, in the orthonormal basis `bᵢ`. -/
def HessianEnergyStmt (d : ℕ) : Prop :=
  ∀ (w η : Euc d → ℝ), ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)) → ContDiff ℝ ∞ η →
    HasCompactSupport η → tsupport η ⊆ ball (0 : Euc d) (4 / 3) →
    (∫ x, η x ^ 2 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ w) x
        (stdOrthonormalBasis ℝ (Euc d) i) (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2) =
      (∫ x, η x ^ 2 * Δ w x ^ 2) +
        2 * (∫ x, η x * Δ w x * ∑ i, fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)) -
        2 * ∫ x, η x * ∑ i, ∑ j, fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
            (stdOrthonormalBasis ℝ (Euc d) j) * fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) j)

private theorem q2_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (c : NNReal) (hc : c ≠ 0) [(c • μ).IsAddHaarMeasure]
    (h : Q2At E μ) : Q2FinAt E (c • μ) := by
  intro p hp hpt a r hr
  obtain ⟨C, hC, hbound⟩ := h p hp hpt a r hr
  let t : ℝ≥0∞ := ↑(c ^ p.toReal⁻¹)
  refine ⟨C * max 1 t, ENNReal.mul_ne_top hC (max_ne_top (by simp) (by simp [t])), ?_⟩
  intro w hw hf
  have hb := hbound w hw
  have hh : t * eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
      (C * max 1 t) * (t * eLpNorm (Δ w) p (μ.restrict (ball a r)) +
        eLpNorm w ⊤ (μ.restrict (ball a r))) := by
    calc
      _ ≤ t * (C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) +
          eLpNorm w ⊤ (μ.restrict (ball a r)))) := by gcongr
      _ = C * (t * eLpNorm (Δ w) p (μ.restrict (ball a r)) + t * eLpNorm w ⊤ (μ.restrict (ball a r))) := by simp [mul_add, mul_left_comm]
      _ ≤ (C * max 1 t) * (t * eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r))) := by
        simp only [mul_add]
        apply add_le_add
        · have hcm : C ≤ C * max 1 t := by
            calc
              C = C * 1 := (mul_one C).symm
              _ ≤ C * max 1 t := by gcongr; exact le_max_left 1 t
          gcongr
        · rw [← mul_assoc]
          gcongr
          exact le_max_right 1 t
  simp only [Measure.restrict_smul]
  change eLpNorm _ _ (c • μ.restrict _) ≤ _ * (eLpNorm _ _ (c • μ.restrict _) +
    eLpNorm _ _ (c • μ.restrict _))
  simp only [eLpNorm_smul_measure_of_ne_zero' hc, ENNReal.toReal_top, inv_zero,
    NNReal.rpow_zero, one_smul]
  simpa only [ENNReal.smul_def, smul_eq_mul, t] using hh

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem hessian_norm_comp (e : F ≃ₗᵢ[ℝ] E) (w : E → ℝ) (x : F) :
    ‖fderiv ℝ (fderiv ℝ (w ∘ e)) x‖ = ‖fderiv ℝ (fderiv ℝ w) (e x)‖ := by
  have h := e.norm_iteratedFDeriv_comp_right w x 2
  rw [← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 1)] at h
  simpa only [norm_iteratedFDeriv_one] using h

private theorem laplacian_comp (e : F ≃ₗᵢ[ℝ] E) (w : E → ℝ) (x : F) : Δ (w ∘ e) x = Δ w (e x) := by
  let b := stdOrthonormalBasis ℝ F
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (w ∘ e) b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w (b.map e)]
  simp only [OrthonormalBasis.map_apply]
  have hh := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right w
    (s := Set.univ) uniqueDiffOn_univ (x := x) (by simp) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hh
  change iteratedFDeriv ℝ 2 (w ∘ e) x = _ at hh
  rw [hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext j
  fin_cases j <;> rfl

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

private theorem eLpNorm_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (f : E → ℝ) (a : E) (r : ℝ) (p : ℝ≥0∞) :
    eLpNorm (f ∘ e.symm) p (volume.restrict (ball (e a) r)) =
      eLpNorm f p (volume.restrict (ball a r)) := by
  have hm : (volume.restrict (ball a r) : Measure E).map e =
      volume.restrict (ball (e a) r) := by
    rw [← e.measurePreserving.map_eq, Measure.restrict_map e.continuous.measurable measurableSet_ball]
    congr 2
    simp
  rw [← hm]
  change eLpNorm (f ∘ e.symm) p ((volume.restrict (ball a r) : Measure E).map e.toHomeomorph) = _
  rw [e.toHomeomorph.measurableEmbedding.eLpNorm_map_measure]
  change eLpNorm (fun x => f (e.symm (e x))) p _ = _
  simp only [LinearIsometryEquiv.symm_apply_apply]


private theorem q2_isometry (e : E ≃ₗᵢ[ℝ] F) (h : Q2At F volume) : Q2At E volume := by
  intro p hp hpt a r hr
  obtain ⟨C, hC, hbound⟩ := h p hp hpt (e a) r hr
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hw' : ContDiffOn ℝ ∞ (w ∘ e.symm) (ball (e a) r) := by
    have hh := (e.symm.toContinuousLinearEquiv.contDiffOn_comp_iff).2 hw
    change ContDiffOn ℝ ∞ (w ∘ e.symm) (e.symm ⁻¹' ball a r) at hh
    have hs := e.symm.toIsometryEquiv.preimage_ball a r
    change (e.symm ⁻¹' ball a r) = ball (e a) r at hs
    rw [hs] at hh
    exact hh
  have hb := hbound (w ∘ e.symm) hw'
  have hess : (fun x => ‖fderiv ℝ (fderiv ℝ (w ∘ e.symm)) x‖) =
      (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) ∘ e.symm := by
    funext x
    exact hessian_norm_comp e.symm w x
  have hlap : Δ (w ∘ e.symm) = (Δ w) ∘ e.symm := by
    funext x
    exact laplacian_comp e.symm w x
  rw [hess, hlap, eLpNorm_comp_isometry, eLpNorm_comp_isometry,
    eLpNorm_comp_isometry] at hb
  exact hb

/-- An estimate on the standard model gives an estimate on any Euclidean space. -/
theorem L3_model_space {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (h : Q2FinAt (Euc (Module.finrank ℝ E)) volume) : Q2FinAt E μ := by
  let e : E ≃ₗᵢ[ℝ] Euc (Module.finrank ℝ E) := (stdOrthonormalBasis ℝ E).repr
  have he : Q2At E volume := q2_isometry e (L1_infinite_rhs volume h)
  let c : NNReal := Measure.addHaarScalarFactor μ volume
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hμ : μ = c • (volume : Measure E) := Measure.isAddLeftInvariant_eq_smul μ volume
  let : (c • (volume : Measure E)).IsAddHaarMeasure := hμ ▸ ‹μ.IsAddHaarMeasure›
  have ht := q2_smul (volume : Measure E) c hc he
  unfold Q2FinAt at ht ⊢
  rw [hμ]
  exact ht

end HessianAdapter
