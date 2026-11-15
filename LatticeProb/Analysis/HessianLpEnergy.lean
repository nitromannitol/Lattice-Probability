import LatticeProb.Analysis.HessianLpReduction
import LatticeProb.Analysis.HessianLpCutoff

/-!
# The energy inequality for a cutoff

For `w` smooth on the ball of radius `4 / 3` and a smooth cutoff `θ` supported in that ball, the
cutoff energy identity `integral_cutoff_sq_grad_sq` gives the bound
`∫ θ² ‖∇w‖² ≤ ∫ (Δ w)² + (1 + 4 M²) ∫ w²`, where `M` bounds `‖∇θ‖`.  The function `w` is first
replaced by a globally smooth function that agrees with it near the support of `θ`; the bound then
follows from Young's inequality and the absorption of half of the energy.

## Main results

* `HessianAdapter.L12a_energy_ineq`: `EnergyIneqStmt d`.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace HessianAdapter

private theorem norm_sq_eq_sum_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i, (L (stdOrthonormalBasis ℝ E i)) ^ 2 := by
  have hn : ‖(InnerProductSpace.toDual ℝ E).symm L‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ L
  have h := (stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right
    ((InnerProductSpace.toDual ℝ E).symm L)
  rw [hn] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, Real.norm_eq_abs, sq_abs]

private theorem continuous_laplacian_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} (hv : ContDiff ℝ ∞ v) :
    Continuous (Δ v) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]).continuous.comp
    (hv.continuous_iteratedFDeriv (m := 2) (by simp))

private theorem exists_smooth_localization {d : ℕ} {w θ : Euc d → ℝ}
    (hw : ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)))
    (hs : tsupport θ ⊆ ball (0 : Euc d) (4 / 3)) :
    ∃ v : Euc d → ℝ, ContDiff ℝ ∞ v ∧ ∀ x ∈ tsupport θ, v =ᶠ[𝓝 x] w := by
  obtain ⟨r, hr, hsr⟩ := exists_lt_subset_ball (isClosed_tsupport θ) hs
  have hρ : max r 0 < 4 / 3 := max_lt hr (by norm_num)
  have hρ0 : 0 ≤ max r 0 := le_max_right _ _
  have hrρ : r ≤ max r 0 := le_max_left _ _
  have hin : 0 < ((max r 0 + 4 / 3) / 2 : ℝ) := by linarith
  have hio : ((max r 0 + 4 / 3) / 2 : ℝ) < ((max r 0 + 4 / 3) / 2 + 4 / 3) / 2 := by linarith
  let b : ContDiffBump (0 : Euc d) := ⟨_, _, hin, hio⟩
  have hbs : tsupport (b : Euc d → ℝ) ⊆ ball (0 : Euc d) (4 / 3) := by
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by change ((max r 0 + 4 / 3) / 2 + 4 / 3) / 2 < 4 / 3; linarith)
  refine ⟨fun x => b x * w x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : Euc d) (4 / 3)
    · exact b.contDiff.contDiffAt.mul (hw.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hxb : x ∉ tsupport (b : Euc d → ℝ) := fun h => hx (hbs h)
      have hev : (fun x => b x * w x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxb] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    have hxb : x ∈ ball (0 : Euc d) ((max r 0 + 4 / 3) / 2) :=
      ball_subset_ball (by linarith) (hsr hx)
    filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
    simp [b.one_of_mem_closedBall (ball_subset_closedBall hy)]

private theorem young_aux {T W f P G M : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hG : 0 ≤ G)
    (hP : P ^ 2 ≤ M ^ 2 * G) :
    -(T ^ 2 * W * f) - 2 * (T * W * P) ≤
      1 / 2 * f ^ 2 + (1 / 2 + 2 * M ^ 2) * W ^ 2 + 1 / 2 * (T ^ 2 * G) := by
  have hT2 : T ^ 2 ≤ 1 := by nlinarith
  have h1 : -(T ^ 2 * W * f) ≤ 1 / 2 * f ^ 2 + 1 / 2 * W ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg T) (sq_nonneg (W + f)),
      mul_nonneg (sub_nonneg.2 hT2) (add_nonneg (sq_nonneg W) (sq_nonneg f))]
  have hpq : 0 ≤ 1 / 2 * (T ^ 2 * G) + 2 * M ^ 2 * W ^ 2 := by positivity
  have h2 : |2 * (T * W * P)| ≤ 1 / 2 * (T ^ 2 * G) + 2 * M ^ 2 * W ^ 2 := by
    refine abs_le_of_sq_le_sq ?_ hpq
    nlinarith [sq_nonneg (1 / 2 * (T ^ 2 * G) - 2 * M ^ 2 * W ^ 2),
      mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 4 * T ^ 2 * W ^ 2)]
  have h3 := (abs_le.1 h2).1
  nlinarith

/-- The energy inequality for a cutoff (the statement `EnergyIneqStmt`). -/
theorem L12a_energy_ineq (d : ℕ) : EnergyIneqStmt d := by
  intro w θ hw hθ hc hsθ h01 M hM hΔ hW
  obtain ⟨v, hv, hvw⟩ := exists_smooth_localization hw hsθ
  have hθ0 : ∀ x, x ∉ tsupport θ → θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hθB : ∀ x, x ∉ ball (0 : Euc d) (4 / 3) → θ x = 0 := fun x hx =>
    hθ0 x fun h => hx (hsθ h)
  have hloc : ∀ x ∈ tsupport θ, v x = w x ∧ fderiv ℝ v x = fderiv ℝ w x ∧ Δ v x = Δ w x := by
    intro x hx
    have h := hvw x hx
    exact ⟨h.eq_of_nhds, h.fderiv_eq, (InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds⟩
  have hDv : ∀ i, Continuous fun x => fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i) := fun i =>
    ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hDθ : ∀ i, Continuous fun x => fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) := fun i =>
    ((hθ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hsupp : ∀ f : Euc d → ℝ, (∀ x, θ x = 0 → f x = 0) → HasCompactSupport f := fun f hf =>
    HasCompactSupport.intro hc fun x hx => hf x (hθ0 x hx)
  -- the integrands of the cutoff identity for `v`
  have hgi : Integrable fun x =>
      θ x ^ 2 * ∑ i, (fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2 :=
    ((hθ.continuous.pow 2).mul (continuous_finsetSum _ fun i _ =>
      (hDv i).pow 2)).integrable_of_hasCompactSupport (hsupp _ fun x hx => by simp [hx])
  have hai : Integrable fun x => θ x ^ 2 * v x * Δ v x :=
    (((hθ.continuous.pow 2).mul hv.continuous).mul
      (continuous_laplacian_of_contDiff hv)).integrable_of_hasCompactSupport
      (hsupp _ fun x hx => by simp [hx])
  have hci : Integrable fun x => θ x * v x * ∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i) :=
    ((hθ.continuous.mul hv.continuous).mul (continuous_finsetSum _ fun i _ =>
      (hDθ i).mul (hDv i))).integrable_of_hasCompactSupport (hsupp _ fun x hx => by simp [hx])
  have hid := LatticeProb.PegdenSmart.integral_cutoff_sq_grad_sq (w := v) (θ := θ) hv hθ hc
  -- the same functions with `v` replaced by `w`
  have hg : ∀ x, θ x ^ 2 * ∑ i, (fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2 =
      θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ tsupport θ
    · rw [(hloc x hx).2.1, ← norm_sq_eq_sum_sq]
    · simp [hθ0 x hx]
  have hΦ : Integrable fun x => θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := by
    have : (fun x => θ x ^ 2 * ∑ i, (fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2) =
        fun x => θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := funext hg
    rw [← this]
    exact hgi
  have hpt : ∀ x ∈ ball (0 : Euc d) (4 / 3),
      -(θ x ^ 2 * v x * Δ v x) - 2 * (θ x * v x *
        ∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) ≤
      1 / 2 * Δ w x ^ 2 + (1 / 2 + 2 * M ^ 2) * w x ^ 2 +
        1 / 2 * (θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2) := by
    intro x _
    by_cases hx : x ∈ tsupport θ
    · obtain ⟨h1, h2, h3⟩ := hloc x hx
      rw [h1, h2, h3]
      have hP : (∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2 ≤ M ^ 2 * ‖fderiv ℝ w x‖ ^ 2 :=
        calc _ ≤ (∑ i, (fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2) *
              ∑ i, (fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = ‖fderiv ℝ θ x‖ ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := by
            rw [← norm_sq_eq_sum_sq, ← norm_sq_eq_sum_sq]
          _ ≤ M ^ 2 * ‖fderiv ℝ w x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM x) 2) (sq_nonneg _)
      exact young_aux (h01 x).1 (h01 x).2 (sq_nonneg _) hP
    · have hz := hθ0 x hx
      rw [hz]
      have : 0 ≤ 1 / 2 * Δ w x ^ 2 + (1 / 2 + 2 * M ^ 2) * w x ^ 2 +
          1 / 2 * ((0 : ℝ) ^ 2 * ‖fderiv ℝ w x‖ ^ 2) := by positivity
      linarith
  have hhi : Integrable fun x => -(θ x ^ 2 * v x * Δ v x) - 2 * (θ x * v x *
      ∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
        fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) := hai.neg.sub (hci.const_mul 2)
  have hI : (∫ x, θ x ^ 2 * ∑ i, (fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2) =
      ∫ x in ball (0 : Euc d) (4 / 3), (-(θ x ^ 2 * v x * Δ v x) - 2 * (θ x * v x *
        ∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i))) := by
    have han : Integrable fun x => -(θ x ^ 2 * v x * Δ v x) := hai.neg
    have hcn : Integrable fun x => 2 * (θ x * v x *
        ∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) := hci.const_mul 2
    rw [hid, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_sub han hcn, integral_neg,
      integral_const_mul]
    intro x hx
    simp [hθB x hx]
  have hA : (∫ x in ball (0 : Euc d) (4 / 3), θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2) =
      ∫ x, θ x ^ 2 * ∑ i, (fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)) ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Euc d) (4 / 3))
      (f := fun x => θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2) (fun x hx => by simp [hθB x hx])]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hg x).symm)
  have hi1 : IntegrableOn (fun x => 1 / 2 * Δ w x ^ 2) (ball (0 : Euc d) (4 / 3)) :=
    hΔ.const_mul _
  have hi2 : IntegrableOn (fun x => (1 / 2 + 2 * M ^ 2) * w x ^ 2) (ball (0 : Euc d) (4 / 3)) :=
    hW.const_mul _
  have hi3 : IntegrableOn (fun x => 1 / 2 * (θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2))
      (ball (0 : Euc d) (4 / 3)) := hΦ.integrableOn.const_mul _
  have hi12 : IntegrableOn (fun x => 1 / 2 * Δ w x ^ 2 + (1 / 2 + 2 * M ^ 2) * w x ^ 2)
      (ball (0 : Euc d) (4 / 3)) := hi1.add hi2
  have hmono : (∫ x in ball (0 : Euc d) (4 / 3), (-(θ x ^ 2 * v x * Δ v x) - 2 * (θ x * v x *
        ∑ i, fderiv ℝ θ x (stdOrthonormalBasis ℝ (Euc d) i) *
          fderiv ℝ v x (stdOrthonormalBasis ℝ (Euc d) i)))) ≤
      ∫ x in ball (0 : Euc d) (4 / 3), (1 / 2 * Δ w x ^ 2 + (1 / 2 + 2 * M ^ 2) * w x ^ 2 +
        1 / 2 * (θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2)) :=
    setIntegral_mono_on hhi.integrableOn (hi12.add hi3) measurableSet_ball hpt
  rw [integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_const_mul] at hmono
  linarith

end HessianAdapter
