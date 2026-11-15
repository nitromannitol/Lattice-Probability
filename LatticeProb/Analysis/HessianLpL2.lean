import LatticeProb.Analysis.HessianLpReduction

/-! # Cutoffs for interior Hessian estimates

Smooth cutoffs and an absorption estimate used in local Hessian bounds.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace HessianAdapter

/-- A smooth cutoff equal to one on an inner ball, supported in a larger ball,
with uniformly bounded derivative. -/
theorem exists_smooth_cutoff (d : ℕ) {r R S : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRS : R < S) :
    ∃ (θ : Euc d → ℝ) (M : ℝ), ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ ball (0 : Euc d) S ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      (∀ x ∈ ball (0 : Euc d) r, θ x = 1) ∧ ∀ x, ‖fderiv ℝ θ x‖ ≤ M := by
  let b : ContDiffBump (0 : Euc d) := ⟨r, R, hr, hrR⟩
  have hb : HasCompactSupport (b : Euc d → ℝ) := b.hasCompactSupport
  obtain ⟨M, _, hM⟩ := hb.exists_bound_iteratedFDeriv b.contDiff 1
  refine ⟨b, M, b.contDiff, hb, ?_, ?_, ?_, ?_⟩
  · rw [b.tsupport_eq]
    exact closedBall_subset_ball hRS
  · exact fun x => ⟨b.nonneg, b.le_one⟩
  · intro x hx
    exact b.one_of_mem_closedBall (ball_subset_closedBall hx)
  · intro x
    simpa only [norm_iteratedFDeriv_one] using hM 1 (by norm_num) x

/-- Nested cutoffs for the balls of radii `1`, `7/6`, `5/4`, and `4/3`. -/
theorem exists_nested_hessian_cutoffs (d : ℕ) :
    ∃ (η θ : Euc d → ℝ) (M N : ℝ),
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ ball (0 : Euc d) (7 / 6) ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x ∈ ball (0 : Euc d) 1, η x = 1) ∧ (∀ x, ‖fderiv ℝ η x‖ ≤ M) ∧
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ ball (0 : Euc d) (4 / 3) ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      (∀ x ∈ ball (0 : Euc d) (7 / 6), θ x = 1) ∧ ∀ x, ‖fderiv ℝ θ x‖ ≤ N := by
  obtain ⟨η, M, hη, hcη, hsη, hvη, hoη, hdη⟩ :=
    exists_smooth_cutoff d (r := 1) (R := 13 / 12) (S := 7 / 6)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨θ, N, hθ, hcθ, hsθ, hvθ, hoθ, hdθ⟩ :=
    exists_smooth_cutoff d (r := 7 / 6) (R := 5 / 4) (S := 4 / 3)
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨η, θ, M, N, hη, hcη, hsη, hvη, hoη, hdη,
    hθ, hcθ, hsθ, hvθ, hoθ, hdθ⟩

/-- Finite `L²` data on a ball have integrable squares. -/
theorem integrable_sq_data (d : ℕ) (w : Euc d → ℝ)
    (hfinite : eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) +
      eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤) :
    IntegrableOn (fun x => Δ w x ^ 2) (ball (0 : Euc d) (4 / 3)) ∧
      IntegrableOn (fun x => w x ^ 2) (ball (0 : Euc d) (4 / 3)) := by
  have hleft : eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hfinite).1
  have hright : eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hfinite).2
  exact ⟨(show MemLp (Δ w) 2 _ from hleft.lt_top).integrable_sq,
    (show MemLp w 2 _ from hright.lt_top).integrable_sq⟩

/-- The energy hypothesis gives a single cutoff and a uniform gradient bound. -/
theorem exists_gradient_energy_cutoff (d : ℕ) (h1 : EnergyIneqStmt d) :
    ∃ (θ : Euc d → ℝ) (N : ℝ),
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ ball (0 : Euc d) (4 / 3) ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      (∀ x ∈ ball (0 : Euc d) (7 / 6), θ x = 1) ∧ (∀ x, ‖fderiv ℝ θ x‖ ≤ N) ∧
      ∀ w : Euc d → ℝ, ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)) →
      eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) +
        eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤ →
      (∫ x in ball (0 : Euc d) (4 / 3), θ x ^ 2 * ‖fderiv ℝ w x‖ ^ 2) ≤
        (∫ x in ball (0 : Euc d) (4 / 3), Δ w x ^ 2) +
          (1 + 4 * N ^ 2) * ∫ x in ball (0 : Euc d) (4 / 3), w x ^ 2 := by
  obtain ⟨θ, N, hθ, hcθ, hsθ, hvθ, hoθ, hdθ⟩ :=
    exists_smooth_cutoff d (r := 7 / 6) (R := 5 / 4) (S := 4 / 3)
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨θ, N, hθ, hcθ, hsθ, hvθ, hoθ, hdθ, ?_⟩
  intro w hw hf
  obtain ⟨hΔ, hw2⟩ := integrable_sq_data d w hf
  exact h1 w θ hw hθ hcθ hsθ hvθ N hdθ hΔ hw2

/-- Absorb two Cauchy–Schwarz cross terms into an energy estimate. -/
theorem hessian_energy_absorption {I F G a b : ℝ} (hI : 0 ≤ I) (hF : 0 ≤ F)
    (hG : 0 ≤ G) (ha : a ^ 2 ≤ F * G) (hb : b ^ 2 ≤ I * G)
    (h : I ≤ F + 2 * a + 2 * b) : I ≤ 4 * F + 6 * G := by
  have ha' : 2 * a ≤ F + G := by nlinarith [sq_nonneg (F - G), sq_nonneg (a - 1)]
  have hb' : 2 * b ≤ I / 2 + 2 * G := by nlinarith [sq_nonneg (I / 2 - 2 * G), sq_nonneg (b - 1)]
  linarith

/-- Substitute the gradient energy estimate into the Hessian energy estimate. -/
theorem hessian_energy_of_gradient_bound {I F G W M N : ℝ}
    (hG : G ≤ M ^ 2 * (F + (1 + 4 * N ^ 2) * W))
    (hI : I ≤ 4 * F + 6 * G) :
    I ≤ (4 + 6 * M ^ 2) * F + 6 * M ^ 2 * (1 + 4 * N ^ 2) * W := by
  nlinarith

/-- Cauchy–Schwarz for the contraction of a matrix against two vectors. -/
theorem matrix_contraction_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (c : κ → ℝ) (B : ι → κ → ℝ) :
    (∑ i, a i * ∑ j, B i j * c j) ^ 2 ≤
      (∑ i, a i ^ 2) * (∑ i, ∑ j, B i j ^ 2) * (∑ j, c j ^ 2) := by
  classical
  have hrow (i : ι) : (∑ j, B i j * c j) ^ 2 ≤
      (∑ j, B i j ^ 2) * (∑ j, c j ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (B i) c
  have hsum : (∑ i, (∑ j, B i j * c j) ^ 2) ≤
      (∑ i, ∑ j, B i j ^ 2) * (∑ j, c j ^ 2) := by
    calc
      _ ≤ ∑ i, (∑ j, B i j ^ 2) * (∑ j, c j ^ 2) :=
        Finset.sum_le_sum fun i hi => hrow i
      _ = _ := by rw [Finset.sum_mul]
  have ha : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  calc
    _ ≤ (∑ i, a i ^ 2) * (∑ i, (∑ j, B i j * c j) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a _
    _ ≤ (∑ i, a i ^ 2) * ((∑ i, ∑ j, B i j ^ 2) * (∑ j, c j ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum ha
    _ = _ := by ring

/-- Pointwise Young estimates for the two cross terms in the Hessian identity. -/
theorem hessian_cross_terms_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (c : κ → ℝ) (B : ι → κ → ℝ) (η f : ℝ)
    (v : ι → ℝ) (hv : (∑ i, a i * v i) ^ 2 ≤
      (∑ i, a i ^ 2) * (∑ j, c j ^ 2)) :
    2 * η * f * (∑ i, a i * v i) -
      2 * η * (∑ i, a i * ∑ j, B i j * c j) ≤
    η ^ 2 * f ^ 2 + η ^ 2 * (∑ i, ∑ j, B i j ^ 2) / 2 +
      3 * ((∑ i, a i ^ 2) * (∑ j, c j ^ 2)) := by
  classical
  let A := ∑ i, a i ^ 2
  let C := ∑ j, c j ^ 2
  let H := ∑ i, ∑ j, B i j ^ 2
  let X := ∑ i, a i * v i
  let Y := ∑ i, a i * ∑ j, B i j * c j
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : Y ^ 2 ≤ A * H * C := matrix_contraction_sq_le a c B
  have hX : X ^ 2 ≤ A * C := hv
  have hf : (η * f * X) ^ 2 ≤ (η ^ 2 * f ^ 2) * (A * C) := by
    nlinarith [mul_nonneg (sq_nonneg (η * f)) (sub_nonneg.mpr hX)]
  have hg : (-η * Y) ^ 2 ≤ (η ^ 2 * H) * (A * C) := by
    nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hY)]
  have hF : 0 ≤ η ^ 2 * f ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hI : 0 ≤ η ^ 2 * H := mul_nonneg (sq_nonneg _) hH
  have hG : 0 ≤ A * C := mul_nonneg hA hC
  have hfirst : 2 * (η * f * X) ≤ η ^ 2 * f ^ 2 + A * C := by
    nlinarith [sq_nonneg (η ^ 2 * f ^ 2 - A * C)]
  have hsecond : 2 * (-η * Y) ≤ (η ^ 2 * H) / 2 + 2 * (A * C) := by
    nlinarith [sq_nonneg ((η ^ 2 * H) / 2 - 2 * (A * C))]
  dsimp only [A, C, H, X, Y] at hfirst hsecond
  linarith

/-- The cross terms of the Hessian identity are controlled by the Hessian and gradient energies. -/
theorem hessian_cross_terms_bound (d : ℕ) (D W : Euc d →L[ℝ] ℝ)
    (B : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) (η f : ℝ) :
    2 * η * f * (∑ i, D (stdOrthonormalBasis ℝ (Euc d) i) *
      W (stdOrthonormalBasis ℝ (Euc d) i)) -
    2 * η * (∑ i, ∑ j, D (stdOrthonormalBasis ℝ (Euc d) i) *
      B (stdOrthonormalBasis ℝ (Euc d) i) (stdOrthonormalBasis ℝ (Euc d) j) *
      W (stdOrthonormalBasis ℝ (Euc d) j)) ≤
    η ^ 2 * f ^ 2 + η ^ 2 * (∑ i, ∑ j,
      B (stdOrthonormalBasis ℝ (Euc d) i) (stdOrthonormalBasis ℝ (Euc d) j) ^ 2) / 2 +
      3 * (‖D‖ ^ 2 * ‖W‖ ^ 2) := by
  classical
  let b := stdOrthonormalBasis ℝ (Euc d)
  have hv : (∑ i, D (b i) * W (b i)) ^ 2 ≤
      (∑ i, D (b i) ^ 2) * (∑ i, W (b i) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => D (b i)) (fun i => W (b i))
  have h := hessian_cross_terms_le (fun i => D (b i)) (fun i => W (b i))
    (fun i j => B (b i) (b j)) η f (fun i => W (b i)) hv
  rw [← b.norm_dual D, ← b.norm_dual W] at h
  simpa only [b, Finset.mul_sum, mul_assoc] using h

/-- The operator norm of a bilinear form is bounded by its squared matrix entries. -/
theorem bilinear_norm_sq_le_sum (d : ℕ)
    (B : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) :
    ‖B‖ ^ 2 ≤ ∑ i, ∑ j, (B (stdOrthonormalBasis ℝ (Euc d) i)
      (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ (Euc d)
  let S : ℝ := ∑ i, ‖B (b i)‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hbound : ‖B‖ ≤ Real.sqrt S := by
    apply B.opNorm_le_bound (Real.sqrt_nonneg S)
    intro x
    have hre : ∑ i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq, b.repr.norm_map]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => ‖b.repr x i‖) (fun i => ‖B (b i)‖)
    have hsum : ‖B x‖ ≤ ∑ i, ‖b.repr x i‖ * ‖B (b i)‖ := by
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, map_smul]
      simpa only [norm_smul] using
        (norm_sum_le Finset.univ (fun i => b.repr x i • B (b i)))
    calc
      ‖B x‖ ≤ ∑ i, ‖b.repr x i‖ * ‖B (b i)‖ := hsum
      _ ≤ Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) * Real.sqrt S := hcs
      _ = Real.sqrt S * ‖x‖ := by rw [hre, Real.sqrt_sq (norm_nonneg _)]; ring
  have hsq : ‖B‖ ^ 2 ≤ S := by
    nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg S, norm_nonneg B]
  refine hsq.trans_eq ?_
  dsimp only [S, b]
  apply Finset.sum_congr rfl
  intro i hi
  exact (stdOrthonormalBasis ℝ (Euc d)).norm_dual (B _)

/-- Integrating the cross-term bound yields the cutoff Hessian energy estimate. -/
theorem hessian_energy_bound_of_integrable (d : ℕ) (h2 : HessianEnergyStmt d)
    (w η : Euc d → ℝ) (hw : ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)))
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ball (0 : Euc d) (4 / 3))
    (hI : Integrable (fun x => η x ^ 2 * ∑ i, ∑ j,
      (fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2))
    (hF : Integrable (fun x => η x ^ 2 * Δ w x ^ 2))
    (hA : Integrable (fun x => η x * Δ w x * ∑ i,
      fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)))
    (hB : Integrable (fun x => η x * ∑ i, ∑ j,
      fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j) *
      fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) j)))
    (hG : Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2 * ‖fderiv ℝ w x‖ ^ 2)) :
    (∫ x, η x ^ 2 * ∑ i, ∑ j,
      (fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2) ≤
    4 * (∫ x, η x ^ 2 * Δ w x ^ 2) +
      6 * ∫ x, ‖fderiv ℝ η x‖ ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := by
  let I : Euc d → ℝ := fun x => η x ^ 2 * ∑ i, ∑ j,
    (fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
      (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2
  let F : Euc d → ℝ := fun x => η x ^ 2 * Δ w x ^ 2
  let A : Euc d → ℝ := fun x => η x * Δ w x * ∑ i,
    fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
    fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)
  let B : Euc d → ℝ := fun x => η x * ∑ i, ∑ j,
    fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
    fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
      (stdOrthonormalBasis ℝ (Euc d) j) *
    fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) j)
  let G : Euc d → ℝ := fun x => ‖fderiv ℝ η x‖ ^ 2 * ‖fderiv ℝ w x‖ ^ 2
  have he : (∫ x, I x) = (∫ x, F x) + 2 * (∫ x, A x) - 2 * ∫ x, B x :=
    h2 w η hw hη hc hs
  have hp (x : Euc d) : 2 * A x - 2 * B x ≤ F x + I x / 2 + 3 * G x := by
    have hh := hessian_cross_terms_bound d (fderiv ℝ η x) (fderiv ℝ w x)
      (fderiv ℝ (fderiv ℝ w) x) (η x) (Δ w x)
    dsimp [I, F, A, B, G]
    convert hh using 1; ring
  have hm := integral_mono ((hA.const_mul 2).sub (hB.const_mul 2))
    ((hF.add (hI.div_const 2)).add (hG.const_mul 3)) hp
  change (∫ x, 2 * A x - 2 * B x) ≤
    ∫ x, (F x + I x / 2) + 3 * G x at hm
  have hFi : Integrable (fun x => F x + I x / 2) := hF.add (hI.div_const 2)
  have hGc : Integrable (fun x => 3 * G x) := hG.const_mul 3
  have hId : Integrable (fun x => I x / 2) := hI.div_const 2
  rw [integral_sub (hA.const_mul 2) (hB.const_mul 2),
    integral_add hFi hGc, integral_add hF hId, integral_div] at hm
  simp only [integral_const_mul] at hm
  change (∫ x, I x) ≤ 4 * (∫ x, F x) + 6 * ∫ x, G x
  linarith

/-- The cutoff Hessian energy estimate for a locally smooth function. -/
theorem hessian_energy_bound (d : ℕ) (h2 : HessianEnergyStmt d)
    (w η : Euc d → ℝ) (hw : ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)))
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ball (0 : Euc d) (4 / 3)) :
    (∫ x, η x ^ 2 * ∑ i, ∑ j,
      (fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2) ≤
    4 * (∫ x, η x ^ 2 * Δ w x ^ 2) +
      6 * ∫ x, ‖fderiv ℝ η x‖ ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := by
  let U := ball (0 : Euc d) (4 / 3)
  have hlocal (g : Euc d → ℝ) (hg : ContinuousOn g U)
      (hz : ∀ x ∉ tsupport η, g x = 0) : Integrable g :=
    ((hg.mono hs).integrableOn_compact hc).integrable_of_forall_notMem_eq_zero hz
  have hη0 (x : Euc d) (hx : x ∉ tsupport η) : η x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hdη0 (x : Euc d) (hx : x ∉ tsupport η) : fderiv ℝ η x = 0 :=
    fderiv_of_notMem_tsupport ℝ hx
  have hW : ContinuousOn (fderiv ℝ w) U :=
    hw.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have hB : ContinuousOn (fderiv ℝ (fderiv ℝ w)) U :=
    (hw.fderiv_of_isOpen isOpen_ball (m := 1) (by simp)).continuousOn_fderiv_of_isOpen
      isOpen_ball (by simp)
  have hD : ContinuousOn (fderiv ℝ η) U := (hη.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  have hηc : ContinuousOn η U := hη.continuous.continuousOn
  have hΔ : ContinuousOn (Δ w) U := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only [iteratedFDeriv_two_apply]
    apply continuousOn_finsetSum
    intro i hi
    exact (hB.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hI : Integrable (fun x => η x ^ 2 * ∑ i, ∑ j,
      (fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2) := by
    apply hlocal
    · apply (hηc.pow 2).mul
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      exact ((hB.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2
    · intro x hx
      simp [hη0 x hx]
  have hF : Integrable (fun x => η x ^ 2 * Δ w x ^ 2) := by
    apply hlocal _ ((hηc.pow 2).mul (hΔ.pow 2))
    intro x hx
    simp [hη0 x hx]
  have hA : Integrable (fun x => η x * Δ w x * ∑ i,
      fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)) := by
    apply hlocal
    · apply (hηc.mul hΔ).mul
      apply continuousOn_finsetSum
      intro i hi
      exact (hD.clm_apply continuousOn_const).mul (hW.clm_apply continuousOn_const)
    · intro x hx
      simp [hη0 x hx]
  have hCross : Integrable (fun x => η x * ∑ i, ∑ j,
      fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j) *
      fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) j)) := by
    apply hlocal
    · apply hηc.mul
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      exact ((hD.clm_apply continuousOn_const).mul
        ((hB.clm_apply continuousOn_const).clm_apply continuousOn_const)).mul
        (hW.clm_apply continuousOn_const)
    · intro x hx
      simp [hη0 x hx]
  have hG : Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2 * ‖fderiv ℝ w x‖ ^ 2) := by
    apply hlocal _ ((hD.norm.pow 2).mul (hW.norm.pow 2))
    intro x hx
    simp [hdη0 x hx]
  exact hessian_energy_bound_of_integrable d h2 w η hw hη hc hs hI hF hA hCross hG

/-- It suffices to prove the interior estimate when the right-hand side is finite. -/
theorem l2HessEucStmt_of_finite_rhs (d : ℕ)
    (h : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : Euc d → ℝ,
      ContDiffOn ℝ ∞ w (ball (0 : Euc d) (4 / 3)) →
      eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) +
        eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤ →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) 2
          (volume.restrict (ball (0 : Euc d) 1)) ≤
        C * (eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) +
          eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))))) : L2HessEucStmt d := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C + 1, ENNReal.add_ne_top.mpr ⟨hC, by simp⟩, ?_⟩
  intro w hw
  by_cases hf : eLpNorm (Δ w) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) +
      eLpNorm w 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) = ⊤
  · rw [hf, ENNReal.mul_top (by simp)]
    exact le_top
  · refine (hbound w hw hf).trans ?_
    gcongr
    exact le_add_of_nonneg_right bot_le

/-- The interior estimate in the zero-dimensional model space. -/
theorem l2HessEucStmt_zero : L2HessEucStmt 0 := by
  refine ⟨0, by simp, ?_⟩
  intro w hw
  simp

end HessianAdapter
