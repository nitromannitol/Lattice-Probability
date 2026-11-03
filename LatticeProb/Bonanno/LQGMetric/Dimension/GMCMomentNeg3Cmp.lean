/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg3Cmp at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Fam

/-!
# Negative moments on a small square: Kahane comparison (P2-NEGMOM2, step 2)

`Neg3.exists_uniform_neg_moment_nM`: for `0 < γ < 2` and `p < 0`, `E nM_{k,j}(v)^p ≤ C` for all
`k ≤ j` and all offsets `v` keeping the shifted centres in `[0,1]²`.

The q < 0 version of `integral_oM_rpow_le` (GMCMomentPos2Cmp.lean): Berestycki–Powell
arXiv:2404.16642, `GMCproperties.tex` l. 1211–1218 (Kahane's inequality with an added independent
Gaussian), with the lower variance bound for the normalisation (since `x ↦ x^p` decreases).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

namespace Neg3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **Kahane comparison for `p ≤ 0`** -/
theorem integral_nM_rpow_le (hX : IsZeroBoundaryGFFOn openSquare X P) {γ cK c : ℝ}
    {K : Set ℂ} (hKU : K ⊆ openSquare) (hcK : 0 ≤ cK)
    (hK : ∀ {z w : ℂ} {r : ℝ}, 0 < r → closedBall z r ⊆ K → closedBall w r ⊆ K →
      |cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w r); P] +
        Real.log (max r ‖z - w‖)| ≤ cK)
    {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K)
    (hc : LogCorr (bZ γ X z₀ m) P (γ ^ 2) c) {p : ℝ} (hp : p ≤ 0) (k j : ℕ) {v : ℂ}
    (hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq) :
    ∫ ω, nM γ X z₀ m k j v ω ^ p ∂P ≤
      Real.exp (-(γ ^ 2 * cK / 2)) ^ p *
        (Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK) / 2) *
          ∫ ω, gM (bZ γ X z₀ m k) P j (grid j) ω ^ p ∂P) := by
  have hP := hc.isProb
  set r := radius (m + k)
  have hr : 0 < r := radius_pos _
  have hne : Nonempty ↥(grid j) := (grid_nonempty j).to_subtype
  set pX : ↥(grid j) → ℂ := fun i => z₀ + radius m • (cpt j i + v)
  have hBX : ∀ i : ↥(grid j), closedBall (pX i) r ⊆ K := fun i =>
    closedBall_sub_of_hQ hQ (hv i i.2) k
  have hBY : ∀ i : ↥(grid j), closedBall (z₀ + radius m • clampC (cpt j i)) r ⊆ K := fun i =>
    closedBall_sub_of_hQ hQ (clampC_mem _) k
  have hproc : IsGaussianProcess (fun (i : ↥(grid j)) (ω : Ω) =>
      γ • X ω (foldedCircle (pX i) r)) P :=
    (hX.gaussian.comp_right fun i : ↥(grid j) => admC hr ((hBX i).trans hKU)).smul fun _ => γ
  have hXv : HasGaussianLaw (fun ω (i : ↥(grid j)) => γ * X ω (foldedCircle (pX i) r)) P :=
    hasGaussianLaw_fintype hproc id
  have hYv : HasGaussianLaw (fun ω (i : ↥(grid j)) => bZ γ X z₀ m k (cpt j i) ω) P :=
    hasGaussianLaw_fintype (hc.gauss k) (fun i : ↥(grid j) => cpt j i)
  have hXm : ∀ i : ↥(grid j), ∫ ω, γ * X ω (foldedCircle (pX i) r) ∂P = 0 := fun i => by
    rw [integral_const_mul, integral_circle hX hr ((hBX i).trans hKU), mul_zero]
  have hcov : ∀ a b : ↥(grid j),
      cov[fun ω => γ * X ω (foldedCircle (pX a) r), fun ω => γ * X ω (foldedCircle (pX b) r); P] ≤
      cov[fun ω => bZ γ X z₀ m k (cpt j a) ω, fun ω => bZ γ X z₀ m k (cpt j b) ω; P] +
        ((⟨2 * γ ^ 2 * cK, by positivity⟩ : ℝ≥0) : ℝ) := by
    intro a b
    show _ ≤ _ + 2 * γ ^ 2 * cK
    have e : cov[fun ω => bZ γ X z₀ m k (cpt j a) ω, fun ω => bZ γ X z₀ m k (cpt j b) ω; P] =
        cov[fun ω => γ * X ω (foldedCircle (z₀ + radius m • clampC (cpt j a)) r),
          fun ω => γ * X ω (foldedCircle (z₀ + radius m • clampC (cpt j b)) r); P] := rfl
    rw [e, covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_left,
      covariance_const_mul_right]
    have h1 := abs_le.1 (hK hr (hBX a) (hBX b))
    have h2 := abs_le.1 (hK hr (hBY a) (hBY b))
    have hd : ‖pX a - pX b‖ = ‖(z₀ + radius m • clampC (cpt j a)) -
        (z₀ + radius m • clampC (cpt j b))‖ := by
      rw [clampC_eq (cpt_mem_unitSq a.2), clampC_eq (cpt_mem_unitSq b.2)]
      simp only [pX]
      rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, ← smul_sub, ← smul_sub,
        add_sub_add_right_eq_sub]
    rw [hd] at h1
    set C1 := cov[fun ω => X ω (foldedCircle (pX a) r), fun ω => X ω (foldedCircle (pX b) r); P]
    set C2 := cov[fun ω => X ω (foldedCircle (z₀ + radius m • clampC (cpt j a)) r),
      fun ω => X ω (foldedCircle (z₀ + radius m • clampC (cpt j b)) r); P]
    have := mul_le_mul_of_nonneg_left (show C1 - C2 - 2 * cK ≤ 0 by linarith [h1.2, h2.1])
      (sq_nonneg γ)
    nlinarith
  have hKa := Kahane.kahane_rpow_le_add_const (Or.inl hp) (p := fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j)
    (fun _ => by positivity) hXv hYv hXm (fun i => hc.mean k _) _ hcov
  -- the variance lower bound
  have hvar : ∀ i : ↥(grid j), γ ^ 2 * (-Real.log r - cK) ≤
      Var[fun ω => γ * X ω (foldedCircle (pX i) r); P] := fun i => by
    have hm : AEMeasurable (fun ω => γ * X ω (foldedCircle (pX i) r)) P :=
      ((hX.measurable_coord _).const_mul γ).aemeasurable
    rw [← covariance_self hm, covariance_const_mul_left, covariance_const_mul_right]
    have h := abs_le.1 (hK hr (hBX i) (hBX i))
    rw [sub_self, norm_zero, max_eq_left hr.le] at h
    set C := cov[fun ω => X ω (foldedCircle (pX i) r), fun ω => X ω (foldedCircle (pX i) r); P]
    have := mul_le_mul_of_nonneg_left (show -Real.log r - cK ≤ C by linarith [h.1]) (sq_nonneg γ)
    nlinarith
  set A := Real.exp (-(γ ^ 2 * cK / 2))
  set SX : Ω → ℝ := fun ω => ∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j *
    Real.exp (γ * X ω (foldedCircle (pX i) r) -
      Var[fun ω => γ * X ω (foldedCircle (pX i) r); P] / 2)
  have hSX : ∀ ω, 0 < SX ω := fun ω =>
    Finset.sum_pos (fun _ _ => by positivity) Finset.univ_nonempty
  have hpt : ∀ ω, A * SX ω ≤ nM γ X z₀ m k j v ω := fun ω => by
    rw [nM, ← Finset.sum_coe_sort (grid j), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 : (4 : ℝ)⁻¹ ^ j * (r ^ (γ ^ 2 / 2) * Real.exp (γ * X ω (foldedCircle (pX i) r))) =
        (4 : ℝ)⁻¹ ^ j * Real.exp (Real.log r * (γ ^ 2 / 2) + γ * X ω (foldedCircle (pX i) r)) := by
      rw [Real.rpow_def_of_pos hr, Real.exp_add]
    have e2 : A * ((4 : ℝ)⁻¹ ^ j * Real.exp (γ * X ω (foldedCircle (pX i) r) -
        Var[fun ω => γ * X ω (foldedCircle (pX i) r); P] / 2)) =
        (4 : ℝ)⁻¹ ^ j * Real.exp (-(γ ^ 2 * cK / 2) + (γ * X ω (foldedCircle (pX i) r) -
        Var[fun ω => γ * X ω (foldedCircle (pX i) r); P] / 2)) := by
      rw [Real.exp_add]; ring
    show A * ((4 : ℝ)⁻¹ ^ j * Real.exp (γ * X ω (foldedCircle (pX i) r) -
        Var[fun ω => γ * X ω (foldedCircle (pX i) r); P] / 2)) ≤
      (4 : ℝ)⁻¹ ^ j * (r ^ (γ ^ 2 / 2) * Real.exp (γ * X ω (foldedCircle (pX i) r)))
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := hvar i
    nlinarith
  have hnM : ∀ ω, 0 ≤ nM γ X z₀ m k j v ω := fun ω => Finset.sum_nonneg fun _ _ => by positivity
  -- integrability of `SX^p`
  have hint1 : Integrable (fun ω => SX ω ^ p) P := by
    obtain ⟨i₀⟩ := hne
    have hmeas : Measurable SX :=
      Finset.measurable_sum _ fun i _ =>
        ((((hX.measurable_coord _).const_mul γ).sub_const _).exp).const_mul _
    have hg : HasGaussianLaw (fun ω => γ * X ω (foldedCircle (pX i₀) r)) P :=
      hproc.hasGaussianLaw_eval i₀
    obtain ⟨hi, -⟩ := integral_exp_mul_of_hasGaussianLaw hg (hXm i₀) p
    set V := Var[fun ω => γ * X ω (foldedCircle (pX i₀) r); P]
    refine Integrable.mono' (hi.const_mul (((4 : ℝ)⁻¹ ^ j) ^ p * Real.exp (-(p * V / 2))))
      (hmeas.pow_const p).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hSX ω).le _)]
    have hle : (4 : ℝ)⁻¹ ^ j * Real.exp (γ * X ω (foldedCircle (pX i₀) r) - V / 2) ≤ SX ω :=
      Finset.single_le_sum (f := fun i : ↥(grid j) => (4 : ℝ)⁻¹ ^ j *
        Real.exp (γ * X ω (foldedCircle (pX i) r) -
          Var[fun ω => γ * X ω (foldedCircle (pX i) r); P] / 2))
        (fun _ _ => by positivity) (Finset.mem_univ i₀)
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hle hp).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add]
    congr 2; ring
  have hY : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => bZ γ X z₀ m k (cpt j i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => bZ γ X z₀ m k (cpt j i) ω) ω i; P] / 2)) ^ p) =
      fun ω => gM (bZ γ X z₀ m k) P j (grid j) ω ^ p := by
    funext ω
    rw [gM, ← Finset.sum_coe_sort (grid j)]
  rw [hY] at hKa
  calc ∫ ω, nM γ X z₀ m k j v ω ^ p ∂P
      ≤ ∫ ω, A ^ p * SX ω ^ p ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω =>
          Real.rpow_nonneg (hnM ω) _) (hint1.const_mul _) (Eventually.of_forall fun ω => ?_)
        beta_reduce
        rw [← Real.mul_rpow (Real.exp_pos _).le (hSX ω).le]
        exact Real.rpow_le_rpow_of_nonpos (mul_pos (Real.exp_pos _) (hSX ω)) (hpt ω) hp
    _ = A ^ p * ∫ ω, SX ω ^ p ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hKa (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- **uniform negative moments of the Riemann sums on the square** -/
theorem exists_uniform_neg_moment_nM (hX : IsZeroBoundaryGFFOn openSquare X P) {γ p : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0) {K : Set ℂ} (hKU : K ⊆ openSquare)
    (hKc : Convex ℝ K) (hKk : IsCompact K) {z₀ : ℂ} {m : ℕ}
    (hQ : ∀ w ∈ unitSq, closedBall (z₀ + radius m • w) (2 * radius m) ⊆ K) :
    ∃ C : ℝ, ∀ (k j : ℕ) (v : ℂ), k ≤ j → (∀ i ∈ grid j, cpt j i + v ∈ unitSq) →
      ∫ ω, nM γ X z₀ m k j v ω ^ p ∂P ≤ C := by
  obtain ⟨cK, hcK⟩ := circleCov_two_sided hKU hKc hKk
  obtain ⟨c, hc⟩ := logCorr_bZ hX γ hKU hKc hKk hQ
  have hβ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨C₀, hC₀⟩ := hc.exists_uniform_neg_moment (by positivity) hβ4 hp
  set cK' := max cK 0
  have hK' : ∀ {z w : ℂ} {r : ℝ}, 0 < r → closedBall z r ⊆ K → closedBall w r ⊆ K →
      |cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w r); P] +
        Real.log (max r ‖z - w‖)| ≤ cK' := fun hr h1 h2 =>
    (hcK hX hr h1 h2).trans (le_max_left _ _)
  refine ⟨Real.exp (-(γ ^ 2 * cK' / 2)) ^ p *
    (Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK') / 2) * C₀), fun k j v hkj hv => ?_⟩
  refine (integral_nM_rpow_le hX hKU (le_max_right _ _) hK' hQ hc hp.le k j hv).trans ?_
  gcongr
  exact hC₀ k j hkj

end Neg3

end DGMC

end LQGMetric
