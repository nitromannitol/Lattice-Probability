/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4M4 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 3.1, canonical nesting: the increment vectors and their orthogonality (P2-LM34c)

Source: MQ arXiv:1812.03913 `lqg_geodesics.tex`, proof of Prop 4.3 (l. 693–700). Notation of
`L3_4M3`. With `ρ = r_{j+1}/r_j` and `κ_j` the vector of `h_{r_{j+1}}(0) − h_{r_j}(0)`:
`[⟨Y_{j+1}, φ⟩] = ρ⁻² [⟨Y_j, φ(·/ρ)⟩] − (∫φ) κ_j` (`nPV_succ`), and the increments
`δ_0 = a_0`, `δ_{j+1} φ = ρ⁻² z_j(φ(·/ρ)) − z_{j+1} φ − (∫φ) P_{K_j} κ_j`.

* `nDelta_succ_mem` (`δ_{j+1} ∈ K_j`), `inner_nDelta` (`δ_i ⊥ K_i`),
  `inner_nDelta_nDelta` (`δ_{j+1} ⊥ δ_i`, `i ≤ j`), `inner_nDelta_compl` (`δ_j ⊥ pv_j − δ_j`);
* `indepFun_of_orth` (Janson Thm 1.7 for two families in the Gaussian space).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric.LM

open Blueprint QuantumZipper QuantumZipper.K3 MarkovZB MarkovExt MarkovGauss MarkovNorm

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **Two orthogonal families in the Gaussian space are independent** (Janson Thm 1.7). -/
theorem indepFun_of_orth (hh : IsWholePlaneGFF h P) {S₁ S₂ : Type*} (u : S₁ → Lp ℝ 2 P)
    (v : S₂ → Lp ℝ 2 P) (hu : ∀ s, u s ∈ gaussSpace (pairProc h) (memLp_pair hh))
    (hv : ∀ t, v t ∈ gaussSpace (pairProc h) (memLp_pair hh))
    (horth : ∀ s t, ⟪u s, v t⟫ = 0) :
    IndepFun (fun ω s => (u s : Ω → ℝ) ω) (fun ω t => (v t : Ω → ℝ) ω) P := by
  have hG := isGaussianProcess_of_mem_gaussSpace (gaussian_pairProc hh) (centered_pairProc hh)
    (memLp_pair hh) (Sum.elim u v) (fun x => by cases x with
      | inl s => exact hu s
      | inr t => exact hv t)
  have hG' : IsGaussianProcess (Sum.elim (fun s => (u s : Ω → ℝ)) fun t => (v t : Ω → ℝ)) P :=
    hG.congr fun x => by cases x with
      | inl s => exact Filter.EventuallyEq.rfl
      | inr t => exact Filter.EventuallyEq.rfl
  refine hG'.indepFun_of_covariance_eq_zero (fun s => (Lp.aestronglyMeasurable _).aemeasurable)
    (fun t => (Lp.aestronglyMeasurable _).aemeasurable) fun s t => ?_
  rw [covariance_eq_inner (u s) (Lp.memLp (v t))
    (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh) (centered_pairProc hh)
      (memLp_pair hh) (hu s)).2, Lp.toLp_coeFn, horth]

/-- a test function with integral `1` -/
def phiOne : TestC := (∫ y, GM.radProf 1 y)⁻¹ • GM.radBump 1 zero_le_one 0

lemma integral_phiOne : ∫ x, phiOne x = 1 := by
  have e : (phiOne : ℂ → ℝ) = fun x => (∫ y, GM.radProf 1 y)⁻¹ * GM.radBump 1 zero_le_one 0 x := by
    funext x; rfl
  rw [e, integral_const_mul, GM.integral_radBump,
    inv_mul_cancel₀ (GM.integral_radProf_pos one_pos).ne']

variable (hh : IsNormalizedWPGFF h P) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hA : Antitone r)
include hh hr

lemma nPV_ae (k : ℕ) (φ : TestC) :
    (nPV hh hr k φ : Ω → ℝ) =ᵐ[P] fun ω => lmScaled h (r k) ω φ :=
  pairVec_ae (nY hh hr k) φ

/-- `κ_j`, the vector of `h_{r_{j+1}}(0) − h_{r_j}(0)` -/
def nKappa (j : ℕ) : Lp ℝ 2 P :=
  ((r (j + 1) / r j) ^ 2)⁻¹ • nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 phiOne) -
    nPV hh hr (j + 1) phiOne

/-- `[⟨Y_{j+1}, φ⟩] = ρ⁻² [⟨Y_j, φ(·/ρ)⟩] − (∫φ) κ_j` -/
lemma nPV_succ (j : ℕ) (φ : TestC) :
    nPV hh hr (j + 1) φ = ((r (j + 1) / r j) ^ 2)⁻¹ •
      nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 φ) - (∫ x, φ x) • nKappa hh hr j := by
  have hc := ratio_pos hr j
  have e : r (j + 1) = r j * (r (j + 1) / r j) := by field_simp [(hr j).ne']
  have key : ∀ (ψ : TestC) (ω : Ω), lmScaled h (r (j + 1)) ω ψ =
      ((r (j + 1) / r j) ^ 2)⁻¹ * lmScaled h (r j) ω (testAffinePull (r (j + 1) / r j) 0 ψ) -
      (circleAvg (h ω) (r (j + 1)) 0 - circleAvg (h ω) (r j) 0) * ∫ x, ψ x := by
    intro ψ ω
    have := lmScaled_mul_apply h (hr j) hc ψ ω
    rw [← e] at this
    exact this
  refine Lp.ext ?_
  filter_upwards [nPV_ae hh hr (j + 1) φ, nPV_ae hh hr j
      (testAffinePull (r (j + 1) / r j) 0 φ), nPV_ae hh hr (j + 1) phiOne,
    nPV_ae hh hr j (testAffinePull (r (j + 1) / r j) 0 phiOne),
    Lp.coeFn_sub (((r (j + 1) / r j) ^ 2)⁻¹ •
      nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 φ)) ((∫ x, φ x) • nKappa hh hr j),
    Lp.coeFn_smul ((r (j + 1) / r j) ^ 2)⁻¹ (nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 φ)),
    Lp.coeFn_smul (∫ x, φ x) (nKappa hh hr j),
    Lp.coeFn_sub (((r (j + 1) / r j) ^ 2)⁻¹ •
      nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 phiOne)) (nPV hh hr (j + 1) phiOne),
    Lp.coeFn_smul ((r (j + 1) / r j) ^ 2)⁻¹
      (nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 phiOne))]
    with ω h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h1, h5, Pi.sub_apply, h6, h7, Pi.smul_apply, Pi.smul_apply, h2]
  rw [show nKappa hh hr j = ((r (j + 1) / r j) ^ 2)⁻¹ •
      nPV hh hr j (testAffinePull (r (j + 1) / r j) 0 phiOne) - nPV hh hr (j + 1) phiOne from rfl,
    h8, Pi.sub_apply, h9, Pi.smul_apply, h4, h3, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    key φ ω, key phiOne ω, integral_phiOne]
  ring

/-- the increments `δ_j` -/
def nDelta : ℕ → TestC → Lp ℝ 2 P
  | 0, φ => nA hh hr 0 φ
  | j + 1, φ => ((r (j + 1) / r j) ^ 2)⁻¹ • nZ hh hr j (testAffinePull (r (j + 1) / r j) 0 φ) -
      nZ hh hr (j + 1) φ - (∫ x, φ x) • nProj hh hr j (nKappa hh hr j)

lemma nDelta_succ_eq (j : ℕ) (φ : TestC) :
    nDelta hh hr (j + 1) φ = nA hh hr (j + 1) φ -
      ((r (j + 1) / r j) ^ 2)⁻¹ • nA hh hr j (testAffinePull (r (j + 1) / r j) 0 φ) +
      (∫ x, φ x) • (nKappa hh hr j - nProj hh hr j (nKappa hh hr j)) := by
  simp only [nDelta, nA]
  rw [nPV_succ hh hr j φ]
  simp only [smul_sub]
  abel

include hA in
lemma nDelta_succ_mem (j : ℕ) (φ : TestC) : nDelta hh hr (j + 1) φ ∈ nK hh hr j := by
  simp only [nDelta]
  exact sub_mem (sub_mem (Submodule.smul_mem _ _ (nZ_mem hh hr j _))
    (nK_succ_le hh hr hA j (nZ_mem hh hr (j + 1) φ)))
    (Submodule.smul_mem _ _ (nProj_mem hh hr j _))

include hA in
lemma inner_nDelta (i : ℕ) (φ : TestC) (w : Lp ℝ 2 P) (hw : w ∈ nK hh hr i) :
    ⟪nDelta hh hr i φ, w⟫ = 0 := by
  cases i with
  | zero => exact inner_nA hh hr 0 φ w hw
  | succ j =>
    have hw' := nK_succ_le hh hr hA j hw
    rw [nDelta_succ_eq, inner_add_left, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, inner_nA hh hr (j + 1) φ w hw, inner_nA hh hr j _ w hw',
      inner_sub_nProj hh hr j _ w hw']
    simp

include hA in
lemma inner_nDelta_nDelta {i j : ℕ} (hij : i ≤ j) (φ ψ : TestC) :
    ⟪nDelta hh hr (j + 1) φ, nDelta hh hr i ψ⟫ = 0 := by
  rw [real_inner_comm]
  exact inner_nDelta hh hr hA i ψ _ (nK_anti hh hr hA hij (nDelta_succ_mem hh hr hA j φ))

include hA in
lemma inner_nDelta_compl (j : ℕ) (φ ψ : TestC) :
    ⟪nDelta hh hr j φ, nPV hh hr j ψ - nDelta hh hr j ψ⟫ = 0 := by
  cases j with
  | zero =>
    have e : nPV hh hr 0 ψ - nDelta hh hr 0 ψ = nZ hh hr 0 ψ := by
      simp only [nDelta, nA]; abel
    rw [e]
    exact inner_nDelta hh hr hA 0 φ _ (nZ_mem hh hr 0 ψ)
  | succ j =>
    have e : nPV hh hr (j + 1) ψ - nDelta hh hr (j + 1) ψ = nZ hh hr (j + 1) ψ +
        ((r (j + 1) / r j) ^ 2)⁻¹ • nA hh hr j (testAffinePull (r (j + 1) / r j) 0 ψ) -
        (∫ x, ψ x) • (nKappa hh hr j - nProj hh hr j (nKappa hh hr j)) := by
      rw [nDelta_succ_eq]; simp only [nA]; abel
    have hm := nDelta_succ_mem hh hr hA j φ
    rw [e, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_nDelta hh hr hA (j + 1) φ _ (nZ_mem hh hr (j + 1) ψ), real_inner_comm,
      inner_nA hh hr j _ _ hm, real_inner_comm, inner_sub_nProj hh hr j _ _ hm]
    simp

lemma nDelta_mem (j : ℕ) (φ : TestC) :
    nDelta hh hr j φ ∈ gaussSpace (pairProc h) (memLp_pair hh.1) := by
  cases j with
  | zero => exact sub_mem (nPV_mem hh hr 0 φ) (nK_le_gauss hh hr 0 (nZ_mem hh hr 0 φ))
  | succ j =>
    simp only [nDelta]
    exact sub_mem (sub_mem (Submodule.smul_mem _ _ (nK_le_gauss hh hr j (nZ_mem hh hr j _)))
      (nK_le_gauss hh hr (j + 1) (nZ_mem hh hr (j + 1) φ)))
      (Submodule.smul_mem _ _ (nK_le_gauss hh hr j (nProj_mem hh hr j _)))

end LQGMetric.LM
