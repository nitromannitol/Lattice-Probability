/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaExistence at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceTRL
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GaussianToolkit
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# M4-A1, part 1: the two-radius lemma for the free field's approximating area measures

Blueprint `M4_BLUEPRINT.md`, node M4-A1 (the area analogue of M4-B2/B3).

For the free field `X` (`IsFreeGFFModConstH X P`) and `R > 0` we work with the normalized field
`aZ X R ω = addConst (X ω) (-X ω (fc(0,R)))` (`Z` of blueprint §0). On a region `S ⊆ ℍ` with
`Im z ≥ d > 0` and `‖z‖ + 1 ≤ R`, at radii `2^{-k} ≤ d`, folded circles are genuine circles and
the interior kernel identities (`kernelCov_fc_interior_*`) give the Gaussian structure.

* `trlHypC_field`: the planar hypotheses `TRLHypC` hold for `U z = avgReg (Z) k z` and
  `Δ z = avgReg (Z) (k+1) z - U z`, with `L = ½ log 2^k`, `K = 2 log R - log (2d)`,
  `W = log 2`, `δ = 2^{1-k}`.
* `integral_abs_areaApprox_step_le_rate`: `E|∫ f dμ_k - ∫ f dμ_{k+1}| ≤ C e^{-β k log 2}`,
  `β = areaRate γ > 0` for every `γ ∈ (0,2)`.
* `integral_abs_areaApprox_sub_le_rate`: the telescoped form, for `k₀ ≤ k ≤ k'`.
* `areaApprox_L1_rate`: the same for `f` continuous with compact support in `ℍ ∩ B(0,R-1)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaExist

open GaussTK TwoRadius TwoRadiusC KernelId

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The normalized field `Z = X − X(fc(0,R))`. -/
def aZ (X : Ω → FieldSample) (R : ℝ) (ω : Ω) : FieldSample :=
  addConst (X ω) (-X ω (foldedCircle 0 R))

/-- Coarse coordinate `U z = h_{2^{-k}}(z)` of the normalized field. -/
def aU (X : Ω → FieldSample) (R : ℝ) (k : ℕ) (z : ℂ) (ω : Ω) : ℝ :=
  avgReg (aZ X R ω) k z

/-- Increment `Δ z = h_{2^{-k-1}}(z) − h_{2^{-k}}(z)`. -/
def aΔ (X : Ω → FieldSample) (R : ℝ) (k : ℕ) (z : ℂ) (ω : Ω) : ℝ :=
  aU X R (k + 1) z ω - aU X R k z ω

/-- Density of `areaApprox γ (Z ω) k` (on `ℍ`). -/
def aDens (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (k : ℕ) (z : ℂ) (ω : Ω) : ℝ :=
  radius k ^ (γ ^ 2 / 2) * exp (γ * aU X R k z ω)

/-- Variance of `U z`. -/
def aV (R : ℝ) (k : ℕ) (z : ℂ) : ℝ≥0 :=
  (fcPairCov (z, radius k, 0, R) (z, radius k, 0, R)).toNNReal

theorem aradius_succ (k : ℕ) : radius (k + 1) = radius k / 2 := by
  simp [radius, pow_succ, div_eq_mul_inv]

theorem aradius_le_one (k : ℕ) : radius k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem aradius_anti {j k : ℕ} (h : j ≤ k) : radius k ≤ radius j :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem alog_one_div_radius (k : ℕ) : log (1 / radius k) = k * log 2 := by
  rw [one_div, log_inv, radius, log_pow, log_inv]; ring

theorem measurable_aZ (hX : IsFreeGFFModConstH X P) (R : ℝ) : Measurable (aZ X R) := by
  refine measurable_pi_iff.mpr fun μ => ?_
  simp only [aZ, addConst]
  exact (hX.measurable_coord μ).add ((hX.measurable_coord _).neg.mul_const _)

theorem measurable_aU (hX : IsFreeGFFModConstH X P) (R : ℝ) (k : ℕ) :
    Measurable (fun p : ℂ × Ω => aU X R k p.1 p.2) :=
  (measurable_avgReg k).comp (((measurable_aZ hX R).comp measurable_snd).prodMk measurable_fst)

/-! ### Almost sure identification of `avgReg` -/

theorem ae_avgReg_spec (hX : IsFreeGFFModConstH X P) (k : ℕ) :
    (∀ᵐ ω ∂P, ∀ z ∈ Hbar, Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 (avgReg (X ω) k z))) ∧
    ∀ z ∈ Hbar, (fun ω => avgReg (X ω) k z) =ᵐ[P] fun ω => X ω (foldedCircle z (radius k)) := by
  have hr := radius_pos k
  obtain ⟨Y, -, hae, hlim⟩ := CircleCont.exists_continuous_modification
    (Z := fun z ω => X ω (foldedCircle z (radius k)) - X ω (foldedCircle 0 (radius k)))
    (fun z => ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable)
    (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hr.le) 4) (gaussianAbsMoment_nonneg 8))
    (CircleCont.momentBound_circleDiff hX hr 0)
  have hlim' : ∀ᵐ ω ∂P, ∀ z ∈ Hbar,
      Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)))
        atTop (𝓝 (Y z ω + X ω (foldedCircle 0 (radius k)))) := by
    filter_upwards [hlim] with ω hω z hz
    have := (hω z hz).add_const (X ω (foldedCircle 0 (radius k)))
    simpa using this
  refine ⟨?_, ?_⟩
  · filter_upwards [hlim'] with ω hω z hz
    have h := hω z hz
    have he : avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) := h.limUnder_eq
    rw [he]; exact h
  · intro z hz
    filter_upwards [hlim', hae z hz] with ω hω hY
    have he : avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) := (hω z hz).limUnder_eq
    rw [he, hY]
    ring

theorem ae_avgReg_aZ (hX : IsFreeGFFModConstH X P) (R : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ z ∈ Hbar,
      avgReg (aZ X R ω) k z = avgReg (X ω) k z - X ω (foldedCircle 0 R) := by
  filter_upwards [(ae_avgReg_spec hX k).1] with ω hω z hz
  have h := (hω z hz).add_const (-X ω (foldedCircle 0 R))
  have e : (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)) + -X ω (foldedCircle 0 R)) =
      fun n => aZ X R ω (foldedCircle (dyadicRoundC n z) (radius k)) := by
    funext n; simp [aZ, addConst]
  rw [e] at h
  have := h.limUnder_eq
  change avgReg (aZ X R ω) k z = _ at this
  rw [this]; ring

theorem avgReg_aZ_ae_eq (hX : IsFreeGFFModConstH X P) (R : ℝ) (k : ℕ) {z : ℂ}
    (hz : z ∈ Hbar) :
    (fun ω => avgReg (aZ X R ω) k z) =ᵐ[P] fcPairVal X (z, radius k, 0, R) := by
  filter_upwards [ae_avgReg_aZ hX R k, (ae_avgReg_spec hX k).2 z hz] with ω h1 h2
  rw [h1 z hz, h2]; rfl

theorem hasLaw_fcPairVal' (hX : IsFreeGFFModConstH X P) {p : FcIdx} (hp : p.Good) :
    HasLaw (fcPairVal X p) (gaussianReal 0 (fcPairCov p p).toNNReal) P := by
  have hG : HasGaussianLaw (fcPairVal X p) P :=
    (isGaussianProcess_fcPair hX).hasGaussianLaw_eval ⟨p, hp⟩
  have hm : AEMeasurable (fcPairVal X p) P := (measurable_fcPairVal hX p).aemeasurable
  refine ⟨hm, ?_⟩
  rw [hG.map_eq_gaussianReal, integral_fcPairVal hX hp, ← covariance_self hm,
    covariance_fcPairVal hX hp hp]

/-! ### Interior covariances (M4-R1 interior, M4-R2(c)) -/

theorem two_im_le_norm_sub_conj (z : ℂ) : 2 * z.im ≤ ‖z - conj z‖ := by
  have := im_add_im_le_norm_sub_conj z z; linarith

theorem mem_Hbar_of_le_im {z : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ z.im) : z ∈ Hbar :=
  show 0 ≤ z.im by linarith

theorem fcPairCov_Zself_int {z : ℂ} {r R : ℝ} (hr : 0 < r) (hrz : r ≤ z.im)
    (h : ‖z‖ + r ≤ R) :
    fcPairCov (z, r, 0, R) (z, r, 0, R) = 2 * log R - log r - log ‖z - conj z‖ := by
  rw [fcPairCov_Z hr hr h h, kernelCov_fc_interior_sameCenter hr hr hrz hrz, max_self]; ring

theorem fcPairCov_incr_self_int {z : ℂ} {r : ℝ} (hr : 0 < r) (hrz : r ≤ z.im) :
    fcPairCov (z, r / 2, z, r) (z, r / 2, z, r) = log 2 := by
  have hr2 : 0 < r / 2 := by positivity
  have hle : r / 2 ≤ r := by linarith
  have hr2z : r / 2 ≤ z.im := hle.trans hrz
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hr2 hr2 hr2z hr2z,
    kernelCov_fc_interior_sameCenter hr2 hr hr2z hrz,
    kernelCov_fc_interior_sameCenter hr hr2 hrz hr2z,
    kernelCov_fc_interior_sameCenter hr hr hrz hrz, max_eq_right hle, max_eq_left hle]
  simp only [max_self]
  rw [log_div hr.ne' two_ne_zero]
  ring

theorem fcPairCov_incr_Zsame_int {z : ℂ} {ε ε' R : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hε'z : ε' ≤ z.im) (hR : ‖z‖ + ε' ≤ R) :
    fcPairCov (z, ε, z, ε') (z, ε', 0, R) = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hε hε' (hεε'.trans hε'z) hε'z,
    kernelCov_fc_interior_sameCenter hε' hε' hε'z hε'z,
    kernelCov_fc_bigCircle_right hε (by linarith),
    kernelCov_fc_bigCircle_right hε' hR, max_eq_right hεε', max_self]
  ring

theorem fcPairCov_incr_Zfar_int {z u : ℂ} {ε ε' r R : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hε'z : ε' ≤ z.im) (hr : 0 < r) (hru : r ≤ u.im) (hR : ‖z‖ + ε' ≤ R)
    (htu : ε' + r ≤ ‖z - u‖) :
    fcPairCov (z, ε, z, ε') (u, r, 0, R) = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_separated hε hr (hεε'.trans hε'z) hru (by linarith),
    kernelCov_fc_interior_separated hε' hr hε'z hru htu,
    kernelCov_fc_bigCircle_right hε (by linarith),
    kernelCov_fc_bigCircle_right hε' hR]
  ring

theorem fcPairCov_incr_incr_far_int {z u : ℂ} {ε ε' δ δ' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hε'z : ε' ≤ z.im) (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδ'u : δ' ≤ u.im)
    (htu : ε' + δ' ≤ ‖z - u‖) :
    fcPairCov (z, ε, z, ε') (u, δ, u, δ') = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_separated hε hδ (hεε'.trans hε'z) (hδδ'.trans hδ'u) (by linarith),
    kernelCov_fc_interior_separated hε hδ' (hεε'.trans hε'z) hδ'u (by linarith),
    kernelCov_fc_interior_separated hε' hδ hε'z (hδδ'.trans hδ'u) (by linarith),
    kernelCov_fc_interior_separated hε' hδ' hε'z hδ'u htu]
  ring

/-- Interior version of `GaussTK.indepFun_incr_bullet1`. -/
theorem indepFun_incr_bullet1_int (hX : IsFreeGFFModConstH X P) {z u : ℂ} {ε ε' r δ δ' R : ℝ}
    (hε : 0 < ε) (hεε' : ε ≤ ε') (hε'z : ε' ≤ z.im) (hr : 0 < r) (hru : r ≤ u.im)
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδ'u : δ' ≤ u.im)
    (hR : ‖z‖ + ε' ≤ R) (hu : ‖u‖ + r ≤ R) (htu : ε' + max r δ' ≤ ‖z - u‖) :
    IndepFun (fun ω (_ : Unit) => fcPairVal X (z, ε, z, ε') ω)
      (fun ω (i : Fin 3) => fcPairVal X
        (![(z, ε', 0, R), (u, r, 0, R), (u, δ, u, δ')] i) ω) P := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  have hR0 : 0 < R := by linarith [norm_nonneg z]
  have hzH := mem_Hbar_of_le_im hε' hε'z
  have huH := mem_Hbar_of_le_im hr hru
  have hg : ∀ i : Fin 3, FcIdx.Good (![(z, ε', 0, R), (u, r, 0, R), (u, δ, u, δ')] i) := by
    intro i
    fin_cases i
    · exact good_Z hzH hε' hR0
    · exact good_Z huH hr hR0
    · exact ⟨huH, hδ, huH, hδ.trans_le hδδ'⟩
  refine indepFun_fcPair hX (fun _ => ⟨_, ⟨hzH, hε, hzH, hε'⟩⟩) (fun i => ⟨_, hg i⟩) ?_
  intro _ i
  fin_cases i
  · exact fcPairCov_incr_Zsame_int hε hεε' hε'z hR
  · exact fcPairCov_incr_Zfar_int hε hεε' hε'z hr hru hR (by linarith [le_max_left r δ'])
  · exact fcPairCov_incr_incr_far_int hε hεε' hε'z hδ hδδ' hδ'u
      (by linarith [le_max_right r δ'])

/-! ### The Gaussian hypotheses of the planar two-radius lemma -/

/-- **Instantiation of `TRLHypC`** for the normalized free field at the consecutive radii
`2^{-k}` (coarse, `U`) and `2^{-k-1}` (fine, `U + Δ`), on any `S` with `‖z‖ + 1 ≤ R` and
`Im z ≥ d ≥ 2^{-k}`. -/
theorem trlHypC_field (hX : IsFreeGFFModConstH X P) {R d : ℝ} {S : Set ℂ} (hd1 : 2 * d ≤ 1)
    (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) (hSd : ∀ z ∈ S, d ≤ z.im) {k : ℕ} (hk : radius k ≤ d) :
    TRLHypC P S (2 * radius k) (2 * log R - log (2 * d)) (log 2)
      (fun _ => 1 / 2 * log (1 / radius k)) (aV R k) (fun _ => (log 2).toNNReal)
      (aU X R k) (aΔ X R k) := by
  have hr := radius_pos k
  have hr1 := aradius_le_one k
  have hd : 0 < d := hr.trans_le hk
  have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg one_le_two
  have hrz : ∀ z ∈ S, radius k ≤ z.im := fun z hz => hk.trans (hSd z hz)
  have hzH : ∀ z ∈ S, z ∈ Hbar := fun z hz => mem_Hbar_of_le_im hr (hrz z hz)
  have hUe : ∀ j, ∀ z ∈ S, aU X R j z =ᵐ[P] fcPairVal X (z, radius j, 0, R) :=
    fun j z hz => avgReg_aZ_ae_eq hX R j (hzH z hz)
  have hΔe : ∀ z ∈ S, aΔ X R k z =ᵐ[P] fcPairVal X (z, radius k / 2, z, radius k) := by
    intro z hz
    filter_upwards [hUe (k + 1) z hz, hUe k z hz] with ω h1 h2
    simp only [aΔ, h1, h2, fcPairVal, aradius_succ]
    ring
  have hR : ∀ z ∈ S, ‖z‖ + radius k ≤ R := fun z hz => by linarith [hSR z hz]
  have hR0 : ∀ z ∈ S, 0 < R := fun z hz => by linarith [hSR z hz, norm_nonneg z]
  refine
    { measU := measurable_aU hX R k
      measΔ := (measurable_aU hX R (k + 1)).sub (measurable_aU hX R k)
      measL := measurable_const
      measw := measurable_const
      lawU := ?_, lawΔ := ?_, varU := ?_, varΔ := ?_, indep := ?_, decor := ?_ }
  · intro z hz
    exact (hasLaw_fcPairVal' hX (good_Z (hzH z hz) hr (hR0 z hz))).congr (hUe k z hz)
  · intro z hz
    have := (hasLaw_fcPairVal' hX (p := (z, radius k / 2, z, radius k))
      ⟨hzH z hz, by positivity, hzH z hz, hr⟩).congr (hΔe z hz)
    rwa [fcPairCov_incr_self_int hr (hrz z hz)] at this
  · intro z hz
    have hlogR : 0 ≤ log R := log_nonneg (by linarith [hSR z hz, norm_nonneg z])
    have hlogr : log (radius k) ≤ 0 := log_nonpos hr.le hr1
    have hlogd : log (2 * d) ≤ 0 := log_nonpos (by positivity) hd1
    have hc : log (2 * d) ≤ log ‖z - conj z‖ :=
      log_le_log (by positivity) (by linarith [two_im_le_norm_sub_conj z, hSd z hz])
    show ((fcPairCov (z, radius k, 0, R) (z, radius k, 0, R)).toNNReal : ℝ) ≤
      2 * (1 / 2 * log (1 / radius k)) + (2 * log R - log (2 * d))
    rw [Real.coe_toNNReal', fcPairCov_Zself_int hr (hrz z hz) (hR z hz),
      show log (1 / radius k) = -log (radius k) by rw [one_div, log_inv]]
    exact max_le (by linarith) (by linarith)
  · intro z _
    exact (Real.coe_toNNReal _ hlog2).le
  · intro z hz
    have hI := indepFun_fcPair hX
      (fun _ : Unit => (⟨(z, radius k / 2, z, radius k),
        ⟨hzH z hz, by positivity, hzH z hz, hr⟩⟩ : {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨(z, radius k, 0, R),
        good_Z (hzH z hz) hr (hR0 z hz)⟩ : {p : FcIdx // p.Good}))
      (fun _ _ => fcPairCov_incr_Zsame_int (by positivity) (by linarith) (hrz z hz) (hR z hz))
    have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
    exact hI2.congr (hΔe z hz).symm (hUe k z hz).symm
  · intro z hz u hu hzu
    have hI := indepFun_incr_bullet1_int hX (z := z) (u := u) (ε := radius k / 2)
      (ε' := radius k) (r := radius k) (δ := radius k / 2) (δ' := radius k) (R := R)
      (by positivity) (by linarith) (hrz z hz) hr (hrz u hu) (by positivity) (by linarith)
      (hrz u hu) (hR z hz) (hR u hu) (by rw [max_self]; linarith)
    have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    have hI2 := hI.comp (measurable_pi_apply ()) hφ
    refine hI2.congr (hΔe z hz).symm ?_
    filter_upwards [hUe k z hz, hUe k u hu, hΔe u hu] with ω h1 h2 h3
    simp [h1, h2, h3]

/-! ### Pathwise integrals and integrability -/

/-- `∫ f dμ_k` as a Lebesgue integral over `S ⊆ ℍ` when `f` vanishes off `S`. -/
theorem integral_areaApprox_eq (γ : ℝ) (x : FieldSample) (k : ℕ) {S : Set ℂ}
    (hSH : S ⊆ H) {f : ℂ → ℝ} (hfS : ∀ z ∉ S, f z = 0) :
    ∫ z, f z ∂(areaApprox γ x k) =
      ∫ z in S, f z * (radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z)) := by
  have hm : Measurable (fun z : ℂ => avgReg x k z) :=
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable (fun z : ℂ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hm.const_mul _).exp))
  unfold areaApprox
  rw [integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  calc ∫ z in H, (ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z))).toReal • f z
      = ∫ z in H, f z * (radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z)) := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [smul_eq_mul]
        rw [ENNReal.toReal_ofReal (mul_nonneg (rpow_nonneg (radius_pos k).le _) (exp_pos _).le)]
        ring
    _ = ∫ z, f z * (radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z)) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
          rw [hfS z (fun hzS => hz (hSH hzS)), zero_mul]
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
          rw [hfS z hz, zero_mul]).symm

section Integrability

variable [IsProbabilityMeasure P]

theorem integral_exp_aU (hX : IsFreeGFFModConstH X P) {R d : ℝ} {S : Set ℂ} (hd1 : 2 * d ≤ 1)
    (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) (hSd : ∀ z ∈ S, d ≤ z.im) {k : ℕ} (hk : radius k ≤ d)
    {z : ℂ} (hz : z ∈ S) (c : ℝ) :
    ∫ ω, exp (c * aU X R k z ω) ∂P = exp (aV R k z * c ^ 2 / 2) := by
  have hL := (trlHypC_field hX hd1 hSR hSd hk).lawU z hz
  have h2 := integral_exp_mul_add_gaussianReal (aV R k z) c 0
  simp only [zero_add] at h2
  rw [← h2]
  exact hL.integral_comp (f := fun x => exp (c * x)) (by fun_prop)

/-- Joint integrability of `f z · dens_j(z, ω)` on `P × (vol|S)`. -/
theorem integrable_fDensA (hX : IsFreeGFFModConstH X P) {R d : ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hd1 : 2 * d ≤ 1)
    (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) (hSd : ∀ z ∈ S, d ≤ z.im) (γ : ℝ) {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) {j : ℕ} (hj : radius j ≤ d) :
    Integrable (fun p : Ω × ℂ => f p.2 * aDens γ X R j p.2 p.1) (P.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  have h := trlHypC_field (P := P) hX hd1 hSR hSd hj
  have h1 : Measurable (fun p : Ω × ℂ => aU X R j p.2 p.1) :=
    show Measurable (fun p : Ω × ℂ => avgReg (aZ X R p.1) j p.2) from
      (measurable_avgReg j).comp (((measurable_aZ hX R).comp measurable_fst).prodMk
        measurable_snd)
  have hmeas : Measurable (fun p : Ω × ℂ => f p.2 * aDens γ X R j p.2 p.1) :=
    (hf.comp measurable_snd).mul (measurable_const.mul ((h1.const_mul _).exp))
  have hr := (rpow_pos_of_pos (radius_pos j) (γ ^ 2 / 2))
  set Vb := 2 * (1 / 2 * log (1 / radius j)) + (2 * log R - log (2 * d)) with hVb
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' hS]
    refine ae_of_all _ fun z hz => ?_
    have hL := h.lawU z hz
    have hi : Integrable (fun ω => exp (0 + γ * aU X R j z ω)) P :=
      hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ γ 0)
    simp only [zero_add] at hi
    exact (hi.const_mul _).const_mul (f z)
  · refine Integrable.mono' (integrable_const
      (M * (radius j ^ (γ ^ 2 / 2) * exp (Vb * γ ^ 2 / 2)))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [ae_restrict_iff' hS]
      refine ae_of_all _ fun z hz => ?_
      have e : ∀ ω, ‖f z * aDens γ X R j z ω‖ =
          |f z| * (radius j ^ (γ ^ 2 / 2) * exp (γ * aU X R j z ω)) := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, aDens, abs_of_pos (mul_pos hr (exp_pos _))]
      simp_rw [e]
      rw [integral_const_mul, integral_const_mul, integral_exp_aU hX hd1 hSR hSd hj hz,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hv : (aV R j z : ℝ) * γ ^ 2 / 2 ≤ Vb * γ ^ 2 / 2 := by
        have := h.varU z hz
        have hg2 : 0 ≤ γ ^ 2 := sq_nonneg γ
        nlinarith
      exact mul_le_mul (hM z) (mul_le_mul_of_nonneg_left (exp_le_exp.2 hv) hr.le)
        (by positivity) ((abs_nonneg _).trans (hM z))

theorem integral_areaApprox_aZ (γ : ℝ) (R : ℝ) (j : ℕ) {S : Set ℂ} (hSH : S ⊆ H)
    {f : ℂ → ℝ} (hfS : ∀ z ∉ S, f z = 0) (ω : Ω) :
    ∫ z, f z ∂(areaApprox γ (aZ X R ω) j) = ∫ z in S, f z * aDens γ X R j z ω :=
  integral_areaApprox_eq γ _ j hSH hfS

theorem integrable_integral_areaApprox (hX : IsFreeGFFModConstH X P) {R d : ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSH : S ⊆ H) (hd1 : 2 * d ≤ 1)
    (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) (hSd : ∀ z ∈ S, d ≤ z.im) (γ : ℝ) {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) (hfS : ∀ z ∉ S, f z = 0) {j : ℕ}
    (hj : radius j ≤ d) :
    Integrable (fun ω => ∫ z, f z ∂(areaApprox γ (aZ X R ω) j)) P := by
  simp_rw [integral_areaApprox_aZ γ R j hSH hfS]
  exact (integrable_fDensA hX hS hSf hd1 hSR hSd γ hf hM hj).integral_prod_left

/-! ### The two-radius bound for consecutive dyadic levels -/

/-- **M4-A1, planar two-radius lemma for the free field**: `E|∫ f dμ_k − ∫ f dμ_{k+1}|` is
bounded by the right side of `trlC_bound_area`, with `δ = 2^{1-k}`, `K = 2 log R - log (2d)`,
`W = log 2`, `Lc = ½ log 2^k`. -/
theorem integral_abs_areaApprox_step_le (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {R d M : ℝ} {S : Set ℂ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hSH : S ⊆ H) (hd1 : 2 * d ≤ 1) (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) (hSd : ∀ z ∈ S, d ≤ z.im)
    {f : ℂ → ℝ} (hf : Measurable f) (hM : ∀ z, |f z| ≤ M) (hfS : ∀ z ∉ S, f z = 0) {k : ℕ}
    (hk : radius k ≤ d) :
    ∫ ω, |∫ z, f z ∂(areaApprox γ (aZ X R ω) k) -
        ∫ z, f z ∂(areaApprox γ (aZ X R ω) (k + 1))| ∂P
      ≤ √(M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
            (exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * (2 * log R - log (2 * d)) / 2) *
            exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) *
              (1 / 2 * log (1 / radius k))))) *
            (π * (2 * radius k) ^ 2 * volume.real S))
        + M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * (2 * log R - log (2 * d)) / 2) *
            exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * log (1 / radius k))))) * volume.real S := by
  have h := trlHypC_field (P := P) hX hd1 hSR hSd hk
  have hk1 : radius (k + 1) ≤ d := (aradius_anti (Nat.le_succ k)).trans hk
  have hr := radius_pos k
  have hb := trlC_bound_area hγ hγ2 (δ := 2 * radius k) (by positivity) hS hSf hf hM h
  refine le_trans (le_of_eq (integral_congr_ae ?_)) hb
  filter_upwards [(integrable_fDensA hX hS hSf hd1 hSR hSd γ hf hM hk).prod_right_ae,
    (integrable_fDensA hX hS hSf hd1 hSR hSd γ hf hM hk1).prod_right_ae] with ω h1 h2
  rw [integral_areaApprox_aZ γ R k hSH hfS, integral_areaApprox_aZ γ R (k + 1) hSH hfS,
    ← integral_sub h1 h2]
  congr 1
  refine setIntegral_congr_fun hS fun z _ => ?_
  set A := aU X R k z ω with hA
  set B := aU X R (k + 1) z ω with hB
  have e1 : radius k ^ (γ ^ 2 / 2) * exp (γ * A)
      = exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (1 / radius k)) + 2 * γ / 2 * A) := by
    rw [rpow_def_of_pos hr, ← exp_add, show log (1 / radius k) = -log (radius k) by rw [one_div, log_inv]]; congr 1; ring
  have e2 : radius (k + 1) ^ (γ ^ 2 / 2) * exp (γ * B)
      = exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (1 / radius k)) + 2 * γ / 2 * A) *
        exp (-((2 * γ) ^ 2 / 8 * log 2) + 2 * γ / 2 * (B - A)) := by
    rw [aradius_succ, rpow_def_of_pos (by positivity), ← exp_add, ← exp_add,
      log_div hr.ne' two_ne_zero,
      show log (1 / radius k) = -log (radius k) by rw [one_div, log_inv]]
    congr 1; ring
  have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg one_le_two
  simp only [aDens, dC, tiltY, aΔ, ← hA, ← hB]
  rw [Real.coe_toNNReal _ hlog2, e1, e2]
  ring

/-- The area rate `β°(γ) = min(e₁°/2, e₂°)`, `e₁° = 2 − γ² + θ²/2` with
`θ = max 0 ((3γ−2)/2)`, and `e₂° = (2−γ)²/8` (blueprint §4). -/
def areaRate (γ : ℝ) : ℝ :=
  min ((2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2) / 2) ((2 - γ) ^ 2 / 8)

theorem areaRate_e1_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < 2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2 := by
  rcases le_total ((3 * γ - 2) / 2) 0 with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

theorem areaRate_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < areaRate γ := by
  unfold areaRate
  have := areaRate_e1_pos hγ hγ2
  have h2 : 0 < (2 - γ) ^ 2 / 8 := div_pos (pow_pos (by linarith) 2) (by norm_num)
  exact lt_min (by linarith) h2

/-- **Rate form:** `E|∫ f dμ_k − ∫ f dμ_{k+1}| ≤ C e^{-β k log 2}`, `β = areaRate γ > 0`,
uniformly in `k` with `2^{-k} ≤ d`. -/
theorem integral_abs_areaApprox_step_le_rate (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R d M : ℝ} {S : Set ℂ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSH : S ⊆ H) (hd1 : 2 * d ≤ 1) (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R)
    (hSd : ∀ z ∈ S, d ≤ z.im) {f : ℂ → ℝ} (hf : Measurable f) (hM : ∀ z, |f z| ≤ M)
    (hfS : ∀ z ∉ S, f z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, radius k ≤ d →
      ∫ ω, |∫ z, f z ∂(areaApprox γ (aZ X R ω) k) -
        ∫ z, f z ∂(areaApprox γ (aZ X R ω) (k + 1))| ∂P
        ≤ C * exp (-areaRate γ * (k * log 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set θ := max 0 ((3 * γ - 2) / 2) with hθ
  set e₁ := 2 - γ ^ 2 + θ ^ 2 / 2 with he₁
  set β := areaRate γ with hβ
  set K := 2 * log R - log (2 * d) with hK
  have hβ1 : β ≤ e₁ / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 8 := min_le_right _ _
  set c₁ := M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
      exp ((2 * γ - θ) ^ 2 * K / 2)) * (4 * π * volume.real S) with hc₁
  set c₂ := M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S
    with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨√c₁ + c₂, by positivity, fun k hk => ?_⟩
  refine (integral_abs_areaApprox_step_le hX hγ hγ2 hS hSf hSH hd1 hSR hSd hf hM hfS hk).trans ?_
  set L := log (1 / radius k) with hL
  have hLk : L = k * log 2 := alog_one_div_radius k
  have hL0 : 0 ≤ L := by rw [hLk]; exact mul_nonneg (Nat.cast_nonneg k) (log_nonneg one_le_two)
  have hrad : radius k = exp (-L) := by
    rw [hL, one_div, log_inv, neg_neg, exp_log (radius_pos k)]
  have hin : M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
        (exp ((2 * γ - θ) ^ 2 * K / 2) * exp ((2 * γ ^ 2 - θ ^ 2) * (1 / 2 * L)))) *
        (π * (2 * radius k) ^ 2 * volume.real S) = c₁ * exp (-e₁ * L) := by
    rw [hrad, hc₁, he₁]
    have : exp ((2 * γ ^ 2 - θ ^ 2) * (1 / 2 * L)) * exp (-L) ^ 2
        = exp (-(2 - γ ^ 2 + θ ^ 2 / 2) * L) := by
      rw [← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
    calc _ = M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
          exp ((2 * γ - θ) ^ 2 * K / 2)) * (4 * π * volume.real S) *
          (exp ((2 * γ ^ 2 - θ ^ 2) * (1 / 2 * L)) * exp (-L) ^ 2) := by ring
      _ = _ := by rw [this]
  have hexp1 : exp (-e₁ * L) ≤ exp (-β * L) ^ 2 := by
    rw [← exp_nat_mul]; apply exp_le_exp.2; push_cast; nlinarith
  have hexp2 : exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * L)) ≤ exp (-β * L) := by
    apply exp_le_exp.2; nlinarith
  rw [hin, ← hLk]
  have ht1 : √(c₁ * exp (-e₁ * L)) ≤ √c₁ * exp (-β * L) := by
    rw [← Real.sqrt_sq (exp_pos (-β * L)).le, ← Real.sqrt_mul hc₁0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hexp1 hc₁0)
  have ht2 : M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
      exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * L)))) * volume.real S ≤ c₂ * exp (-β * L) := by
    rw [hc₂]
    calc _ = M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S *
          exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp2 (by positivity)
  calc _ ≤ √c₁ * exp (-β * L) + c₂ * exp (-β * L) := add_le_add ht1 ht2
    _ = (√c₁ + c₂) * exp (-β * L) := by ring

/-- **Telescoped rate (M4-A1 (1)):** for `k ≤ k'` with `2^{-k} ≤ d`,
`E|∫ f dμ_{k'} − ∫ f dμ_k| ≤ C e^{-β k log 2}`, `β = areaRate γ`. -/
theorem integral_abs_areaApprox_sub_le_rate (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R d M : ℝ} {S : Set ℂ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSH : S ⊆ H) (hd1 : 2 * d ≤ 1) (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R)
    (hSd : ∀ z ∈ S, d ≤ z.im) {f : ℂ → ℝ} (hf : Measurable f) (hM : ∀ z, |f z| ≤ M)
    (hfS : ∀ z ∉ S, f z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k k' : ℕ, radius k ≤ d → k ≤ k' →
      ∫ ω, |∫ z, f z ∂(areaApprox γ (aZ X R ω) k') -
        ∫ z, f z ∂(areaApprox γ (aZ X R ω) k)| ∂P
        ≤ C * exp (-areaRate γ * (k * log 2)) := by
  obtain ⟨C, hC0, hC⟩ :=
    integral_abs_areaApprox_step_le_rate hX hγ hγ2 hS hSf hSH hd1 hSR hSd hf hM hfS
  set q := exp (-areaRate γ * log 2) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq]
    exact Real.exp_lt_one_iff.2 (mul_neg_of_neg_of_pos (neg_neg_of_pos (areaRate_pos hγ hγ2))
      (log_pos one_lt_two))
  have hpow : ∀ j : ℕ, exp (-areaRate γ * (j * log 2)) = q ^ j := by
    intro j; rw [hq, ← exp_nat_mul]; congr 1; ring
  set G : ℕ → Ω → ℝ := fun j ω => ∫ z, f z ∂(areaApprox γ (aZ X R ω) j) with hG
  have hGi : ∀ j, radius j ≤ d → Integrable (G j) P := fun j hj =>
    integrable_integral_areaApprox hX hS hSf hSH hd1 hSR hSd γ hf hM hfS hj
  refine ⟨C / (1 - q), div_nonneg hC0 (by linarith), fun k k' hk hkk' => ?_⟩
  have key : ∀ n : ℕ, ∫ ω, |G (k + n) ω - G k ω| ∂P ≤ C * ∑ i ∈ Finset.Ico k (k + n), q ^ i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hj : radius (k + n) ≤ d := (aradius_anti (Nat.le_add_right k n)).trans hk
      have hj1 : radius (k + n + 1) ≤ d := (aradius_anti (by omega)).trans hk
      have hstep : ∫ ω, |G (k + n) ω - G (k + n + 1) ω| ∂P ≤ C * q ^ (k + n) := by
        have := hC (k + n) hj
        rw [hpow] at this
        exact this
      have hi1 : Integrable (fun ω => |G (k + n) ω - G k ω|) P :=
        ((hGi _ hj).sub (hGi _ hk)).abs
      have hi2 : Integrable (fun ω => |G (k + n) ω - G (k + n + 1) ω|) P :=
        ((hGi _ hj).sub (hGi _ hj1)).abs
      calc ∫ ω, |G (k + (n + 1)) ω - G k ω| ∂P
          ≤ ∫ ω, (|G (k + n) ω - G k ω| + |G (k + n) ω - G (k + n + 1) ω|) ∂P := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hi1.add hi2)
              (ae_of_all _ fun ω => ?_)
            have h3 := abs_sub_le (G (k + n + 1) ω) (G (k + n) ω) (G k ω)
            rw [abs_sub_comm (G (k + n + 1) ω) (G (k + n) ω)] at h3
            rw [show k + (n + 1) = k + n + 1 by ring]
            linarith
        _ = ∫ ω, |G (k + n) ω - G k ω| ∂P + ∫ ω, |G (k + n) ω - G (k + n + 1) ω| ∂P :=
            integral_add hi1 hi2
        _ ≤ C * ∑ i ∈ Finset.Ico k (k + n), q ^ i + C * q ^ (k + n) := add_le_add ih hstep
        _ = C * ∑ i ∈ Finset.Ico k (k + (n + 1)), q ^ i := by
            rw [show k + (n + 1) = k + n + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
            ring
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  calc ∫ ω, |G (k + n) ω - G k ω| ∂P ≤ C * ∑ i ∈ Finset.Ico k (k + n), q ^ i := key n
    _ ≤ C * (q ^ k / (1 - q)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) hC0
    _ = C / (1 - q) * exp (-areaRate γ * (k * log 2)) := by rw [hpow]; ring

end Integrability

/-- A compact subset of `ℍ` stays at positive height (with the height normalized `≤ 1/2`). -/
theorem exists_im_lower_bound {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ d : ℝ, 0 < d ∧ 2 * d ≤ 1 ∧ ∀ z ∈ K, d ≤ z.im := by
  rcases K.eq_empty_or_nonempty with hK0 | hne
  · exact ⟨1 / 2, by norm_num, by norm_num, by simp [hK0]⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    have h0 : 0 < z₀.im := hKH hz₀
    refine ⟨min z₀.im (1 / 2), lt_min h0 (by norm_num),
      by linarith [min_le_right z₀.im (1 / 2)], fun z hz => ?_⟩
    exact (min_le_left _ _).trans (isMinOn_iff.mp hmin z hz)

/-- **M4-A1 (1), test-function form.** For `f` continuous with compact support in
`ℍ ∩ {‖z‖ + 1 ≤ R}`, there are `C ≥ 0` and `k₀` with
`E|∫ f d(areaApprox γ Z k') − ∫ f d(areaApprox γ Z k)| ≤ C e^{-β k log 2}` for `k₀ ≤ k ≤ k'`,
`β = areaRate γ > 0`, `Z = X − X(fc(0,R))`. -/
theorem areaApprox_L1_rate [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) (hfR : ∀ z ∈ tsupport f, ‖z‖ + 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∃ k₀ : ℕ,
      (∀ k : ℕ, k₀ ≤ k → Integrable (fun ω => ∫ z, f z ∂(areaApprox γ (aZ X R ω) k)) P) ∧
      ∀ k k' : ℕ, k₀ ≤ k → k ≤ k' →
      ∫ ω, |∫ z, f z ∂(areaApprox γ (aZ X R ω) k') -
        ∫ z, f z ∂(areaApprox γ (aZ X R ω) k)| ∂P
        ≤ C * exp (-areaRate γ * (k * log 2)) := by
  obtain ⟨d, hd, hd1, hSd⟩ := exists_im_lower_bound hfc.isCompact hfH
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨C, hC0, hC⟩ := integral_abs_areaApprox_sub_le_rate hX hγ hγ2
    (isClosed_tsupport f).measurableSet hfc.isCompact.measure_lt_top hfH hd1 hfR hSd
    hf.measurable (M := M) (fun z => by simpa [Real.norm_eq_abs] using hM z)
    (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hd (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨C, hC0, k₀, fun k hk => ?_, fun k k' hk hkk' =>
    hC k k' ((aradius_anti hk).trans hk₀.le) hkk'⟩
  exact integrable_integral_areaApprox hX (isClosed_tsupport f).measurableSet
    hfc.isCompact.measure_lt_top hfH hd1 hfR hSd γ hf.measurable (M := M)
    (fun z => by simpa [Real.norm_eq_abs] using hM z)
    (fun z hz => image_eq_zero_of_notMem_tsupport hz) ((aradius_anti hk).trans hk₀.le)

end AreaExist
end QuantumZipper
