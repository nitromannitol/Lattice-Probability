/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6EtaVar
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Cont
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Sum
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box

/-!
# DZZ Lemma 2.7, uniform Gaussian tail of `Σ_i |Δ_i|` (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Lemma 2.7 (`lem-tilde-h-eta`),
l. 548–576: `P(max_{v∈𝕍} max_{j≥0} |h̃_{2^{-j}}(v) − η_{2^{-j}}(v)|≥ λ) ≤ O(1)e^{−Ω(λ²)}`, proved by
bounding `Σ_i max_v |Δ_i(v)|`. Here (for continuous versions `Y_i` of `Δ_i`):

* `deltaKernel i x = K^{h̃}_x − K^η_x` on the band `bandSet i` (DZZ's `Δ_i = √π W(deltaKernel i ·)`
  a.s., `dzzDelta_ae_eq`);
* (eq-variance-truncation) `π‖deltaKernel i x‖² ≤ Kρ^i` (`dzz_variance_truncation`);
* (eq-feb25, increment half) `‖deltaKernel i x − deltaKernel i x'‖² ≤ K₁ 2^i |x − x'|`, from Lemma 2.5
  for `h̃` and `η` on the band (`dzz_lemma25_wnField`, `dzz_lemma25_etaField`; the latter assumes
  `BridgeShellBound`);
* continuous versions exist (`exists_continuous_modification_of_kernel_half`);
* `dzz_lemma27_sum`: `P(∃ v ∈ [0,1]², ∃ n, λ ≤ Σ_{i<n} |Y_i(v)|) ≤ C e^{−λ²/C}` via the probabilistic
  core `dzz_sum_sup_tail` (DZZ l. 565–576 with Lemmas 2.1, 2.3).

Not yet done: the a.s. telescoping `h̃_{2^{-j}} − η_{2^{-j}} = Σ_{i≤j} Δ_i` (see handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### Fields `√π W(F x)` -/

theorem isGaussianProcess_sqrtPi (hW : IsWhiteNoise P W) {T : Type} (F : T → WNSpace) :
    IsGaussianProcess (fun t ω => Real.sqrt Real.pi * W (F t) ω) P :=
  QuantumZipper.GFFExist.gs_isGaussianProcess
    (fun t => ((hW.measurable _).const_mul _).aemeasurable)
    fun I c => ⟨_, (hW.hasLaw (fun i : I => F i)
      (fun i => c i * Real.sqrt Real.pi)).congr (Eventually.of_forall fun ω => by
        exact Finset.sum_congr rfl fun i _ => by ring)⟩

lemma integral_sqrtPi (hW : IsWhiteNoise P W) (f : WNSpace) :
    ∫ ω, Real.sqrt Real.pi * W f ω ∂P = 0 := by
  rw [integral_const_mul, QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _),
    mul_zero]

lemma variance_sqrtPi (hW : IsWhiteNoise P W) (f : WNSpace) :
    Var[fun ω => Real.sqrt Real.pi * W f ω; P] = Real.pi * ‖f‖ ^ 2 := by
  have e : (fun ω => Real.sqrt Real.pi * W f ω) = Real.sqrt Real.pi • W f := rfl
  rw [e, variance_smul, (hW.hasLaw_single f).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity), Real.sq_sqrt Real.pi_pos.le]

lemma integral_sq_sqrtPi_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    ∫ ω, (Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) ^ 2 ∂P =
      Real.pi * ‖f - g‖ ^ 2 := by
  have := hW.isProbabilityMeasure
  have hm : AEMeasurable (fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) P :=
    (((hW.measurable _).const_mul _).sub ((hW.measurable _).const_mul _)).aemeasurable
  have hmf : MemLp (fun ω => Real.sqrt Real.pi * W f ω) 2 P :=
    ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  have hmg : MemLp (fun ω => Real.sqrt Real.pi * W g ω) 2 P :=
    ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  have h0 : ∫ ω, (Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) ∂P = 0 := by
    rw [integral_sub (hmf.integrable one_le_two) (hmg.integrable one_le_two),
      integral_sqrtPi hW, integral_sqrtPi hW, sub_zero]
  rw [← variance_of_integral_eq_zero hm h0, variance_sqrtPi_sub hW]

/-! ### The band kernels -/

/-- The time set of `Δ_i`: `(1, ∞)` for `i = 0`, `(4^{-i}, 4^{-i+1})` for `i ≥ 1`. -/
def bandSet (i : ℕ) : Set ℝ :=
  if i = 0 then Ioi ((1 : ℝ) ^ 2) else Ioo (((1 / 2 : ℝ) ^ i) ^ 2) (((1 / 2 : ℝ) ^ (i - 1)) ^ 2)

lemma measurableSet_bandSet (i : ℕ) : MeasurableSet (bandSet i) := by
  unfold bandSet; split_ifs
  · exact measurableSet_Ioi
  · exact measurableSet_Ioo

lemma bandSet_subset (i : ℕ) : bandSet i ⊆ Ioi (((1 / 2 : ℝ) ^ i) ^ 2) := by
  unfold bandSet; split_ifs with h
  · subst h; simp
  · exact Ioo_subset_Ioi_self

/-- DZZ's `Δ_i(x) = √π W(deltaKernel i x)`. -/
def deltaKernel (i : ℕ) (x : ℂ) : WNSpace :=
  wndKernelL2 openSquare (bandSet i) x - etaKernelL2 (bandSet i) x

lemma dzzDelta_eq (W : WNSpace → Ω → ℝ) (i : ℕ) (x : ℂ) :
    dzzDelta W i x = fun ω => wnField W openSquare (bandSet i) x ω - etaField W (bandSet i) x ω := by
  funext ω
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [dzzDelta, bandSet, tildeHInf, etaInf]
  · simp [dzzDelta, bandSet, tildeH, eta, h.ne']

/-- `Δ_i(x) = √π W(deltaKernel i x)` almost surely. -/
lemma dzzDelta_ae_eq (hW : IsWhiteNoise P W) (i : ℕ) (x : ℂ) :
    dzzDelta W i x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (deltaKernel i x) ω := by
  rw [dzzDelta_eq]
  have h1 := hW.add_ae (wndKernelL2 openSquare (bandSet i) x) (-etaKernelL2 (bandSet i) x)
  have h2 := hW.smul_ae (-1) (etaKernelL2 (bandSet i) x)
  filter_upwards [h1, h2] with ω e1 e2
  simp only [deltaKernel, sub_eq_add_neg, wnField, etaField]
  have e3 : W (-etaKernelL2 (bandSet i) x) ω = -W (etaKernelL2 (bandSet i) x) ω := by
    rw [← neg_one_smul ℝ (etaKernelL2 (bandSet i) x), e2]; ring
  rw [e1, e3]
  ring

lemma sq_norm_sub_sub_le (a b c d : WNSpace) :
    ‖(a - b) - (c - d)‖ ^ 2 ≤ 2 * ‖a - c‖ ^ 2 + 2 * ‖b - d‖ ^ 2 := by
  have e : (a - b) - (c - d) = (a - c) - (b - d) := by abel
  rw [e]
  have h := norm_sub_le (a - c) (b - d)
  have h' : ‖(a - c) - (b - d)‖ ^ 2 ≤ (‖a - c‖ + ‖b - d‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a - c‖ - ‖b - d‖)]

/-- (eq-feb25), increment half: `‖Δ_i(x) − Δ_i(x')‖²_{L²} ≤ K₁ 2^i |x − x'|`. -/
theorem sq_norm_deltaKernel_sub_le {C : ℝ} (hC0 : 0 ≤ C) (hC : BridgeShellBound C)
    (hW : IsWhiteNoise P W) (i : ℕ) (x x' : ℂ) :
    ‖deltaKernel i x - deltaKernel i x'‖ ^ 2 ≤
      2 * (28 + 4 * (13 + C)) / Real.pi * 2 ^ i * ‖x - x'‖ := by
  have hδ : (0 : ℝ) < (1 / 2) ^ i := by positivity
  have h1 := dzz_lemma25_wnField (P := P) hW hδ (measurableSet_bandSet i) (bandSet_subset i) x x'
  have h2 := dzz_lemma25_etaField hC0 hC hW hδ (measurableSet_bandSet i) (bandSet_subset i) x x'
  simp only [wnField, etaField] at h1 h2
  rw [variance_sqrtPi_sub hW] at h1 h2
  have hpi := Real.pi_pos
  have hδinv : ((1 / 2 : ℝ) ^ i)⁻¹ = 2 ^ i := by rw [one_div, inv_pow, inv_inv]
  rw [div_eq_mul_inv, hδinv] at h1 h2
  refine (sq_norm_sub_sub_le _ _ _ _).trans ?_
  rw [show 2 * (28 + 4 * (13 + C)) / Real.pi * 2 ^ i * ‖x - x'‖ =
    (2 * (28 * ‖x - x'‖ * 2 ^ i) + 2 * (4 * (13 + C) * ‖x - x'‖ * 2 ^ i)) / Real.pi by ring,
    le_div_iff₀ hpi]
  nlinarith

universe u

/-- **DZZ Lemma 2.7, the sum over scales** (l. 565–576), assuming `BridgeShellBound`: for
continuous versions `Y_i` of `Δ_i`,
`P(∃ v ∈ [0,1]², ∃ n, λ ≤ Σ_{i<n} |Y_i(v)|) ≤ C e^{−λ²/C}` with an absolute `C`. -/
theorem dzz_lemma27_sum {C₀ : ℝ} (hC0 : 0 ≤ C₀) (hC : BridgeShellBound C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Y : ℕ → ℂ → Ω → ℝ,
      (∀ i ω, Continuous fun x => Y i x ω) → (∀ i x, Y i x =ᵐ[P] dzzDelta W i x) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox 0 1, ∃ n : ℕ, lam ≤ ∑ i ∈ Finset.range n, |Y i v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  obtain ⟨K, ρ, hK, hρ0, hρ1, hvar⟩ := dzz_variance_truncation
  set K₁ : ℝ := 2 * (28 + 4 * (13 + C₀)) / Real.pi with hK₁
  have hpi := Real.pi_pos
  set K' : ℝ := max K (Real.pi * K₁) with hK'
  have hK'0 : 0 < K' := lt_max_of_lt_left hK
  obtain ⟨C, hCpos, hsum⟩ := dzz_sum_sup_tail (K := K') hK'0 hρ0 hρ1
  refine ⟨C, hCpos, fun {Ω} _ {P} {W} hW Y hYc hY lam hlam => ?_⟩
  have hYs : ∀ i x, Y i x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (deltaKernel i x) ω :=
    fun i x => (hY i x).trans (dzzDelta_ae_eq hW i x)
  refine hsum Ω P 0 1 one_pos le_rfl Y (fun i => ?_) (fun i v => ?_) (fun i ω => ?_)
    (fun i v _ => ?_) (fun i u _ v _ => ?_) lam hlam
  · exact (isGaussianProcess_sqrtPi hW (deltaKernel i)).congr fun x => (hYs i x).symm
  · rw [integral_congr_ae (hYs i v)]; exact integral_sqrtPi hW _
  · exact (hYc i ω).continuousOn
  · rw [variance_congr (hY i v)]
    exact (hvar hW i v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hae : (fun ω => (Y i v ω - Y i u ω) ^ 2) =ᵐ[P] fun ω =>
        (Real.sqrt Real.pi * W (deltaKernel i v) ω -
          Real.sqrt Real.pi * W (deltaKernel i u) ω) ^ 2 := by
      filter_upwards [hYs i u, hYs i v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
    have h := sq_norm_deltaKernel_sub_le hC0 hC hW i v u
    rw [norm_sub_rev v u] at h
    calc Real.pi * ‖deltaKernel i v - deltaKernel i u‖ ^ 2
        ≤ Real.pi * (K₁ * 2 ^ i * ‖u - v‖) := mul_le_mul_of_nonneg_left h hpi.le
      _ = Real.pi * K₁ * 2 ^ i * ‖u - v‖ := by ring
      _ ≤ K' * 2 ^ i * ‖u - v‖ := by
          gcongr
          exact le_max_right _ _

/-- Continuous versions of all `Δ_i` exist (assuming `BridgeShellBound`, which gives the
`1/2`-Hölder bound on the kernels). -/
theorem exists_continuous_dzzDelta {C₀ : ℝ} (hC0 : 0 ≤ C₀) (hC : BridgeShellBound C₀)
    (hW : IsWhiteNoise P W) :
    ∃ Y : ℕ → ℂ → Ω → ℝ, (∀ i ω, Continuous fun x => Y i x ω) ∧ (∀ i x, Measurable (Y i x)) ∧
      ∀ i x, Y i x =ᵐ[P] dzzDelta W i x := by
  have h : ∀ i : ℕ, ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧
      (∀ x, Measurable (Y x)) ∧ ∀ x, (fun ω => Y x ω) =ᵐ[P]
        fun ω => Real.sqrt Real.pi * W (deltaKernel i x) ω := fun i =>
    exists_continuous_modification_of_kernel_half hW (deltaKernel i) (by positivity)
      (sq_norm_deltaKernel_sub_le hC0 hC hW i) _
  choose Y hYc hYm hYe using h
  exact ⟨Y, hYc, hYm, fun i x => (hYe i x).trans (dzzDelta_ae_eq hW i x).symm⟩

end DZZ
end LQGMetric
