/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.PsiField at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiAdd
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiSupTail

/-!
# Continuous `ψ_{m,n}` and the per-scale differences `D_k` (task P2-DDDFPSI; DDDF Prop 5)

DDDF (arXiv:1904.08021, `tightness.tex` l. 423–451): `ψ_{m,n} = ψ_{2^{-n}, 2^{-m}}` (continuous
version, as `phiMN`), and `D_k := φ_{k−1,k} − ψ_{k−1,k}`; here `deltaM m = D_{m+1}` is the
difference of the continuous versions `phiMN m (m+1) − psiMN m (m+1)`.

Facts proved for `deltaM m` (the inputs of DZZ Lemma 2.7, DZZ arXiv:1807.00422 l. 548–575):
it is a centred Gaussian process, continuous in `x`, with
`Var D_{m+1}(x) ≤ log 4 · e^{−r₀²(m+1)^{2ε₀}}` ((2.23)) and
`E(D(v) − D(u))² ≤ K₀ 2^{m+1} |u − v|` ((2.24) via Lemma 4), hence (`tail_iSup_deltaM`) for
`n_m = 2^{m+1}(m+1)⁴` boxes per side:
`P(sup_{[0,1]²} |D_{m+1}| ≥ C_F √K₀ (m+1)^{-2} + u) ≤ 2 n_m² e^{−u²/(2σ_m²)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Y` is a continuous (every `ω`) measurable (every `x`) modification of `ψ_{a,b}`. -/
structure IsPsiVersion (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ)
    (Y : ℂ → Ω → ℝ) : Prop where
  cont : ∀ ω, Continuous fun x => Y x ω
  meas : ∀ x, Measurable (Y x)
  ae_eq : ∀ x, (fun ω => Y x ω) =ᵐ[P] psi Q W a b x

open Classical in
/-- a chosen continuous version of `ψ_{a,b}` (junk `0` if there is none) -/
def psiVer (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ) : ℂ → Ω → ℝ :=
  if h : ∃ Y, IsPsiVersion Q W P a b Y then h.choose else 0

theorem isPsiVersion_psiVer {Q : PsiParams} {W : WNSpace → Ω → ℝ} {P : Measure Ω}
    (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IsPsiVersion Q W P a b (psiVer Q W P a b) := by
  have h : ∃ Y, IsPsiVersion Q W P a b Y := by
    obtain ⟨Y, h1, h2, h3⟩ := exists_continuous_modification_psi hW Q ha hab
    exact ⟨Y, h1, h2, h3⟩
  rw [psiVer, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- DDDF's `ψ_{m,n} = ψ_{2^{-n}, 2^{-m}}` (continuous version) -/
def psiMN (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (m n : ℕ) : ℂ → Ω → ℝ :=
  psiVer Q W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m)

theorem isPsiVersion_psiMN {Q : PsiParams} {W : WNSpace → Ω → ℝ} {P : Measure Ω}
    (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) :
    IsPsiVersion Q W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) (psiMN Q W P m n) :=
  isPsiVersion_psiVer hW (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)

/-- `D_{m+1} = φ_{m,m+1} − ψ_{m,m+1}` (continuous versions; DDDF l. 431) -/
def deltaM (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (m : ℕ) : ℂ → Ω → ℝ :=
  fun x ω => phiMN W P m (m + 1) x ω - psiMN Q W P m (m + 1) x ω

/-- `[0,1]² = R_{1,1}` as a Fernique box. -/
theorem rectAB_one_toSet : (rectAB 1 1).toSet = SupTail.ferniqueBox 0 1 := by
  simp [MarkedRect.toSet, rectAB, SupTail.ferniqueBox]

variable {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma integral_W (hW : IsWhiteNoise P W) (g : WNSpace) : ∫ ω, W g ω ∂P = 0 :=
  QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single g)

lemma integral_sq_W (hW : IsWhiteNoise P W) (g : WNSpace) :
    ∫ ω, (W g ω) ^ 2 ∂P = ‖g‖ ^ 2 := by
  have h := (hW.hasLaw_single g).variance_eq
  rw [variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity),
    variance_eq_integral (hW.measurable g).aemeasurable, integral_W hW g] at h
  simp only [sub_zero] at h
  exact h

/-- The kernel of `D_{m+1}`: `√π (k_x − k^{Tr}_x)` at scales `(2^{-(m+1)}, 2^{-m})`. -/
def deltaKernel (Q : PsiParams) (m : ℕ) (x : ℂ) : WNSpace :=
  Real.sqrt Real.pi • (phiKernelL2 ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x -
    Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x)

theorem deltaM_ae (hW : IsWhiteNoise P W) (Q : PsiParams) (m : ℕ) (x : ℂ) :
    (fun ω => deltaM Q W P m x ω) =ᵐ[P] W (deltaKernel Q m x) := by
  have h1 := (isPhiVersion_phiMN hW (Nat.le_succ m)).ae_eq x
  have h2 := (isPsiVersion_psiMN (Q := Q) hW (Nat.le_succ m)).ae_eq x
  have h3 := hW.ae_eq_zero_of_norm_eq_zero
    ![deltaKernel Q m x, phiKernelL2 ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x,
      Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x]
    ![1, -Real.sqrt Real.pi, Real.sqrt Real.pi] (by
      simp [Fin.sum_univ_three, deltaKernel, smul_sub]; abel)
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Pi.zero_apply] at e3
  simp only [deltaM, phi, psi] at e1 e2 ⊢
  rw [e1, e2]
  simp only [Matrix.tail_cons, Matrix.head_cons, one_mul] at e3
  linarith

theorem isGaussianProcess_deltaM (hW : IsWhiteNoise P W) (Q : PsiParams) (m : ℕ) :
    IsGaussianProcess (deltaM Q W P m) P :=
  (hW.isGaussianProcess_comp (deltaKernel Q m)).congr fun x => (deltaM_ae hW Q m x).symm

theorem integral_deltaM (hW : IsWhiteNoise P W) (Q : PsiParams) (m : ℕ) (x : ℂ) :
    ∫ ω, deltaM Q W P m x ω ∂P = 0 := by
  rw [integral_congr_ae (deltaM_ae hW Q m x)]; exact integral_W hW _

theorem continuous_deltaM (hW : IsWhiteNoise P W) (Q : PsiParams) (m : ℕ) (ω : Ω) :
    Continuous fun x => deltaM Q W P m x ω :=
  ((isPhiVersion_phiMN hW (Nat.le_succ m)).cont ω).sub
    ((isPsiVersion_psiMN (Q := Q) hW (Nat.le_succ m)).cont ω)

/-- (2.23) for the continuous version. -/
theorem variance_deltaM_le (hW : IsWhiteNoise P W) (Q : PsiParams) (m : ℕ) (x : ℂ) :
    Var[deltaM Q W P m x; P] ≤
      Real.log 4 * Real.exp (-(Q.r₀ ^ 2 * ((m : ℝ) + 1) ^ (2 * Q.ε₀))) := by
  have h1 := (isPhiVersion_phiMN hW (Nat.le_succ m)).ae_eq x
  have h2 := (isPsiVersion_psiMN (Q := Q) hW (Nat.le_succ m)).ae_eq x
  have h : deltaM Q W P m x =ᵐ[P] fun ω =>
      phi W ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x ω -
        psi Q W ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x ω := by
    filter_upwards [h1, h2] with ω e1 e2
    simp only [deltaM]; rw [e1, e2]
  rw [variance_congr h]
  exact variance_phi_sub_psi_scale_le hW Q m x

/-- (2.24) for `D_{m+1}`: `E(D(v) − D(u))² ≤ K₀ 2^{m+1} |u − v|` with `K₀ = 2(√2 + |C_ψ|)`. -/
theorem exists_incr_deltaM_le (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ m : ℕ, ∀ u v : ℂ,
      ∫ ω, (deltaM Q W P m v ω - deltaM Q W P m u ω) ^ 2 ∂P ≤ K₀ * 2 ^ (m + 1) * ‖u - v‖ := by
  obtain ⟨C, hC⟩ := exists_variance_psi_sub_le hW Q
  refine ⟨2 * (Real.sqrt 2 + |C|), by positivity, fun m u v => ?_⟩
  set a : ℝ := (2 : ℝ)⁻¹ ^ (m + 1)
  set b : ℝ := (2 : ℝ)⁻¹ ^ m
  have ha : 0 < a := by positivity
  have hab : a ≤ b := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
  have hb1 : b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha1 : a ≤ 1 := hab.trans hb1
  -- reduce to the kernels
  have hae : (fun ω => deltaM Q W P m v ω - deltaM Q W P m u ω) =ᵐ[P]
      W (deltaKernel Q m v - deltaKernel Q m u) := by
    have h3 := hW.ae_eq_zero_of_norm_eq_zero
      ![deltaKernel Q m v - deltaKernel Q m u, deltaKernel Q m v, deltaKernel Q m u]
      ![1, -1, 1] (by simp [Fin.sum_univ_three]; abel)
    filter_upwards [deltaM_ae hW Q m v, deltaM_ae hW Q m u, h3] with ω e1 e2 e3
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Pi.zero_apply, Matrix.tail_cons, Matrix.head_cons] at e3
    rw [e1, e2]; linarith
  have hae2 : (fun ω => (deltaM Q W P m v ω - deltaM Q W P m u ω) ^ 2) =ᵐ[P]
      fun ω => (W (deltaKernel Q m v - deltaKernel Q m u) ω) ^ 2 := by
    filter_upwards [hae] with ω h
    rw [h]
  rw [integral_congr_ae hae2, integral_sq_W hW]
  -- `‖F v − F u‖² ≤ 2π‖φ-incr‖² + 2π‖ψ-incr‖²`
  set f := phiKernelL2 a b v - phiKernelL2 a b u
  set g := Q.psiKernelL2 a b v - Q.psiKernelL2 a b u
  have hFe : deltaKernel Q m v - deltaKernel Q m u = Real.sqrt Real.pi • (f - g) := by
    simp only [deltaKernel, f, g, a, b, ← smul_sub]; congr 1; abel
  have hφ : Real.pi * ‖f‖ ^ 2 ≤ Real.sqrt 2 * ‖v - u‖ / a := by
    have e : Real.pi * ‖f‖ ^ 2 = Var[fun ω => phi W a b v ω - phi W a b u ω; P] :=
      (variance_sqrtPi_sub hW _ _).symm
    rw [e]
    exact (variance_phi_sub_mono hW ha hab hb1 v u).trans (variance_phi_sub_le hW ha ha1 v u)
  have hψ : Real.pi * ‖g‖ ^ 2 ≤ |C| * ‖v - u‖ / a := by
    have e : Real.pi * ‖g‖ ^ 2 = Var[fun ω => psi Q W a b v ω - psi Q W a b u ω; P] :=
      (variance_sqrtPi_sub hW _ _).symm
    rw [e]
    refine (variance_psi_sub_mono hW Q ha hab hb1 v u).trans ((hC a ha ha1 v u).trans ?_)
    gcongr; exact le_abs_self C
  rw [hFe, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt Real.pi_pos.le]
  have htri : ‖f - g‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 2 * ‖g‖ ^ 2 := by
    have := norm_sub_le f g
    nlinarith [norm_nonneg f, norm_nonneg g, norm_nonneg (f - g), sq_nonneg (‖f‖ - ‖g‖)]
  have hainv : a⁻¹ = 2 ^ (m + 1) := by simp only [a, inv_pow, inv_inv]
  have hvu : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
  calc Real.pi * ‖f - g‖ ^ 2 ≤ 2 * (Real.pi * ‖f‖ ^ 2) + 2 * (Real.pi * ‖g‖ ^ 2) := by
        nlinarith [Real.pi_pos]
    _ ≤ 2 * (Real.sqrt 2 * ‖v - u‖ / a) + 2 * (|C| * ‖v - u‖ / a) := by linarith
    _ = 2 * (Real.sqrt 2 + |C|) * 2 ^ (m + 1) * ‖u - v‖ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, hainv, hvu]; ring


/-- `σ_m = (log 4 · e^{−r₀²(m+1)^{2ε₀}})^{1/2}`, the standard deviation bound of `D_{m+1}`. -/
def sigmaM (Q : PsiParams) (m : ℕ) : ℝ :=
  Real.sqrt (Real.log 4 * Real.exp (-(Q.r₀ ^ 2 * ((m : ℝ) + 1) ^ (2 * Q.ε₀))))

lemma sigmaM_pos (Q : PsiParams) (m : ℕ) : 0 < sigmaM Q m := by
  unfold sigmaM
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

lemma sigmaM_sq (Q : PsiParams) (m : ℕ) :
    sigmaM Q m ^ 2 = Real.log 4 * Real.exp (-(Q.r₀ ^ 2 * ((m : ℝ) + 1) ^ (2 * Q.ε₀))) := by
  unfold sigmaM
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  exact Real.sq_sqrt (by positivity)

/-- The number of boxes per side at scale `m`: `n_m = 2^{m+1}(m+1)⁴` (DZZ's mesh
`2^{-i} i^{-4}`, l. 562). -/
def boxN (m : ℕ) : ℕ := 2 ^ (m + 1) * (m + 1) ^ 4

/-- **Per-scale sup tail** (DZZ (2.40)–(2.41) adapted, DDDF l. 431–437): on the square
`[0,R]²`, `P(sup |D_{m+1}| ≥ C_F √(K₀R) (m+1)^{-2} + u) ≤ 2 n_m² e^{−u²/(2σ_m²)}`. -/
theorem exists_tail_iSup_deltaM (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ R : ℝ, 0 < R → ∀ m : ℕ, ∀ u : ℝ, 0 ≤ u →
      P {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (K₀ * R) / ((m : ℝ) + 1) ^ 2 + u) ≤
          ⨆ x ∈ SupTail.ferniqueBox 0 R, ENNReal.ofReal |deltaM Q W P m x ω|} ≤
        ENNReal.ofReal (2 * (boxN m : ℝ) ^ 2 * Real.exp (-u ^ 2 / (2 * sigmaM Q m ^ 2))) := by
  obtain ⟨K₀, hK₀, hinc⟩ := exists_incr_deltaM_le hW Q
  refine ⟨K₀, hK₀, fun R hR m u hu => ?_⟩
  have hn : 0 < boxN m := by unfold boxN; positivity
  have h := SupTail.tail_iSup_abs_square (P := P) hn hR (isGaussianProcess_deltaM hW Q m)
    (integral_deltaM hW Q m) (continuous_deltaM hW Q m) (A := K₀ * 2 ^ (m + 1))
    (by positivity) (hinc m) (sigmaM_pos Q m)
    (fun v => (sigmaM_sq Q m).symm ▸ variance_deltaM_le hW Q m v) hu
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have e : Real.sqrt (K₀ * 2 ^ (m + 1) * (R / (boxN m : ℝ))) =
      Real.sqrt (K₀ * R) / ((m : ℝ) + 1) ^ 2 := by
    have : K₀ * 2 ^ (m + 1) * (R / (boxN m : ℝ)) = K₀ * R / (((m : ℝ) + 1) ^ 2) ^ 2 := by
      simp only [boxN]; push_cast; field_simp
    rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  rw [e, ← mul_div_assoc] at h
  exact h

end DDDF
end LQGMetric
