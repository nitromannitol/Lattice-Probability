/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR3b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR3a

/-!
# DGo (3.9) on every square (task P2-HEAT3, packet R3, part 2)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, (3.9) (DGo:702–704):
`Var(ĥ^𝒰_δ(u) − ĥ^𝒰_δ(w)) ≤ A |u − w| / δ`, here for `𝒰 = D = (a, a+L)²` with `ĥ^D_δ(v) =
√π W(dirCircKernel a L δ v)` (`π ‖K_u − K_w‖²` is that variance).

* Brownian scaling of the image-series kernel: `sqDirKernel a L (L² s) (T x) (T y) =
  L⁻² sqDirKernel 0 1 s x y` for `T z = a(1+i) + L z` (`sqDirKernel_affT`), hence
  `⟪K^{a,L}_{Lδ, T u}, K^{a,L}_{Lδ, T w}⟫ = ⟪K^{0,1}_{δ,u}, K^{0,1}_{δ,w}⟫` (`inner_dirCircKernel_affT`,
  change of variables `s = L² s'` in `inner_dirCircKernel`);
* **`dgo_incr_bound`**: (3.9) for `B̄(u, ε), B̄(w, ε) ⊆ D`, `δ < ε/4`, from the unit-square bound
  `pi_norm_sq_dirCircKernel_sub_le_unit` (HeatDirR3a) on `K = sqIn(ε/(2L))`.

The scaling is an own elementary computation (DGo use (3.9) for a general domain, citing
Hu–Miller–Peres Prop. 2.1); proposed DEVIATIONS entry HEAT3-1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq

/-- the affine map `z ↦ a(1+i) + L z` of `(0,1)²` onto `(a, a+L)²` -/
def affT (a L : ℝ) (z : ℂ) : ℂ := ((a : ℂ) + a * Complex.I) + (L : ℂ) * z

lemma affT_re (a L : ℝ) (z : ℂ) : (affT a L z).re = a + L * z.re := by simp [affT]

lemma affT_im (a L : ℝ) (z : ℂ) : (affT a L z).im = a + L * z.im := by simp [affT]

lemma dist_affT {a L : ℝ} (hL : 0 < L) (z z' : ℂ) :
    dist (affT a L z) (affT a L z') = L * dist z z' := by
  rw [dist_eq_norm, dist_eq_norm, show affT a L z - affT a L z' = (L : ℂ) * (z - z') by
    unfold affT; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL.le]

lemma exists_affT_eq {a L : ℝ} (hL : 0 < L) (x : ℂ) : ∃ z, affT a L z = x :=
  ⟨(x - ((a : ℂ) + a * Complex.I)) / L, by
    have : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
    unfold affT; field_simp; ring⟩

lemma affT_mem_sqOpen_iff {a L : ℝ} (hL : 0 < L) (z : ℂ) :
    affT a L z ∈ sqOpen a L ↔ z ∈ sqOpen 0 1 := by
  simp only [sqOpen, mem_ofPred_eq, affT_re, affT_im, zero_add]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma closedBall_affT_subset_iff {a L : ℝ} (hL : 0 < L) (u : ℂ) (δ : ℝ) :
    closedBall (affT a L u) (L * δ) ⊆ sqOpen a L ↔ closedBall u δ ⊆ sqOpen 0 1 := by
  constructor
  · intro h z hz
    rw [← affT_mem_sqOpen_iff hL]
    refine h ?_
    rw [mem_closedBall, dist_affT hL]
    exact mul_le_mul_of_nonneg_left hz hL.le
  · intro h x hx
    obtain ⟨z, rfl⟩ := exists_affT_eq (a := a) hL x
    rw [affT_mem_sqOpen_iff hL]
    refine h ?_
    rw [mem_closedBall, dist_affT hL] at hx
    exact le_of_mul_le_mul_left hx hL

lemma gauss1_scale {L : ℝ} (hL : 0 < L) (s x : ℝ) :
    gauss1 (L ^ 2 * s) (L * x) = L⁻¹ * gauss1 s x := by
  unfold gauss1
  rw [show 2 * π * (L ^ 2 * s) = L ^ 2 * (2 * π * s) by ring,
    Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le, mul_inv,
    show -(L * x) ^ 2 / (2 * (L ^ 2 * s)) = (L ^ 2 * (-x ^ 2)) / (L ^ 2 * (2 * s)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hL.ne')]
  ring

lemma intervalDirKernel_scale {a L : ℝ} (hL : 0 < L) (s u v : ℝ) :
    intervalDirKernel a L (L ^ 2 * s) (a + L * u) (a + L * v) =
      L⁻¹ * intervalDirKernel 0 1 s u v := by
  unfold intervalDirKernel
  rw [← tsum_mul_left]
  congr 1; funext n
  rw [show a + L * u - (a + L * v) + 2 * n * L = L * (u - v + 2 * n * 1) by ring,
    show a + L * u + (a + L * v) - 2 * a + 2 * n * L = L * (u + v - 2 * 0 + 2 * n * 1) by ring,
    gauss1_scale hL, gauss1_scale hL]
  ring

/-- **Brownian scaling** of the Dirichlet heat kernel of the square -/
lemma sqDirKernel_affT {a L : ℝ} (hL : 0 < L) (s : ℝ) (x y : ℂ) :
    sqDirKernel a L (L ^ 2 * s) (affT a L x) (affT a L y) = (L ^ 2)⁻¹ * sqDirKernel 0 1 s x y := by
  unfold sqDirKernel
  rw [affT_re, affT_re, affT_im, affT_im, intervalDirKernel_scale hL, intervalDirKernel_scale hL]
  ring

lemma circleMap_affT (a L : ℝ) (v : ℂ) (δ θ : ℝ) :
    circleMap (affT a L v) (L * δ) θ = affT a L (circleMap v δ θ) := by
  unfold circleMap affT; push_cast; ring

lemma circFn_affT {a L : ℝ} (hL : 0 < L) (δ : ℝ) (v : ℂ) (r : ℝ) (y : ℂ) :
    circFn a L (L * δ) (affT a L v) (L ^ 2 * r) (affT a L y) =
      (L ^ 2)⁻¹ * circFn 0 1 δ v r y := by
  unfold circFn
  simp_rw [circleMap_affT, sqDirKernel_affT hL]
  rw [integral_const_mul]; ring

lemma circPair_affT {a L : ℝ} (hL : 0 < L) (δ : ℝ) (v v' : ℂ) (s : ℝ) :
    circPair a L (L * δ) (affT a L v) (affT a L v') (L ^ 2 * s) =
      (L ^ 2)⁻¹ * circPair 0 1 δ v v' s := by
  unfold circPair
  simp_rw [circleMap_affT, circFn_affT hL]
  rw [integral_const_mul]; ring

lemma integral_circPair_affT {a L : ℝ} (hL : 0 < L) (δ : ℝ) (v v' : ℂ) :
    ∫ s in Ioi 0, circPair a L (L * δ) (affT a L v) (affT a L v') s =
      ∫ s in Ioi 0, circPair 0 1 δ v v' s := by
  have h := integral_comp_mul_left_Ioi
    (fun s => circPair a L (L * δ) (affT a L v) (affT a L v') s) 0 (pow_pos hL 2)
  simp only [mul_zero, circPair_affT hL, integral_const_mul, smul_eq_mul] at h
  have hL2 : (L ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hL.ne')
  exact (mul_left_cancel₀ hL2 h).symm

theorem inner_dirCircKernel_affT {a L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {u w : ℂ}
    (hu : closedBall u δ ⊆ sqOpen 0 1) (hw : closedBall w δ ⊆ sqOpen 0 1) :
    ⟪dirCircKernel a L (L * δ) (affT a L u), dirCircKernel a L (L * δ) (affT a L w)⟫ =
      ⟪dirCircKernel 0 1 δ u, dirCircKernel 0 1 δ w⟫ := by
  rw [(inner_dirCircKernel hL (mul_pos hL hδ) ((closedBall_affT_subset_iff hL u δ).2 hu)
      ((closedBall_affT_subset_iff hL w δ).2 hw)).2,
    (inner_dirCircKernel one_pos hδ hu hw).2, integral_circPair_affT hL]

theorem norm_dirCircKernel_sub_affT {a L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {u w : ℂ}
    (hu : closedBall u δ ⊆ sqOpen 0 1) (hw : closedBall w δ ⊆ sqOpen 0 1) :
    ‖dirCircKernel a L (L * δ) (affT a L u) - dirCircKernel a L (L * δ) (affT a L w)‖ ^ 2 =
      ‖dirCircKernel 0 1 δ u - dirCircKernel 0 1 δ w‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_dirCircKernel_affT hL hδ hu hu, inner_dirCircKernel_affT hL hδ hu hw,
    inner_dirCircKernel_affT hL hδ hw hw]

/-- a ball of radius `ε` in `𝕍` shrunk to radius `δ ≤ ε/2` lies in `sqIn (ε/2)` -/
lemma closedBall_subset_sqIn_of {u : ℂ} {ε δ : ℝ} (hε : 0 < ε) (hB : closedBall u ε ⊆ openSquare)
    (hδ : δ ≤ ε / 2) : closedBall u δ ⊆ sqIn (ε / 2) := by
  have h1 := hB (show u + ε ∈ closedBall u ε by simp [abs_of_pos hε])
  have h2 := hB (show u - ε ∈ closedBall u ε by simp [abs_of_pos hε])
  have h3 := hB (show u + ε * Complex.I ∈ closedBall u ε by simp [abs_of_pos hε])
  have h4 := hB (show u - ε * Complex.I ∈ closedBall u ε by simp [abs_of_pos hε])
  simp only [openSquare, mem_ofPred_eq, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] at h1 h2 h3 h4
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre : |(z - u).re| ≤ δ := (Complex.abs_re_le_norm _).trans hz
  have him : |(z - u).im| ≤ δ := (Complex.abs_im_le_norm _).trans hz
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **DGo (3.9)** (DGo:702–704) on the square `D = (a, a+L)²`, for all `u, w`:
`π ‖K^D_{δ,u} − K^D_{δ,w}‖² = Var(ĥ^D_δ(u) − ĥ^D_δ(w)) ≤ A ‖u − w‖ / δ` -/
theorem dgo_incr_bound_all (a L : ℝ) : ∀ ε > 0, ∃ A : ℝ, 0 < A ∧ ∀ δ ∈ Ioo 0 (ε / 4),
    ∀ u w : ℂ, closedBall u ε ⊆ sqOpen a L → closedBall w ε ⊆ sqOpen a L →
      Real.pi * ‖dirCircKernel a L δ u - dirCircKernel a L δ w‖ ^ 2 ≤ A * ‖u - w‖ / δ := by
  intro ε hε
  by_cases hL : 0 < L
  swap
  · refine ⟨1, one_pos, fun δ _ u w hu _ => ?_⟩
    have := hu (mem_closedBall_self hε.le)
    simp only [sqOpen, mem_ofPred_eq] at this
    exact absurd (by linarith [this.1, this.2.1] : 0 < L) hL
  set ε' := ε / L with hε'
  have hε'0 : 0 < ε' := div_pos hε hL
  obtain ⟨C, hC0, hC⟩ := exists_hS_lip (K := sqIn (ε' / 2))
    (sqIn_subset_openSquare (by positivity)) (DGMC.convex_sqIn _) (isCompact_sqIn (by positivity))
  refine ⟨2 + C * ε' / 2, by positivity, fun δ hδ u w hu hw => ?_⟩
  obtain ⟨u', rfl⟩ := exists_affT_eq (a := a) hL u
  obtain ⟨w', rfl⟩ := exists_affT_eq (a := a) hL w
  have hεL : ε = L * ε' := by rw [hε']; field_simp
  obtain ⟨δ', rfl⟩ : ∃ δ', δ = L * δ' := ⟨δ / L, by field_simp⟩
  have hδ'0 : 0 < δ' := pos_of_mul_pos_right hδ.1 hL.le
  have hδ'4 : δ' < ε' / 4 := by
    have := hδ.2; rw [hεL] at this
    nlinarith
  rw [hεL, closedBall_affT_subset_iff hL, sqOpen_zero_one] at hu hw
  have hu' := closedBall_subset_sqIn_of (δ := δ') hε'0 hu (by linarith)
  have hw' := closedBall_subset_sqIn_of (δ := δ') hε'0 hw (by linarith)
  rw [norm_dirCircKernel_sub_affT hL hδ'0 (sqOpen_zero_one ▸ (hu'.trans
      (sqIn_subset_openSquare (by positivity))))
      (sqOpen_zero_one ▸ (hw'.trans (sqIn_subset_openSquare (by positivity)))),
    show ‖affT a L u' - affT a L w'‖ = L * ‖u' - w'‖ by
      rw [← dist_eq_norm, dist_affT hL, dist_eq_norm]]
  refine (pi_norm_sq_dirCircKernel_sub_le_unit (sqIn_subset_openSquare (by positivity)) hC hδ'0
    hu' hw').trans ?_
  rw [show (2 + C * ε' / 2) * (L * ‖u' - w'‖) / (L * δ') = (2 + C * ε' / 2) / δ' * ‖u' - w'‖ by
    field_simp]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [show (2 + C * ε' / 2) / δ' = 2 / δ' + C * (ε' / (2 * δ')) by field_simp]
  have : 2 ≤ ε' / (2 * δ') := by rw [le_div_iff₀ (by positivity)]; linarith
  nlinarith
