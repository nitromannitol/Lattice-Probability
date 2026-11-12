/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117D1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Var

/-!
# D117, packet P-DIH, part 1: the symmetries of `𝕍` and the kernel `p_𝕍`

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-translation-invariant) l. 2271 and "by symmetry"
l. 2555. In our model the exact form (DEC-117 §1, `DZZDihedralLaw`) rests on the invariance of the
killed heat kernel `p_𝕍(t; x, y)` (DZZ l. 467–469: `p_t(x,y) · q_𝕍(t; x, y)`) under the
symmetries of the square. Here, for an involutive symmetry `σ` of `𝕍` (`IsDihGen`; instances
`dzzRefl : x+iy ↦ (1−x)+iy` and `dzzSwap : x+iy ↦ y+ix`, which generate the group since
`dzzRot = dzzRefl ∘ dzzSwap`):

* `bridgeStay_of_signed`: `q_𝕍(t; σz, σw) = q_𝕍(t; z, w)` — the image of a planar Brownian
  bridge under a signed permutation of the coordinates is a planar Brownian bridge
  (`IsGaussianProcess.comp_right`, `.smul`, covariances), and `bridgeStay_eq_of_isPlanarBridge`;
* `killedHeat_dih`: `p_𝕍(t; σz, σw) = p_𝕍(t; z, w)`;
* `dihL2 σ`: the isometry `f ↦ f(·, σ ·)` of `L²(ℝ × ℂ)` (`Lp.compMeasurePreservingₗᵢ`), and
  `dihL2_wndKernelL2`: it maps the kernel `K_v` of `h̃` to `K_{σv}`.

Own elementary argument (the invariance is "clear" in DZZ); DV-D117-3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

/-- the reflection in the diagonal, `x + iy ↦ y + ix` -/
def dzzSwap (z : ℂ) : ℂ := ⟨z.im, z.re⟩

lemma dzzRot_eq (z : ℂ) : dzzRot z = dzzRefl (dzzSwap z) := by
  apply Complex.ext <;> simp [dzzRot, dzzRefl, dzzSwap] <;> ring

/-- an involutive symmetry of `𝕍` with the properties used for the law transfer -/
structure IsDihGen (σ : ℂ → ℂ) : Prop where
  invol : ∀ z, σ (σ z) = z
  norm_sub : ∀ z w, ‖σ z - σ w‖ = ‖z - w‖
  sq : ∀ z ∈ openSquare, σ z ∈ openSquare
  V : ∀ z ∈ dzzV, σ z ∈ dzzV
  mp : MeasurePreserving σ volume volume
  bridge : ∀ t : ℝ≥0, t ≠ 0 → ∀ z w,
    bridgeStay openSquare t (σ z) (σ w) = bridgeStay openSquare t z w
  rat : ∀ c : ℚ × ℚ, ∃ c' : ℚ × ℚ, ratPt c' = σ (ratPt c)

/-! ### Signed permutations of the coordinates preserve planar bridges -/

/-- the coordinate `b` of `z` (`false` ↦ real part, `true` ↦ imaginary part) -/
def coordB (b : Bool) (z : ℂ) : ℝ := if b then z.im else z.re

lemma isPlanarBridge_signed {Ω : Type*} {mΩ : MeasurableSpace Ω} {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ}
    {P : Measure Ω} (hX : IsPlanarBridge t X P) {π : Bool → Bool} (hπ : Function.Injective π)
    {ε : Bool → ℝ} (hε : ∀ b, ε b * ε b = 1) {L : ℂ → ℂ} (hLc : Continuous L)
    (hL : ∀ b z, coordB b (L z) = ε b * coordB (π b) z) :
    IsPlanarBridge t (fun s ω => L (X s ω)) P := by
  have e : coordProc (fun s ω => L (X s ω)) =
      fun p ω => ε p.1 • coordProc X (π p.1, p.2) ω := by
    funext p ω
    have := hL p.1 (X p.2 ω)
    simp only [coordB] at this
    simp only [coordProc, smul_eq_mul]
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hX.cont] with ω h using hLc.comp h
  · rw [e]
    exact (hX.gauss.comp_right (fun p : Bool × ℝ≥0 => (π p.1, p.2))).smul (fun p => ε p.1)
  · intro p
    rw [e]
    simp only [smul_eq_mul]
    rw [integral_const_mul, hX.mean, mul_zero]
  · intro p q hp hq
    rw [e]
    simp only [smul_eq_mul]
    rw [covariance_const_mul_left, covariance_const_mul_right, hX.cov (π p.1, p.2) (π q.1, q.2) hp hq]
    simp only [bridgeCov, hπ.eq_iff]
    split_ifs with h
    · rw [h, ← mul_assoc, hε, one_mul]
    · simp

/-- **bridge invariance**: for `σ = L + σ 0` with `L` a linear involution preserving planar
bridges, and `A` invariant under `σ`, `q_A(t; σz, σw) = q_A(t; z, w)` -/
lemma bridgeStay_of_lin {σ : ℂ → ℂ} (L : ℂ →ₗ[ℝ] ℂ) (hσ : ∀ z, σ z = L z + σ 0)
    (hLL : ∀ z, L (L z) = z) {A : Set ℂ} (hAo : IsOpen A) (hA : ∀ z, σ z ∈ A ↔ z ∈ A)
    {t : ℝ≥0} (ht : t ≠ 0) (hX : IsPlanarBridge t (fun s ω => L (stdBridge t s ω)) P2)
    (z w : ℂ) : bridgeStay A t (σ z) (σ w) = bridgeStay A t z w := by
  rw [← bridgeStay_eq_of_isPlanarBridge hAo ht hX z w, bridgeStay]
  congr 2
  ext ω
  simp only [bridgeEvent, mem_ofPred_eq]
  refine forall₂_congr fun s _ => ?_
  have : bridgePath t (σ z) (σ w) (stdBridge t) s ω =
      σ (bridgePath t z w (fun s ω => L (stdBridge t s ω)) s ω) := by
    simp only [bridgePath]
    rw [hσ (z + _ + _), hσ z, hσ w, map_add, map_add, hLL]
    have hr : ∀ (r : ℝ) (a : ℂ), L ((r : ℂ) * a) = (r : ℂ) * L a := fun r a => by
      rw [← Complex.real_smul, map_smul, Complex.real_smul]
    rw [hr, map_sub]
    ring
  rw [this, hA]

/-! ### The two generators -/

/-- the linear part of `dzzRefl`: `x + iy ↦ −x + iy` -/
def reflLin : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨-z.re, z.im⟩
  map_add' a b := by apply Complex.ext <;> simp <;> ring
  map_smul' r a := by apply Complex.ext <;> simp

/-- `dzzSwap` as a linear map -/
def swapLin : ℂ →ₗ[ℝ] ℂ where
  toFun := dzzSwap
  map_add' a b := by apply Complex.ext <;> simp [dzzSwap]
  map_smul' r a := by apply Complex.ext <;> simp [dzzSwap]

lemma continuous_reflLin : Continuous reflLin := LinearMap.continuous_of_finiteDimensional _

lemma continuous_dzzSwap : Continuous dzzSwap :=
  LinearMap.continuous_of_finiteDimensional swapLin

lemma mem_openSquare_dzzRefl (z : ℂ) : dzzRefl z ∈ openSquare ↔ z ∈ openSquare := by
  simp only [openSquare, dzzRefl, mem_ofPred_eq]
  constructor <;> rintro ⟨a, b, c, d⟩ <;> exact ⟨by linarith, by linarith, c, d⟩

lemma mem_openSquare_dzzSwap (z : ℂ) : dzzSwap z ∈ openSquare ↔ z ∈ openSquare := by
  simp only [openSquare, dzzSwap, mem_ofPred_eq]
  constructor <;> rintro ⟨a, b, c, d⟩ <;> exact ⟨c, d, a, b⟩

lemma dzzRefl_involutive (z : ℂ) : dzzRefl (dzzRefl z) = z := by
  apply Complex.ext <;> simp [dzzRefl]

lemma dzzSwap_involutive (z : ℂ) : dzzSwap (dzzSwap z) = z := by
  apply Complex.ext <;> simp [dzzSwap]

lemma measurePreserving_dzzRefl : MeasurePreserving dzzRefl volume volume := by
  have e : dzzRefl = Complex.measurableEquivRealProd.symm ∘
      (Prod.map (fun x : ℝ => 1 - x) id) ∘ Complex.measurableEquivRealProd := by
    funext z; apply Complex.ext <;> simp [dzzRefl, Complex.measurableEquivRealProd_symm_apply]
  rw [e]
  refine Complex.volume_preserving_equiv_real_prod.symm.comp ?_
  refine MeasurePreserving.comp ?_ Complex.volume_preserving_equiv_real_prod
  rw [Measure.volume_eq_prod]
  exact (volume.measurePreserving_sub_left 1).prod (MeasurePreserving.id volume)

lemma measurePreserving_dzzSwap : MeasurePreserving dzzSwap volume volume := by
  have e : dzzSwap = Complex.measurableEquivRealProd.symm ∘ Prod.swap ∘
      Complex.measurableEquivRealProd := by
    funext z; apply Complex.ext <;> simp [dzzSwap, Complex.measurableEquivRealProd_symm_apply]
  rw [e]
  refine Complex.volume_preserving_equiv_real_prod.symm.comp ?_
  refine MeasurePreserving.comp ?_ Complex.volume_preserving_equiv_real_prod
  rw [Measure.volume_eq_prod]
  exact Measure.measurePreserving_swap

lemma isDihGen_dzzRefl : IsDihGen dzzRefl where
  invol := dzzRefl_involutive
  norm_sub z w := by
    have : dzzRefl z - dzzRefl w = -(starRingEnd ℂ (z - w)) := by
      apply Complex.ext <;> simp [dzzRefl] <;> linarith
    rw [this, norm_neg, Complex.norm_conj]
  sq z hz := (mem_openSquare_dzzRefl z).2 hz
  V z hz := by
    obtain ⟨a, b, c, d⟩ := hz
    exact ⟨by simp [dzzRefl]; linarith, by simp [dzzRefl]; linarith, c, d⟩
  mp := measurePreserving_dzzRefl
  bridge t ht z w := by
    refine bridgeStay_of_lin reflLin (fun z => ?_) (fun z => ?_) isOpen_openSquare
      mem_openSquare_dzzRefl ht ?_ z w
    · apply Complex.ext <;> simp [dzzRefl, reflLin] <;> ring
    · apply Complex.ext <;> simp [reflLin]
    · refine isPlanarBridge_signed (isPlanarBridge_stdBridge ht) (π := id) Function.injective_id
        (ε := fun b => if b then 1 else -1) (fun b => by cases b <;> norm_num)
        continuous_reflLin fun b z => ?_
      cases b <;> simp [coordB, reflLin]
  rat c := ⟨(1 - c.1, c.2), by apply Complex.ext <;> simp [ratPt, dzzRefl]⟩

lemma isDihGen_dzzSwap : IsDihGen dzzSwap where
  invol := dzzSwap_involutive
  norm_sub z w := by
    have : dzzSwap z - dzzSwap w = Complex.I * starRingEnd ℂ (z - w) := by
      apply Complex.ext <;> simp [dzzSwap] <;> ring
    rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_conj]
  sq z hz := (mem_openSquare_dzzSwap z).2 hz
  V z hz := by
    obtain ⟨a, b, c, d⟩ := hz
    exact ⟨c, d, a, b⟩
  mp := measurePreserving_dzzSwap
  bridge t ht z w := by
    refine bridgeStay_of_lin swapLin (fun z => ?_) (fun z => dzzSwap_involutive z)
      isOpen_openSquare mem_openSquare_dzzSwap ht ?_ z w
    · apply Complex.ext <;> simp [dzzSwap, swapLin]
    · refine isPlanarBridge_signed (isPlanarBridge_stdBridge ht) (π := not)
        (fun a b h => by simpa using h) (ε := fun _ => 1) (fun b => by norm_num)
        continuous_dzzSwap fun b z => ?_
      cases b <;> simp [coordB, swapLin, dzzSwap]
  rat c := ⟨(c.2, c.1), by apply Complex.ext <;> simp [ratPt, dzzSwap]⟩

/-! ### The killed heat kernel and the white-noise isometry -/

variable {σ : ℂ → ℂ}

lemma IsDihGen.continuous (hσ : IsDihGen σ) : Continuous σ := by
  refine Metric.continuous_iff.2 fun z ε hε => ⟨ε, hε, fun w hw => ?_⟩
  rw [dist_eq_norm, hσ.norm_sub, ← dist_eq_norm]; exact hw

lemma IsDihGen.mem_dzzV (hσ : IsDihGen σ) (z : ℂ) : σ z ∈ dzzV ↔ z ∈ dzzV :=
  ⟨fun h => hσ.invol z ▸ hσ.V _ h, hσ.V z⟩

/-- **`p_𝕍` is invariant under the symmetries of `𝕍`** -/
lemma killedHeat_dih (hσ : IsDihGen σ) (t : ℝ≥0) (z w : ℂ) :
    killedHeat openSquare t (σ z) (σ w) = killedHeat openSquare t z w := by
  by_cases ht : t = 0
  · subst ht; simp [killedHeat, heatKernel]
  rw [killedHeat, killedHeat, hσ.bridge t ht, heatKernel, heatKernel, hσ.norm_sub]

/-- the space-time map `(s, w) ↦ (s, σ w)` -/
lemma measurePreserving_dihST (hσ : IsDihGen σ) :
    MeasurePreserving (fun p : ℝ × ℂ => (p.1, σ p.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id volume).prod hσ.mp

/-- the white-noise isometry `f ↦ f(·, σ ·)` -/
def dihL2 (hσ : IsDihGen σ) : WNSpace →ₗᵢ[ℝ] WNSpace :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun p : ℝ × ℂ => (p.1, σ p.2)) (measurePreserving_dihST hσ)

lemma wndKernel_comp_dih (hσ : IsDihGen σ) (I : Set ℝ) (v : ℂ) :
    wndKernel openSquare I v ∘ (fun p : ℝ × ℂ => (p.1, σ p.2)) = wndKernel openSquare I (σ v) := by
  funext p
  simp only [Function.comp_apply, wndKernel]
  congr 1
  funext s
  rw [← killedHeat_dih hσ _ (σ v), hσ.invol]

/-- **kernel covariance**: `dihL2 (K_v) = K_{σ v}` -/
theorem dihL2_wndKernelL2 (hσ : IsDihGen σ) (I : Set ℝ) (v : ℂ) :
    dihL2 hσ (wndKernelL2 openSquare I v) = wndKernelL2 openSquare I (σ v) := by
  have hφ := measurePreserving_dihST hσ
  by_cases hm : MemLp (wndKernel openSquare I v) 2 volume
  · have hm' : MemLp (wndKernel openSquare I (σ v)) 2 volume := by
      rw [← wndKernel_comp_dih hσ]; exact hm.comp_measurePreserving hφ
    simp only [wndKernelL2, dif_pos hm, dif_pos hm']
    have hdef : dihL2 hσ (hm.toLp _) = Lp.compMeasurePreserving _ hφ (hm.toLp _) := rfl
    rw [hdef]
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hm.toLp _) hφ,
      hφ.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp, hm'.coeFn_toLp] with p h1 h2 h3
    rw [h1, h3, ← wndKernel_comp_dih hσ]
    exact h2
  · have hm' : ¬ MemLp (wndKernel openSquare I (σ v)) 2 volume := by
      intro h
      apply hm
      have := h.comp_measurePreserving hφ
      rwa [wndKernel_comp_dih hσ, hσ.invol] at this
    simp only [wndKernelL2, dif_neg hm, dif_neg hm', map_zero]

/-- the transformed white noise `W ∘ dihL2` -/
def dihNoise {Ω : Type*} (hσ : IsDihGen σ) (W : WNSpace → Ω → ℝ) : WNSpace → Ω → ℝ :=
  fun f ω => W (dihL2 hσ f) ω

lemma isWhiteNoise_dihNoise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hσ : IsDihGen σ) :
    IsWhiteNoise P (dihNoise hσ W) :=
  DG.isWhiteNoise_comp hW (dihL2 hσ)

/-- **pathwise covariance of `h̃_δ`**: `h̃_δ[W ∘ dihL2](v) = h̃_δ[W](σ v)` -/
lemma tildeHInf_dihNoise {Ω : Type*} (hσ : IsDihGen σ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (v : ℂ)
    (ω : Ω) : tildeHInf (dihNoise hσ W) δ v ω = tildeHInf W δ (σ v) ω := by
  simp only [tildeHInf, DZZ.wnField, dihNoise, dihL2_wndKernelL2]

/-- the variance `Var h̃_ε(v)` is `σ`-invariant -/
lemma tildeVar_dih (hσ : IsDihGen σ) (ε : ℝ) (v : ℂ) : tildeVar ε (σ v) = tildeVar ε v := by
  simp only [tildeVar]
  rw [← dihL2_wndKernelL2 hσ, LinearIsometry.norm_map]

end DZZ
end LQGMetric
