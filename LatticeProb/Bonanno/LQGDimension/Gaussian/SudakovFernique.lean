/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.SudakovFernique at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.SteinIBP
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Sudakov–Fernique inequality with drift

We prove `Blueprint.SudakovFernique` by Chatterjee's interpolation argument.

1. Both families are placed in the single space `H = WithLp 2 (E × E')`, as `u i = (v i, 0)` and
   `u' i = (0, w i)`; by `GramBridge` this does not change the expected maxima.
2. For `θ ∈ [0, π/2]` put `U θ i = cos θ • u i + sin θ • u' i` and
   `φ(θ) = E[F_β((⟪U θ i, x⟫ + b i)_i)]` where `F_β z = β⁻¹ log ∑_{i ∈ F} exp (β z_i)` is the
   smooth maximum (`smoothMax`).
3. Differentiating under the integral and applying Gaussian integration by parts
   (`SteinIBP.integral_inner_mul_stdGaussian`) to the softmax weights `p_i`, one gets
   `φ'(θ) = β cos θ sin θ · ½ E ∑_{i,j} p_i p_j (‖u' i - u' j‖² - ‖u i - u j‖²) ≥ 0`
   (`integral_interpDeriv_nonneg`), so `φ(0) ≤ φ(π/2)`.
4. Since `max ≤ F_β ≤ max + log |F| / β`, letting `β → ∞` gives the inequality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

namespace SudakovFernique

/-! ### Smooth maximum and softmax -/

section SmoothMax

variable {ι : Type*}

/-- The log-sum-exp smooth maximum `β⁻¹ log ∑_{i ∈ F} exp (β z_i)`. -/
def smoothMax (F : Finset ι) (β : ℝ) (z : ι → ℝ) : ℝ :=
  β⁻¹ * Real.log (∑ i ∈ F, Real.exp (β * z i))

/-- The softmax weights `exp (β z_i) / ∑_{j ∈ F} exp (β z_j)`. -/
def softmax (F : Finset ι) (β : ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (β * z i) / ∑ j ∈ F, Real.exp (β * z j)

lemma sumExp_pos {F : Finset ι} (hF : F.Nonempty) (β : ℝ) (z : ι → ℝ) :
    0 < ∑ i ∈ F, Real.exp (β * z i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hF

lemma exp_le_sumExp {F : Finset ι} (β : ℝ) (z : ι → ℝ) {i : ι} (hi : i ∈ F) :
    Real.exp (β * z i) ≤ ∑ j ∈ F, Real.exp (β * z j) :=
  Finset.single_le_sum (f := fun j => Real.exp (β * z j)) (fun _ _ => (Real.exp_pos _).le) hi

lemma softmax_nonneg (F : Finset ι) (β : ℝ) (z : ι → ℝ) (i : ι) : 0 ≤ softmax F β z i :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

lemma softmax_le_one {F : Finset ι} (β : ℝ) (z : ι → ℝ) {i : ι} (hi : i ∈ F) :
    softmax F β z i ≤ 1 := by
  rw [softmax, div_le_one (sumExp_pos ⟨i, hi⟩ β z)]
  exact exp_le_sumExp β z hi

lemma abs_softmax_le_one {F : Finset ι} (β : ℝ) (z : ι → ℝ) {i : ι} (hi : i ∈ F) :
    |softmax F β z i| ≤ 1 := by
  rw [abs_of_nonneg (softmax_nonneg F β z i)]
  exact softmax_le_one β z hi

lemma sum_softmax {F : Finset ι} (hF : F.Nonempty) (β : ℝ) (z : ι → ℝ) :
    ∑ i ∈ F, softmax F β z i = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (sumExp_pos hF β z).ne'

lemma le_smoothMax {F : Finset ι} {β : ℝ} (hβ : 0 < β) (z : ι → ℝ) {i : ι} (hi : i ∈ F) :
    z i ≤ smoothMax F β z := by
  rw [smoothMax, le_inv_mul_iff₀ hβ]
  calc β * z i = Real.log (Real.exp (β * z i)) := (Real.log_exp _).symm
    _ ≤ Real.log (∑ j ∈ F, Real.exp (β * z j)) :=
      Real.log_le_log (Real.exp_pos _) (exp_le_sumExp β z hi)

lemma smoothMax_le {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β) (z : ι → ℝ) {M : ℝ}
    (hM : ∀ i ∈ F, z i ≤ M) : smoothMax F β z ≤ M + Real.log F.card / β := by
  have hsum : ∑ i ∈ F, Real.exp (β * z i) ≤ F.card * Real.exp (β * M) := by
    calc ∑ i ∈ F, Real.exp (β * z i) ≤ ∑ _i ∈ F, Real.exp (β * M) :=
          Finset.sum_le_sum fun i hi =>
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hM i hi) hβ.le)
      _ = F.card * Real.exp (β * M) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hlog : Real.log (∑ i ∈ F, Real.exp (β * z i)) ≤ Real.log F.card + β * M := by
    calc Real.log (∑ i ∈ F, Real.exp (β * z i)) ≤ Real.log (F.card * Real.exp (β * M)) :=
          Real.log_le_log (sumExp_pos hF β z) hsum
      _ = Real.log F.card + β * M := by
          rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [smoothMax]
  calc β⁻¹ * Real.log (∑ i ∈ F, Real.exp (β * z i)) ≤ β⁻¹ * (Real.log F.card + β * M) :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hβ.le)
    _ = (β⁻¹ * β) * M + β⁻¹ * Real.log F.card := by ring
    _ = M + Real.log F.card / β := by
        rw [inv_mul_cancel₀ hβ.ne', one_mul, div_eq_inv_mul, add_comm]

lemma iSup_le_smoothMax {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β) (z : ι → ℝ) :
    (⨆ i : F, z i) ≤ smoothMax F β z := by
  have : Nonempty F := hF.to_subtype
  exact ciSup_le fun i => le_smoothMax hβ z i.2

lemma smoothMax_le_iSup {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β) (z : ι → ℝ) :
    smoothMax F β z ≤ (⨆ i : F, z i) + Real.log F.card / β :=
  smoothMax_le hF hβ z fun i hi =>
    le_ciSup (f := fun j : F => z j) (Set.finite_range _).bddAbove ⟨i, hi⟩

lemma abs_smoothMax_le {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β) (z : ι → ℝ) :
    |smoothMax F β z| ≤ ∑ i ∈ F, |z i| + Real.log F.card / β := by
  obtain ⟨i₀, hi₀⟩ := hF
  have hcard : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.card_pos.2 ⟨i₀, hi₀⟩
  have hL : 0 ≤ Real.log F.card / β := div_nonneg (Real.log_nonneg hcard) hβ.le
  have hsingle : ∀ i ∈ F, |z i| ≤ ∑ j ∈ F, |z j| := fun i hi =>
    Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg _) hi
  rw [abs_le]
  constructor
  · have h1 := le_smoothMax (F := F) hβ z hi₀
    have h2 := neg_abs_le (z i₀)
    have h3 := hsingle i₀ hi₀
    linarith
  · have := smoothMax_le ⟨i₀, hi₀⟩ hβ z (M := ∑ j ∈ F, |z j|) fun i hi =>
      (le_abs_self _).trans (hsingle i hi)
    linarith

lemma hasDerivAt_sumExp (F : Finset ι) (β : ℝ) {γ : ℝ → ι → ℝ} {γ' : ι → ℝ} {t : ℝ}
    (hγ : ∀ i, HasDerivAt (fun s => γ s i) (γ' i) t) :
    HasDerivAt (fun s => ∑ i ∈ F, Real.exp (β * γ s i))
      (∑ i ∈ F, Real.exp (β * γ t i) * (β * γ' i)) t :=
  HasDerivAt.fun_sum fun i _ => ((hγ i).const_mul β).exp

private lemma inv_mul_aux {β : ℝ} (hβ : β ≠ 0) (e g S : ℝ) :
    β⁻¹ * (e * (β * g) / S) = e / S * g := by
  calc β⁻¹ * (e * (β * g) / S) = (β⁻¹ * β) * (e / S * g) := by ring
    _ = e / S * g := by rw [inv_mul_cancel₀ hβ, one_mul]

/-- Derivative of the smooth maximum along a differentiable curve: `∂_i F_β = p_i`. -/
theorem hasDerivAt_smoothMax {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : β ≠ 0)
    {γ : ℝ → ι → ℝ} {γ' : ι → ℝ} {t : ℝ} (hγ : ∀ i, HasDerivAt (fun s => γ s i) (γ' i) t) :
    HasDerivAt (fun s => smoothMax F β (γ s)) (∑ i ∈ F, softmax F β (γ t) i * γ' i) t := by
  have h := ((hasDerivAt_sumExp F β hγ).log (sumExp_pos hF β (γ t)).ne').const_mul β⁻¹
  refine h.congr_deriv ?_
  rw [Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => inv_mul_aux hβ _ _ _

/-- Derivative of the softmax weights along a differentiable curve:
`∂_j p_i = β (p_i δ_ij - p_i p_j)`. -/
theorem hasDerivAt_softmax {F : Finset ι} (hF : F.Nonempty) (β : ℝ) {γ : ℝ → ι → ℝ}
    {γ' : ι → ℝ} {t : ℝ} (hγ : ∀ i, HasDerivAt (fun s => γ s i) (γ' i) t) (i : ι) :
    HasDerivAt (fun s => softmax F β (γ s) i)
      (β * softmax F β (γ t) i * (γ' i - ∑ j ∈ F, softmax F β (γ t) j * γ' j)) t := by
  have hS := (sumExp_pos hF β (γ t)).ne'
  have h := (((hγ i).const_mul β).exp).div (hasDerivAt_sumExp F β hγ) hS
  refine h.congr_deriv ?_
  have h1 : ∑ j ∈ F, Real.exp (β * γ t j) * (β * γ' j) =
      β * ∑ j ∈ F, Real.exp (β * γ t j) * γ' j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j ∈ F, softmax F β (γ t) j * γ' j =
      (∑ j ∈ F, Real.exp (β * γ t j) * γ' j) / ∑ j ∈ F, Real.exp (β * γ t j) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [softmax]; ring
  rw [h1, h2]
  simp only [softmax]
  generalize ∑ j ∈ F, Real.exp (β * γ t j) = S at hS ⊢
  generalize ∑ j ∈ F, Real.exp (β * γ t j) * γ' j = T
  field_simp

lemma continuous_sumExp {X : Type*} [TopologicalSpace X] (F : Finset ι) (β : ℝ)
    {Z : X → ι → ℝ} (hZ : ∀ i, Continuous fun x => Z x i) :
    Continuous fun x => ∑ i ∈ F, Real.exp (β * Z x i) :=
  continuous_finsetSum _ fun i _ => Real.continuous_exp.comp (continuous_const.mul (hZ i))

lemma continuous_smoothMax {X : Type*} [TopologicalSpace X] {F : Finset ι} (hF : F.Nonempty)
    (β : ℝ) {Z : X → ι → ℝ} (hZ : ∀ i, Continuous fun x => Z x i) :
    Continuous fun x => smoothMax F β (Z x) := by
  unfold smoothMax
  exact continuous_const.mul
    ((continuous_sumExp F β hZ).log fun x => (sumExp_pos hF β (Z x)).ne')

lemma continuous_softmax {X : Type*} [TopologicalSpace X] {F : Finset ι} (hF : F.Nonempty)
    (β : ℝ) {Z : X → ι → ℝ} (hZ : ∀ i, Continuous fun x => Z x i) (i : ι) :
    Continuous fun x => softmax F β (Z x) i := by
  unfold softmax
  exact (Real.continuous_exp.comp (continuous_const.mul (hZ i))).div
    (continuous_sumExp F β hZ) fun x => (sumExp_pos hF β (Z x)).ne'

/-- The double-sum identity behind the sign of the derivative. -/
lemma two_mul_sum_eq_double_sum (F : Finset ι) (p : ι → ℝ) (hp1 : ∑ i ∈ F, p i = 1)
    (D : ι → ι → ℝ) (hD : ∀ i j, D i j = D j i) :
    2 * ∑ i ∈ F, p i * (D i i - ∑ j ∈ F, p j * D j i) =
      ∑ i ∈ F, ∑ j ∈ F, p i * p j * (D i i + D j j - 2 * D i j) := by
  have hA : ∑ i ∈ F, ∑ j ∈ F, p i * p j * D i i = ∑ i ∈ F, p i * D i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ j ∈ F, p i * p j * D i i = (p i * D i i) * ∑ j ∈ F, p j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = p i * D i i := by rw [hp1, mul_one]
  have hB : ∑ i ∈ F, ∑ j ∈ F, p i * p j * D j j = ∑ i ∈ F, p i * D i i := by
    rw [Finset.sum_comm, ← hA]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hC : ∑ i ∈ F, ∑ j ∈ F, p i * p j * D i j = ∑ i ∈ F, p i * ∑ j ∈ F, p j * D j i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hD i j]; ring
  have hsplit : ∑ i ∈ F, ∑ j ∈ F, p i * p j * (D i i + D j j - 2 * D i j) =
      ∑ i ∈ F, ∑ j ∈ F, p i * p j * D i i + ∑ i ∈ F, ∑ j ∈ F, p i * p j * D j j -
        2 * ∑ i ∈ F, ∑ j ∈ F, p i * p j * D i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hL : ∑ i ∈ F, p i * (D i i - ∑ j ∈ F, p j * D j i) =
      ∑ i ∈ F, p i * D i i - ∑ i ∈ F, p i * ∑ j ∈ F, p j * D j i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hA, hB, hC, hL]
  ring

end SmoothMax

/-! ### The interpolation -/

section Interpolation

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The interpolating vectors `U θ i = cos θ • u i + sin θ • u' i`. -/
def interpVec (u u' : ι → H) (θ : ℝ) (i : ι) : H :=
  Real.cos θ • u i + Real.sin θ • u' i

/-- The `θ`-derivative `-sin θ • u i + cos θ • u' i` of `interpVec`. -/
def interpVec' (u u' : ι → H) (θ : ℝ) (i : ι) : H :=
  (-Real.sin θ) • u i + Real.cos θ • u' i

/-- The interpolating Gaussian family with drift, `⟪U θ i, x⟫ + b i`. -/
def interpZ (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x : H) (i : ι) : ℝ :=
  ⟪interpVec u u' θ i, x⟫ + b i

lemma interpZ_zero (u u' : ι → H) (b : ι → ℝ) (x : H) (i : ι) :
    interpZ u u' b 0 x i = ⟪u i, x⟫ + b i := by
  simp [interpZ, interpVec]

lemma interpZ_pi_div_two (u u' : ι → H) (b : ι → ℝ) (x : H) (i : ι) :
    interpZ u u' b (π / 2) x i = ⟪u' i, x⟫ + b i := by
  simp [interpZ, interpVec]

lemma interpZ_eq_cos_sin (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x : H) (i : ι) :
    interpZ u u' b θ x i = Real.cos θ * ⟪u i, x⟫ + Real.sin θ * ⟪u' i, x⟫ + b i := by
  simp only [interpZ, interpVec, inner_add_left, real_inner_smul_left]

lemma norm_interpVec_le (u u' : ι → H) (θ : ℝ) (i : ι) :
    ‖interpVec u u' θ i‖ ≤ ‖u i‖ + ‖u' i‖ := by
  unfold interpVec
  calc ‖Real.cos θ • u i + Real.sin θ • u' i‖
      ≤ ‖Real.cos θ • u i‖ + ‖Real.sin θ • u' i‖ := norm_add_le _ _
    _ = |Real.cos θ| * ‖u i‖ + |Real.sin θ| * ‖u' i‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖u i‖ + 1 * ‖u' i‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg _))
    _ = ‖u i‖ + ‖u' i‖ := by ring

lemma norm_interpVec'_le (u u' : ι → H) (θ : ℝ) (i : ι) :
    ‖interpVec' u u' θ i‖ ≤ ‖u i‖ + ‖u' i‖ := by
  unfold interpVec'
  calc ‖(-Real.sin θ) • u i + Real.cos θ • u' i‖
      ≤ ‖(-Real.sin θ) • u i‖ + ‖Real.cos θ • u' i‖ := norm_add_le _ _
    _ = |Real.sin θ| * ‖u i‖ + |Real.cos θ| * ‖u' i‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    _ ≤ 1 * ‖u i‖ + 1 * ‖u' i‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _))
    _ = ‖u i‖ + ‖u' i‖ := by ring

lemma hasDerivAt_interpZ_theta (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x : H) (i : ι) :
    HasDerivAt (fun θ => interpZ u u' b θ x i) ⟪interpVec' u u' θ i, x⟫ θ := by
  simp only [interpZ_eq_cos_sin]
  refine ((((Real.hasDerivAt_cos θ).mul_const ⟪u i, x⟫).add
    ((Real.hasDerivAt_sin θ).mul_const ⟪u' i, x⟫)).add_const (b i)).congr_deriv ?_
  simp only [interpVec', inner_add_left, real_inner_smul_left]

lemma hasDerivAt_interpZ_line (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x e : H) (t : ℝ) (i : ι) :
    HasDerivAt (fun s : ℝ => interpZ u u' b θ (x + s • e) i) ⟪interpVec u u' θ i, e⟫ t := by
  have h : (fun s : ℝ => interpZ u u' b θ (x + s • e) i) =
      fun s => s * ⟪interpVec u u' θ i, e⟫ + (⟪interpVec u u' θ i, x⟫ + b i) := by
    funext s
    simp only [interpZ, inner_add_right, real_inner_smul_right]
    ring
  rw [h]
  exact (hasDerivAt_mul_const _).add_const _

lemma continuous_interpZ (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (i : ι) :
    Continuous fun x : H => interpZ u u' b θ x i := by
  unfold interpZ
  exact (continuous_const.inner continuous_id).add continuous_const

lemma abs_interpZ_le (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x : H) (i : ι) :
    |interpZ u u' b θ x i| ≤ (‖u i‖ + ‖u' i‖) * ‖x‖ + |b i| := by
  unfold interpZ
  calc |⟪interpVec u u' θ i, x⟫ + b i| ≤ |⟪interpVec u u' θ i, x⟫| + |b i| := abs_add_le _ _
    _ ≤ ‖interpVec u u' θ i‖ * ‖x‖ + |b i| := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ ≤ (‖u i‖ + ‖u' i‖) * ‖x‖ + |b i| := by
        gcongr
        exact norm_interpVec_le u u' θ i

/-- The key algebraic inequality: for probability weights `p` on `F`, if `u` and `u'` span
orthogonal subspaces and `‖u i - u j‖ ≤ ‖u' i - u' j‖` on `F`, then for `cos θ sin θ ≥ 0`,
`∑_i p_i (⟪U_i, V_i⟫ - ∑_j p_j ⟪U_j, V_i⟫) ≥ 0`, where `U = interpVec`, `V = interpVec'`. -/
lemma inner_interpVec_interpVec' {u u' : ι → H} (horth : ∀ i j, ⟪u i, u' j⟫ = 0) (θ : ℝ)
    (i j : ι) :
    ⟪interpVec u u' θ j, interpVec' u u' θ i⟫ =
      Real.cos θ * Real.sin θ * (⟪u' j, u' i⟫ - ⟪u j, u i⟫) := by
  have h1 : ⟪u j, u' i⟫ = 0 := horth j i
  have h2 : ⟪u' j, u i⟫ = 0 := by rw [real_inner_comm]; exact horth i j
  simp only [interpVec, interpVec', inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, h1, h2]
  ring

lemma interp_quadratic_nonneg (F : Finset ι) {u u' : ι → H} (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hdist : ∀ i ∈ F, ∀ j ∈ F, ‖u i - u j‖ ≤ ‖u' i - u' j‖) {p : ι → ℝ}
    (hp : ∀ i ∈ F, 0 ≤ p i) (hp1 : ∑ i ∈ F, p i = 1) {θ : ℝ}
    (hθ : 0 ≤ Real.cos θ * Real.sin θ) :
    0 ≤ ∑ i ∈ F, p i * (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
      ∑ j ∈ F, p j * ⟪interpVec u u' θ j, interpVec' u u' θ i⟫) := by
  have hD : ∀ i j : ι, (⟪u' i, u' j⟫ - ⟪u i, u j⟫) = (⟪u' j, u' i⟫ - ⟪u j, u i⟫) :=
    fun i j => by rw [real_inner_comm (u' i), real_inner_comm (u i)]
  have hDnonneg : ∀ i ∈ F, ∀ j ∈ F, 0 ≤ (⟪u' i, u' i⟫ - ⟪u i, u i⟫) +
      (⟪u' j, u' j⟫ - ⟪u j, u j⟫) - 2 * (⟪u' i, u' j⟫ - ⟪u i, u j⟫) := by
    intro i hi j hj
    have h1 : (⟪u' i, u' i⟫ - ⟪u i, u i⟫) + (⟪u' j, u' j⟫ - ⟪u j, u j⟫) -
        2 * (⟪u' i, u' j⟫ - ⟪u i, u j⟫) = ‖u' i - u' j‖ ^ 2 - ‖u i - u j‖ ^ 2 := by
      simp only [norm_sub_sq_real, real_inner_self_eq_norm_sq]
      ring
    rw [h1, sub_nonneg]
    have := hdist i hi j hj
    gcongr
  have e : ∑ i ∈ F, p i * (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
      ∑ j ∈ F, p j * ⟪interpVec u u' θ j, interpVec' u u' θ i⟫) =
      Real.cos θ * Real.sin θ * ∑ i ∈ F, p i * ((⟪u' i, u' i⟫ - ⟪u i, u i⟫) -
        ∑ j ∈ F, p j * (⟪u' j, u' i⟫ - ⟪u j, u i⟫)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [inner_interpVec_interpVec' horth]
    rw [show ∑ j ∈ F, p j * (Real.cos θ * Real.sin θ * (⟪u' j, u' i⟫ - ⟪u j, u i⟫)) =
        Real.cos θ * Real.sin θ * ∑ j ∈ F, p j * (⟪u' j, u' i⟫ - ⟪u j, u i⟫) by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  rw [e]
  refine mul_nonneg hθ ?_
  have h2 := two_mul_sum_eq_double_sum F p hp1 (fun j i => ⟪u' j, u' i⟫ - ⟪u j, u i⟫) hD
  have h3 : 0 ≤ ∑ i ∈ F, ∑ j ∈ F, p i * p j * ((⟪u' i, u' i⟫ - ⟪u i, u i⟫) +
      (⟪u' j, u' j⟫ - ⟪u j, u j⟫) - 2 * (⟪u' i, u' j⟫ - ⟪u i, u j⟫)) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hp i hi) (hp j hj)) (hDnonneg i hi j hj)
  linarith

end Interpolation

/-! ### Differentiating the interpolation -/

section Gaussian

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

lemma integrable_norm_stdGaussian : Integrable (fun x : H => ‖x‖) (stdGaussian H) :=
  IsGaussian.integrable_fun_id.norm

lemma integrable_smoothMax_interpZ {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) :
    Integrable (fun x => smoothMax F β (interpZ u u' b θ x)) (stdGaussian H) := by
  refine Integrable.mono'
    ((integrable_norm_stdGaussian.const_mul (∑ i ∈ F, (‖u i‖ + ‖u' i‖))).fun_add
      (integrable_const (∑ i ∈ F, |b i| + Real.log F.card / β)))
    (continuous_smoothMax hF β fun i => continuous_interpZ u u' b θ i).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  show ‖smoothMax F β (interpZ u u' b θ x)‖ ≤
    (∑ i ∈ F, (‖u i‖ + ‖u' i‖)) * ‖x‖ + (∑ i ∈ F, |b i| + Real.log F.card / β)
  rw [Real.norm_eq_abs]
  refine (abs_smoothMax_le hF hβ _).trans ?_
  have : ∑ i ∈ F, |interpZ u u' b θ x i| ≤ ∑ i ∈ F, ((‖u i‖ + ‖u' i‖) * ‖x‖ + |b i|) :=
    Finset.sum_le_sum fun i _ => abs_interpZ_le u u' b θ x i
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at this
  linarith

/-- The `θ`-derivative of the integrand of the interpolation. -/
def interpDeriv (F : Finset ι) (β : ℝ) (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x : H) : ℝ :=
  ∑ i ∈ F, softmax F β (interpZ u u' b θ x) i * ⟪interpVec' u u' θ i, x⟫

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma abs_interpDeriv_le (F : Finset ι) (β : ℝ) (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (x : H) :
    |interpDeriv F β u u' b θ x| ≤ (∑ i ∈ F, (‖u i‖ + ‖u' i‖)) * ‖x‖ := by
  unfold interpDeriv
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul]
  calc |softmax F β (interpZ u u' b θ x) i| * |⟪interpVec' u u' θ i, x⟫|
      ≤ 1 * (‖interpVec' u u' θ i‖ * ‖x‖) :=
        mul_le_mul (abs_softmax_le_one β _ hi) (abs_real_inner_le_norm _ _) (abs_nonneg _)
          zero_le_one
    _ ≤ (‖u i‖ + ‖u' i‖) * ‖x‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (norm_interpVec'_le u u' θ i) (norm_nonneg _)

/-- The interpolation `φ(θ) = E[F_β((⟪U θ i, x⟫ + b i)_i)]`. -/
def interpPhi (F : Finset ι) (β : ℝ) (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, smoothMax F β (interpZ u u' b θ x) ∂(stdGaussian H)

theorem hasDerivAt_interpPhi {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (θ₀ : ℝ) :
    HasDerivAt (interpPhi F β u u' b)
      (∫ x, interpDeriv F β u u' b θ₀ x ∂(stdGaussian H)) θ₀ := by
  have hcont : ∀ θ, Continuous fun x => smoothMax F β (interpZ u u' b θ x) := fun θ =>
    continuous_smoothMax hF β fun i => continuous_interpZ u u' b θ i
  have hcont' : Continuous fun x => interpDeriv F β u u' b θ₀ x := by
    unfold interpDeriv
    exact continuous_finsetSum _ fun i _ =>
      (continuous_softmax hF β (fun j => continuous_interpZ u u' b θ₀ j) i).mul
        (continuous_const.inner continuous_id)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussian H)
    (F := fun θ x => smoothMax F β (interpZ u u' b θ x))
    (F' := fun θ x => interpDeriv F β u u' b θ x) (x₀ := θ₀)
    (bound := fun x => (∑ i ∈ F, (‖u i‖ + ‖u' i‖)) * ‖x‖) (s := univ) univ_mem
    (Eventually.of_forall fun θ => (hcont θ).aestronglyMeasurable)
    (integrable_smoothMax_interpZ hF hβ u u' b θ₀) hcont'.aestronglyMeasurable
    (ae_of_all _ fun x θ _ => by
      rw [Real.norm_eq_abs]
      exact abs_interpDeriv_le F β u u' b θ x)
    (integrable_norm_stdGaussian.const_mul _)
    (ae_of_all _ fun x θ _ =>
      hasDerivAt_smoothMax hF hβ.ne' (γ := fun s => interpZ u u' b s x)
        (γ' := fun i => ⟪interpVec' u u' θ i, x⟫)
        fun i => hasDerivAt_interpZ_theta u u' b θ x i)
  exact key.2

/-- The gradient of `x ↦ p_i(x)`, the softmax weight at `(⟪U θ j, x⟫ + b j)_j`. -/
def steinGrad (F : Finset ι) (β : ℝ) (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (i : ι) (x : H) : H :=
  (β * softmax F β (interpZ u u' b θ x) i) •
    (interpVec u u' θ i - ∑ j ∈ F, softmax F β (interpZ u u' b θ x) j • interpVec u u' θ j)

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma continuous_steinGrad {F : Finset ι} (hF : F.Nonempty) (β : ℝ) (u u' : ι → H)
    (b : ι → ℝ) (θ : ℝ) (i : ι) : Continuous (steinGrad F β u u' b θ i) := by
  have hp : ∀ j, Continuous fun x => softmax F β (interpZ u u' b θ x) j := fun j =>
    continuous_softmax hF β (fun k => continuous_interpZ u u' b θ k) j
  unfold steinGrad
  exact (continuous_const.mul (hp i)).smul
    (continuous_const.sub (continuous_finsetSum _ fun j _ => (hp j).smul continuous_const))

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma norm_steinGrad_le {F : Finset ι} {β : ℝ} (hβ : 0 < β) (u u' : ι → H) (b : ι → ℝ)
    (θ : ℝ) {i : ι} (hi : i ∈ F) (x : H) :
    ‖steinGrad F β u u' b θ i x‖ ≤
      β * (‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖) := by
  unfold steinGrad
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hβ,
    abs_of_nonneg (softmax_nonneg F β _ i)]
  have h1 : ‖interpVec u u' θ i -
      ∑ j ∈ F, softmax F β (interpZ u u' b θ x) j • interpVec u u' θ j‖ ≤
      ‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖ := by
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j hj => ?_)))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (softmax_nonneg F β _ j)]
    exact mul_le_of_le_one_left (norm_nonneg _) (softmax_le_one β _ hj)
  have h2 := softmax_le_one β (interpZ u u' b θ x) hi
  have h3 := softmax_nonneg F β (interpZ u u' b θ x) i
  calc β * softmax F β (interpZ u u' b θ x) i *
        ‖interpVec u u' θ i - ∑ j ∈ F, softmax F β (interpZ u u' b θ x) j • interpVec u u' θ j‖
      ≤ β * 1 * (‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖) := by
        gcongr
    _ = β * (‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖) := by ring

/-- Gaussian integration by parts applied to one softmax weight. -/
lemma integral_inner_mul_softmax {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) {i : ι} (hi : i ∈ F) (a : H) :
    ∫ x, ⟪a, x⟫ * softmax F β (interpZ u u' b θ x) i ∂(stdGaussian H) =
      ∫ x, ⟪steinGrad F β u u' b θ i x, a⟫ ∂(stdGaussian H) := by
  refine SteinIBP.integral_inner_mul_stdGaussian
    (G := fun x => softmax F β (interpZ u u' b θ x) i) (G' := steinGrad F β u u' b θ i)
    (C := 1) (C' := β * (‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖))
    (fun x e t => ?_)
    (continuous_softmax hF β (fun k => continuous_interpZ u u' b θ k) i)
    (continuous_steinGrad hF β u u' b θ i) (fun x => abs_softmax_le_one β _ hi)
    (norm_steinGrad_le hβ u u' b θ hi) a
  refine (hasDerivAt_softmax hF β (γ := fun s => interpZ u u' b θ (x + s • e))
    (γ' := fun j => ⟪interpVec u u' θ j, e⟫)
    (fun j => hasDerivAt_interpZ_line u u' b θ x e t j) i).congr_deriv ?_
  simp only [steinGrad, real_inner_smul_left, inner_sub_left, sum_inner]

/-- **The derivative of the interpolation is nonnegative** on `[0, π/2]`. -/
theorem integral_interpDeriv_nonneg {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hdist : ∀ i ∈ F, ∀ j ∈ F, ‖u i - u j‖ ≤ ‖u' i - u' j‖) {θ : ℝ}
    (hθ : 0 ≤ Real.cos θ * Real.sin θ) :
    0 ≤ ∫ x, interpDeriv F β u u' b θ x ∂(stdGaussian H) := by
  have hp : ∀ j, Continuous fun x => softmax F β (interpZ u u' b θ x) j := fun j =>
    continuous_softmax hF β (fun k => continuous_interpZ u u' b θ k) j
  have hint1 : ∀ i ∈ F, Integrable (fun x => ⟪interpVec' u u' θ i, x⟫ *
      softmax F β (interpZ u u' b θ x) i) (stdGaussian H) := by
    intro i hi
    exact (IsGaussian.integrable_fun_id.const_inner (interpVec' u u' θ i)).mul_bdd
      (hp i).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_softmax_le_one β _ hi)
  have hint2 : ∀ i ∈ F, Integrable (fun x => ⟪steinGrad F β u u' b θ i x, interpVec' u u' θ i⟫)
      (stdGaussian H) := by
    intro i hi
    refine Integrable.of_bound
      ((continuous_steinGrad hF β u u' b θ i).inner continuous_const).aestronglyMeasurable
      (β * (‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖) * ‖interpVec' u u' θ i‖)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact norm_steinGrad_le hβ u u' b θ hi x
  have hsum : ∫ x, interpDeriv F β u u' b θ x ∂(stdGaussian H) =
      ∫ x, ∑ i ∈ F, ⟪steinGrad F β u u' b θ i x, interpVec' u u' θ i⟫ ∂(stdGaussian H) := by
    rw [integral_finsetSum _ hint2]
    rw [← Finset.sum_congr rfl fun i hi =>
      integral_inner_mul_softmax hF hβ u u' b θ hi (interpVec' u u' θ i)]
    rw [← integral_finsetSum _ hint1]
    congr 1
    funext x
    unfold interpDeriv
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum]
  refine integral_nonneg fun x => ?_
  have e : ∑ i ∈ F, ⟪steinGrad F β u u' b θ i x, interpVec' u u' θ i⟫ =
      β * ∑ i ∈ F, softmax F β (interpZ u u' b θ x) i *
        (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
          ∑ j ∈ F, softmax F β (interpZ u u' b θ x) j *
            ⟪interpVec u u' θ j, interpVec' u u' θ i⟫) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [steinGrad, real_inner_smul_left, inner_sub_left, sum_inner]
    ring
  show 0 ≤ ∑ i ∈ F, ⟪steinGrad F β u u' b θ i x, interpVec' u u' θ i⟫
  rw [e]
  exact mul_nonneg hβ.le (interp_quadratic_nonneg F horth hdist
    (fun i _ => softmax_nonneg F β _ i) (sum_softmax hF β _) hθ)

/-- **Monotonicity of the interpolation**: `φ(0) ≤ φ(π/2)`. -/
theorem interpPhi_zero_le {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hdist : ∀ i ∈ F, ∀ j ∈ F, ‖u i - u j‖ ≤ ‖u' i - u' j‖) :
    interpPhi F β u u' b 0 ≤ interpPhi F β u u' b (π / 2) := by
  have hd := hasDerivAt_interpPhi (H := H) hF hβ u u' b
  have hmono : MonotoneOn (interpPhi F β u u' b) (Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
      (fun θ _ => (hd θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hd θ).differentiableAt.differentiableWithinAt) fun θ hθ => ?_
    rw [interior_Icc] at hθ
    rw [(hd θ).deriv]
    refine integral_interpDeriv_nonneg hF hβ u u' b horth hdist ?_
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  exact hmono (left_mem_Icc.2 hpi) (right_mem_Icc.2 hpi) hpi

/-- For each `β > 0`, `E max(X + b) ≤ E max(Y + b) + log |F| / β`. -/
theorem vecExpectedMax_le_add_of_orthogonal {F : Finset ι} (hF : F.Nonempty) {β : ℝ}
    (hβ : 0 < β) (u u' : ι → H) (b : ι → ℝ) (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hdist : ∀ i ∈ F, ∀ j ∈ F, ‖u i - u j‖ ≤ ‖u' i - u' j‖)
    (hint : Integrable (fun x => ⨆ i : F, ⟪u i, x⟫ + b i) (stdGaussian H))
    (hint' : Integrable (fun x => ⨆ i : F, ⟪u' i, x⟫ + b i) (stdGaussian H)) :
    vecExpectedMax F u b ≤ vecExpectedMax F u' b + Real.log F.card / β := by
  have h1 : vecExpectedMax F u b ≤ interpPhi F β u u' b 0 := by
    unfold vecExpectedMax interpPhi
    refine integral_mono hint (integrable_smoothMax_interpZ hF hβ u u' b 0) fun x => ?_
    have := iSup_le_smoothMax hF hβ (interpZ u u' b 0 x)
    simpa only [interpZ_zero] using this
  have h2 := interpPhi_zero_le hF hβ u u' b horth hdist
  have h3 : interpPhi F β u u' b (π / 2) ≤ vecExpectedMax F u' b + Real.log F.card / β := by
    unfold vecExpectedMax interpPhi
    have hle : ∀ x, smoothMax F β (interpZ u u' b (π / 2) x) ≤
        (⨆ i : F, ⟪u' i, x⟫ + b i) + Real.log F.card / β := fun x => by
      have := smoothMax_le_iSup hF hβ (interpZ u u' b (π / 2) x)
      simpa only [interpZ_pi_div_two] using this
    calc ∫ x, smoothMax F β (interpZ u u' b (π / 2) x) ∂(stdGaussian H)
        ≤ ∫ x, ((⨆ i : F, ⟪u' i, x⟫ + b i) + Real.log F.card / β) ∂(stdGaussian H) :=
          integral_mono (integrable_smoothMax_interpZ hF hβ u u' b _)
            (hint'.fun_add (integrable_const _)) hle
      _ = ∫ x, (⨆ i : F, ⟪u' i, x⟫ + b i) ∂(stdGaussian H) + Real.log F.card / β := by
          rw [integral_add hint' (integrable_const _), integral_const]
          simp
  linarith

/-- **Sudakov–Fernique for two families in one space spanning orthogonal subspaces.** -/
theorem vecExpectedMax_le_of_orthogonal (F : Finset ι) (u u' : ι → H) (b : ι → ℝ)
    (horth : ∀ i j, ⟪u i, u' j⟫ = 0) (hdist : ∀ i ∈ F, ∀ j ∈ F, ‖u i - u j‖ ≤ ‖u' i - u' j‖)
    (hint : Integrable (fun x => ⨆ i : F, ⟪u i, x⟫ + b i) (stdGaussian H))
    (hint' : Integrable (fun x => ⨆ i : F, ⟪u' i, x⟫ + b i) (stdGaussian H)) :
    vecExpectedMax F u b ≤ vecExpectedMax F u' b := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [vecExpectedMax]
  have hcard : (1 : ℝ) ≤ F.card := by exact_mod_cast hF.card_pos
  have hL : 0 ≤ Real.log F.card := Real.log_nonneg hcard
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hβ : 0 < (Real.log F.card + 1) / ε := div_pos (by linarith) hε
  have h := vecExpectedMax_le_add_of_orthogonal hF hβ u u' b horth hdist hint hint'
  have h4 : Real.log F.card / ((Real.log F.card + 1) / ε) ≤ ε := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

end Gaussian

end SudakovFernique

open SudakovFernique

/-- **Sudakov–Fernique inequality with drift** (blueprint obligation), from the Gram bridge and
the integrability of finite maxima. -/
theorem sudakovFernique_of (hGB : Blueprint.GramBridge) (_hGR : Blueprint.GramRepresentation)
    (hMI : Blueprint.MaxIntegrable) : Blueprint.SudakovFernique := by
  intro ι E E' _ _ _ _ _ _ _ _ _ _ F v w b hvw
  let u : ι → WithLp 2 (E × E') := fun i => WithLp.toLp 2 (v i, 0)
  let u' : ι → WithLp 2 (E × E') := fun i => WithLp.toLp 2 (0, w i)
  have hu : vecExpectedMax F v b = vecExpectedMax F u b := by
    rw [← hGB ι E F v b, ← hGB ι (WithLp 2 (E × E')) F u b]
    congr 1
    funext i j
    simp [u]
  have hu' : vecExpectedMax F w b = vecExpectedMax F u' b := by
    rw [← hGB ι E' F w b, ← hGB ι (WithLp 2 (E × E')) F u' b]
    congr 1
    funext i j
    simp [u']
  rw [hu, hu']
  refine vecExpectedMax_le_of_orthogonal F u u' b (fun i j => by simp [u, u'])
    (fun i hi j hj => ?_) (hMI ι _ F u b) (hMI ι _ F u' b)
  have e1 : ‖u i - u j‖ = ‖v i - v j‖ := by
    simp only [u]
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero, WithLp.norm_toLp_fst]
  have e2 : ‖u' i - u' j‖ = ‖w i - w j‖ := by
    simp only [u']
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero, WithLp.norm_toLp_snd]
  rw [e1, e2]
  exact hvw i hi j hj

/-- **Sudakov–Fernique inequality with drift**, unconditionally. -/
theorem sudakovFernique : Blueprint.SudakovFernique :=
  sudakovFernique_of gramBridge gramRepresentation maxIntegrable

end LQGDimension
