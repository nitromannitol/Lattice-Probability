/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51Aux6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux4
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux

/-!
# Lemma 5.1, auxiliary file 6: the Taylor linearization of `C_f(μ)`

For `C_f(μ) = Σ_i r_i Σ_z w_z e^{ξ X(T^f_i z)}` (`blockCost`), with `r_i = |p_{i+1} - p_i|`:

* `tl_exp_le`: `e^{ξX} ≤ 1 + ξX + 2ξ² (e^{2X} + e^{-2X})` for `0 < ξ ≤ 1`;
* `tl_edge_ge`, `tl_sum_edge_le`: `r_i ≥ 1/M` and `Σ_i r_i ≤ 1 + δ² E(f)`;
* `tl_blockCost_le`: `C_f ≤ Σ_i r_i + ξ ⟪V_f, x⟫ + err_f(x)` with an explicit nonnegative
  error `err_f` (`tlErr`), a combination of `e^{±⟪a, x⟫}` and `e^{±2⟪a, x⟫}`;
* `integral_tlErr_le`: `E err_f ≤ 2ξ e^{v/2} δ² E₀ + 4ξ² e^{2v} (1 + δ² E₀)`;
* `integral_iInf_blockCost_le`: the linearization used in the proof of Lemma 5.1:
  `E min_f C_f ≤ 1 - δ² E max_f (-(ξ/δ²) ⟪V_f - V_0, x⟫ - E(f)) + |Fn| · error`,
  the common centered term `ξ ⟪V_0, x⟫` integrating to zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

open Blueprint.Draft

/-! ## Scalar inequalities -/

lemma tl_exp_sub_le (y : ℝ) : exp y - 1 - y ≤ y ^ 2 * exp |y| := by
  have h1 : 1 ≤ exp |y| := one_le_exp (abs_nonneg y)
  have h3 : y ^ 2 ≤ y ^ 2 * exp |y| := le_mul_of_one_le_right (sq_nonneg _) h1
  rcases le_or_gt |y| 1 with hy | hy
  · have := (le_abs_self _).trans (abs_exp_sub_one_sub_id_le hy)
    linarith
  · rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0] at hy h1 ⊢
      have hy2 : 1 ≤ y ^ 2 := by nlinarith
      have h4 : exp y ≤ y ^ 2 * exp y := le_mul_of_one_le_left (exp_pos y).le hy2
      linarith
    · rw [abs_of_neg h0] at hy
      have h5 : exp y ≤ 1 := exp_le_one_iff.2 h0.le
      have h4 : -y ≤ y ^ 2 := by nlinarith
      linarith

lemma tl_exp_abs_le (t : ℝ) : exp |t| ≤ exp t + exp (-t) := by
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0]; linarith [exp_pos (-t)]
  · rw [abs_of_neg h0]; linarith [exp_pos t]

lemma tl_le_ch (X : ℝ) : X ≤ exp (1 * X) + exp (-1 * X) := by
  have h := add_one_le_exp |X|
  have h2 := tl_exp_abs_le X
  rw [one_mul, show -1 * X = -X by ring]
  linarith [le_abs_self X]

lemma tl_sq_le (X : ℝ) : X ^ 2 ≤ 2 * exp |X| := by
  have := quadratic_le_exp_of_nonneg (abs_nonneg X)
  rw [sq_abs] at this
  linarith [abs_nonneg X]

lemma tl_exp_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (X : ℝ) :
    exp (ξ * X) ≤ 1 + ξ * X + 2 * ξ ^ 2 * (exp (2 * X) + exp (-2 * X)) := by
  have h1 := tl_exp_sub_le (ξ * X)
  have h2 : |ξ * X| ≤ |X| := by
    rw [abs_mul, abs_of_pos hξ]; exact mul_le_of_le_one_left (abs_nonneg X) hξ1
  have h3 : exp |ξ * X| ≤ exp |X| := exp_le_exp.2 h2
  have h4 := tl_sq_le X
  have h5 : exp |X| * exp |X| = exp |2 * X| := by
    rw [← exp_add, abs_mul, abs_two]; ring_nf
  have h6 := tl_exp_abs_le (2 * X)
  rw [show -(2 * X) = -2 * X by ring] at h6
  have h7 : (ξ * X) ^ 2 * exp |ξ * X| ≤ ξ ^ 2 * (2 * exp |X|) * exp |X| := by
    rw [show (ξ * X) ^ 2 = ξ ^ 2 * X ^ 2 by ring]
    calc ξ ^ 2 * X ^ 2 * exp |ξ * X| ≤ ξ ^ 2 * X ^ 2 * exp |X| :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ ξ ^ 2 * (2 * exp |X|) * exp |X| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (sq_nonneg ξ)) (exp_pos _).le
  have h9 : ξ ^ 2 * (2 * exp |X|) * exp |X| = 2 * ξ ^ 2 * exp |2 * X| := by
    rw [← h5]; ring
  have h10 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 2 * ξ ^ 2)
  linarith

/-! ## Edge lengths -/

lemma tl_pVert (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    pVert (16 ^ n) δ f i = (((i : ℝ) / (16 : ℝ) ^ n : ℝ) : ℂ) +
      ((δ * f ((i : ℝ) / (16 : ℝ) ^ n) : ℝ) : ℂ) * Complex.I := by
  unfold pVert
  push_cast
  ring

lemma tl_edge_eq (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i =
      ((1 / (16 : ℝ) ^ n : ℝ) : ℂ) +
        ((δ * (f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)) : ℝ) : ℂ) * Complex.I := by
  rw [tl_pVert, tl_pVert]
  push_cast
  ring

lemma tl_edge_norm (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ =
      √((1 / (16 : ℝ) ^ n) ^ 2 +
        (δ * (f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n))) ^ 2) := by
  rw [tl_edge_eq, Complex.norm_add_mul_I]

lemma tl_edge_ge (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    1 / (16 : ℝ) ^ n ≤ ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ := by
  rw [tl_edge_norm]
  calc 1 / (16 : ℝ) ^ n = √((1 / (16 : ℝ) ^ n) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

lemma tl_edge_le (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ ≤ 1 / (16 : ℝ) ^ n +
      δ ^ 2 * ((16 : ℝ) ^ n / 2 * (f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)) ^ 2) := by
  rw [tl_edge_norm]
  set d := f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)
  set a : ℝ := 1 / (16 : ℝ) ^ n with ha_def
  have ha : 0 < a := by positivity
  have key : a + δ ^ 2 * ((16 : ℝ) ^ n / 2 * d ^ 2) = a + (δ * d) ^ 2 / (2 * a) := by
    rw [ha_def]; field_simp
  rw [key]
  have h2 : 2 * a * ((δ * d) ^ 2 / (2 * a)) = (δ * d) ^ 2 := by field_simp
  calc √(a ^ 2 + (δ * d) ^ 2) ≤ √((a + (δ * d) ^ 2 / (2 * a)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((δ * d) ^ 2 / (2 * a))])
    _ = _ := Real.sqrt_sq (by positivity)

lemma tl_sum_edge_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) :
    ∑ i ∈ Finset.range (16 ^ n), ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ ≤
      1 + δ ^ 2 * energy f := by
  rw [Subadd.V_energy hf]
  calc _ ≤ ∑ i ∈ Finset.range (16 ^ n), (1 / (16 : ℝ) ^ n +
        δ ^ 2 * ((16 : ℝ) ^ n / 2 * (f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)) ^ 2)) :=
        Finset.sum_le_sum fun i _ => tl_edge_le n δ f i
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

/-! ## The error term -/

section Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `e^{t⟪a, x⟫} + e^{-t⟪a, x⟫}`. -/
def tlCh (t : ℝ) (a x : E) : ℝ := exp (t * ⟪a, x⟫) + exp (-t * ⟪a, x⟫)

lemma tlCh_nonneg (t : ℝ) (a x : E) : 0 ≤ tlCh t a x :=
  add_nonneg (exp_pos _).le (exp_pos _).le

/-- The explicit error `err_f(x)` of the linearization of `C_f(μ)`. -/
def tlErr (ξ δ : ℝ) (n : ℕ) (f : ℝ → ℝ) (S : Finset ℂ) (w : ℂ → ℝ) (u : ℂ → E) (x : E) : ℝ :=
  ∑ i ∈ Finset.range (16 ^ n), ∑ z ∈ S,
    (ξ * (‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ - 1 / (16 : ℝ) ^ n) * w z *
        tlCh 1 (u (edgeSim (16 ^ n) δ f i z)) x +
      2 * ξ ^ 2 * ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ * w z *
        tlCh 2 (u (edgeSim (16 ^ n) δ f i z)) x)

lemma tlErr_nonneg {ξ : ℝ} (hξ : 0 < ξ) (δ : ℝ) (n : ℕ) (f : ℝ → ℝ) {S : Finset ℂ}
    {w : ℂ → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z) (u : ℂ → E) (x : E) : 0 ≤ tlErr ξ δ n f S w u x := by
  unfold tlErr
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun z hz => ?_
  have hr := tl_edge_ge n δ f i
  have h1 : 0 ≤ ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ - 1 / (16 : ℝ) ^ n := by
    linarith
  have := hw z hz
  have := tlCh_nonneg 1 (u (edgeSim (16 ^ n) δ f i z)) x
  have := tlCh_nonneg 2 (u (edgeSim (16 ^ n) δ f i z)) x
  positivity

/-- **Pointwise linearization**: `C_f ≤ Σ_i r_i + ξ ⟪V_f, x⟫ + err_f(x)`. -/
lemma tl_blockCost_le {n : ℕ} (f : ℝ → ℝ) {ξ δ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    {S : Finset ℂ} {w : ℂ → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z) (hw1 : ∑ z ∈ S, w z = 1)
    (u : ℂ → E) (x : E) :
    blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫) ≤
      ∑ i ∈ Finset.range (16 ^ n), ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ +
        ξ * ⟪vecV n δ S w u f, x⟫ + tlErr ξ δ n f S w u x := by
  have e1 : ∑ i ∈ Finset.range (16 ^ n), ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ =
      ∑ i ∈ Finset.range (16 ^ n), ∑ z ∈ S,
        ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ * w z := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hw1, mul_one]
  have e2 : ξ * ⟪vecV n δ S w u f, x⟫ = ∑ i ∈ Finset.range (16 ^ n), ∑ z ∈ S,
      ξ * (w z / (16 : ℝ) ^ n * ⟪u (edgeSim (16 ^ n) δ f i z), x⟫) := by
    simp only [vecV, sum_inner, real_inner_smul_left, Finset.mul_sum]
  rw [e1, e2, tlErr, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold blockCost
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z hz => ?_
  have hr := tl_edge_ge n δ f i
  set r := ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖
  set X := ⟪u (edgeSim (16 ^ n) δ f i z), x⟫
  have hwz := hw z hz
  have hr0 : 0 ≤ r := norm_nonneg _
  have hT := tl_exp_le hξ hξ1 X
  have hA := tl_le_ch X
  have h1 := mul_le_mul_of_nonneg_left hT (mul_nonneg hr0 hwz)
  have hc : 0 ≤ ξ * (r - 1 / (16 : ℝ) ^ n) * w z := by
    have : 0 ≤ r - 1 / (16 : ℝ) ^ n := by linarith
    positivity
  have h2 := mul_le_mul_of_nonneg_left hA hc
  simp only [tlCh]
  have e3 : r * w z * (1 + ξ * X + 2 * ξ ^ 2 * (exp (2 * X) + exp (-2 * X))) =
      r * w z + ξ * (w z / (16 : ℝ) ^ n * X) + ξ * (r - 1 / (16 : ℝ) ^ n) * w z * X +
        2 * ξ ^ 2 * r * w z * (exp (2 * X) + exp (-2 * X)) := by ring
  have e4 : r * (w z * exp (ξ * X)) = r * w z * exp (ξ * X) := by ring
  rw [e4]
  linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tlCh_integrable (t : ℝ) (a : E) : Integrable (fun x => tlCh t a x) (stdGaussian E) :=
  (GaussianMax.integrable_exp_mul_inner a t).add (GaussianMax.integrable_exp_mul_inner a (-t))

lemma integral_tlCh (t : ℝ) (a : E) :
    ∫ x, tlCh t a x ∂stdGaussian E = 2 * exp (‖a‖ ^ 2 * t ^ 2 / 2) := by
  unfold tlCh
  rw [integral_add (GaussianMax.integrable_exp_mul_inner a t)
    (GaussianMax.integrable_exp_mul_inner a (-t)), GaussianMax.integral_exp_mul_inner,
    GaussianMax.integral_exp_mul_inner]
  rw [neg_sq]; ring

lemma tlErr_integrable (ξ δ : ℝ) (n : ℕ) (f : ℝ → ℝ) (S : Finset ℂ) (w : ℂ → ℝ)
    (u : ℂ → E) : Integrable (fun x => tlErr ξ δ n f S w u x) (stdGaussian E) := by
  unfold tlErr
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun z _ =>
    ((tlCh_integrable 1 _).const_mul _).add ((tlCh_integrable 2 _).const_mul _)

lemma integral_tlErr_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) {E₀ : ℝ} (hE : energy f ≤ E₀)
    {ξ δ : ℝ} (hξ : 0 < ξ) {S : Finset ℂ} {w : ℂ → ℝ} (hw1 : ∑ z ∈ S, w z = 1)
    (u : ℂ → E) {v : ℝ}
    (hv : ∀ i < 16 ^ n, ∀ z ∈ S, ‖u (edgeSim (16 ^ n) δ f i z)‖ ^ 2 = v) :
    ∫ x, tlErr ξ δ n f S w u x ∂stdGaussian E ≤
      2 * ξ * exp (v / 2) * δ ^ 2 * E₀ + 4 * ξ ^ 2 * exp (2 * v) * (1 + δ ^ 2 * E₀) := by
  set R := ∑ i ∈ Finset.range (16 ^ n), ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖
    with hR
  have hRle : R ≤ 1 + δ ^ 2 * energy f := tl_sum_edge_le hf δ
  have hval : ∫ x, tlErr ξ δ n f S w u x ∂stdGaussian E =
      2 * ξ * exp (v / 2) * (R - 1) + 4 * ξ ^ 2 * exp (2 * v) * R := by
    unfold tlErr
    rw [integral_finsetSum]
    swap
    · intro i _
      exact integrable_finsetSum _ fun z _ =>
        ((tlCh_integrable 1 _).const_mul _).add ((tlCh_integrable 2 _).const_mul _)
    have hi : ∀ i ∈ Finset.range (16 ^ n), ∫ x, ∑ z ∈ S,
        (ξ * (‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ - 1 / (16 : ℝ) ^ n) * w z *
          tlCh 1 (u (edgeSim (16 ^ n) δ f i z)) x +
        2 * ξ ^ 2 * ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ * w z *
          tlCh 2 (u (edgeSim (16 ^ n) δ f i z)) x) ∂stdGaussian E =
        2 * ξ * exp (v / 2) *
          (‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ - 1 / (16 : ℝ) ^ n) +
        4 * ξ ^ 2 * exp (2 * v) * ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ := by
      intro i hi
      rw [integral_finsetSum]
      swap
      · intro z _
        exact ((tlCh_integrable 1 _).const_mul _).add ((tlCh_integrable 2 _).const_mul _)
      have hz : ∀ z ∈ S, ∫ x,
          (ξ * (‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ - 1 / (16 : ℝ) ^ n) * w z *
            tlCh 1 (u (edgeSim (16 ^ n) δ f i z)) x +
          2 * ξ ^ 2 * ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ * w z *
            tlCh 2 (u (edgeSim (16 ^ n) δ f i z)) x) ∂stdGaussian E =
          (2 * ξ * exp (v / 2) *
            (‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖ - 1 / (16 : ℝ) ^ n) +
          4 * ξ ^ 2 * exp (2 * v) * ‖pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i‖) *
            w z := by
        intro z hz
        rw [integral_add]
        rotate_left
        · exact (tlCh_integrable 1 _).const_mul _
        · exact (tlCh_integrable 2 _).const_mul _
        rw [integral_const_mul, integral_const_mul, integral_tlCh, integral_tlCh,
          hv i (Finset.mem_range.1 hi) z hz]
        have e1 : v * 1 ^ 2 / 2 = v / 2 := by ring
        have e2 : v * 2 ^ 2 / 2 = 2 * v := by ring
        rw [e1, e2]; ring
      rw [Finset.sum_congr rfl hz, ← Finset.mul_sum, hw1, mul_one]
    rw [Finset.sum_congr rfl hi, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← hR]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hval]
  have hR1 : 1 ≤ R := by
    calc (1 : ℝ) = ∑ i ∈ Finset.range (16 ^ n), 1 / (16 : ℝ) ^ n := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
      _ ≤ R := Finset.sum_le_sum fun i _ => tl_edge_ge n δ f i
  have hδE : δ ^ 2 * energy f ≤ δ ^ 2 * E₀ := mul_le_mul_of_nonneg_left hE (sq_nonneg δ)
  have ha : 0 ≤ 2 * ξ * exp (v / 2) := by positivity
  have hb : 0 ≤ 4 * ξ ^ 2 * exp (2 * v) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (show R - 1 ≤ δ ^ 2 * E₀ by linarith) ha
  have h2 := mul_le_mul_of_nonneg_left (show R ≤ 1 + δ ^ 2 * E₀ by linarith) hb
  have e : 2 * ξ * exp (v / 2) * δ ^ 2 * E₀ = 2 * ξ * exp (v / 2) * (δ ^ 2 * E₀) := by ring
  linarith

end Gauss

/-! ## The linearization -/

lemma tl_blockCost_nonneg (ξ : ℝ) (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) {S : Finset ℂ} {w : ℂ → ℝ}
    (hw : ∀ z ∈ S, 0 ≤ w z) (X : ℂ → ℝ) : 0 ≤ blockCost ξ (16 ^ n) δ f S w X := by
  unfold blockCost
  exact Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun z hz => mul_nonneg (hw z hz) (exp_pos _).le)

/-- **The Taylor linearization in the proof of Lemma 5.1**: with `V_f = vecV n δ S w u f`
(so that `⟨X, ν^f_μ⟩ = ⟪V_f, x⟫`), `E min_f C_f(μ)` is at most
`1 - δ² E max_f (-(ξ/δ²) ⟪V_f - V_0, x⟫ - E(f))` plus `|Fn|` times the Taylor/edge-length
error. -/
theorem integral_iInf_blockCost_le {n : ℕ} {Fn : Finset (ℝ → ℝ)} (hFnV : ∀ f ∈ Fn, f ∈ V n)
    (h0 : (0 : ℝ → ℝ) ∈ Fn) {E₀ : ℝ} (hE : ∀ f ∈ Fn, energy f ≤ E₀) {ξ δ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1) (hδ : 0 < δ) {S : Finset ℂ} {w : ℂ → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z)
    (hw1 : ∑ z ∈ S, w z = 1) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (u : ℂ → E) {v : ℝ}
    (hv : ∀ f ∈ Fn, ∀ i < 16 ^ n, ∀ z ∈ S, ‖u (edgeSim (16 ^ n) δ f i z)‖ ^ 2 = v) :
    ∫ x, (⨅ f : Fn, blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫)) ∂stdGaussian E ≤
      1 - δ ^ 2 * vecExpectedMax Fn (fun f => -((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)))
        (fun f => -energy f)
      + Fn.card * (2 * ξ * Real.exp (v / 2) * δ ^ 2 * E₀ + 4 * ξ ^ 2 * Real.exp (2 * v) * (1 + δ ^ 2 * E₀)) := by
  classical
  have : Nonempty Fn := ⟨⟨0, h0⟩⟩
  have hGint := integrable_iSup_inner_add Fn
    (fun f => -((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0))) (fun f => -energy f)
  have hint0 : Integrable (fun x => ξ * ⟪vecV n δ S w u 0, x⟫) (stdGaussian E) :=
    (IsGaussian.integrable_id.const_inner _).const_mul ξ
  have hErrInt : Integrable (fun x => ∑ f ∈ Fn, tlErr ξ δ n f S w u x) (stdGaussian E) :=
    integrable_finsetSum Fn fun f _ => tlErr_integrable ξ δ n f S w u
  have hA : Integrable (fun x => 1 - δ ^ 2 * (⨆ f : Fn,
      ⟪-((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)), x⟫ + -energy (f : ℝ → ℝ)))
      (stdGaussian E) := (integrable_const 1).sub (hGint.const_mul _)
  have hB : Integrable (fun x => 1 - δ ^ 2 * (⨆ f : Fn,
      ⟪-((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)), x⟫ + -energy (f : ℝ → ℝ)) +
      ξ * ⟪vecV n δ S w u 0, x⟫) (stdGaussian E) := hA.add hint0
  have hgint : Integrable (fun x => 1 - δ ^ 2 * (⨆ f : Fn,
      ⟪-((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)), x⟫ + -energy (f : ℝ → ℝ)) +
      ξ * ⟪vecV n δ S w u 0, x⟫ + ∑ f ∈ Fn, tlErr ξ δ n f S w u x) (stdGaussian E) :=
    hB.add hErrInt
  have hle : ∀ x : E, (⨅ f : Fn, blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫)) ≤
      1 - δ ^ 2 * (⨆ f : Fn,
        ⟪-((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)), x⟫ + -energy (f : ℝ → ℝ)) +
      ξ * ⟪vecV n δ S w u 0, x⟫ + ∑ f ∈ Fn, tlErr ξ δ n f S w u x := by
    intro x
    obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite (f := fun f : Fn =>
      ⟪-((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)), x⟫ + -energy (f : ℝ → ℝ))
    rw [← hf₀]
    have h1 : (⨅ f : Fn, blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫)) ≤
        blockCost ξ (16 ^ n) δ f₀ S w (fun z => ⟪u z, x⟫) :=
      ciInf_le (Set.finite_range _).bddBelow f₀
    have h2 := tl_blockCost_le (n := n) (δ := δ) f₀.1 hξ hξ1 hw hw1 u x
    have h3 := tl_sum_edge_le (hFnV f₀.1 f₀.2) δ
    have h4 : tlErr ξ δ n f₀ S w u x ≤ ∑ f ∈ Fn, tlErr ξ δ n f S w u x :=
      Finset.single_le_sum (f := fun f => tlErr ξ δ n f S w u x)
        (fun f _ => tlErr_nonneg hξ δ n f hw u x) f₀.2
    have h6 : δ ^ 2 * (⟪-((ξ / δ ^ 2) • (vecV n δ S w u f₀ - vecV n δ S w u 0)), x⟫ +
        -energy (f₀ : ℝ → ℝ)) = -(ξ * ⟪vecV n δ S w u f₀, x⟫) + ξ * ⟪vecV n δ S w u 0, x⟫ -
          δ ^ 2 * energy (f₀ : ℝ → ℝ) := by
      rw [inner_neg_left, real_inner_smul_left, inner_sub_left]
      field_simp
      ring
    linarith
  have hnn : ∀ x : E, 0 ≤ ⨅ f : Fn, blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫) :=
    fun x => Real.iInf_nonneg fun f => tl_blockCost_nonneg ξ n δ f hw _
  have hmean : ∫ x, ξ * ⟪vecV n δ S w u 0, x⟫ ∂stdGaussian E = 0 := by
    have h := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id (μ := stdGaussian E))
      (vecV n δ S w u 0)
    simp only [id] at h
    rw [integral_const_mul, h, integral_id_stdGaussian, inner_zero_right, mul_zero]
  have hErr : ∫ x, ∑ f ∈ Fn, tlErr ξ δ n f S w u x ∂stdGaussian E ≤
      Fn.card * (2 * ξ * Real.exp (v / 2) * δ ^ 2 * E₀ +
        4 * ξ ^ 2 * Real.exp (2 * v) * (1 + δ ^ 2 * E₀)) := by
    rw [integral_finsetSum _ fun f _ => tlErr_integrable ξ δ n f S w u]
    calc ∑ f ∈ Fn, ∫ x, tlErr ξ δ n f S w u x ∂stdGaussian E
        ≤ ∑ _f ∈ Fn, (2 * ξ * Real.exp (v / 2) * δ ^ 2 * E₀ +
            4 * ξ ^ 2 * Real.exp (2 * v) * (1 + δ ^ 2 * E₀)) :=
          Finset.sum_le_sum fun f hf =>
            integral_tlErr_le (hFnV f hf) (hE f hf) hξ hw1 u (hv f hf)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∫ x, (⨅ f : Fn, blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫)) ∂stdGaussian E
      ≤ ∫ x, (1 - δ ^ 2 * (⨆ f : Fn,
          ⟪-((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)), x⟫ + -energy (f : ℝ → ℝ)) +
          ξ * ⟪vecV n δ S w u 0, x⟫ + ∑ f ∈ Fn, tlErr ξ δ n f S w u x) ∂stdGaussian E :=
        integral_mono_of_nonneg (ae_of_all _ hnn) hgint (ae_of_all _ hle)
    _ = 1 - δ ^ 2 * vecExpectedMax Fn
          (fun f => -((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)))
          (fun f => -energy f) + 0 + ∫ x, ∑ f ∈ Fn, tlErr ξ δ n f S w u x ∂stdGaussian E := by
        rw [integral_add hB hErrInt, integral_add hA hint0,
          integral_sub (integrable_const 1) (hGint.const_mul _), integral_const_mul, hmean,
          integral_const, probReal_univ, one_smul]
        rfl
    _ ≤ _ := by linarith

end LQGDimension.L51
