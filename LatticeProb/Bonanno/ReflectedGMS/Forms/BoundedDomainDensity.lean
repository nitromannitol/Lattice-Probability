/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedDomainDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DomainDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.NormalContraction
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Bounded functions are dense in the full form domain

Symmetric interval projections truncate an arbitrary full-domain function without
introducing a finite-support closure or a summability assumption on the speed.
Dominated convergence is applied separately to the weighted value densities and
to the full ordered-pair edge densities.
-/

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- Symmetric truncation at height `n`. -/
noncomputable def boundedTruncation (n : ℕ) (x : ℝ) : ℝ :=
  Set.projIcc (-(n : ℝ)) (n : ℝ)
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) x

@[simp] theorem boundedTruncation_zero (n : ℕ) : boundedTruncation n 0 = 0 := by
  simp [boundedTruncation, Set.coe_projIcc]

theorem boundedTruncation_lipschitz (n : ℕ) :
    LipschitzWith 1 (boundedTruncation n) := by
  unfold boundedTruncation
  simpa only [one_mul, Function.comp_def] using
    (LipschitzWith.subtype_val (Set.Icc (-(n : ℝ)) (n : ℝ))).comp
      (LipschitzWith.projIcc
        ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)))

theorem abs_boundedTruncation_le (n : ℕ) (x : ℝ) :
    |boundedTruncation n x| ≤ n := by
  rw [abs_le]
  exact (Set.projIcc (-(n : ℝ)) (n : ℝ)
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) x).property

theorem boundedTruncation_hasSpeedL2 (m : V → ℝ) (f : V → ℝ)
    (hL2 : HasSpeedL2 m f) (n : ℕ) :
    HasSpeedL2 m (boundedTruncation n ∘ f) :=
  hasSpeedL2_normalContraction m f (boundedTruncation_lipschitz n)
    (boundedTruncation_zero n) hL2

theorem boundedTruncation_hasFiniteEnergy
    (G : ReflectedWalk.ConductanceGraph V) (f : V → ℝ)
    (hE : G.HasFiniteEnergy f) (n : ℕ) :
    G.HasFiniteEnergy (boundedTruncation n ∘ f) :=
  hasFiniteEnergy_contraction G f (boundedTruncation_lipschitz n) hE

private theorem abs_sub_boundedTruncation_le (n : ℕ) (x : ℝ) :
    |x - boundedTruncation n x| ≤ 2 * |x| := by
  calc
    |x - boundedTruncation n x| ≤ |x| + |boundedTruncation n x| := abs_sub _ _
    _ ≤ |x| + |x| := add_le_add_right (by
      simpa only [Real.norm_eq_abs] using
        norm_normalContraction_le (boundedTruncation_lipschitz n)
          (boundedTruncation_zero n) x) _
    _ = 2 * |x| := by ring

private theorem speedResidualSq_le (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (n : ℕ) (v : V) :
    m v * (f v - boundedTruncation n (f v)) ^ 2 ≤
      4 * (m v * (f v) ^ 2) := by
  have hsq : (f v - boundedTruncation n (f v)) ^ 2 ≤ 4 * (f v) ^ 2 := by
    have h := abs_sub_boundedTruncation_le n (f v)
    calc
      _ = |f v - boundedTruncation n (f v)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * |f v|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))).2 h
      _ = 4 * (f v) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  calc
    _ ≤ m v * (4 * (f v) ^ 2) := mul_le_mul_of_nonneg_left hsq (hm v).le
    _ = _ := by ring

private theorem gradSq_residual_le (G : ReflectedWalk.ConductanceGraph V)
    (f : V → ℝ) (n : ℕ) (p : V × V) :
    G.gradSq (f - boundedTruncation n ∘ f) p ≤ 4 * G.gradSq f p := by
  have hc : |boundedTruncation n (f p.2) - boundedTruncation n (f p.1)| ≤
      |f p.2 - f p.1| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul]
      using (boundedTruncation_lipschitz n).dist_le_mul (f p.2) (f p.1)
  have hr : |(f p.2 - f p.1) -
      (boundedTruncation n (f p.2) - boundedTruncation n (f p.1))| ≤
      2 * |f p.2 - f p.1| := by
    calc
      _ ≤ |f p.2 - f p.1| +
          |boundedTruncation n (f p.2) - boundedTruncation n (f p.1)| := abs_sub _ _
      _ ≤ |f p.2 - f p.1| + |f p.2 - f p.1| := add_le_add_right hc _
      _ = 2 * |f p.2 - f p.1| := by ring
  unfold ReflectedWalk.ConductanceGraph.gradSq
  simp only [Pi.sub_apply, Function.comp_apply]
  have hsq : ((f p.2 - boundedTruncation n (f p.2)) -
      (f p.1 - boundedTruncation n (f p.1))) ^ 2 ≤
      4 * (f p.2 - f p.1) ^ 2 := by
    rw [show (f p.2 - boundedTruncation n (f p.2)) -
      (f p.1 - boundedTruncation n (f p.1)) =
      (f p.2 - f p.1) -
        (boundedTruncation n (f p.2) - boundedTruncation n (f p.1)) by ring]
    calc
      _ = |(f p.2 - f p.1) -
          (boundedTruncation n (f p.2) - boundedTruncation n (f p.1))| ^ 2 :=
        (sq_abs _).symm
      _ ≤ (2 * |f p.2 - f p.1|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))).2 hr
      _ = 4 * (f p.2 - f p.1) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  calc
    _ ≤ G.c p.1 p.2 * (4 * (f p.2 - f p.1) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (G.c_nonneg p.1 p.2)
    _ = _ := by ring

private theorem inHilbertDomain_sub_norm_sq
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f g : V → ℝ) (hfL2 : HasSpeedL2 m f) (hgL2 : HasSpeedL2 m g)
    (hfE : G.HasFiniteEnergy f) (hgE : G.HasFiniteEnergy g) :
    ‖inHilbertDomain G m hm f hfL2 hfE -
      inHilbertDomain G m hm g hgL2 hgE‖ ^ 2 =
      (∑' v, m v * (g v - f v) ^ 2) + G.Energy (g - f) := by
  change ‖WithLp.toLp 2 (weightedValue m f hfL2, weightedGradient G f hfE) -
    WithLp.toLp 2 (weightedValue m g hgL2, weightedGradient G g hgE)‖ ^ 2 = _
  change ‖WithLp.toLp 2
    (weightedValue m f hfL2 - weightedValue m g hgL2,
      weightedGradient G f hfE - weightedGradient G g hgE)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  congr 1
  · have hn := lp.norm_rpow_eq_tsum (E := fun _ : V => ℝ)
      (p := 2) (by norm_num) (weightedValue m f hfL2 - weightedValue m g hgL2)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
    change ‖weightedValue m f hfL2 - weightedValue m g hgL2‖ ^ 2 = _
    rw [hn]
    apply tsum_congr
    intro v
    simp only [Real.norm_eq_abs, sq_abs, lp.coeFn_sub, Pi.sub_apply,
      weightedValue_apply]
    rw [show Real.sqrt (m v) * f v - Real.sqrt (m v) * g v =
      Real.sqrt (m v) * (f v - g v) by ring, mul_pow,
      Real.sq_sqrt (hm v).le]
    ring
  · have hn := lp.norm_rpow_eq_tsum (E := fun _ : V × V => ℝ)
      (p := 2) (by norm_num) (weightedGradient G f hfE - weightedGradient G g hgE)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
    change ‖weightedGradient G f hfE - weightedGradient G g hgE‖ ^ 2 = _
    rw [hn]
    unfold ReflectedWalk.ConductanceGraph.Energy
    rw [← tsum_div_const]
    apply tsum_congr
    intro p
    simp only [Real.norm_eq_abs, sq_abs, lp.coeFn_sub, Pi.sub_apply,
      weightedGradient_apply]
    unfold ReflectedWalk.ConductanceGraph.gradSq
    simp only [Pi.sub_apply]
    rw [show Real.sqrt (G.c p.1 p.2 / 2) * (f p.2 - f p.1) -
        Real.sqrt (G.c p.1 p.2 / 2) * (g p.2 - g p.1) =
      Real.sqrt (G.c p.1 p.2 / 2) *
        ((f p.2 - g p.2) - (f p.1 - g p.1)) by ring,
      mul_pow, Real.sq_sqrt (div_nonneg (G.c_nonneg _ _) (by norm_num))]
    ring

end ReflectedGMS.FullNetworkForm
