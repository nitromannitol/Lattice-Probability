/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.ZCovPSD at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2

/-!
# Positive semidefiniteness of `zCov`

We prove `Blueprint.ZCovPSD`: for every finite family `F` of functions `ℝ → ℝ` that are
interval integrable on `[0,1]`, the matrix `(zCov f g)_{f,g ∈ F}` is positive semidefinite.

## Strategy

For reals `a b`,
`|a| + |b| - |a - b| = 2 * max (min a b) 0 + 2 * max (min (-a) (-b)) 0` (`kernel_eq`), a pure case
analysis on signs.  Each of the two summands is a Gram kernel: with the "ramp" indicator
functions `posRamp a := (Ioo 0 a).indicator 1` and `negRamp a := (Ioo a 0).indicator 1`,

`∫ y, posRamp a y * posRamp b y ∂volume = max (min a b) 0` and
`∫ y, negRamp a y * negRamp b y ∂volume = max (min (-a) (-b)) 0`

(`posRamp_integral`, `negRamp_integral`), because `posRamp a * posRamp b` is literally the
indicator of `Ioo 0 (min a b)` and likewise for `negRamp`.  Hence, for any finite index set and
any real coefficients `c`,

`∑ᵢⱼ cᵢ cⱼ (|aᵢ| + |aⱼ| - |aᵢ - aⱼ|)
  = 2 ∫ (∑ᵢ cᵢ posRamp aᵢ)² + 2 ∫ (∑ᵢ cᵢ negRamp aᵢ)² ≥ 0` (`kernel_sum_nonneg`),

using linearity of the Bochner integral over finite sums and nonnegativity of a square integral.
Applying this pointwise in `x ∈ [0,1]` to `aᵢ = f x` and integrating over `x` (using linearity of
the interval integral over finite sums, `sum_intervalIntegral_nonneg`) gives `zCovPSD`.

We also record the two corollaries other files need: interval integrability of members of `V n`
(`mem_V_intervalIntegrable`, via the piecewise-affine structure and
`IntervalIntegrable.trans_iterate`), and the specialization of `zCovPSD` to `V n`
(`zCovPSD_V`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped Matrix

namespace LQGDimension

/-! ### Symmetry of `zCov` -/

/-- `zCov` is symmetric in its two arguments. -/
lemma zCov_comm (f g : ℝ → ℝ) : zCov f g = zCov g f := by
  unfold zCov
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  show |f x| + |g x| - |f x - g x| = |g x| + |f x| - |g x - f x|
  rw [abs_sub_comm (f x) (g x)]
  ring

/-! ### Ramp indicator functions and their Gram kernel

`posRamp a` and `negRamp a` are the indicators of the (possibly empty) intervals `(0,a)` and
`(a,0)`.  Their pairwise products are again indicators of intervals, whose integrals compute the
two halves of the kernel `|a| + |b| - |a - b|` (see `kernel_eq` below). -/

/-- The "positive ramp" indicator of `a`: `1` on `(0, a)`, `0` elsewhere (empty if `a ≤ 0`). -/
private def posRamp (a : ℝ) : ℝ → ℝ := (Set.Ioo (0 : ℝ) a).indicator 1

/-- The "negative ramp" indicator of `a`: `1` on `(a, 0)`, `0` elsewhere (empty if `a ≥ 0`). -/
private def negRamp (a : ℝ) : ℝ → ℝ := (Set.Ioo a (0 : ℝ)).indicator 1

private lemma posRamp_mul_posRamp (a b : ℝ) :
    (fun y => posRamp a y * posRamp b y) = (Set.Ioo (0 : ℝ) (min a b)).indicator 1 := by
  have h : (Set.Ioo (0:ℝ) a).indicator (1:ℝ→ℝ) * (Set.Ioo (0:ℝ) b).indicator (1:ℝ→ℝ)
      = (Set.Ioo (0:ℝ) (min a b)).indicator (1:ℝ→ℝ) := by
    rw [← Set.inter_indicator_one, Set.Ioo_inter_Ioo]; norm_num
  funext y
  simpa [posRamp] using congrFun h y

private lemma negRamp_mul_negRamp (a b : ℝ) :
    (fun y => negRamp a y * negRamp b y) = (Set.Ioo (max a b) (0 : ℝ)).indicator 1 := by
  have h : (Set.Ioo a (0:ℝ)).indicator (1:ℝ→ℝ) * (Set.Ioo b (0:ℝ)).indicator (1:ℝ→ℝ)
      = (Set.Ioo (max a b) (0:ℝ)).indicator (1:ℝ→ℝ) := by
    rw [← Set.inter_indicator_one, Set.Ioo_inter_Ioo]; norm_num
  funext y
  simpa [negRamp] using congrFun h y

private lemma posRamp_integrable (a b : ℝ) :
    Integrable (fun y => posRamp a y * posRamp b y) volume := by
  rw [posRamp_mul_posRamp]
  refine (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const ?_)
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

private lemma negRamp_integrable (a b : ℝ) :
    Integrable (fun y => negRamp a y * negRamp b y) volume := by
  rw [negRamp_mul_negRamp]
  refine (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const ?_)
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

private lemma posRamp_integral (a b : ℝ) :
    ∫ y, posRamp a y * posRamp b y ∂volume = max (min a b) 0 := by
  rw [posRamp_mul_posRamp, MeasureTheory.integral_indicator_one measurableSet_Ioo]
  show (volume (Set.Ioo (0:ℝ) (min a b))).toReal = max (min a b) 0
  rcases le_total (min a b) 0 with h | h
  · rw [Set.Ioo_eq_empty (not_lt.mpr h)]
    simp [max_eq_right h]
  · rw [Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal h, max_eq_left h]

private lemma negRamp_integral (a b : ℝ) :
    ∫ y, negRamp a y * negRamp b y ∂volume = max (min (-a) (-b)) 0 := by
  rw [negRamp_mul_negRamp, MeasureTheory.integral_indicator_one measurableSet_Ioo, min_neg_neg]
  show (volume (Set.Ioo (max a b) (0:ℝ))).toReal = max (-(max a b)) 0
  rcases le_total 0 (max a b) with h | h
  · rw [Set.Ioo_eq_empty (not_lt.mpr h)]
    simp [max_eq_right (by linarith : -(max a b) ≤ (0:ℝ))]
  · rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 0 - max a b), zero_sub,
      max_eq_left (by linarith : (0:ℝ) ≤ -(max a b))]

/-- For any finite family of "ramp-type" kernels `∫ ρᵢ ρⱼ`, the associated quadratic form is
nonnegative: it equals `∫ (∑ᵢ cᵢ ρᵢ)² ≥ 0`. -/
private lemma sum_ramp_sq_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρ : ι → ℝ → ℝ)
    (hInt : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun y => ρ i y * ρ j y) volume) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, ρ i y * ρ j y ∂volume) := by
  have step1 : ∀ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, ρ i y * ρ j y ∂volume)
      = ∫ y, ∑ j ∈ s, c i * c j * (ρ i y * ρ j y) ∂volume := by
    intro i hi
    simp_rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.integral_finsetSum s fun j hj => (hInt i hi j hj).const_mul (c i * c j)).symm
  have hfun : (fun y => ∑ i ∈ s, ∑ j ∈ s, c i * c j * (ρ i y * ρ j y))
      = fun y => (∑ i ∈ s, c i * ρ i y) * (∑ i ∈ s, c i * ρ i y) := by
    funext y
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, ρ i y * ρ j y ∂volume)
      = ∫ y, (∑ i ∈ s, c i * ρ i y) * (∑ i ∈ s, c i * ρ i y) ∂volume := by
    rw [Finset.sum_congr rfl step1,
        ← MeasureTheory.integral_finsetSum s fun i hi =>
          MeasureTheory.integrable_finsetSum s fun j hj => (hInt i hi j hj).const_mul (c i * c j),
        hfun]
  rw [key]
  exact MeasureTheory.integral_nonneg fun y => mul_self_nonneg _

/-! ### The pointwise real kernel `|a| + |b| - |a - b|` -/

private lemma kernel_eq (x y : ℝ) :
    |x| + |y| - |x - y| = 2 * max (min x y) 0 + 2 * max (min (-x) (-y)) 0 := by
  rcases abs_cases x with ⟨hxe, hxs⟩ | ⟨hxe, hxs⟩ <;>
    rcases abs_cases y with ⟨hye, hys⟩ | ⟨hye, hys⟩ <;>
    rcases abs_cases (x - y) with ⟨hxye, hxys⟩ | ⟨hxye, hxys⟩ <;>
    rw [hxe, hye, hxye] <;>
    simp only [min_def, max_def] <;>
    split_ifs <;>
    linarith

/-- The key finite fact: the kernel `(a, b) ↦ |a| + |b| - |a - b|` is positive semidefinite on
any finite family of reals. -/
private lemma kernel_sum_nonneg {ι : Type*} (s : Finset ι) (a c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (|a i| + |a j| - |a i - a j|) := by
  have hpos := sum_ramp_sq_nonneg s c (fun i => posRamp (a i))
    (fun i _ j _ => posRamp_integrable (a i) (a j))
  have hneg := sum_ramp_sq_nonneg s c (fun i => negRamp (a i))
    (fun i _ j _ => negRamp_integrable (a i) (a j))
  have heq : ∑ i ∈ s, ∑ j ∈ s, c i * c j * (|a i| + |a j| - |a i - a j|)
      = 2 * (∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, posRamp (a i) y * posRamp (a j) y ∂volume))
        + 2 * (∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, negRamp (a i) y * negRamp (a j) y ∂volume)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [posRamp_integral, negRamp_integral, kernel_eq]
    ring
  rw [heq]
  linarith

/-! ### From the pointwise kernel to `zCov` -/

/-- Linearity of the interval integral over a finite double sum, combined with a pointwise (in
`x`) nonnegativity hypothesis, gives nonnegativity of the double sum of interval integrals. -/
private lemma sum_intervalIntegral_nonneg {ι : Type*} (s : Finset ι) (g : ι → ι → ℝ → ℝ)
    (hInt : ∀ i ∈ s, ∀ j ∈ s, IntervalIntegrable (g i j) volume 0 1)
    (hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, g i j x) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, ∫ x in (0:ℝ)..1, g i j x := by
  have step1 : ∀ i ∈ s, ∑ j ∈ s, ∫ x in (0:ℝ)..1, g i j x
      = ∫ x in (0:ℝ)..1, ∑ j ∈ s, g i j x :=
    fun i hi => (intervalIntegral.integral_finsetSum fun j hj => hInt i hi j hj).symm
  have hFi : ∀ i ∈ s, IntervalIntegrable (fun x => ∑ j ∈ s, g i j x) volume 0 1 := by
    intro i hi
    have heq : (fun x => ∑ j ∈ s, g i j x) = ∑ j ∈ s, g i j := by
      funext x; rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum s fun j hj => hInt i hi j hj
  have step2 : ∑ i ∈ s, ∑ j ∈ s, ∫ x in (0:ℝ)..1, g i j x
      = ∫ x in (0:ℝ)..1, ∑ i ∈ s, ∑ j ∈ s, g i j x := by
    rw [Finset.sum_congr rfl step1, ← intervalIntegral.integral_finsetSum hFi]
  rw [step2]
  exact intervalIntegral.integral_nonneg zero_le_one hpt

/-- The general form of `zCovPSD`: for any index type `ι`, `zCov ∘ φ` is a PSD kernel on any
finite family of interval-integrable functions `φ i : ℝ → ℝ`. -/
private lemma zCov_psdOn_aux {ι : Type*} (F : Finset ι) (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ F, IntervalIntegrable (φ i) volume 0 1) :
    PSDOn F (fun i j => zCov (φ i) (φ j)) := by
  rw [PSDOn, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun c => ?_⟩
  · simp only [Matrix.of_apply, star_trivial]
    exact zCov_comm (φ (j : ι)) (φ (i : ι))
  · have hsum : star c ⬝ᵥ ((Matrix.of fun i j : F => zCov (φ i) (φ j)) *ᵥ c)
        = ∑ i : F, ∑ j : F, c i * c j * zCov (φ (i : ι)) (φ (j : ι)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    set g : F → F → ℝ → ℝ := fun i j x => c i * c j *
      (|φ (i : ι) x| + |φ (j : ι) x| - |φ (i : ι) x - φ (j : ι) x|) with hg_def
    have hInt : ∀ i ∈ (Finset.univ : Finset F), ∀ j ∈ (Finset.univ : Finset F),
        IntervalIntegrable (g i j) volume 0 1 := by
      intro i _ j _
      exact (((hφ (i : ι) i.2).abs.add (hφ (j : ι) j.2).abs).sub
        (((hφ (i : ι) i.2).sub (hφ (j : ι) j.2)).abs)).const_mul (c i * c j)
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ∑ i : F, ∑ j : F, g i j x :=
      fun x _ => kernel_sum_nonneg Finset.univ (fun i : F => φ (i : ι) x) c
    have hnn := sum_intervalIntegral_nonneg (Finset.univ : Finset F) g hInt hpt
    have hrw : ∑ i : F, ∑ j : F, c i * c j * zCov (φ (i : ι)) (φ (j : ι))
        = π * ∑ i : F, ∑ j : F, ∫ x in (0 : ℝ)..1, g i j x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show c i * c j * zCov (φ (i : ι)) (φ (j : ι)) = π * ∫ x in (0 : ℝ)..1, g i j x
      unfold zCov
      simp only [hg_def]
      rw [intervalIntegral.integral_const_mul]
      ring
    rw [hrw]
    exact mul_nonneg Real.pi_pos.le hnn

/-! ### Main theorem and corollaries -/

/-- `zCov` is positive semidefinite on every finite family of interval-integrable functions. -/
theorem zCovPSD : Blueprint.ZCovPSD := by
  intro F hF
  exact zCov_psdOn_aux F id hF

/-- Every `f ∈ V n` is interval integrable on `[0,1]`: it is affine, hence continuous, on each of
the finitely many closed mesh intervals `[k/16ⁿ, (k+1)/16ⁿ]`, `k < 16ⁿ`, which cover `[0,1]`. -/
theorem mem_V_intervalIntegrable {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) :
    IntervalIntegrable f volume 0 1 := by
  obtain ⟨-, -, -, hpieces⟩ := hf
  have hNpos : (0:ℝ) < (16:ℝ) ^ n := by positivity
  set a : ℕ → ℝ := fun k => (k : ℝ) / (16:ℝ) ^ n with ha_def
  have hstep : ∀ k, k < 16 ^ n → IntervalIntegrable f volume (a k) (a (k + 1)) := by
    intro k hk
    obtain ⟨α, β, hαβ⟩ := hpieces k hk
    have hle : a k ≤ a (k + 1) := by
      have hcast : (k:ℝ) ≤ ((k + 1 : ℕ):ℝ) := by exact_mod_cast Nat.le_succ k
      exact div_le_div_of_nonneg_right hcast hNpos.le
    have hci : IntervalIntegrable (fun x => α * x + β) volume (a k) (a (k + 1)) :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
    refine hci.congr fun x hx => ?_
    have hx' : x ∈ Set.Icc (a k) (a (k + 1)) := (Set.uIcc_of_le hle ▸ Set.uIoc_subset_uIcc) hx
    have haux : a (k + 1) = ((k:ℝ) + 1) / (16:ℝ) ^ n := by
      simp only [ha_def]; push_cast; ring
    have hx'' : x ∈ Set.Icc ((k:ℝ) / (16:ℝ) ^ n) (((k:ℝ) + 1) / (16:ℝ) ^ n) := by
      rw [← haux]; exact hx'
    exact (hαβ x hx'').symm
  have htrans := IntervalIntegrable.trans_iterate hstep
  have ha0 : a 0 = 0 := by simp [ha_def]
  have haN : a (16 ^ n) = 1 := by
    simp only [ha_def]
    push_cast
    exact div_self hNpos.ne'
  rwa [ha0, haN] at htrans

/-- Specialization of `zCovPSD` to finite subfamilies of `V n`. -/
theorem zCovPSD_V (n : ℕ) (F : Finset (V n)) : PSDOn F (fun f g => zCov f g) :=
  zCov_psdOn_aux F (fun f => (f : ℝ → ℝ)) fun f _ => mem_V_intervalIntegrable f.2

end LQGDimension
