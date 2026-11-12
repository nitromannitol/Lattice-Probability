/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstructionAux2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstructionAux1
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Node `B57`, auxiliary file 2: the scale-space kernel

A *triple* `q = (a, b, z) : Tri` stands for the band `(a, b]` of scales at the point `z`
(the white noise on `(a, b] × ℝ²` integrated against the heat kernel at `z`).  Its covariance
kernel is
`kap q q' = ∫_0^∞ 1_{(a,b]}(t) 1_{(a',b']}(t) e^{-|z-z'|²/(4t²)} dt/t`.

* `kap_psd`: `kap` is positive semidefinite on finite sets of triples with `a > 0`
  (Fourier representation of the Gaussian kernel).
* `kap_band`: `kap (a,b,z) (a,b,w) = bandCov a b z w`; `kap_diag`: `= log (b/a)` for `z = w`.
* `kap_split`: additivity over `(a,c] = (a,b] ∪ (b,c]`.
* `kap_eq_zero_of_le`: disjoint bands are uncorrelated.
* `kap_sim`: invariance under `t ↦ r t`, `z ↦ T z` with `|Tz - Tw| = r |z - w|`.
* `exists_gram_kap`: Gram realisation in `EuclideanSpace ℝ (Fin d)`;
  `gram_eq_sum_of_kap`: linear relations of the kernel are inherited by the Gram vectors.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.BlockCons

open Blueprint.Draft

/-! ## The Gaussian kernel is positive semidefinite -/

/-- `gK t z w = e^{-|z-w|²/(4t²)}`. -/
def gK (t : ℝ) (z w : ℂ) : ℝ := Real.exp (-‖z - w‖ ^ 2 / (4 * t ^ 2))

theorem gK_pos (t : ℝ) (z w : ℂ) : 0 < gK t z w := Real.exp_pos _

theorem gK_le_one (t : ℝ) (z w : ℂ) : gK t z w ≤ 1 := by
  rw [gK, Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

theorem gK_comm (t : ℝ) (z w : ℂ) : gK t z w = gK t w z := by
  rw [gK, gK, norm_sub_rev]

theorem integral_cos_inner_std (u : ℂ) :
    ∫ x, Real.cos ⟪x, u⟫ ∂(stdGaussian ℂ) = Real.exp (-‖u‖ ^ 2 / 2) := by
  have h := charFun_stdGaussian (E := ℂ) u
  rw [charFun_apply] at h
  have hint : Integrable (fun x : ℂ => Complex.exp (⟪x, u⟫ * Complex.I)) (stdGaussian ℂ) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h2 := integral_re hint
  rw [h] at h2
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at h2
  rw [h2, show (-(‖u‖ : ℂ) ^ 2 / 2) = ((-‖u‖ ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.exp_ofReal_re _

/-- Fourier features: `gK t z w = ∫ (cos cos + sin sin) dγ`. -/
theorem gK_eq_integral (t : ℝ) (z w : ℂ) :
    gK t z w = ∫ x, (Real.cos ((Real.sqrt 2 * t)⁻¹ * ⟪x, z⟫) *
        Real.cos ((Real.sqrt 2 * t)⁻¹ * ⟪x, w⟫) +
      Real.sin ((Real.sqrt 2 * t)⁻¹ * ⟪x, z⟫) * Real.sin ((Real.sqrt 2 * t)⁻¹ * ⟪x, w⟫))
        ∂(stdGaussian ℂ) := by
  have hfun : (fun x : ℂ => Real.cos ((Real.sqrt 2 * t)⁻¹ * ⟪x, z⟫) *
        Real.cos ((Real.sqrt 2 * t)⁻¹ * ⟪x, w⟫) +
      Real.sin ((Real.sqrt 2 * t)⁻¹ * ⟪x, z⟫) * Real.sin ((Real.sqrt 2 * t)⁻¹ * ⟪x, w⟫)) =
      fun x => Real.cos ⟪x, ((Real.sqrt 2 * t)⁻¹ : ℝ) • (z - w)⟫ := by
    funext x
    simp only [inner_smul_right, inner_sub_right, mul_sub]
    rw [Real.cos_sub]
  rw [hfun, integral_cos_inner_std, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, gK]
  congr 1
  rw [inv_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The Gaussian kernel is positive semidefinite. -/
theorem gK_quad_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) (z : ι → ℂ) (t : ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, y i * y j * gK t (z i) (z j) := by
  set c : ι → ℂ → ℝ := fun i x => Real.cos ((Real.sqrt 2 * t)⁻¹ * ⟪x, z i⟫) with hc
  set sn : ι → ℂ → ℝ := fun i x => Real.sin ((Real.sqrt 2 * t)⁻¹ * ⟪x, z i⟫) with hsn
  have hint : ∀ i j, Integrable (fun x => y i * y j * (c i x * c j x + sn i x * sn j x))
      (stdGaussian ℂ) := by
    intro i j
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by rw [hc, hsn]; fun_prop))
      (|y i| * |y j| * 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    gcongr
    calc |c i x * c j x + sn i x * sn j x| ≤ |c i x| * |c j x| + |sn i x| * |sn j x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * 1 + 1 * 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
          · exact Real.abs_sin_le_one _
          · exact Real.abs_sin_le_one _
      _ = 2 := by norm_num
  have heq : ∑ i ∈ s, ∑ j ∈ s, y i * y j * gK t (z i) (z j) =
      ∫ x, ∑ i ∈ s, ∑ j ∈ s, y i * y j * (c i x * c j x + sn i x * sn j x) ∂(stdGaussian ℂ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, gK_eq_integral]
  rw [heq]
  refine integral_nonneg fun x => ?_
  have : ∑ i ∈ s, ∑ j ∈ s, y i * y j * (c i x * c j x + sn i x * sn j x) =
      (∑ i ∈ s, y i * c i x) ^ 2 + (∑ i ∈ s, y i * sn i x) ^ 2 := by
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only
  rw [this]
  positivity

/-! ## The scale-space kernel -/

/-- Band weight `1_{(a,b]}(t)`. -/
def bw (a b t : ℝ) : ℝ := (Ioc a b).indicator (fun _ => (1 : ℝ)) t

/-- A triple `(a, b, z)`: the band `(a, b]` at the point `z`. -/
abbrev Tri := ℝ × ℝ × ℂ

/-- The scale-space kernel. -/
def kap (q q' : Tri) : ℝ :=
  ∫ t in Ioi 0, bw q.1 q.2.1 t * bw q'.1 q'.2.1 t * gK t q.2.2 q'.2.2 / t

theorem bw_nonneg (a b t : ℝ) : 0 ≤ bw a b t := by
  unfold bw; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem bw_le_one (a b t : ℝ) : bw a b t ≤ 1 := by
  unfold bw Set.indicator; split_ifs <;> norm_num

theorem bw_mul_self (a b t : ℝ) : bw a b t * bw a b t = bw a b t := by
  unfold bw Set.indicator; split_ifs <;> simp

theorem measurable_bw (a b : ℝ) : Measurable (bw a b) :=
  (measurable_const.indicator measurableSet_Ioc)

theorem measurable_gK_t (z w : ℂ) : Measurable fun t => gK t z w := by
  unfold gK; fun_prop

theorem bw_mul_div_eq_indicator (a b : ℝ) (g : ℝ → ℝ) :
    (fun t => bw a b t * g t / t) = (Ioc a b).indicator (fun t => g t / t) := by
  funext t
  by_cases ht : t ∈ Ioc a b
  · simp [bw, ht]
  · simp [bw, ht]

/-- Integrability in the scale variable of a band integrand. -/
theorem integrableOn_band {a b : ℝ} (ha : 0 < a) {H : ℝ → ℝ} (hH : Measurable H)
    (hHb : ∀ t, |H t| ≤ 1) : IntegrableOn (fun t => bw a b t * H t / t) (Ioi 0) := by
  rw [bw_mul_div_eq_indicator]
  have h1 : IntegrableOn (fun t => H t / t) (Ioc a b) := by
    refine IntegrableOn.of_bound (by simp [Real.volume_Ioc]) (hH.div measurable_id).aestronglyMeasurable
      (1 / a) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := ha.trans ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |H t| / t ≤ 1 / t := by gcongr; exact hHb t
      _ ≤ 1 / a := by gcongr; exact ht.1.le
  exact (h1.integrable_indicator measurableSet_Ioc).integrableOn

theorem integrableOn_kap {q : Tri} (hq : 0 < q.1) (q' : Tri) :
    IntegrableOn (fun t => bw q.1 q.2.1 t * bw q'.1 q'.2.1 t * gK t q.2.2 q'.2.2 / t) (Ioi 0) := by
  have := integrableOn_band (b := q.2.1) hq (H := fun t => bw q'.1 q'.2.1 t * gK t q.2.2 q'.2.2)
    ((measurable_bw _ _).mul (measurable_gK_t _ _)) (fun t => by
      rw [abs_of_nonneg (mul_nonneg (bw_nonneg _ _ _) (gK_pos _ _ _).le)]
      calc bw q'.1 q'.2.1 t * gK t q.2.2 q'.2.2 ≤ 1 * 1 :=
            mul_le_mul (bw_le_one _ _ _) (gK_le_one _ _ _) (gK_pos _ _ _).le zero_le_one
        _ = 1 := by norm_num)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only
  ring

theorem kap_comm (q q' : Tri) : kap q q' = kap q' q := by
  unfold kap
  congr 1
  funext t
  rw [gK_comm]
  ring

/-- Band covariance. -/
theorem kap_band {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z w : ℂ) :
    kap (a, b, z) (a, b, w) = bandCov a b z w := by
  unfold kap bandCov
  simp only
  simp_rw [bw_mul_self]
  rw [bw_mul_div_eq_indicator, setIntegral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le hab]
  have : Ioi (0 : ℝ) ∩ Ioc a b = Ioc a b := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨ha.trans h.1, h⟩
  rw [this]
  rfl

theorem kap_diag {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    kap (a, b, z) (a, b, z) = Real.log (b / a) := by
  rw [kap_band ha hab, bandCov]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Real.exp_zero]
  rw [← integral_one_div_of_pos ha (ha.trans_le hab)]

theorem bw_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (t : ℝ) :
    bw a c t = bw a b t + bw b c t := by
  unfold bw
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, Set.indicator_union_of_disjoint]
  exact Set.disjoint_left.2 fun x h1 h2 => absurd h2.1 (not_lt.2 h1.2)

/-- Additivity of the kernel over adjacent bands. -/
theorem kap_split {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (z : ℂ) (q' : Tri) :
    kap (a, c, z) q' = kap (a, b, z) q' + kap (b, c, z) q' := by
  unfold kap
  simp only
  rw [← integral_add (integrableOn_kap (q := (a, b, z)) ha q')
    (integrableOn_kap (q := (b, c, z)) (ha.trans_le hab) q')]
  congr 1
  funext t
  rw [bw_split hab hbc]
  ring

/-- Disjoint bands are uncorrelated. -/
theorem kap_eq_zero_of_le {q q' : Tri} (h : q.2.1 ≤ q'.1) : kap q q' = 0 := by
  unfold kap
  have : ∀ t, bw q.1 q.2.1 t * bw q'.1 q'.2.1 t = 0 := by
    intro t
    unfold bw Set.indicator
    split_ifs with h1 h2 <;> try simp
    exact absurd (h1.2.trans h) (not_le.2 h2.1)
  simp_rw [this, zero_mul, zero_div, integral_zero]

theorem kap_eq_zero_of_le' {q q' : Tri} (h : q'.2.1 ≤ q.1) : kap q q' = 0 := by
  rw [kap_comm]; exact kap_eq_zero_of_le h

/-- Similarity invariance. -/
theorem kap_sim {r : ℝ} (hr : 0 < r) (T : ℂ → ℂ) (hT : ∀ z w, ‖T z - T w‖ = r * ‖z - w‖)
    (q q' : Tri) :
    kap (r * q.1, r * q.2.1, T q.2.2) (r * q'.1, r * q'.2.1, T q'.2.2) = kap q q' := by
  unfold kap
  simp only
  set g : ℝ → ℝ := fun t => bw (r * q.1) (r * q.2.1) t * bw (r * q'.1) (r * q'.2.1) t *
    gK t (T q.2.2) (T q'.2.2) / t with hg
  have hbw : ∀ a b x : ℝ, bw (r * a) (r * b) (r * x) = bw a b x := by
    intro a b x
    unfold bw Set.indicator
    simp only [mem_Ioc, mul_lt_mul_iff_right₀ hr, mul_le_mul_iff_right₀ hr]
  have hgK : ∀ x, gK (r * x) (T q.2.2) (T q'.2.2) = gK x q.2.2 q'.2.2 := by
    intro x
    unfold gK
    rw [hT]
    congr 1
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · field_simp
  have hgx : ∀ x, g (r * x) = r⁻¹ * (bw q.1 q.2.1 x * bw q'.1 q'.2.1 x * gK x q.2.2 q'.2.2 / x) := by
    intro x
    simp only [hg, hbw, hgK]
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · field_simp
  have := integral_comp_mul_left_Ioi' g 0 hr
  rw [mul_zero] at this
  change ∫ t in Ioi 0, g t = _
  rw [← this]
  simp_rw [hgx]
  rw [integral_const_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-! ## Positive semidefiniteness and Gram realisation -/

open Matrix in
theorem kap_psd (F : Finset Tri) (hF : ∀ q ∈ F, 0 < q.1) : PSDOn F kap := by
  unfold PSDOn
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, kap_comm (j : Tri) i]
  · intro x
    simp only [star_trivial]
    have hint : ∀ i j : F, IntegrableOn
        (fun t => bw (i : Tri).1 (i : Tri).2.1 t * bw (j : Tri).1 (j : Tri).2.1 t *
          gK t (i : Tri).2.2 (j : Tri).2.2 / t) (Ioi 0) :=
      fun i j => integrableOn_kap (hF i i.2) j
    have heq : x ⬝ᵥ ((Matrix.of fun i j : F => kap i j) *ᵥ x) =
        ∫ t in Ioi 0, ∑ i : F, ∑ j : F, x i * x j *
          (bw (i : Tri).1 (i : Tri).2.1 t * bw (j : Tri).1 (j : Tri).2.1 t *
            gK t (i : Tri).2.2 (j : Tri).2.2 / t) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hint i j).const_mul _)]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, kap]
      ring
    rw [heq]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have h := gK_quad_nonneg Finset.univ (fun i : F => x i * bw (i : Tri).1 (i : Tri).2.1 t)
      (fun i : F => (i : Tri).2.2) t
    have : ∑ i : F, ∑ j : F, x i * x j *
          (bw (i : Tri).1 (i : Tri).2.1 t * bw (j : Tri).1 (j : Tri).2.1 t *
            gK t (i : Tri).2.2 (j : Tri).2.2 / t) =
        (∑ i : F, ∑ j : F, (x i * bw (i : Tri).1 (i : Tri).2.1 t) *
          (x j * bw (j : Tri).1 (j : Tri).2.1 t) * gK t (i : Tri).2.2 (j : Tri).2.2) / t := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact div_nonneg h (le_of_lt ht)

/-- Gram realisation of the kernel on a finite set of triples. -/
theorem exists_gram_kap (F : Finset Tri) (hF : ∀ q ∈ F, 0 < q.1) :
    ∃ d : ℕ, ∃ β : Tri → EuclideanSpace ℝ (Fin d), ∀ q ∈ F, ∀ q' ∈ F, ⟪β q, β q'⟫ = kap q q' := by
  obtain ⟨v, hv⟩ := exists_gram_of_psdOn F kap (kap_psd F hF)
  refine ⟨F.card, fun q => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ F.equivFin (v q), ?_⟩
  intro q hq q' hq'
  rw [LinearIsometryEquiv.inner_map_map]
  exact hv q hq q' hq'

end LQGDimension.BlockCons
