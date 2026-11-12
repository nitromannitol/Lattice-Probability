/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51Aux1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.CircCovDominated
import LatticeProb.Bonanno.LQGDimension.LFPP.GraphCov

/-!
# Lemma 5.1, auxiliary file 1: the band bilinear form on segment combinations

For `0 < a ≤ b` we put `bandForm a b c c' = ∫_a^b gaussPair t c c' dt / t`.  On point
combinations it is the band covariance `bandCov a b` (`bandForm_pt_pt`), it is bilinear
(`bandForm_sub_left`, …), symmetric and positive semidefinite (`bandForm_self_nonneg`), hence
satisfies Cauchy–Schwarz (`bandForm_two_mul_le`, `abs_bandForm_le`).  For zero-mass `c` and
nondegenerate `c'` the log kernel splits into the three scale ranges `(0,a]`, `(a,b]`, `(b,∞)`
(`logCov_split`), and `bandForm a b m m ≤ logCov m m` (`bandForm_le_logCov`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

open Blueprint.Draft HeatKernel

/-! ## Weighted double sums -/

/-- The weighted double sum `Σ_p Σ_p' w_p w_p' K(seg_p, seg_p')`. -/
def dsum (K : ℂ × ℂ → ℂ × ℂ → ℝ) (c c' : SegComb) : ℝ :=
  (c.map fun p => (c'.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum).sum

/-- The heat kernel between two segments at scale `t`. -/
def hk (t : ℝ) (e e' : ℂ × ℂ) : ℝ := pairHeat e.1 e.2 e'.1 e'.2 t

lemma gaussPair_eq_dsum (t : ℝ) (c c' : SegComb) : gaussPair t c c' = dsum (hk t) c c' := rfl

lemma logCov_eq_dsum (c c' : SegComb) :
    c.logCov c' = dsum (fun e e' => segLogPair e.1 e.2 e'.1 e'.2) c c' := rfl

section Dsum

variable (K : ℂ × ℂ → ℂ × ℂ → ℝ)

lemma dsum_cons_left (p : ℝ × ℂ × ℂ) (c e : SegComb) :
    dsum K (p :: c) e = (e.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum + dsum K c e := by
  simp [dsum]

lemma dsum_append_left (c d e : SegComb) : dsum K (c ++ d) e = dsum K c e + dsum K d e := by
  simp [dsum, List.map_append, List.sum_append]

lemma dsum_append_right (c d e : SegComb) : dsum K c (d ++ e) = dsum K c d + dsum K c e := by
  induction c with
  | nil => simp [dsum]
  | cons p c ih =>
    rw [dsum_cons_left, dsum_cons_left, dsum_cons_left, ih, List.map_append, List.sum_append]
    ring

lemma dsum_neg_left (c e : SegComb) :
    dsum K (c.map fun p => (-p.1, p.2)) e = -dsum K c e := by
  induction c with
  | nil => simp [dsum]
  | cons p c ih =>
    rw [List.map_cons, dsum_cons_left, dsum_cons_left, ih]
    simp only [neg_mul]
    rw [GraphCov.list_sum_map_neg']
    ring

lemma dsum_neg_right (c e : SegComb) :
    dsum K c (e.map fun p => (-p.1, p.2)) = -dsum K c e := by
  induction c with
  | nil => simp [dsum]
  | cons p c ih =>
    rw [dsum_cons_left, dsum_cons_left, ih, List.map_map]
    have : (e.map ((fun p' : ℝ × ℂ × ℂ => p.1 * p'.1 * K p.2 p'.2) ∘
        fun p : ℝ × ℂ × ℂ => (-p.1, p.2))).sum =
        -(e.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum := by
      rw [← GraphCov.list_sum_map_neg']
      congr 1
      refine List.map_congr_left (fun p' _ => ?_)
      simp only [Function.comp]
      ring
    rw [this]; ring

lemma dsum_sub_left (c d e : SegComb) : dsum K (c.sub d) e = dsum K c e - dsum K d e := by
  unfold SegComb.sub
  rw [dsum_append_left, dsum_neg_left]
  ring

lemma dsum_sub_right (c d e : SegComb) : dsum K c (d.sub e) = dsum K c d - dsum K c e := by
  unfold SegComb.sub
  rw [dsum_append_right, dsum_neg_right]
  ring

lemma list_sum_map_mul_left' {α : Type*} (l : List α) (r : ℝ) (F : α → ℝ) :
    (l.map fun a => r * F a).sum = r * (l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma dsum_smul_left (r : ℝ) (c e : SegComb) : dsum K (SegComb.smul r c) e = r * dsum K c e := by
  induction c with
  | nil => simp [dsum, SegComb.smul]
  | cons p c ih =>
    have h1 : SegComb.smul r (p :: c) = (r * p.1, p.2) :: SegComb.smul r c := rfl
    rw [h1, dsum_cons_left, dsum_cons_left, ih]
    have : (e.map fun p' : ℝ × ℂ × ℂ => (r * p.1, p.2).1 * p'.1 * K (r * p.1, p.2).2 p'.2).sum =
        r * (e.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum := by
      rw [← list_sum_map_mul_left']
      congr 1
      refine List.map_congr_left (fun p' _ => ?_)
      ring
    rw [this]; ring

lemma dsum_smul_right (r : ℝ) (c e : SegComb) : dsum K c (SegComb.smul r e) = r * dsum K c e := by
  induction c with
  | nil => simp [dsum]
  | cons p c ih =>
    rw [dsum_cons_left, dsum_cons_left, ih]
    unfold SegComb.smul
    rw [List.map_map]
    have : (e.map ((fun p' : ℝ × ℂ × ℂ => p.1 * p'.1 * K p.2 p'.2) ∘
        fun p : ℝ × ℂ × ℂ => (r * p.1, p.2))).sum =
        r * (e.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum := by
      rw [← list_sum_map_mul_left']
      congr 1
      refine List.map_congr_left (fun p' _ => ?_)
      simp only [Function.comp]
      ring
    rw [this]; ring

/-- Total absolute weight. -/
def wsum (c : SegComb) : ℝ := (c.map fun p => |p.1|).sum

lemma wsum_nonneg (c : SegComb) : 0 ≤ wsum c := by
  unfold wsum
  induction c with
  | nil => simp
  | cons p c ih => simp only [List.map_cons, List.sum_cons]; exact add_nonneg (abs_nonneg _) ih

lemma abs_inner_le {B : ℝ} (hK : ∀ e e', |K e e'| ≤ B) (w : ℝ) (q : ℂ × ℂ) (e : SegComb) :
    |(e.map fun p' => w * p'.1 * K q p'.2).sum| ≤ |w| * wsum e * B := by
  induction e with
  | nil => simp [wsum]
  | cons p' e ih =>
    simp only [List.map_cons, List.sum_cons, wsum] at ih ⊢
    have h1 : |w * p'.1 * K q p'.2| ≤ |w| * |p'.1| * B := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hK _ _) (by positivity)
    calc |w * p'.1 * K q p'.2 + (e.map fun p' => w * p'.1 * K q p'.2).sum|
        ≤ |w * p'.1 * K q p'.2| + |(e.map fun p' => w * p'.1 * K q p'.2).sum| := abs_add_le _ _
      _ ≤ |w| * |p'.1| * B + |w| * (e.map fun p => |p.1|).sum * B := add_le_add h1 ih
      _ = |w| * (|p'.1| + (e.map fun p => |p.1|).sum) * B := by ring

lemma abs_dsum_le {B : ℝ} (hK : ∀ e e', |K e e'| ≤ B) (c e : SegComb) :
    |dsum K c e| ≤ wsum c * wsum e * B := by
  induction c with
  | nil => simp [dsum, wsum]
  | cons p c ih =>
    rw [dsum_cons_left]
    have h1 := abs_inner_le K hK p.1 p.2 e
    have e1 : wsum (p :: c) = |p.1| + wsum c := by simp [wsum]
    rw [e1]
    calc |(e.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum + dsum K c e|
        ≤ |(e.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum| + |dsum K c e| := abs_add_le _ _
      _ ≤ |p.1| * wsum e * B + wsum c * wsum e * B := add_le_add h1 ih
      _ = (|p.1| + wsum c) * wsum e * B := by ring

end Dsum

/-! ## Measurability and bounds for `gaussPair` -/

lemma pairHeat_nonneg (a b a' b' : ℂ) (t : ℝ) : 0 ≤ pairHeat a b a' b' t := by
  unfold pairHeat
  exact intervalIntegral.integral_nonneg zero_le_one fun s _ =>
    intervalIntegral.integral_nonneg zero_le_one fun s' _ => (Real.exp_pos _).le

lemma pairHeat_le_one (a b a' b' : ℂ) (t : ℝ) : pairHeat a b a' b' t ≤ 1 := by
  rw [pairHeat_eq]
  have hint := integrable_exp_heat unitSq (continuous_segDist a b a' b').measurable t
  calc ∫ q, Real.exp (-segDist a b a' b' q ^ 2 / (4 * t ^ 2)) ∂unitSq
      ≤ ∫ _q, (1 : ℝ) ∂unitSq := by
        refine integral_mono hint (integrable_const 1) fun q => ?_
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)
    _ = 1 := by rw [integral_const, unitSq_real_univ, one_smul]

lemma abs_hk_le (t : ℝ) (e e' : ℂ × ℂ) : |hk t e e'| ≤ 1 := by
  unfold hk
  rw [abs_of_nonneg (pairHeat_nonneg _ _ _ _ _)]
  exact pairHeat_le_one _ _ _ _ _

lemma abs_gaussPair_le (t : ℝ) (c c' : SegComb) : |gaussPair t c c'| ≤ wsum c * wsum c' := by
  have := abs_dsum_le (hk t) (abs_hk_le t) c c'
  rwa [mul_one] at this

lemma measurable_pairHeat (a b a' b' : ℂ) : Measurable (pairHeat a b a' b') := by
  have e : pairHeat a b a' b' =
      fun t => ∫ q, Real.exp (-segDist a b a' b' q ^ 2 / (4 * t ^ 2)) ∂unitSq :=
    funext (pairHeat_eq a b a' b')
  rw [e]
  have hs := (continuous_segDist a b a' b').measurable
  have hm : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      Real.exp (-segDist a b a' b' p.2 ^ 2 / (4 * p.1 ^ 2))) := by
    have h1 : Measurable (fun p : ℝ × (ℝ × ℝ) => segDist a b a' b' p.2) :=
      hs.comp measurable_snd
    exact Real.measurable_exp.comp ((h1.pow_const 2).neg.div
      ((measurable_fst.pow_const 2).const_mul 4))
  have : SFinite unitSq := by unfold unitSq; infer_instance
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := unitSq)).measurable

lemma measurable_list_sum {α : Type*} (l : List α) (F : α → ℝ → ℝ)
    (hF : ∀ a ∈ l, Measurable (F a)) : Measurable fun t => (l.map fun a => F a t).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (by simp)).add (ih fun b hb => hF b (by simp [hb]))

lemma measurable_gaussPair (c c' : SegComb) : Measurable fun t => gaussPair t c c' := by
  show Measurable fun t => (c.map fun p => (c'.map fun p' => p.1 * p'.1 * hk t p.2 p'.2).sum).sum
  refine measurable_list_sum c _ fun p _ => measurable_list_sum c' _ fun p' _ => ?_
  exact (measurable_pairHeat _ _ _ _).const_mul _

lemma intervalIntegrable_gp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c c' : SegComb) :
    IntervalIntegrable (fun t => gaussPair t c c' / t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hw : 0 ≤ wsum c * wsum c' := mul_nonneg (wsum_nonneg c) (wsum_nonneg c')
  refine Measure.integrableOn_of_bounded (M := wsum c * wsum c' / a) (by simp)
    ((measurable_gaussPair c c').div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ha.trans ht.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
  calc |gaussPair t c c'| / t ≤ wsum c * wsum c' / t := by
        gcongr; exact abs_gaussPair_le t c c'
    _ ≤ wsum c * wsum c' / a := by gcongr; exact ht.1.le

lemma gaussPair_self_nonneg (t : ℝ) (c : SegComb) : 0 ≤ gaussPair t c c := by
  have := CircDom.gaussPair_quadForm_nonneg ({()} : Finset Unit) (fun _ => c) (fun _ => 1) t
  simpa using this

/-! ## The band form -/

/-- `∫_a^b gaussPair t c c' dt/t`: the band-limited covariance of two segment combinations. -/
def bandForm (a b : ℝ) (c c' : SegComb) : ℝ := ∫ t in a..b, gaussPair t c c' / t

section Band

variable {a b : ℝ}

lemma bandForm_sub_left (ha : 0 < a) (hab : a ≤ b) (c d e : SegComb) :
    bandForm a b (c.sub d) e = bandForm a b c e - bandForm a b d e := by
  unfold bandForm
  rw [← intervalIntegral.integral_sub (intervalIntegrable_gp ha hab c e)
    (intervalIntegrable_gp ha hab d e)]
  congr 1; funext t
  rw [gaussPair_eq_dsum, gaussPair_eq_dsum, gaussPair_eq_dsum, dsum_sub_left]; ring

lemma bandForm_sub_right (ha : 0 < a) (hab : a ≤ b) (c d e : SegComb) :
    bandForm a b c (d.sub e) = bandForm a b c d - bandForm a b c e := by
  unfold bandForm
  rw [← intervalIntegral.integral_sub (intervalIntegrable_gp ha hab c d)
    (intervalIntegrable_gp ha hab c e)]
  congr 1; funext t
  rw [gaussPair_eq_dsum, gaussPair_eq_dsum, gaussPair_eq_dsum, dsum_sub_right]; ring

lemma bandForm_smul_left (r : ℝ) (c e : SegComb) :
    bandForm a b (SegComb.smul r c) e = r * bandForm a b c e := by
  unfold bandForm
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t
  rw [gaussPair_eq_dsum, gaussPair_eq_dsum, dsum_smul_left]; ring

lemma bandForm_smul_right (r : ℝ) (c e : SegComb) :
    bandForm a b c (SegComb.smul r e) = r * bandForm a b c e := by
  unfold bandForm
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t
  rw [gaussPair_eq_dsum, gaussPair_eq_dsum, dsum_smul_right]; ring

lemma bandForm_comm (c e : SegComb) : bandForm a b c e = bandForm a b e c := by
  unfold bandForm
  congr 1; funext t
  rw [CircDom.gaussPair_comm]

lemma bandForm_self_nonneg (ha : 0 ≤ a) (hab : a ≤ b) (c : SegComb) : 0 ≤ bandForm a b c c :=
  intervalIntegral.integral_nonneg hab fun t ht =>
    div_nonneg (gaussPair_self_nonneg t c) (ha.trans ht.1)

/-- Cauchy–Schwarz in the form `2 B(c,d) - B(d,d) ≤ B(c,c)`. -/
lemma bandForm_two_mul_le (ha : 0 < a) (hab : a ≤ b) (c d : SegComb) :
    2 * bandForm a b c d - bandForm a b d d ≤ bandForm a b c c := by
  have h := bandForm_self_nonneg ha.le hab (c.sub d)
  rw [bandForm_sub_left ha hab, bandForm_sub_right ha hab, bandForm_sub_right ha hab,
    bandForm_comm (a := a) (b := b) d c] at h
  linarith

lemma bandForm_sq_le (ha : 0 < a) (hab : a ≤ b) (c d : SegComb) :
    bandForm a b c d ^ 2 ≤ bandForm a b c c * bandForm a b d d := by
  have key : ∀ x : ℝ, 0 ≤ bandForm a b d d * (x * x) + (-2 * bandForm a b c d) * x +
      bandForm a b c c := by
    intro x
    have h := bandForm_self_nonneg ha.le hab (c.sub (SegComb.smul x d))
    rw [bandForm_sub_left ha hab, bandForm_sub_right ha hab, bandForm_sub_right ha hab,
      bandForm_smul_right, bandForm_smul_left, bandForm_smul_left, bandForm_smul_right,
      bandForm_comm (a := a) (b := b) d c] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

/-- Cauchy–Schwarz: `|B(c,d)| ≤ √B(c,c) √B(d,d)`. -/
lemma abs_bandForm_le (ha : 0 < a) (hab : a ≤ b) (c d : SegComb) :
    |bandForm a b c d| ≤ √(bandForm a b c c) * √(bandForm a b d d) := by
  rw [← Real.sqrt_mul (bandForm_self_nonneg ha.le hab c)]
  exact Real.abs_le_sqrt (bandForm_sq_le ha hab c d)

end Band

/-! ## Point combinations -/

/-- The unit point mass at `p`, as a degenerate segment. -/
def pt (p : ℂ) : SegComb := [(1, p, p)]

lemma pairHeat_pt (p q : ℂ) (t : ℝ) :
    pairHeat p p q q t = Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2)) := by
  simp [pairHeat]

lemma gaussPair_pt_pt (t : ℝ) (p q : ℂ) :
    gaussPair t (pt p) (pt q) = Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2)) := by
  simp [gaussPair_eq_dsum, dsum, pt, hk, pairHeat_pt]

lemma bandForm_pt_pt (a b : ℝ) (p q : ℂ) : bandForm a b (pt p) (pt q) = bandCov a b p q := by
  unfold bandForm bandCov
  congr 1; funext t
  rw [gaussPair_pt_pt]

lemma mass_pt (p : ℂ) : (pt p).mass = 1 := by simp [pt, SegComb.mass]

lemma mass_sub (c d : SegComb) : (c.sub d).mass = c.mass - d.mass := by
  unfold SegComb.sub SegComb.mass
  rw [List.map_append, List.sum_append, List.map_map]
  have : ((d.map ((fun p : ℝ × ℂ × ℂ => p.1) ∘ fun p : ℝ × ℂ × ℂ => (-p.1, p.2))).sum) =
      -(d.map fun p => p.1).sum := by
    rw [← GraphCov.list_sum_map_neg']
    rfl
  rw [this]; ring

lemma gaussPair_dip_self (t : ℝ) (p q : ℂ) :
    gaussPair t ((pt p).sub (pt q)) ((pt p).sub (pt q)) =
      2 - 2 * Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2)) := by
  rw [gaussPair_eq_dsum, dsum_sub_left, dsum_sub_right, dsum_sub_right, ← gaussPair_eq_dsum,
    ← gaussPair_eq_dsum, ← gaussPair_eq_dsum, ← gaussPair_eq_dsum, gaussPair_pt_pt,
    gaussPair_pt_pt, gaussPair_pt_pt, gaussPair_pt_pt, norm_sub_rev q p]
  simp only [sub_self, norm_zero]
  norm_num
  ring

/-- The band variance of a point dipole is at most `|p-q|² log(b/a) / (2a²)`. -/
lemma bandForm_dip_self_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p q : ℂ) :
    bandForm a b ((pt p).sub (pt q)) ((pt p).sub (pt q)) ≤
      ‖p - q‖ ^ 2 / (2 * a ^ 2) * Real.log (b / a) := by
  unfold bandForm
  simp_rw [gaussPair_dip_self]
  have hb : 0 < b := ha.trans_le hab
  have hint2 : IntervalIntegrable (fun t : ℝ => ‖p - q‖ ^ 2 / (2 * a ^ 2) * t⁻¹) volume a b := by
    refine IntervalIntegrable.const_mul ?_ _
    refine (continuousOn_inv₀.mono ?_).intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (ha.trans_le ht.1).ne'
  have hint1 : IntervalIntegrable (fun t : ℝ => (2 - 2 * Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2))) / t)
      volume a b := by
    have h := intervalIntegrable_gp ha hab ((pt p).sub (pt q)) ((pt p).sub (pt q))
    simp_rw [gaussPair_dip_self] at h
    exact h
  calc ∫ t in a..b, (2 - 2 * Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2))) / t
      ≤ ∫ t in a..b, ‖p - q‖ ^ 2 / (2 * a ^ 2) * t⁻¹ := by
        refine intervalIntegral.integral_mono_on hab hint1 hint2 fun t ht => ?_
        have ht0 : 0 < t := ha.trans_le ht.1
        have hx : 0 ≤ ‖p - q‖ ^ 2 / (4 * t ^ 2) := by positivity
        have h1 : 1 - ‖p - q‖ ^ 2 / (4 * t ^ 2) ≤ Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2)) := by
          have := Real.add_one_le_exp (-‖p - q‖ ^ 2 / (4 * t ^ 2))
          rw [neg_div] at this ⊢
          linarith
        have h2 : (2 - 2 * Real.exp (-‖p - q‖ ^ 2 / (4 * t ^ 2))) ≤ ‖p - q‖ ^ 2 / (2 * t ^ 2) := by
          have : ‖p - q‖ ^ 2 / (2 * t ^ 2) = 2 * (‖p - q‖ ^ 2 / (4 * t ^ 2)) := by
            field_simp; ring
          rw [this]; linarith
        have h3 : ‖p - q‖ ^ 2 / (2 * t ^ 2) ≤ ‖p - q‖ ^ 2 / (2 * a ^ 2) := by
          gcongr; exact ht.1
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (h2.trans h3) (inv_nonneg.2 ht0.le)
    _ = ‖p - q‖ ^ 2 / (2 * a ^ 2) * Real.log (b / a) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]

/-! ## Splitting the log kernel by scales -/

lemma logCov_split {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c c' : SegComb) (hc : c.mass = 0)
    (hc' : c'.Nondeg) :
    c.logCov c' = (∫ t in Ioc 0 a, gaussPair t c c' / t) + bandForm a b c c' +
      ∫ t in Ioi b, gaussPair t c c' / t := by
  obtain ⟨hint, heq⟩ := gaussPair_heatRep c c' hc hc'
  rw [heq, bandForm, intervalIntegral.integral_of_le hab]
  have h1 : Ioi (0:ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have h2 : Ioi a = Ioc a b ∪ Ioi b := (Ioc_union_Ioi_eq_Ioi hab).symm
  have hsub1 : Ioc 0 a ⊆ Ioi (0:ℝ) := fun t ht => ht.1
  have hsub2 : Ioi a ⊆ Ioi (0:ℝ) := fun t ht => ha.trans ht
  have hsub3 : Ioc a b ⊆ Ioi (0:ℝ) := fun t ht => ha.trans ht.1
  have hsub4 : Ioi b ⊆ Ioi (0:ℝ) := fun t ht => (ha.trans_le hab).trans ht
  have hd1 : Disjoint (Ioc 0 a) (Ioi a) :=
    Set.disjoint_left.2 fun t ht ht' => (not_lt.2 ht.2) ht'
  have hd2 : Disjoint (Ioc a b) (Ioi b) :=
    Set.disjoint_left.2 fun t ht ht' => (not_lt.2 ht.2) ht'
  rw [h1, setIntegral_union hd1 measurableSet_Ioi (hint.mono_set hsub1) (hint.mono_set hsub2),
    h2, setIntegral_union hd2 measurableSet_Ioi (hint.mono_set hsub3) (hint.mono_set hsub4)]
  ring

lemma bandForm_le_logCov {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (m : SegComb) (hm : m.mass = 0)
    (hn : m.Nondeg) : bandForm a b m m ≤ m.logCov m := by
  rw [logCov_split ha hab m m hm hn]
  have h1 : 0 ≤ ∫ t in Ioc 0 a, gaussPair t m m / t :=
    setIntegral_nonneg measurableSet_Ioc fun t ht => div_nonneg (gaussPair_self_nonneg t m) ht.1.le
  have h2 : 0 ≤ ∫ t in Ioi b, gaussPair t m m / t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      div_nonneg (gaussPair_self_nonneg t m) ((ha.le.trans hab).trans ht.le)
  linarith

/-! ## Finite point combinations -/

/-- The point combination `Σ_{k ∈ I} α_k δ_{P_k}`. -/
def ptComb {ι : Type*} (I : Finset ι) (α : ι → ℝ) (P : ι → ℂ) : SegComb :=
  I.toList.map fun k => (α k, P k, P k)

lemma dsum_ptComb_left (K : ℂ × ℂ → ℂ × ℂ → ℝ) {ι : Type*} (I : Finset ι) (α : ι → ℝ)
    (P : ι → ℂ) (e : SegComb) :
    dsum K (ptComb I α P) e = ∑ k ∈ I, α k * dsum K (pt (P k)) e := by
  unfold dsum ptComb pt
  rw [List.map_map, ← Finset.sum_map_toList]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    one_mul]
  rw [← list_sum_map_mul_left']
  congr 1
  refine List.map_congr_left fun p' _ => ?_
  ring

lemma dsum_pt_ptComb (K : ℂ × ℂ → ℂ × ℂ → ℝ) {ι : Type*} (p : ℂ) (J : Finset ι) (β : ι → ℝ)
    (P : ι → ℂ) : dsum K (pt p) (ptComb J β P) = ∑ l ∈ J, β l * dsum K (pt p) (pt (P l)) := by
  unfold dsum ptComb pt
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
    List.map_map]
  rw [← Finset.sum_map_toList]
  congr 1

lemma bandForm_ptComb_left {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ι : Type*} (I : Finset ι)
    (α : ι → ℝ) (P : ι → ℂ) (e : SegComb) :
    bandForm a b (ptComb I α P) e = ∑ k ∈ I, α k * bandForm a b (pt (P k)) e := by
  unfold bandForm
  simp_rw [gaussPair_eq_dsum, dsum_ptComb_left, Finset.sum_div]
  rw [intervalIntegral.integral_finsetSum fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  · have h := (intervalIntegrable_gp ha hab (pt (P k)) e).const_mul (α k)
    refine h.congr fun t _ => ?_
    simp only [gaussPair_eq_dsum]
    ring

lemma bandForm_pt_ptComb {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ι : Type*} (p : ℂ) (J : Finset ι)
    (β : ι → ℝ) (P : ι → ℂ) :
    bandForm a b (pt p) (ptComb J β P) = ∑ l ∈ J, β l * bandCov a b p (P l) := by
  unfold bandForm
  simp_rw [gaussPair_eq_dsum, dsum_pt_ptComb, Finset.sum_div]
  rw [intervalIntegral.integral_finsetSum fun l _ => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← bandForm_pt_pt, bandForm, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; rw [gaussPair_eq_dsum]; ring
  · have h := (intervalIntegrable_gp ha hab (pt p) (pt (P l))).const_mul (β l)
    refine h.congr fun t _ => ?_
    simp only [gaussPair_eq_dsum]
    ring

lemma bandForm_ptComb_ptComb {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ι κ : Type*} (I : Finset ι)
    (α : ι → ℝ) (P : ι → ℂ) (J : Finset κ) (β : κ → ℝ) (P' : κ → ℂ) :
    bandForm a b (ptComb I α P) (ptComb J β P') =
      ∑ k ∈ I, ∑ l ∈ J, α k * β l * bandCov a b (P k) (P' l) := by
  rw [bandForm_ptComb_left ha hab]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bandForm_pt_ptComb ha hab, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end LQGDimension.L51
