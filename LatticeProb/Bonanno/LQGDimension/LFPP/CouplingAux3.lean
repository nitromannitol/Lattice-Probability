/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.CouplingAux3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2

/-!
# Node `C36`, auxiliary file 3: the joint band/circle kernel

For `0 < ε < ρ` we define a kernel `Kc ε ρ` on `ℂ × Bool`:
`(s, false)` is the band field `G_{ε,ρ}(s)` (the point mass `δ_s` on the scales `t ∈ (ε, ρ]`),
`(s, true)` is the circle average `h_ε(s)` (the zero-mass measure `σ_{s,ε} - σ_{0,1}` on all
scales).  With `P_t(i, j)` the Gaussian-kernel pairing of the two signed measures at scale `t`
(in Fourier form), `Kc i j = ∫_0^∞ P_t(i, j) dt/t`.

* `Kc_ff`: `Kc (s,false) (s',false) = bandCov ε ρ s s'`;
* `Kc_tt`: `Kc (s,true) (s',true) = gffCircleCov ε s ε s'`;
* `Kc_psd`: `Kc` is positive semidefinite on every finite set;
* `Kc_diag_bound`: `Kc(s,f)(s,f) - 2 Kc(s,f)(s,t) + Kc(s,t)(s,t) ≤ Cb ρ` for `‖s‖ ≤ 3`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.Coupling

open HeatKernel

/-! ## 1. The band weight and the two kinds of indices -/

/-- The band weight `1_{(ε, ρ]}(t)`. -/
def bw (ε ρ t : ℝ) : ℝ := (Ioc ε ρ).indicator (fun _ => (1 : ℝ)) t

lemma bw_mul_self (ε ρ t : ℝ) : bw ε ρ t * bw ε ρ t = bw ε ρ t := by
  unfold bw Set.indicator; split_ifs <;> simp

lemma bw_of_mem {ε ρ t : ℝ} (ht : t ∈ Ioc ε ρ) : bw ε ρ t = 1 := by
  simp [bw, ht]

lemma bw_of_notMem {ε ρ t : ℝ} (ht : t ∉ Ioc ε ρ) : bw ε ρ t = 0 := by
  simp [bw, ht]

lemma bw_mul_div_eq_indicator (ε ρ : ℝ) (g : ℝ → ℝ) :
    (fun t => bw ε ρ t * g t / t) = (Ioc ε ρ).indicator (fun t => g t / t) := by
  funext t
  by_cases ht : t ∈ Ioc ε ρ
  · rw [bw_of_mem ht, Set.indicator_of_mem ht, one_mul]
  · rw [bw_of_notMem ht, Set.indicator_of_notMem ht, zero_mul, zero_div]

/-- Weight of the first measure of index `i`. -/
def wA (ε ρ t : ℝ) (i : ℂ × Bool) : ℝ := bif i.2 then 1 else bw ε ρ t

/-- Weight of the second measure of index `i`. -/
def wB (i : ℂ × Bool) : ℝ := bif i.2 then -1 else 0

/-- First measure of index `i`: `σ_{s,ε}` or `δ_s`. -/
def mA (ε : ℝ) (i : ℂ × Bool) : Measure ℂ := bif i.2 then circMeas i.1 ε else Measure.dirac i.1

/-- Second measure of index `i`: `σ_{0,1}` (or `δ_s` with weight `0`). -/
def mB (i : ℂ × Bool) : Measure ℂ := bif i.2 then circMeas 0 1 else Measure.dirac i.1

instance (ε : ℝ) (i : ℂ × Bool) : IsProbabilityMeasure (mA ε i) := by
  rcases i with ⟨a, b⟩
  cases b
  · exact (inferInstance : IsProbabilityMeasure (Measure.dirac a))
  · exact (inferInstance : IsProbabilityMeasure (circMeas a ε))

instance (i : ℂ × Bool) : IsProbabilityMeasure (mB i) := by
  rcases i with ⟨a, b⟩
  cases b
  · exact (inferInstance : IsProbabilityMeasure (Measure.dirac a))
  · exact (inferInstance : IsProbabilityMeasure (circMeas 0 1))

/-- Cosine feature of index `i` at scale `t`. -/
def cI (ε ρ t : ℝ) (i : ℂ × Bool) (ξ : ℂ) : ℝ := cL t (wA ε ρ t i) (wB i) (mA ε i) (mB i) ξ

/-- Sine feature of index `i` at scale `t`. -/
def sI (ε ρ t : ℝ) (i : ℂ × Bool) (ξ : ℂ) : ℝ := sL t (wA ε ρ t i) (wB i) (mA ε i) (mB i) ξ

/-- The scale-`t` pairing `P_t(i, j)`, in Fourier form. -/
def Pt (ε ρ t : ℝ) (i j : ℂ × Bool) : ℝ :=
  ∫ ξ, (cI ε ρ t i ξ * cI ε ρ t j ξ + sI ε ρ t i ξ * sI ε ρ t j ξ) ∂(stdGaussian ℂ)

/-- The joint kernel `Kc i j = ∫_0^∞ P_t(i, j) dt/t`. -/
def Kc (ε ρ : ℝ) (i j : ℂ × Bool) : ℝ := ∫ t in Ioi 0, Pt ε ρ t i j / t

lemma integrable_PtIntegrand (ε ρ t : ℝ) (i j : ℂ × Bool) :
    Integrable (fun ξ => cI ε ρ t i ξ * cI ε ρ t j ξ + sI ε ρ t i ξ * sI ε ρ t j ξ)
      (stdGaussian ℂ) :=
  integrable_lin t _ _ _ _ _ _ _ _

lemma Pt_eq (ε ρ t : ℝ) (i j : ℂ × Bool) :
    Pt ε ρ t i j = wA ε ρ t i * wA ε ρ t j * gPair t (mA ε i) (mA ε j) +
      wA ε ρ t i * wB j * gPair t (mA ε i) (mB j) + wB i * wA ε ρ t j * gPair t (mB i) (mA ε j) +
        wB i * wB j * gPair t (mB i) (mB j) :=
  integral_lin t _ _ _ _ _ _ _ _

lemma Pt_comm (ε ρ t : ℝ) (i j : ℂ × Bool) : Pt ε ρ t i j = Pt ε ρ t j i := by
  unfold Pt; congr 1; funext ξ; ring

lemma Kc_comm (ε ρ : ℝ) (i j : ℂ × Bool) : Kc ε ρ i j = Kc ε ρ j i := by
  unfold Kc; simp_rw [Pt_comm ε ρ _ i j]

lemma Pt_ff (ε ρ t : ℝ) (a b : ℂ) : Pt ε ρ t (a, false) (b, false) = bw ε ρ t * gK t a b := by
  rw [Pt_eq]
  simp only [wA, wB, mA, mB, Bool.cond_false]
  rw [gPair_dirac_left, integral_dirac]
  linear_combination (gK t a b) * bw_mul_self ε ρ t

lemma Pt_ft (ε ρ t : ℝ) (a b : ℂ) : Pt ε ρ t (a, false) (b, true) =
    bw ε ρ t * (gPair t (Measure.dirac a) (circMeas b ε) -
      gPair t (Measure.dirac a) (circMeas 0 1)) := by
  rw [Pt_eq]
  simp only [wA, wB, mA, mB, Bool.cond_false, Bool.cond_true]
  ring

lemma Pt_tt (ε ρ t : ℝ) (a b : ℂ) : Pt ε ρ t (a, true) (b, true) =
    gPair t (circMeas a ε) (circMeas b ε) - gPair t (circMeas a ε) (circMeas 0 1) -
      gPair t (circMeas 0 1) (circMeas b ε) + gPair t (circMeas 0 1) (circMeas 0 1) := by
  rw [Pt_eq]
  simp only [wA, wB, mA, mB, Bool.cond_true]
  ring

/-! ## 2. Integrability in the scale variable -/

lemma integrableOn_band {ε ρ : ℝ} (hε : 0 < ε) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) : IntegrableOn (fun t => bw ε ρ t * g t / t) (Ioi 0) := by
  rw [bw_mul_div_eq_indicator]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h1 : IntegrableOn (fun t => g t / t) (Ioc ε ρ) := by
    refine IntegrableOn.of_bound (by simp [Real.volume_Ioc]) (hg.div measurable_id).aestronglyMeasurable
      (M / ε) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := hε.trans ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |g t| / t ≤ M / t := div_le_div_of_nonneg_right (hM t) ht0.le
      _ ≤ M / ε := div_le_div_of_nonneg_left hM0 hε ht.1.le
  exact (h1.integrable_indicator measurableSet_Ioc).integrableOn

lemma abs_gPair_sub_gPair_le (t : ℝ) (μ ν μ' ν' : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
    |gPair t μ ν - gPair t μ' ν'| ≤ 1 := by
  have h1 := gPair_nonneg t μ ν
  have h2 := gPair_le t μ ν
  have h3 := gPair_nonneg t μ' ν'
  have h4 := gPair_le t μ' ν'
  rw [abs_le]; constructor <;> linarith

/-- The heat-representation integrand `(gPair t μ ν - e^{-1/(4t²)}) / t`. -/
def Hc (t : ℝ) (μ ν : Measure ℂ) : ℝ := (gPair t μ ν - Real.exp (-1 / (4 * t ^ 2))) / t

lemma circ_heatRep' (c c' : ℂ) (r : ℝ) {r' : ℝ} (hr' : 0 < r') :
    IntegrableOn (fun t => Hc t (circMeas c r) (circMeas c' r')) (Ioi 0) ∧
    ∫ t in Ioi 0, Hc t (circMeas c r) (circMeas c' r') = -lPair (circMeas c r) (circMeas c' r') :=
  circ_heatRep c c' r hr'

lemma Pt_tt_div (ε ρ t : ℝ) (a b : ℂ) : Pt ε ρ t (a, true) (b, true) / t =
    Hc t (circMeas a ε) (circMeas b ε) - Hc t (circMeas a ε) (circMeas 0 1) -
      Hc t (circMeas 0 1) (circMeas b ε) + Hc t (circMeas 0 1) (circMeas 0 1) := by
  rw [Pt_tt]; simp only [Hc]; ring

lemma measurable_gK_left (a b : ℂ) : Measurable fun t => gK t a b := by
  unfold gK; fun_prop

lemma integrableOn_Pt {ε : ℝ} (ρ : ℝ) (hε : 0 < ε) (i j : ℂ × Bool) :
    IntegrableOn (fun t => Pt ε ρ t i j / t) (Ioi 0) := by
  rcases i with ⟨a, _ | _⟩ <;> rcases j with ⟨b, _ | _⟩
  · have h := integrableOn_band (ρ := ρ) hε (measurable_gK_left a b) (M := 1)
      (fun t => by rw [abs_of_pos (gK_pos _ _ _)]; exact gK_le_one _ _ _)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pt_ff]
  · have h := integrableOn_band (ρ := ρ) hε
      ((measurable_gPair (Measure.dirac a) (circMeas b ε)).sub
        (measurable_gPair (Measure.dirac a) (circMeas 0 1)))
      (fun t => abs_gPair_sub_gPair_le t _ _ _ _)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pt_ft, Pi.sub_apply]
  · have h := integrableOn_band (ρ := ρ) hε
      ((measurable_gPair (Measure.dirac b) (circMeas a ε)).sub
        (measurable_gPair (Measure.dirac b) (circMeas 0 1)))
      (fun t => abs_gPair_sub_gPair_le t _ _ _ _)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pt_comm ε ρ t (a, true) (b, false), Pt_ft, Pi.sub_apply]
  · have h1 := (circ_heatRep' a b ε hε).1
    have h2 := (circ_heatRep' a 0 ε one_pos).1
    have h3 := (circ_heatRep' 0 b 1 hε).1
    have h4 := (circ_heatRep' 0 0 1 one_pos).1
    refine (((h1.sub h2).sub h3).add h4).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply, Pt_tt_div]

/-! ## 3. The two diagonal blocks -/

/-- The band block is `bandCov`. -/
theorem Kc_ff {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (a b : ℂ) :
    Kc ε ρ (a, false) (b, false) = Blueprint.Draft.bandCov ε ρ a b := by
  unfold Kc
  simp_rw [Pt_ff]
  rw [bw_mul_div_eq_indicator ε ρ (fun t => gK t a b), setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.2 (show Ioc ε ρ ⊆ Ioi 0 from fun t ht => hε.trans ht.1),
    Blueprint.Draft.bandCov,
    intervalIntegral.integral_of_le hερ]
  rfl

/-- The circle block is the circle-average covariance of the normalised GFF. -/
theorem Kc_tt {ε : ℝ} (ρ : ℝ) (hε : 0 < ε) (a b : ℂ) :
    Kc ε ρ (a, true) (b, true) = gffCircleCov ε a ε b := by
  unfold Kc
  simp_rw [Pt_tt_div]
  obtain ⟨h1, e1⟩ := circ_heatRep' a b ε hε
  obtain ⟨h2, e2⟩ := circ_heatRep' a 0 ε one_pos
  obtain ⟨h3, e3⟩ := circ_heatRep' 0 b 1 hε
  obtain ⟨h4, e4⟩ := circ_heatRep' 0 0 1 one_pos
  have k1 : IntegrableOn (fun t => Hc t (circMeas a ε) (circMeas b ε) -
      Hc t (circMeas a ε) (circMeas 0 1)) (Ioi 0) := h1.sub h2
  have k2 : IntegrableOn (fun t => Hc t (circMeas a ε) (circMeas b ε) -
      Hc t (circMeas a ε) (circMeas 0 1) - Hc t (circMeas 0 1) (circMeas b ε)) (Ioi 0) :=
    k1.sub h3
  rw [integral_add k2 h4, integral_sub k1 h3, integral_sub h1 h2, e1, e2, e3, e4,
    gffCircleCov_eq_lPair a b hε]
  ring

/-! ## 4. Positive semidefiniteness -/

lemma quad_Pt_nonneg {ι : Type*} (s : Finset ι) (x : ι → ℝ) (ε ρ t : ℝ)
    (k : ι → ℂ × Bool) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * x j * Pt ε ρ t (k i) (k j) := by
  set Φ : ι → ι → ℂ → ℝ := fun i j ξ => x i * x j *
    (cI ε ρ t (k i) ξ * cI ε ρ t (k j) ξ + sI ε ρ t (k i) ξ * sI ε ρ t (k j) ξ) with hΦ
  have hint : ∀ i j, Integrable (Φ i j) (stdGaussian ℂ) := fun i j =>
    (integrable_PtIntegrand ε ρ t (k i) (k j)).const_mul _
  have heq : ∑ i ∈ s, ∑ j ∈ s, x i * x j * Pt ε ρ t (k i) (k j) =
      ∫ ξ, ∑ i ∈ s, ∑ j ∈ s, Φ i j ξ ∂(stdGaussian ℂ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ]
    simp only
    rw [integral_const_mul, Pt]
  rw [heq]
  refine integral_nonneg fun ξ => ?_
  have : ∑ i ∈ s, ∑ j ∈ s, Φ i j ξ = (∑ i ∈ s, x i * cI ε ρ t (k i) ξ) ^ 2 +
      (∑ i ∈ s, x i * sI ε ρ t (k i) ξ) ^ 2 := by
    simp only [hΦ, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  positivity

open Matrix in
/-- **The joint kernel is positive semidefinite** on every finite set of indices. -/
theorem Kc_psd {ε : ℝ} (ρ : ℝ) (hε : 0 < ε) (F : Finset (ℂ × Bool)) : PSDOn F (Kc ε ρ) := by
  unfold PSDOn
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Kc_comm ε ρ (j : ℂ × Bool) i]
  · intro x
    simp only [star_trivial]
    have hint : ∀ i j : F, IntegrableOn (fun t => Pt ε ρ t i j / t) (Ioi 0) :=
      fun i j => integrableOn_Pt ρ hε i j
    have heq : x ⬝ᵥ ((Matrix.of fun i j : F => Kc ε ρ i j) *ᵥ x) =
        ∫ t in Ioi 0, ∑ i : F, ∑ j : F, x i * x j * (Pt ε ρ t i j / t) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hint i j).const_mul _)]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, Kc]
      ring
    rw [heq]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have h := quad_Pt_nonneg Finset.univ x ε ρ t (fun i : F => (i : ℂ × Bool))
    have : ∑ i : F, ∑ j : F, x i * x j * (Pt ε ρ t i j / t) =
        (∑ i : F, ∑ j : F, x i * x j * Pt ε ρ t i j) / t := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact div_nonneg h (le_of_lt ht)

/-! ## 5. The diagonal distance bound -/

/-- `Q_t(s) = P_t((s,f),(s,f)) - 2 P_t((s,f),(s,t)) + P_t((s,t),(s,t))`. -/
def Qd (ε ρ t : ℝ) (s : ℂ) : ℝ :=
  Pt ε ρ t (s, false) (s, false) - 2 * Pt ε ρ t (s, false) (s, true) +
    Pt ε ρ t (s, true) (s, true)

lemma gPair_dirac_self (t : ℝ) (s : ℂ) :
    gPair t (Measure.dirac s) (Measure.dirac s) = 1 := by
  rw [gPair_dirac_left, integral_dirac]; simp [gK]

lemma gPair_dirac_circ (t : ℝ) (s : ℂ) {ε : ℝ} (hε : 0 < ε) :
    gPair t (Measure.dirac s) (circMeas s ε) = Real.exp (-ε ^ 2 / (4 * t ^ 2)) := by
  rw [gPair_dirac_left]
  have : ∀ᵐ y ∂circMeas s ε, gK t s y = Real.exp (-ε ^ 2 / (4 * t ^ 2)) := by
    filter_upwards [ae_circMeas s ε] with y hy
    rw [gK, norm_sub_rev, hy, abs_of_pos hε]
  rw [integral_congr_ae this]
  simp

lemma abs_gK_sub_one_le (t : ℝ) (x y : ℂ) : |gK t x y - 1| ≤ ‖x - y‖ ^ 2 / (4 * t ^ 2) := by
  have h := abs_gK_sub_exp_le t x y 0
  simpa using h

lemma ae_norm_le_circ (c : ℂ) (r : ℝ) : ∀ᵐ x ∂circMeas c r, ‖x‖ ≤ ‖c‖ + |r| :=
  (ae_circMeas c r).mono fun _ hx => norm_le_of_circ hx

/-- Pointwise (in `t`) bound through the Fourier form: `(a + b)² ≤ 2a² + 2b²`. -/
lemma Qd_le (ε ρ t : ℝ) (s : ℂ) (hε : 0 < ε) :
    Qd ε ρ t s ≤ 2 * (bw ε ρ t * bw ε ρ t - 2 * bw ε ρ t * Real.exp (-ε ^ 2 / (4 * t ^ 2)) +
      gPair t (circMeas s ε) (circMeas s ε)) + 2 * gPair t (circMeas 0 1) (circMeas 0 1) := by
  set F : ℂ × Bool → ℂ × Bool → ℂ → ℝ := fun i j ξ =>
    cI ε ρ t i ξ * cI ε ρ t j ξ + sI ε ρ t i ξ * sI ε ρ t j ξ with hF
  have iF : ∀ i j, Integrable (F i j) (stdGaussian ℂ) := fun i j => integrable_PtIntegrand ε ρ t i j
  set u := cL t (bw ε ρ t) (-1) (Measure.dirac s) (circMeas s ε) with hu
  set v := sL t (bw ε ρ t) (-1) (Measure.dirac s) (circMeas s ε) with hv
  have hc : ∀ ξ, cI ε ρ t (s, false) ξ - cI ε ρ t (s, true) ξ = u ξ + cA t (circMeas 0 1) ξ := by
    intro ξ; simp only [hu, cI, cL, wA, wB, mA, mB, Bool.cond_false, Bool.cond_true]; ring
  have hs : ∀ ξ, sI ε ρ t (s, false) ξ - sI ε ρ t (s, true) ξ = v ξ + sA t (circMeas 0 1) ξ := by
    intro ξ; simp only [hv, sI, sL, wA, wB, mA, mB, Bool.cond_false, Bool.cond_true]; ring
  have hQ : Qd ε ρ t s = ∫ ξ, (F (s, false) (s, false) ξ - 2 * F (s, false) (s, true) ξ +
      F (s, true) (s, true) ξ) ∂(stdGaussian ℂ) := by
    have j1 : Integrable (fun ξ => 2 * F (s, false) (s, true) ξ) (stdGaussian ℂ) :=
      (iF _ _).const_mul 2
    have j2 : Integrable (fun ξ => F (s, false) (s, false) ξ - 2 * F (s, false) (s, true) ξ)
        (stdGaussian ℂ) := (iF _ _).sub j1
    rw [integral_add j2 (iF _ _), integral_sub (iF _ _) j1, integral_const_mul]
    rfl
  have iU : Integrable (fun ξ => u ξ * u ξ + v ξ * v ξ) (stdGaussian ℂ) :=
    integrable_lin t _ _ _ _ _ _ _ _
  have iB : Integrable (fun ξ => 2 * (u ξ * u ξ + v ξ * v ξ) +
      2 * fPair t (circMeas 0 1) (circMeas 0 1) ξ) (stdGaussian ℂ) :=
    (iU.const_mul 2).add ((integrable_fPair t _ _).const_mul 2)
  have hpt : ∀ ξ, F (s, false) (s, false) ξ - 2 * F (s, false) (s, true) ξ +
      F (s, true) (s, true) ξ ≤ 2 * (u ξ * u ξ + v ξ * v ξ) +
        2 * fPair t (circMeas 0 1) (circMeas 0 1) ξ := by
    intro ξ
    have e1 : F (s, false) (s, false) ξ - 2 * F (s, false) (s, true) ξ +
        F (s, true) (s, true) ξ = (cI ε ρ t (s, false) ξ - cI ε ρ t (s, true) ξ) ^ 2 +
          (sI ε ρ t (s, false) ξ - sI ε ρ t (s, true) ξ) ^ 2 := by
      simp only [hF]; ring
    rw [e1, hc, hs, fPair]
    nlinarith [sq_nonneg (u ξ - cA t (circMeas 0 1) ξ), sq_nonneg (v ξ - sA t (circMeas 0 1) ξ)]
  rw [hQ]
  have j3 : Integrable (fun ξ => F (s, false) (s, false) ξ - 2 * F (s, false) (s, true) ξ +
      F (s, true) (s, true) ξ) (stdGaussian ℂ) :=
    ((iF _ _).sub ((iF _ _).const_mul 2)).add (iF _ _)
  refine (integral_mono j3 iB hpt).trans
    (le_of_eq ?_)
  rw [integral_add (iU.const_mul 2) ((integrable_fPair t _ _).const_mul 2), integral_const_mul,
    integral_const_mul, ← gPair_eq_integral_fPair, hu, hv, integral_lin, gPair_dirac_self,
    gPair_comm t (circMeas s ε), gPair_dirac_circ t s hε]
  ring

lemma Qd_small (ε ρ t : ℝ) (s : ℂ) (hε : 0 < ε) (ht : t ≤ ε) :
    Qd ε ρ t s ≤ 2 * gPair t (circMeas s ε) (circMeas s ε) +
      2 * gPair t (circMeas 0 1) (circMeas 0 1) := by
  have h := Qd_le ε ρ t s hε
  rw [bw_of_notMem (fun h' => absurd h'.1 (not_lt.2 ht))] at h
  linarith

lemma Qd_band (ε ρ t : ℝ) (s : ℂ) (hε : 0 < ε) (ht : t ∈ Ioc ε ρ) :
    Qd ε ρ t s ≤ ε ^ 2 / t ^ 2 + 2 * gPair t (circMeas 0 1) (circMeas 0 1) := by
  have h := Qd_le ε ρ t s hε
  rw [bw_of_mem ht] at h
  have ht0 : 0 < t := hε.trans ht.1
  have hG := gPair_le t (circMeas s ε) (circMeas s ε)
  have he : 1 - ε ^ 2 / (4 * t ^ 2) ≤ Real.exp (-ε ^ 2 / (4 * t ^ 2)) := by
    have := Real.add_one_le_exp (-ε ^ 2 / (4 * t ^ 2))
    rw [neg_div] at this ⊢
    linarith
  have hq : ε ^ 2 / t ^ 2 = 4 * (ε ^ 2 / (4 * t ^ 2)) := by field_simp
  rw [hq]
  linarith

lemma Qd_large {ε ρ t : ℝ} (s : ℂ) (hε : 0 < ε) (hερ : ε < ρ) (hs : ‖s‖ ≤ 3) (ht : ρ < t) :
    Qd ε ρ t s ≤ (6 + 2 * ρ) ^ 2 / t ^ 2 := by
  have hbw : bw ε ρ t = 0 := bw_of_notMem fun h => absurd h.2 (not_le.2 ht)
  have hQ : Qd ε ρ t s = Pt ε ρ t (s, true) (s, true) := by
    rw [Qd, Pt_ff, Pt_ft, hbw]; ring
  rw [hQ, Pt_tt]
  have hR : ∀ x y : ℂ, ‖x‖ ≤ 3 + ρ → ‖y‖ ≤ 3 + ρ → |gK t x y - 1| ≤ (6 + 2 * ρ) ^ 2 / (4 * t ^ 2) := by
    intro x y hx hy
    refine (abs_gK_sub_one_le t x y).trans ?_
    have hxy : ‖x - y‖ ≤ 6 + 2 * ρ := by
      calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 6 + 2 * ρ := by linarith
    gcongr
  have h1 : ∀ᵐ x ∂circMeas s ε, ‖x‖ ≤ 3 + ρ := by
    filter_upwards [ae_norm_le_circ s ε] with x hx
    rw [abs_of_pos hε] at hx; linarith
  have h0 : ∀ᵐ x ∂circMeas 0 1, ‖x‖ ≤ 3 + ρ := by
    filter_upwards [ae_norm_le_circ 0 1] with x hx
    simp only [norm_zero, abs_one, zero_add] at hx; linarith [hε.trans hερ]
  have b1 := abs_gPair_sub_le h1 h1 hR
  have b2 := abs_gPair_sub_le h1 h0 hR
  have b3 := abs_gPair_sub_le h0 h1 hR
  have b4 := abs_gPair_sub_le h0 h0 hR
  have hq : (6 + 2 * ρ) ^ 2 / t ^ 2 = 4 * ((6 + 2 * ρ) ^ 2 / (4 * t ^ 2)) := by
    have : t ≠ 0 := (lt_trans (hε.trans hερ) ht).ne'
    field_simp
  rw [hq]
  rw [abs_le] at b1 b2 b3 b4
  linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]

/-- The uniform constant of (3.6). -/
def Cb (ρ : ℝ) : ℝ := 6 + 4 * (2 * ρ ^ 2 + 1 / (2 * ρ ^ 2)) + (6 + 2 * ρ) ^ 2 / (2 * ρ ^ 2)

/-- **Uniform bound for the diagonal distance** `‖k_s - b_s‖²`. -/
theorem Kc_diag_bound {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (s : ℂ) (hs : ‖s‖ ≤ 3) :
    Kc ε ρ (s, false) (s, false) - 2 * Kc ε ρ (s, false) (s, true) + Kc ε ρ (s, true) (s, true)
      ≤ Cb ρ := by
  have hρ : 0 < ρ := hε.trans hερ
  have i1 := integrableOn_Pt ρ hε (s, false) (s, false)
  have i2 := integrableOn_Pt ρ hε (s, false) (s, true)
  have i3 := integrableOn_Pt ρ hε (s, true) (s, true)
  have hQint : IntegrableOn (fun t => Qd ε ρ t s / t) (Ioi 0) := by
    refine ((i1.sub (i2.const_mul 2)).add i3).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply, Qd]
    ring
  have hK : Kc ε ρ (s, false) (s, false) - 2 * Kc ε ρ (s, false) (s, true) +
      Kc ε ρ (s, true) (s, true) = ∫ t in Ioi 0, Qd ε ρ t s / t := by
    have j1 : IntegrableOn (fun t => 2 * (Pt ε ρ t (s, false) (s, true) / t)) (Ioi 0) :=
      i2.const_mul 2
    have j2 : IntegrableOn (fun t => Pt ε ρ t (s, false) (s, false) / t -
        2 * (Pt ε ρ t (s, false) (s, true) / t)) (Ioi 0) := i1.sub j1
    have hfun : ∀ t, Qd ε ρ t s / t = Pt ε ρ t (s, false) (s, false) / t -
        2 * (Pt ε ρ t (s, false) (s, true) / t) + Pt ε ρ t (s, true) (s, true) / t := by
      intro t; simp only [Qd]; ring
    simp_rw [hfun]
    rw [integral_add j2 i3, integral_sub i1 j1, integral_const_mul]
    rfl
  rw [hK]
  -- split the scale axis at `ε` and `ρ`
  have hsplit : ∫ t in Ioi 0, Qd ε ρ t s / t = (∫ t in Ioc 0 ε, Qd ε ρ t s / t) +
      ((∫ t in Ioc ε ρ, Qd ε ρ t s / t) + ∫ t in Ioi ρ, Qd ε ρ t s / t) := by
    have hIε : IntegrableOn (fun t => Qd ε ρ t s / t) (Ioi ε) :=
      hQint.mono_set (Ioi_subset_Ioi hε.le)
    rw [← Ioc_union_Ioi_eq_Ioi hε.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hQint.mono_set Ioc_subset_Ioi_self) hIε, ← Ioc_union_Ioi_eq_Ioi hερ.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hIε.mono_set Ioc_subset_Ioi_self) (hIε.mono_set (Ioi_subset_Ioi hερ.le))]
  rw [hsplit]
  -- the unit-circle self pairing
  set G0 : ℝ → ℝ := fun t => gPair t (circMeas 0 1) (circMeas 0 1) / t with hG0
  set Gs : ℝ → ℝ := fun t => gPair t (circMeas s ε) (circMeas s ε) / t with hGs
  obtain ⟨g0I, g0B⟩ := selfPair_bound (0 : ℂ) one_pos hρ
  obtain ⟨gsI, gsB⟩ := selfPair_bound s hε hε
  have hB0 : ∀ {a : ℝ}, 0 ≤ a → a ≤ ρ → ∫ t in Ioc a ρ, G0 t ≤ 2 * ρ ^ 2 + 1 / (2 * ρ ^ 2) := by
    intro a ha haρ
    refine le_trans ?_ (le_of_le_of_eq g0B (by ring))
    refine setIntegral_mono_set g0I ?_ (Ioc_subset_Ioc_left ha).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (gPair_nonneg _ _ _) ht.1.le
  have hB0' : ∫ t in Ioc 0 ε, G0 t ≤ 2 * ρ ^ 2 + 1 / (2 * ρ ^ 2) := by
    refine le_trans ?_ (le_of_le_of_eq g0B (by ring))
    refine setIntegral_mono_set g0I ?_ (Ioc_subset_Ioc_right hερ.le).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (gPair_nonneg _ _ _) ht.1.le
  have hBs : ∫ t in Ioc 0 ε, Gs t ≤ 5 / 2 := by
    refine gsB.trans (le_of_eq ?_)
    field_simp
    ring
  -- piece 1: `(0, ε]`
  have p1 : ∫ t in Ioc 0 ε, Qd ε ρ t s / t ≤ 2 * (5 / 2) + 2 * (2 * ρ ^ 2 + 1 / (2 * ρ ^ 2)) := by
    have hI : IntegrableOn (fun t => 2 * Gs t + 2 * G0 t) (Ioc 0 ε) :=
      (gsI.const_mul 2).add ((g0I.mono_set (Ioc_subset_Ioc_right hερ.le)).const_mul 2)
    calc ∫ t in Ioc 0 ε, Qd ε ρ t s / t ≤ ∫ t in Ioc 0 ε, (2 * Gs t + 2 * G0 t) := by
          refine setIntegral_mono_on (hQint.mono_set Ioc_subset_Ioi_self) hI measurableSet_Ioc
            fun t ht => ?_
          rw [div_le_iff₀ ht.1]
          have := Qd_small ε ρ t s hε ht.2
          simp only [hGs, hG0]
          rw [add_mul, mul_assoc, mul_assoc, div_mul_cancel₀ _ ht.1.ne',
            div_mul_cancel₀ _ ht.1.ne']
          exact this
      _ = 2 * (∫ t in Ioc 0 ε, Gs t) + 2 * ∫ t in Ioc 0 ε, G0 t := by
          rw [integral_add (gsI.const_mul 2)
            ((g0I.mono_set (Ioc_subset_Ioc_right hερ.le)).const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by linarith
  -- piece 2: `(ε, ρ]`
  have p2 : ∫ t in Ioc ε ρ, Qd ε ρ t s / t ≤ 1 / 2 + 2 * (2 * ρ ^ 2 + 1 / (2 * ρ ^ 2)) := by
    have hpow : IntegrableOn (fun t : ℝ => (t ^ 3)⁻¹) (Ioc ε ρ) :=
      (integrableOn_inv_pow_three hε).mono_set Ioc_subset_Ioi_self
    have hG0I : IntegrableOn G0 (Ioc ε ρ) := g0I.mono_set (Ioc_subset_Ioc_left hε.le)
    have hI : IntegrableOn (fun t => ε ^ 2 * (t ^ 3)⁻¹ + 2 * G0 t) (Ioc ε ρ) :=
      (hpow.const_mul _).add (hG0I.const_mul 2)
    have hpowB : ∫ t in Ioc ε ρ, (t ^ 3)⁻¹ ≤ (2 * ε ^ 2)⁻¹ := by
      rw [← integral_inv_pow_three hε]
      refine setIntegral_mono_set (integrableOn_inv_pow_three hε) ?_
        Ioc_subset_Ioi_self.eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have : 0 < t := hε.trans ht
      positivity
    calc ∫ t in Ioc ε ρ, Qd ε ρ t s / t ≤ ∫ t in Ioc ε ρ, (ε ^ 2 * (t ^ 3)⁻¹ + 2 * G0 t) := by
          refine setIntegral_mono_on (hQint.mono_set (fun t ht => hε.trans ht.1)) hI
            measurableSet_Ioc fun t ht => ?_
          have ht0 : 0 < t := hε.trans ht.1
          rw [div_le_iff₀ ht0]
          have := Qd_band ε ρ t s hε ht
          simp only [hG0]
          have e : (ε ^ 2 * (t ^ 3)⁻¹ + 2 * (gPair t (circMeas 0 1) (circMeas 0 1) / t)) * t =
              ε ^ 2 / t ^ 2 + 2 * gPair t (circMeas 0 1) (circMeas 0 1) := by
            field_simp
          rw [e]
          exact this
      _ = ε ^ 2 * (∫ t in Ioc ε ρ, (t ^ 3)⁻¹) + 2 * ∫ t in Ioc ε ρ, G0 t := by
          rw [integral_add (hpow.const_mul _) (hG0I.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ ε ^ 2 * (2 * ε ^ 2)⁻¹ + 2 * (2 * ρ ^ 2 + 1 / (2 * ρ ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hpowB (by positivity))
            (mul_le_mul_of_nonneg_left (hB0 hε.le hερ.le) (by norm_num))
      _ = 1 / 2 + 2 * (2 * ρ ^ 2 + 1 / (2 * ρ ^ 2)) := by
          field_simp
  -- piece 3: `(ρ, ∞)`
  have p3 : ∫ t in Ioi ρ, Qd ε ρ t s / t ≤ (6 + 2 * ρ) ^ 2 / (2 * ρ ^ 2) := by
    calc ∫ t in Ioi ρ, Qd ε ρ t s / t ≤ ∫ t in Ioi ρ, (6 + 2 * ρ) ^ 2 * (t ^ 3)⁻¹ := by
          refine setIntegral_mono_on (hQint.mono_set (Ioi_subset_Ioi hρ.le))
            ((integrableOn_inv_pow_three hρ).const_mul _) measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := hρ.trans ht
          rw [div_le_iff₀ ht0]
          have := Qd_large s hε hερ hs ht
          have e : (6 + 2 * ρ) ^ 2 * (t ^ 3)⁻¹ * t = (6 + 2 * ρ) ^ 2 / t ^ 2 := by
            field_simp
          rw [e]
          exact this
      _ = (6 + 2 * ρ) ^ 2 / (2 * ρ ^ 2) := by
          rw [integral_const_mul, integral_inv_pow_three hρ]; ring
  unfold Cb
  linarith

end LQGDimension.Coupling
