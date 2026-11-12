/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.LenBasic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import Mathlib.Analysis.Complex.ReImTopology

/-!
# DDDF length observables, deterministic layer (task P2-DDDFLEN; blueprint DDDF.D2.len, S2.c)

DDDF = Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage percolation for
γ ∈ (0,2)*, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.

DDDF (2.21) = `DefLength` (l. 457–460): `L^{(n)}_{a,b}(φ) := inf_π ∫_π e^{ξ φ_{0,n}} ds`, the
infimum over curves `π` in `R_{a,b} = [0,a] × [0,b]` joining its left and right sides; and
(l. 494–496) `L^{(n)}(P, φ)` for a rectangle `P` with two marked opposite sides. Here, for a
weight field `f : ℂ → ℝ`:

* `MarkedRect`: a closed rectangle `[x₀, x₀+w] × [y₀, y₀+h]` with marked sides (left/right if
  `horiz`, bottom/top otherwise); `rectAB a b` is DDDF's `R_{a,b}` with left/right marked.
* `crossLenIn ξ f U A B`: the infimum of `lfppLen ξ f P = ∫₀¹ e^{ξ f(P t)} |P'(t)| dt` over
  piecewise-C¹ paths `P` (FOUNDATIONS §7 `IsPiecewiseC1Path`) from `A` to `B` staying in `U`.
  (`Blueprint.lfppCrossIn ξ ε h` is `(crossLenIn ξ (h*_ε) [0,1]² leftSide rightSide).toReal`.)
  DDDF writes "smooth curves" (l. 462); we use piecewise-C¹ paths as DFGPS and GM do
  (blueprint DDDF.D2.len, proposed deviation D-DDDF-10).
* `rectLen ξ f R := crossLenIn ξ f R R.side₁ R.side₂` (= `L^{(n)}(P, φ)` with `f = φ_{0,n}`).

Results:
* `crossLenIn_le_of_abs_sub_le`: if `|f − g| ≤ c` on `U` then `L(f) ≤ e^{|ξ| c} L(g)`; this is
  DDDF's "straightforward" inequality `e^{−ξX_{a,b}} L(ψ) ≤ L(φ) ≤ e^{ξX_{a,b}} L(ψ)` (l. 482–485).
* `rectLen_ge`, `rectLen_le` (DDDF.S2.c, l. 908 "e^{−ξ‖φ_{0,n}‖} ≤ L^{(n)}_{1,1} ≤ e^{ξ‖φ_{0,n}‖}"):
  if `|f| ≤ M` on `R` then `e^{−|ξ|M} c ≤ L(R) ≤ e^{|ξ|M} c` with `c` the Euclidean crossing
  distance (`crossWidth`); the lower bound is "chord ≤ arclength", whose proof is ported from
  LQGDimension (`LQGDimension.TreeIneqJ42.chord_le_arclength`, `deriv_intervalIntegrable`,
  LFPP/TreeInequalityAux.lean l. 659–712), the upper bound is the straight segment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

/-- A closed rectangle `[x₀, x₀ + w] × [y₀, y₀ + h]` with two marked opposite sides: the left and
right sides if `horiz`, the bottom and top sides otherwise (DDDF l. 494–496). -/
structure MarkedRect where
  /-- left abscissa -/
  x0 : ℝ
  /-- bottom ordinate -/
  y0 : ℝ
  /-- width -/
  w : ℝ
  /-- height -/
  h : ℝ
  /-- whether the marked sides are the vertical (left/right) ones -/
  horiz : Bool

namespace MarkedRect

/-- the closed rectangle as a subset of `ℂ` -/
def toSet (R : MarkedRect) : Set ℂ := Icc R.x0 (R.x0 + R.w) ×ℂ Icc R.y0 (R.y0 + R.h)

/-- the first marked side (left, or bottom) -/
def side₁ (R : MarkedRect) : Set ℂ :=
  if R.horiz then {R.x0} ×ℂ Icc R.y0 (R.y0 + R.h) else Icc R.x0 (R.x0 + R.w) ×ℂ {R.y0}

/-- the second marked side (right, or top) -/
def side₂ (R : MarkedRect) : Set ℂ :=
  if R.horiz then {R.x0 + R.w} ×ℂ Icc R.y0 (R.y0 + R.h)
  else Icc R.x0 (R.x0 + R.w) ×ℂ {R.y0 + R.h}

/-- the Euclidean distance between the marked sides -/
def crossWidth (R : MarkedRect) : ℝ := if R.horiz then R.w else R.h

/-- the lower-left corner (a point of `side₁`) -/
def p₁ (R : MarkedRect) : ℂ := ⟨R.x0, R.y0⟩

/-- the point of `side₂` opposite to `p₁` -/
def p₂ (R : MarkedRect) : ℂ := if R.horiz then ⟨R.x0 + R.w, R.y0⟩ else ⟨R.x0, R.y0 + R.h⟩

theorem isCompact_toSet (R : MarkedRect) : IsCompact R.toSet :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

end MarkedRect

/-- DDDF's rectangle `R_{a,b} = [0,a] × [0,b]` with its left and right sides marked (l. 453). -/
def rectAB (a b : ℝ) : MarkedRect := ⟨0, 0, a, b, true⟩

/-- `P` is an admissible crossing path: piecewise C¹ from a point of `A` to a point of `B`,
staying in `U` -/
def AdmPath (U A B : Set ℂ) (P : ℝ → ℂ) : Prop :=
  ∃ z ∈ A, ∃ w ∈ B, IsPiecewiseC1Path P z w ∧ ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U

/-- The crossing length `inf_{π : A → B, π ⊆ U} ∫_π e^{ξ f} ds` over piecewise-C¹ paths
(DDDF (2.21), l. 457–460). -/
def crossLenIn (ξ : ℝ) (f : ℂ → ℝ) (U A B : Set ℂ) : ℝ≥0∞ :=
  ⨅ z ∈ A, ⨅ w ∈ B,
    ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P z w ∧ ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U}, lfppLen ξ f P.1

/-- `L(P, f)`: the crossing length between the marked sides of `R` (DDDF l. 494–496). -/
def rectLen (ξ : ℝ) (f : ℂ → ℝ) (R : MarkedRect) : ℝ≥0∞ :=
  crossLenIn ξ f R.toSet R.side₁ R.side₂

variable {ξ : ℝ} {f g : ℂ → ℝ} {U A B : Set ℂ}

theorem crossLenIn_eq_biInf (ξ : ℝ) (f : ℂ → ℝ) (U A B : Set ℂ) :
    crossLenIn ξ f U A B = ⨅ P ∈ {P | AdmPath U A B P}, lfppLen ξ f P := by
  refine le_antisymm (le_iInf₂ fun P hP => ?_) (le_iInf₂ fun z hz => le_iInf₂ fun w hw =>
    le_iInf fun P => iInf₂_le P.1 ⟨z, hz, w, hw, P.2.1, P.2.2⟩)
  obtain ⟨z, hz, w, hw, hP, hU⟩ := hP
  exact iInf₂_le_of_le z hz (iInf₂_le_of_le w hw (iInf_le_of_le ⟨P, hP, hU⟩ le_rfl))

theorem crossLenIn_le_lfppLen {P : ℝ → ℂ} (hP : AdmPath U A B P) :
    crossLenIn ξ f U A B ≤ lfppLen ξ f P := by
  rw [crossLenIn_eq_biInf]; exact iInf₂_le P hP

theorem le_crossLenIn {c : ℝ≥0∞} (h : ∀ P, AdmPath U A B P → c ≤ lfppLen ξ f P) :
    c ≤ crossLenIn ξ f U A B := by
  rw [crossLenIn_eq_biInf]; exact le_iInf₂ h

/-! ### Comparison of weights -/

theorem lfppLen_le_of_abs_sub_le {P : ℝ → ℂ} {c : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |f (P t) - g (P t)| ≤ c) :
    lfppLen ξ f P ≤ ENNReal.ofReal (Real.exp (|ξ| * c)) * lfppLen ξ g P := by
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _))
  have h1 : ξ * (f (P t) - g (P t)) ≤ |ξ| * c := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h t ht) (abs_nonneg _)
  linarith

/-- If `|f − g| ≤ c` on `U` then `L(f) ≤ e^{|ξ| c} L(g)` (DDDF l. 482–485). -/
theorem crossLenIn_le_of_abs_sub_le {c : ℝ} (h : ∀ x ∈ U, |f x - g x| ≤ c) :
    crossLenIn ξ f U A B ≤ ENNReal.ofReal (Real.exp (|ξ| * c)) * crossLenIn ξ g U A B := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * c)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [crossLenIn_eq_biInf, crossLenIn_eq_biInf, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun hP => ?_
  obtain ⟨z, -, w, -, -, hU⟩ := hP
  exact lfppLen_le_of_abs_sub_le fun t ht => h _ (hU t ht)

/-! ### Chord ≤ arclength (ported from LQGDimension) -/

open LQGDimension.TreeIneqJ42 in
/-- `P'` is integrable on `[0,1]` for a piecewise-C¹ path (LQGDimension
`TreeIneqJ42.deriv_intervalIntegrable`, same proof). -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.intervalIntegrable_deriv_dddf {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) : IntervalIntegrable (deriv P) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hP.piecewise
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv P x‖ ≤ C :=
    fun i => deriv_bound_piece (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv P x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv P).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

open LQGDimension.TreeIneqJ42 in
/-- Chord ≤ arclength (LQGDimension `TreeIneqJ42.chord_le_arclength`, same proof). -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.norm_sub_le_endpoints {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) : ‖w - z‖ ≤ ∫ t in (0 : ℝ)..1, ‖deriv P t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hP.piecewise
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le P (deriv P)
    zero_le_one (countable_range t) hP.continuousOn
    (fun x hx => hasDerivAt_of_piece ht0 htk hC hx.1 hx.2) hP.intervalIntegrable_deriv_dddf
  rw [← hP.source, ← hP.target, ← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm zero_le_one

theorem _root_.LQGMetric.IsPiecewiseC1Path.ofReal_norm_sub_le_endpoints {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) :
    ENNReal.ofReal ‖w - z‖ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖deriv P t‖ := by
  have hI := hP.intervalIntegrable_deriv_dddf
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at hI
  rw [← ofReal_integral_eq_lintegral_ofReal hI.norm
    (Eventually.of_forall fun _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (hP.norm_sub_le_endpoints.trans_eq ?_)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- `∫_P e^{ξ f} ds ≥ e^{−|ξ|M} |w − z|` when `|f| ≤ M` along `P`. -/
theorem lfppLen_ge {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {M : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f (P t)| ≤ M) :
    ENNReal.ofReal (Real.exp (-(|ξ| * M)) * ‖w - z‖) ≤ lfppLen ξ f P := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left hP.ofReal_norm_sub_le_endpoints (zero_le : (0 : ℝ≥0∞) ≤ _)).trans ?_
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _))
  have h1 : |ξ * f (P t)| ≤ |ξ| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb t ht) (abs_nonneg _)
  linarith [neg_abs_le (ξ * f (P t))]

/-! ### Crude bounds (DDDF.S2.c) -/

namespace MarkedRect

theorem crossWidth_le_norm (R : MarkedRect) {z w : ℂ} (hz : z ∈ R.side₁) (hw : w ∈ R.side₂) :
    R.crossWidth ≤ ‖w - z‖ := by
  unfold side₁ at hz; unfold side₂ at hw; unfold crossWidth
  split_ifs at hz hw ⊢
  · rw [Complex.mem_reProdIm] at hz hw
    have h := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re, mem_singleton_iff.1 hz.1, mem_singleton_iff.1 hw.1] at h
    have : R.x0 + R.w - R.x0 = R.w := by ring
    rw [this] at h; exact (le_abs_self _).trans h
  · rw [Complex.mem_reProdIm] at hz hw
    have h := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im, mem_singleton_iff.1 hz.2, mem_singleton_iff.1 hw.2] at h
    have : R.y0 + R.h - R.y0 = R.h := by ring
    rw [this] at h; exact (le_abs_self _).trans h

/-- the straight segment `t ↦ p₁ + t (p₂ − p₁)` -/
def seg (R : MarkedRect) : ℝ → ℂ := fun t => R.p₁ + (t : ℂ) * (R.p₂ - R.p₁)

theorem hasDerivAt_seg (R : MarkedRect) (t : ℝ) : HasDerivAt R.seg (R.p₂ - R.p₁) t := by
  have := (((hasDerivAt_id t).ofReal_comp).mul_const (R.p₂ - R.p₁)).const_add R.p₁
  simp only [id, Complex.ofReal_one, one_mul] at this
  exact this

theorem continuous_seg (R : MarkedRect) : Continuous R.seg := by unfold seg; fun_prop

theorem isPiecewiseC1Path_seg (R : MarkedRect) : IsPiecewiseC1Path R.seg R.p₁ R.p₂ where
  source := by simp [seg]
  target := by simp [seg]
  continuousOn := R.continuous_seg.continuousOn
  piecewise := by
    refine ⟨1, ![0, 1], ?_, rfl, rfl, fun i => ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · have : ContDiff ℝ 1 R.seg := by
        unfold seg
        exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
      exact this.contDiffOn

theorem seg_re_im (R : MarkedRect) (t : ℝ) :
    (R.seg t).re = R.x0 + (if R.horiz then t * R.w else 0) ∧
      (R.seg t).im = R.y0 + (if R.horiz then 0 else t * R.h) := by
  unfold seg p₁ p₂
  split_ifs <;> simp

theorem admPath_seg (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) :
    AdmPath R.toSet R.side₁ R.side₂ R.seg := by
  refine ⟨R.p₁, ?_, R.p₂, ?_, R.isPiecewiseC1Path_seg, fun t ht => ?_⟩
  · unfold side₁ p₁; split_ifs <;> simp [Complex.mem_reProdIm, hw, hh]
  · unfold side₂ p₂; split_ifs <;> simp [Complex.mem_reProdIm, hw, hh]
  · obtain ⟨h1, h2⟩ := R.seg_re_im t
    rw [toSet, Complex.mem_reProdIm, h1, h2]
    have hw' : t * R.w ≤ R.w := mul_le_of_le_one_left hw ht.2
    have hh' : t * R.h ≤ R.h := mul_le_of_le_one_left hh ht.2
    have hw0 : 0 ≤ t * R.w := mul_nonneg ht.1 hw
    have hh0 : 0 ≤ t * R.h := mul_nonneg ht.1 hh
    split_ifs <;> simp only [mem_Icc] <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem norm_p₂_sub_p₁ (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) :
    ‖R.p₂ - R.p₁‖ = R.crossWidth := by
  unfold p₂ p₁ crossWidth
  split_ifs
  · have : (⟨R.x0 + R.w, R.y0⟩ : ℂ) - ⟨R.x0, R.y0⟩ = (R.w : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  · have : (⟨R.x0, R.y0 + R.h⟩ : ℂ) - ⟨R.x0, R.y0⟩ = (R.h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hh]

end MarkedRect

/-- **DDDF.S2.c, lower bound** (l. 908): if `|f| ≤ M` on `R` then
`L(R, f) ≥ e^{−|ξ|M} · crossWidth R`. -/
theorem rectLen_ge (R : MarkedRect) {M : ℝ} (hb : ∀ x ∈ R.toSet, |f x| ≤ M) :
    ENNReal.ofReal (Real.exp (-(|ξ| * M)) * R.crossWidth) ≤ rectLen ξ f R := by
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, hz, w, hw, hP, hU⟩ := hP
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (lfppLen_ge hP fun t ht => hb _ (hU t ht))
  exact mul_le_mul_of_nonneg_left (R.crossWidth_le_norm hz hw) (Real.exp_pos _).le

/-- **DDDF.S2.c, upper bound** (l. 908): if `|f| ≤ M` on `R` then
`L(R, f) ≤ e^{|ξ|M} · crossWidth R` (the straight segment). -/
theorem rectLen_le (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) {M : ℝ}
    (hb : ∀ x ∈ R.toSet, |f x| ≤ M) :
    rectLen ξ f R ≤ ENNReal.ofReal (Real.exp (|ξ| * M) * R.crossWidth) := by
  have hA := R.admPath_seg hw hh
  refine (crossLenIn_le_lfppLen hA).trans ?_
  have hd : ∀ t, deriv R.seg t = R.p₂ - R.p₁ := fun t => (R.hasDerivAt_seg t).deriv
  unfold lfppLen
  simp only [hd, R.norm_p₂_sub_p₁ hw hh]
  calc ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (ξ * f (R.seg t)) * R.crossWidth)
      ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (|ξ| * M) * R.crossWidth) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal ?_
        have hc : 0 ≤ R.crossWidth := by unfold MarkedRect.crossWidth; split_ifs <;> assumption
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hc
        obtain ⟨_, _, _, _, _, hU⟩ := hA
        have h1 : |ξ * f (R.seg t)| ≤ |ξ| * M := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb _ (hU t ht)) (abs_nonneg _)
        exact (le_abs_self _).trans h1
    _ = ENNReal.ofReal (Real.exp (|ξ| * M) * R.crossWidth) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- For a continuous weight, crossing lengths of rectangles are finite. -/
theorem rectLen_ne_top (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) (hf : Continuous f) :
    rectLen ξ f R ≠ ∞ := by
  obtain ⟨M, hM⟩ := (R.isCompact_toSet.image_of_continuousOn
    (continuous_abs.comp hf).continuousOn).isBounded.bddAbove
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rectLen_le R hw hh (M := M) fun x hx => ?_)
  exact hM ⟨x, hx, rfl⟩

/-- For a continuous weight and `crossWidth R > 0`, crossing lengths of rectangles are
positive. -/
theorem rectLen_pos (R : MarkedRect) (hc : 0 < R.crossWidth) (hf : Continuous f) :
    0 < rectLen ξ f R := by
  obtain ⟨M, hM⟩ := (R.isCompact_toSet.image_of_continuousOn
    (continuous_abs.comp hf).continuousOn).isBounded.bddAbove
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _) hc))
    (rectLen_ge R (M := M) fun x hx => ?_)
  exact hM ⟨x, hx, rfl⟩

end DDDF
end LQGMetric
