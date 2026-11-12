/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28L1A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Low2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect

/-!
# DDDF Prop 28 Part 2 Step 1 for the family `δ ∈ (0,1)`: tools (task P2-DDDF28L)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1455–1472 (Part 2, Step 1), for the family
`δ = 2^{-n-r}` (l. 1648, "the same argument").

* `law_mrect_phiVer`: scaling and rigid motions (DDDF (2.30), l. 1613): for `δ ≤ h = 2^{-K}`,
  the crossing length of `φ_{δ,h}` across `u 2^{-K} R_{a,b} + c` has the law of
  `h · L(φ_{δ/h,1}, R_{a,b})` (same proof as `T20B.law_mrectLen`, via `map_ker_eq`,
  `phiKernelL2_motion` and `map_modification_scale`);
* `cross_lower` (DDDF l. 1457–1460, `eq:BoundHolderLowR`): a path in `[0,1]²` from `x ∈ P` to
  a point `y` outside the open box `\hat P°` crosses one of the four short rectangles
  `R_i^S(P)` (`T20D.piece_of_cross`); so `d_f(x,y) ≥ e^{-ξM} min_{i} L_g(R_i^S(P))` when
  `|f − g| ≤ M` on `[0,1]²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28L

open WhiteNoise LFPP Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **Scaling and rigid motions** (DDDF (2.30), l. 1613): for `δ ≤ h = 2^{-K}`,
`L(φ_{δ,h}, u 2^{-K} R_{a,b} + c) =ᵈ h · L(φ_{δ/h,1}, R_{a,b})`. -/
theorem law_mrect_phiVer (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (K : ℕ)
    (hδh : δ ≤ (2 : ℝ)⁻¹ ^ K) (u : Circle) (c : ℂ) (a b : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    P {ω | T20B.mrectLen ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K u c a b ∈ S} =
      P {ω | (2 : ℝ)⁻¹ ^ K * lenObs ξ (phiVer W P (δ / (2 : ℝ)⁻¹ ^ K) 1) (rectAB a b) ω ∈ S} := by
  have := hW.isProbabilityMeasure
  set h : ℝ := (2 : ℝ)⁻¹ ^ K with hh_def
  have hh : 0 < h := by positivity
  have hφ := isPhiVersion_phiVer hW hδ hδh
  have hδh' : δ / h ≤ 1 := (div_le_one hh).2 hδh
  have hφ1 := isPhiVersion_phiVer hW (div_pos hδ hh) hδh'
  set Y₁ : ℂ → Ω → ℝ := fun x ω => phiVer W P δ h ((u : ℂ) * ((h : ℂ) * x) + c) ω
  set Y₀ : ℂ → Ω → ℝ := fun x ω => phiVer W P δ h ((h : ℂ) * x) ω
  have hm : ∀ x, Measurable (Y₁ x) := fun x => hφ.meas _
  have hm0 : ∀ x, Measurable (Y₀ x) := fun x => hφ.meas _
  -- the law of `Y₁` is the law of `Y₀` (rigid motion) and of `φ_{δ/h,1}` (scaling)
  have hlaw1 : P.map (fun ω => (Y₀ · ω)) = P.map (fun ω => (Y₁ · ω)) := by
    refine map_ker_eq hW (fun x => phiKernelL2 δ h ((h : ℂ) * x)) (motionL2 u c) hm0 hm
      (fun x => hφ.ae_eq _) (fun x => ?_)
    refine (hφ.ae_eq _).trans (Filter.Eventually.of_forall fun ω => ?_)
    simp only [phi, phiKernelL2_motion hδ]
  have hhh : h / h = 1 := div_self hh.ne'
  have hlaw2 := map_modification_scale hW hδ hδh hh (Y₁ := Y₀) (Y₂ := phiVer W P (δ / h) 1)
    hm0 hφ1.meas (fun x => hφ.ae_eq _) (fun x => by rw [hhh]; exact hφ1.ae_eq x)
    (F := id) measurable_id
  simp only [id] at hlaw2
  have hlaw : P.map (fun ω => (Y₁ · ω)) = P.map (fun ω => (phiVer W P (δ / h) 1 · ω)) :=
    hlaw1.symm.trans hlaw2
  set T : Set ℝ≥0∞ := {v | h * v.toReal ∈ S}
  have hT : MeasurableSet T := (measurable_const.mul ENNReal.measurable_toReal) hS
  have e1 : ∀ ω, T20B.mrectLen ξ (fun x => phiVer W P δ h x ω) K u c a b =
      h * (crossLenIn ξ (fun x => Y₁ x ω) (rectAB a b).toSet (rectAB a b).side₁
        (rectAB a b).side₂).toReal := by
    intro ω
    simp only [T20B.mrectLen, T20B.mot_image]
    rw [crossLenIn_image_motion, image_mul_rectAB_toSet hh, image_mul_rectAB_side₁ hh,
      image_mul_rectAB_side₂ hh]
    have := rectLen_rectAB_mul (ξ := ξ) (fun x => phiVer W P δ h ((u : ℂ) * x + c) ω) hh a b
    unfold rectLen at this
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le]
  have h1 : {ω | T20B.mrectLen ξ (fun x => phiVer W P δ h x ω) K u c a b ∈ S} =
      {ω | crossLenIn ξ (fun x => Y₁ x ω) (rectAB a b).toSet (rectAB a b).side₁
        (rectAB a b).side₂ ∈ T} := by
    ext ω; simp only [mem_ofPred_eq, e1, T]
  have h2 : {ω | h * lenObs ξ (phiVer W P (δ / h) 1) (rectAB a b) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiVer W P (δ / h) 1 x ω) (rectAB a b).toSet
        (rectAB a b).side₁ (rectAB a b).side₂ ∈ T} := rfl
  rw [h1, h2]
  exact measure_crossLenIn_eq (MarkedRect.isCompact_toSet _)
    (fun ω => (hφ.cont ω).comp ((continuous_const.mul
      (continuous_const.mul continuous_id)).add continuous_const)) hm hφ1.cont hφ1.meas hlaw hT

omit [MeasurableSpace Ω] in
/-- **Crossing of a short rectangle** (DDDF l. 1457–1460): if `x ∈ P` (level `K`) and `y` lies
outside the open box `\hat P°`, every path from `x` to `y` in `[0,1]²` crosses one of the
`R_i^S(P)`, so `d_f(x, y) ≥ e^{-ξ M} min_i L_g(R_i^S(P))` when `|g − f| ≤ M` on `[0,1]²`. -/
theorem cross_lower (hξ : 0 ≤ ξ) {f g : ℂ → ℝ} {M : ℝ}
    (hfg : ∀ z ∈ closedUnitSquare, |g z - f z| ≤ M) {K : ℕ} {b : ℤ × ℤ} {x y : ℂ}
    (hx : x ∈ T20.dyBlock K b)
    (hy : y ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K)) {m : ℝ≥0∞}
    (hm : ∀ j ∈ T20D.shortJ K b,
      m ≤ crossLenIn ξ g (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j)) :
    ENNReal.ofReal (Real.exp (-(ξ * M))) * m ≤ crossLenIn ξ f closedUnitSquare {x} {y} := by
  refine le_crossLenIn fun G ⟨z, hz, w, hw, hG, hU⟩ => ?_
  rw [mem_singleton_iff] at hz hw
  subst hz hw
  have h0 : G 0 ∈ T20.dyBlock K b := by rw [hG.source]; exact hx
  have h1 : G 1 ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) := by
    rw [hG.target]; exact hy
  obtain ⟨u, v, hu, huv, hv, -, j, hj, hadm⟩ :=
    T20D.piece_of_cross hG ⟨le_rfl, zero_le_one⟩ h0 h1
  have hsubU : ∀ t ∈ Icc (0 : ℝ) 1, subPath G u v t ∈ closedUnitSquare := fun t ht =>
    hU _ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  have hc1 := crossLenIn_le_lfppLen (ξ := ξ) (f := g) hadm
  have hc2 := lfppLen_le_of_abs_sub_le (ξ := ξ) (f := g) (g := f) (P := subPath G u v)
    (c := M) fun t ht => hfg _ (hsubU t ht)
  have hc3 : lfppLen ξ f (subPath G u v) ≤ lfppLen ξ f G := by
    rw [lfppLen_subPath G huv, lfppLen_eq]
    exact lintegral_mono_set (Icc_subset_Icc hu hv)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfg _ (hU 0 ⟨le_rfl, zero_le_one⟩))
  rw [abs_of_nonneg hξ] at hc2
  have key : m ≤ ENNReal.ofReal (Real.exp (ξ * M)) * lfppLen ξ f G :=
    ((hm j hj).trans hc1).trans (hc2.trans (by gcongr))
  calc ENNReal.ofReal (Real.exp (-(ξ * M))) * m
      ≤ ENNReal.ofReal (Real.exp (-(ξ * M))) *
          (ENNReal.ofReal (Real.exp (ξ * M)) * lfppLen ξ f G) := by gcongr
    _ = lfppLen ξ f G := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

end S6P28L
end DDDF
end LQGMetric
