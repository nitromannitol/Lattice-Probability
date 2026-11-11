import Mathlib
import LatticeProb.LQG.WeylCompositionOuter

/-!
# Weyl composition for the outer scaling, LP

Second part of the LP copy of `HarmonicBalls/FirstPass/Phase2/WeylCompositionOuterDerived.lean` (lines 708-1219): the
arclength reparametrization by inner distance, the Riemann comparison `riemann_arc`, and the one-way-topology lemma
`weylScaling_innerDist_le_direct`. The LP statement `LatticeProb.LQG.WeylMetricCompositionContinuousOuterLP` is the form of
`WeylMetricCompositionContinuousOuterFrozen` (`FirstPass/Frozen/S11j.lean:117`),
and `LatticeProb.LQG.weylMetricCompositionContinuousOuter_lp` proves it with no hypothesis added.
Source: Bou-Rabee-Gwynne (arXiv:2208.11795) Fact 2.2 III; Gwynne-Miller (1.8).
-/

namespace LatticeProb.LQG

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

/-- Finiteness of the outer-free cost: a `D`-length-parametrized curve of finite cost for the weight `e^{ξ(g+f)}`
has finite cost for the weight `e^{ξ g}`, since `e^{ξ f}` is bounded below on its compact image. -/
theorem IsEuclideanLengthMetric.cost_g_ne_top {D : ℂ → ℂ → ℝ} {ξ : ℝ} {g f : ℂ → ℝ} (hf : Continuous f)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) ≠ ⊤) :
    ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ := by
  have hcont : ContinuousOn (fun t => Real.exp (ξ * f (p t))) (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul hf)).comp_continuousOn hp.2.1
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    ⟨0, ⟨le_rfl, hp.1⟩⟩ hcont
  set c : ℝ := Real.exp (ξ * f (p t0)) with hc_def
  have hc0 : 0 < c := Real.exp_pos _
  have hle : (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t)))) * ENNReal.ofReal c ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) := by
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
    have hm : c ≤ Real.exp (ξ * f (p t)) := isMinOn_iff.mp hmin t ht
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Real.exp (ξ * (g (p t) + f (p t))) = Real.exp (ξ * g (p t)) * Real.exp (ξ * f (p t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
  intro hA
  rw [hA, ENNReal.top_mul (ENNReal.ofReal_pos.mpr hc0).ne'] at hle
  exact hC (top_le_iff.mp hle)

/-- Cost bound for the inner length: the inner length of a sub-arc is at most its `e^{ξ g}`-cost. -/
theorem IsEuclideanLengthMetric.curveLength_innerDist_le_cost {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T) {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ T) :
    curveLength (innerDist D ξ g) p u v ≤
      ∫⁻ t in Icc u v, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
  unfold curveLength
  refine iSup_le ?_
  rintro ⟨n, w, hwmono, hwmem⟩
  have hterm : ∀ i ∈ Finset.range n, ENNReal.ofReal (innerDist D ξ g (p (w (i + 1))) (p (w i))) ≤
      ∫⁻ t in Icc (w i) (w (i + 1)), ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro i _
    have hi1 : w i ≤ w (i + 1) := hwmono (Nat.le_succ i)
    rw [innerDist_ofReal hfin, hD.weylScaling_symm ξ g (p (w (i + 1))) (p (w i))]
    exact hD.weylScaling_le_segment_cost ξ g hp (hu.trans (hwmem i).1) hi1
      (((hwmem (i + 1)).2).trans hv)
  calc ∑ i ∈ Finset.range n, ENNReal.ofReal (innerDist D ξ g (p (w (i + 1))) (p (w i)))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ t in Icc (w i) (w (i + 1)), ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        Finset.sum_le_sum hterm
    _ = ∫⁻ t in Icc (w 0) (w n), ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        sum_lintegral_Icc_adjacent (fun t => ENNReal.ofReal (Real.exp (ξ * g (p t)))) w hwmono n
    _ ≤ ∫⁻ t in Icc u v, ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        lintegral_mono_set (Icc_subset_Icc (hwmem 0).1 (hwmem n).2)

/-- Auxiliary point type carrying the inner distance, used for the arc-length parametrization. -/
private structure InnerLengthPt where
  val : ℂ

/-- The inner distance as a metric on `InnerLengthPt`. -/
noncomputable abbrev innerMetricSpace {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) :
    MetricSpace InnerLengthPt where
  dist x y := innerDist D ξ g x.val y.val
  dist_self x := innerDist_self hD ξ g x.val
  dist_comm x y := innerDist_symm hD ξ g x.val y.val
  dist_triangle x y z := innerDist_triangle hD hfin x.val y.val z.val
  eq_of_dist_eq_zero {x y} h := by
    cases x
    cases y
    exact congrArg InnerLengthPt.mk (hD.innerDist_eq_zero hg hfin h)

/-- Additivity of the inner length along a curve (through `eVariationOn`). -/
theorem curveLength_innerDist_add {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) (p : ℝ → ℂ)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    curveLength (innerDist D ξ g) p a b + curveLength (innerDist D ξ g) p b c =
      curveLength (innerDist D ξ g) p a c := by
  let := innerMetricSpace hD hg hfin
  have hcurve : ∀ u v, curveLength (innerDist D ξ g) p u v =
      eVariationOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc u v) := by
    intro u v
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  rw [hcurve, hcurve, hcurve]
  have h := eVariationOn.Icc_add_Icc (fun t => (⟨p t⟩ : InnerLengthPt)) (s := univ) hab hbc (mem_univ b)
  simpa only [univ_inter] using h

/-- Arc-length parametrization for the inner distance (copy of `exists_lengthParametrized_with_tracking`,
with the continuity of the curve in the inner metric supplied as the hypothesis `hdc`; the Euclidean continuity of
the reparametrized curve follows from the one-way topology `weylScaling_nhds`). -/
theorem IsEuclideanLengthMetric.exists_arclength_innerDist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hfinite : curveLength (innerDist D ξ g) p 0 T ≠ ⊤)
    (hdc : ∀ t ∈ Icc 0 T, Tendsto (fun v => innerDist D ξ g (p t) (p v)) (𝓝[Icc 0 T] t) (𝓝 0)) :
    ∃ q : ℝ → ℂ, IsLengthParametrized (innerDist D ξ g) q (curveLength (innerDist D ξ g) p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength (innerDist D ξ g) p 0 T).toReal = p T ∧
      ∀ t ∈ Icc 0 T, q (curveLength (innerDist D ξ g) p 0 t).toReal = p t := by
  let := innerMetricSpace hD hg hfin
  have hcurve (q : ℝ → ℂ) (a b : ℝ) :
      curveLength (innerDist D ξ g) q a b = eVariationOn (fun t => (⟨q t⟩ : InnerLengthPt)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  have hrcont : ContinuousOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) := by
    intro t ht
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    refine (hdc t ht).congr (fun v => ?_)
    show innerDist D ξ g (p t) (p v) = innerDist D ξ g (p v) (p t)
    exact innerDist_symm hD ξ g _ _
  have hrvar : BoundedVariationOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) := by
    change eVariationOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) ≠ ⊤
    rw [← hcurve]
    exact hfinite
  obtain ⟨hspeed, hstart, hend⟩ := naturalParameterization_unitSpeed_Icc
    (fun t => (⟨p t⟩ : InnerLengthPt)) hT hrcont hrvar
  set R := (curveLength (innerDist D ξ g) p 0 T).toReal with hR_def
  have hs : HasUnitSpeedOn (naturalParameterization (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) 0)
      (Icc 0 R) := by
    simpa only [hR_def, hcurve] using hspeed
  have hval : Continuous (fun z : InnerLengthPt => z.val) := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ, h⟩ := hD.weylScaling_nhds hg hfin b.val (isOpen_ball (x := b.val) (ε := ε))
      (mem_ball_self hε)
    refine ⟨δ, hδ, fun a ha => ?_⟩
    have ha' : innerDist D ξ g b.val a.val < δ := by
      rw [innerDist_symm hD ξ g]
      exact ha
    have hmem := h a.val ha'
    exact mem_ball.mp hmem
  refine ⟨fun t => (naturalParameterization (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) 0 t).val,
    ⟨ENNReal.toReal_nonneg, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hval.comp_continuousOn (HasUnitSpeedOn.lipschitzOnWith_Icc hs).continuousOn)
  · intro a b ha hab hb
    have ha' : a ∈ Icc 0 R := ⟨ha, hab.trans hb⟩
    have hb' : b ∈ Icc 0 R := ⟨ha.trans hab, hb⟩
    have hinter : Icc 0 R ∩ Icc a b = Icc a b := by
      apply inter_eq_right.mpr
      exact Icc_subset_Icc ha hb
    have h := hs ha' hb'
    simp only [NNReal.coe_one, one_mul, hinter] at h
    rw [hcurve]
    exact h
  · exact congrArg InnerLengthPt.val hstart
  · have h := congrArg InnerLengthPt.val hend
    simpa only [hR_def, hcurve] using h
  · intro t ht
    have h := edist_naturalParameterization_eq_zero hrvar.locallyBoundedVariationOn
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht
    rw [variationOnFromTo.eq_of_le _ (Icc 0 T) ht.1,
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)] at h
    have heq := edist_eq_zero.mp h
    have hv := congrArg InnerLengthPt.val heq
    simpa only [hcurve] using hv

/-- Absolute continuity of a finite integral, pointwise along `[0, T]`. -/
theorem integral_small_near {F : ℝ → ENNReal} {T : ℝ} (hF : ∫⁻ t in Icc 0 T, F t ≠ ⊤) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Tendsto (fun v => ∫⁻ s in Icc (min t v) (max t v), F s) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hvol : Tendsto (fun v => volume (Icc (min t v) (max t v))) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have hc : Continuous fun v : ℝ => |v - t| := by fun_prop
    have h1 : Tendsto (fun v : ℝ => |v - t|) (𝓝[Icc 0 T] t) (𝓝 0) := by
      have := (hc.tendsto t).mono_left (nhdsWithin_le_nhds (s := Icc 0 T))
      simpa using this
    have h2 : Tendsto (fun v : ℝ => ENNReal.ofReal |v - t|) (𝓝[Icc 0 T] t) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      simpa [Function.comp_def] using this
    refine h2.congr' ?_
    filter_upwards with v
    simp only [Real.volume_Icc]
    congr 1
    rw [max_sub_min_eq_abs', abs_sub_comm]
  have hlim := tendsto_setLIntegral_zero (μ := volume.restrict (Icc 0 T)) (f := F) hF
    (s := fun v => Icc (min t v) (max t v)) (l := 𝓝[Icc 0 T] t) (by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol (fun _ => zero_le) ?_
      intro v
      rw [Function.comp, Measure.restrict_apply measurableSet_Icc]
      exact measure_mono inter_subset_left)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hsub : Icc (min t v) (max t v) ⊆ Icc 0 T :=
    Icc_subset_Icc (le_min ht.1 hv.1) (max_le ht.2 hv.2)
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub]

theorem IsEuclideanLengthMetric.innerDist_le_cost_minmax {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {u v : ℝ} (hu : u ∈ Icc 0 T)
    (hv : v ∈ Icc 0 T) :
    innerDist D ξ g (p u) (p v) ≤
      (∫⁻ t in Icc (min u v) (max u v), ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
  have key : ∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T → a ≤ b →
      innerDist D ξ g (p b) (p a) ≤
        (∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
    intro a b ha hb hab
    have hI : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
      ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc ha.1 hb.2))
    have h1 := hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2) (u := a) (v := b)
    have h2 := two_point_le_curveLength (D := innerDist D ξ g) p hab
    exact (ENNReal.ofReal_le_iff_le_toReal hI).mp (h2.trans h1)
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv, max_eq_right huv]
    have := key u v hu hv huv
    rw [innerDist_symm hD ξ g]
    exact this
  · rw [min_eq_right huv, max_eq_left huv]
    exact key v u hv hu huv

theorem IsEuclideanLengthMetric.abs_sub_arc_le {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {u v : ℝ} (hu : u ∈ Icc 0 T)
    (hv : v ∈ Icc 0 T) :
    |(curveLength (innerDist D ξ g) p 0 u).toReal - (curveLength (innerDist D ξ g) p 0 v).toReal| ≤
      (∫⁻ t in Icc (min u v) (max u v), ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
  have hfinw : ∀ w ∈ Icc 0 T, curveLength (innerDist D ξ g) p 0 w ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top hC ((hD.curveLength_innerDist_le_cost hfin hp (hu := le_rfl) (hv := hw.2)).trans
      (lintegral_mono_set (Icc_subset_Icc le_rfl hw.2)))
  have hI : ∫⁻ t in Icc (min u v) (max u v), ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
    ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc (le_min hu.1 hv.1) (max_le hu.2 hv.2)))
  -- for a ≤ b in [0, T]: |s b - s a| ≤ cost on [a, b]
  have key : ∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T → a ≤ b →
      |(curveLength (innerDist D ξ g) p 0 b).toReal - (curveLength (innerDist D ξ g) p 0 a).toReal| ≤
        (∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
    intro a b ha hb hab
    have hadd := curveLength_innerDist_add hD hg hfin p (a := 0) (b := a) (c := b) ha.1 hab
    have hXb := hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2) (u := a) (v := b)
    have hXI : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
      ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc ha.1 hb.2))
    have hX : curveLength (innerDist D ξ g) p a b ≠ ⊤ := ne_top_of_le_ne_top hXI hXb
    have hsum := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (hfinw a ha) hX] at hsum
    have hnn : 0 ≤ (curveLength (innerDist D ξ g) p a b).toReal := ENNReal.toReal_nonneg
    have hpos : 0 ≤ (curveLength (innerDist D ξ g) p 0 b).toReal -
        (curveLength (innerDist D ξ g) p 0 a).toReal := by linarith
    rw [abs_of_nonneg hpos]
    have hle := ENNReal.toReal_mono hXI hXb
    linarith
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv, max_eq_right huv]
    rw [abs_sub_comm]
    exact key u v hu hv huv
  · rw [min_eq_right huv, max_eq_left huv]
    exact key v u hv hu huv

theorem IsEuclideanLengthMetric.innerDist_tendsto_of_cost {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun v => innerDist D ξ g (p t) (p v)) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hlim := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp
    (integral_small_near (F := fun s => ENNReal.ofReal (Real.exp (ξ * g (p s)))) hC ht)
  rw [ENNReal.toReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun v => innerDist_nonneg _ _ _ _
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact hD.innerDist_le_cost_minmax hfin hp hC ht hv

/-- Uniform multiplicative modulus of a continuous real function on a compact interval. -/
theorem exists_exp_modulus {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (Icc a b)) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ κ > 0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |s - t| < κ →
      Real.exp (φ s) ≤ ρ * Real.exp (φ t) := by
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  obtain ⟨κ, hκ, hκU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) (Real.log ρ) hlog
  refine ⟨κ, hκ, fun s hs t ht hst => ?_⟩
  have h1 : dist (φ s) (φ t) < Real.log ρ := hκU s hs t ht (by rw [Real.dist_eq]; exact hst)
  rw [Real.dist_eq, abs_lt] at h1
  rw [show ρ * Real.exp (φ t) = Real.exp (φ t + Real.log ρ) by
    rw [Real.exp_add, Real.exp_log (by linarith), mul_comm]]
  exact Real.exp_le_exp.mpr (by linarith [h1.2])

/-- The Riemann comparison for the arc-length reparametrization: the cost of the reparametrized curve for the weight
`e^{ξ f}` is at most `ρ²` times the cost of the original curve for the weight `e^{ξ(g+f)}`. -/
theorem riemann_arc {ξ : ℝ} {f g : ℂ → ℝ} {φ q : ℝ → ℂ} {s : ℝ → ℝ} {T L : ℝ} (hT : 0 ≤ T)
    (hL : s T = L) (hs0 : s 0 = 0) (hqp : ∀ t ∈ Icc 0 T, q (s t) = φ t)
    (hscont : ContinuousOn s (Icc 0 T))
    (hsinc : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → s a ≤ s b ∧
      ENNReal.ofReal (s b - s a) ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (φ t))))
    (hφc : ContinuousOn (fun t => ξ * f (φ t)) (Icc 0 T)) {ρ : ℝ} (hρ : 1 < ρ) :
    ∫⁻ τ in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q τ))) ≤
      ENNReal.ofReal (ρ * ρ) * ∫⁻ t in Icc 0 T,
        ENNReal.ofReal (Real.exp (ξ * f (φ t))) * ENNReal.ofReal (Real.exp (ξ * g (φ t))) := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨κ, hκ, hmod⟩ := exists_exp_modulus hφc hρ
  -- the uniform partition of [0, T]
  set m := κ with hm_def
  set n : ℕ := ⌈T / m⌉₊ + 1 with hn_def
  have hnpos : (0 : ℝ) < n := by positivity
  set Δ := T / n with hΔ_def
  have hΔ0 : 0 ≤ Δ := div_nonneg hT hnpos.le
  have hΔκ : Δ < κ := by
    have h1 : T / m ≤ (⌈T / m⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈T / m⌉₊ : ℝ) < (n : ℝ) := by rw [hn_def]; push_cast; linarith
    rw [hΔ_def, div_lt_iff₀ hnpos]
    rw [div_le_iff₀ hκ] at h1
    nlinarith
  set t : ℕ → ℝ := fun i => (i : ℝ) * Δ with ht_def
  have ht0 : t 0 = 0 := by simp [ht_def]
  have htn : t n = T := by
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have : (n : ℝ) * (T / n) = T := by field_simp
    exact this
  have htmono : Monotone t := fun i j hij => by
    simp only [ht_def]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hΔ0
  have htmem : ∀ i ≤ n, t i ∈ Icc 0 T := fun i hi =>
    ⟨mul_nonneg (Nat.cast_nonneg i) hΔ0, htn ▸ htmono hi⟩
  have hte : ∀ i, t (i + 1) - t i = Δ := fun i => by
    simp only [ht_def]
    push_cast
    ring
  -- the arc-length points (clamped to [0, T])
  set τ : ℕ → ℝ := fun i => s (min (t i) T) with hτ_def
  have hmemT : ∀ i, min (t i) T ∈ Icc 0 T := fun i =>
    ⟨le_min (mul_nonneg (Nat.cast_nonneg i) hΔ0) hT, min_le_right _ _⟩
  have hτmono : Monotone τ := fun i j hij =>
    (hsinc _ (hmemT i) _ (hmemT j) (min_le_min_right _ (htmono hij))).1
  have hτt : ∀ i ≤ n, τ i = s (t i) := fun i hi => by
    simp only [hτ_def]
    rw [min_eq_left (htmem i hi).2]
  have hτ0 : τ 0 = 0 := by
    simp only [hτ_def, ht0, min_eq_left hT, hs0]
  have hτn : τ n = L := by
    simp only [hτ_def, htn, min_self, hL]
  -- one piece
  have hpiece : ∀ i < n, ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ'))) ≤
      ENNReal.ofReal (ρ * ρ) * ∫⁻ t' in Icc (t i) (t (i + 1)),
        ENNReal.ofReal (Real.exp (ξ * f (φ t'))) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
    intro i hi
    have hti : t i ∈ Icc 0 T := htmem i (by omega)
    have hti1 : t (i + 1) ∈ Icc 0 T := htmem (i + 1) (by omega)
    have hle : t i ≤ t (i + 1) := htmono (Nat.le_succ i)
    have hτi : τ i = s (t i) := hτt i (by omega)
    have hτi1 : τ (i + 1) = s (t (i + 1)) := hτt (i + 1) (by omega)
    set bi : ℝ := Real.exp (ξ * f (φ (t i))) with hbi_def
    have hbi0 : 0 < bi := Real.exp_pos _
    have hq_le : ∀ τ' ∈ Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ'))) ≤
        ENNReal.ofReal (ρ * bi) := by
      intro τ' hτ'
      rw [hτi, hτi1] at hτ'
      obtain ⟨t', ht', hst'⟩ := intermediate_value_Icc hle
        (hscont.mono (Icc_subset_Icc hti.1 hti1.2)) ⟨hτ'.1, hτ'.2⟩
      have ht'T : t' ∈ Icc 0 T := ⟨hti.1.trans ht'.1, ht'.2.trans hti1.2⟩
      have hqeq : q τ' = φ t' := by rw [← hst', hqp t' ht'T]
      rw [hqeq]
      apply ENNReal.ofReal_le_ofReal
      have hnn : 0 ≤ t' - t i := by linarith [ht'.1]
      have hdist : |t' - t i| < κ := by
        rw [abs_of_nonneg hnn]
        linarith [ht'.2, hte i]
      have hm : Real.exp (ξ * f (φ t')) ≤ ρ * Real.exp (ξ * f (φ (t i))) :=
        hmod t' ht'T (t i) hti hdist
      exact hm
    have hτint : ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ'))) ≤
        ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) := by
      calc _ ≤ ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (ρ * bi) :=
            setLIntegral_mono' measurableSet_Icc hq_le
        _ = ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) := by
            rw [setLIntegral_const, Real.volume_Icc]
    have hI_le : ENNReal.ofReal (τ (i + 1) - τ i) ≤
        ∫⁻ t' in Icc (t i) (t (i + 1)), ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
      rw [hτi, hτi1]
      exact (hsinc (t i) hti (t (i + 1)) hti1 hle).2
    have hstep : ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) ≤
        ∫⁻ t' in Icc (t i) (t (i + 1)), ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul_of_nonneg_left hI_le (by positivity)
    have hstep2 : ∫⁻ t' in Icc (t i) (t (i + 1)), ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) ≤
        ENNReal.ofReal (ρ * ρ) * ∫⁻ t' in Icc (t i) (t (i + 1)),
          ENNReal.ofReal (Real.exp (ξ * f (φ t'))) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc (fun t' ht' => ?_)
      have ht'T : t' ∈ Icc 0 T := ⟨hti.1.trans ht'.1, ht'.2.trans hti1.2⟩
      have hdist : |t i - t'| < κ := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht'.1] : (0 : ℝ) ≤ t' - t i)]
        linarith [ht'.2, hte i]
      have hbi_le : bi ≤ ρ * Real.exp (ξ * f (φ t')) := hmod (t i) hti t' ht'T hdist
      have hA : ENNReal.ofReal (ρ * bi) ≤
          ENNReal.ofReal (ρ * ρ) * ENNReal.ofReal (Real.exp (ξ * f (φ t'))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left hbi_le hρ0.le
        nlinarith [this]
      calc ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (Real.exp (ξ * g (φ t')))
          ≤ (ENNReal.ofReal (ρ * ρ) * ENNReal.ofReal (Real.exp (ξ * f (φ t')))) *
              ENNReal.ofReal (Real.exp (ξ * g (φ t'))) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = ENNReal.ofReal (ρ * ρ) * (ENNReal.ofReal (Real.exp (ξ * f (φ t'))) *
              ENNReal.ofReal (Real.exp (ξ * g (φ t')))) := by ring
    calc ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ')))
        ≤ ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) := hτint
      _ ≤ _ := hstep
      _ ≤ _ := hstep2
  -- summing the pieces
  have hadj := sum_lintegral_Icc_adjacent (fun τ' => ENNReal.ofReal (Real.exp (ξ * f (q τ')))) τ hτmono n
  have hadjt := sum_lintegral_Icc_adjacent
    (fun t' => ENNReal.ofReal (Real.exp (ξ * f (φ t'))) * ENNReal.ofReal (Real.exp (ξ * g (φ t')))) t htmono n
  rw [hτ0, hτn] at hadj
  rw [ht0, htn] at hadjt
  rw [← hadj, ← hadjt, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.mp hi)

theorem IsEuclideanLengthMetric.curveLength_ne_top_of_mem {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {w : ℝ} (hw : w ∈ Icc 0 T) :
    curveLength (innerDist D ξ g) p 0 w ≠ ⊤ :=
  ne_top_of_le_ne_top hC ((hD.curveLength_innerDist_le_cost hfin hp (hu := le_rfl) (hv := hw.2)).trans
    (lintegral_mono_set (Icc_subset_Icc le_rfl hw.2)))

theorem IsEuclideanLengthMetric.arc_sinc {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {a b : ℝ} (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    (curveLength (innerDist D ξ g) p 0 a).toReal ≤ (curveLength (innerDist D ξ g) p 0 b).toReal ∧
      ENNReal.ofReal ((curveLength (innerDist D ξ g) p 0 b).toReal -
        (curveLength (innerDist D ξ g) p 0 a).toReal) ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
  have hadd := curveLength_innerDist_add hD hg hfin p (a := 0) (b := a) (c := b) ha.1 hab
  have hXI : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
    ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc ha.1 hb.2))
  have hX : curveLength (innerDist D ξ g) p a b ≠ ⊤ :=
    ne_top_of_le_ne_top hXI (hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2))
  have hsum := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (hD.curveLength_ne_top_of_mem hfin hp hC ha) hX] at hsum
  have hdiff : (curveLength (innerDist D ξ g) p 0 b).toReal -
      (curveLength (innerDist D ξ g) p 0 a).toReal = (curveLength (innerDist D ξ g) p a b).toReal := by
    linarith
  have hnn : 0 ≤ (curveLength (innerDist D ξ g) p a b).toReal := ENNReal.toReal_nonneg
  refine ⟨by linarith, ?_⟩
  rw [hdiff, ENNReal.ofReal_toReal hX]
  exact hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2)

theorem IsEuclideanLengthMetric.arc_continuousOn {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) :
    ContinuousOn (fun t => (curveLength (innerDist D ξ g) p 0 t).toReal) (Icc 0 T) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (integral_small_near (F := fun s => ENNReal.ofReal (Real.exp (ξ * g (p s)))) hC ht)
  rw [ENNReal.toReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun v => dist_nonneg
  · filter_upwards [self_mem_nhdsWithin] with v hv
    rw [Real.dist_eq, abs_sub_comm]
    exact hD.abs_sub_arc_le hg hfin hp hC ht hv

theorem le_of_forall_ofReal_mul_le {W C : ENNReal} (hC : C ≠ ⊤)
    (h : ∀ ρ : ℝ, 1 < ρ → W ≤ ENNReal.ofReal (ρ * ρ) * C) : W ≤ C := by
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (ρ * ρ) * C) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal (1 * 1) * C)) := by
    have h1 : Tendsto (fun ρ : ℝ => ρ * ρ) (𝓝[>] 1) (𝓝 (1 * 1)) :=
      ((continuous_id.mul continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
    exact ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto _).comp h1) (Or.inr hC)
  have hge := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact h ρ hρ)
  simpa using hge

theorem IsEuclideanLengthMetric.weylScaling_innerDist_le_direct {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) {x y : ℂ}
    (h0 : p 0 = x) (hT : p T = y)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) ≠ ⊤) :
    weylScaling (innerDist D ξ g) ξ f x y ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) := by
  have hGc := IsEuclideanLengthMetric.cost_g_ne_top hf hp hC
  have hfinite : curveLength (innerDist D ξ g) p 0 T ≠ ⊤ :=
    hD.curveLength_ne_top_of_mem hfin hp hGc ⟨hp.1, le_rfl⟩
  obtain ⟨q, hq, hq0, hqT, hqp⟩ := hD.exists_arclength_innerDist hg hfin hp.1 hfinite
    (fun t ht => hD.innerDist_tendsto_of_cost hfin hp hGc ht)
  have hs0 : (curveLength (innerDist D ξ g) p 0 0).toReal = 0 := by
    have h := hD.curveLength_innerDist_le_cost hfin hp (u := 0) (v := 0) (hu := le_rfl) (hv := hp.1)
    have hz : ∫⁻ t in Icc (0 : ℝ) 0, ENNReal.ofReal (Real.exp (ξ * g (p t))) = 0 := by
      simp
    rw [hz] at h
    rw [nonpos_iff_eq_zero.mp h, ENNReal.toReal_zero]
  have hφc : ContinuousOn (fun t => ξ * f (p t)) (Icc 0 T) :=
    (continuous_const.mul hf).comp_continuousOn hp.2.1
  have hρ : ∀ ρ : ℝ, 1 < ρ → weylScaling (innerDist D ξ g) ξ f x y ≤
      ENNReal.ofReal (ρ * ρ) * ∫⁻ t in Icc 0 T,
        ENNReal.ofReal (Real.exp (ξ * f (p t))) * ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro ρ hρ1
    have hR := riemann_arc (ξ := ξ) (f := f) (g := g) (φ := p) (q := q)
      (s := fun t => (curveLength (innerDist D ξ g) p 0 t).toReal) (T := T)
      (L := (curveLength (innerDist D ξ g) p 0 T).toReal) hp.1 rfl hs0 hqp
      (hD.arc_continuousOn hg hfin hp hGc)
      (fun a ha b hb hab => hD.arc_sinc hg hfin hp hGc ha hb hab) hφc hρ1
    have hW : weylScaling (innerDist D ξ g) ξ f x y ≤
        ∫⁻ τ in Icc 0 (curveLength (innerDist D ξ g) p 0 T).toReal,
          ENNReal.ofReal (Real.exp (ξ * f (q τ))) := by
      unfold weylScaling
      exact (iInf₂_le _ q).trans ((iInf₂_le hq (hq0.trans h0)).trans (iInf_le _ (hqT.trans hT)))
    exact hW.trans hR
  have hcongr : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) *
      ENNReal.ofReal (Real.exp (ξ * g (p t))) =
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) :=
    setLIntegral_congr_fun measurableSet_Icc (fun t _ => by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring)
  have hCfin : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) *
      ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ := by
    rw [hcongr]
    exact hC
  rw [← hcongr]
  exact le_of_forall_ofReal_mul_le hCfin hρ


/-- LP form of `WeylMetricCompositionContinuousOuterFrozen` (`FirstPass/Frozen/S11j.lean:117`): the same binders and
conclusion, with the LP predicates `IsEuclideanLengthMetric` and `weylScaling` of `LatticeProb/LQG/LengthMetric.lean`. -/
def WeylMetricCompositionContinuousOuterLP : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ (D : ℂ → ℂ → ℝ) (g f : ℂ → ℝ), IsEuclideanLengthMetric D →
    ContinuousOn g {z | z ≠ 0} → Continuous f →
    (∀ x y, weylScaling D ξ g x y ≠ ⊤) →
    ∀ x y, weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ f x y =
      weylScaling D ξ (fun z => g z + f z) x y

/-- **Derived**: the LP form `WeylMetricCompositionContinuousOuterLP` holds, with no hypothesis added (LP copy of
`weylMetricCompositionContinuousOuter_derived`, `FirstPass/Phase2/WeylCompositionOuterDerived.lean:1221`). -/
theorem weylMetricCompositionContinuousOuter_lp : WeylMetricCompositionContinuousOuterLP := by
  intro ξ _ D g f hD hg hf hfin x y
  apply le_antisymm
  · show weylScaling (innerDist D ξ g) ξ f x y ≤ ⨅ (T : ℝ) (p : ℝ → ℂ) (_ : IsLengthParametrized D p T)
      (_ : p 0 = x) (_ : p T = y), ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t))))
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
    by_cases hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) = ⊤
    · rw [hC]
      exact le_top
    · exact hD.weylScaling_innerDist_le_direct hg hfin hf hp h0 hT hC
  · show weylScaling D ξ (fun z => g z + f z) x y ≤ ⨅ (L : ℝ) (q : ℝ → ℂ)
      (_ : IsLengthParametrized (innerDist D ξ g) q L) (_ : q 0 = x) (_ : q L = y),
        ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t)))
    refine le_iInf fun L => le_iInf fun q => le_iInf fun hq => le_iInf fun h0 => le_iInf fun hL => ?_
    exact hD.weylScaling_le_iterated hg hfin hf hq h0 hL

end LatticeProb.LQG
