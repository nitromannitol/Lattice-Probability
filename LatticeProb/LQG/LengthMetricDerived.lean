import Mathlib
import LatticeProb.LQG.LengthMetric

/-!
# Length-metric statements

Two statements of the deterministic metric geometry of the γ-Liouville quantum gravity (LQG) metric, in the vocabulary of
`LatticeProb/LQG/LengthMetric.lean`, each with the same binders, quantifiers and conclusion as in its source:

* `weylScaledEuclidean_derived`: the Weyl scaling `e^{ξ f} · D` of a Euclidean length metric `D` by a continuous
  compactly supported `f` is a Euclidean length metric (Gwynne-Miller, arXiv:1905.00383, (1.7)-(1.8)).
* `internalMetricClosedEqIInfThickening_derived`: for a closed set `C` and `x, y ∈ C`, the internal metric of `C` is the
  infimum over `n` of the suprema over `k` of the internal metrics of `thickening ((k+1)⁻¹) (C ∩ closedBall 0 (n+1))`.

Both statements are proved with no hypothesis added. The proofs use the arc-length reparametrization of a curve by its
`D`-length (Burago-Burago-Ivanov length structures), the comparison bounds of the Weyl scaling, and concatenation and
reversal of curves.

Provenance: the arc-length and Weyl comparison lemmas of `LatticeProb/LQG/WeylInternalClosed.lean` (provenance recorded
there) are adapted here, together with the auxiliary path lemmas and the proofs of the Weyl scaling and of the internal
metric of closed sets in the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity,
arXiv:2208.11795], with namespace `LatticeProb.LQG`. The file imports only Mathlib and
`LatticeProb.LQG.LengthMetric`. `LatticeProb/LQG/WeylInternalClosed.lean` imports this file and uses its declarations
so the two modules can be imported together.
-/

namespace LatticeProb.LQG

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The image of the cumulative variation of a continuous bounded-variation
curve on a closed interval is the interval of its total length. -/
theorem variationOnFromTo_image_Icc {E : Type*} [PseudoMetricSpace E]
    (p : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hp : ContinuousOn p (Icc 0 T)) (hvar : BoundedVariationOn p (Icc 0 T)) :
    variationOnFromTo p (Icc 0 T) 0 '' Icc 0 T =
      Icc 0 (eVariationOn p (Icc 0 T)).toReal := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hcont : ContinuousOn (variationOnFromTo p (Icc 0 T) 0) (Icc 0 T) := by
    intro x hx
    exact (hvar.continuousWithinAt_variationOnFromTo_iff hzero hx).2 (hp x hx)
  have hmono := variationOnFromTo.monotoneOn hvar.locallyBoundedVariationOn hzero
  rw [hcont.image_Icc_of_monotoneOn hT hmono, variationOnFromTo.self,
    variationOnFromTo.eq_of_le p (Icc 0 T) hT, inter_self]

/-- Natural parametrization of a finite-length continuous curve has unit
speed on its full length interval and agrees with both endpoints. -/
theorem naturalParameterization_unitSpeed_Icc {E : Type*} [MetricSpace E]
    (p : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hp : ContinuousOn p (Icc 0 T)) (hvar : BoundedVariationOn p (Icc 0 T)) :
    HasUnitSpeedOn (naturalParameterization p (Icc 0 T) 0)
        (Icc 0 (eVariationOn p (Icc 0 T)).toReal) ∧
      naturalParameterization p (Icc 0 T) 0 0 = p 0 ∧
      naturalParameterization p (Icc 0 T) 0 (eVariationOn p (Icc 0 T)).toReal = p T := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hlocal := hvar.locallyBoundedVariationOn
  have himage := variationOnFromTo_image_Icc p hT hp hvar
  have hs := has_unit_speed_naturalParameterization p hlocal hzero
  rw [himage] at hs
  refine ⟨hs, ?_, ?_⟩
  · have h := edist_naturalParameterization_eq_zero hlocal hzero hzero
    rw [variationOnFromTo.self] at h
    exact edist_eq_zero.mp h
  · have h := edist_naturalParameterization_eq_zero hlocal hzero hTmem
    rw [variationOnFromTo.eq_of_le p (Icc 0 T) hT, inter_self] at h
    exact edist_eq_zero.mp h

/-- A unit-speed curve on an interval is one-Lipschitz on that interval. -/
theorem HasUnitSpeedOn.lipschitzOnWith_Icc {E : Type*} [PseudoMetricSpace E]
    {p : ℝ → E} {a b : ℝ} (hp : HasUnitSpeedOn p (Icc a b)) :
    LipschitzOnWith 1 p (Icc a b) := by
  intro x hx y hy
  change edist (p x) (p y) ≤ (1 : ℝ≥0∞) * edist x y
  simp only [one_mul]
  rcases le_total x y with hxy | hyx
  · have hv := eVariationOn.edist_le p
      (s := Icc a b ∩ Icc x y) (x := x) (y := y)
      ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
    have hs : eVariationOn p (Icc a b ∩ Icc x y) = ENNReal.ofReal (y - x) := by
      simpa only [NNReal.coe_one, one_mul] using hp hx hy
    rw [hs] at hv
    have hdist : edist x y = ENNReal.ofReal (y - x) := by
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      congr 1
      ring
    exact hdist ▸ hv
  · have hv := eVariationOn.edist_le p
      (s := Icc a b ∩ Icc y x) (x := y) (y := x)
      ⟨hy, le_rfl, hyx⟩ ⟨hx, hyx, le_rfl⟩
    have hs : eVariationOn p (Icc a b ∩ Icc y x) = ENNReal.ofReal (x - y) := by
      simpa only [NNReal.coe_one, one_mul] using hp hy hx
    rw [hs] at hv
    have hdist : edist x y = ENNReal.ofReal (x - y) := by
      rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [edist_comm] at hv
    exact hdist ▸ hv


private structure ConcatLengthPoint where
  val : ℂ

/-- Curves agreeing on an interval have the same length there. -/
theorem curveLength_eq_of_eqOn {D : ℂ → ℂ → ℝ} {p q : ℝ → ℂ} {a b : ℝ}
    (h : EqOn p q (Icc a b)) : curveLength D p a b = curveLength D q a b := by
  unfold curveLength
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  rw [h (n.2.2.2 (i + 1)), h (n.2.2.2 i)]

/-- Curve length is unchanged by translating the parameter. -/
theorem IsEuclideanLengthMetric.curveLength_translate
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (c a b : ℝ) :
    curveLength D (fun t => p (t - c)) a b = curveLength D p (a - c) (b - c) := by
  let : MetricSpace ConcatLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ConcatLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (q : ℝ → ℂ) (s t : ℝ) :
      curveLength D q s t = eVariationOn (fun r => (⟨q r⟩ : ConcatLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let q : ℝ → ConcatLengthPoint := fun t => ⟨p t⟩
  have hmono : MonotoneOn (fun t : ℝ => t - c) (Icc a b) := by
    intro x hx y hy hxy
    linarith
  have himage : (fun t : ℝ => t - c) '' Icc a b = Icc (a - c) (b - c) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      refine ⟨x + c, ?_, by ring⟩
      constructor <;> linarith [hx.1, hx.2]
  calc
    curveLength D (fun t => p (t - c)) a b =
        eVariationOn (q ∘ fun t : ℝ => t - c) (Icc a b) := hcurve _ _ _
    _ = eVariationOn q (Icc (a - c) (b - c)) := by
      rw [eVariationOn.comp_eq_of_monotoneOn q _ hmono, himage]
    _ = curveLength D p (a - c) (b - c) := (hcurve _ _ _).symm


/-- Translating a subinterval to start at zero preserves length
parametrization. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_subcurve
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IsLengthParametrized D (fun t => p (a + t)) (b - a) := by
  refine ⟨sub_nonneg.mpr hab, ?_, ?_⟩
  · apply hp.2.1.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change 0 ≤ a + t ∧ a + t ≤ T
    constructor <;> linarith [ht.1, ht.2]
  · intro s t hs hst ht
    have heq : (fun t : ℝ => p (a + t)) = fun t => p (t - (-a)) := by
      funext t
      congr 1
      ring
    rw [heq, hD.curveLength_translate]
    have h := hp.2.2 (s - -a) (t - -a) (by linarith) (by linarith) (by linarith)
    rw [h]
    congr 1
    ring


private structure ReverseLengthPoint where
  val : ℂ

/-- Reversing time changes the interval of a curve length to its reflected
interval. -/
theorem IsEuclideanLengthMetric.curveLength_reverse
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (T a b : ℝ) :
    curveLength D (fun t => p (T - t)) a b = curveLength D p (T - b) (T - a) := by
  let : MetricSpace ReverseLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ReverseLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (q : ℝ → ℂ) (s t : ℝ) :
      curveLength D q s t = eVariationOn (fun r => (⟨q r⟩ : ReverseLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let q : ℝ → ReverseLengthPoint := fun t => ⟨p t⟩
  have hanti : AntitoneOn (fun t : ℝ => T - t) (Icc a b) := by
    intro x hx y hy hxy
    linarith
  have himage : (fun t : ℝ => T - t) '' Icc a b = Icc (T - b) (T - a) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      refine ⟨T - x, ?_, by ring⟩
      constructor <;> linarith [hx.1, hx.2]
  calc
    curveLength D (fun t => p (T - t)) a b =
        eVariationOn (q ∘ fun t : ℝ => T - t) (Icc a b) := hcurve _ _ _
    _ = eVariationOn q (Icc (T - b) (T - a)) := by
      rw [eVariationOn.comp_eq_of_antitoneOn q _ hanti, himage]
    _ = curveLength D p (T - b) (T - a) := (hcurve _ _ _).symm

/-- Reversing a length-parametrized curve preserves its parametrization. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_reverse
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    IsLengthParametrized D (fun t => p (T - t)) T := by
  refine ⟨hp.1, ?_, ?_⟩
  · apply hp.2.1.comp (continuous_const.sub continuous_id).continuousOn
    intro t ht
    change T - t ∈ Icc (0 : ℝ) T
    constructor <;> linarith [ht.1, ht.2]
  · intro s t hs hst ht
    rw [hD.curveLength_reverse, hp.2.2 (T - t) (T - s) (by linarith) (by linarith) (by linarith)]
    congr 1
    ring


private structure ArcLengthPoint where
  val : ℂ

/-- A continuous curve of finite length can be parametrized by metric
arc length, preserving its endpoints, total length and cumulative-length tracking. -/
theorem IsEuclideanLengthMetric.exists_lengthParametrized_with_tracking
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (curveLength D p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength D p 0 T).toReal = p T ∧
      ∀ t ∈ Icc 0 T, q (curveLength D p 0 t).toReal = p t := by
  let : MetricSpace ArcLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ArcLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hopen (U : Set ℂ) : IsOpen {z : ArcLengthPoint | z.val ∈ U} ↔ IsOpen U := by
    rw [Metric.isOpen_iff, hD.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hεx⟩ := h ⟨x⟩ hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      apply hεx
      change D y x < ε
      rw [hD.symm]
      exact hy
    · intro h ⟨x⟩ hx
      obtain ⟨ε, hε, hεx⟩ := h x hx
      refine ⟨ε, hε, ?_⟩
      intro ⟨y⟩ hy
      apply hεx y
      change D y x < ε at hy
      rwa [hD.symm] at hy
  have hmk : Continuous (fun z : ℂ => (⟨z⟩ : ArcLengthPoint)) := by
    rw [continuous_def]
    intro U hU
    apply (hopen _).mp
    convert hU using 1
    ext ⟨x⟩
    rfl
  have hval : Continuous (fun z : ArcLengthPoint => z.val) := by
    rw [continuous_def]
    intro U hU
    exact (hopen U).mpr hU
  let r : ℝ → ArcLengthPoint := fun t => ⟨p t⟩
  have hcurve (q : ℝ → ℂ) (a b : ℝ) :
      curveLength D q a b = eVariationOn (fun t => (⟨q t⟩ : ArcLengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  have hrcont : ContinuousOn r (Icc 0 T) := hmk.comp_continuousOn hp
  have hrvar : BoundedVariationOn r (Icc 0 T) := by
    change eVariationOn r (Icc 0 T) ≠ ∞
    rw [← hcurve]
    exact hfinite.ne
  obtain ⟨hspeed, hstart, hend⟩ := naturalParameterization_unitSpeed_Icc r hT hrcont hrvar
  let R := (curveLength D p 0 T).toReal
  have hs : HasUnitSpeedOn (naturalParameterization r (Icc 0 T) 0) (Icc 0 R) := by
    simpa only [R, hcurve] using hspeed
  let q : ℝ → ℂ := fun t => (naturalParameterization r (Icc 0 T) 0 t).val
  have hqcont : ContinuousOn q (Icc 0 R) :=
    hval.comp_continuousOn (HasUnitSpeedOn.lipschitzOnWith_Icc hs).continuousOn
  refine ⟨q, ⟨ENNReal.toReal_nonneg, hqcont, ?_⟩, ?_, ?_, ?_⟩
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
  · exact congrArg ArcLengthPoint.val hstart
  · have h := congrArg ArcLengthPoint.val hend
    simpa only [q, r, R, hcurve] using h

  · intro t ht
    have h := edist_naturalParameterization_eq_zero hrvar.locallyBoundedVariationOn
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht
    rw [variationOnFromTo.eq_of_le r (Icc 0 T) ht.1,
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)] at h
    have heq := edist_eq_zero.mp h
    have hv := congrArg ArcLengthPoint.val heq
    simpa only [q, r, hcurve] using hv


private structure ReparamLengthPoint where
  val : ℂ

/-- A continuous increasing change of parameter preserves metric length. -/
theorem IsEuclideanLengthMetric.curveLength_comp_of_monotoneOn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hφcont : ContinuousOn φ (Icc a b)) (hφmono : MonotoneOn φ (Icc a b)) :
    curveLength D (p ∘ φ) a b = curveLength D p (φ a) (φ b) := by
  let : MetricSpace ReparamLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ReparamLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (q : ℝ → ℂ) (s t : ℝ) :
      curveLength D q s t = eVariationOn (fun r => (⟨q r⟩ : ReparamLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let q : ℝ → ReparamLengthPoint := fun t => ⟨p t⟩
  have himage : φ '' Icc a b = Icc (φ a) (φ b) :=
    hφcont.image_Icc_of_monotoneOn hab hφmono
  calc
    _ = eVariationOn (q ∘ φ) (Icc a b) := hcurve _ _ _
    _ = eVariationOn q (Icc (φ a) (φ b)) := by
      rw [eVariationOn.comp_eq_of_monotoneOn q φ hφmono, himage]
    _ = _ := (hcurve _ _ _).symm

/-- For a continuous finite-length curve, cumulative length is continuous,
increasing and ranges over the whole interval of total length. -/
theorem IsEuclideanLengthMetric.cumulative_curveLength_properties
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    let L : ℝ → ℝ := fun t => (curveLength D p 0 t).toReal
    ContinuousOn L (Icc 0 T) ∧ MonotoneOn L (Icc 0 T) ∧ L 0 = 0 ∧
      L '' Icc 0 T = Icc 0 (L T) := by
  let : MetricSpace ReparamLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ReparamLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hopen (U : Set ℂ) : IsOpen {z : ReparamLengthPoint | z.val ∈ U} ↔ IsOpen U := by
    rw [Metric.isOpen_iff, hD.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hεx⟩ := h ⟨x⟩ hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      apply hεx
      change D y x < ε
      rwa [hD.symm]
    · intro h ⟨x⟩ hx
      obtain ⟨ε, hε, hεx⟩ := h x hx
      refine ⟨ε, hε, ?_⟩
      intro ⟨y⟩ hy
      apply hεx y
      change D y x < ε at hy
      rwa [hD.symm] at hy
  have hmk : Continuous (fun z : ℂ => (⟨z⟩ : ReparamLengthPoint)) := by
    rw [continuous_def]
    intro U hU
    apply (hopen _).mp
    convert hU using 1
    ext ⟨x⟩
    rfl
  let q : ℝ → ReparamLengthPoint := fun t => ⟨p t⟩
  have hcurve (s t : ℝ) : curveLength D p s t = eVariationOn q (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  have hqcont : ContinuousOn q (Icc 0 T) := hmk.comp_continuousOn hp
  have hvar : BoundedVariationOn q (Icc 0 T) := by
    change eVariationOn q (Icc 0 T) ≠ ∞
    rw [← hcurve]
    exact hfinite.ne
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have heq : EqOn (variationOnFromTo q (Icc 0 T) 0)
      (fun t => (curveLength D p 0 t).toReal) (Icc 0 T) := by
    intro t ht
    rw [variationOnFromTo.eq_of_le q (Icc 0 T) ht.1,
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2), ← hcurve]
  have hcont : ContinuousOn (variationOnFromTo q (Icc 0 T) 0) (Icc 0 T) := by
    intro t ht
    exact (hvar.continuousWithinAt_variationOnFromTo_iff hzero ht).2 (hqcont t ht)
  have hmono := variationOnFromTo.monotoneOn hvar.locallyBoundedVariationOn hzero
  have hLzero : (curveLength D p 0 0).toReal = 0 := by
    have h := heq hzero
    rw [variationOnFromTo.self] at h
    exact h.symm
  have himage := variationOnFromTo_image_Icc q hT hqcont hvar
  refine ⟨hcont.congr heq.symm, ?_, hLzero, ?_⟩
  · intro x hx y hy hxy
    rw [← heq hx, ← heq hy]
    exact hmono hx hy hxy
  · rw [← image_congr heq, himage, ← hcurve]


/-- A `D`-arclength parametrized curve `q` on `[0, L]` with weight `ξ f ≤ B` along it: the sub-arc `r ↦ q (a + r)` is a
competitor in `weylScaling`, so `weylScaling D ξ f (q a) (q b) ≤ e^B (b - a)` for `0 ≤ a ≤ b ≤ L`. -/
theorem weylScaling_le_of_subarc {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized D q L)
    (hw : ∀ x ∈ Icc 0 L, ξ * f (q x) ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    weylScaling D ξ f (q a) (q b) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
  have hsub : IsLengthParametrized D (fun t => q (a + t)) (b - a) :=
    hD.isLengthParametrized_subcurve hq ha hab hb
  have h0 : (fun t => q (a + t)) 0 = q a := by simp
  have hT : (fun t => q (a + t)) (b - a) = q b := by simp
  refine iInf_le_of_le (b - a) (iInf_le_of_le (fun t => q (a + t)) (iInf_le_of_le hsub
    (iInf_le_of_le h0 (iInf_le_of_le hT ?_))))
  calc ∫⁻ t in Icc 0 (b - a), ENNReal.ofReal (Real.exp (ξ * f ((fun t => q (a + t)) t)))
      ≤ ∫⁻ _ in Icc 0 (b - a), ENNReal.ofReal (Real.exp B) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact hw (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    _ = ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]

/-- Both orientations: for `0 ≤ a ≤ b ≤ L`, `weylScaling (q a) (q b)` and `weylScaling (q b) (q a)` are at most
`e^B (b - a)`. The second follows from the first applied to the reversed curve `t ↦ q (L - t)`. -/
theorem weylScaling_le_of_subarc_both {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized D q L)
    (hw : ∀ x ∈ Icc 0 L, ξ * f (q x) ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    weylScaling D ξ f (q a) (q b) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) ∧
      weylScaling D ξ f (q b) (q a) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
  refine ⟨weylScaling_le_of_subarc hD hq hw ha hab hb, ?_⟩
  have hr : IsLengthParametrized D (fun t => q (L - t)) L := hD.isLengthParametrized_reverse hq
  have hwr : ∀ x ∈ Icc 0 L, ξ * f ((fun t => q (L - t)) x) ≤ B := fun x hx =>
    hw (L - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := weylScaling_le_of_subarc hD hr hwr (a := L - b) (b := L - a)
    (by linarith) (by linarith) (by linarith)
  simp only [sub_sub_cancel] at h
  rw [show L - a - (L - b) = b - a by ring] at h
  exact h

/-- Telescoping bound for partition sums: if `σ` is nondecreasing with `0 ≤ σ 0` and `σ N ≤ L`, and each term is at most
`c (σ (i+1) - σ i)`, the sum over `range N` is at most `c L`. -/
theorem sum_le_of_telescope {c : ℝ≥0∞} {σ : ℕ → ℝ} {L : ℝ} {d : ℕ → ℝ≥0∞} (N : ℕ)
    (hσ : ∀ i, σ i ≤ σ (i + 1)) (h0 : 0 ≤ σ 0) (hN : σ N ≤ L)
    (hd : ∀ i ∈ Finset.range N, d i ≤ c * ENNReal.ofReal (σ (i + 1) - σ i)) :
    ∑ i ∈ Finset.range N, d i ≤ c * ENNReal.ofReal L := by
  calc ∑ i ∈ Finset.range N, d i
      ≤ ∑ i ∈ Finset.range N, c * ENNReal.ofReal (σ (i + 1) - σ i) := Finset.sum_le_sum hd
    _ = c * ∑ i ∈ Finset.range N, ENNReal.ofReal (σ (i + 1) - σ i) := by rw [Finset.mul_sum]
    _ = c * ENNReal.ofReal (∑ i ∈ Finset.range N, (σ (i + 1) - σ i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hσ i))]
    _ = c * ENNReal.ofReal (σ N - σ 0) := by rw [Finset.sum_range_sub σ N]
    _ ≤ c * ENNReal.ofReal L :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith)) zero_le

/-- A partition bound for the `E`-length of a curve `p` on `[0, 1]` gives a bound for `curveLength E p 0 1`. -/
theorem curveLength_le_of_partition_bound {E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {M : ℝ≥0∞}
    (h : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (p (u (i + 1))) (p (u i))) ≤ M) :
    curveLength E p 0 1 ≤ M := by
  unfold curveLength
  exact iSup_le fun ⟨N, u, hu, hI⟩ => h N u hu hI

/-- For a path `P` in `U`, with `E` the Weyl scaling of `D` by `f` and `ξ f ≤ B` on `U`, the `E`-length of `P` is at most
`e^B` times its `D`-length. The path is reparametrized by its `D`-arclength; each sub-arc is a competitor in `weylScaling`. -/
theorem pathLength_le_of_weylScaling {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ U, ξ * f z ≤ B) {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ U) :
    pathLength E P ≤ ENNReal.ofReal (Real.exp B) * pathLength D P := by
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  unfold pathLength
  by_cases hfin : curveLength D P.extend 0 1 = ⊤
  · rw [hfin, ENNReal.mul_top hc0]
    exact le_top
  have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
  have hcont : ContinuousOn P.extend (Icc 0 1) := P.continuous_extend.continuousOn
  have hPU : ∀ t ∈ Icc (0:ℝ) 1, P.extend t ∈ U := fun t ht => by
    rw [Path.extend_apply P ht]
    exact hP ⟨t, ht⟩
  obtain ⟨q, hq, -, -, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hcont hlt
  obtain ⟨-, hmono, -, himg⟩ := hD.cumulative_curveLength_properties zero_le_one hcont hlt
  have hmono' : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → a ≤ b →
      (curveLength D P.extend 0 a).toReal ≤ (curveLength D P.extend 0 b).toReal :=
    fun a b ha hb hab => hmono ha hb hab
  -- the image of `q` on `[0, L]` is the image of `P` on `[0, 1]`, hence lies in `U`
  have hqU : ∀ x ∈ Icc (0:ℝ) (curveLength D P.extend 0 1).toReal, q x ∈ U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (Set.ext_iff.mp himg x).mpr hx
    show q (curveLength D P.extend 0 t).toReal ∈ U
    rw [htrack t ht]
    exact hPU t ht
  have hw : ∀ x ∈ Icc (0:ℝ) (curveLength D P.extend 0 1).toReal, ξ * f (q x) ≤ B :=
    fun x hx => hweight _ (hqU x hx)
  have hsum : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (curveLength D P.extend 0 1).toReal := by
    intro N u hu hI
    have hσ : ∀ i, (curveLength D P.extend 0 (u i)).toReal ≤
        (curveLength D P.extend 0 (u (i + 1))).toReal :=
      fun i => hmono' _ _ (hI i) (hI (i + 1)) (hu (Nat.le_succ i))
    have hd : ∀ i ∈ Finset.range N, ENNReal.ofReal (E (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (Real.exp B) *
          ENNReal.ofReal ((curveLength D P.extend 0 (u (i + 1))).toReal -
            (curveLength D P.extend 0 (u i)).toReal) := by
      intro i _
      have hL : (curveLength D P.extend 0 (u (i + 1))).toReal ≤
          (curveLength D P.extend 0 1).toReal :=
        hmono' _ _ (hI (i + 1)) (right_mem_Icc.mpr zero_le_one) (hI (i + 1)).2
      rw [hscale, ← htrack (u (i + 1)) (hI (i + 1)), ← htrack (u i) (hI i)]
      exact (weylScaling_le_of_subarc_both hD hq hw ENNReal.toReal_nonneg (hσ i) hL).2
    have hN : (curveLength D P.extend 0 (u N)).toReal ≤ (curveLength D P.extend 0 1).toReal :=
      hmono' _ _ (hI N) (right_mem_Icc.mpr zero_le_one) (hI N).2
    exact sum_le_of_telescope (σ := fun i => (curveLength D P.extend 0 (u i)).toReal) N hσ
      ENNReal.toReal_nonneg hN hd
  calc curveLength E P.extend 0 1
      ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (curveLength D P.extend 0 1).toReal :=
        curveLength_le_of_partition_bound (fun N u hu hI => hsum N u hu hI)
    _ = ENNReal.ofReal (Real.exp B) * curveLength D P.extend 0 1 := by
        rw [ENNReal.ofReal_toReal hfin]



section WeylLocalEdges
open Metric

/-- Every point of a length-parametrized curve is within its elapsed length
of the starting point. -/
theorem IsEuclideanLengthMetric.ofReal_dist_start_le_lengthParametrized
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T t : ℝ} (hp : IsLengthParametrized D p T)
    (ht : t ∈ Icc 0 T) :
    ENNReal.ofReal (D (p 0) (p t)) ≤ ENNReal.ofReal T := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else t
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n
    · simpa [u] using ht.1
    · simp [u]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) T := by
    intro n
    rcases n with _ | n
    · simpa [u] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hp.1⟩)
    · simpa [u] using ht
  have h := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 T} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i))))
      ⟨1, ⟨u, hu, humem⟩⟩
  change _ ≤ curveLength D p 0 T at h
  simpa [u, hD.symm, hp.2.2 0 T le_rfl hp.1 le_rfl] using h

/-- A bound on the Weyl exponent along a length-parametrized path bounds
its weighted endpoint distance. -/
theorem weylScaling_le_of_lengthParametrized
    (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) {x y : ℂ}
    {p : ℝ → ℂ} {T B : ℝ} (hp : IsLengthParametrized D p T)
    (h0 : p 0 = x) (hT : p T = y)
    (hweight : ∀ t ∈ Icc 0 T, ξ * f (p t) ≤ B) :
    weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal T := by
  refine (iInf₂_le T p).trans ((iInf₂_le hp h0).trans ((iInf_le _ hT).trans ?_))
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp B) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hweight t ht))
    _ = _ := by simp [lintegral_const, Real.volume_Icc]

end WeylLocalEdges

section WeylPathReverse

/-- Reflection of a closed interval preserves Lebesgue integration. -/
theorem lintegral_Icc_reverse (F : ℝ → ℝ≥0∞) (T : ℝ) :
    (∫⁻ t in Icc (0 : ℝ) T, F (T - t)) = ∫⁻ t in Icc (0 : ℝ) T, F t := by
  have hpre : (fun t : ℝ => T - t) ⁻¹' Icc (0 : ℝ) T = Icc 0 T := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  have hemb : MeasurableEmbedding (fun t : ℝ => T - t) :=
    (Homeomorph.subLeft T).measurableEmbedding
  have hm := ((volume : Measure ℝ).measurePreserving_sub_left T).restrict_preimage_emb
    hemb (Icc (0 : ℝ) T)
  rw [hpre] at hm
  exact hm.lintegral_comp_emb hemb F

/-- Weyl scaling is symmetric for arbitrary weights on a Euclidean length
metric. -/
theorem IsEuclideanLengthMetric.weylScaling_symm
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ) (x y : ℂ) :
    weylScaling D ξ f x y = weylScaling D ξ f y x := by
  have hle (x y : ℂ) : weylScaling D ξ f x y ≤ weylScaling D ξ f y x := by
    unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 =>
      le_iInf fun hT => ?_
    have hrev := hD.isLengthParametrized_reverse hp
    have hrev0 : (fun t => p (T - t)) 0 = x := by simpa using hT
    have hrevT : (fun t => p (T - t)) T = y := by simpa using h0
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * f (p (T - t)))) :=
        (iInf₂_le T (fun t => p (T - t))).trans
          ((iInf₂_le hrev hrev0).trans (iInf_le _ hrevT))
      _ = _ := lintegral_Icc_reverse (fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))) T
  exact le_antisymm (hle x y) (hle y x)

end WeylPathReverse

section WeylPathConcatenation

/-- Curve length is additive across adjacent intervals. -/
theorem IsEuclideanLengthMetric.curveLength_add
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    curveLength D p a b + curveLength D p b c = curveLength D p a c := by
  let : MetricSpace ConcatLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ConcatLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (s t : ℝ) :
      curveLength D p s t = eVariationOn (fun r => (⟨p r⟩ : ConcatLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  rw [hcurve, hcurve, hcurve]
  simpa only [univ_inter] using eVariationOn.Icc_add_Icc
    (fun r => (⟨p r⟩ : ConcatLengthPoint)) (s := univ) hab hbc (mem_univ b)

/-- Joining two length-parametrized curves preserves length parametrization,
provided the joined curve is continuous at the junction. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_concat
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p q r : ℝ → ℂ} {T S : ℝ}
    (hp : IsLengthParametrized D p T) (hq : IsLengthParametrized D q S)
    (hr : ContinuousOn r (Icc 0 (T + S)))
    (hleft : EqOn r p (Icc 0 T))
    (hright : EqOn r (fun t => q (t - T)) (Icc T (T + S))) :
    IsLengthParametrized D r (T + S) := by
  refine ⟨add_nonneg hp.1 hq.1, hr, ?_⟩
  intro a b ha hab hb
  by_cases hbT : b ≤ T
  · rw [curveLength_eq_of_eqOn (hleft.mono (Icc_subset_Icc ha hbT))]
    exact hp.2.2 a b ha hab hbT
  · by_cases haT : T ≤ a
    · rw [curveLength_eq_of_eqOn (hright.mono (Icc_subset_Icc haT hb)),
        hD.curveLength_translate]
      have h := hq.2.2 (a - T) (b - T) (by linarith) (by linarith) (by linarith)
      convert h using 1; congr 1; ring
    · have haT' : a ≤ T := le_of_not_ge haT
      have hTb : T ≤ b := le_of_not_ge hbT
      rw [← hD.curveLength_add r haT' hTb,
        curveLength_eq_of_eqOn (hleft.mono (Icc_subset_Icc ha le_rfl)),
        curveLength_eq_of_eqOn (hright.mono (Icc_subset_Icc le_rfl hb)),
        hD.curveLength_translate,
        hp.2.2 a T ha haT' le_rfl]
      have h := hq.2.2 (T - T) (b - T) (by linarith) (by linarith) (by linarith)
      rw [h, ← ENNReal.ofReal_add (by linarith : 0 ≤ T - a)]
      congr 1
      ring
      all_goals linarith

/-- Two continuous curves with a common endpoint have a continuous
concatenation parametrized by the sum of their durations. -/
theorem continuousOn_length_concat {p q : ℝ → ℂ} {T S : ℝ}
    (hp : ContinuousOn p (Icc 0 T)) (hq : ContinuousOn q (Icc 0 S))
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hjoin : p T = q 0) :
    ContinuousOn (fun t => if t ≤ T then p t else q (t - T)) (Icc 0 (T + S)) := by
  let r : ℝ → ℂ := fun t => if t ≤ T then p t else q (t - T)
  have hleft : EqOn r p (Icc 0 T) := by
    intro t ht
    simp only [r, ite_eq_left ht.2]
  have hright : EqOn r (fun t => q (t - T)) (Icc T (T + S)) := by
    intro t ht
    by_cases htT : t ≤ T
    · have heq : t = T := le_antisymm htT ht.1
      subst t
      simpa [r] using hjoin
    · simp only [r, ite_eq_right htT]
  have hleftcont : ContinuousOn r (Icc 0 T) := hp.congr hleft
  have hrightcont : ContinuousOn r (Icc T (T + S)) := by
    apply (hq.comp (continuous_id.sub continuous_const).continuousOn ?_).congr hright
    intro t ht
    change 0 ≤ t - T ∧ t - T ≤ S
    constructor <;> linarith [ht.1, ht.2]
  have hunion : Icc (0 : ℝ) T ∪ Icc T (T + S) = Icc 0 (T + S) :=
    Icc_union_Icc_eq_Icc hT (by linarith)
  rw [← hunion]
  exact hleftcont.union_of_isClosed hrightcont isClosed_Icc isClosed_Icc

/-- The usual time concatenation of two length-parametrized curves is
length-parametrized when their endpoints agree. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_piecewise_concat
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p q : ℝ → ℂ} {T S : ℝ}
    (hp : IsLengthParametrized D p T) (hq : IsLengthParametrized D q S)
    (hjoin : p T = q 0) :
    IsLengthParametrized D (fun t => if t ≤ T then p t else q (t - T)) (T + S) := by
  apply hD.isLengthParametrized_concat hp hq
    (continuousOn_length_concat hp.2.1 hq.2.1 hp.1 hq.1 hjoin)
  · intro t ht
    simp only [ite_eq_left ht.2]
  · intro t ht
    by_cases htT : t ≤ T
    · have heq : t = T := le_antisymm htT ht.1
      subst t
      simpa using hjoin
    · simp only [ite_eq_right htT]

/-- Lebesgue integration on an interval is invariant under translation. -/
theorem lintegral_Icc_translate (F : ℝ → ℝ≥0∞) (T S : ℝ) :
    (∫⁻ t in Icc T (T + S), F (t - T)) = ∫⁻ t in Icc (0 : ℝ) S, F t := by
  have hpre : (fun t : ℝ => t - T) ⁻¹' Icc (0 : ℝ) S = Icc T (T + S) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  have hemb : MeasurableEmbedding (fun t : ℝ => t - T) :=
    (Homeomorph.subRight T).measurableEmbedding
  have hpres : MeasurePreserving (fun t : ℝ => t - T) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-T)
  have hm := hpres.restrict_preimage_emb hemb (Icc (0 : ℝ) S)
  rw [hpre] at hm
  exact hm.lintegral_comp_emb hemb F

/-- The weighted cost of a concatenation is bounded by the sum of the two
costs. No measurability assumption on the weight is required. -/
theorem lintegral_length_concat_le (F : ℂ → ℝ≥0∞) (p q : ℝ → ℂ) {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hjoin : p T = q 0) :
    (∫⁻ t in Icc 0 (T + S), F (if t ≤ T then p t else q (t - T))) ≤
      (∫⁻ t in Icc 0 T, F (p t)) + ∫⁻ t in Icc 0 S, F (q t) := by
  let r : ℝ → ℂ := fun t => if t ≤ T then p t else q (t - T)
  have hleft : ∀ t ∈ Icc (0 : ℝ) T, F (r t) = F (p t) := by
    intro t ht
    simp only [r, ite_eq_left ht.2]
  have hright : ∀ t ∈ Icc T (T + S), F (r t) = F (q (t - T)) := by
    intro t ht
    by_cases htT : t ≤ T
    · have heq : t = T := le_antisymm htT ht.1
      subst t
      simp only [r, le_refl, ite_true, sub_self, hjoin]
    · simp only [r, ite_eq_right htT]
  have hunion : Icc (0 : ℝ) T ∪ Icc T (T + S) = Icc 0 (T + S) :=
    Icc_union_Icc_eq_Icc hT (by linarith)
  change (∫⁻ t in Icc 0 (T + S), F (r t)) ≤ _
  rw [← hunion]
  calc
    (∫⁻ t in Icc (0 : ℝ) T ∪ Icc T (T + S), F (r t)) ≤
        (∫⁻ t in Icc 0 T, F (r t)) + ∫⁻ t in Icc T (T + S), F (r t) :=
      lintegral_union_le _ _ _
    _ = (∫⁻ t in Icc 0 T, F (p t)) + ∫⁻ t in Icc T (T + S), F (q (t - T)) := by
      rw [setLIntegral_congr_fun measurableSet_Icc hleft,
        setLIntegral_congr_fun measurableSet_Icc hright]
    _ = _ := by
      congr 1
      exact lintegral_Icc_translate (fun t => F (q t)) T S

/-- Weyl scaling of a length metric satisfies the triangle inequality for
arbitrary weights, including weights for which path costs can be infinite. -/
theorem IsEuclideanLengthMetric.weylScaling_triangle
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ) (x y z : ℂ) :
    weylScaling D ξ f x z ≤ weylScaling D ξ f x y + weylScaling D ξ f y z := by
  simp only [weylScaling, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun S => le_iInf fun q => le_iInf fun hq => le_iInf fun hq0 =>
    le_iInf fun hqS => le_iInf fun T => le_iInf fun p => le_iInf fun hp =>
    le_iInf fun hp0 => le_iInf fun hpT => ?_
  have hjoin : p T = q 0 := hpT.trans hq0.symm
  let r : ℝ → ℂ := fun t => if t ≤ T then p t else q (t - T)
  have hr := hD.isLengthParametrized_piecewise_concat hp hq hjoin
  have hr0 : r 0 = x := by
    simpa only [r, ite_eq_left hp.1] using hp0
  have hrend : r (T + S) = z := by
    by_cases hS : S = 0
    · subst S
      simpa [r] using hpT.trans (hq0.symm.trans hqS)
    · have hSpos : 0 < S := lt_of_le_of_ne hq.1 (Ne.symm hS)
      have hTS : ¬T + S ≤ T := by linarith
      simp only [r, ite_eq_right hTS, add_sub_cancel_left, hqS]
  calc
    _ ≤ ∫⁻ t in Icc 0 (T + S), ENNReal.ofReal (Real.exp (ξ * f (r t))) :=
      (iInf₂_le (T + S) r).trans ((iInf₂_le hr hr0).trans (iInf_le _ hrend))
    _ ≤ _ := lintegral_length_concat_le (fun u => ENNReal.ofReal (Real.exp (ξ * f u)))
      p q hp.1 hq.1 hjoin

end WeylPathConcatenation

section WeylPathSegments

/-- The Weyl distance between two points on a length-parametrized curve is at
most the weighted cost of the intervening segment. -/
theorem IsEuclideanLengthMetric.weylScaling_le_segment_cost
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ) {p : ℝ → ℂ} {T a b : ℝ}
    (hp : IsLengthParametrized D p T) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    weylScaling D ξ f (p a) (p b) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  have hsub := hD.isLengthParametrized_subcurve hp ha hab hb
  have hstart : (fun t => p (a + t)) 0 = p a := by simp
  have hend : (fun t => p (a + t)) (b - a) = p b := by
    ring
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) (b - a),
        ENNReal.ofReal (Real.exp (ξ * f (p (a + t)))) :=
      (iInf₂_le (b - a) (fun t => p (a + t))).trans
        ((iInf₂_le hsub hstart).trans (iInf_le _ hend))
    _ = _ := by
      have h := lintegral_Icc_translate
        (fun t => ENNReal.ofReal (Real.exp (ξ * f (p (a + t))))) a (b - a)
      have h₁ : a + (b - a) = b := by ring
      have h₂ (t : ℝ) : a + (t - a) = t := by ring
      simpa only [h₁, h₂] using h.symm

/-- Weighted costs over successive subintervals add, even for a
nonmeasurable integrand. -/
theorem sum_lintegral_Icc_adjacent (F : ℝ → ℝ≥0∞) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫⁻ t in Icc (u i) (u (i + 1)), F t) =
      ∫⁻ t in Icc (u 0) (u n), F t := by
  have hinterval (a b : ℝ) :
      (∫⁻ t in Icc a b, F t) = ∫⁻ t in Ioc a b, F t := by
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  simp_rw [hinterval]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hsplit := lintegral_union (μ := volume) (f := F) measurableSet_Ioc
      (Ioc_disjoint_Ioc_of_le (le_refl (u n)) :
        Disjoint (Ioc (u 0) (u n)) (Ioc (u n) (u (n + 1))))
    rw [Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))] at hsplit
    exact hsplit.symm

/-- A length-parametrized curve has shifted length bounded by its Weyl cost. -/
theorem IsEuclideanLengthMetric.curveLength_weyl_le_cost
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    curveLength E p 0 T ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  unfold curveLength
  refine iSup_le fun q => ?_
  let F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))
  have hedge (i : ℕ) :
      ENNReal.ofReal (E (p (q.2.1 (i + 1))) (p (q.2.1 i))) ≤
        ∫⁻ t in Icc (q.2.1 i) (q.2.1 (i + 1)), F t := by
    rw [hEsymm, hE]
    exact hD.weylScaling_le_segment_cost ξ f hp (q.2.2.2 i).1
      (q.2.2.1 (Nat.le_succ i)) (q.2.2.2 (i + 1)).2
  calc
    _ ≤ ∑ i ∈ Finset.range q.1, ∫⁻ t in Icc (q.2.1 i) (q.2.1 (i + 1)), F t :=
      Finset.sum_le_sum fun i _ => hedge i
    _ = ∫⁻ t in Icc (q.2.1 0) (q.2.1 q.1), F t :=
      sum_lintegral_Icc_adjacent F q.2.1 q.2.2.1 q.1
    _ ≤ ∫⁻ t in Icc 0 T, F t :=
      lintegral_mono' (Measure.restrict_mono_set volume (Icc_subset_Icc
        (q.2.2.2 0).1 (q.2.2.2 q.1).2)) le_rfl

/-- A continuous curve on a finite interval gives a unit-interval path whose
length is bounded by the length of the original curve. -/
theorem exists_path_pathLength_le_curveLength
    {E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T)) :
    ∃ P : Path (p 0) (p T), pathLength E P ≤ curveLength E p 0 T := by
  have hcont : Continuous (fun t : Set.Icc (0 : ℝ) 1 => p (T * (t : ℝ))) := by
    apply hp.comp_continuous (continuous_const.mul continuous_subtype_val)
    intro t
    change 0 ≤ T * (t : ℝ) ∧ T * (t : ℝ) ≤ T
    constructor
    · exact mul_nonneg hT t.2.1
    · nlinarith [t.2.2]
  let P : Path (p 0) (p T) := {
    toFun := fun t => p (T * (t : ℝ))
    continuous_toFun := hcont
    source' := by simp
    target' := by simp }
  refine ⟨P, ?_⟩
  unfold pathLength curveLength
  refine iSup_le fun q => ?_
  let u : ℕ → ℝ := fun i => T * q.2.1 i
  have hu : Monotone u := fun i j hij => mul_le_mul_of_nonneg_left (q.2.2.1 hij) hT
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) T := by
    intro i
    constructor
    · exact mul_nonneg hT (q.2.2.2 i).1
    · have h := (q.2.2.2 i).2
      dsimp [u]
      nlinarith
  have hle := le_iSup (fun r : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc 0 T} =>
    ∑ i ∈ Finset.range r.1, ENNReal.ofReal (E (p (r.2.1 (i + 1))) (p (r.2.1 i))))
      ⟨q.1, ⟨u, hu, humem⟩⟩
  apply le_trans ?_ hle
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  simp only [u, P, Path.extend_apply _ (q.2.2.2 (i + 1)),
    Path.extend_apply _ (q.2.2.2 i)]
  rfl

/-- The internal distance of a shifted metric is at most its Weyl distance. -/
theorem IsEuclideanLengthMetric.internalMetric_le_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x) (x y : ℂ) :
    internalMetric E univ x y ≤ weylScaling D ξ f x y := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 =>
    le_iInf fun hpT => ?_
  obtain ⟨P, hP⟩ := exists_path_pathLength_le_curveLength (E := E) hp.1 hp.2.1
  have hbound := hD.curveLength_weyl_le_cost ξ f hE hEsymm hp
  subst x
  subst y
  exact (iInf_le_of_le P (iInf_le _ (fun _ => mem_univ _))).trans (hP.trans hbound)

/-- The length of a path dominates the symmetric distance of its endpoints. -/
theorem ofReal_le_pathLength_of_symm {E : ℂ → ℂ → ℝ}
    (hEsymm : ∀ x y, E x y = E y x) {x y : ℂ} (P : Path x y) :
    ENNReal.ofReal (E x y) ≤ pathLength E P := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else 1
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n <;> simp [u]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) 1 := by
    intro n
    rcases n with _ | n <;> simp [u]
  have h := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (E (P.extend (q.2.1 (i + 1)))
      (P.extend (q.2.1 i)))) ⟨1, ⟨u, hu, humem⟩⟩
  change _ ≤ pathLength E P at h
  simpa [u, hEsymm] using h

/-- If a symmetric real distance represents a Weyl scaling, its internal
distance on the plane equals that distance. -/
theorem IsEuclideanLengthMetric.weylScaling_internalMetric
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x) (x y : ℂ) :
    ENNReal.ofReal (E x y) = internalMetric E univ x y := by
  apply le_antisymm
  · refine le_iInf fun P => le_iInf fun _ => ?_
    exact ofReal_le_pathLength_of_symm hEsymm P
  · rw [hE]
    exact hD.internalMetric_le_weylScaling ξ f hE hEsymm x y

end WeylPathSegments

section WeylScaledEuclideanDerived

/-- Upper comparison `weylScaling ≤ e^K · D` when `ξ f ≤ K` everywhere. Each path `P` from `x` to `y` is
reparametrized by its `D`-arclength; the reparametrized curve is a competitor in `weylScaling` of cost at most
`e^K` times its `D`-length. Taking the infimum over paths gives the bound with `D x y = internalMetric D univ x y`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_exp_mul {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ K : ℝ} {f : ℂ → ℝ} (hw : ∀ z, ξ * f z ≤ K) (x y : ℂ) :
    weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (D x y) := by
  have hc0 : ENNReal.ofReal (Real.exp K) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos K)).ne'
  have hP : ∀ P : Path x y, weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * pathLength D P := by
    intro P
    rcases eq_or_ne (curveLength D P.extend 0 1) ⊤ with htop | hfin
    · unfold pathLength
      rw [htop, ENNReal.mul_top hc0]
      exact le_top
    · have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
      obtain ⟨q, hq, h0, hL, -⟩ :=
        hD.exists_lengthParametrized_with_tracking zero_le_one P.continuous_extend.continuousOn hlt
      have hle := weylScaling_le_of_lengthParametrized D ξ f hq (h0.trans P.extend_zero)
        (hL.trans P.extend_one) (fun t _ => hw (q t))
      rw [ENNReal.ofReal_toReal hfin] at hle
      exact hle
  have hinter : internalMetric D univ x y = ⨅ P : Path x y, pathLength D P := by
    unfold internalMetric
    simp only [mem_univ, forall_const, iInf_true]
  rw [hD.ofReal_eq_internalMetric x y, hinter, ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  exact le_iInf fun P => hP P

/-- Lower comparison `e^{-K} · D ≤ weylScaling` when `-K ≤ ξ f` everywhere. Each competitor `(T, p)` of `weylScaling`
has `T ≥ D x y` (the one-interval partition `{0, T}` in `curveLength D p 0 T = T`), and its weighted cost is at least
`e^{-K} T`. -/
theorem IsEuclideanLengthMetric.exp_mul_le_weylScaling {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ K : ℝ} {f : ℂ → ℝ} (hw : ∀ z, -K ≤ ξ * f z) (x y : ℂ) :
    ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D x y) ≤ weylScaling D ξ f x y := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 => le_iInf fun hpT => ?_
  obtain ⟨hT0, -, hlen⟩ := hp
  have hcl : curveLength D p 0 T = ENNReal.ofReal T := by
    rw [hlen 0 T le_rfl hT0 le_rfl, sub_zero]
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else T
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n <;> simp [u, hT0]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) T := by
    intro n
    rcases n with _ | n <;> simp [u, hT0]
  have hle : ENNReal.ofReal (D (p T) (p 0)) ≤ curveLength D p 0 T := by
    unfold curveLength
    refine le_iSup_of_le (⟨1, ⟨u, hu, humem⟩⟩ : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) T}) ?_
    simp [u]
  rw [hp0, hpT, hcl, hD.symm y x] at hle
  have hDT : D x y ≤ T := (ENNReal.ofReal_le_ofReal_iff hT0).mp hle
  calc ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D x y)
      ≤ ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal T := by
        gcongr
    _ = ∫⁻ _ in Icc 0 T, ENNReal.ofReal (Real.exp (-K)) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        setLIntegral_mono' measurableSet_Icc fun t _ =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hw (p t)))

end WeylScaledEuclideanDerived

section InternalMetricClosedDerived
open Filter Topology

theorem internalMetric_anti_set {D : ℂ → ℂ → ℝ} {U V : Set ℂ} (h : U ⊆ V) (z w : ℂ) :
    internalMetric D V z w ≤ internalMetric D U z w := by
  unfold internalMetric
  exact le_iInf₂ fun P hP => iInf₂_le P (fun t => h (hP t))

/-- Route 1.3, (1.11): a thickening of `A` contains `A`, so its internal metric is at most that of `A`. -/
theorem iSup_thickening_le_internalMetric {D : ℂ → ℂ → ℝ} (A : Set ℂ) (x y : ℂ) :
    (⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y) ≤ internalMetric D A x y :=
  iSup_le fun k => internalMetric_anti_set (Metric.self_subset_thickening (by positivity) A) x y

theorem euclid_D_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z w : ℂ) : 0 ≤ D z w := by
  have h := hD.triangle z w z
  rw [hD.self_eq_zero, hD.symm w z] at h
  linarith

/-- The `D`-ball `{z | D z w < ε}` is Euclidean-open (`D` induces the Euclidean topology). -/
theorem isOpen_D_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (w : ℂ) (ε : ℝ) :
    IsOpen {z : ℂ | D z w < ε} := by
  rw [hD.isOpen_iff]
  intro z hz
  refine ⟨ε - D z w, sub_pos.mpr hz, fun z' hz' => ?_⟩
  have h1 := hD.triangle z' z w
  rw [hD.symm z' z] at h1
  have h2 : D z z' < ε - D z w := hz'
  show D z' w < ε
  linarith

/-- `D`-small implies Euclidean-small, at a fixed point. -/
theorem exists_D_small_dist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ η > 0, ∀ w : ℂ, D z w < η → dist w z < r := by
  obtain ⟨η, hη, h⟩ :=
    (hD.isOpen_iff (Metric.ball z r)).mp Metric.isOpen_ball z (Metric.mem_ball_self hr)
  exact ⟨η, hη, fun w hw => Metric.mem_ball.mp (h w hw)⟩

theorem eq_of_forall_D_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {z w : ℂ}
    (h : ∀ ε > 0, D z w < ε) : z = w := by
  have h0 : D z w = 0 :=
    le_antisymm (le_of_forall_pos_lt_add fun ε hε => by simpa using h ε hε) (euclid_D_nonneg hD z w)
  exact hD.eq_of_eq_zero z w h0

theorem inv_succ_lt_half {e : ℝ} (he : 0 < e) {K k : ℕ} (hK : 2 / e < K) (hkK : K ≤ k) :
    ((k : ℝ) + 1)⁻¹ < e / 2 := by
  rw [div_lt_iff₀ he] at hK
  have hk : (K : ℝ) ≤ k := by exact_mod_cast hkK
  rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem dist_le_of_lengthParam_aux {D : ℂ → ℂ → ℝ} {q : ℝ → ℂ} {ℓ : ℝ}
    (hq : IsLengthParametrized D q ℓ) {s t : ℝ} (hs : s ∈ Icc 0 ℓ) (ht : t ∈ Icc 0 ℓ) (hst : s ≤ t) :
    D (q t) (q s) ≤ t - s := by
  have hc : curveLength D q s t = ENNReal.ofReal (t - s) := hq.2.2 s t hs.1 hst ht.2
  have hmono : Monotone (fun i : ℕ => if i = 0 then s else t) := by
    intro i j hij
    dsimp only
    split_ifs <;> first | exact le_refl _ | exact hst | (exfalso; omega)
  have hmem : ∀ i : ℕ, (fun i : ℕ => if i = 0 then s else t) i ∈ Icc s t := by
    intro i
    dsimp only
    split_ifs
    · exact ⟨le_refl _, hst⟩
    · exact ⟨hst, le_refl _⟩
  have hle : ENNReal.ofReal (D (q t) (q s)) ≤ curveLength D q s t := by
    unfold curveLength
    refine le_iSup_of_le ⟨1, ⟨fun i : ℕ => if i = 0 then s else t, hmono, hmem⟩⟩ ?_
    simp
  rw [hc] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hst)).mp hle

/-- Lipschitz bound of an arc-length parametrization: `D (q s) (q t) ≤ |s - t|`. -/
theorem dist_le_of_lengthParam {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {q : ℝ → ℂ} {ℓ : ℝ}
    (hq : IsLengthParametrized D q ℓ) {s t : ℝ} (hs : s ∈ Icc 0 ℓ) (ht : t ∈ Icc 0 ℓ) :
    D (q s) (q t) ≤ |s - t| := by
  rcases le_total s t with hst | hst
  · rw [hD.symm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact dist_le_of_lengthParam_aux hq hs ht hst
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact dist_le_of_lengthParam_aux hq ht hs hst

/-- Route 1.2: a path inside `U` of finite `D`-length has an arc-length parametrization on `[0, ℓ]`,
`ℓ = len(P; D)`, with the same endpoints and image inside `U`. -/
theorem arcLength_param {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {x y : ℂ}
    (P : Path x y) (hU : ∀ t, P t ∈ U) (hfin : pathLength D P ≠ ⊤) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (pathLength D P).toReal ∧ q 0 = x ∧
      q (pathLength D P).toReal = y ∧ ∀ s ∈ Icc 0 (pathLength D P).toReal, q s ∈ U := by
  unfold pathLength at hfin ⊢
  have hcont : ContinuousOn P.extend (Icc 0 1) := P.continuous_extend.continuousOn
  have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
  obtain ⟨q, hq, hq0, hqT, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hcont hlt
  obtain ⟨_, _, _, himg⟩ := hD.cumulative_curveLength_properties zero_le_one hcont hlt
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · rw [hq0]
    simp
  · rw [hqT]
    simp
  · intro s hs
    have hs' : s ∈ (fun t => (curveLength D P.extend 0 t).toReal) '' Icc 0 1 := by
      rw [himg]
      exact hs
    obtain ⟨t, ht, rfl⟩ := hs'
    show q (curveLength D P.extend 0 t).toReal ∈ U
    rw [htrack t ht]
    have hI : t ∈ unitInterval := ⟨ht.1, ht.2⟩
    have h2 : P.extend t = P ⟨t, hI⟩ := P.extend_extends' ⟨t, ht⟩
    rw [h2]
    exact hU ⟨t, hI⟩

/-- Cluster-point extraction in the product topology: a family of maps `ι → ℂ` with values in a compact set
has a cluster point `g`, and every finite set of coordinates is `ε`-approximated by the family at arbitrarily
large indices. This replaces the diagonal extraction of route 1.3. -/
theorem exists_clusterPt_family {ι : Type*} {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {E : Set ℂ}
    (hE : IsCompact E) (F : ℕ → ι → ℂ) (hF : ∀ k t, F k t ∈ E) :
    ∃ g : ι → ℂ, (∀ t, g t ∈ E) ∧
      ∀ (S : Finset ι) {ε : ℝ}, 0 < ε → ∀ K₀ : ℕ, ∃ k, K₀ ≤ k ∧ ∀ t ∈ S, D (F k t) (g t) < ε := by
  have hpi : IsCompact (Set.pi univ fun _ : ι => E) := isCompact_univ_pi fun _ => hE
  have hle : Filter.map F atTop ≤ 𝓟 (Set.pi univ fun _ : ι => E) := by
    rw [le_principal_iff]
    exact mem_map.mpr (univ_mem' fun k => fun t _ => hF k t)
  obtain ⟨g, hgmem, hcl⟩ := hpi.exists_clusterPt hle
  refine ⟨g, fun t => mem_univ_pi.mp hgmem t, ?_⟩
  intro S ε hε K₀
  let V : Set (ι → ℂ) := ⋂ t ∈ S, (fun h : ι → ℂ => h t) ⁻¹' {z : ℂ | D z (g t) < ε}
  have hVopen : IsOpen V :=
    isOpen_biInter_finset fun t _ => (isOpen_D_lt hD (g t) ε).preimage (continuous_apply t)
  have hgV : g ∈ V := by
    simp only [V, mem_iInter, mem_preimage, Set.mem_ofPred_eq]
    intro t _
    rw [hD.self_eq_zero]
    exact hε
  have hfreq := clusterPt_iff_frequently.mp hcl V (hVopen.mem_nhds hgV)
  rw [Filter.frequently_map] at hfreq
  obtain ⟨b, hb, hbV⟩ := Filter.frequently_atTop.mp hfreq K₀
  refine ⟨b, hb, ?_⟩
  intro t ht
  have h3 := hbV
  simp only [V, mem_iInter, mem_preimage, Set.mem_ofPred_eq] at h3
  exact h3 t ht

/-- Route 1.3, (1.10), for a compact set `A`: the internal metric of `A` is the supremum of the internal metrics of
the thickenings `thickening ((k+1)⁻¹) A`. A near-minimizing path in each thickening is arc-length parametrized,
the parametrizations are `D`-Lipschitz with a common constant, a cluster point `g` of the family is a `D`-Lipschitz
path in `A` with the same endpoints, and its length is at most the supremum. -/
theorem internalMetric_le_iSup_thickening {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A : Set ℂ}
    (hA : IsCompact A) (x y : ℂ) :
    internalMetric D A x y ≤ ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y := by
  set a : ℝ≥0∞ := ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y with ha
  by_cases htop : a = ⊤
  · rw [htop]
    exact le_top
  -- Step 1: near-minimizing paths in the thickenings.
  have hchoose : ∀ k : ℕ, ∃ P : Path x y, (∀ t, P t ∈ Metric.thickening (((k : ℝ) + 1)⁻¹) A) ∧
      pathLength D P < a + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) := by
    intro k
    have hpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    have hlt : internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y <
        a + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) :=
      lt_of_le_of_lt
        (le_iSup (fun k : ℕ => internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y) k)
        (ENNReal.lt_add_right htop (ENNReal.ofReal_pos.mpr hpos).ne')
    unfold internalMetric at hlt
    obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hPU, hPlt⟩ := iInf_lt_iff.mp hP
    exact ⟨P, hPU, hPlt⟩
  choose P hPU hPlt using hchoose
  -- Step 2: lengths.
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ → ℝ, ∀ k, ℓ k = (pathLength D (P k)).toReal := ⟨_, fun k => rfl⟩
  have hℓ0 : ∀ k, 0 ≤ ℓ k := fun k => by
    rw [hℓ k]
    exact ENNReal.toReal_nonneg
  have hℓle : ∀ k : ℕ, ℓ k ≤ a.toReal + 1 := by
    intro k
    have h1 : pathLength D (P k) ≤ a + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) := (hPlt k).le
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htop, ENNReal.ofReal_ne_top⟩) h1
    rw [ENNReal.toReal_add htop ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h2
    have h3 : ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [hℓ k]
    linarith
  -- Step 3: arc-length parametrizations inside the thickenings.
  have hq : ∀ k, ∃ q : ℝ → ℂ, IsLengthParametrized D q (ℓ k) ∧ q 0 = x ∧ q (ℓ k) = y ∧
      ∀ s ∈ Icc 0 (ℓ k), q s ∈ Metric.thickening (((k : ℝ) + 1)⁻¹) A := by
    intro k
    obtain ⟨q, h1, h2, h3, h4⟩ := arcLength_param hD (P k) (hPU k) (ne_top_of_lt (hPlt k))
    exact ⟨q, by rw [hℓ k]; exact h1, h2, by rw [hℓ k]; exact h3, by rw [hℓ k]; exact h4⟩
  choose q hqP hq0 hqℓ hqU using hq
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → unitInterval → ℂ, ∀ k t, Φ k t = q k (ℓ k * (t : ℝ)) :=
    ⟨fun k t => q k (ℓ k * (t : ℝ)), fun k t => rfl⟩
  have hΦmem : ∀ (k : ℕ) (t : unitInterval), Φ k t ∈ Metric.thickening (((k : ℝ) + 1)⁻¹) A := by
    intro k t
    rw [hΦdef]
    exact hqU k _ ⟨mul_nonneg (hℓ0 k) (unitInterval.nonneg t), mul_le_of_le_one_right (hℓ0 k) (unitInterval.le_one t)⟩
  have hΦlip : ∀ (k : ℕ) (s t : unitInterval), D (Φ k s) (Φ k t) ≤ (a.toReal + 1) * |(s : ℝ) - t| := by
    intro k s t
    rw [hΦdef, hΦdef]
    have hs : ℓ k * (s : ℝ) ∈ Icc 0 (ℓ k) :=
      ⟨mul_nonneg (hℓ0 k) (unitInterval.nonneg s), mul_le_of_le_one_right (hℓ0 k) (unitInterval.le_one s)⟩
    have ht : ℓ k * (t : ℝ) ∈ Icc 0 (ℓ k) :=
      ⟨mul_nonneg (hℓ0 k) (unitInterval.nonneg t), mul_le_of_le_one_right (hℓ0 k) (unitInterval.le_one t)⟩
    have h1 := dist_le_of_lengthParam hD (hqP k) hs ht
    have h2 : |ℓ k * (s : ℝ) - ℓ k * (t : ℝ)| = ℓ k * |(s : ℝ) - t| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (hℓ0 k)]
    have h3 : ℓ k * |(s : ℝ) - t| ≤ (a.toReal + 1) * |(s : ℝ) - t| :=
      mul_le_mul_of_nonneg_right (hℓle k) (abs_nonneg _)
    rw [h2] at h1
    exact h1.trans h3
  have hΦ0 : ∀ k, Φ k 0 = x := by
    intro k
    rw [hΦdef]
    simp [hq0 k]
  have hΦ1 : ∀ k, Φ k 1 = y := by
    intro k
    rw [hΦdef]
    simp [hqℓ k]
  -- Step 4: cluster point of the family.
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
  have hΦE : ∀ (k : ℕ) (t : unitInterval), Φ k t ∈ Metric.closedBall (0 : ℂ) (R + 1) := by
    intro k t
    obtain ⟨z, hzA, hz⟩ := Metric.mem_thickening_iff.mp (hΦmem k t)
    have hz0 : dist z 0 ≤ R := Metric.mem_closedBall.mp (hR hzA)
    have hδ : ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [Metric.mem_closedBall]
    linarith [dist_triangle (Φ k t) z 0]
  obtain ⟨g, -, hgcl⟩ := exists_clusterPt_family hD (isCompact_closedBall (0 : ℂ) (R + 1)) Φ hΦE
  have hglip : ∀ s t : unitInterval, D (g s) (g t) ≤ (a.toReal + 1) * |(s : ℝ) - t| := by
    intro s t
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨k, -, hk⟩ := hgcl {s, t} (half_pos hε) 0
    have hs := hk s (by simp)
    have ht := hk t (by simp)
    have h := hΦlip k s t
    linarith [hD.triangle (g s) (Φ k s) (g t), hD.triangle (Φ k s) (Φ k t) (g t),
      hD.symm (g s) (Φ k s)]
  have hgA : ∀ t : unitInterval, g t ∈ A := by
    intro t
    by_contra hgt
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hA.isClosed.isOpen_compl (g t) hgt
    obtain ⟨η, hη, hηd⟩ := exists_D_small_dist hD (g t) (half_pos hr)
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 / r)
    obtain ⟨k, hkK, hk⟩ := hgcl {t} hη K₀
    have hδk : ((k : ℝ) + 1)⁻¹ < r / 2 := inv_succ_lt_half hr hK₀ hkK
    have h1 : dist (Φ k t) (g t) < r / 2 := by
      apply hηd
      rw [hD.symm]
      exact hk t (by simp)
    obtain ⟨z, hzA, hz⟩ := Metric.mem_thickening_iff.mp (hΦmem k t)
    have h2 : z ∈ Metric.ball (g t) r := by
      rw [Metric.mem_ball]
      linarith [dist_triangle z (Φ k t) (g t), dist_comm z (Φ k t)]
    exact hball h2 hzA
  have hg0 : g 0 = x := by
    refine eq_of_forall_D_lt hD fun ε hε => ?_
    obtain ⟨k, -, hk⟩ := hgcl {0} hε 0
    have h := hk 0 (by simp)
    rw [hΦ0 k, hD.symm] at h
    exact h
  have hg1 : g 1 = y := by
    refine eq_of_forall_D_lt hD fun ε hε => ?_
    obtain ⟨k, -, hk⟩ := hgcl {1} hε 0
    have h := hk 1 (by simp)
    rw [hΦ1 k, hD.symm] at h
    exact h
  have hgc : Continuous g := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨η, hη, hηd⟩ := exists_D_small_dist hD (g b) hε
    have hLc : 0 < a.toReal + 1 := by positivity
    refine ⟨η / (a.toReal + 1), div_pos hη hLc, fun s hs => ?_⟩
    have h1 := hglip b s
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, lt_div_iff₀ hLc] at hs
    apply hηd (g s)
    linarith
  -- Step 5: the limit path `γ` and its length.
  let γ : Path x y :=
    { toFun := g
      continuous_toFun := hgc
      source' := hg0
      target' := hg1 }
  have hext : ∀ (u : ℕ → ℝ) (i : ℕ) (hi : u i ∈ Icc (0:ℝ) 1), γ.extend (u i) = g ⟨u i, hi⟩ :=
    fun u i hi => γ.extend_extends' ⟨u i, hi⟩
  have hpartΦ : ∀ (k N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) ≤
        ENNReal.ofReal (ℓ k) := by
    intro k N u hu hI
    have hc : curveLength D (q k) 0 (ℓ k) = ENNReal.ofReal (ℓ k - 0) :=
      (hqP k).2.2 0 (ℓ k) le_rfl (hℓ0 k) le_rfl
    have hmono : Monotone (fun i => ℓ k * u i) := fun i j hij =>
      mul_le_mul_of_nonneg_left (hu hij) (hℓ0 k)
    have hmem : ∀ i, (fun i => ℓ k * u i) i ∈ Icc 0 (ℓ k) := fun i =>
      ⟨mul_nonneg (hℓ0 k) (hI i).1, mul_le_of_le_one_right (hℓ0 k) (hI i).2⟩
    calc ∑ i ∈ Finset.range N, ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i)))
        ≤ curveLength D (q k) 0 (ℓ k) := by
          unfold curveLength
          exact le_iSup_of_le ⟨N, ⟨fun i => ℓ k * u i, hmono, hmem⟩⟩ le_rfl
      _ = ENNReal.ofReal (ℓ k) := by rw [hc, sub_zero]
  have hlen : pathLength D γ ≤ a := by
    unfold pathLength
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    refine curveLength_le_of_partition_bound fun N u hu hI => ?_
    have he : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (ε : ℝ) / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
    have hδ : 0 < δ := by
      rw [hδdef]
      positivity
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 / (ε : ℝ))
    obtain ⟨k, hkK, hk⟩ :=
      hgcl ((Finset.range (N + 1)).image fun i => (⟨u i, hI i⟩ : unitInterval)) hδ K₀
    have hkδ : ((k : ℝ) + 1)⁻¹ < (ε : ℝ) / 2 := inv_succ_lt_half he hK₀ hkK
    have hterm : ∀ i ∈ Finset.range N,
        ENNReal.ofReal (D (γ.extend (u (i + 1))) (γ.extend (u i))) ≤
          ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) + ENNReal.ofReal (2 * δ) := by
      intro i hi
      have hi' : i < N := Finset.mem_range.mp hi
      have ha1 : (⟨u (i + 1), hI (i + 1)⟩ : unitInterval) ∈
          (Finset.range (N + 1)).image fun i => (⟨u i, hI i⟩ : unitInterval) :=
        Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
      have hb1 : (⟨u i, hI i⟩ : unitInterval) ∈
          (Finset.range (N + 1)).image fun i => (⟨u i, hI i⟩ : unitInterval) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      have hA1 := hk _ ha1
      have hB1 := hk _ hb1
      have e1 : D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i)) =
          D (Φ k ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u i, hI i⟩) := by
        rw [hΦdef, hΦdef]
      rw [hext u (i + 1) (hI (i + 1)), hext u i (hI i), e1]
      have hab : D (g ⟨u (i + 1), hI (i + 1)⟩) (g ⟨u i, hI i⟩) ≤
          D (Φ k ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u i, hI i⟩) + 2 * δ := by
        linarith [hD.triangle (g ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u (i + 1), hI (i + 1)⟩) (g ⟨u i, hI i⟩),
          hD.triangle (Φ k ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u i, hI i⟩) (g ⟨u i, hI i⟩),
          hD.symm (g ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u (i + 1), hI (i + 1)⟩)]
      exact (ENNReal.ofReal_le_ofReal hab).trans ENNReal.ofReal_add_le
    have hNle : (N : ℝ) * (2 * δ) ≤ (ε : ℝ) / 2 := by
      have h1 : (N : ℝ) * (2 * δ) = ((ε : ℝ) / 2) * ((N : ℝ) / ((N : ℝ) + 1)) := by
        rw [hδdef]
        field_simp
        ring
      rw [h1]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity)]
      linarith
    have hNδ : (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal ((ε : ℝ) / 2) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hNle
    have hℓP : ENNReal.ofReal (ℓ k) ≤ a + ENNReal.ofReal ((ε : ℝ) / 2) := by
      rw [hℓ k, ENNReal.ofReal_toReal (ne_top_of_lt (hPlt k))]
      exact (hPlt k).le.trans (add_le_add_right (ENNReal.ofReal_le_ofReal hkδ.le) a)
    calc ∑ i ∈ Finset.range N, ENNReal.ofReal (D (γ.extend (u (i + 1))) (γ.extend (u i)))
        ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) +
            ENNReal.ofReal (2 * δ)) := Finset.sum_le_sum hterm
      _ = ∑ i ∈ Finset.range N, ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) +
            (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (ℓ k) + ENNReal.ofReal ((ε : ℝ) / 2) :=
          add_le_add (hpartΦ k N u hu hI) hNδ
      _ ≤ a + ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2) :=
          add_le_add_left hℓP _
      _ = a + (ε : ℝ≥0∞) := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal]
          congr 2
          ring
  have hle : internalMetric D A x y ≤ pathLength D γ := by
    unfold internalMetric
    exact iInf₂_le γ fun t => hgA t
  exact hle.trans hlen

/-- Route 1.4, (1.13)-(1.14): for a closed `C`, the internal metric is the infimum over `n` of the suprema over `k`
of the internal metrics of `thickening ((k+1)⁻¹) (C ∩ closedBall 0 (n+1))`. -/
theorem internalMetric_closed_eq_iInf_sup {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (C : Set ℂ)
    (hC : IsClosed C) (x y : ℂ) :
    internalMetric D C x y = ⨅ n : ℕ, ⨆ k : ℕ,
      internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((n : ℝ) + 1))) x y := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact (internalMetric_anti_set Set.inter_subset_left x y).trans
      (internalMetric_le_iSup_thickening hD ((isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)).inter_left hC) x y)
  · refine le_trans (iInf_mono fun n => iSup_thickening_le_internalMetric _ x y) ?_
    unfold internalMetric
    refine le_iInf₂ fun P hP => ?_
    obtain ⟨R, hR⟩ := (isCompact_range P.continuous).isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_nat_ge R
    refine (iInf_le _ N).trans (iInf₂_le P fun t => ⟨hP t, ?_⟩)
    have h1 := Metric.mem_closedBall.mp (hR (Set.mem_range_self t))
    exact Metric.mem_closedBall.mpr (by linarith)
end InternalMetricClosedDerived

/-- **Weyl scaling of a Euclidean length metric.** The Weyl scaling
`e^{ξ f} · D` of a Euclidean length metric `D` by a continuous compactly supported `f` is a Euclidean length metric. No
hypothesis is added. -/
theorem weylScaledEuclidean_derived :
    ∀ (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ), IsEuclideanLengthMetric D → Continuous f → HasCompactSupport f →
      IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal) := by
  intro D ξ f hD hf hc
  -- `|f| ≤ B` by continuity and compact support (Mathlib's bound is on the norm)
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨B, hfB⟩ : ∃ B : ℝ, ∀ z, |f z| ≤ B :=
    ⟨max C 0, fun z => (show |f z| ≤ C by simpa [Real.norm_eq_abs] using hC z).trans (le_max_left C 0)⟩
  -- `|ξ f| ≤ K := |ξ| B`
  set K : ℝ := |ξ| * B with hKdef
  have hξf : ∀ z, |ξ * f z| ≤ K := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfB z) (abs_nonneg ξ)
  have hw1 : ∀ z, ξ * f z ≤ K := fun z => (abs_le.mp (hξf z)).2
  have hw2 : ∀ z, -K ≤ ξ * f z := fun z => (abs_le.mp (hξf z)).1
  have hup : ∀ x y, weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (D x y) :=
    fun x y => hD.weylScaling_le_exp_mul hw1 x y
  have hlo : ∀ x y, ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D x y) ≤ weylScaling D ξ f x y :=
    fun x y => hD.exp_mul_le_weylScaling hw2 x y
  have hfin : ∀ x y, weylScaling D ξ f x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hup x y)
  have hDnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    rw [hD.self_eq_zero x, hD.symm y x] at h1
    linarith
  -- the real Weyl scaling
  set E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal with hEdef
  have hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y :=
    fun x y => ENNReal.ofReal_toReal (hfin x y)
  have hEsymm : ∀ x y, E x y = E y x := fun x y => by
    show (weylScaling D ξ f x y).toReal = (weylScaling D ξ f y x).toReal
    rw [hD.weylScaling_symm ξ f x y]
  have hEge : ∀ x y, Real.exp (-K) * D x y ≤ E x y := fun x y => by
    have h := hlo x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hE x y] at h
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
  have hEle : ∀ x y, E x y ≤ Real.exp K * D x y := fun x y => by
    have h := hup x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hE x y] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos K).le (hDnn x y))).mp h
  have hEmetric : IsEuclideanLengthMetric E := by
    refine ⟨?_, ?_, hEsymm, ?_, ?_, fun z w => hD.weylScaling_internalMetric ξ f hE hEsymm z w⟩
    · -- `D z z = 0` gives `weylScaling z z = 0`
      intro z
      have h := hup z z
      rw [hD.self_eq_zero z, ENNReal.ofReal_zero, mul_zero, nonpos_iff_eq_zero] at h
      show (weylScaling D ξ f z z).toReal = 0
      rw [h, ENNReal.toReal_zero]
    · -- separation: `E z w = 0` forces `weylScaling z w = 0`, hence `D z w = 0`
      intro z w hzw
      have hW : weylScaling D ξ f z w = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hzw with h | h
        · exact h
        · exact absurd h (hfin z w)
      have h := hlo z w
      rw [hW, nonpos_iff_eq_zero] at h
      have hpos : ENNReal.ofReal (Real.exp (-K)) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      have h0 : ENNReal.ofReal (D z w) = 0 :=
        (mul_eq_zero.mp h).resolve_left hpos
      have hDzw : D z w = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp h0) (hDnn z w)
      exact hD.eq_of_eq_zero z w hDzw
    · -- triangle inequality, from `weylScaling_triangle` and finiteness
      intro x y z
      have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin x y, hfin y z⟩)
        (hD.weylScaling_triangle ξ f x y z)
      rw [ENNReal.toReal_add (hfin x y) (hfin y z)] at h
      exact h
    · -- topology: `e^{-K}`-comparison with `D`
      intro U
      constructor
      · intro hU z hz
        obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).mp hU z hz
        refine ⟨Real.exp (-K) * ε, mul_pos (Real.exp_pos _) hε, fun w hw => hball w ?_⟩
        have h1 : Real.exp (-K) * D z w < Real.exp (-K) * ε := lt_of_le_of_lt (hEge z w) hw
        exact lt_of_mul_lt_mul_left h1 (Real.exp_pos _).le
      · intro h
        refine (hD.isOpen_iff U).mpr fun z hz => ?_
        obtain ⟨ε, hε, hball⟩ := h z hz
        refine ⟨ε * Real.exp (-K), mul_pos hε (Real.exp_pos _), fun w hw => hball w ?_⟩
        have hexp : Real.exp K * (ε * Real.exp (-K)) = ε := by
          rw [Real.exp_neg]
          field_simp
        calc E z w ≤ Real.exp K * D z w := hEle z w
          _ < Real.exp K * (ε * Real.exp (-K)) := mul_lt_mul_of_pos_left hw (Real.exp_pos K)
          _ = ε := hexp
  exact hEmetric

/-- **Internal metric of a closed set.** For a Euclidean length metric `D`, a closed set `C` and `x, y ∈ C`, the internal metric of
`C` is the infimum over `n` of the suprema over `k` of the internal metrics of the thickenings of `C ∩ closedBall 0 (n+1)`.
No hypothesis is added. -/
theorem internalMetricClosedEqIInfThickening_derived :
    ∀ (D : ℂ → ℂ → ℝ) (C : Set ℂ), IsClosed C → IsEuclideanLengthMetric D →
      ∀ {x y : ℂ}, x ∈ C → y ∈ C →
        internalMetric D C x y = ⨅ n : ℕ, ⨆ k : ℕ,
          internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((n : ℝ) + 1))) x y := by
  intro D C hC hD x y _ _
  exact internalMetric_closed_eq_iInf_sup hD C hC x y

end LatticeProb.LQG
