/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylBasic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic

/-!
# Weyl scaling `e^{ξ f}·D`: basic deterministic identities

`weylScale ξ f D` is GM's `(e^{ξ f}·D)` (GM, arXiv:1905.00383v3, eq. (1.6) = `eqn-metric-f`,
`literature/src/1905.00383/uniqueness-final.tex` l. 300–302): the infimum, over continuous paths
`P` from `z` to `w` parametrized by `D`-length on `[0, L]`, of `∫_0^L e^{ξ f(P t)} dt`.

We add the version `weylScaleOn ξ f D U` in which the paths are required to stay in `U` (the
paths used for GM's internal metrics `(e^{ξ f}·D)(·,·;U)`, l. 270–272 and GM §5, blueprint
GM.S5.W). Results (blueprint GM.S1.6, GM.S5.W, FOUNDATIONS §5):

* `weylScaleOn_mono`: monotone in `ξ f` (pointwise on `U`); `weylScaleOn_congr`: depends only on
  `f|_U` (locality in `f`); `weylScaleOn_anti`: antitone in `U`;
* `weylScaleOn_of_eq_const`: if `ξ f ≡ a` on `U`, then `e^{ξ f}·D` with paths in `U` equals
  `e^a · D(·,·;U)` (GM.S5.W "if f ≡ c on an open set U then (e^{ξf}·D)(·,·;U) = e^{ξc}D(·,·;U)";
  GM.S1.6 "e^{ξc}·D = e^{ξc}D", which uses Axiom I: `weylScale_const_of_isLength`);
* the bounds `e^a D(·,·;U) ≤ … ≤ e^b D(·,·;U)` when `a ≤ ξ f ≤ b` on `U`
  (DFGPS.S5 `e^{−ξ‖f‖∞}D ≤ e^{ξf}·D ≤ e^{ξ‖f‖∞}D`).

The proofs are direct from the definition (GM uses these facts without proof); the only
geometric input is reparametrization by length (mathlib's `naturalParameterization`, BBI
Prop. 2.5.9, via `LQGMetric.MetricGeometry.lengthParam`). Own elementary proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric

namespace MetricGeometry

variable {X : Type*} [EMetricSpace X]

/-- A path of finite length `ℓ` has a unit-speed parametrization on `[0, ℓ]` with the same
endpoints whose values lie in the range of the path (mathlib's natural parameterization). -/
theorem exists_unitSpeed_of_path {x y : X} (γ : Path x y) (hL : pathLength γ ≠ ∞) :
    ∃ P : ℝ → X, HasUnitSpeedOn P (Icc 0 (pathLength γ).toReal) ∧
      ContinuousOn P (Icc 0 (pathLength γ).toReal) ∧ P 0 = x ∧
      P (pathLength γ).toReal = y ∧ ∀ u ∈ Icc 0 (pathLength γ).toReal, P u ∈ range γ := by
  have hPc : ContinuousOn (⇑γ.extend) (Icc 0 1) := γ.continuous_extend.continuousOn
  have hL' : curveLength (⇑γ.extend) 0 1 ≠ ∞ := hL
  have himg := variationOnFromTo_image_Icc zero_le_one hPc hL'
  refine ⟨lengthParam (⇑γ.extend) 0 1, hasUnitSpeedOn_lengthParam zero_le_one hPc hL',
    (lipschitzOnWith_lengthParam zero_le_one hPc hL').continuousOn, ?_, ?_, ?_⟩
  · have := lengthParam_variationOnFromTo hL' (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.self] at this
    exact this.trans (Path.extend_zero γ)
  · have := lengthParam_variationOnFromTo hL' (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.eq_of_le _ _ zero_le_one, Set.inter_self] at this
    exact this.trans (Path.extend_one γ)
  · intro u hu
    have hu' : u ∈ Icc 0 (curveLength (⇑γ.extend) 0 1).toReal := hu
    rw [← himg] at hu'
    obtain ⟨t, ht, rfl⟩ := hu'
    rw [lengthParam_variationOnFromTo hL' ht, Path.extend_apply γ ht]
    exact mem_range_self _

end MetricGeometry

open MetricGeometry

/-- Weyl scaling with paths constrained to `U`: the infimum of `∫_0^L e^{ξ f(P t)} dt` over
continuous paths `P ⊂ U` from `z` to `w` parametrized by `D`-length on `[0, L]` (GM (1.6) with
the constraint of GM (1.5)). `weylScaleOn ξ f D univ = weylScale ξ f D` (`weylScaleOn_univ`). -/
def weylScaleOn (ξ : ℝ) (f : C(ℂ, ℝ)) (D : ContMetric) (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (L : ℝ) (P : ℝ → ℂ) (_ : 0 ≤ L) (_ : ContinuousOn (D.pt ∘ P) (Icc 0 L))
    (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = z) (_ : P L = w)
    (_ : ∀ t ∈ Icc 0 L, P t ∈ U),
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))

variable {ξ η : ℝ} {f g : C(ℂ, ℝ)} {D : ContMetric} {U V : Set ℂ} {z w : ℂ}

theorem weylScaleOn_univ (ξ : ℝ) (f : C(ℂ, ℝ)) (D : ContMetric) (z w : ℂ) :
    weylScaleOn ξ f D univ z w = weylScale ξ f D z w := by
  simp only [weylScaleOn, weylScale, mem_univ, implies_true, iInf_pos]

theorem weylScaleOn_le {L : ℝ} {P : ℝ → ℂ} (hL : 0 ≤ L) (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L))
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (h0 : P 0 = z) (h1 : P L = w)
    (hU : ∀ t ∈ Icc 0 L, P t ∈ U) :
    weylScaleOn ξ f D U z w ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
  iInf_le_of_le L <| iInf_le_of_le P <| iInf_le_of_le hL <| iInf_le_of_le hc <|
    iInf_le_of_le hu <| iInf_le_of_le h0 <| iInf_le_of_le h1 <| iInf_le_of_le hU le_rfl

theorem le_weylScaleOn {c : ℝ≥0∞}
    (h : ∀ (L : ℝ) (P : ℝ → ℂ), 0 ≤ L → ContinuousOn (D.pt ∘ P) (Icc 0 L) →
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) → P 0 = z → P L = w → (∀ t ∈ Icc 0 L, P t ∈ U) →
      c ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) :
    c ≤ weylScaleOn ξ f D U z w := by
  simp only [weylScaleOn, le_iInf_iff]
  exact h

/-- Monotonicity in `ξ f` (GM.S5.W "monotone in f"): if `ξ f ≤ η g` on `U`, then
`(e^{ξ f}·D)_U ≤ (e^{η g}·D)_U`. -/
theorem weylScaleOn_mono (hfg : ∀ x ∈ U, ξ * f x ≤ η * g x) :
    weylScaleOn ξ f D U z w ≤ weylScaleOn η g D U z w :=
  le_weylScaleOn fun _ _ hL hc hu h0 h1 hU =>
    (weylScaleOn_le hL hc hu h0 h1 hU).trans <| setLIntegral_mono' measurableSet_Icc
      fun t ht => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hfg _ (hU t ht)))

/-- Locality in `f`: `(e^{ξ f}·D)_U` depends only on `ξ f` restricted to `U`. -/
theorem weylScaleOn_congr (hfg : ∀ x ∈ U, ξ * f x = η * g x) :
    weylScaleOn ξ f D U z w = weylScaleOn η g D U z w :=
  le_antisymm (weylScaleOn_mono fun x hx => (hfg x hx).le)
    (weylScaleOn_mono fun x hx => (hfg x hx).ge)

/-- Fewer admissible paths for a smaller set. -/
theorem weylScaleOn_anti (hUV : U ⊆ V) : weylScaleOn ξ f D V z w ≤ weylScaleOn ξ f D U z w :=
  le_weylScaleOn fun _ _ hL hc hu h0 h1 hU =>
    weylScaleOn_le hL hc hu h0 h1 fun t ht => hUV (hU t ht)

theorem weylScale_le_weylScaleOn : weylScale ξ f D z w ≤ weylScaleOn ξ f D U z w := by
  rw [← weylScaleOn_univ]; exact weylScaleOn_anti (subset_univ U)

/-- Global monotonicity: `ξ f ≤ η g` everywhere ⇒ `e^{ξ f}·D ≤ e^{η g}·D`. -/
theorem weylScale_mono (hfg : ∀ x, ξ * f x ≤ η * g x) :
    weylScale ξ f D z w ≤ weylScale η g D z w := by
  rw [← weylScaleOn_univ, ← weylScaleOn_univ]; exact weylScaleOn_mono fun x _ => hfg x

/-- `f ≤ g` and `ξ ≥ 0` ⇒ `e^{ξ f}·D ≤ e^{ξ g}·D`. -/
theorem weylScale_mono_of_le (hξ : 0 ≤ ξ) (hfg : ∀ x, f x ≤ g x) :
    weylScale ξ f D z w ≤ weylScale ξ g D z w :=
  weylScale_mono fun x => mul_le_mul_of_nonneg_left (hfg x) hξ

/-- The integral of a constant `e^a` along a length-parametrized path of length `L`. -/
theorem setLIntegral_exp_of_eq_const {L a : ℝ} {F : ℝ → ℝ}
    (hF : ∀ t ∈ Icc 0 L, F t = a) :
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (F t)) =
      ENNReal.ofReal (Real.exp a) * ENNReal.ofReal L := by
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => ENNReal.ofReal (Real.exp a))
    (fun t ht => by simp only [hF t ht]), setLIntegral_const, Real.volume_Icc, sub_zero]

/-- The `D`-internal distance in `U` is at most the length `L` of a unit-speed path in `U`. -/
theorem ContMetric.internal_le_of_unitSpeed {L : ℝ} {P : ℝ → ℂ} (hL : 0 ≤ L)
    (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hU : ∀ t ∈ Icc 0 L, P t ∈ U) : D.internal U (P 0) (P L) ≤ ENNReal.ofReal L := by
  obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hL hc
  have hlen : curveLength (D.pt ∘ P) 0 L = ENNReal.ofReal L := by
    rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩, sub_zero]
  refine (internalEDist_le_pathLength γ fun t => ?_).trans (hγ.trans hlen).le
  obtain ⟨s, hs, hst⟩ := hrange (mem_range_self t)
  exact ⟨P s, hU s hs, hst⟩

/-- A path inside `D.pt '' U` of finite length `ℓ` yields an admissible unit-speed path. -/
theorem ContMetric.exists_unitSpeed_of_path (γ : Path (D.pt z) (D.pt w))
    (hγ : ∀ t, γ t ∈ D.pt '' U) (hL : pathLength γ ≠ ∞) :
    ∃ P : ℝ → ℂ, ContinuousOn (D.pt ∘ P) (Icc 0 (pathLength γ).toReal) ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 (pathLength γ).toReal) ∧ P 0 = z ∧
      P (pathLength γ).toReal = w ∧ ∀ t ∈ Icc 0 (pathLength γ).toReal, P t ∈ U := by
  obtain ⟨P, hu, hc, h0, h1, hr⟩ := MetricGeometry.exists_unitSpeed_of_path γ hL
  refine ⟨P, hc, hu, h0, h1, fun t ht => ?_⟩
  obtain ⟨s, hs⟩ := hr t ht
  obtain ⟨x, hx, hxs⟩ := hγ s
  have : x = P t := hxs.trans hs
  exact this ▸ hx

/-- **Constant Weyl factor** (GM.S5.W, GM.S1.6): if `ξ f ≡ a` on `U`, then
`(e^{ξ f}·D)_U(z, w) = e^a · D(z, w; U)`. -/
theorem weylScaleOn_of_eq_const {a : ℝ} (hf : ∀ x ∈ U, ξ * f x = a) :
    weylScaleOn ξ f D U z w = ENNReal.ofReal (Real.exp a) * D.internal U z w := by
  have hea0 : ENNReal.ofReal (Real.exp a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos a
  apply le_antisymm
  · unfold ContMetric.internal internalEDist
    rw [ENNReal.mul_iInf_of_ne hea0 ENNReal.ofReal_ne_top]
    refine le_iInf fun γ => ?_
    by_cases hL : pathLength γ.1 = ∞
    · rw [hL, ENNReal.mul_top hea0]; exact le_top
    obtain ⟨P, hc, hu, h0, h1, hU⟩ := ContMetric.exists_unitSpeed_of_path γ.1 γ.2 hL
    refine (weylScaleOn_le ENNReal.toReal_nonneg hc hu h0 h1 hU).trans_eq ?_
    rw [setLIntegral_exp_of_eq_const fun t ht => hf _ (hU t ht),
      ENNReal.ofReal_toReal hL]
  · refine le_weylScaleOn fun L P hL hc hu h0 h1 hU => ?_
    rw [setLIntegral_exp_of_eq_const fun t ht => hf _ (hU t ht)]
    gcongr
    rw [← h0, ← h1]
    exact ContMetric.internal_le_of_unitSpeed hL hc hu hU

/-- `e^{ξ f}·D` for `ξ f ≡ a` is `e^a` times the induced length metric `D(·,·;ℂ)`. -/
theorem weylScale_of_eq_const {a : ℝ} (hf : ∀ x, ξ * f x = a) :
    weylScale ξ f D z w = ENNReal.ofReal (Real.exp a) * D.internal univ z w := by
  rw [← weylScaleOn_univ]; exact weylScaleOn_of_eq_const fun x _ => hf x

/-- For a length metric, `D(·,·;ℂ) = D`. -/
theorem ContMetric.internal_univ_of_isLength (hD : D.IsLength) (z w : ℂ) :
    D.internal univ z w = ENNReal.ofReal (D.1 (z, w)) := by
  unfold ContMetric.internal
  rw [image_univ_of_surjective (fun x => ⟨x, rfl⟩ : Function.Surjective D.pt),
    internalEDist_univ_of_isLengthSpace hD, edist_dist]
  rfl

/-- **GM.S1.6**: for a length metric `D` and a constant `c`, `e^{ξ c}·D = e^{ξ c} D`. -/
theorem weylScale_const_of_isLength (hD : D.IsLength) (ξ c : ℝ) (z w : ℂ) :
    weylScale ξ (ContinuousMap.const ℂ c) D z w =
      ENNReal.ofReal (Real.exp (ξ * c) * D.1 (z, w)) := by
  rw [weylScale_of_eq_const (a := ξ * c) (fun _ => rfl), D.internal_univ_of_isLength hD,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Lower bound (DFGPS.S5): `a ≤ ξ f` on `U` ⇒ `e^a D(·,·;U) ≤ (e^{ξ f}·D)_U`. -/
theorem le_weylScaleOn_of_le {a : ℝ} (hf : ∀ x ∈ U, a ≤ ξ * f x) :
    ENNReal.ofReal (Real.exp a) * D.internal U z w ≤ weylScaleOn ξ f D U z w := by
  rw [← weylScaleOn_of_eq_const (ξ := 1) (f := ContinuousMap.const ℂ a)
    (fun _ _ => one_mul a)]
  exact weylScaleOn_mono fun x hx => (one_mul a).trans_le (hf x hx)

/-- Upper bound (DFGPS.S5): `ξ f ≤ b` on `U` ⇒ `(e^{ξ f}·D)_U ≤ e^b D(·,·;U)`. -/
theorem weylScaleOn_le_of_le {b : ℝ} (hf : ∀ x ∈ U, ξ * f x ≤ b) :
    weylScaleOn ξ f D U z w ≤ ENNReal.ofReal (Real.exp b) * D.internal U z w := by
  rw [← weylScaleOn_of_eq_const (ξ := 1) (f := ContinuousMap.const ℂ b)
    (fun _ _ => one_mul b)]
  exact weylScaleOn_mono fun x hx => (hf x hx).trans (one_mul b).ge

/-- Global two-sided bound for a length metric: `a ≤ ξ f ≤ b` ⇒
`e^a D ≤ e^{ξ f}·D ≤ e^b D`. -/
theorem weylScale_mem_Icc_of_isLength (hD : D.IsLength) {a b : ℝ}
    (ha : ∀ x, a ≤ ξ * f x) (hb : ∀ x, ξ * f x ≤ b) :
    ENNReal.ofReal (Real.exp a * D.1 (z, w)) ≤ weylScale ξ f D z w ∧
      weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp b * D.1 (z, w)) := by
  have hdist : 0 ≤ D.1 (z, w) := dist_nonneg (x := D.pt z) (y := D.pt w)
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← D.internal_univ_of_isLength hD, ← weylScaleOn_univ]
  exact ⟨le_weylScaleOn_of_le fun x _ => ha x, weylScaleOn_le_of_le fun x _ => hb x⟩

end LQGMetric
