/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/CurveNatural.lean.
-/
import Mathlib.Analysis.ConstantSpeed
import LatticeProb.Topology.Length.LengthSpace

/-!
# Curves parametrized by length

For a continuous curve `P : [a, b] → X` of finite length `L`, mathlib's
`naturalParameterization P (Icc a b) a` (here `lengthParam P a b`) is the curve `P`
parametrized by length: it has unit speed on `[0, L]` (so it is `1`-Lipschitz there), its length on
`[0, L]` is `L`, and `P t = lengthParam P a b (σ t)` up to distance zero, where
`σ t = variationOnFromTo P (Icc a b) a t` is the length of `P` on `[a, t]`; `σ` maps `[a, b]` onto
`[0, L]` (`variationOnFromTo_image_Icc`).

As a consequence (`exists_lipschitz_path`), in an extended metric space every path of finite
length `L` has a reparametrization (same endpoints, same length, image inside the original one)
which is `L`-Lipschitz on `[0, 1]` (constant speed). This is the step "parametrize by arc length"
in Burago–Burago–Ivanov, *A course in metric geometry*, Prop. 2.5.9, and in Petrunin,
*Pure metric geometry* (arXiv:2007.09846), §1 "Length" (curves parametrized by length).
The proofs wrap mathlib's `has_unit_speed_naturalParameterization`,
`edist_naturalParameterization_eq_zero` and the variation estimates
`BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left` and `_right`, which give the continuity of
the length function (`continuousOn_variationOnFromTo`).
-/

open Set Filter Topology unitInterval
open scoped ENNReal NNReal

namespace LatticeProb.MetricGeometry

section Pseudo

variable {X : Type*} [PseudoEMetricSpace X]

/-- `P` parametrized by length on `[a, b]`: mathlib's natural parameterization. -/
noncomputable def lengthParam (P : ℝ → X) (a b : ℝ) : ℝ → X :=
  naturalParameterization P (Icc a b) a

/-- A curve of finite length on `[a, b]` has bounded variation there. -/
theorem boundedVariationOn_of_curveLength_ne_top {P : ℝ → X} {a b : ℝ}
    (hL : curveLength P a b ≠ ∞) : BoundedVariationOn P (Icc a b) := hL

/-- The length function `t ↦ len(P; [a, t])` is continuous on `[a, b]` when `P` is continuous
there and has bounded variation. Mathlib's `BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici`
is stated on `univ` at this pin, so the restriction to `[a, b]` is proved here. -/
theorem continuousOn_variationOnFromTo {P : ℝ → X} {a b : ℝ} (hf : BoundedVariationOn P (Icc a b))
    (ha : a ∈ Icc a b) (hP : ContinuousOn P (Icc a b)) :
    ContinuousOn (variationOnFromTo P (Icc a b) a) (Icc a b) := by
  intro x hx
  -- The increment of the length function from `x` is a difference of two one-sided variations.
  have hV : ∀ y, variationOnFromTo P (Icc a b) x y =
      (eVariationOn P (Icc a b ∩ Icc x y)).toReal - (eVariationOn P (Icc a b ∩ Icc y x)).toReal := by
    intro y
    rcases le_total x y with hxy | hyx
    · have hs : (Icc a b ∩ Icc y x).Subsingleton := by
        rintro u ⟨-, hu1, hu2⟩ v ⟨-, hv1, hv2⟩
        exact le_antisymm (hu2.trans (hxy.trans hv1)) (hv2.trans (hxy.trans hu1))
      rw [variationOnFromTo.eq_of_le _ _ hxy, eVariationOn.subsingleton _ hs]
      simp
    · have hs : (Icc a b ∩ Icc x y).Subsingleton := by
        rintro u ⟨-, hu1, hu2⟩ v ⟨-, hv1, hv2⟩
        exact le_antisymm (hu2.trans (hyx.trans hv1)) (hv2.trans (hyx.trans hu1))
      rw [variationOnFromTo.eq_of_ge _ _ hyx, eVariationOn.subsingleton _ hs]
      simp
  have hA := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (hf.tendsto_eVariationOn_Icc_zero_right x ((hP x hx).mono inter_subset_left))
  have hB := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (hf.tendsto_eVariationOn_Icc_zero_left (x := x) ((hP x hx).mono inter_subset_left))
  rw [ENNReal.toReal_zero] at hA hB
  have hV0 : Tendsto (fun y => variationOnFromTo P (Icc a b) x y) (𝓝[Icc a b] x) (𝓝 0) := by
    have h := hA.sub hB
    rw [sub_zero] at h
    exact Tendsto.congr (fun y => (hV y).symm) h
  have hVx : ContinuousWithinAt (variationOnFromTo P (Icc a b) x) (Icc a b) x := by
    rw [ContinuousWithinAt, variationOnFromTo.self]
    exact hV0
  have hc : ContinuousWithinAt
      (fun y => variationOnFromTo P (Icc a b) a x + variationOnFromTo P (Icc a b) x y)
      (Icc a b) x := continuousWithinAt_const.add hVx
  refine hc.congr (fun y hy => ?_) ?_
  · exact (variationOnFromTo.add hf.locallyBoundedVariationOn ha hx hy).symm
  · rw [variationOnFromTo.self, add_zero]

/-- The length function `σ t = len(P; [a, t])` maps `[a, b]` onto `[0, len(P; [a, b])]`. -/
theorem variationOnFromTo_image_Icc {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hL : curveLength P a b ≠ ∞) :
    variationOnFromTo P (Icc a b) a '' Icc a b = Icc 0 (curveLength P a b).toReal := by
  have hf : BoundedVariationOn P (Icc a b) := hL
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcont : ContinuousOn (variationOnFromTo P (Icc a b) a) (Icc a b) :=
    continuousOn_variationOnFromTo hf ha hP
  rw [hcont.image_Icc_of_monotoneOn hab
    (variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn ha), variationOnFromTo.self,
    variationOnFromTo.eq_of_le _ _ hab, Set.inter_self]
  rfl

/-- `lengthParam P a b` has unit speed on `[0, L]`. -/
theorem hasUnitSpeedOn_lengthParam {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hL : curveLength P a b ≠ ∞) :
    HasUnitSpeedOn (lengthParam P a b) (Icc 0 (curveLength P a b).toReal) := by
  have h := has_unit_speed_naturalParameterization P
    (boundedVariationOn_of_curveLength_ne_top hL).locallyBoundedVariationOn
    (a := a) ⟨le_rfl, hab⟩
  rwa [variationOnFromTo_image_Icc hab hP hL] at h

/-- The length of `lengthParam P a b` on `[0, L]` is `L = len(P; [a, b])`. -/
theorem curveLength_lengthParam {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hL : curveLength P a b ≠ ∞) :
    curveLength (lengthParam P a b) 0 (curveLength P a b).toReal = curveLength P a b := by
  have h := hasUnitSpeedOn_lengthParam hab hP hL
    (⟨le_rfl, ENNReal.toReal_nonneg⟩ : (0 : ℝ) ∈ Icc 0 (curveLength P a b).toReal)
    (⟨ENNReal.toReal_nonneg, le_rfl⟩ : (curveLength P a b).toReal ∈ Icc 0 _)
  rw [Set.inter_self] at h
  unfold curveLength at h ⊢
  rw [h, NNReal.coe_one, one_mul, sub_zero]
  exact ENNReal.ofReal_toReal hL

/-- `lengthParam P a b` is `1`-Lipschitz on `[0, L]`. -/
theorem lipschitzOnWith_lengthParam {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hL : curveLength P a b ≠ ∞) :
    LipschitzOnWith 1 (lengthParam P a b) (Icc 0 (curveLength P a b).toReal) := by
  have hu := hasUnitSpeedOn_lengthParam hab hP hL
  have key : ∀ x ∈ Icc 0 (curveLength P a b).toReal, ∀ y ∈ Icc 0 (curveLength P a b).toReal,
      x ≤ y → edist (lengthParam P a b x) (lengthParam P a b y) ≤ 1 * edist x y := by
    intro x hx y hy hxy
    have h := hu hx hy
    calc edist (lengthParam P a b x) (lengthParam P a b y)
        ≤ eVariationOn (lengthParam P a b) (Icc 0 (curveLength P a b).toReal ∩ Icc x y) :=
          eVariationOn.edist_le _ ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
      _ = 1 * edist x y := by
          rw [h, NNReal.coe_one, one_mul, one_mul, edist_comm, edist_dist, Real.dist_eq,
            abs_of_nonneg (sub_nonneg.2 hxy)]
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · exact key x hx y hy hxy
  · rw [edist_comm, edist_comm x]; exact key y hy x hx hxy

/-- `P t` and `lengthParam P a b (σ t)` are at distance zero, `σ t = len(P; [a, t])`. -/
theorem edist_lengthParam_variationOnFromTo {P : ℝ → X} {a b : ℝ}
    (hL : curveLength P a b ≠ ∞) {t : ℝ} (ht : t ∈ Icc a b) :
    edist (lengthParam P a b (variationOnFromTo P (Icc a b) a t)) (P t) = 0 :=
  edist_naturalParameterization_eq_zero
    (boundedVariationOn_of_curveLength_ne_top hL).locallyBoundedVariationOn
    ⟨le_rfl, ht.1.trans ht.2⟩ ht

end Pseudo

section EMetric

variable {X : Type*} [EMetricSpace X]

/-- In an extended metric space, `P = lengthParam P a b ∘ σ` on `[a, b]`. -/
theorem lengthParam_variationOnFromTo {P : ℝ → X} {a b : ℝ}
    (hL : curveLength P a b ≠ ∞) {t : ℝ} (ht : t ∈ Icc a b) :
    lengthParam P a b (variationOnFromTo P (Icc a b) a t) = P t :=
  edist_eq_zero.1 (edist_lengthParam_variationOnFromTo hL ht)

/-- **Constant-speed reparametrization.** A path of finite length `L` in an extended metric space
has a reparametrization with the same endpoints and length, image inside the original image,
which is `L`-Lipschitz on `[0, 1]`. -/
theorem exists_lipschitz_path {x y : X} (γ : Path x y) (hL : pathLength γ ≠ ∞) :
    ∃ γ' : Path x y, pathLength γ' = pathLength γ ∧ Set.range γ' ⊆ Set.range γ ∧
      LipschitzWith (pathLength γ).toNNReal γ' := by
  set P : ℝ → X := ⇑γ.extend
  have hPc : ContinuousOn P (Icc 0 1) := γ.continuous_extend.continuousOn
  have hL' : curveLength P 0 1 ≠ ∞ := hL
  set L : ℝ := (curveLength P 0 1).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set Q := lengthParam P 0 1
  have hlip := lipschitzOnWith_lengthParam zero_le_one hPc hL'
  have himg := variationOnFromTo_image_Icc zero_le_one hPc hL'
  have hmaps : ∀ s : I, L * (s : ℝ) ∈ Icc 0 L := fun s =>
    ⟨mul_nonneg hL0 s.2.1, mul_le_of_le_one_right hL0 s.2.2⟩
  have hQP : ∀ u ∈ Icc 0 L, ∃ t ∈ Icc (0 : ℝ) 1, Q u = P t := by
    intro u hu
    rw [← himg] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨t, ht, lengthParam_variationOnFromTo hL' ht⟩
  have hQ0 : Q 0 = x := by
    have := lengthParam_variationOnFromTo hL' (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.self] at this
    exact this.trans (Path.extend_zero γ)
  have hQ1 : Q L = y := by
    have := lengthParam_variationOnFromTo hL' (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.eq_of_le _ _ zero_le_one, Set.inter_self] at this
    exact this.trans (Path.extend_one γ)
  have hlipI : LipschitzWith (pathLength γ).toNNReal (fun s : I => Q (L * s)) := by
    intro s t
    have h1 := hlip (hmaps s) (hmaps t)
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.coe_one, one_mul, ENNReal.coe_toNNReal hL, edist_dist, edist_dist, Real.dist_eq, ← mul_sub,
      abs_mul, abs_of_nonneg hL0, ENNReal.ofReal_mul hL0, Subtype.dist_eq, Real.dist_eq,
      show ENNReal.ofReal L = pathLength γ from ENNReal.ofReal_toReal hL']
  let γ' : Path x y :=
    { toFun := fun s => Q (L * s)
      continuous_toFun := hlipI.continuous
      source' := by simpa using hQ0
      target' := by simpa using hQ1 }
  refine ⟨γ', ?_, ?_, hlipI⟩
  · unfold pathLength
    rw [curveLength_congr (Q := Q ∘ fun s => L * s) (fun t ht => by
      simp [γ', Path.extend_apply _ ht])]
    rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one (by fun_prop)
      (fun s _ t _ hst => mul_le_mul_of_nonneg_left hst hL0)]
    simp only [mul_zero, mul_one]
    exact curveLength_lengthParam zero_le_one hPc hL'
  · rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht, hts⟩ := hQP _ (hmaps s)
    refine ⟨⟨t, ht⟩, ?_⟩
    change γ ⟨t, ht⟩ = Q (L * s)
    rw [hts]
    exact (Path.extend_apply γ ht).symm

end EMetric

end LatticeProb.MetricGeometry
