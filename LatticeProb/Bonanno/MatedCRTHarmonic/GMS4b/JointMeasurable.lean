/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.JointMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.DegOutMeasurable

/-!
# Joint measurability of the point forms `z ↦ DA^ε(z), deg^ε_in(z), deg^ε_out(z), u^ε_*(z)`

[18] Propositions 4.1/4.8 integrate `z ↦ f(z) u^ε_*(z)` over `D` ([18]), which needs `(ω, z) ↦ u^ε_*(z)` to be jointly measurable. Here, on `C(ℝ, ℂ) × ℂ`:

* `measurable_hitTime`: `(c, z) ↦ τ_z = inf {t : c(t) = z}` is Borel (Lean's `sInf` junk value `0` on curves that do not
  hit `z` or whose hitting set is unbounded below is handled by a measurable case split);
* `locDA_curveShift` etc.: root time `t₀` is root time `0` of the shifted curve `c(t₀ + ·)`, a continuous function of
  `(c, t₀)`;
* `measurable_areaRatio`, `measurable_degreeIn`, `measurable_degreeOut`, `measurable_uStar`, `measurable_windowDiam`.
Composing with a measurable random curve `η : Ω → C(ℝ, ℂ)` gives joint measurability in `(ω, z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-! ## The shifted curve -/

/-- `t ↦ c(t₀ + t)`. -/
def curveShift (c : C(ℝ, ℂ)) (t₀ : ℝ) : C(ℝ, ℂ) := c.comp ⟨fun u => t₀ + u, by fun_prop⟩

theorem coe_curveShift (c : C(ℝ, ℂ)) (t₀ : ℝ) : (curveShift c t₀ : ℝ → ℂ) = timeAffine c t₀ 1 := by
  funext u; simp [curveShift, timeAffine]

theorem continuous_curveShift : Continuous fun p : C(ℝ, ℂ) × ℝ => curveShift p.1 p.2 := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).add continuous_snd))

theorem locDA_curveShift (ε : ℝ) (c : C(ℝ, ℂ)) (t₀ : ℝ) : locDA ε c t₀ = locDA ε (curveShift c t₀) 0 := by
  rw [coe_curveShift, show ε = ε / 1 from (div_one ε).symm, locDA_timeAffine c one_pos, div_one, mul_zero,
    add_zero]

theorem locDegIn_curveShift (ε : ℝ) (c : C(ℝ, ℂ)) (t₀ : ℝ) :
    locDegIn ε c t₀ = locDegIn ε (curveShift c t₀) 0 := by
  rw [coe_curveShift, show ε = ε / 1 from (div_one ε).symm, locDegIn_timeAffine c one_pos, div_one,
    mul_zero, add_zero]

theorem locDegOut_curveShift (ε : ℝ) (c : C(ℝ, ℂ)) (t₀ : ℝ) :
    locDegOut ε c t₀ = locDegOut ε (curveShift c t₀) 0 := by
  rw [coe_curveShift, show ε = ε / 1 from (div_one ε).symm, locDegOut_timeAffine c one_pos, div_one,
    mul_zero, add_zero]

theorem locWindow_curveShift (ε : ℝ) (c : C(ℝ, ℂ)) (t₀ : ℝ) :
    locWindow ε c t₀ = locWindow ε (curveShift c t₀) 0 := by
  rw [coe_curveShift, show ε = ε / 1 from (div_one ε).symm, locWindow_timeAffine c one_pos, div_one,
    mul_zero, add_zero]

theorem locUStar_curveShift (ε : ℝ) (c : C(ℝ, ℂ)) (t₀ : ℝ) :
    locUStar ε c t₀ = locUStar ε (curveShift c t₀) 0 := by
  rw [locUStar, locUStar, locDA_curveShift, locDegIn_curveShift, locDegOut_curveShift]

/-! ## The hitting time -/

/-- Curves hitting `z` at some time in a compact set: a closed condition. -/
theorem isClosed_hitIn {K : Set ℝ} (hK : IsCompact K) :
    IsClosed {p : C(ℝ, ℂ) × ℂ | ∃ t ∈ K, p.1 t = p.2} :=
  isClosed_exists_mem_of_isCompact (F := {q : (C(ℝ, ℂ) × ℂ) × ℝ | q.1.1 q.2 = q.1.2}) hK
    (isClosed_eq (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (continuous_snd.comp continuous_fst))

theorem measurableSet_hitIn_Iic (x : ℝ) :
    MeasurableSet {p : C(ℝ, ℂ) × ℂ | ∃ t ≤ x, p.1 t = p.2} := by
  have : {p : C(ℝ, ℂ) × ℂ | ∃ t ≤ x, p.1 t = p.2} =
      ⋃ n : ℕ, {p : C(ℝ, ℂ) × ℂ | ∃ t ∈ Icc (x - n) x, p.1 t = p.2} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_Icc]
    constructor
    · rintro ⟨t, ht, h⟩
      obtain ⟨n, hn⟩ := exists_nat_ge (x - t)
      exact ⟨n, t, ⟨by linarith, ht⟩, h⟩
    · rintro ⟨n, t, ⟨-, ht⟩, h⟩
      exact ⟨t, ht, h⟩
  rw [this]
  exact MeasurableSet.iUnion fun n => (isClosed_hitIn isCompact_Icc).measurableSet

theorem measurableSet_hitNonempty :
    MeasurableSet {p : C(ℝ, ℂ) × ℂ | (p.1 ⁻¹' {p.2}).Nonempty} := by
  have : {p : C(ℝ, ℂ) × ℂ | (p.1 ⁻¹' {p.2}).Nonempty} =
      ⋃ n : ℕ, {p : C(ℝ, ℂ) × ℂ | ∃ t ∈ Icc (-(n : ℝ)) n, p.1 t = p.2} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_Icc, Set.Nonempty, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨t, h⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |t|
      exact ⟨n, t, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩, h⟩
    · rintro ⟨n, t, -, h⟩
      exact ⟨t, h⟩
  rw [this]
  exact MeasurableSet.iUnion fun n => (isClosed_hitIn isCompact_Icc).measurableSet

theorem measurableSet_hitBddBelow :
    MeasurableSet {p : C(ℝ, ℂ) × ℂ | BddBelow (p.1 ⁻¹' {p.2})} := by
  have : {p : C(ℝ, ℂ) × ℂ | BddBelow (p.1 ⁻¹' {p.2})} =
      ⋃ M : ℕ, {p : C(ℝ, ℂ) × ℂ | ∃ t ≤ -(M : ℝ), p.1 t = p.2}ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, not_exists, not_and]
    constructor
    · rintro ⟨L, hL⟩
      obtain ⟨M, hM⟩ := exists_nat_gt (-L)
      refine ⟨M, fun t ht h => ?_⟩
      have := hL (show t ∈ p.1 ⁻¹' {p.2} from h)
      linarith
    · rintro ⟨M, hM⟩
      refine ⟨-(M : ℝ), fun t ht => ?_⟩
      by_contra hlt
      exact hM t (not_le.mp hlt).le ht
  rw [this]
  exact MeasurableSet.iUnion fun M => (measurableSet_hitIn_Iic _).compl

/-- **`τ_z` is a Borel function of `(c, z)`.** -/
theorem measurable_hitTime : Measurable fun p : C(ℝ, ℂ) × ℂ => hitTime p.1 p.2 := by
  set G : Set (C(ℝ, ℂ) × ℂ) := {p | (p.1 ⁻¹' {p.2}).Nonempty} ∩ {p | BddBelow (p.1 ⁻¹' {p.2})} with hG
  have hGm : MeasurableSet G := measurableSet_hitNonempty.inter measurableSet_hitBddBelow
  refine measurable_of_Iic fun x => ?_
  have heq : (fun p : C(ℝ, ℂ) × ℂ => hitTime p.1 p.2) ⁻¹' Iic x =
      (G ∩ {p | ∃ t ≤ x, p.1 t = p.2}) ∪ (Gᶜ ∩ {_p | (0 : ℝ) ≤ x}) := by
    ext p
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    by_cases hp : p ∈ G
    · obtain ⟨hne, hbdd⟩ := hp
      have hcl : IsClosed (p.1 ⁻¹' {p.2}) := isClosed_singleton.preimage p.1.continuous
      have hmem := hcl.csInf_mem hne hbdd
      simp only [hG, mem_inter_iff, hne, hbdd, true_and, not_true_eq_false, false_and,
        or_false]
      constructor
      · intro h; exact ⟨_, h, hmem⟩
      · rintro ⟨t, ht, h⟩; exact (csInf_le hbdd h).trans ht
    · have h0 : hitTime p.1 p.2 = 0 := by
        rw [hitTime]
        by_cases hne : (p.1 ⁻¹' {p.2}).Nonempty
        · have hbdd : ¬ BddBelow (p.1 ⁻¹' {p.2}) := fun hb => hp ⟨hne, hb⟩
          exact Real.sInf_of_not_bddBelow hbdd
        · rw [not_nonempty_iff_eq_empty] at hne
          change sInf (p.1 ⁻¹' {p.2}) = 0
          rw [hne, Real.sInf_empty]
      rw [h0]
      simp only [hp, false_and, not_false_eq_true, true_and, false_or]
  rw [heq]
  exact (hGm.inter (measurableSet_hitIn_Iic x)).union (hGm.compl.inter (MeasurableSet.const _))

/-! ## The point forms -/

theorem measurable_shiftAtHit : Measurable fun p : C(ℝ, ℂ) × ℂ => curveShift p.1 (hitTime p.1 p.2) :=
  continuous_curveShift.measurable.comp (measurable_fst.prodMk measurable_hitTime)

theorem measurable_areaRatio (ε : ℝ) : Measurable fun p : C(ℝ, ℂ) × ℂ => areaRatio ε p.1 p.2 := by
  have : (fun p : C(ℝ, ℂ) × ℂ => areaRatio ε p.1 p.2) =
      (fun c : C(ℝ, ℂ) => locDA ε c 0) ∘ fun p => curveShift p.1 (hitTime p.1 p.2) := by
    funext p; exact locDA_curveShift ε p.1 (hitTime p.1 p.2)
  rw [this]; exact (measurable_locDA ε 0).comp measurable_shiftAtHit

theorem measurable_degreeIn (ε : ℝ) : Measurable fun p : C(ℝ, ℂ) × ℂ => degreeIn ε p.1 p.2 := by
  have : (fun p : C(ℝ, ℂ) × ℂ => degreeIn ε p.1 p.2) =
      (fun c : C(ℝ, ℂ) => locDegIn ε c 0) ∘ fun p => curveShift p.1 (hitTime p.1 p.2) := by
    funext p; exact locDegIn_curveShift ε p.1 (hitTime p.1 p.2)
  rw [this]; exact (measurable_locDegIn ε 0).comp measurable_shiftAtHit

theorem measurable_degreeOut {ε : ℝ} (hε : 0 ≤ ε) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => degreeOut ε p.1 p.2 := by
  have : (fun p : C(ℝ, ℂ) × ℂ => degreeOut ε p.1 p.2) =
      (fun c : C(ℝ, ℂ) => locDegOut ε c 0) ∘ fun p => curveShift p.1 (hitTime p.1 p.2) := by
    funext p; exact locDegOut_curveShift ε p.1 (hitTime p.1 p.2)
  rw [this]; exact (measurable_locDegOut hε 0).comp measurable_shiftAtHit

theorem measurable_uStar {ε : ℝ} (hε : 0 ≤ ε) : Measurable fun p : C(ℝ, ℂ) × ℂ => uStar ε p.1 p.2 := by
  have : (fun p : C(ℝ, ℂ) × ℂ => uStar ε p.1 p.2) =
      (fun c : C(ℝ, ℂ) => locUStar ε c 0) ∘ fun p => curveShift p.1 (hitTime p.1 p.2) := by
    funext p; exact locUStar_curveShift ε p.1 (hitTime p.1 p.2)
  rw [this]; exact (measurable_locUStar hε 0).comp measurable_shiftAtHit

theorem measurable_windowDiam (ε : ℝ) : Measurable fun p : C(ℝ, ℂ) × ℂ => windowDiam ε p.1 p.2 := by
  have : (fun p : C(ℝ, ℂ) × ℂ => windowDiam ε p.1 p.2) =
      (fun c : C(ℝ, ℂ) => diam (locWindow ε c 0)) ∘ fun p => curveShift p.1 (hitTime p.1 p.2) := by
    funext p; exact congrArg diam (locWindow_curveShift ε p.1 (hitTime p.1 p.2))
  rw [this]; exact (continuous_diam_window ε 0).measurable.comp measurable_shiftAtHit

end MatedCRTHarmonic.GMS4b
