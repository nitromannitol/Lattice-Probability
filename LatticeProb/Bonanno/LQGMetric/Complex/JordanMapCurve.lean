/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Complex.JordanMapCurve at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMap
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Carathéodory's theorem for Jordan domains (generic form of DEC-B node J2)

`IsJordanCurve Γ`: `Γ` is the image of the unit circle under a map continuous and injective on
the circle. A Jordan curve is ULC (QuantumZipper `ULC.image_Icc`, through the parametrization
`t ↦ e^{i(2πt − π)}` of the circle) and has no cut points (the circle minus a point is the image
of `ℝ` under a rotated Cayley map). Hence `jm_exists_closedDisc_extension` applies:
`jm_jordan_closedDisc_extension` is Pommerenke (1992) Thm 2.6 (Carathéodory) for bounded Jordan
domains `U ∋ 0` that are simply connected in QuantumZipper's sense `HasHoloSqrt U`; the variant
`jm_jordan_closedDisc_extension'` takes instead "every component of `ℂ ∖ U` is unbounded"
(QuantumZipper `hasHoloSqrt_of_unbounded_compl`). Note: `IsSimplyConnected U → HasHoloSqrt U`
is not available in QuantumZipper or mathlib at our pins (QZ `RMTStep1.lean` l. 27).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter Complex
open QuantumZipper QuantumZipper.CA QuantumZipper.CA.Car

namespace LQGMetric.JordanMap

/-- `Γ` is a Jordan curve: the image of the unit circle under a map that is continuous and
injective on the circle. -/
def IsJordanCurve (Γ : Set ℂ) : Prop :=
  ∃ γ : ℂ → ℂ, ContinuousOn γ (sphere 0 1) ∧ InjOn γ (sphere 0 1) ∧ γ '' sphere 0 1 = Γ

theorem jm_sphere_eq_image_Icc :
    (fun t : ℝ => Complex.exp (((2 * Real.pi * t - Real.pi : ℝ) : ℂ) * I)) '' Icc 0 1 =
      sphere (0 : ℂ) 1 := by
  ext w
  constructor
  · rintro ⟨t, -, rfl⟩
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
  · intro hw
    have hn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
    have hpi := Real.pi_pos
    refine ⟨(arg w + Real.pi) / (2 * Real.pi), ⟨div_nonneg (by linarith [neg_pi_lt_arg w])
      (by positivity), (div_le_one (by positivity)).2 (by linarith [arg_le_pi w])⟩, ?_⟩
    have he : 2 * Real.pi * ((arg w + Real.pi) / (2 * Real.pi)) - Real.pi = arg w := by
      field_simp
      ring
    show Complex.exp (((2 * Real.pi * ((arg w + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) : ℂ)
      * I) = w
    rw [he]
    have h := norm_mul_exp_arg_mul_I w
    rwa [hn, Complex.ofReal_one, one_mul] at h

/-- The circle minus `1` is the Cayley image of `ℝ`. -/
theorem jm_sphere_diff_one_eq : sphere (0 : ℂ) 1 \ {1} = cayley '' range ((↑) : ℝ → ℂ) := by
  ext w
  constructor
  · rintro ⟨hw, hw1⟩
    refine ⟨cayleyInv w, ⟨(cayleyInv w).re, (jm_cayleyInv_real hw).symm⟩, ?_⟩
    exact cayley_cayleyInv hw1
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(jm_cayley_real x).1, (jm_cayley_real x).2⟩

theorem jm_isPreconnected_sphere_diff_one : IsPreconnected (sphere (0 : ℂ) 1 \ {1}) := by
  rw [jm_sphere_diff_one_eq]
  refine isPreconnected_range Complex.continuous_ofReal |>.image _ ?_
  refine continuousOn_cayley.mono ?_
  rintro _ ⟨x, rfl⟩
  exact ne_neg_I_iff.2 (add_I_ne_zero_of_im_nonneg (by simp))

theorem jm_isPreconnected_sphere_diff {p : ℂ} (hp : p ∈ sphere (0 : ℂ) 1) :
    IsPreconnected (sphere (0 : ℂ) 1 \ {p}) := by
  have hn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hn
  have he : sphere (0 : ℂ) 1 \ {p} = (fun w => p * w) '' (sphere (0 : ℂ) 1 \ {1}) := by
    ext w
    constructor
    · rintro ⟨hw, hwp⟩
      refine ⟨w / p, ⟨?_, fun h => hwp ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_div, mem_sphere_zero_iff_norm.1 hw, hn, div_one]
      · rw [mem_singleton_iff, div_eq_one_iff_eq hp0] at h
        exact h
      · field_simp
    · rintro ⟨v, ⟨hv, hv1⟩, rfl⟩
      refine ⟨?_, fun h => hv1 ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_mul, hn, mem_sphere_zero_iff_norm.1 hv, one_mul]
      · rw [mem_singleton_iff] at h ⊢
        exact (mul_eq_left₀ hp0).1 h
  rw [he]
  exact jm_isPreconnected_sphere_diff_one.image _ (by fun_prop)

theorem jm_isPreconnected_sphere : IsPreconnected (sphere (0 : ℂ) 1) := by
  have h : sphere (0 : ℂ) 1 = (sphere (0 : ℂ) 1 \ {1}) ∪ (sphere (0 : ℂ) 1 \ {-1}) := by
    ext w
    constructor
    · intro hw
      by_cases h1 : w = 1
      · refine Or.inr ⟨hw, ?_⟩
        rw [h1, mem_singleton_iff]
        norm_num
      · exact Or.inl ⟨hw, h1⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hI : I ∈ sphere (0 : ℂ) 1 := by simp
  have hI1 : I ≠ 1 := fun h => by simpa using congrArg Complex.im h
  have hI2 : I ≠ -1 := fun h => by simpa using congrArg Complex.im h
  rw [h]
  exact IsPreconnected.union I ⟨hI, hI1⟩ ⟨hI, hI2⟩ jm_isPreconnected_sphere_diff_one
    (jm_isPreconnected_sphere_diff (by simp))

/-- A Jordan curve is ULC. -/
theorem jm_ulc_of_isJordanCurve {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) : Topo.ULC Γ := by
  obtain ⟨γ, hγc, -, rfl⟩ := hΓ
  rw [← jm_sphere_eq_image_Icc, image_image]
  refine Topo.ULC.image_Icc (hγc.comp (by fun_prop) ?_)
  intro t _
  rw [← jm_sphere_eq_image_Icc]
  exact ⟨t, ‹_›, rfl⟩

/-- A Jordan curve has no cut points (and is connected). -/
theorem jm_isPreconnected_diff_of_isJordanCurve {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) (q : ℂ) :
    IsPreconnected (Γ \ {q}) := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hΓ
  by_cases hq : q ∈ γ '' sphere 0 1
  · obtain ⟨p, hp, rfl⟩ := hq
    have he : γ '' sphere 0 1 \ {γ p} = γ '' (sphere 0 1 \ {p}) := by
      ext y
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hne⟩
        refine ⟨x, ⟨hx, fun h => hne ?_⟩, rfl⟩
        rw [mem_singleton_iff] at h ⊢
        rw [h]
      · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, fun h => hxp (hγi hx hp (mem_singleton_iff.1 h))⟩
    rw [he]
    exact (jm_isPreconnected_sphere_diff hp).image _ (hγc.mono diff_subset)
  · rw [diff_singleton_eq_self hq]
    exact jm_isPreconnected_sphere.image _ hγc

/-- **J2 (generic, Jordan form; Carathéodory, Pommerenke 1992 Thm 2.6).** For `U ⊆ ℂ` open,
bounded, preconnected, simply connected in the sense `HasHoloSqrt U`, with `0 ∈ U` and
`frontier U` a Jordan curve, there is `φ` continuous and injective on the closed unit disc,
holomorphic on the open disc, `φ 0 = 0`, `φ '' 𝔻 = U`, `φ '' ∂𝔻 = ∂U`. -/
theorem jm_jordan_closedDisc_extension {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (h0 : (0 : ℂ) ∈ U) (hUb : Bornology.IsBounded U) (hsq : RMT.HasHoloSqrt U)
    (hJ : IsJordanCurve (frontier U)) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = 0 ∧ φ '' ball 0 1 = U ∧
      φ '' sphere 0 1 = frontier U :=
  jm_exists_closedDisc_extension hUo hUc h0 hUb hsq (jm_ulc_of_isJordanCurve hJ)
    (jm_isPreconnected_diff_of_isJordanCurve hJ)

/-- Variant of `jm_jordan_closedDisc_extension` with simple connectivity given as "every
component of `ℂ ∖ U` is unbounded" (QuantumZipper `hasHoloSqrt_of_unbounded_compl`). -/
theorem jm_jordan_closedDisc_extension' {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (h0 : (0 : ℂ) ∈ U) (hUb : Bornology.IsBounded U)
    (hcomp : ∀ a ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a))
    (hJ : IsJordanCurve (frontier U)) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = 0 ∧ φ '' ball 0 1 = U ∧
      φ '' sphere 0 1 = frontier U :=
  jm_jordan_closedDisc_extension hUo hUc h0 hUb (RMT.hasHoloSqrt_of_unbounded_compl hUo hUc hcomp)
    hJ

end LQGMetric.JordanMap
