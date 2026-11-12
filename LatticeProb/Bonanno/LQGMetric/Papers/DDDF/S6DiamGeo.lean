/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DiamGeo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamChain

/-!
# DDDF Prop 27, Step 1: the systems of a dyadic square (task P2-DDDF6d)

DF (arXiv:1809.02607) l. 1013: the system of a dyadic square of side `2h` (lower-left corner
`(X, Y)`) is formed by crossings of its two horizontal halves `[X, X+2h] × [Y, Y+h]`,
`[X, X+2h] × [Y+h, Y+2h]` (left to right) and of its two vertical halves `[X, X+h] × [Y, Y+2h]`,
`[X+h, X+2h] × [Y, Y+2h]` (bottom to top). The halves are the rectangles
`2^{-(k+1)} R_{2,1}` moved by `T20E.eH`, `T20E.eV` (scale `K = k + 1`).

* `adm_eH`, `adm_eV`: the coordinates of crossings of the moved rectangles.
* `sys_center`: every point of the system is within the sum of the four lengths of the meeting
  point of the first horizontal and the first vertical crossing.
* `sys_meet_child`: the first horizontal crossing of a quadrant meets the vertical crossing of
  the half of the parent square containing it (DF l. 1017: "the path goes from scale `n` to scale
  `n − 1`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP T20E

/-- the crossing condition of the moved rectangle `u 2^{-K} R_{2,1} + c` -/
def Adm21 (K : ℕ) (j : Circle × ℂ) (γ : ℝ → ℂ) : Prop :=
  AdmPath (T20B.mot K j.1 j.2 '' (rectAB 2 1).toSet) (T20B.mot K j.1 j.2 '' (rectAB 2 1).side₁)
    (T20B.mot K j.1 j.2 '' (rectAB 2 1).side₂) γ

/-- its crossing length -/
def len21 (ξ : ℝ) (f : ℂ → ℝ) (K : ℕ) (j : Circle × ℂ) : ℝ≥0∞ :=
  crossLenIn ξ f (T20B.mot K j.1 j.2 '' (rectAB 2 1).toSet)
    (T20B.mot K j.1 j.2 '' (rectAB 2 1).side₁) (T20B.mot K j.1 j.2 '' (rectAB 2 1).side₂)

theorem adm_eH {K : ℕ} {a b : ℤ} {γ : ℝ → ℂ} (h : Adm21 K (eH K a b) γ) :
    IsPiecewiseC1Path γ (γ 0) (γ 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, (γ t).re ∈ Icc ((a : ℝ) * (2 : ℝ)⁻¹ ^ K)
        ((a : ℝ) * (2 : ℝ)⁻¹ ^ K + 2 * (2 : ℝ)⁻¹ ^ K) ∧
      (γ t).im ∈ Icc ((b : ℝ) * (2 : ℝ)⁻¹ ^ K) ((b : ℝ) * (2 : ℝ)⁻¹ ^ K + (2 : ℝ)⁻¹ ^ K)) ∧
    (γ 0).re = (a : ℝ) * (2 : ℝ)⁻¹ ^ K ∧
    (γ 1).re = (a : ℝ) * (2 : ℝ)⁻¹ ^ K + 2 * (2 : ℝ)⁻¹ ^ K := by
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hP, hU⟩ := h
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  rw [mem_rectAB_side₁] at hx
  rw [mem_rectAB_side₂] at hy
  refine ⟨hP.source ▸ hP.target ▸ hP, fun t ht => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, e⟩ := hU t ht
    rw [mem_rectAB_toSet] at hz
    obtain ⟨e1, e2⟩ := mot_eH K a b z
    rw [← e, e1, e2]
    exact ⟨⟨by nlinarith [hz.1.1], by nlinarith [hz.1.2]⟩,
      ⟨by nlinarith [hz.2.1], by nlinarith [hz.2.2]⟩⟩
  · rw [hP.source, (mot_eH K a b x).1, hx.1]; ring
  · rw [hP.target, (mot_eH K a b y).1, hy.1]; ring

theorem adm_eV {K : ℕ} {a b : ℤ} {γ : ℝ → ℂ} (h : Adm21 K (eV K a b) γ) :
    IsPiecewiseC1Path γ (γ 0) (γ 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, (γ t).re ∈ Icc ((a : ℝ) * (2 : ℝ)⁻¹ ^ K - (2 : ℝ)⁻¹ ^ K)
        ((a : ℝ) * (2 : ℝ)⁻¹ ^ K) ∧
      (γ t).im ∈ Icc ((b : ℝ) * (2 : ℝ)⁻¹ ^ K) ((b : ℝ) * (2 : ℝ)⁻¹ ^ K + 2 * (2 : ℝ)⁻¹ ^ K)) ∧
    (γ 0).im = (b : ℝ) * (2 : ℝ)⁻¹ ^ K ∧
    (γ 1).im = (b : ℝ) * (2 : ℝ)⁻¹ ^ K + 2 * (2 : ℝ)⁻¹ ^ K := by
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hP, hU⟩ := h
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  rw [mem_rectAB_side₁] at hx
  rw [mem_rectAB_side₂] at hy
  refine ⟨hP.source ▸ hP.target ▸ hP, fun t ht => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, e⟩ := hU t ht
    rw [mem_rectAB_toSet] at hz
    obtain ⟨e1, e2⟩ := mot_eV K a b z
    rw [← e, e1, e2]
    exact ⟨⟨by nlinarith [hz.2.2], by nlinarith [hz.2.1]⟩,
      ⟨by nlinarith [hz.1.1], by nlinarith [hz.1.2]⟩⟩
  · rw [hP.source, (mot_eV K a b x).2, hx.1]; ring
  · rw [hP.target, (mot_eV K a b y).2, hy.1]; ring

/-- near-minimizing crossings exist -/
theorem exists_near {ξ : ℝ} {f : ℂ → ℝ} {U A B : Set ℂ} (hfin : crossLenIn ξ f U A B ≠ ⊤)
    {η : ℝ} (hη : 0 < η) :
    ∃ γ, AdmPath U A B γ ∧ lfppLen ξ f γ ≤ crossLenIn ξ f U A B + ENNReal.ofReal η := by
  have hlt : crossLenIn ξ f U A B < crossLenIn ξ f U A B + ENNReal.ofReal η :=
    ENNReal.lt_add_right hfin (by simpa using hη)
  rw [crossLenIn_eq_biInf] at hlt
  obtain ⟨γ, hlt1⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hγ, hlt'⟩ := iInf_lt_iff.1 hlt1
  exact ⟨γ, hγ, by rw [crossLenIn_eq_biInf]; exact hlt'.le⟩


/-- the four crossings `γ 0, γ 1` (horizontal halves) and `γ 2, γ 3` (vertical halves) of the
square `[X, X+2h] × [Y, Y+2h]` -/
structure SqSys (X Y h : ℝ) (γ : Fin 4 → ℝ → ℂ) : Prop where
  pc : ∀ e, IsPiecewiseC1Path (γ e) (γ e 0) (γ e 1)
  h0 : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0 t).re ∈ Icc X (X + 2 * h) ∧ (γ 0 t).im ∈ Icc Y (Y + h)
  h0e : (γ 0 0).re = X ∧ (γ 0 1).re = X + 2 * h
  h1 : ∀ t ∈ Icc (0 : ℝ) 1, (γ 1 t).re ∈ Icc X (X + 2 * h) ∧ (γ 1 t).im ∈ Icc (Y + h) (Y + 2 * h)
  h1e : (γ 1 0).re = X ∧ (γ 1 1).re = X + 2 * h
  h2 : ∀ t ∈ Icc (0 : ℝ) 1, (γ 2 t).re ∈ Icc X (X + h) ∧ (γ 2 t).im ∈ Icc Y (Y + 2 * h)
  h2e : (γ 2 0).im = Y ∧ (γ 2 1).im = Y + 2 * h
  h3 : ∀ t ∈ Icc (0 : ℝ) 1, (γ 3 t).re ∈ Icc (X + h) (X + 2 * h) ∧ (γ 3 t).im ∈ Icc Y (Y + 2 * h)
  h3e : (γ 3 0).im = Y ∧ (γ 3 1).im = Y + 2 * h

namespace SqSys

variable {X Y h : ℝ} {γ : Fin 4 → ℝ → ℂ}

lemma inSq (hS : SqSys X Y h γ) (hh : 0 ≤ h) (e : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ e t ∈ RectCross.rect X (X + 2 * h) Y (Y + 2 * h) := by
  obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> simp
  · obtain ⟨a, b⟩ := hS.h0 t ht
    exact ⟨a, b.1, by linarith [b.2]⟩
  · obtain ⟨a, b⟩ := hS.h1 t ht
    exact ⟨a, by linarith [b.1], b.2⟩
  · obtain ⟨a, b⟩ := hS.h2 t ht
    exact ⟨⟨a.1, by linarith [a.2]⟩, b⟩
  · obtain ⟨a, b⟩ := hS.h3 t ht
    exact ⟨⟨by linarith [a.1], a.2⟩, b⟩

/-- horizontal and vertical crossings of the system meet -/
lemma meet (hS : SqSys X Y h γ) (hh : 0 ≤ h) {e e' : Fin 4} (he : e = 0 ∨ e = 1)
    (he' : e' = 2 ∨ e' = 3) : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, γ e s = γ e' t := by
  have hx : (γ e 0).re = X ∧ (γ e 1).re = X + 2 * h := by
    rcases he with rfl | rfl
    · exact hS.h0e
    · exact hS.h1e
  have hy : (γ e' 0).im = Y ∧ (γ e' 1).im = Y + 2 * h := by
    rcases he' with rfl | rfl
    · exact hS.h2e
    · exact hS.h3e
  exact meet_of_cross (hS.pc e) (hS.pc e') (fun t ht => hS.inSq hh e ht)
    (fun t ht => hS.inSq hh e' ht) hx.1 hx.2 hy.1 hy.2

/-- the centre of the system: a meeting point of `γ 0` and `γ 2` -/
def center (hS : SqSys X Y h γ) (hh : 0 ≤ h) : ℂ :=
  γ 0 (hS.meet hh (Or.inl rfl) (Or.inl rfl)).choose

lemma center_spec (hS : SqSys X Y h γ) (hh : 0 ≤ h) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, hS.center hh = γ 0 s ∧ hS.center hh = γ 2 t := by
  obtain ⟨hs, t, ht, e⟩ := (hS.meet hh (Or.inl rfl) (Or.inl rfl)).choose_spec
  exact ⟨_, hs, t, ht, rfl, e⟩

/-- **every point of the system is within the sum of the four lengths of its centre** -/
lemma dist_center (hS : SqSys X Y h γ) (hh : 0 ≤ h) {ξ : ℝ} {f : ℂ → ℝ} {S : Set ℂ}
    (hSS : ∀ e, ∀ t ∈ Icc (0 : ℝ) 1, γ e t ∈ S) (e : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lfppDOn ξ f S (hS.center hh) (γ e t) ≤ ∑ e', lfppLen ξ f (γ e') := by
  obtain ⟨s₀, hs₀, t₀, ht₀, c0, c2⟩ := hS.center_spec hh
  have hd : ∀ e'' {a b : ℝ}, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      lfppDOn ξ f S (γ e'' a) (γ e'' b) ≤ lfppLen ξ f (γ e'') :=
    fun e'' a b ha hb => dOn_le_len (hS.pc e'') (hSS e'') ha hb
  have hsum := Fin.sum_univ_four (fun e' => lfppLen ξ f (γ e'))
  rw [hsum]
  obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> simp
  · rw [c0]
    calc lfppDOn ξ f S (γ 0 s₀) (γ 0 t) ≤ lfppLen ξ f (γ 0) := hd 0 hs₀ ht
      _ ≤ _ := by
          rw [show lfppLen ξ f (γ 0) + lfppLen ξ f (γ 1) + lfppLen ξ f (γ 2) + lfppLen ξ f (γ 3) = lfppLen ξ f (γ 0) + (lfppLen ξ f (γ 1) + lfppLen ξ f (γ 2) + lfppLen ξ f (γ 3)) by ring]; exact le_self_add
  · obtain ⟨a, ha, b, hb, eab⟩ := hS.meet hh (e := 1) (e' := 2) (Or.inr rfl) (Or.inl rfl)
    rw [c2]
    calc lfppDOn ξ f S (γ 2 t₀) (γ 1 t)
        ≤ lfppDOn ξ f S (γ 2 t₀) (γ 2 b) + lfppDOn ξ f S (γ 2 b) (γ 1 t) :=
          lfppDOn_triangle _ _ _
      _ ≤ lfppLen ξ f (γ 2) + lfppLen ξ f (γ 1) := by
          gcongr
          · exact hd 2 ht₀ hb
          · rw [← eab]; exact hd 1 ha ht
      _ ≤ _ := by
          rw [show lfppLen ξ f (γ 0) + lfppLen ξ f (γ 1) + lfppLen ξ f (γ 2) + lfppLen ξ f (γ 3) = lfppLen ξ f (γ 2) + lfppLen ξ f (γ 1) + (lfppLen ξ f (γ 0) + lfppLen ξ f (γ 3)) by ring]; exact le_self_add
  · rw [c2]
    calc lfppDOn ξ f S (γ 2 t₀) (γ 2 t) ≤ lfppLen ξ f (γ 2) := hd 2 ht₀ ht
      _ ≤ _ := by
          rw [show lfppLen ξ f (γ 0) + lfppLen ξ f (γ 1) + lfppLen ξ f (γ 2) + lfppLen ξ f (γ 3) = lfppLen ξ f (γ 2) + (lfppLen ξ f (γ 0) + lfppLen ξ f (γ 1) + lfppLen ξ f (γ 3)) by ring]; exact le_self_add
  · obtain ⟨a, ha, b, hb, eab⟩ := hS.meet hh (e := 0) (e' := 3) (Or.inl rfl) (Or.inr rfl)
    rw [c0]
    calc lfppDOn ξ f S (γ 0 s₀) (γ 3 t)
        ≤ lfppDOn ξ f S (γ 0 s₀) (γ 0 a) + lfppDOn ξ f S (γ 0 a) (γ 3 t) :=
          lfppDOn_triangle _ _ _
      _ ≤ lfppLen ξ f (γ 0) + lfppLen ξ f (γ 3) := by
          gcongr
          · exact hd 0 hs₀ ha
          · rw [eab]; exact hd 3 hb ht
      _ ≤ _ := by
          rw [show lfppLen ξ f (γ 0) + lfppLen ξ f (γ 1) + lfppLen ξ f (γ 2) + lfppLen ξ f (γ 3) = lfppLen ξ f (γ 0) + lfppLen ξ f (γ 3) + (lfppLen ξ f (γ 1) + lfppLen ξ f (γ 2)) by ring]; exact le_self_add

/-- **the first horizontal crossing of a quadrant meets a vertical crossing of the parent** -/
lemma meet_child {X' Y' : ℝ} {γ' : Fin 4 → ℝ → ℂ} (hS : SqSys X Y h γ) (hh : 0 ≤ h)
    (hS' : SqSys X' Y' (h / 2) γ') (hX : X' = X ∨ X' = X + h) (hY : Y' = Y ∨ Y' = Y + h) :
    ∃ e, ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, γ' 0 s = γ e t := by
  have hY' : ∀ t ∈ Icc (0 : ℝ) 1, (γ' 0 t).im ∈ Icc Y (Y + 2 * h) := fun t ht => by
    obtain ⟨-, b⟩ := hS'.h0 t ht
    rcases hY with rfl | rfl
    · exact ⟨b.1, by linarith [b.2]⟩
    · exact ⟨by linarith [b.1], by linarith [b.2]⟩
  rcases hX with rfl | rfl
  · obtain ⟨s, hs, t, ht, e⟩ := meet_of_cross (hS'.pc 0) (hS.pc 2) (x₀ := X') (x₁ := X' + h)
      (y₀ := Y) (y₁ := Y + 2 * h)
      (fun t ht => ⟨⟨(hS'.h0 t ht).1.1, by linarith [(hS'.h0 t ht).1.2]⟩, hY' t ht⟩)
      (fun t ht => hS.h2 t ht) hS'.h0e.1 (by rw [hS'.h0e.2]; ring) hS.h2e.1 hS.h2e.2
    exact ⟨2, s, hs, t, ht, e⟩
  · obtain ⟨s, hs, t, ht, e⟩ := meet_of_cross (hS'.pc 0) (hS.pc 3) (x₀ := X + h)
      (x₁ := X + 2 * h) (y₀ := Y) (y₁ := Y + 2 * h)
      (fun t ht => ⟨⟨(hS'.h0 t ht).1.1, by linarith [(hS'.h0 t ht).1.2]⟩, hY' t ht⟩)
      (fun t ht => hS.h3 t ht) hS'.h0e.1 (by rw [hS'.h0e.2]; ring) hS.h3e.1 hS.h3e.2
    exact ⟨3, s, hs, t, ht, e⟩

end SqSys

end S6D
end DDDF
end LQGMetric
