/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.RectCross at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Topology.Path
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A crossing of a portrait rectangle crosses a sub-rectangle the thin way (DDDF Lemma 11)

**DDDF Lemma 11** (Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage
percolation for γ ∈ (0,2)*, arXiv:1904.08021, `tightness.tex` lines 739–742) = **DF Lemma 4.8**
(Dubédat–Falconet, *Liouville metric of star-scale invariant fields: tails and Weyl scaling*,
arXiv:1809.02607, `LiouvilleMetricStarScale.tex` lines 607–618): for `0 < a < b` there are
`j = j(b/a)` rectangles isometric to `[0, a/2] × [0, b/2]` such that every left–right crossing of
`[0, a] × [0, b]` has a subpath crossing one of them in the thin direction.

We follow DF's proof. With `δ = (b - a)/4` the rectangles are the vertical ones
`[0, a/2] × [kδ, kδ + b/2]` and (containing DF's squares `[0, a/2] × [kδ, kδ + a/2]`) the
horizontal ones `[0, b/2] × [kδ, kδ + a/2]`, `k ≤ ⌊b/δ⌋ + 1`; so `j = 2(⌊4(b/a)/(b/a - 1)⌋ + 2)`.
Take a subpath from the left side to the line `x = a/2` (inside the strip `0 ≤ x ≤ a/2`); let `h`
be its height. If `h ≤ a/2 + δ` it lies in a vertical rectangle and crosses it left–right; else
it crosses a square (hence the horizontal rectangle containing it) bottom–top.
Subpaths are given by parameter intervals `[s, t] ⊆ [0, 1]` of `γ.extend`, so the sub-crossing is
a genuine piece of `γ` (as the length comparison in DDDF Prop 14 needs). The one-dimensional
sub-crossing extraction `exists_sub_crossing` (last visit to level `z` before the first visit to
level `w`) is an own elementary argument (DF: "consider the subpath from the left side to the
first hitting point of `{a/2} × [0, b]`").
-/

namespace LQGMetric

open Set

namespace RectCross

/-- Sub-crossing extraction: if `f` is continuous on `[α, β]` with `f α ≤ z ≤ w ≤ f β`, there is
`[s, t] ⊆ [α, β]` with `f s = z`, `f t = w` and `f ∈ [z, w]` on `[s, t]`. -/
theorem exists_sub_crossing {f : ℝ → ℝ} {α β z w : ℝ} (hαβ : α ≤ β)
    (hf : ContinuousOn f (Icc α β)) (hzw : z ≤ w) (hα : f α ≤ z) (hβ : w ≤ f β) :
    ∃ s t, α ≤ s ∧ s ≤ t ∧ t ≤ β ∧ f s = z ∧ f t = w ∧ ∀ u ∈ Icc s t, f u ∈ Icc z w := by
  set T := Icc α β ∩ f ⁻¹' {w} with hT
  have hTc : IsClosed T := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := by
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hαβ hf ⟨hα.trans hzw, hβ⟩
    exact ⟨v, hv, hfv⟩
  have hTb : BddBelow T := ⟨α, fun u hu => hu.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTc.csInf_mem hTne hTb
  have hαt : α ≤ t := htT.1.1
  have hbelow : ∀ u ∈ Ico α t, f u < w := by
    intro u hu
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hu.1
      (hf.mono (Icc_subset_Icc le_rfl (hu.2.le.trans htT.1.2))) ⟨hα.trans hzw, hcon⟩
    have : t ≤ v := csInf_le hTb ⟨⟨hv.1, hv.2.trans (hu.2.le.trans htT.1.2)⟩, hfv⟩
    linarith [hv.2, hu.2]
  have hft : f t = w := htT.2
  set S := Icc α t ∩ f ⁻¹' {z} with hS
  have hfαt : ContinuousOn f (Icc α t) := hf.mono (Icc_subset_Icc le_rfl htT.1.2)
  have hSc : IsClosed S := hfαt.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hαt hfαt ⟨hα, hft ▸ hzw⟩
    exact ⟨v, hv, hfv⟩
  have hSb : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  set s := sSup S with hs
  have hsS : s ∈ S := hSc.csSup_mem hSne hSb
  have habove : ∀ u ∈ Ioc s t, z ≤ f u := by
    intro u hu
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hu.2
      (hfαt.mono (Icc_subset_Icc (hsS.1.1.trans hu.1.le) le_rfl)) ⟨hcon.le, hft ▸ hzw⟩
    have : v ≤ s := le_csSup hSb ⟨⟨hsS.1.1.trans (hu.1.le.trans hv.1), hv.2⟩, hfv⟩
    linarith [hv.1, hu.1]
  refine ⟨s, t, hsS.1.1, hsS.1.2, htT.1.2, hsS.2, hft, fun u hu => ⟨?_, ?_⟩⟩
  · rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact hsS.2.ge
    · exact habove u ⟨h, hu.2⟩
  · rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h, hft]
    · exact (hbelow u ⟨hsS.1.1.trans hu.1, h⟩).le

/-- The decreasing version of `exists_sub_crossing`. -/
theorem exists_sub_crossing' {f : ℝ → ℝ} {α β z w : ℝ} (hαβ : α ≤ β)
    (hf : ContinuousOn f (Icc α β)) (hzw : z ≤ w) (hα : w ≤ f α) (hβ : f β ≤ z) :
    ∃ s t, α ≤ s ∧ s ≤ t ∧ t ≤ β ∧ f s = w ∧ f t = z ∧ ∀ u ∈ Icc s t, f u ∈ Icc z w := by
  obtain ⟨s, t, h1, h2, h3, h4, h5, h6⟩ := exists_sub_crossing (f := fun u => -f u) hαβ hf.neg
    (neg_le_neg hzw) (neg_le_neg hα) (neg_le_neg hβ)
  refine ⟨s, t, h1, h2, h3, by simpa using h4, by simpa using h5, fun u hu => ?_⟩
  have := h6 u hu
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

/-- The closed rectangle `[x₀, x₁] × [y₀, y₁] ⊂ ℂ`. -/
def rect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ := {ζ | ζ.re ∈ Icc x₀ x₁ ∧ ζ.im ∈ Icc y₀ y₁}

/-- A subpath `γ|[s,t]` lies in `[x₀, x₁] × [y₀, y₁]` and joins its left and right sides. -/
def CrossesLR {p q : ℂ} (γ : Path p q) (x₀ x₁ y₀ y₁ : ℝ) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧ (∀ u ∈ Icc s t, γ.extend u ∈ rect x₀ x₁ y₀ y₁) ∧
    (((γ.extend s).re = x₀ ∧ (γ.extend t).re = x₁) ∨
      ((γ.extend s).re = x₁ ∧ (γ.extend t).re = x₀))

/-- A subpath `γ|[s,t]` lies in `[x₀, x₁] × [y₀, y₁]` and joins its bottom and top sides. -/
def CrossesBT {p q : ℂ} (γ : Path p q) (x₀ x₁ y₀ y₁ : ℝ) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧ (∀ u ∈ Icc s t, γ.extend u ∈ rect x₀ x₁ y₀ y₁) ∧
    (((γ.extend s).im = y₀ ∧ (γ.extend t).im = y₁) ∨
      ((γ.extend s).im = y₁ ∧ (γ.extend t).im = y₀))

/-- **DDDF Lemma 11 = DF Lemma 4.8.** Let `0 < a < b` and `δ = (b - a)/4`. Every left–right
crossing `γ` of `[0, a] × [0, b]` has a subpath crossing, in the thin direction, one of the
`2(⌊b/δ⌋ + 2)` rectangles `[0, a/2] × [kδ, kδ + b/2]` (left–right) or
`[0, b/2] × [kδ, kδ + a/2]` (bottom–top), `k ≤ ⌊b/δ⌋ + 1`; all are isometric to
`[0, a/2] × [0, b/2]`, and `⌊b/δ⌋ = ⌊4(b/a)/(b/a - 1)⌋` depends only on `b/a`. -/
theorem crossing_thin_subrect {a b : ℝ} (ha : 0 < a) (hab : a < b) {p q : ℂ} (γ : Path p q)
    (hγ : ∀ τ, γ τ ∈ rect 0 a 0 b) (hp : p.re = 0) (hq : q.re = a) :
    ∃ k : ℕ, k ≤ ⌊b / ((b - a) / 4)⌋₊ + 1 ∧
      (CrossesLR γ 0 (a / 2) (k * ((b - a) / 4)) (k * ((b - a) / 4) + b / 2) ∨
        CrossesBT γ 0 (b / 2) (k * ((b - a) / 4)) (k * ((b - a) / 4) + a / 2)) := by
  set δ := (b - a) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set g := γ.extend with hg
  have hgc : Continuous g := γ.continuous_extend
  have hgR : ∀ u, g u ∈ rect 0 a 0 b := by
    intro u
    obtain ⟨τ, hτ⟩ : g u ∈ range γ := γ.extend_range ▸ mem_range_self u
    exact hτ ▸ hγ τ
  -- the subpath from the left side to the line `x = a/2`
  obtain ⟨s, t, hs0, hst, ht1, hgs, hgt, hre⟩ := exists_sub_crossing (f := fun u => (g u).re)
    zero_le_one (Complex.continuous_re.comp hgc).continuousOn (by linarith : (0 : ℝ) ≤ a / 2)
    (by simp [hg, hp]) (by simp [hg, hq]; linarith)
  -- its lowest and highest points
  have himc : ContinuousOn (fun u => (g u).im) (Icc s t) :=
    (Complex.continuous_im.comp hgc).continuousOn
  obtain ⟨σ₁, hσ₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hst) himc
  obtain ⟨σ₂, hσ₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hst) himc
  set m := (g σ₁).im with hm
  set M := (g σ₂).im with hM
  have hm0 : 0 ≤ m := (hgR σ₁).2.1
  have hMb : M ≤ b := (hgR σ₂).2.2
  set k₀ := ⌊m / δ⌋₊ with hk₀
  have hk₀le : (k₀ : ℝ) * δ ≤ m := by
    have := Nat.floor_le (div_nonneg hm0 hδ0.le)
    rw [← hk₀] at this
    exact (le_div_iff₀ hδ0).1 this
  have hk₀lt : m < ((k₀ : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one (m / δ)
    rw [← hk₀] at this
    exact (div_lt_iff₀ hδ0).1 this
  have hk₀N : k₀ ≤ ⌊b / δ⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right ((hgR σ₁).2.2) hδ0.le)
  have hsub : ∀ u ∈ Icc s t, (g u).re ∈ Icc 0 (a / 2) ∧ (g u).im ∈ Icc m M := fun u hu =>
    ⟨hre u hu, hmin hu, hmax hu⟩
  rcases le_or_gt (M - m) (a / 2 + δ) with hh | hh
  · -- low path: a left–right crossing of a vertical rectangle
    refine ⟨k₀, by omega, Or.inl ⟨s, t, hs0, hst, ht1, fun u hu => ?_, Or.inl ⟨hgs, hgt⟩⟩⟩
    obtain ⟨h1, h2⟩ := hsub u hu
    refine ⟨h1, by linarith [h2.1], ?_⟩
    have : 2 * δ + a / 2 = b / 2 := by rw [hδ]; ring
    linarith [h2.2]
  · -- tall path: a bottom–top crossing of a square, inside a horizontal rectangle
    set z := ((k₀ : ℝ) + 1) * δ with hz
    have hzm : m ≤ z := hk₀lt.le
    have hzM : z + a / 2 ≤ M := by nlinarith
    have hcast : ((k₀ + 1 : ℕ) : ℝ) = (k₀ : ℝ) + 1 := by push_cast; ring
    refine ⟨k₀ + 1, by omega, Or.inr ?_⟩
    rw [hcast, ← hz]
    have hin : ∀ {s' t' : ℝ}, s ≤ s' → t' ≤ t → (∀ u ∈ Icc s' t', (g u).im ∈ Icc z (z + a / 2))
        → ∀ u ∈ Icc s' t', g u ∈ rect 0 (b / 2) z (z + a / 2) := by
      intro s' t' hs' ht' hI u hu
      have := (hsub u ⟨hs'.trans hu.1, hu.2.trans ht'⟩).1
      exact ⟨⟨this.1, by linarith [this.2]⟩, hI u hu⟩
    rcases le_total σ₁ σ₂ with h12 | h21
    · obtain ⟨s', t', h1, h2, h3, h4, h5, h6⟩ := exists_sub_crossing h12
        (himc.mono (Icc_subset_Icc hσ₁.1 hσ₂.2)) (by linarith) hzm hzM
      exact ⟨s', t', hs0.trans (hσ₁.1.trans h1), h2, h3.trans (hσ₂.2.trans ht1),
        hin (hσ₁.1.trans h1) (h3.trans hσ₂.2) h6, Or.inl ⟨h4, h5⟩⟩
    · obtain ⟨s', t', h1, h2, h3, h4, h5, h6⟩ := exists_sub_crossing' h21
        (himc.mono (Icc_subset_Icc hσ₂.1 hσ₁.2)) (by linarith) hzM hzm
      exact ⟨s', t', hs0.trans (hσ₂.1.trans h1), h2, h3.trans (hσ₁.2.trans ht1),
        hin (hσ₂.1.trans h1) (h3.trans hσ₁.2) h6, Or.inr ⟨h4, h5⟩⟩

end RectCross

end LQGMetric
