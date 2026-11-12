/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20DGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CCross
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Blocks
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

/-!
# DDDF Theorem 20, Step 4: short crossings around a visited block (task P2-DDDFT20d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1131–1135: "If `P ∈ 𝒫_K` is visited by a
`π_n(ψ)` geodesic, then there are at least two short disjoint rectangle crossings among the four
surrounding `P`", `R_i^S(P)` the four short rectangles of size `2^{-K}(1,3)` surrounding `P`,
inside the box `\hat P` of three times the size of `P`.

* `T20D.hatBox K b`: the box `\hat P` of the block `T20.dyBlock K b`;
* `T20D.shortJ K b`: the four rectangles `R_i^S(P)` as similarities `u 2^{-K} R_{1,3} + c`
  (marked sides: inner side → outer side);
* `T20D.exists_short_piece`: a crossing `γ : side₁ → side₂` of `[0,1]²` that visits `P` has a
  piece `γ|[a,c]` inside `\hat P` crossing one of the `R_i^S(P)` (forwards or backwards); we use
  one crossing (DDDF use two; one suffices for (5.67));
* `T20D.card_filter_hatBox_le`: a point lies in at most 16 boxes `\hat P` (DDDF: 9, for the
  interiors).
Own elementary arguments (DDDF leave them implicit), via `T20C.annulus_cross`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DDDF
namespace T20D

open LFPP

/-- the box `\hat P` of size `3 · 2^{-K}` with the block `T20.dyBlock K b` at its centre -/
def hatBox (K : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  Icc (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
    Icc (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K)

open Classical in
/-- the four short rectangles `R_i^S(P)` (DDDF l. 1137) as similarities `u 2^{-K} R_{1,3} + c`:
right, left, top and bottom strip of `\hat P \ P`, marked from the inner to the outer side -/
def shortJ (K : ℕ) (b : ℤ × ℤ) : Finset (Circle × ℂ) :=
  {(1, ⟨((b.1 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K, ((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K⟩),
   (circI * circI, ⟨(b.1 : ℝ) * (2 : ℝ)⁻¹ ^ K, ((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K⟩),
   (circI, ⟨((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K, ((b.2 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K⟩),
   (circI⁻¹, ⟨((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K, (b.2 : ℝ) * (2 : ℝ)⁻¹ ^ K⟩)}

lemma card_shortJ_le (K : ℕ) (b : ℤ × ℤ) : (shortJ K b).card ≤ 4 := by
  classical
  unfold shortJ
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  simp

/-- the image of `R_{1,3}` and of its marked sides under `x ↦ u 2^{-K} x + c` -/
def RS (K : ℕ) (j : Circle × ℂ) : Set ℂ := T20B.mot K j.1 j.2 '' (rectAB 1 3).toSet
/-- the first marked side -/
def RS₁ (K : ℕ) (j : Circle × ℂ) : Set ℂ := T20B.mot K j.1 j.2 '' (rectAB 1 3).side₁
/-- the second marked side -/
def RS₂ (K : ℕ) (j : Circle × ℂ) : Set ℂ := T20B.mot K j.1 j.2 '' (rectAB 1 3).side₂

lemma mem_R13 {x : ℂ} (h1 : 0 ≤ x.re) (h2 : x.re ≤ 1) (h3 : 0 ≤ x.im) (h4 : x.im ≤ 3) :
    x ∈ (rectAB 1 3).toSet := by
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add]
  exact ⟨⟨h1, h2⟩, h3, h4⟩

lemma mem_R13₁ {x : ℂ} (h1 : x.re = 0) (h3 : 0 ≤ x.im) (h4 : x.im ≤ 3) :
    x ∈ (rectAB 1 3).side₁ := by
  simp only [MarkedRect.side₁, rectAB, ↓reduceIte, Complex.mem_reProdIm, mem_Icc, zero_add,
    mem_singleton_iff]
  exact ⟨h1, h3, h4⟩

lemma mem_R13₂ {x : ℂ} (h1 : x.re = 1) (h3 : 0 ≤ x.im) (h4 : x.im ≤ 3) :
    x ∈ (rectAB 1 3).side₂ := by
  simp only [MarkedRect.side₂, rectAB, ↓reduceIte, Complex.mem_reProdIm, mem_Icc, zero_add,
    mem_singleton_iff]
  exact ⟨h1, h3, h4⟩

lemma mot_apply (K : ℕ) (u : Circle) (c x : ℂ) :
    T20B.mot K u c x = (u : ℂ) * (((2 : ℝ)⁻¹ ^ K : ℝ) * x) + c := rfl

/-- membership in a strip from the preimage point -/
lemma strip_mem {K : ℕ} {j : Circle × ℂ} {z : ℂ} (x : ℂ) (hx : T20B.mot K j.1 j.2 x = z)
    (h1 : 0 ≤ x.re) (h2 : x.re ≤ 1) (h3 : 0 ≤ x.im) (h4 : x.im ≤ 3) :
    z ∈ RS K j ∧ (x.re = 0 → z ∈ RS₁ K j) ∧ (x.re = 1 → z ∈ RS₂ K j) :=
  ⟨⟨x, mem_R13 h1 h2 h3 h4, hx⟩, fun h => ⟨x, mem_R13₁ h h3 h4, hx⟩,
    fun h => ⟨x, mem_R13₂ h h3 h4, hx⟩⟩

lemma h_pos (K : ℕ) : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity

lemma div_mem01 {h lo a m : ℝ} (hh : 0 < h) (h1 : lo ≤ a) (h2 : a ≤ lo + m * h) :
    0 ≤ (a - lo) / h ∧ (a - lo) / h ≤ m :=
  ⟨div_nonneg (by linarith) hh.le, by rw [div_le_iff₀ hh]; linarith⟩


section strips
variable (K : ℕ) (b : ℤ × ℤ) {z : ℂ}
local notation "hh" => ((2 : ℝ)⁻¹ ^ K)

lemma strip_right (h1 : ((b.1 : ℝ) + 1) * hh ≤ z.re) (h2 : z.re ≤ ((b.1 : ℝ) + 2) * hh)
    (h3 : ((b.2 : ℝ) - 1) * hh ≤ z.im) (h4 : z.im ≤ ((b.2 : ℝ) + 2) * hh) :
    let j : Circle × ℂ := (1, ⟨((b.1 : ℝ) + 1) * hh, ((b.2 : ℝ) - 1) * hh⟩)
    z ∈ RS K j ∧ (z.re = ((b.1 : ℝ) + 1) * hh → z ∈ RS₁ K j) ∧
      (z.re = ((b.1 : ℝ) + 2) * hh → z ∈ RS₂ K j) := by
  intro j
  have hp := h_pos K
  obtain ⟨a1, a2⟩ := div_mem01 (m := 1) hp h1 (by linarith)
  obtain ⟨a3, a4⟩ := div_mem01 (m := 3) hp h3 (by linarith)
  have hx : T20B.mot K j.1 j.2 ⟨(z.re - ((b.1 : ℝ) + 1) * hh) / hh,
      (z.im - ((b.2 : ℝ) - 1) * hh) / hh⟩ = z := by
    simp only [j, mot_apply]; generalize (2 : ℝ)⁻¹ ^ K = r at hp ⊢
    apply Complex.ext <;> simp <;> field_simp <;> ring
  obtain ⟨m1, m2, m3⟩ := strip_mem _ hx a1 a2 a3 a4
  refine ⟨m1, fun e => m2 (by simp only; rw [e]; simp), fun e => m3 ?_⟩
  simp only; rw [e]; field_simp; ring

lemma strip_left (h1 : ((b.1 : ℝ) - 1) * hh ≤ z.re) (h2 : z.re ≤ (b.1 : ℝ) * hh)
    (h3 : ((b.2 : ℝ) - 1) * hh ≤ z.im) (h4 : z.im ≤ ((b.2 : ℝ) + 2) * hh) :
    let j : Circle × ℂ := (circI * circI, ⟨(b.1 : ℝ) * hh, ((b.2 : ℝ) + 2) * hh⟩)
    z ∈ RS K j ∧ (z.re = (b.1 : ℝ) * hh → z ∈ RS₁ K j) ∧
      (z.re = ((b.1 : ℝ) - 1) * hh → z ∈ RS₂ K j) := by
  intro j
  have hp := h_pos K
  obtain ⟨a1, a2⟩ := div_mem01 (m := 1) hp (a := (b.1 : ℝ) * hh - z.re + ((b.1 : ℝ) - 1) * hh)
    (lo := ((b.1 : ℝ) - 1) * hh) (by linarith) (by linarith)
  obtain ⟨a3, a4⟩ := div_mem01 (m := 3) hp
    (a := ((b.2 : ℝ) + 2) * hh - z.im + ((b.2 : ℝ) - 1) * hh)
    (lo := ((b.2 : ℝ) - 1) * hh) (by linarith) (by linarith)
  have hx : T20B.mot K j.1 j.2 ⟨((b.1 : ℝ) * hh - z.re + ((b.1 : ℝ) - 1) * hh -
      ((b.1 : ℝ) - 1) * hh) / hh, (((b.2 : ℝ) + 2) * hh - z.im + ((b.2 : ℝ) - 1) * hh -
      ((b.2 : ℝ) - 1) * hh) / hh⟩ = z := by
    simp only [j, mot_apply]; generalize (2 : ℝ)⁻¹ ^ K = r at hp ⊢
    apply Complex.ext <;> simp [coe_circI] <;> field_simp <;> ring
  obtain ⟨m1, m2, m3⟩ := strip_mem _ hx a1 a2 a3 a4
  refine ⟨m1, fun e => m2 (by simp only; rw [e]; simp), fun e => m3 ?_⟩
  simp only; rw [e]; field_simp; ring

lemma strip_top (h1 : ((b.1 : ℝ) - 1) * hh ≤ z.re) (h2 : z.re ≤ ((b.1 : ℝ) + 2) * hh)
    (h3 : ((b.2 : ℝ) + 1) * hh ≤ z.im) (h4 : z.im ≤ ((b.2 : ℝ) + 2) * hh) :
    let j : Circle × ℂ := (circI, ⟨((b.1 : ℝ) + 2) * hh, ((b.2 : ℝ) + 1) * hh⟩)
    z ∈ RS K j ∧ (z.im = ((b.2 : ℝ) + 1) * hh → z ∈ RS₁ K j) ∧
      (z.im = ((b.2 : ℝ) + 2) * hh → z ∈ RS₂ K j) := by
  intro j
  have hp := h_pos K
  obtain ⟨a1, a2⟩ := div_mem01 (m := 1) hp h3 (by linarith)
  obtain ⟨a3, a4⟩ := div_mem01 (m := 3) hp
    (a := ((b.1 : ℝ) + 2) * hh - z.re + ((b.1 : ℝ) - 1) * hh)
    (lo := ((b.1 : ℝ) - 1) * hh) (by linarith) (by linarith)
  have hx : T20B.mot K j.1 j.2 ⟨(z.im - ((b.2 : ℝ) + 1) * hh) / hh,
      (((b.1 : ℝ) + 2) * hh - z.re + ((b.1 : ℝ) - 1) * hh - ((b.1 : ℝ) - 1) * hh) / hh⟩ = z := by
    simp only [j, mot_apply]; generalize (2 : ℝ)⁻¹ ^ K = r at hp ⊢
    apply Complex.ext <;> simp [coe_circI] <;> field_simp <;> ring
  obtain ⟨m1, m2, m3⟩ := strip_mem _ hx a1 a2 a3 a4
  refine ⟨m1, fun e => m2 (by simp only; rw [e]; simp), fun e => m3 ?_⟩
  simp only; rw [e]; field_simp; ring

lemma strip_bot (h1 : ((b.1 : ℝ) - 1) * hh ≤ z.re) (h2 : z.re ≤ ((b.1 : ℝ) + 2) * hh)
    (h3 : ((b.2 : ℝ) - 1) * hh ≤ z.im) (h4 : z.im ≤ (b.2 : ℝ) * hh) :
    let j : Circle × ℂ := (circI⁻¹, ⟨((b.1 : ℝ) - 1) * hh, (b.2 : ℝ) * hh⟩)
    z ∈ RS K j ∧ (z.im = (b.2 : ℝ) * hh → z ∈ RS₁ K j) ∧
      (z.im = ((b.2 : ℝ) - 1) * hh → z ∈ RS₂ K j) := by
  intro j
  have hp := h_pos K
  obtain ⟨a1, a2⟩ := div_mem01 (m := 1) hp (a := (b.2 : ℝ) * hh - z.im + ((b.2 : ℝ) - 1) * hh)
    (lo := ((b.2 : ℝ) - 1) * hh) (by linarith) (by linarith)
  obtain ⟨a3, a4⟩ := div_mem01 (m := 3) hp h1 (by linarith)
  have hx : T20B.mot K j.1 j.2 ⟨((b.2 : ℝ) * hh - z.im + ((b.2 : ℝ) - 1) * hh -
      ((b.2 : ℝ) - 1) * hh) / hh, (z.re - ((b.1 : ℝ) - 1) * hh) / hh⟩ = z := by
    simp only [j, mot_apply]; generalize (2 : ℝ)⁻¹ ^ K = r at hp ⊢
    apply Complex.ext <;> simp [coe_circI] <;> field_simp <;> ring
  obtain ⟨m1, m2, m3⟩ := strip_mem _ hx a1 a2 a3 a4
  refine ⟨m1, fun e => m2 (by simp only; rw [e]; simp), fun e => m3 ?_⟩
  simp only; rw [e]; field_simp; ring

end strips

lemma lt_sub_one_mul (a : ℝ) {h : ℝ} (hp : 0 < h) : (a - 1) * h < a * h := by nlinarith
lemma lt_add_two_mul (a : ℝ) {h : ℝ} (hp : 0 < h) : (a + 1) * h < (a + 2) * h := by nlinarith

lemma mem_hatBox {K : ℕ} {b : ℤ × ℤ} {z : ℂ} (hz : z ∈ hatBox K b) :
    ((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K ≤ z.re ∧ z.re ≤ ((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K ∧
      ((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K ≤ z.im ∧ z.im ≤ ((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K := by
  unfold hatBox at hz
  rw [Complex.mem_reProdIm] at hz
  exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩

/-- **A short crossing in the annulus** (DDDF l. 1131–1132): a piecewise `C¹` path from the block
`P` to the outside of the open box `\hat P°` has a piece inside `\hat P` crossing one of the four
short rectangles `R_i^S(P)` from the inner to the outer side. -/
lemma piece_of_cross {K : ℕ} {b : ℤ × ℤ} {G : ℝ → ℂ} {z w : ℂ} (hG : IsPiecewiseC1Path G z w)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hin : G s ∈ T20.dyBlock K b)
    (hout : G 1 ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K)) :
    ∃ u v, s ≤ u ∧ u < v ∧ v ≤ 1 ∧ (∀ r ∈ Icc u v, G r ∈ hatBox K b) ∧
      ∃ j ∈ shortJ K b, AdmPath (RS K j) (RS₁ K j) (RS₂ K j) (subPath G u v) := by
  classical
  have hp := h_pos K
  obtain ⟨u, v, hsu, huv, hv1, hbox, hcase⟩ := T20C.annulus_cross hs.2
    (hG.continuousOn.mono (Icc_subset_Icc hs.1 le_rfl)) (lt_sub_one_mul _ hp)
    (lt_add_two_mul _ hp) (lt_sub_one_mul _ hp) (lt_add_two_mul _ hp) hin hout
  have hbox' : ∀ r ∈ Icc u v, G r ∈ hatBox K b := hbox
  refine ⟨u, v, hsu, huv, hv1, hbox', ?_⟩
  have hP' := isPiecewiseC1Path_subPath hG (hs.1.trans hsu) huv hv1
  have hτ : ∀ τ ∈ Icc (0 : ℝ) 1, (v - u) * τ + u ∈ Icc u v := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hu : u ∈ Icc u v := ⟨le_rfl, huv.le⟩
  have hv : v ∈ Icc u v := ⟨huv.le, le_rfl⟩
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · have hS := fun r (hr' : r ∈ Icc u v) => have m := mem_hatBox (hbox' r hr')
      strip_top K b m.1 m.2.1 (hr r hr') m.2.2.2
    refine ⟨_, by simp [shortJ], G u, (hS u hu).2.1 e1, G v, (hS v hv).2.2 e2, hP',
      fun τ h => (hS _ (hτ τ h)).1⟩
  · have hS := fun r (hr' : r ∈ Icc u v) => have m := mem_hatBox (hbox' r hr')
      strip_bot K b m.1 m.2.1 m.2.2.1 (hr r hr')
    refine ⟨_, by simp [shortJ], G u, (hS u hu).2.1 e1, G v, (hS v hv).2.2 e2, hP',
      fun τ h => (hS _ (hτ τ h)).1⟩
  · have hS := fun r (hr' : r ∈ Icc u v) => have m := mem_hatBox (hbox' r hr')
      strip_right K b (hr r hr') m.2.1 m.2.2.1 m.2.2.2
    refine ⟨_, by simp [shortJ], G u, (hS u hu).2.1 e1, G v, (hS v hv).2.2 e2, hP',
      fun τ h => (hS _ (hτ τ h)).1⟩
  · have hS := fun r (hr' : r ∈ Icc u v) => have m := mem_hatBox (hbox' r hr')
      strip_left K b m.1 (hr r hr') m.2.2.1 m.2.2.2
    refine ⟨_, by simp [shortJ], G u, (hS u hu).2.1 e1, G v, (hS v hv).2.2 e2, hP',
      fun τ h => (hS _ (hτ τ h)).1⟩

lemma subPath_revPath (G : ℝ → ℂ) (u v : ℝ) :
    subPath (revPath G) u v = revPath (subPath G (1 - v) (1 - u)) := by
  funext τ; simp only [subPath, revPath]; congr 1; ring

/-- **Short crossing of a visited block** (DDDF l. 1131–1135): a left–right crossing `γ` of
`[0,1]²` that visits the block `P` (`K ≥ 2`) has a piece `γ|[a,c]` inside `\hat P` crossing one of
the four short rectangles `R_i^S(P)`, forwards or backwards. -/
theorem exists_short_piece {K : ℕ} (hK : 2 ≤ K) {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ) {b : ℤ × ℤ}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hb : γ t ∈ T20.dyBlock K b) :
    ∃ a c, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧ (∀ r ∈ Icc a c, γ r ∈ hatBox K b) ∧ ∃ j ∈ shortJ K b,
      (AdmPath (RS K j) (RS₁ K j) (RS₂ K j) (subPath γ a c) ∨
        AdmPath (RS K j) (RS₁ K j) (RS₂ K j) (revPath (subPath γ a c))) := by
  obtain ⟨z, hz, w, hw, hP, -⟩ := hγ
  have hp := h_pos K
  have hz0 : (γ 0).re = 0 := by
    rw [hP.source]
    simp only [MarkedRect.side₁, rectAB, ↓reduceIte, Complex.mem_reProdIm,
      mem_singleton_iff] at hz
    exact hz.1
  have hw1 : (γ 1).re = 1 := by
    rw [hP.target]
    simp only [MarkedRect.side₂, rectAB, ↓reduceIte, Complex.mem_reProdIm,
      mem_singleton_iff, zero_add] at hw
    exact hw.1
  have hsmall : 3 * (2 : ℝ)⁻¹ ^ K < 1 := by
    have : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
    norm_num at this ⊢; linarith
  by_cases h1 : γ 1 ∈ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K)
  · have h0 : revPath γ 1 ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K)
        (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
        Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) := by
      have e : revPath γ 1 = γ 0 := by simp only [revPath]; norm_num
      rw [e]
      intro h0
      rw [Complex.mem_reProdIm] at h0 h1
      have := h1.1.2; have := h0.1.1
      nlinarith
    have hs : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hin : revPath γ (1 - t) ∈ T20.dyBlock K b := by
      have e : revPath γ (1 - t) = γ t := by simp only [revPath]; congr 1; ring
      rwa [e]
    obtain ⟨u, v, hsu, huv, hv1, hbox, j, hj, hadm⟩ :=
      piece_of_cross (isPiecewiseC1Path_revPath hP) hs hin h0
    refine ⟨1 - v, 1 - u, by linarith, by linarith, by linarith [ht.2], fun r hr => ?_, j, hj,
      Or.inr ?_⟩
    · have := hbox (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have e : revPath γ (1 - r) = γ r := by simp only [revPath]; congr 1; ring
      rwa [e] at this
    · rwa [subPath_revPath] at hadm
  · obtain ⟨u, v, hsu, huv, hv1, hbox, j, hj, hadm⟩ := piece_of_cross hP ht hb h1
    exact ⟨u, v, ht.1.trans hsu, huv, hv1, hbox, j, hj, Or.inl hadm⟩

open Classical in
/-- a point lies in at most `16` boxes `\hat P` -/
lemma card_filter_hatBox_le (K : ℕ) (s : Finset (ℤ × ℤ)) (x : ℂ) :
    (s.filter fun b => x ∈ hatBox K b).card ≤ 16 := by
  have hp := h_pos K
  set m₁ : ℤ := ⌈x.re / (2 : ℝ)⁻¹ ^ K⌉
  set m₂ : ℤ := ⌈x.im / (2 : ℝ)⁻¹ ^ K⌉
  have hsub : s.filter (fun b => x ∈ hatBox K b) ⊆
      Finset.Icc (m₁ - 2) (m₁ + 1) ×ˢ Finset.Icc (m₂ - 2) (m₂ + 1) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨a1, a2, a3, a4⟩ := mem_hatBox hb.2
    have c1 : x.re / (2 : ℝ)⁻¹ ^ K ≤ (b.1 : ℝ) + 2 := by rw [div_le_iff₀ hp]; linarith
    have c2 : (b.1 : ℝ) - 1 ≤ x.re / (2 : ℝ)⁻¹ ^ K := by rw [le_div_iff₀ hp]; linarith
    have c3 : x.im / (2 : ℝ)⁻¹ ^ K ≤ (b.2 : ℝ) + 2 := by rw [div_le_iff₀ hp]; linarith
    have c4 : (b.2 : ℝ) - 1 ≤ x.im / (2 : ℝ)⁻¹ ^ K := by rw [le_div_iff₀ hp]; linarith
    have d1 : m₁ ≤ b.1 + 2 := Int.ceil_le.2 (by push_cast; linarith)
    have d2 : b.1 - 1 ≤ m₁ := by
      have : x.re / (2 : ℝ)⁻¹ ^ K ≤ (m₁ : ℝ) := Int.le_ceil _
      have : ((b.1 - 1 : ℤ) : ℝ) ≤ m₁ := by push_cast; linarith
      exact_mod_cast this
    have d3 : m₂ ≤ b.2 + 2 := Int.ceil_le.2 (by push_cast; linarith)
    have d4 : b.2 - 1 ≤ m₂ := by
      have : x.im / (2 : ℝ)⁻¹ ^ K ≤ (m₂ : ℝ) := Int.le_ceil _
      have : ((b.2 - 1 : ℤ) : ℝ) ≤ m₂ := by push_cast; linarith
      exact_mod_cast this
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have e : ∀ a : ℤ, (a + 1 + 1 - (a - 2)).toNat = 4 := fun a => by omega
  rw [e, e]

end T20D
end DDDF
end LQGMetric
