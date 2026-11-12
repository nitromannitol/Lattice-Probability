/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XBridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L16Good

/-!
# DZZ Lemma 3.12: an enclosure is not inside one cell; rotating a ring (D93, P-6a)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1471–1477,
the two segments of `𝒞_{i,cross}` presume a ring of at least two cells) in the ring form of D93.

* `hray`: the horizontal rays from the centre of `𝖢` to `∂𝖢_large`;
* **`not_enc_one_cell`**: boxes with interiors outside `𝖢` lying in one cell `c` do not enclose `𝖢`
  (both rays meet `c`, so `c` contains the centre of `𝖢`, and dyadic nesting);
* `exists_suffix_split`, **`block_rotate`**: rotating a cyclic list at a change of cell keeps the
  blocks of the parent cells.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- The horizontal ray `t ↦ c_𝖢 + σ t s_𝖢`. -/
def hray (C : DyBox) (σ : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => C.center + ((σ * (t : ℝ) * C.side : ℝ) : ℂ),
    continuous_const.add (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const))⟩

lemma hray_re (C : DyBox) (σ : ℝ) (t : unitInterval) :
    (hray C σ t).re = C.center.re + σ * (t : ℝ) * C.side := by
  simp [hray]

lemma hray_im (C : DyBox) (σ : ℝ) (t : unitInterval) : (hray C σ t).im = C.center.im := by
  simp [hray]

lemma largeBox_closed (C : DyBox) : IsClosed C.largeBox := by
  have cr : Continuous fun w : ℂ => |w.re - C.center.re| :=
    continuous_abs.comp (Complex.continuous_re.sub continuous_const)
  have ci : Continuous fun w : ℂ => |w.im - C.center.im| :=
    continuous_abs.comp (Complex.continuous_im.sub continuous_const)
  exact (isClosed_le cr continuous_const).inter (isClosed_le ci continuous_const)

lemma hray_mem {C : DyBox} {σ : ℝ} (hσ : |σ| = 1) (t : unitInterval) :
    hray C σ t ∈ C.largeBox := by
  have hs := C.side_pos'
  have ht0 := t.2.1; have ht1 := t.2.2
  refine ⟨?_, ?_⟩
  · rw [hray_re, add_sub_cancel_left, abs_mul, abs_mul, hσ, abs_of_nonneg ht0,
      abs_of_pos hs]
    nlinarith
  · rw [hray_im, sub_self, abs_zero]; exact hs.le

lemma hray_one {C : DyBox} {σ : ℝ} (hσ : |σ| = 1) : hray C σ 1 ∈ frontier C.largeBox := by
  have hs := C.side_pos'
  rw [(largeBox_closed C).frontier_eq]
  refine ⟨hray_mem hσ 1, fun hi => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hi
  set w : ℂ := hray C σ 1 + ((σ * (ε / 2) : ℝ) : ℂ)
  have hw : w ∈ Metric.ball (hray C σ 1) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [w, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_mul, hσ,
      one_mul, abs_of_pos (half_pos hε)]
    linarith
  have h1 := (interior_subset (hball hw)).1
  have e : w.re - C.center.re = σ * (C.side + ε / 2) := by
    simp only [w, Complex.add_re, Complex.ofReal_re, hray_re]
    simp; ring
  rw [e, abs_mul, hσ, one_mul, abs_of_pos (by positivity)] at h1
  linarith

/-- **An enclosure of `𝖢` does not lie in one cell.** -/
lemma not_enc_one_cell {C c : DyBox} (hC : IsCell m δ C) (hc : IsCell m δ c)
    (hint : C.largeBox ⊆ interior dzzV) {S : Set DyBox}
    (hS : ∀ b ∈ S, b.closedBox ⊆ c.closedBox ∧ Disjoint (interior b.closedBox) C.closedBox)
    (henc : EnclosesBox C S) : False := by
  have hs := C.side_pos'
  have ray : ∀ σ : ℝ, |σ| = 1 → ∃ t : unitInterval, ∃ b ∈ S, hray C σ t ∈ b.closedBox :=
    fun σ hσ => henc (hray C σ) (fun t => interior_subset (hint (hray_mem hσ t)))
      (by
        have e : hray C σ 0 = C.center := by simp [hray]
        rw [e]; exact center_mem_closedBox C)
      (hray_one hσ)
  obtain ⟨t1, b1, hb1, hp1⟩ := ray 1 (by simp)
  obtain ⟨t2, b2, hb2, hp2⟩ := ray (-1) (by simp)
  have q1 := (hS b1 hb1).1 hp1
  have q2 := (hS b2 hb2).1 hp2
  have hcen : C.center ∈ c.closedBox := by
    obtain ⟨a1, a2, a3, a4⟩ := q1
    obtain ⟨c1, c2, c3, c4⟩ := q2
    rw [hray_re] at a1 a2 c1 c2
    rw [hray_im] at a3 a4 c3 c4
    have u1 := t1.2.1; have u2 := t2.2.1
    refine ⟨?_, ?_, a3, a4⟩
    · nlinarith
    · nlinarith
  have key : c.closedBox ⊆ C.closedBox := by
    rcases le_or_gt C.n c.n with hle | hlt
    · set D := c.anc C.n
      have hDn : D.n = C.n := by show min C.n c.n = C.n; omega
      have hcD := closedBox_sub_anc c C.n
      have hCD : C.closedBox ⊆ D.closedBox := sub_of_center_mem rfl hDn.le (hcD hcen)
      have e : C.anc D.n = D := anc_eq_of_sub rfl hDn.le hCD
      have e2 : C.anc C.n = C := anc_eq_of_sub rfl le_rfl subset_rfl
      rw [hDn, e2] at e
      rw [e]; exact hcD
    · exact absurd hc (not_isCell_of_sub hC hlt (sub_of_center_mem rfl hlt.le hcen))
  have hb := hS b1 hb1
  exact Set.disjoint_left.1 hb.2 (center_mem_interior_closedBox b1)
    (key (hb.1 (interior_subset (center_mem_interior_closedBox b1))))

/-- Splitting off the maximal suffix satisfying `Q`. -/
lemma exists_suffix_split (Q : DyBox → Prop) : ∀ F : List DyBox,
    ∃ A T : List DyBox, F = A ++ T ∧ (∀ y ∈ T, Q y) ∧ ∀ a ∈ A.getLast?, ¬ Q a
  | [] => ⟨[], [], rfl, by simp, by simp⟩
  | a :: F => by
    obtain ⟨A, T, rfl, hT, hA⟩ := exists_suffix_split Q F
    rcases A with _ | ⟨x, A⟩
    · by_cases ha : Q a
      · refine ⟨[], a :: T, rfl, ?_, by simp⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ha
        · exact hT y hy
      · exact ⟨[a], T, rfl, hT, by simpa using ha⟩
    · refine ⟨a :: x :: A, T, rfl, hT, ?_⟩
      rw [List.getLast?_cons_cons]; exact hA

/-- The boxes of cell `P` form one block of `L`. -/
def CellBlock (f : DyBox → DyBox) (P : DyBox) (L : List DyBox) : Prop :=
  ∃ L₁ L₂ L₃ : List DyBox, L = L₁ ++ L₂ ++ L₃ ∧ (∀ b ∈ L₂, f b = P) ∧ ∀ b ∈ L₁ ++ L₃, f b ≠ P

lemma mem_of_getLast? {l : List DyBox} {a : DyBox} (h : a ∈ l.getLast?) : a ∈ l := by
  rcases l with _ | ⟨x, l⟩
  · simp at h
  · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at h
    cases h; exact List.getLast_mem _

/-- **Rotating at a change of cell keeps the blocks.** -/
lemma block_rotate {f : DyBox → DyBox} {P c : DyBox} {A T : List DyBox}
    (hT : ∀ y ∈ T, f y = c) (hA : ∀ a ∈ A.getLast?, f a ≠ c)
    (hnot : ∃ y ∈ A ++ T, f y ≠ c) (hhead : ∀ a ∈ (A ++ T).head?, f a = c)
    (hB : CellBlock f P (A ++ T)) : CellBlock f P (T ++ A) := by
  by_cases hT0 : T = []
  · subst hT0; simpa using hB
  obtain ⟨L₁, L₂, L₃, e, h2, h13⟩ := hB
  by_cases hcP : c = P
  · exfalso
    subst hcP
    have hL1 : L₁ = [] := by
      rcases L₁ with _ | ⟨x, L₁⟩
      · rfl
      · exfalso
        exact h13 x (by simp) (hhead x (by rw [e]; simp))
    have hL3 : L₃ = [] := by
      rcases List.eq_nil_or_concat L₃ with h | ⟨L₃', x, rfl⟩
      · exact h
      · exfalso
        have hx : x ∈ (A ++ T).getLast? := by rw [e]; simp
        rw [List.getLast?_append_of_ne_nil _ hT0] at hx
        exact h13 x (by simp) (hT x (mem_of_getLast? hx))
    obtain ⟨y, hy, hyc⟩ := hnot
    rw [e, hL1, hL3] at hy
    exact hyc (h2 y (by simpa using hy))
  by_cases hL2 : L₂ = []
  · subst hL2
    refine ⟨T ++ A, [], [], by simp, by simp, fun y hy => h13 y ?_⟩
    have : y ∈ A ++ T := by
      rcases List.mem_append.1 (by simpa using hy) with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    rw [e] at this; simpa using this
  rw [List.append_assoc L₁ L₂ L₃, ← List.append_assoc, List.append_eq_append_iff] at e
  rcases e with ⟨a', h1, h3⟩ | ⟨c', h1, h3⟩
  · -- `L₁ ++ L₂ = A ++ a'`, `T = a' ++ L₃`
    rcases List.eq_nil_or_concat a' with ha' | ⟨a'', z, rfl⟩
    · subst ha'
      simp only [List.append_nil] at h1
      subst h3
      refine ⟨T ++ L₁, L₂, [], by rw [← h1]; simp, h2, fun y hy => ?_⟩
      simp only [List.append_nil, List.mem_append] at hy
      rcases hy with hy | hy
      · rw [hT y (by simpa using hy)]; exact hcP
      · exact h13 y (List.mem_append_left _ hy)
    · exfalso
      have hz : z ∈ (L₁ ++ L₂).getLast? := by rw [h1]; simp
      rw [List.getLast?_append_of_ne_nil _ hL2] at hz
      have := h2 z (mem_of_getLast? hz)
      rw [hT z (by rw [h3]; simp)] at this
      exact hcP this
  · -- `A = L₁ ++ L₂ ++ c'`, `L₃ = c' ++ T`
    subst h1
    refine ⟨T ++ L₁, L₂, c', by simp, h2, fun y hy => ?_⟩
    simp only [List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · rw [hT y hy]; exact hcP
    · exact h13 y (List.mem_append_left _ hy)
    · exact h13 y (List.mem_append_right _ (by rw [h3]; exact List.mem_append_left _ hy))

end DZZ
end LQGMetric
