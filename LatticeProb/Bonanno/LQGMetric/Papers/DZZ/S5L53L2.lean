/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53I5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G6

/-!
# DZZ Lemma 5.3, part 1: the chain of `𝓔*` is a chain of Lemma 3.13 boxes (P2-DZZ53L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2366–2379: the sequence `𝒞` of
`𝓔*_{δ,α*,u,v}` consists of dyadic boxes "not necessarily cells", namely (as in l. 1719–1730) the
boxes of Lemma 3.13 (side `(ε*)² s_𝖢̂`), for which the fine field is independent of `𝓕*`. Node 1
(S5L53F1–F4, I5) works with chains of *cells* of `𝒱_δ` (`L53CellChain`, `l53BadR`); for a cell `𝖢`,
the white noise in `(0, s_𝖢²) × 𝖡**` of a sub-box `𝖡` near `∂𝖢` is read by the masses of the
explored boxes of smaller neighbouring cells (not controlled by the goodness of the chain away
from `Λ_{i−1} ∪ Λ_i`), so (R3) fails for cell chains. This file states the bad event of nodes 2–4
for chains of Lemma 3.13 boxes (DZZ's own `𝒞`) and proves that it suffices:

* `L53BoxChain`: neighbouring boxes joining `u`, `v`, inside a cell meeting `R` at level `n_𝖢 + 2k`,
  explored boxes disjoint from the fine region (DZZ's three bullets), `d ≤ e^T` (`L53BoxQ`).
* `corners_of_subset`, `eq_of_safe_subset` (two Lemma 3.13 boxes are never strictly nested),
  `l53_iface_ne_top_of_nest` (a copy of `l53_iface_ne_top`, S5L53F3, with non-nesting in place of
  the cell property), `l53Iface_pos_box`, `l53_two_le_length_box`, **`l53_mem_desirableB`**.
* `l53BadBox`, **`l53_hdes_of_D1Box`** (copy of `l53_hdes_of_D1R`, S5L53I5): `hdes` from the cell
  event `𝒟₁` (threshold `T₁c`) and the box bad event (box chain threshold `T₁`).

Own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox WhiteNoise

lemma corners_of_subset {b c : DyBox} (h : b.closedBox ⊆ c.closedBox) :
    (c.j : ℝ) * c.side ≤ b.j * b.side ∧ ((b.j : ℝ) + 1) * b.side ≤ (c.j + 1) * c.side ∧
      (c.k : ℝ) * c.side ≤ b.k * b.side ∧ ((b.k : ℝ) + 1) * b.side ≤ (c.k + 1) * c.side := by
  have hs := side_pos' b
  have hlo : (⟨b.j * b.side, b.k * b.side⟩ : ℂ) ∈ c.closedBox := h ⟨le_rfl, by
    show (b.j : ℝ) * b.side ≤ (b.j + 1) * b.side; nlinarith, le_rfl, by
    show (b.k : ℝ) * b.side ≤ (b.k + 1) * b.side; nlinarith⟩
  have hhi : (⟨(b.j + 1) * b.side, (b.k + 1) * b.side⟩ : ℂ) ∈ c.closedBox := h ⟨by
    show (b.j : ℝ) * b.side ≤ (b.j + 1) * b.side; nlinarith, le_rfl, by
    show (b.k : ℝ) * b.side ≤ (b.k + 1) * b.side; nlinarith, le_rfl⟩
  exact ⟨hlo.1, hhi.2.1, hlo.2.2.1, hhi.2.2.2⟩

variable {m : DyBox → ℝ} {δ : ℝ}

/-- Two Lemma 3.13 boxes are never strictly nested. -/
lemma eq_of_safe_subset {k : ℕ} {b b' : DyBox}
    (hb : ∃ C : DyBox, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧ b.n = C.n + 2 * k)
    (hb' : ∃ C : DyBox, IsCell m δ C ∧ b'.closedBox ⊆ C.closedBox ∧ b'.n = C.n + 2 * k)
    (h : b.closedBox ⊆ b'.closedBox) : b = b' := by
  obtain ⟨C, hC, hbC, hbn⟩ := hb
  obtain ⟨C', hC', hbC', hbn'⟩ := hb'
  obtain ⟨a1, a2, a3, a4⟩ := corners_of_subset hbC
  obtain ⟨c1, c2, c3, c4⟩ := corners_of_subset (h.trans hbC')
  have hs := side_pos' b
  have hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side := by nlinarith
  have hj2 : (C'.j : ℝ) * C'.side < (C.j + 1) * C.side := by nlinarith
  have hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side := by nlinarith
  have hk2 : (C'.k : ℝ) * C'.side < (C.k + 1) * C.side := by nlinarith
  have hCC : C = C' := by
    rcases le_total C'.n C.n with hle | hle
    · have u := dy_nested_real (n := C.n) (n' := C'.n) hle hj1 hj2
      have v := dy_nested_real (n := C.n) (n' := C'.n) hle hk1 hk2
      have hsub : C.closedBox ⊆ C'.closedBox := by
        rintro q ⟨q1, q2, q3, q4⟩
        exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
      exact eq_of_sub_cell hC hC' le_rfl hle hsub
    · have u := dy_nested_real (n := C'.n) (n' := C.n) hle hj2 hj1
      have v := dy_nested_real (n := C'.n) (n' := C.n) hle hk2 hk1
      have hsub : C'.closedBox ⊆ C.closedBox := by
        rintro q ⟨q1, q2, q3, q4⟩
        exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
      exact (eq_of_sub_cell hC' hC le_rfl hle hsub).symm
  subst hCC
  have hn : b.n = b'.n := by omega
  have hs' : b'.side = b.side := by unfold DyBox.side; rw [hn]
  obtain ⟨e1, e2, e3, e4⟩ := corners_of_subset h
  rw [hs'] at e1 e2 e3 e4
  have f1 := le_of_mul_le_mul_right e1 hs
  have f2 := le_of_mul_le_mul_right e2 hs
  have f3 := le_of_mul_le_mul_right e3 hs
  have f4 := le_of_mul_le_mul_right e4 hs
  have hj : b.j = b'.j := by
    have : (b.j : ℝ) = b'.j := le_antisymm (by linarith) f1
    exact_mod_cast this
  have hk : b.k = b'.k := by
    have : (b.k : ℝ) = b'.k := le_antisymm (by linarith) f3
    exact_mod_cast this
  exact DyBox.ext hn hj hk

/-- **`μH¹(B̄ ∩ B̄') < ∞`** for two distinct, non-nested boxes (copy of `l53_iface_ne_top`, S5L53F3,
whose cell hypotheses enter only through non-nesting). -/
lemma l53_iface_ne_top_of_nest {C C' : DyBox} (hne : C ≠ C')
    (hn1 : C.closedBox ⊆ C'.closedBox → C = C') (hn2 : C'.closedBox ⊆ C.closedBox → C' = C) :
    μH[1] (C.closedBox ∩ C'.closedBox) ≠ ⊤ := by
  have hs : 0 < C.side := by unfold DyBox.side; positivity
  have hs' : 0 < C'.side := by unfold DyBox.side; positivity
  by_cases hj2 : (C'.j : ℝ) * C'.side < (C.j + 1) * C.side
  · by_cases hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side
    · by_cases hk2 : (C'.k : ℝ) * C'.side < (C.k + 1) * C.side
      · by_cases hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side
        · exfalso
          rcases le_total C'.n C.n with hle | hle
          · have u := dy_nested_real (n := C.n) (n' := C'.n) hle hj1 hj2
            have v := dy_nested_real (n := C.n) (n' := C'.n) hle hk1 hk2
            have hsub : C.closedBox ⊆ C'.closedBox := by
              rintro q ⟨q1, q2, q3, q4⟩
              exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
            exact hne (hn1 hsub)
          · have u := dy_nested_real (n := C'.n) (n' := C.n) hle hj2 hj1
            have v := dy_nested_real (n := C'.n) (n' := C.n) hle hk2 hk1
            have hsub : C'.closedBox ⊆ C.closedBox := by
              rintro q ⟨q1, q2, q3, q4⟩
              exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
            exact hne (hn2 hsub).symm
        · refine ne_top_of_le_ne_top (l53_hline_ne_top (C.k * C.side) (C.j * C.side)
            ((C.j + 1) * C.side)) (measure_mono ?_)
          rintro z ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
          push Not at hk1
          exact ⟨le_antisymm (b4.trans hk1) a3, a1, a2⟩
      · refine ne_top_of_le_ne_top (l53_hline_ne_top ((C.k + 1) * C.side) (C.j * C.side)
          ((C.j + 1) * C.side)) (measure_mono ?_)
        rintro z ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
        push Not at hk2
        exact ⟨le_antisymm a4 (hk2.trans b3), a1, a2⟩
    · refine ne_top_of_le_ne_top (l53_vline_ne_top (C.j * C.side) (C.k * C.side)
        ((C.k + 1) * C.side)) (measure_mono ?_)
      rintro z ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
      push Not at hj1
      exact ⟨le_antisymm (b2.trans hj1) a1, a3, a4⟩
  · refine ne_top_of_le_ne_top (l53_vline_ne_top ((C.j + 1) * C.side) (C.k * C.side)
      ((C.k + 1) * C.side)) (measure_mono ?_)
    rintro z ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
    push Not at hj2
    exact ⟨le_antisymm a2 (hj2.trans b1), a3, a4⟩

/-- The interfaces of a chain of Lemma 3.13 boxes: `0 < μH¹(Λ_i) < ∞`. -/
lemma l53Iface_pos_box {k : ℕ} {c : List DyBox}
    (hsafe : ∀ b ∈ c, ∃ C : DyBox, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧ b.n = C.n + 2 * k)
    (hg : c.IsChain Neighbour) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ c.length - 1) :
    μH[1] (l53Iface c i) ≠ ⊤ ∧ 0 < (μH[1] : Measure ℂ).real (l53Iface c i) := by
  have hlt : i - 1 + 1 < c.length := by omega
  have hN := List.isChain_iff_getElem.1 hg (i - 1) hlt
  have e1 : c.getD (i - 1) DyBox.root = c[i - 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have e2 : c.getD i DyBox.root = c[i - 1 + 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1; omega
  unfold l53Iface
  rw [e1, e2]
  have h1 := hsafe _ (List.getElem_mem (l := c) (n := i - 1) (by omega))
  have h2 := hsafe _ (List.getElem_mem (l := c) (n := i - 1 + 1) hlt)
  have hfin := l53_iface_ne_top_of_nest hN.1 (eq_of_safe_subset h1 h2) (eq_of_safe_subset h2 h1)
  exact ⟨hfin, l53_iface_pos hN hfin⟩

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- On `cellSizeEvent`, a chain of Lemma 3.13 boxes joining `u`, `v` with `2δ^{C_Mc} < |u − v|` has
`d ≥ 2` (copy of `l53_two_le_length`, S5L53F4). -/
lemma l53_two_le_length_box {γ : ℝ} {W : WNSpace → Ω → ℝ} {ω : Ω} {u v : ℂ} {k : ℕ}
    {c : List DyBox} (hsize : ω ∈ cellSizeEvent γ W δ)
    (hj : ∃ hL : c ≠ [], (c.head hL).Mem u ∧ (c.getLast hL).Mem v)
    (hsafe : ∀ b ∈ c, ∃ C : DyBox, IsCell (approxLQG γ W ω) δ C ∧ b.closedBox ⊆ C.closedBox ∧
      b.n = C.n + 2 * k)
    (hsep : 2 * δ ^ dzzCMc γ < ‖u - v‖) : 2 ≤ c.length := by
  obtain ⟨hne, hu, hv⟩ := hj
  by_contra hlt
  have h1 : c.length = 1 := by
    have := List.length_pos_of_ne_nil hne; omega
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 h1
  simp only [List.head_cons, List.getLast_singleton] at hu hv
  obtain ⟨C, hC, hbC, -⟩ := hsafe b List.mem_cons_self
  have hCs := (hsize.2 C hC).2
  obtain ⟨c1, c2, -, -⟩ := corners_of_subset hbC
  have hbs : b.side ≤ C.side := by nlinarith
  have hb := hbs.trans hCs
  obtain ⟨a1, a2, a3, a4⟩ := mem_closedBox_of_mem hu
  obtain ⟨b1, b2, b3, b4⟩ := mem_closedBox_of_mem hv
  have hre : |(u - v).re| ≤ b.side := by
    rw [Complex.sub_re, abs_le]; constructor <;> nlinarith
  have him : |(u - v).im| ≤ b.side := by
    rw [Complex.sub_im, abs_le]; constructor <;> nlinarith
  have := Complex.norm_le_abs_re_add_abs_im (u - v)
  linarith

end DZZ
end LQGMetric
