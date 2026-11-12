/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53NN1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GA1

/-!
# DZZ Lemma 5.3: consecutive Lemma 3.13 boxes are not nested; the interface bound (P2-DZZ53NN)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1719–1730 (the boxes of Lemma 3.13
have side `(ε*)² s_𝖢` inside a cell `𝖢` of `𝒱_δ`) and l. 2366–2379 (the chain of `𝓔*`);
DEC-131-IF §3, G-A1 corollary.

* `l53_eq_of_l313_subset`: two boxes `b, b'` with `b ⊆ C`, `s_b = s_C ε²`, `b' ⊆ C'`,
  `s_b' = s_C' ε²` for cells `C, C'` of `𝒱_δ` and `b̄ ⊆ b̄'` are equal. This is a copy of
  `eq_of_safe_subset` (S5L53L2) with the side relation `s_b = s_C ε²` (any real `ε`) in place of
  `n_b = n_C + 2k`.
* `l53_l313_nonnest`: the non-nesting of consecutive boxes of an `L313Q` sequence (both directions).
* `l53_l313_iface_ge_min`: `min(s_i, s_{i+1}) ≤ μH¹(Λ_{i+1})` (M1's `l53_iface_ge_min_of_nest`).
* `l53_l313_iface_ge_max`: `ε² max(s_i, s_{i+1}) ≤ μH¹(Λ_{i+1})` (with GA's `l53_side_ratio`).
* `l53_l313_iface_ge`: the requested form `ε² min(s_i, s_{i+1}) ≤ μH¹(Λ_{i+1})`.

No hypothesis on `ε` is needed. Own elementary proofs (copies of the cited declarations).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open DyBox WhiteNoise

variable {m : DyBox → ℝ} {δ : ℝ}

/-- Two Lemma 3.13 boxes (side `s_C ε²` inside a cell `C` of `𝒱_δ`) are never strictly nested
(copy of `eq_of_safe_subset`, S5L53L2). -/
lemma l53_eq_of_l313_subset {ε : ℝ} {b b' : DyBox}
    (hb : ∃ C : DyBox, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧ b.side = C.side * ε ^ 2)
    (hb' : ∃ C : DyBox, IsCell m δ C ∧ b'.closedBox ⊆ C.closedBox ∧ b'.side = C.side * ε ^ 2)
    (h : b.closedBox ⊆ b'.closedBox) : b = b' := by
  obtain ⟨C, hC, hbC, hbs⟩ := hb
  obtain ⟨C', hC', hbC', hbs'⟩ := hb'
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
  have hs' : b'.side = b.side := by rw [hbs, hbs']
  have hn : b.n = b'.n := by
    have : (2 : ℝ)⁻¹ ^ b.n = (2 : ℝ)⁻¹ ^ b'.n := hs'.symm
    exact pow_right_injective₀ (by norm_num) (by norm_num) this
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

section chain

variable {ε : ℝ} {u v : ℂ} {l : List DyBox}

lemma l53NN_getD_eq (l : List DyBox) {i : ℕ} (hi : i < l.length) : l.getD i root = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **Non-nesting of consecutive `L313Q` boxes** (both directions; in fact of any two boxes). -/
lemma l53_l313_nonnest (hQ : L313Q ε u v (fun b => IsCell m δ b) l) (i : ℕ)
    (hi : i + 1 < l.length) :
    ((l.getD i root).closedBox ⊆ (l.getD (i + 1) root).closedBox →
        l.getD i root = l.getD (i + 1) root) ∧
      ((l.getD (i + 1) root).closedBox ⊆ (l.getD i root).closedBox →
        l.getD (i + 1) root = l.getD i root) := by
  rw [l53NN_getD_eq l (by omega), l53NN_getD_eq l hi]
  have h1 := hQ.2.1 _ (List.getElem_mem (l := l) (n := i) (by omega))
  have h2 := hQ.2.1 _ (List.getElem_mem (l := l) (n := i + 1) hi)
  exact ⟨l53_eq_of_l313_subset h1 h2, l53_eq_of_l313_subset h2 h1⟩

/-- `μH¹(Λ_{i+1}) < ∞` and `min(s_i, s_{i+1}) ≤ μH¹(Λ_{i+1})` for an `L313Q` sequence. -/
lemma l53_l313_iface_ge_min (hQ : L313Q ε u v (fun b => IsCell m δ b) l) (i : ℕ)
    (hi : i + 1 < l.length) :
    μH[1] (l53Iface l (i + 1)) ≠ ⊤ ∧
      min (l.getD i root).side (l.getD (i + 1) root).side ≤
        (μH[1] : Measure ℂ).real (l53Iface l (i + 1)) := by
  obtain ⟨n1, n2⟩ := l53_l313_nonnest hQ i hi
  have hN : Neighbour (l.getD i root) (l.getD (i + 1) root) := by
    rw [l53NN_getD_eq l (by omega), l53NN_getD_eq l hi]
    exact hQ.1.2.getElem i hi
  have hfin := l53_iface_ne_top_of_nest hN.1 n1 n2
  have e : l53Iface l (i + 1) = (l.getD i root).closedBox ∩ (l.getD (i + 1) root).closedBox := by
    simp [l53Iface]
  rw [e]
  exact ⟨hfin, l53_iface_ge_min_of_nest n1 n2 hN hfin⟩

/-- `ε² ≤ 1` for a nonempty `L313Q` sequence (a box lies in its cell). -/
lemma l53_l313_eps_sq_le_one (hQ : L313Q ε u v (fun b => IsCell m δ b) l) {b : DyBox}
    (hb : b ∈ l) : ε ^ 2 ≤ 1 := by
  obtain ⟨C, -, hbC, hbs⟩ := hQ.2.1 b hb
  obtain ⟨a1, a2, -, -⟩ := corners_of_subset hbC
  have hC := side_pos' C
  have hle : b.side ≤ C.side := by nlinarith
  rw [hbs] at hle
  nlinarith

/-- `ε² max(s_i, s_{i+1}) ≤ μH¹(Λ_{i+1})` for an `L313Q` sequence. -/
lemma l53_l313_iface_ge_max (hQ : L313Q ε u v (fun b => IsCell m δ b) l) (i : ℕ)
    (hi : i + 1 < l.length) :
    ε ^ 2 * max (l.getD i root).side (l.getD (i + 1) root).side ≤
      (μH[1] : Measure ℂ).real (l53Iface l (i + 1)) := by
  obtain ⟨r1, r2⟩ := l53_side_ratio hQ i hi
  have he := l53_l313_eps_sq_le_one hQ (List.getElem_mem (l := l) (n := i) (by omega))
  have p1 := side_pos' (l.getD i root)
  have p2 := side_pos' (l.getD (i + 1) root)
  refine le_trans ?_ (l53_l313_iface_ge_min hQ i hi).2
  rw [mul_max_of_nonneg _ _ (sq_nonneg ε)]
  exact max_le (le_min (by nlinarith) r1) (le_min r2 (by nlinarith))

end chain

end DZZ
end LQGMetric
