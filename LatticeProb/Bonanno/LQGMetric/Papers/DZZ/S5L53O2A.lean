/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53O2A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53O1A

/-!
# DZZ Lemma 5.3, node 3: the covering inequalities of the chain cells (P2-DZZ53O2)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1946–1952 (the boundary pieces
`Λ_{i-1}, Λ_i ⊆ ∂𝖢_i` are covered, up to `O(L²)` sub-box sides, by the boundary segments of the
good boundary sub-boxes) and l. 2510–2514. Open item (O2) of handoff P2-DZZ53J.

* `L53CoverIn C κ n N j Kt Λ S`: the hypotheses `hrange`, `hΛ ≠ ⊤`, `hPrev`/`hNext`, `hcovP`,
  `hcardP`, `hcovN` of `l53_box_desirable_prob` (S5L53GB4) for one interface `Λ` with segment set `S`
  (verbatim GB4 expressions; `b + a ≤ c` is GB4's internal `hac`, from `8 ≤ Kt`).
* **`l53_node3_cover_piece`**: for a grid-aligned side piece `Λ = l53SidePiece 𝖢 κ d p q`
  (O1A), `S = l53SidePrev d n N p q`, `80 ≤ Kt` and `20 (2(N-n) + 3 + 128 j) t < μH¹(Λ)`
  (`t = s_𝖢 2^{-κ}`).
* **`l53_node3_cover`**: on an `L313Q` sequence with `20 (2(N-n) + 3 + 128 j) 2^{-κ} < ε²`, both
  cells `l_i`, `l_{i+1}` satisfy `L53CoverIn` for `Λ_{i+1} = l53Iface l (i+1)` (O1A
  `l53_l313_iface_sidePiece`, NN1 `l53_l313_iface_ge_max`).

Own elementary arithmetic (the paper's "≥ ε*² s ≫ L² t" step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- The covering hypotheses of `l53_box_desirable_prob` (GB4) for the interface `Λ` of `𝖢` and the
segment set `S` (to be used as `(Prev, Λprev)` and as `(Next, Λnext)`). -/
def L53CoverIn (C : DyBox) (κ n N j : ℕ) (Kt : ℝ≥0∞) (Λ : Set ℂ)
    (S : Finset (PercDir × ℤ)) : Prop :=
  (∀ p ∈ S, (N : ℤ) - n < p.2 ∧ p.2 < N + n) ∧ μH[1] Λ ≠ ⊤ ∧
    (∀ p ∈ S, l53CellSeg C κ n N p ⊆ Λ) ∧
    0.2 * (μH[1] : Measure ℂ).real Λ + 4 * (7 + 1) * j * (4 * (2 : ℝ)⁻¹ ^ (C.n + κ))
      ≤ (μH[1] : Measure ℂ).real (⋃ p ∈ S, l53CellSeg C κ n N p) ∧
    (S.card : ℝ) * (Kt⁻¹ * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + κ)))).toReal ≤
      0.1 * (μH[1] : Measure ℂ).real Λ ∧
    (μH[1] : Measure ℂ).real (Λ \ ⋃ p ∈ S, l53CellSeg C κ n N p) +
      S.card * (Kt⁻¹ * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + κ)))).toReal +
        4 * (7 + 1) * j * (4 * (2 : ℝ)⁻¹ ^ (C.n + κ)) < 0.1 * (μH[1] : Measure ℂ).real Λ

/-- The length of a side piece. -/
lemma l53O2_sidePiece_measure (C : DyBox) (κ : ℕ) (d : PercDir) (u v : ℝ) :
    μH[1] (l53SidePiece C κ d u v) = ENNReal.ofReal ((v - u) * (2 : ℝ)⁻¹ ^ (C.n + κ)) := by
  cases d
  · exact l53_lineSeg_measure_h _ _ _ _ _
  · exact l53_botSeg_measure C κ u v
  · exact l53_lineSeg_measure_v _ _ _ _ _
  · exact l53_lineSeg_measure_v _ _ _ _ _

/-- `#l53SidePrev d n N p q ≤ q - p`. -/
lemma l53O2_card_sidePrev (d : PercDir) (n N : ℕ) {p q : ℤ} (hpq : p ≤ q) :
    ((l53SidePrev d n N p q).card : ℝ) ≤ ((q - p : ℤ) : ℝ) := by
  classical
  have h1 : (l53SidePrev d n N p q).card ≤ (Finset.Ico p q).card :=
    Finset.card_image_le.trans
      (Finset.card_le_card (Finset.Ico_subset_Ico (le_max_left _ _) (min_le_left _ _)))
  rw [Int.card_Ico] at h1
  have h2 : ((q - p).toNat : ℤ) = q - p := Int.toNat_of_nonneg (by omega)
  have h3 : ((l53SidePrev d n N p q).card : ℤ) ≤ q - p := by omega
  exact_mod_cast h3

/-- `(Kt⁻¹ · 4t).toReal ≤ t / 20` for `80 ≤ Kt`. -/
lemma l53O2_a_le {Kt : ℝ≥0∞} (hK80 : 80 ≤ Kt) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (Kt⁻¹ * (4 * ENNReal.ofReal t)).toReal ∧
      (Kt⁻¹ * (4 * ENNReal.ofReal t)).toReal ≤ t / 20 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h1 : Kt⁻¹ ≤ 80⁻¹ := ENNReal.inv_le_inv.2 hK80
  have h2 : Kt⁻¹ * (4 * ENNReal.ofReal t) ≤ 80⁻¹ * (4 * ENNReal.ofReal t) := by gcongr
  have h3 : (80⁻¹ * (4 * ENNReal.ofReal t) : ℝ≥0∞).toReal = t / 20 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ht]
    norm_num
    ring
  rw [← h3]
  exact ENNReal.toReal_mono (by finiteness) h2

/-- **(O2) for one grid-aligned side piece.** -/
theorem l53_node3_cover_piece (C : DyBox) {κ n N j : ℕ} (hK : 2 ^ κ = 2 * N + 2) (hnN : n ≤ N)
    {Kt : ℝ≥0∞} (hK80 : 80 ≤ Kt) (d : PercDir) {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ 2 * N + 2)
    (hlen : 20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) * (2 : ℝ)⁻¹ ^ (C.n + κ) <
      (μH[1] : Measure ℂ).real (l53SidePiece C κ d p q)) :
    L53CoverIn C κ n N j Kt (l53SidePiece C κ d p q) (l53SidePrev d n N p q) := by
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + κ) with ht
  have ht0 : 0 < t := by positivity
  set Λ := l53SidePiece C κ d p q with hΛ
  set S := l53SidePrev d n N p q with hS
  have hm := l53O2_sidePiece_measure C κ d p q
  have hlam : (μH[1] : Measure ℂ).real Λ = ((q : ℝ) - p) * t := by
    rw [Measure.real, hm, ENNReal.toReal_ofReal]
    exact mul_nonneg (by have : (p : ℝ) ≤ q := by exact_mod_cast hpq
                         linarith) ht0.le
  obtain ⟨h1, h2, h3⟩ := l53_cover_sidePiece C hK hnN d hp hpq hq
  rw [← hΛ, ← hS, ← ht] at h2 h3
  rw [← hΛ, ← hS] at h1
  have hcard : (S.card : ℝ) * t ≤ (μH[1] : Measure ℂ).real Λ := by
    rw [hlam]
    have := l53O2_card_sidePrev d n N hpq
    push_cast at this
    exact mul_le_mul_of_nonneg_right this ht0.le
  obtain ⟨ha0, ha⟩ := l53O2_a_le hK80 ht0.le
  set a := (Kt⁻¹ * (4 * ENNReal.ofReal t)).toReal with ha_def
  have hNn : (0 : ℝ) ≤ (N : ℝ) - n := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set X : ℝ := 2 * ((N : ℝ) - n) + 3 with hX
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hlen' : 20 * (X * t) + 20 * 128 * (j * t) < (μH[1] : Measure ℂ).real Λ := by
    have e : 20 * (X + 128 * j) * t = 20 * (X * t) + 20 * 128 * (j * t) := by ring
    rw [← e]; exact hlen
  have hjt : 0 ≤ (j : ℝ) * t := mul_nonneg hj ht0.le
  have hXt : 0 ≤ X * t := mul_nonneg hX0 ht0.le
  have hcardA : (S.card : ℝ) * a ≤ (μH[1] : Measure ℂ).real Λ / 20 := by
    calc (S.card : ℝ) * a ≤ S.card * (t / 20) :=
          mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
      _ = S.card * t / 20 := by ring
      _ ≤ _ := by linarith
  have e4 : 4 * (7 + 1) * (j : ℝ) * (4 * t) = 128 * (j * t) := by ring
  refine ⟨fun x hx => (h1 x hx).2, ?_, fun x hx => (h1 x hx).1, ?_, ?_, ?_⟩
  · rw [hΛ, hm]; exact ENNReal.ofReal_ne_top
  · rw [e4]; linarith
  · rw [← ht, ← ha_def]; linarith
  · rw [← ht, ← ha_def, e4]; linarith

section chain

variable {m : DyBox → ℝ} {δ ε : ℝ} {u v : ℂ} {l : List DyBox}

/-- **(O2) on an `L313Q` sequence**: if `20 (2(N-n) + 3 + 128 j) 2^{-κ} < ε²` and `80 ≤ Kt`, the
interface `Λ_{i+1} = l53Iface l (i+1)` satisfies GB4's covering hypotheses both as the `Next`
interface of `l_i` and as the `Prev` interface of `l_{i+1}`, with `S` a `l53SidePrev`. -/
theorem l53_node3_cover (hQ : L313Q ε u v (fun b => IsCell m δ b) l) {κ n N j : ℕ}
    (hK : 2 ^ κ = 2 * N + 2) (hnN : n ≤ N) {Kt : ℝ≥0∞} (hK80 : 80 ≤ Kt)
    (hpar : 20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) * (2 : ℝ)⁻¹ ^ κ < ε ^ 2)
    (i : ℕ) (hi : i + 1 < l.length) :
    (∃ S, L53CoverIn (l.getD i root) κ n N j Kt (l53Iface l (i + 1)) S) ∧
      (∃ S, L53CoverIn (l.getD (i + 1) root) κ n N j Kt (l53Iface l (i + 1)) S) := by
  have hNn : (0 : ℝ) ≤ (N : ℝ) - n := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hκ0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ κ := by positivity
  have hε : (2 : ℝ)⁻¹ ^ κ ≤ ε ^ 2 := by
    have h1 : (1 : ℝ) ≤ 20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hκ0.le
    linarith
  obtain ⟨⟨d, p, q, hp, hpq, hq, e⟩, ⟨d', p', q', hp', hpq', hq', e'⟩⟩ :=
    l53_l313_iface_sidePiece hQ hK hε i hi
  have hge := l53_l313_iface_ge_max hQ i hi
  have key : ∀ b : DyBox, b.side ≤ max (l.getD i root).side (l.getD (i + 1) root).side →
      20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) * (2 : ℝ)⁻¹ ^ (b.n + κ) <
        (μH[1] : Measure ℂ).real (l53Iface l (i + 1)) := by
    intro b hb
    have hs : (2 : ℝ)⁻¹ ^ (b.n + κ) = (2 : ℝ)⁻¹ ^ κ * b.side := by
      rw [pow_add, mul_comm]; rfl
    have hb0 := side_pos' b
    have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
    calc 20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) * (2 : ℝ)⁻¹ ^ (b.n + κ)
        = (20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) * (2 : ℝ)⁻¹ ^ κ) * b.side := by
          rw [hs]; ring
      _ < ε ^ 2 * b.side := mul_lt_mul_of_pos_right hpar hb0
      _ ≤ ε ^ 2 * max (l.getD i root).side (l.getD (i + 1) root).side :=
          mul_le_mul_of_nonneg_left hb hε2
      _ ≤ _ := hge
  refine ⟨⟨l53SidePrev d n N p q, ?_⟩, ⟨l53SidePrev d' n N p' q', ?_⟩⟩
  · rw [e]
    refine l53_node3_cover_piece _ hK hnN hK80 d hp hpq hq ?_
    rw [← e]; exact key _ (le_max_left _ _)
  · rw [e']
    refine l53_node3_cover_piece _ hK hnN hK80 d' hp' hpq' hq' ?_
    rw [← e']; exact key _ (le_max_right _ _)

end chain

end DZZ
end LQGMetric
