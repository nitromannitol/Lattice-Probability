/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Asym
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XGeo
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YSq

/-!
# DZZ Lemma 3.13, cell geometry I: half-open membership, neighbourhoods, chains in a box (P2-DZZ313G)

Ding–Zeitouni–Zhang arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1327–1336 (proof of Lemma 3.13).
Elementary tools for the construction of the box sequence:

* `idx_eq_of_bounds`, `boxAt_eq_of_ho`, `cellSide_eq_of_ho`: a point of the half-open box of a cell `𝖢`
  lies in `𝖢` (so `s_{z,δ} = s_𝖢`).
* `l313Near r b z`: `z` is within sup-distance `< r` of the closed box `b`; `l313Near_of_largeBox`: a point
  within `ρ` of `B_large` is `l313Near (ρ + s_B/2)`.
* `le_cellSide_of_goodPoint`: near a box inside the cell of a good point, cells have side `≥ ε s_𝖢`
  (DZZ l. 1329: "an arbitrary sequence of boxes in `𝒞_1`", controlled by the goodness of `u`).
* `exists_chain_of_rtg`, `exists_chain_in_box`: a loop-free `Neighbour`-chain of level-`N` squares of a box
  `C` joining two given squares, of length `≤ 4^{N - C.n}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma idx_eq_of_bounds {n i : ℕ} (hi : i < 2 ^ n) {x : ℝ} (h1 : i * (2 : ℝ)⁻¹ ^ n ≤ x)
    (h2 : x < (i + 1) * (2 : ℝ)⁻¹ ^ n) : idx n x = i := by
  have e := pow_inv_mul_pow n
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have a1 : (i : ℝ) ≤ x * 2 ^ n := by
    have := mul_le_mul_of_nonneg_right h1 hp.le
    rw [mul_assoc, e, mul_one] at this; exact this
  have a2 : x * 2 ^ n < i + 1 := by
    have := mul_lt_mul_of_pos_right h2 hp
    rw [mul_assoc, e, mul_one] at this; exact this
  have hf : ⌊x * 2 ^ n⌋₊ = i :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg i).trans a1)).2 ⟨a1, a2⟩
  unfold idx; rw [hf]; omega

/-- A point of the half-open box `[j s, (j+1) s) × [k s, (k+1) s)` has `boxAt` equal to the box. -/
lemma boxAt_eq_of_ho {C : DyBox} {z : ℂ} (h1 : C.j * C.side ≤ z.re) (h2 : z.re < (C.j + 1) * C.side)
    (h3 : C.k * C.side ≤ z.im) (h4 : z.im < (C.k + 1) * C.side) : boxAt C.n z = C :=
  DyBox.ext rfl (idx_eq_of_bounds C.hj h1 h2) (idx_eq_of_bounds C.hk h3 h4)

lemma cellSide_eq_of_ho {C : DyBox} (hC : IsCell m δ C) {z : ℂ} (hz : z ∈ dzzV)
    (h1 : C.j * C.side ≤ z.re) (h2 : z.re < (C.j + 1) * C.side)
    (h3 : C.k * C.side ≤ z.im) (h4 : z.im < (C.k + 1) * C.side) : cellSide m δ z = C.side :=
  cellSide_eq_of_isCell hC ⟨hz, boxAt_eq_of_ho h1 h2 h3 h4⟩

/-- `z` is within sup-distance `< r` of the closed box `b`. -/
def l313Near (r : ℝ) (b : DyBox) (z : ℂ) : Prop :=
  b.j * b.side - r < z.re ∧ z.re < (b.j + 1) * b.side + r ∧
    b.k * b.side - r < z.im ∧ z.im < (b.k + 1) * b.side + r

lemma l313Near_of_largeBox {b : DyBox} {x z : ℂ} (hx : x ∈ b.largeBox) {ρ : ℝ}
    (hd : dist z x < ρ) : l313Near (ρ + b.side / 2) b z := by
  obtain ⟨h1, h2⟩ := hx
  rw [dist_eq_norm] at hd
  have a1 : |z.re - x.re| < ρ := lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - x)) hd
  have a2 : |z.im - x.im| < ρ := lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (z - x)) hd
  simp only [DyBox.center] at h1 h2
  rw [abs_lt] at a1 a2; rw [abs_le] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The coordinate bounds of a box inside another. -/
lemma bounds_of_sub {b C : DyBox} (h : b.closedBox ⊆ C.closedBox) :
    C.j * C.side ≤ b.j * b.side ∧ (b.j + 1) * b.side ≤ (C.j + 1) * C.side ∧
      C.k * C.side ≤ b.k * b.side ∧ (b.k + 1) * b.side ≤ (C.k + 1) * C.side := by
  have hs := side_pos' b
  have c1 : (⟨b.j * b.side, b.k * b.side⟩ : ℂ) ∈ b.closedBox :=
    ⟨le_rfl, by simp only; nlinarith, le_rfl, by simp only; nlinarith⟩
  have c2 : (⟨(b.j + 1) * b.side, (b.k + 1) * b.side⟩ : ℂ) ∈ b.closedBox :=
    ⟨by simp only; nlinarith, le_rfl, by simp only; nlinarith, le_rfl⟩
  obtain ⟨p1, -, p3, -⟩ := h c1
  obtain ⟨-, q2, -, q4⟩ := h c2
  exact ⟨p1, q2, p3, q4⟩

/-- **Boxes in the cell of a good point** (DZZ l. 1329 with Definition 3.11): if `u` is good and
`u ∈ 𝖢_large`, every `z ∈ 𝕍` within `s_𝖢/2` of a box inside `𝖢` has `s_{z,δ} ≥ ε s_𝖢`. -/
lemma le_cellSide_of_goodPoint {ε : ℝ} {u : ℂ} (hu : IsGoodPoint m δ ε u) {C : DyBox}
    (hC : IsCell m δ C) (huC : u ∈ C.largeBox) {b : DyBox} (hb : b.closedBox ⊆ C.closedBox)
    {r : ℝ} (hr : r ≤ C.side / 2) {z : ℂ} (hz : z ∈ dzzV) (hn : l313Near r b z) :
    ε * C.side ≤ cellSide m δ z := by
  obtain ⟨e1, e2, e3, e4⟩ := bounds_of_sub hb
  obtain ⟨n1, n2, n3, n4⟩ := hn
  refine hu C hC huC z ⟨?_, ?_⟩ hz <;> simp only [DyBox.center] <;> rw [abs_lt] <;>
    constructor <;> linarith

/-! ### Loop-free chains of squares -/

lemma reachable_of_rtg {P : DyBox → Prop} {s t : DyBox} (hs : P s)
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) s t) :
    (SimpleGraph.fromRel fun a b => SqAdj a b ∧ P a ∧ P b).Reachable s t ∧ P t := by
  induction h with
  | refl => exact ⟨SimpleGraph.Reachable.refl _, hs⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih1.trans (SimpleGraph.Adj.reachable ?_), hbc.2⟩
    rw [SimpleGraph.fromRel_adj]
    refine ⟨fun e => ?_, Or.inl ⟨hbc.1, ih2, hbc.2⟩⟩
    subst e
    obtain ⟨-, h⟩ := hbc.1
    rcases h with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> omega

lemma mem_support_P {P : DyBox → Prop} {a b : DyBox} (ha : P a) :
    ∀ (p : (SimpleGraph.fromRel fun a b => SqAdj a b ∧ P a ∧ P b).Walk a b), ∀ x ∈ p.support, P x
  | .nil, x, hx => by simp at hx; rw [hx]; exact ha
  | .cons (v := c) h p, x, hx => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · rw [SimpleGraph.fromRel_adj] at h
      have hP : P c := by rcases h.2 with h | h; exacts [h.2.2, h.2.1]
      exact mem_support_P hP p x hx

/-- A loop-free `Neighbour`-chain from a `ReflTransGen` of 4-adjacent squares. -/
lemma exists_chain_of_rtg {P : DyBox → Prop} {s t : DyBox} (hs : P s)
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) s t) :
    ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s ∧ L.getLast hL = t ∧ L.IsChain Neighbour ∧
      L.Nodup ∧ ∀ b ∈ L, P b := by
  obtain ⟨⟨p₀⟩, -⟩ := reachable_of_rtg hs h
  set p := p₀.bypass
  refine ⟨p.support, by simp, SimpleGraph.Walk.head_support p, SimpleGraph.Walk.getLast_support p,
    (SimpleGraph.Walk.isChain_adj_support p).imp fun a b hab => ?_,
    (SimpleGraph.Walk.bypass_isPath p₀).support_nodup, mem_support_P hs p⟩
  rw [SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with h | h
  · exact neighbour_of_sqAdj h.1
  · exact (neighbour_of_sqAdj h.1).symm

/-- At most `4^{N - C.n}` distinct level-`N` squares lie in `C`. -/
lemma length_le_of_sub {C : DyBox} {N : ℕ} (hC : C.n ≤ N) (L : List DyBox) (hnd : L.Nodup)
    (hL : ∀ b ∈ L, b.n = N ∧ b.closedBox ⊆ C.closedBox) : L.length ≤ 4 ^ (N - C.n) := by
  classical
  set f : DyBox → ℕ × ℕ := fun b => (b.j - C.j * 2 ^ (N - C.n), b.k - C.k * 2 ^ (N - C.n))
  have hmap : ∀ b ∈ L.toFinset,
      f b ∈ Finset.range (2 ^ (N - C.n)) ×ˢ Finset.range (2 ^ (N - C.n)) := by
    intro b hb
    rw [List.mem_toFinset] at hb
    obtain ⟨hbn, hbC⟩ := hL b hb
    obtain ⟨c1, c2, c3, c4⟩ := int_of_sub_closedBox hbn hC hbC
    simp only [Finset.mem_product, Finset.mem_range, f]
    constructor <;> rw [add_mul, one_mul] at * <;> omega
  have hinj : Set.InjOn f L.toFinset := by
    intro b hb b' hb' e
    rw [Finset.mem_coe, List.mem_toFinset] at hb hb'
    obtain ⟨hbn, hbC⟩ := hL b hb
    obtain ⟨hbn', hbC'⟩ := hL b' hb'
    obtain ⟨c1, -, c3, -⟩ := int_of_sub_closedBox hbn hC hbC
    obtain ⟨d1, -, d3, -⟩ := int_of_sub_closedBox hbn' hC hbC'
    simp only [f, Prod.mk.injEq] at e
    exact DyBox.ext (hbn.trans hbn'.symm) (by omega) (by omega)
  have := Finset.card_le_card_of_injOn f hmap hinj
  rw [List.toFinset_card_of_nodup hnd, Finset.card_product, Finset.card_range] at this
  calc L.length ≤ 2 ^ (N - C.n) * 2 ^ (N - C.n) := this
    _ = 4 ^ (N - C.n) := by rw [← mul_pow]; norm_num

/-- **A loop-free chain of level-`N` squares inside `C`** joining two given squares, of length
`≤ 4^{N - C.n}`. -/
theorem exists_chain_in_box {C : DyBox} {N : ℕ} (hC : C.n ≤ N) {s t : DyBox} (hs : s.n = N)
    (ht : t.n = N) (hsC : s.closedBox ⊆ C.closedBox) (htC : t.closedBox ⊆ C.closedBox) :
    ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s ∧ L.getLast hL = t ∧ L.IsChain Neighbour ∧
      L.length ≤ 4 ^ (N - C.n) ∧ ∀ b ∈ L, b.n = N ∧ b.closedBox ⊆ C.closedBox := by
  obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := exists_chain_of_rtg (P := fun b => b.n = N ∧
    b.closedBox ⊆ C.closedBox) ⟨hs, hsC⟩ (path_in_box hC hs ht hsC htC)
  exact ⟨L, hL, h1, h2, h3, length_le_of_sub hC L h4 h5, h5⟩

end DZZ
end LQGMetric
