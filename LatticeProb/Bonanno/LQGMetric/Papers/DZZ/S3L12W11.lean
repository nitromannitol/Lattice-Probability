/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W10

/-!
# DZZ Lemma 3.12: from a ring of fine boxes to the cell ring (D93/D99, packet P-6b)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Remark 3.15 (l. 1360–1363) and
(eq-percolation-good-surrounding) (l. 1433–1435), in the ring form of D93: a closed walk of
good boxes of `𝓑(𝖢, ε)` enclosing `𝖢`, in which the boxes of each parent cell form one block,
gives, mapped to their cells (`cellOf`) with consecutive repeats removed, the cell ring of
`CellRingOfCrossRing`.

* `dd`: removal of consecutive repeats, and its API;
* `cellOf_eq_of_sub` (DEC P-5), `FineGood`, `cellOf_spec_fine`, `isChain_map_cellOf'`;
* `FineRing`: the ring of fine boxes (output of packet P-6a);
* **`ring_of_fineRing`**, **`cellRingOfCrossRing_of_fine`**: `CellRingOfCrossRing` from
  `FineRingOfCross` (the remaining open node, P-6a).

Own elementary arguments (DEC-93 §2), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- Removal of consecutive repeats. -/
def dd : List DyBox → List DyBox
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then dd (b :: t) else a :: dd (b :: t)

lemma dd_head : ∀ (a : DyBox) (t : List DyBox), (dd (a :: t)).head? = some a
  | a, [] => rfl
  | a, b :: t => by
    simp only [dd]
    split_ifs with h
    · rw [dd_head b t, h]
    · rfl

lemma dd_ne_nil (a : DyBox) (t : List DyBox) : dd (a :: t) ≠ [] := by
  intro h; have := dd_head a t; rw [h] at this; simp at this

lemma dd_cons (a : DyBox) (t : List DyBox) : dd (a :: t) = dd t ∨ dd (a :: t) = a :: dd t := by
  rcases t with _ | ⟨b, t⟩
  · right; rfl
  · simp only [dd]; split_ifs <;> simp

lemma dd_getLast : ∀ l : List DyBox, (dd l).getLast? = l.getLast?
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => by
    have ih := dd_getLast (b :: t)
    simp only [dd]
    split_ifs
    · rw [ih]; simp
    · obtain ⟨x, s, hxs⟩ := List.exists_cons_of_ne_nil (dd_ne_nil b t)
      rw [hxs] at ih ⊢
      rw [List.getLast?_cons_cons, ih, List.getLast?_cons_cons]

lemma mem_dd : ∀ (l : List DyBox) (c : DyBox), c ∈ dd l ↔ c ∈ l
  | [] => by simp [dd]
  | [a] => by simp [dd]
  | a :: b :: t => by
    intro c
    have ih := mem_dd (b :: t) c
    simp only [dd]
    split_ifs with h
    · rw [ih]; subst h; simp
    · simp only [List.mem_cons] at ih ⊢; tauto

lemma isChain_dd : ∀ l : List DyBox, l.IsChain (fun c c' => c = c' ∨ Neighbour c c') →
    (dd l).IsChain Neighbour
  | [] => fun _ => by simp [dd]
  | [a] => fun _ => by simp [dd]
  | a :: b :: t => fun h => by
    rw [List.isChain_cons_cons] at h
    have ih := isChain_dd (b :: t) h.2
    simp only [dd]
    split_ifs with hab
    · exact ih
    · rw [List.isChain_cons]
      refine ⟨fun y hy => ?_, ih⟩
      rw [dd_head] at hy
      cases hy
      exact h.1.resolve_left hab

lemma count_dd_le {P : DyBox} :
    ∀ (L₁ L₂ L₃ : List DyBox), P ∉ L₁ → P ∉ L₃ → (∀ b ∈ L₂, b = P) →
      (dd (L₁ ++ L₂ ++ L₃)).count P ≤ 1
  | a :: L₁, L₂, L₃, h1, h3, h2 => by
    have ih := count_dd_le L₁ L₂ L₃ (fun h => h1 (List.mem_cons_of_mem _ h)) h3 h2
    have haP : a ≠ P := fun e => h1 (e ▸ List.mem_cons_self)
    rcases dd_cons a (L₁ ++ L₂ ++ L₃) with e | e <;>
      simp only [List.cons_append] at e ⊢ <;> rw [e]
    · exact ih
    · rw [List.count_cons]; simp only [beq_iff_eq, haP, if_false]; simpa using ih
  | [], [], L₃, _, h3, _ => by
    simp only [List.nil_append]
    rw [List.count_eq_zero.2 (fun h => h3 ((mem_dd L₃ P).1 h))]; omega
  | [], [b], L₃, _, h3, h2 => by
    simp only [List.nil_append, List.singleton_append]
    rcases dd_cons b L₃ with e | e <;> rw [e]
    · rw [List.count_eq_zero.2 (fun h => h3 ((mem_dd L₃ P).1 h))]; omega
    · rw [List.count_cons, List.count_eq_zero.2 (fun h => h3 ((mem_dd L₃ P).1 h))]; split_ifs <;> omega
  | [], b :: c :: L₂, L₃, h1, h3, h2 => by
    have hb := h2 b List.mem_cons_self
    have hc := h2 c (by simp)
    have ih := count_dd_le [] (c :: L₂) L₃ h1 h3 (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
    simp only [List.nil_append, List.cons_append] at ih ⊢
    simp only [dd, if_pos (hb.trans hc.symm)]
    exact ih

/-- A box inside a cell has that cell as `cellOf` (DEC-93 P-5 `cellOf_eq_of_sub`). -/
lemma cellOf_eq_of_sub {b P : DyBox} (hP : IsCell m δ P) (hn : P.n ≤ b.n)
    (hs : b.closedBox ⊆ P.closedBox) : cellOf m δ b = P := by
  have h : ∃ i, i ≤ b.n ∧ IsCell m δ (b.anc i) :=
    ⟨P.n, hn, by rw [anc_eq_of_sub rfl hn hs]; exact hP⟩
  unfold cellOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hi, hc⟩ := h.choose_spec
  have hle : (b.anc h.choose).n ≤ b.n := by show min _ _ ≤ _; omega
  exact cell_eq_of_sub hc hP hle hn (closedBox_sub_anc b _) hs

/-- The boxes of a fine ring: of mass `< δ²`, or inside a parent cell. -/
def FineGood (m : DyBox → ℝ) (δ : ℝ) (C b : DyBox) : Prop :=
  m b < δ ^ 2 ∨ ∃ P, IsParent m δ C P ∧ b.closedBox ⊆ P.closedBox

lemma cellOf_spec_fine {C b : DyBox} {K : ℕ} (hb : b ∈ boxColl C K) (h : FineGood m δ C b) :
    IsCell m δ (cellOf m δ b) ∧ b.closedBox ⊆ (cellOf m δ b).closedBox ∧
      b.side ≤ (cellOf m δ b).side := by
  rcases h with h | ⟨P, hP, hs⟩
  · exact cellOf_spec h
  · have hlt := n_lt_of_side_lt hP.2.1
    have hn : P.n ≤ b.n := by rw [hb.1]; omega
    rw [cellOf_eq_of_sub hP.1 hn hs]
    refine ⟨hP.1, hs, ?_⟩
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn

lemma isChain_map_cellOf' {l : List DyBox} (hl : l.IsChain Neighbour)
    (hm : ∀ b ∈ l, b.closedBox ⊆ (cellOf m δ b).closedBox) :
    (l.map (cellOf m δ)).IsChain (fun c c' => c = c' ∨ Neighbour c c') := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      rw [List.isChain_cons_cons] at hl
      simp only [List.map_cons, List.isChain_cons_cons]
      refine ⟨?_, by simpa using ih hl.2 (fun x hx => hm x (List.mem_cons_of_mem _ hx))⟩
      by_cases he : cellOf m δ a = cellOf m δ b
      · exact Or.inl he
      · exact Or.inr ⟨he, fun hsub => hl.1.2 (hsub.anti (inter_subset_inter (hm a (by simp))
          (hm b (by simp))))⟩

/-- **A ring of fine boxes** around `𝖢` (output of DEC-93 packet P-6a): a cyclic `Neighbour`-list
of boxes of `𝓑(𝖢, 2^{-K})` in `𝖢_large \ 𝖢°`, each good or inside a parent cell,, enclosing `𝖢`, whose first and last boxes lie
in different cells, and in which the boxes of each parent form one block. -/
def FineRing (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (K : ℕ) (L : List DyBox) : Prop :=
  L ≠ [] ∧ CycChain L ∧
    (∀ b ∈ L, b ∈ boxColl C K ∧ Disjoint (interior b.closedBox) C.closedBox ∧ FineGood m δ C b) ∧
    EnclosesBox C {b | b ∈ L} ∧
    (∀ a ∈ L.head?, ∀ b ∈ L.getLast?, cellOf m δ a ≠ cellOf m δ b) ∧
    ∀ P, IsParent m δ C P → ∃ L₁ L₂ L₃ : List DyBox, L = L₁ ++ L₂ ++ L₃ ∧
      (∀ b ∈ L₂, cellOf m δ b = P) ∧ ∀ b ∈ L₁ ++ L₃, cellOf m δ b ≠ P

/-- **The cell ring from a ring of fine boxes** (Remark 3.15 in ring form). -/
theorem ring_of_fineRing {C : DyBox} {K : ℕ} {L : List DyBox} (h : FineRing m δ C K L) :
    ∃ Z : List DyBox, ∃ hne : Z ≠ [],
      Z.IsChain Neighbour ∧ Neighbour (Z.getLast hne) (Z.head hne) ∧
      (∀ c ∈ Z, IsCell m δ c ∧ (2 : ℝ)⁻¹ ^ K * C.side ≤ c.side ∧
        (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty) ∧
      EnclosesBox C {c | c ∈ Z} ∧ ∀ p ∈ Z, C.side < p.side → Z.count p = 1 := by
  obtain ⟨hne, ⟨hch, hcyc⟩, hall, henc, hends, hpar⟩ := h
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  set Z := dd ((a :: t).map (cellOf m δ)) with hZ
  have hZne : Z ≠ [] := by simp only [Z, List.map_cons]; exact dd_ne_nil _ _
  have hmem : ∀ c, c ∈ Z ↔ ∃ b ∈ a :: t, cellOf m δ b = c := fun c => by
    rw [hZ, mem_dd, List.mem_map]
  have hcell : ∀ c ∈ Z, IsCell m δ c ∧ (2 : ℝ)⁻¹ ^ K * C.side ≤ c.side ∧
      (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := (hmem c).1 hc
    obtain ⟨⟨hbn, hbsub⟩, hdisj, hmb⟩ := hall b hb
    obtain ⟨hcell, hsub, hside⟩ := cellOf_spec_fine (hall b hb).1 hmb
    refine ⟨hcell, ?_, b.center, hsub (center_mem_closedBox b),
      hbsub (center_mem_closedBox b), fun hC => ?_⟩
    · refine le_trans (le_of_eq ?_) hside
      simp only [DyBox.side, hbn, pow_add]; ring
    · exact disjoint_left.mp hdisj (center_mem_interior_closedBox b) hC
  refine ⟨Z, hZne, isChain_dd _ (isChain_map_cellOf' hch fun b hb => (cellOf_spec_fine (hall b hb).1 (hall b hb).2.2).2.1), ?_, hcell,
    ?_, ?_⟩
  · -- the closing edge
    set b := (a :: t).getLast (List.cons_ne_nil a t)
    have hb : b ∈ a :: t := List.getLast_mem _
    have hl : Z.getLast hZne = cellOf m δ b := by
      have e := dd_getLast ((a :: t).map (cellOf m δ))
      rw [← hZ, List.getLast?_eq_some_getLast hZne, List.getLast?_map,
        List.getLast?_eq_some_getLast (List.cons_ne_nil a t)] at e
      simpa using e
    have hh : Z.head hZne = cellOf m δ a := by
      have e := dd_head (cellOf m δ a) (t.map (cellOf m δ))
      simp only [List.map_cons] at hZ
      rw [← hZ, List.head?_eq_some_head hZne] at e
      simpa using e
    rw [hl, hh]
    have hn : Neighbour b a := hcyc b (by simp [b, List.getLast?_eq_some_getLast]) a (by simp)
    have hne' : cellOf m δ a ≠ cellOf m δ b :=
      hends a (by simp) b (by simp [b, List.getLast?_eq_some_getLast])
    refine ⟨fun e => hne' e.symm, fun hsub => hn.2 (hsub.anti ?_)⟩
    exact inter_subset_inter (cellOf_spec_fine (hall b hb).1 (hall b hb).2.2).2.1
      (cellOf_spec_fine (hall a (by simp)).1 (hall a (by simp)).2.2).2.1
  · intro p hp h0 h1
    obtain ⟨s, b, hb, hs⟩ := henc p hp h0 h1
    exact ⟨s, cellOf m δ b, (hmem _).2 ⟨b, hb, rfl⟩,
      (cellOf_spec_fine (hall b hb).1 (hall b hb).2.2).2.1 hs⟩
  · intro p hp hs
    have hpc := hcell p hp
    obtain ⟨L₁, L₂, L₃, hL, h2, h13⟩ := hpar p ⟨hpc.1, hs,
      hpc.2.2.mono (inter_subset_inter_right _ sdiff_subset)⟩
    have hle : Z.count p ≤ 1 := by
      rw [hZ, hL, List.map_append, List.map_append]
      refine count_dd_le _ _ _ ?_ ?_ ?_
      · intro hm; obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
        exact h13 b (List.mem_append_left _ hb) e
      · intro hm; obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
        exact h13 b (List.mem_append_right _ hb) e
      · intro c hc; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc; exact h2 b hb
    have := List.count_pos_iff.2 hp
    omega

/-- **DEC-93 packet P-6a** (open node): the ring of fine boxes from the crossings. -/
def FineRingOfCross : Prop :=
  ∀ (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (K : ℕ), IsCell m δ C → 1 ≤ C.n →
    HasCrossRing C K (fun b' => m b' < δ ^ 2) → C.largeBox ⊆ interior dzzV →
    ∃ L, FineRing m δ C K L

theorem cellRingOfCrossRing_of_fine (h : FineRingOfCross) : CellRingOfCrossRing :=
  fun m δ C K hC h1 hc hint => by
    obtain ⟨L, hL⟩ := h m δ C K hC h1 hc hint
    exact ring_of_fineRing hL

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  {W : WhiteNoise.WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.12** from packet P-6a. -/
theorem dzz_lemma312_of_fineRing (hW : WhiteNoise.IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hR : FineRingOfCross) : DZZLemma312 P γ W :=
  dzz_lemma312_of_cellRingRing hW hγ hγ2 (cellRingOfCrossRing_of_fine hR)

end DZZ
end LQGMetric
