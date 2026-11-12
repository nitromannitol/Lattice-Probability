/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X2

/-!
# DZZ Lemma 3.12: the fine ring from a coarse ring (D93/D99, packet P-6a, refinement step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 3.16 (l. 1381–1397: the
boundary boxes of the open boxes of the coarse enclosure enclose at the fine scale) and the proof
of Lemma 3.12 (l. 1461–1477), in the ring form of D93/D99.

* `CoarseRing`: a cyclic `Neighbour`-list of boxes of `𝓑(𝖢, 2^{-k})` in `𝖢_large \ 𝖢°`, each
  with all boundary boxes of depth `d` good or inside a parent cell, enclosing `𝖢`, in which the
  boxes inside each parent cell form one block;
* **`fineRing_of_coarse`**: the boundary rings of a coarse ring, walked in order (S3L12X1) and
  rotated at a change of cell (S3L12X2), form a `FineRing`;
* `enclosesBox_of_hasCross`: separation of any box set containing the four crossings;
* `CoarseRingOfCross` (open, the gluing of the four crossings and the zone merges of D93 §2),
  **`fineRingOfCross_of_coarse`**, **`dzz_lemma312_of_coarseRing`**.

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

/-- **A coarse ring of boxes** around `𝖢` at scale `2^{-k}`, refinable at depth `d`. -/
def CoarseRing (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (k d : ℕ) (l : List DyBox) : Prop :=
  l ≠ [] ∧ CycChain l ∧
    (∀ b ∈ l, b ∈ boxColl C k ∧ Disjoint (interior b.closedBox) C.closedBox ∧
      ((∀ bt ∈ boxCollBdry b d, m bt < δ ^ 2) ∨
        ∃ P, IsParent m δ C P ∧ b.closedBox ⊆ P.closedBox)) ∧
    EnclosesBox C {b | b ∈ l} ∧
    ∀ P, IsParent m δ C P → ∃ L₁ L₂ L₃ : List DyBox, l = L₁ ++ L₂ ++ L₃ ∧
      (∀ b ∈ L₂, b.closedBox ⊆ P.closedBox) ∧ ∀ b ∈ L₁ ++ L₃, ¬ b.closedBox ⊆ P.closedBox

/-- A ring box of a coarse box inside a parent cell has that cell as `cellOf`, and conversely. -/
lemma cellOf_ring_iff {C P b y : DyBox} {k d : ℕ} (hb : b ∈ boxColl C k) (hP : IsParent m δ C P)
    (hy : IsRingOf d b y) (hg : FineGood m δ C y) :
    cellOf m δ y = P ↔ b.closedBox ⊆ P.closedBox := by
  have hlt := n_lt_of_side_lt hP.2.1
  have hyb := closedBox_sub_of_ring hy
  have hPb : P.n ≤ b.n := by rw [hb.1]; omega
  have hby : b.n ≤ y.n := by rw [hy.1]; omega
  constructor
  · intro e
    have hyP : y.closedBox ⊆ P.closedBox := by
      have := (cellOf_spec_fine (K := k + d) ⟨by rw [hy.1, hb.1, Nat.add_assoc], hyb.trans hb.2⟩
        hg).2.1
      rwa [e] at this
    have e1 : y.anc b.n = b := anc_eq_of_sub rfl hby hyb
    have e2 : y.anc P.n = P := anc_eq_of_sub rfl (hPb.trans hby) hyP
    have e3 : b.anc P.n = P := by rw [← e1, anc_anc y hPb, e2]
    rw [← e3]; exact closedBox_sub_anc b P.n
  · intro hs
    exact cellOf_eq_of_sub hP.1 (hPb.trans hby) (hyb.trans hs)

/-- **The fine ring from a coarse ring.** -/
theorem fineRing_of_coarse {C : DyBox} {k d : ℕ} {l : List DyBox} (hC : IsCell m δ C)
    (hint : C.largeBox ⊆ interior dzzV) (hl : CoarseRing m δ C k d l) :
    ∃ L, FineRing m δ C (k + d) L := by
  obtain ⟨hne, ⟨hch, hcyc⟩, hall, henc, hblk⟩ := hl
  obtain ⟨b₀, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  set bL := (b₀ :: t).getLast (List.cons_ne_nil _ _) with hbL
  have hlev : ∀ c ∈ b₀ :: t, c.n = b₀.n := fun c hc => by
    rw [(hall c hc).1.1, (hall b₀ List.mem_cons_self).1.1]
  obtain ⟨x, e, hx, he, hxe⟩ := ring_edge (d := d) (b := bL) (b' := b₀)
    ((hlev bL (List.getLast_mem _)).symm)
    (hcyc bL (by simp [bL, List.getLast?_eq_some_getLast]) b₀ (by simp))
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := exists_ring_segs d t b₀ e x hch hlev he hx
  set F := (P.map Prod.snd).flatten with hFdef
  have hmemF : ∀ y ∈ F, ∃ b ∈ b₀ :: t, IsRingOf d b y := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := List.mem_flatten.1 hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    exact ⟨p.1, by rw [← h1]; exact List.mem_map_of_mem hp, (h2 p hp y).1 hys⟩
  have hcovF : ∀ b ∈ b₀ :: t, ∀ y, IsRingOf d b y → y ∈ F := by
    intro b hb y hy
    rw [← h1] at hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    exact List.mem_flatten.2 ⟨p.2, List.mem_map_of_mem hp, (h2 p hp y).2 hy⟩
  have hgood : ∀ b ∈ b₀ :: t, ∀ y, IsRingOf d b y →
      y ∈ boxColl C (k + d) ∧ Disjoint (interior y.closedBox) C.closedBox ∧ FineGood m δ C y := by
    intro b hb y hr
    have hsub := closedBox_sub_of_ring hr
    obtain ⟨hbc, hdis, hg⟩ := hall b hb
    refine ⟨⟨by rw [hr.1, hbc.1, Nat.add_assoc], hsub.trans hbc.2⟩,
      Disjoint.mono_left (interior_mono hsub) hdis, ?_⟩
    rcases hg with hg | ⟨Q, hQ, hbQ⟩
    · exact Or.inl (hg y (ring_mem_boxCollBdry hr))
    · exact Or.inr ⟨Q, hQ, hsub.trans hbQ⟩
  have hboxF : ∀ y ∈ F,
      y ∈ boxColl C (k + d) ∧ Disjoint (interior y.closedBox) C.closedBox ∧ FineGood m δ C y := by
    intro y hy
    obtain ⟨b, hb, hr⟩ := hmemF y hy
    exact hgood b hb y hr
  -- enclosure (as in `hasEnclosure_ring`)
  have hencF : EnclosesBox C {y | y ∈ F} := by
    intro p hpV hp0 hp1
    obtain ⟨t', b, hb, hpt⟩ := henc p hpV hp0 hp1
    have hfr : ∃ s, p s ∈ frontier b.closedBox := by
      by_cases hin : p t' ∈ interior b.closedBox
      · have hA : (frontier (p ⁻¹' interior b.closedBox)).Nonempty := by
          refine nonempty_frontier_iff.2 ⟨⟨t', hin⟩, fun hu => ?_⟩
          have h0 : (0 : unitInterval) ∈ p ⁻¹' interior b.closedBox := hu ▸ mem_univ _
          exact Set.disjoint_left.1 (hall b hb).2.1 h0 hp0
        obtain ⟨s, hs⟩ := hA
        exact ⟨s, frontier_interior_subset (p.continuous.frontier_preimage_subset _ hs)⟩
      · exact ⟨t', by rw [(isClosed_closedBox b).frontier_eq]; exact ⟨hpt, hin⟩⟩
    obtain ⟨s, hs⟩ := hfr
    obtain ⟨bt, hr, hz⟩ := exists_ring_of_frontier d hs
    exact ⟨s, bt, hcovF b hb bt hr, hz⟩
  -- blocks
  have hblkF : ∀ Q, IsParent m δ C Q → CellBlock (cellOf m δ) Q F := by
    intro Q hQ
    obtain ⟨L₁, L₂, L₃, eL, hL2, hL13⟩ := hblk Q hQ
    refine block_of_segs (Q := fun b => b.closedBox ⊆ Q.closedBox)
      (QF := fun y => cellOf m δ y = Q) P ?_ (by rw [h1, eL]) hL2 hL13
    intro p hp y hy
    have hpl : p.1 ∈ b₀ :: t := by rw [← h1]; exact List.mem_map_of_mem hp
    have hr := (h2 p hp y).1 hy
    exact cellOf_ring_iff (hall p.1 hpl).1 hQ hr (hgood p.1 hpl y hr).2.2
  have hcycF : CycChain F := ⟨h3, fun a ha b hb => by
    rw [h5] at ha; rw [h4] at hb; cases ha; cases hb; exact hxe⟩
  have heF : e ∈ F := hcovF b₀ List.mem_cons_self e he
  have hspec : ∀ y ∈ F, IsCell m δ (cellOf m δ y) ∧ y.closedBox ⊆ (cellOf m δ y).closedBox :=
    fun y hy => ⟨(cellOf_spec_fine (hboxF y hy).1 (hboxF y hy).2.2).1,
      (cellOf_spec_fine (hboxF y hy).1 (hboxF y hy).2.2).2.1⟩
  set c := cellOf m δ e
  have hnot : ∃ y ∈ F, cellOf m δ y ≠ c := by
    by_contra hn
    push Not at hn
    refine not_enc_one_cell (c := c) hC (hspec e heF).1 hint (S := {y | y ∈ F}) ?_ hencF
    intro b hb
    refine ⟨?_, (hboxF b hb).2.1⟩
    have := (hspec b hb).2
    rwa [hn b hb] at this
  -- rotation at a change of cell
  obtain ⟨A, T, hAT, hT, hA⟩ := exists_suffix_split (fun y => cellOf m δ y = c) F
  have hmem : ∀ y, y ∈ T ++ A ↔ y ∈ F := fun y => by
    rw [hAT]; simp only [List.mem_append]; tauto
  have hA0 : A ≠ [] := by
    rintro rfl
    obtain ⟨y, hy, hyc⟩ := hnot
    rw [hAT] at hy
    exact hyc (hT y (by simpa using hy))
  refine ⟨T ++ A, by simp [hA0], cycChain_rotate (hAT ▸ hcycF),
    fun b hb => hboxF b ((hmem b).1 hb), ?_, ?_, ?_⟩
  · intro p hpV hp0 hp1
    obtain ⟨s, b, hb, hz⟩ := hencF p hpV hp0 hp1
    exact ⟨s, b, (hmem b).2 hb, hz⟩
  · intro a ha b hb
    rw [List.getLast?_append_of_ne_nil _ hA0] at hb
    have hbc := hA b hb
    have hac : cellOf m δ a = c := by
      rcases T with _ | ⟨u, T⟩
      · simp only [List.nil_append, List.append_nil] at ha hAT
        rw [← hAT, h4] at ha
        cases ha; rfl
      · simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
        subst ha; exact hT _ List.mem_cons_self
    rw [hac]; exact fun h => hbc h.symm
  · intro Q hQ
    have hB := hblkF Q hQ
    rw [hAT] at hB hnot
    exact block_rotate hT hA hnot (by rw [← hAT, h4]; intro a ha; cases ha; rfl) hB

/-- **DEC-93 packet P-6a, coarse form** (open node): the coarse ring from the crossings —
gluing the four long-way crossings of `HasCross` into a closed walk and merging the zones of
the parent cells (DEC-93 §2). -/
def CoarseRingOfCross : Prop :=
  ∀ (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (k d : ℕ), IsCell m δ C → 1 ≤ C.n →
    HasCross C k (fun b' => ∀ bt ∈ boxCollBdry b' d, m bt < δ ^ 2) →
    C.largeBox ⊆ interior dzzV → ∃ l, CoarseRing m δ C k d l

theorem fineRingOfCross_of_coarse (h : CoarseRingOfCross) : FineRingOfCross := by
  intro m δ C K hC h1 hcr hint
  obtain ⟨k, d, hkd, hc⟩ := hcr
  obtain ⟨l, hl⟩ := h m δ C k d hC h1 hc hint
  obtain ⟨L, hL⟩ := fineRing_of_coarse hC hint hl
  exact ⟨L, hkd ▸ hL⟩

/-- **Separation from four crossings** (for the coarse node): a set of boxes containing the four
long-way crossings of `HasCross` encloses `𝖢` (`hasEnclosure_of_hasCross`). -/
theorem enclosesBox_of_hasCross {C : DyBox} {k : ℕ} {M : Set DyBox} (h1 : 1 ≤ C.n)
    (h : HasCross C k (· ∈ M)) : EnclosesBox C M := by
  obtain ⟨l, -, -, hl, henc⟩ := hasEnclosure_of_hasCross h1 h
  intro p hpV hp0 hp1
  obtain ⟨t, b, hb, hz⟩ := henc p hpV hp0 hp1
  exact ⟨t, b, (hl b hb).2.2, hz⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  {W : WhiteNoise.WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.12** from the coarse ring node. -/
theorem dzz_lemma312_of_coarseRing (hW : WhiteNoise.IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hR : CoarseRingOfCross) : DZZLemma312 P γ W :=
  dzz_lemma312_of_fineRing hW hγ hγ2 (fineRingOfCross_of_coarse hR)

end DZZ
end LQGMetric
