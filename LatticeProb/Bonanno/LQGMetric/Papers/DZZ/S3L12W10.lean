/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W9
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W1

/-!
# DZZ Lemma 3.12: `L312CoreR` (D93, packet P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1462–1499:
with the ring enclosure `CellRing` of the maximal bad cell `𝖢`, `𝖢_{i,1}` and `𝖢_{i,2}` are the
last ring cell before and the first after `𝖢` (`exists_enc_split`); Case 3 (both parents,
l. 1489–1497: `𝖢_{i,1}, 𝖢_{i,2}` or `𝖢_{i,1}, 𝖢, 𝖢_{i,2}`, with `s_{𝖢_{i,j}} ≤ s_𝖢/ε*` by
maximality of `𝖢`), otherwise the segment of the ring with at most one parent (`pick_arc`),
loop-erased (`exists_enc_path`), Cases 1–2 (`card_l312Bad_le_one_of_parents`).

* **`l312CoreRing_holds`**, **`l312CoreR_holds : L312CoreR γ`**;
* **`dzz_lemma312_of_cellRing`**: DZZ Lemma 3.12 from packet P-6 (`CellRingOfCross`) alone;
* `CellRingOfCrossRing` (open: the ring part of P-6), `cellRingOfCross_of_ring`,
  **`dzz_lemma312_of_cellRingRing`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- **DZZ's choice of the replacing segment, ring case** (l. 1462–1497). -/
theorem l312CoreRing_holds (γ : ℝ) : L312CoreRing γ := by
  intro αs hαs
  refine ⟨1, one_pos, fun δ hδ m hcov hsize hring u hu v hv hgu hgv l hj hch hnd C hC hmax
    hint => ?_⟩
  set ε := epsStar αs δ
  have hε : 0 < ε := by simp only [ε, epsStar]; positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hCcell : IsCell m δ C := hj.2.1 C (mem_of_mem_l312Bad hC)
  set N := ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊
  have hN : ∀ b, IsCell m δ b → b.n ≤ N := fun b hb =>
    Nat.le_floor (n_le_of_rpow_le_side hδ.1 (hsize b hb).1)
  have hCN := n_add_one_le_of_bad hε1 hN hj.2.1 hC
  obtain ⟨Z, hZne, hZch, hZcyc, hZc, hZenc, hZcount⟩ := (hring C hCcell).2 hint
  have hZcells : ∀ c ∈ Z, IsCell m δ c := fun c hc => (hZc c hc).1
  have hZmeet : ∀ c ∈ Z, (c.closedBox ∩ C.largeBox).Nonempty := fun c hc =>
    (hZc c hc).2.2.mono (inter_subset_inter_right _ sdiff_subset)
  obtain ⟨A, M, B, x, y, hl, hCM, hx, hy, hM⟩ := exists_enc_split hN hε1 hgu hgv hj hch hC hCN
    (fun c hc => ⟨(hZc c hc).1, (hZc c hc).2.2⟩) hZenc
  have hxy : x ≠ y := by
    rintro rfl
    have h2 : (x :: (M ++ x :: B)).Nodup := (hl ▸ hnd).sublist (List.sublist_append_right A _)
    exact (List.nodup_cons.1 h2).1 (by simp)
  obtain ⟨w, hwi, hwZ, hwc, hws, hwL⟩ :=
    succ_small hN hCcell hCN hZcells hZenc hch hj.2.1 hl hCM hM
  obtain ⟨w', hwi', hwZ', hwc', hws', hwL'⟩ :=
    pred_small hN hCcell hCN hZcells hZenc hch hj.2.1 hl hCM hM
  have hxw : Neighbour x w := List.isChain_pair.1 (hch.infix hwi)
  have hw'y : Neighbour w' y := List.isChain_pair.1 (hch.infix hwi')
  have hxs := (hZc x hx).2.1
  have hys := (hZc y hy).2.1
  -- the segment `x, R, y` of the ring, loop-erased
  have finish : ∀ R : List DyBox, (x :: R ++ [y]).IsChain Neighbour → (∀ c ∈ R, c ∈ Z) →
      LeOneParent C (x :: R ++ [y]) →
      ∃ (A M B R : List DyBox) (x y : DyBox), l = A ++ x :: (M ++ y :: B) ∧ C ∈ M ∧
        (x :: R ++ [y]).IsChain Neighbour ∧ R.Nodup ∧
        (∀ c ∈ R, IsCell m δ c ∧ ε * C.side ≤ c.side ∧ (c.closedBox ∩ C.largeBox).Nonempty) ∧
        ε * C.side ≤ x.side ∧ ε * C.side ≤ y.side ∧ (l312Bad ε (x :: R ++ [y])).card ≤ 1 := by
    intro R hR hRZ hpar
    have hEZ : ∀ c ∈ x :: R ++ [y], c ∈ Z := by
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | hc | rfl
      · exact hx
      · exact hRZ c hc
      · exact hy
    obtain ⟨R', hR'ch, hR'nd, hR'E⟩ := exists_enc_path (E := x :: R ++ [y])
      (hR.imp fun a b h => Or.inr h) (fun c hc => hZcells c (hEZ c hc)) (by simp) (by simp) hxy
    have hsub : ∀ c ∈ x :: R' ++ [y], c ∈ x :: R ++ [y] := by
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | hc | rfl
      · simp
      · exact hR'E c hc
      · simp
    have hR'nd' : R'.Nodup := by
      have := (List.nodup_cons.1 (by simpa using hR'nd : (x :: (R' ++ [y])).Nodup)).2
      exact this.sublist (List.sublist_append_left R' [y])
    refine ⟨A, M, B, R', x, y, hl, hCM, hR'ch, hR'nd', fun c hc => ?_, hxs, hys, ?_⟩
    · have hcZ := hEZ c (hR'E c hc)
      exact ⟨hZcells c hcZ, (hZc c hcZ).2.1, hZmeet c hcZ⟩
    · refine card_l312Bad_le_one_of_parents hε (fun c hc => (hZc c (hEZ c (hsub c hc))).2.1) ?_
      intro c hc c' hc' hs hs'
      exact hpar c (hsub c hc) c' (hsub c' hc') hs hs'
  by_cases hboth : C.side < x.side ∧ C.side < y.side
  · -- Case 3 (l. 1489–1497)
    have hxP : IsParent m δ C x := ⟨hZcells x hx, hboth.1, hZmeet x hx⟩
    have hyP : IsParent m δ C y := ⟨hZcells y hy, hboth.2, hZmeet y hy⟩
    have hxε : ε * x.side ≤ C.side := by
      by_contra hlt; push Not at hlt
      have := hmax x (mem_l312Bad_of_pair (Or.inl hwi) (lt_of_le_of_lt hws hlt))
      linarith [hboth.1]
    have hyε : ε * y.side ≤ C.side := by
      by_contra hlt; push Not at hlt
      have := hmax y (mem_l312Bad_of_pair (Or.inr hwi') (lt_of_le_of_lt hws' hlt))
      linarith [hboth.2]
    rcases parents_nbr hCcell hxP hyP hxy with hn | ⟨hxC, hCy⟩
    · refine ⟨A, M, B, [], x, y, hl, hCM, by simpa using hn, List.nodup_nil, by simp, hxs,
        hys, ?_⟩
      simpa using card_l312Bad_case3_adj hε1 (x := x) (y := y)
    · refine ⟨A, M, B, [C], x, y, hl, hCM, ?_, List.nodup_singleton _, ?_, hxs, hys, ?_⟩
      · simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
          List.isChain_singleton, and_true]
        exact ⟨hxC, hCy⟩
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨hCcell, mul_le_of_le_one_left c.side_pos'.le hε1,
          ⟨c.center, center_mem_closedBox' c, mem_largeBox_of_mem_self (center_mem_closedBox' c)⟩⟩
      · have := l312Bad_case3_diag hε1 hboth.1.le hboth.2.le hxε hyε
        simp [this]
  · have hcyc : ∀ a ∈ Z.getLast?, ∀ b ∈ Z.head?, Neighbour a b := by
      intro a ha b hb
      rw [List.getLast?_eq_some_getLast hZne, Option.mem_def, Option.some.injEq] at ha
      rw [List.head?_eq_some_head hZne, Option.mem_def, Option.some.injEq] at hb
      subst ha hb
      exact hZcyc
    obtain ⟨R₁, R₂, hW₁, hW₂, hperm⟩ := exists_arcs ⟨hZch, hcyc⟩ hx hy hxy
    have hR1Z : ∀ c ∈ R₁, c ∈ Z := fun c hc => hperm.subset (by simp [hc])
    have hR2Z : ∀ c ∈ R₂, c ∈ Z := fun c hc => hperm.subset (by simp [hc])
    rcases pick_arc hCcell hW₁ hW₂ hperm (fun c hc => ⟨hZcells c hc, hZmeet c hc⟩) hZcount hxy
      hxw hwc hwL hwZ hw'y hwc' hwL' hwZ' hboth with h | h
    · exact finish R₁ hW₁ hR1Z h
    · exact finish R₂ hW₂ hR2Z h

/-- **`L312CoreR`** (DZZ l. 1462–1499, D93). -/
theorem l312CoreR_holds (γ : ℝ) : L312CoreR γ := l312CoreR_of_ring (l312CoreRing_holds γ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {W : WhiteNoise.WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.12** from the ring enclosure of packet P-6 (D93/D99). -/
theorem dzz_lemma312_of_cellRing (hW : WhiteNoise.IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hR : CellRingOfCross) : DZZLemma312 P γ W :=
  dzz_lemma312_of_coreR hW hγ hγ2 (l312CoreR_holds γ) hR

/-- **The ring part of packet P-6** (D93/D99, open node): the crossing form of `𝓔_{δ,𝖢}` gives,
when `𝖢_large ⊆ 𝕍°`, a cyclic `Neighbour`-ring of cells around `𝖢` in which each parent occurs
once. -/
def CellRingOfCrossRing : Prop :=
  ∀ (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (K : ℕ), IsCell m δ C → 1 ≤ C.n →
    HasCrossRing C K (fun b' => m b' < δ ^ 2) → C.largeBox ⊆ interior dzzV →
    ∃ Z : List DyBox, ∃ hne : Z ≠ [],
      Z.IsChain Neighbour ∧ Neighbour (Z.getLast hne) (Z.head hne) ∧
      (∀ c ∈ Z, IsCell m δ c ∧ (2 : ℝ)⁻¹ ^ K * C.side ≤ c.side ∧
        (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty) ∧
      EnclosesBox C {c | c ∈ Z} ∧ ∀ p ∈ Z, C.side < p.side → Z.count p = 1

/-- Packet P-6 from its ring part (the `CellEnclosure` part is Remark 3.15,
`cellEnclosure_of_hasEnclosure`). -/
theorem cellRingOfCross_of_ring (h : CellRingOfCrossRing) : CellRingOfCross :=
  fun m δ C K hC h1 hc =>
    ⟨cellEnclosure_of_hasEnclosure (hasEnclosure_of_hasCrossRing h1 hc), h m δ C K hC h1 hc⟩

/-- **DZZ Lemma 3.12** from the ring part of packet P-6. -/
theorem dzz_lemma312_of_cellRingRing (hW : WhiteNoise.IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hR : CellRingOfCrossRing) : DZZLemma312 P γ W :=
  dzz_lemma312_of_cellRing hW hγ hγ2 (cellRingOfCross_of_ring hR)

end DZZ
end LQGMetric
