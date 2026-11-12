/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5YMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YEnd

/-!
# DZZ Lemma 3.5: the crossing claim on the square grid, assembled (P2-DZZ35X, decision D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1054–1083). Let `u ∈ A`, `v ∈ B`
realize `d = min D'_δ(A, B)` and `𝖢_1, …, 𝖢_d` the cells of a `δ`-geodesic (l. 1056); for each
`𝖢_i` the enclosure `ℂ_i` (l. 1068–1070) gives the ring of boundary squares `Ring i` of its boxes
on the level-`N` grid, `N = N₀ + k + 1` (decision D84). DZZ's claim "`(⋃ ℂ_i) ∪ ℂ_start ∪ ℂ_end`
contains a crossing between `A_δ` and `B_δ`" (l. 1071–1077) is assembled from

* `l35_recursion` (the `i_r` recursion, with F1 = `not_esc_ring` and ring connectivity
  `ringSq_conn`), along the labelled square path of the geodesic (`exists_labelled_path`);
* `end_conn` at both ends (`ℂ_start`, `ℂ_end`);
* the count (Eq.boundDprime): `ring_cells_finset`, `card_toFinset_boxColl_le` and
  `approxDist_le_card_of_path`: `D'_{δ'} ≤ d · 4^{k+2} λ + 2(R + 4)`.

* `cell_level_le`: a `δ`-cell contains a `δ'`-cell, so its level is `≤ N₀`.
* **`l35CrossingSq_holds : L35CrossingSq`**, hence `L35Crossing` (`l35Crossing_of_sq`).

Own argument on the grid following DZZ's sketch; DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ}

/-- A `δ`-cell has level `≤ N₀` when all `δ'`-cells do (`δ' ≤ δ`): it contains the `δ'`-cell of its
centre. -/
lemma cell_level_le {δ δ' : ℝ} (hδ' : 0 < δ') (hδδ' : δ' ≤ δ)
    (hpart' : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀) {C : DyBox} (hC : IsCell m δ C) : C.n ≤ N₀ := by
  obtain ⟨T, hT, hTm⟩ := hpart' C.center (closedBox_sub_dzzV' C (center_mem_closedBox' C))
  have hmT : m T < δ ^ 2 := lt_of_lt_of_le hT.1 (pow_le_pow_left₀ hδ'.le hδδ' 2)
  obtain ⟨i, hi, he, hA⟩ := cellAnc_spec (m := m) (δ := δ) hmT
  have hAm : (cellAnc m δ T).Mem C.center := by rw [he]; exact mem_anc hTm hi
  have hAn : (cellAnc m δ T).n ≤ T.n := by rw [he]; exact min_le_right _ _
  have hCs : IsSqCell m δ (boxAt (C.n + T.n) C.center) C :=
    ⟨hC, Nat.le_add_right _ _, by rw [anc_boxAt (Nat.le_add_right _ _)]; exact boxAt_center rfl⟩
  have hAs : IsSqCell m δ (boxAt (C.n + T.n) C.center) (cellAnc m δ T) :=
    ⟨hA, by show _ ≤ C.n + T.n; omega, by rw [anc_boxAt (by omega)]; exact hAm.2⟩
  have := isSqCell_unique hCs hAs
  rw [this]
  exact hAn.trans (hN₀ T hT)

lemma cstep_of_connIn {δ' : ℝ} {N : ℕ} {S : Finset DyBox} {Y : Set DyBox}
    (hY : ∀ y ∈ Y, SqIn m δ' N S y) {x y : DyBox} (h : ConnIn Y x y) :
    Relation.ReflTransGen (CStep m δ' N S) x y := by
  obtain ⟨hx, h⟩ := h
  refine cstep_of_reach (hY x hx) ?_
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hY _ hbc.2⟩

lemma le_chain {g : ℕ → ℕ} {r : ℕ} (h : ∀ q < r, g q < g (q + 1)) : ∀ q ≤ r, q ≤ g q := by
  intro q
  induction q with
  | zero => intro _; exact Nat.zero_le _
  | succ q ih => intro hq; have := h q (by omega); have := ih (by omega); omega

/-- **DZZ's crossing claim on the square grid** (l. 1071–1079). -/
theorem l35CrossingSq_holds : L35CrossingSq := by
  intro m δ δ' lam R k N₀ A B hδ' hδδ' hlam hR hpart hpart' hN₀ h1 henc hAV hBV _ _ hA hB
  classical
  have hQ : 0 < 4 ^ (k + 2) * (lam + 1) := by positivity
  by_cases htop : approxDistSet m δ A B = ⊤
  · rw [htop]
    have hpos : ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hQ
    rw [ENat.toENNReal_top, ENNReal.top_mul hpos, top_add]
    exact le_top
  have hfin : ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((approxDistSet m δ A B).toNat : ℝ) := by
    rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, ENat.natCast_toNat htop]
  obtain ⟨u, hu, v, hv, T, T', ⟨hT, hTu⟩, ⟨hT', hT'v⟩, q, hqd, -⟩ := exists_walk_of_le hfin
  set d := q.length + 1 with hd
  set C : ℕ → DyBox := fun i => q.getVert i with hCdef
  have hCc : ∀ i, IsCell m δ (C i) := fun i =>
    isCell_of_mem_support' hT q _ (q.getVert_mem_support i)
  have hlev : ∀ b, IsCell m δ b → b.n ≤ N₀ := fun b hb => cell_level_le hδ' hδδ' hpart' hN₀ hb
  set N := N₀ + k + 1 with hNdef
  have hNδ : ∀ b, IsCell m δ b → b.n ≤ N := fun b hb => by have := hlev b hb; omega
  have hE : ∀ i, EncSq m δ' lam (C i) k := fun i => henc _ (hCc i)
  choose l hlne hlch hlall hlsep using hE
  set Ring : ℕ → Set DyBox := fun i => ringSq N {b | b ∈ l i} with hRing
  have hlN : ∀ i, ∀ b ∈ l i, b.n = (C i).n + k := fun i b hb => (hlall i b hb).1.1
  have hlN' : ∀ i, ∀ b ∈ l i, b.n ≤ N := fun i b hb => by
    have := hlN i b hb; have := hlev _ (hCc i); omega
  -- F1
  have hF1 : ∀ i < d, ∀ s : DyBox, s.n = N → s.closedBox ⊆ (C i).closedBox →
      s ∉ Ring i ∧ ¬ Esc (Ring i) (C i).largeBox s := by
    intro i _ s hs hsC
    refine ⟨?_, not_esc_ring (hlsep i N (by have := hlev _ (hCc i); omega)) (hlN' i)
      (fun b hb => (hlall i b hb).2.1) hs hsC⟩
    rintro ⟨b, hb, hbs⟩
    exact disjoint_left.mp (hlall i b hb).2.1 (interior_mono hbs.2.1 (center_mem_interior' s))
      (hsC (center_mem_closedBox' s))
  have hconn : ∀ i, ∀ x ∈ Ring i, ∀ y ∈ Ring i, ConnIn (Ring i) x y := fun i =>
    ringSq_conn (l i) (hlch i) (hlN' i) (fun b hb b' hb' => by rw [hlN i b hb, hlN i b' hb'])
  -- the geodesic as a labelled path of squares
  obtain ⟨M, p, lab, hp0, hpM, hl0, hlM, hall, hsteps⟩ := exists_labelled_path hNδ q hT
    (boxAt N u) (boxAt N v) rfl (boxAt_sub_of_mem hTu (hNδ T hT)) rfl
    (boxAt_sub_of_mem hT'v (hNδ T' hT'))
  obtain ⟨r, g, hgd, hch, hE0, hEr⟩ := l35_recursion (N := N) (d := d) (M := M) C Ring p lab
    (fun i _ => h1 _ (hCc i)) (fun i _ => by have := hlev _ (hCc i); omega) hF1
    (fun i _ => hconn i) (fun t ht => (hall t ht).1) (fun t ht => (hsteps t ht).1)
    (fun t ht => ⟨by have := (hall t ht).2.1; omega, (hall t ht).2.2⟩)
    (fun t ht => (hsteps t ht).2) hl0 (by omega)
  rw [hp0] at hE0
  rw [hpM] at hEr
  -- the ring squares lie in `𝖢_large`
  have hX : ∀ i, ∀ x ∈ Ring i, x.n = N ∧ x.closedBox ⊆ (C i).largeBox := by
    rintro i x ⟨b, hb, hxb⟩
    exact ⟨hxb.1, hxb.2.1.trans (hlall i b hb).1.2⟩
  -- the two ends
  obtain ⟨SA, hSA, u', hu', xA, hxA, hrA, hinA⟩ := end_conn hR hAV hA hpart' hN₀
    (by omega : N₀ ≤ N) (hCc (g 0)) (by have := hlev _ (hCc (g 0)); omega) (hX (g 0)) hu hE0
  obtain ⟨SB, hSB, v', hv', xB, hxB, hrB, hinB⟩ := end_conn hR hBV hB hpart' hN₀
    (by omega : N₀ ≤ N) (hCc (g r)) (by have := hlev _ (hCc (g r)); omega) (hX (g r)) hv hEr
  -- the cells of the rings
  have hrc : ∀ i, ∃ S : Finset DyBox, (S.card : ℝ) ≤ (l i).toFinset.card * lam ∧
      ∀ s ∈ Ring i, ∀ T, IsSqCell m δ' s T → T ∈ S := fun i =>
    ring_cells_finset (m := m) (δ := δ') (N := N) (lam := lam) (l := l i)
      (fun b hb => ⟨hlN' i b hb, (hlall i b hb).2.2⟩)
  choose SR hSR hSRmem using hrc
  set SY := (Finset.range (r + 1)).biUnion fun q' => SR (g q')
  set S := SA ∪ SB ∪ SY
  have hY : ∀ y ∈ {z | ∃ q' ≤ r, z ∈ Ring (g q')}, SqIn m δ' N S y := by
    rintro y ⟨q', hq', hy⟩
    refine ⟨(hX _ y hy).1, fun T hT => ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨q', Finset.mem_range.2 (by omega), hSRmem _ y hy T hT⟩)
  have hmid := cstep_of_connIn hY (connIn_chain (Ring := Ring) (g := g) (r := r)
    (fun q' _ => hconn (g q')) (fun q' hq' => (hch q' hq').2) r le_rfl xA ⟨0, Nat.zero_le _, hxA⟩
    xB ⟨r, le_rfl, hxB⟩)
  have hSAS : SA ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSBS : SB ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hpath : Relation.ReflTransGen (CStep m δ' N S) (boxAt N u') (boxAt N v') :=
    ((cstep_mono hSAS hrA).trans hmid).trans (cstep_symm (cstep_mono hSBS hrB))
  obtain ⟨M', f, hf0, hfM, hf⟩ := rtg_to_fun hpath
  have hfin' : ∀ t ≤ M', SqIn m δ' N S (f t) := by
    intro t ht
    rcases Nat.lt_or_ge t M' with h | h
    · exact (hf t h).2.1
    · rw [show t = M' by omega, hfM]; exact hinB.mono hSBS
  have hcount := approxDist_le_card_of_path hpart' hN₀ f M'
    (fun t ht => by rw [(hfin' t ht).1]; omega) (fun t ht => Or.inr (hf t ht).1) S
    (fun t ht => (hfin' t ht).2) (u := u') (v := v')
    (by rw [hf0]; exact ⟨hAV hu', rfl⟩) (by rw [hfM]; exact ⟨hBV hv', rfl⟩)
  -- the count
  have hrd : r + 1 ≤ d := by have := le_chain (fun q' hq' => (hch q' hq').1) r le_rfl
                             have := hgd r le_rfl; omega
  have hSRle : ∀ i, (SR i : Finset DyBox).card ≤ (4 : ℝ) ^ (k + 2) * lam := by
    intro i
    have hc : ((l i).toFinset.card : ℝ) ≤ (4 : ℝ) ^ (k + 2) := by
      exact_mod_cast card_toFinset_boxColl_le (fun b hb => (hlall i b hb).1)
    exact (hSR i).trans (mul_le_mul_of_nonneg_right hc (by linarith))
  have hSY : (SY.card : ℝ) ≤ d * ((4 : ℝ) ^ (k + 2) * lam) := by
    have e1 : (SY.card : ℝ) ≤ ∑ q' ∈ Finset.range (r + 1), ((SR (g q')).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have e2 : ∑ q' ∈ Finset.range (r + 1), ((SR (g q')).card : ℝ) ≤
        ∑ _q' ∈ Finset.range (r + 1), (4 : ℝ) ^ (k + 2) * lam :=
      Finset.sum_le_sum fun q' _ => hSRle _
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at e2
    have e3 : ((r + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hrd
    have : 0 ≤ (4 : ℝ) ^ (k + 2) * lam := by positivity
    nlinarith
  have hS : (S.card : ℝ) ≤ d * (4 ^ (k + 2) * (lam + 1)) + (2 * R + 8) := by
    have c1 : S.card ≤ SA.card + SB.card + SY.card :=
      (Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _)
    have c1' : (S.card : ℝ) ≤ SA.card + SB.card + SY.card := by exact_mod_cast c1
    have : (0 : ℝ) ≤ d * 4 ^ (k + 2) := by positivity
    nlinarith
  calc ((approxDistSet m δ' A B : ℕ∞) : ℝ≥0∞)
      ≤ ((approxDist m δ' u' v' : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 (iInf₂_le_of_le u' hu' (iInf₂_le v' hv'))
    _ ≤ ((S.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 hcount
    _ = ENNReal.ofReal (S.card : ℝ) := by rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (d * (4 ^ (k + 2) * (lam + 1)) + (2 * R + 8)) :=
        ENNReal.ofReal_le_ofReal hS
    _ = (d : ℝ≥0∞) * ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) + ENNReal.ofReal (2 * R + 8) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ _ := by
        gcongr
        rw [← ENat.toENNReal_coe]
        exact ENat.toENNReal_le.2 hqd

/-- **DZZ's crossing claim** (`L35Crossing`, l. 1071–1079). -/
theorem l35Crossing_holds : L35Crossing := l35Crossing_of_sq l35CrossingSq_holds

end DZZ
end LQGMetric
