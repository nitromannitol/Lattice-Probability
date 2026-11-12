/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W1

/-!
# Walled DZZ Lemma 3.5, W2: the walled crossing claim from the proved one (P2-DZZL35W)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1054–1083) for the walled approximate distance
`D'_S`, `S = cellsInside Bw` (D123), with enclosures *relative to the wall* (finding 3 of
`handoff/P2-DZZ317K.md`). Since the cell graph of `𝒱_δ` restricted to the cells inside `B̄w` is
the cell graph of the pulled-back mass function `m ∘ wEmb Bw` (S3L5W1) on the dyadic grid of `𝕍`,
the deterministic crossing claim of the walled lemma is the proved `l35Crossing_holds`
(S3L5YMain, decision D84) for `m ∘ wEmb Bw`, transported back:

* `edist_map_le`: graph homomorphisms do not increase `edist`;
* `approxDistOn_wHom`, `approxDistSetOn_wHom`: `D'_{S,δ}(A, B) = D'_{m∘wEmb, δ}(ψ⁻¹A, ψ⁻¹B)` for
  `A, B` in the interior of `B̄w` (`ψ = wHom Bw`), when `Bw` is split at `δ`;
* `cellPsi_wEmb`: `Ψ` of a sub-box is the `Ψ` of the pulled-back box;
* `hpart_wEmb`: the pulled-back cells partition `𝕍`;
* **`l35CrossingOn`**: the walled crossing claim (`L35Crossing` for `D'_S`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma edist_map_le {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G')
    (u v : V) : G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · rw [h]; exact le_top
  obtain ⟨p, hp⟩ := (SimpleGraph.reachable_of_edist_ne_top h).exists_walk_length_eq_edist
  rw [← hp]
  exact (SimpleGraph.edist_le (p.map f)).trans (by rw [SimpleGraph.Walk.length_map])

lemma wEmb_root (Bw : DyBox) : wEmb Bw DyBox.root = Bw := by
  ext <;> simp [wEmb, DyBox.root]

lemma closedBox_root : DyBox.root.closedBox = dzzV := by
  ext z; simp [DyBox.closedBox, DyBox.root, DyBox.side, dzzV]

/-- A point whose image lies in the interior of `B̄w` is in `𝕍`, off the top and right edges. -/
lemma of_wHom_mem_interior {Bw : DyBox} {x : ℂ} (h : wHom Bw x ∈ interior Bw.closedBox) :
    x ∈ dzzV ∧ x.re < 1 ∧ x.im < 1 := by
  have e : Bw.closedBox = wHom Bw '' dzzV := by
    rw [← closedBox_root, ← closedBox_wEmb, wEmb_root]
  rw [e, ← (wHom Bw).image_interior, (wHom Bw).injective.mem_set_image] at h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x h
  have h1 : x + ((ε / 2 : ℝ) : ℂ) ∈ dzzV := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]; linarith))
  have h2 : x + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ dzzV := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith))
  refine ⟨interior_subset h, ?_, ?_⟩
  · have := h1.2.1; simp at this; linarith
  · have := h2.2.2.2; simp at this; linarith

/-- The pullback of a box to the grid of `𝕍` (junk off `cellsInside Bw`). -/
def wPull (Bw T : DyBox) : DyBox :=
  open Classical in if h : ∃ b, T = wEmb Bw b then h.choose else T

lemma wPull_wEmb (Bw b : DyBox) : wPull Bw (wEmb Bw b) = b := by
  have h : ∃ b', wEmb Bw b = wEmb Bw b' := ⟨b, rfl⟩
  simp only [wPull, dif_pos h]
  exact (wEmb_injective Bw h.choose_spec).symm

section Graph

variable {m : DyBox → ℝ} {δ : ℝ} {Bw : DyBox}

/-- `wEmb` as a homomorphism of cell graphs. -/
def wEmbHom (hs : WSplit m δ Bw) :
    cellGraph (fun c => m (wEmb Bw c)) δ →g cellGraphOn (cellsInside Bw) m δ where
  toFun := wEmb Bw
  map_rel' {b b'} h := ⟨⟨(isCell_wEmb_iff hs).2 h.1, (isCell_wEmb_iff hs).2 h.2.1,
    neighbour_wEmb_iff.2 h.2.2⟩, wEmb_mem_cellsInside Bw b, wEmb_mem_cellsInside Bw b'⟩

/-- `wPull` as a homomorphism of cell graphs. -/
def wPullHom (hs : WSplit m δ Bw) :
    cellGraphOn (cellsInside Bw) m δ →g cellGraph (fun c => m (wEmb Bw c)) δ where
  toFun := wPull Bw
  map_rel' {T T'} h := by
    obtain ⟨⟨h1, h2, h3⟩, hT, hT'⟩ := h
    obtain ⟨b, rfl⟩ := exists_wEmb_of_sub hT
    obtain ⟨b', rfl⟩ := exists_wEmb_of_sub hT'
    rw [wPull_wEmb, wPull_wEmb]
    exact ⟨(isCell_wEmb_iff hs).1 h1, (isCell_wEmb_iff hs).1 h2, neighbour_wEmb_iff.1 h3⟩

lemma approxDistOn_wHom (hs : WSplit m δ Bw) {x y : ℂ} (hx : wHom Bw x ∈ interior Bw.closedBox)
    (hy : wHom Bw y ∈ interior Bw.closedBox) :
    approxDistOn (cellsInside Bw) m δ (wHom Bw x) (wHom Bw y) =
      approxDist (fun c => m (wEmb Bw c)) δ x y := by
  obtain ⟨hxV, hx1, hx2⟩ := of_wHom_mem_interior hx
  obtain ⟨hyV, hy1, hy2⟩ := of_wHom_mem_interior hy
  apply le_antisymm
  · refine le_iInf fun b => le_iInf fun b' => le_iInf fun hb => le_iInf fun hb' => ?_
    refine iInf_le_of_le (wEmb Bw b) (iInf_le_of_le (wEmb Bw b') (iInf_le_of_le
      ⟨(isCell_wEmb_iff hs).2 hb.1, (mem_wEmb_iff hxV hx1 hx2).2 hb.2, wEmb_mem_cellsInside Bw b⟩
      (iInf_le_of_le ⟨(isCell_wEmb_iff hs).2 hb'.1, (mem_wEmb_iff hyV hy1 hy2).2 hb'.2,
        wEmb_mem_cellsInside Bw b'⟩ ?_)))
    gcongr
    exact edist_map_le (wEmbHom hs) b b'
  · refine le_iInf fun T => le_iInf fun T' => le_iInf fun hT => le_iInf fun hT' => ?_
    obtain ⟨b, rfl⟩ := exists_wEmb_of_sub hT.2.2
    obtain ⟨b', rfl⟩ := exists_wEmb_of_sub hT'.2.2
    refine iInf_le_of_le b (iInf_le_of_le b' (iInf_le_of_le
      ⟨(isCell_wEmb_iff hs).1 hT.1, (mem_wEmb_iff hxV hx1 hx2).1 hT.2.1⟩
      (iInf_le_of_le ⟨(isCell_wEmb_iff hs).1 hT'.1, (mem_wEmb_iff hyV hy1 hy2).1 hT'.2.1⟩ ?_)))
    gcongr
    have := edist_map_le (wPullHom hs) (wEmb Bw b) (wEmb Bw b')
    change (cellGraph _ δ).edist (wPull Bw (wEmb Bw b)) (wPull Bw (wEmb Bw b')) ≤ _ at this
    rwa [wPull_wEmb, wPull_wEmb] at this

lemma approxDistSetOn_wHom (hs : WSplit m δ Bw) {A B : Set ℂ} (hA : A ⊆ interior Bw.closedBox)
    (hB : B ⊆ interior Bw.closedBox) :
    approxDistSetOn (cellsInside Bw) m δ A B =
      approxDistSet (fun c => m (wEmb Bw c)) δ (wHom Bw ⁻¹' A) (wHom Bw ⁻¹' B) := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    rw [← approxDistOn_wHom hs (hA hx) (hB hy)]
    exact iInf₂_le_of_le (wHom Bw x) hx (iInf₂_le (wHom Bw y) hy)
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    have hx' : wHom Bw ((wHom Bw).symm x) = x := by simp
    have hy' : wHom Bw ((wHom Bw).symm y) = y := by simp
    have e := approxDistOn_wHom hs (x := (wHom Bw).symm x) (y := (wHom Bw).symm y)
      (by rw [hx']; exact hA hx) (by rw [hy']; exact hB hy)
    rw [hx', hy'] at e
    rw [e]
    exact iInf₂_le_of_le ((wHom Bw).symm x) (show (wHom Bw).symm x ∈ wHom Bw ⁻¹' A by
      rw [mem_preimage, hx']; exact hx)
      (iInf₂_le ((wHom Bw).symm y) (show (wHom Bw).symm y ∈ wHom Bw ⁻¹' B by
        rw [mem_preimage, hy']; exact hy))

end Graph

/-! ### `Ψ` and the partition -/

/-- Two dyadic boxes: if a ball inside `T̄` has its centre in `B̄` and `T.n ≤ B.n`, then
`B.anc T.n = T`. -/
lemma anc_eq_of_subW {T B : DyBox} (h : B.closedBox ⊆ T.closedBox) : B.anc T.n = T := by
  obtain ⟨b, rfl⟩ := exists_wEmb_of_sub h
  rw [wEmb_anc_le _ _ le_rfl, anc_self le_rfl]

/-- A cell containing a sub-box of a split wall box lies inside the wall. -/
lemma cell_sub_wall {m : DyBox → ℝ} {δ : ℝ} {Bw T c : DyBox} (hs : WSplit m δ Bw)
    (hT : IsCell m δ T) (hc : (wEmb Bw c).closedBox ⊆ T.closedBox) :
    T.closedBox ⊆ Bw.closedBox := by
  set X := wEmb Bw c
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior X.center (center_mem_interior' X)
  have hb : Metric.ball X.center ε ⊆ X.closedBox := hball.trans interior_subset
  have hz : X.center ∈ Metric.ball X.center ε := Metric.mem_ball_self hε
  rcases le_total T.n Bw.n with h | h
  · have hsub := closedBox_sub_of_ball h (hb.trans hc) hz (closedBox_wEmb_sub Bw c
      (center_mem_closedBox' X))
    have := hs T.n h
    rw [anc_eq_of_subW hsub] at this
    linarith [hT.1]
  · exact closedBox_sub_of_ball h (hb.trans (closedBox_wEmb_sub Bw c)) hz
      (hc (center_mem_closedBox' X))

lemma cellPsi_wEmb {m : DyBox → ℝ} {δ : ℝ} {Bw : DyBox} (hs : WSplit m δ Bw) (c : DyBox) :
    cellPsi (fun c => m (wEmb Bw c)) δ c = cellPsi m δ (wEmb Bw c) := by
  classical
  have himg : ∀ b b' : DyBox, (wEmb Bw b).closedBox ⊆ (wEmb Bw b').closedBox ↔
      b.closedBox ⊆ b'.closedBox := fun b b' => by
    rw [closedBox_wEmb, closedBox_wEmb, Set.image_subset_image_iff (wHom Bw).injective]
  have hcond : (∃ c', IsCell (fun c => m (wEmb Bw c)) δ c' ∧ c.closedBox ⊆ c'.closedBox) ↔
      ∃ T, IsCell m δ T ∧ (wEmb Bw c).closedBox ⊆ T.closedBox := by
    constructor
    · rintro ⟨c', h1, h2⟩
      exact ⟨wEmb Bw c', (isCell_wEmb_iff hs).2 h1, (himg c c').2 h2⟩
    · rintro ⟨T, h1, h2⟩
      obtain ⟨c', rfl⟩ := exists_wEmb_of_sub (cell_sub_wall hs h1 h2)
      exact ⟨c', (isCell_wEmb_iff hs).1 h1, (himg c c').1 h2⟩
  unfold cellPsi
  rw [← hcond]
  split_ifs with h
  · rfl
  · have e : {T | IsCell m δ T ∧ T.closedBox ⊆ (wEmb Bw c).closedBox ∧
        (T.closedBox ∩ frontier (wEmb Bw c).closedBox).Nonempty} = wEmb Bw ''
        {c' | IsCell (fun c => m (wEmb Bw c)) δ c' ∧ c'.closedBox ⊆ c.closedBox ∧
          (c'.closedBox ∩ frontier c.closedBox).Nonempty} := by
      ext T
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨c', rfl⟩ := exists_wEmb_of_sub (h2.trans (closedBox_wEmb_sub Bw c))
        refine ⟨c', ⟨(isCell_wEmb_iff hs).1 h1, (himg c' c).1 h2, ?_⟩, rfl⟩
        rw [closedBox_wEmb, closedBox_wEmb, ← (wHom Bw).image_frontier,
          ← image_inter (wHom Bw).injective, image_nonempty] at h3
        exact h3
      · rintro ⟨c', ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨(isCell_wEmb_iff hs).2 h1, (himg c' c).2 h2, ?_⟩
        rw [closedBox_wEmb, closedBox_wEmb, ← (wHom Bw).image_frontier,
          ← image_inter (wHom Bw).injective, image_nonempty]
        exact h3
    rw [e, (wEmb_injective Bw).encard_image]

lemma psiLe_wEmb {m : DyBox → ℝ} {δ lam : ℝ} {Bw : DyBox} (hs : WSplit m δ Bw) (c : DyBox) :
    PsiLe (fun c => m (wEmb Bw c)) δ c lam ↔ PsiLe m δ (wEmb Bw c) lam := by
  unfold PsiLe; rw [cellPsi_wEmb hs]

/-- The pulled-back cells partition `𝕍`. -/
lemma hpart_wEmb {m : DyBox → ℝ} {δ : ℝ} {Bw : DyBox} (hs : WSplit m δ Bw)
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ b → b.n ≤ N₀) :
    ∀ v ∈ dzzV, ∃ b, IsCell (fun c => m (wEmb Bw c)) δ b ∧ b.Mem v := by
  intro v hv
  set X := wEmb Bw (boxAt N₀ v)
  obtain ⟨T, hT, hTm⟩ := hpart X.center (closedBox_sub_dzzV' X (center_mem_closedBox' X))
  have hTn := hN₀ T hT
  have hXn : X.n = Bw.n + N₀ := rfl
  have hTX : T = X.anc T.n := by
    have h1 := hTm.2
    rw [← anc_boxAt (show T.n ≤ X.n by omega), boxAt_center rfl] at h1
    exact h1.symm
  rcases le_or_gt T.n Bw.n with h | h
  · have := hs T.n h
    rw [← wEmb_anc_le Bw (boxAt N₀ v) h, ← hTX] at this
    linarith [hT.1]
  · obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le h.le
    have hiN : i ≤ N₀ := by omega
    have e : T = wEmb Bw (boxAt i v) := by
      rw [hTX, hi, wEmb_anc_add, anc_boxAt hiN]
    rw [e] at hT
    exact ⟨boxAt i v, (isCell_wEmb_iff hs).1 hT, hv, rfl⟩

lemma hasEnclosure_mono {b : DyBox} {k : ℕ} {g g' : DyBox → Prop} (h : ∀ c, g c → g' c)
    (he : HasEnclosure b k g) : HasEnclosure b k g' := by
  obtain ⟨l, hne, hch, hall, henc⟩ := he
  exact ⟨l, hne, hch, fun b' hb' => ⟨(hall b' hb').1, (hall b' hb').2.1, h _ (hall b' hb').2.2⟩,
    henc⟩

/-- **The walled crossing claim** (DZZ l. 1071–1079 for `D'_S`, `S = cellsInside Bw`): the
enclosures are those of the pulled-back cells (enclosures relative to the wall), the end
conditions are for the pulled-back sets. From `l35Crossing_holds` for `m ∘ wEmb Bw`. -/
theorem l35CrossingOn {m : DyBox → ℝ} {δ δ' lam R : ℝ} {k N₀ : ℕ} {Bw : DyBox} {A B : Set ℂ}
    (hδ' : 0 < δ') (hδδ' : δ' ≤ δ) (hlam : 1 ≤ lam) (hR : 0 ≤ R)
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v)
    (hpart' : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀)
    (hs : WSplit m δ Bw)
    (henc : ∀ b, IsCell (fun c => m (wEmb Bw c)) δ b →
      HasEnclosure b k fun c => PsiLe m δ' (wEmb Bw c) lam)
    (hA : A ⊆ interior Bw.closedBox) (hB : B ⊆ interior Bw.closedBox) (hAn : A.Nonempty)
    (hBn : B.Nonempty)
    (hSA : StartCond (fun c => m (wEmb Bw c)) δ δ' R (wHom Bw ⁻¹' A))
    (hSB : StartCond (fun c => m (wEmb Bw c)) δ δ' R (wHom Bw ⁻¹' B)) :
    ((approxDistSetOn (cellsInside Bw) m δ' A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxDistSetOn (cellsInside Bw) m δ A B : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) + ENNReal.ofReal (2 * R + 8) := by
  have hs' : WSplit m δ' Bw := hs.mono hδ'.le hδδ'
  have hN : ∀ b, IsCell m δ b → b.n ≤ N₀ := fun b hb => cell_level_le hδ' hδδ' hpart' hN₀ hb
  rw [approxDistSetOn_wHom hs hA hB, approxDistSetOn_wHom hs' hA hB]
  have hsub : ∀ X : Set ℂ, X ⊆ interior Bw.closedBox → wHom Bw ⁻¹' X ⊆ dzzV :=
    fun X hX x hx => (of_wHom_mem_interior (hX hx)).1
  have hne : ∀ X : Set ℂ, X.Nonempty → (wHom Bw ⁻¹' X).Nonempty := fun X ⟨x, hx⟩ =>
    ⟨(wHom Bw).symm x, by simpa using hx⟩
  exact l35Crossing_holds _ δ δ' lam R k N₀ _ _ hδ' hδδ' hlam hR (hpart_wEmb hs hpart hN)
    (hpart_wEmb hs' hpart' hN₀)
    (fun b hb => by
      have := hN₀ _ ((isCell_wEmb_iff hs').2 hb); simp only [wEmb] at this; omega)
    (not_isCell_root_of_split hs)
    (fun b hb => hasEnclosure_mono (fun c hc => (psiLe_wEmb hs' c).2 hc) (henc b hb))
    (hsub A hA) (hsub B hB) (hne A hAn) (hne B hBn) hSA hSB

end DZZ
end LQGMetric
