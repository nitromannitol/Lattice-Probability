/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5YEnd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YSq

/-!
# DZZ Lemma 3.5: the two ends of the crossing (P2-DZZ35X, decision D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1058–1066 (`ℂ_start`) and
l. 1076–1077: "`A_δ` is connected to `ℂ_start ∪ ℂ_{i_1}`"). On the level-`N` square grid
(decision D84, DEC-84 §4 "Ends"): if the square of `u ∈ A` is enclosed by a wall `X` of squares
of `𝖢_large` (`𝖢` a `δ`-cell), then a 4-path of squares from a point of `A` to `X` uses at most
`R + 4` cells of `𝒱_{δ'}`:

* `A = {u}`: the `δ'`-geodesic from `u` to `∂𝖢_large ∩ 𝕍` (`≤ R` cells, `StartCond`) as a path
  of squares, plus `≤ 2` squares to leave `𝖢_large`; it meets `X` (`hit_of_reach`).
* `A` connected and not inside `𝖢_large`: the squares meeting `A` are 4-connected
  (`sq_reach_of_connected`) and reach outside `𝖢_large`, so one of them lies in `X`; it is
  joined to the square of a point of `A` in its closure by `≤ 2` steps (`ℂ_start = ∅`).

* `SqIn`, `CStep`: squares with cells in a finite set `S`, and steps between them.
* **`end_conn`**.

Own elementary arguments (DZZ's sketch made rigorous); DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- A level-`N` square whose `δ'`-cell lies in `S`. -/
def SqIn (m : DyBox → ℝ) (δ' : ℝ) (N : ℕ) (S : Finset DyBox) (b : DyBox) : Prop :=
  b.n = N ∧ ∀ T, IsSqCell m δ' b T → T ∈ S

/-- A 4-step between squares with cells in `S`. -/
def CStep (m : DyBox → ℝ) (δ' : ℝ) (N : ℕ) (S : Finset DyBox) (a b : DyBox) : Prop :=
  SqAdj a b ∧ SqIn m δ' N S a ∧ SqIn m δ' N S b

variable {m : DyBox → ℝ}

lemma SqIn.mono {δ' : ℝ} {N : ℕ} {S S' : Finset DyBox} (h : S ⊆ S') {b : DyBox}
    (hb : SqIn m δ' N S b) : SqIn m δ' N S' b := ⟨hb.1, fun T hT => h (hb.2 T hT)⟩

lemma CStep.symm {δ' : ℝ} {N : ℕ} {S : Finset DyBox} {a b : DyBox} (h : CStep m δ' N S a b) :
    CStep m δ' N S b a := ⟨h.1.symm, h.2.2, h.2.1⟩

lemma cstep_mono {δ' : ℝ} {N : ℕ} {S S' : Finset DyBox} (h : S ⊆ S') {a b : DyBox}
    (hab : Relation.ReflTransGen (CStep m δ' N S) a b) :
    Relation.ReflTransGen (CStep m δ' N S') a b := by
  induction hab with
  | refl => exact .refl
  | tail _ h' ih => exact ih.tail ⟨h'.1, h'.2.1.mono h, h'.2.2.mono h⟩

lemma cstep_of_reach {δ' : ℝ} {N : ℕ} {S : Finset DyBox} {s x : DyBox} (hs : SqIn m δ' N S s)
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ SqIn m δ' N S b) s x) :
    Relation.ReflTransGen (CStep m δ' N S) s x := by
  have key : ∀ c, Relation.ReflTransGen (fun a b => SqAdj a b ∧ SqIn m δ' N S b) s c →
      SqIn m δ' N S c ∧ Relation.ReflTransGen (CStep m δ' N S) s c := by
    intro c hc
    induction hc with
    | refl => exact ⟨hs, .refl⟩
    | tail _ hbc ih => exact ⟨hbc.2, ih.2.tail ⟨hbc.1, ih.1, hbc.2⟩⟩
  exact (key x h).2

lemma cstep_symm {δ' : ℝ} {N : ℕ} {S : Finset DyBox} {a b : DyBox}
    (h : Relation.ReflTransGen (CStep m δ' N S) a b) :
    Relation.ReflTransGen (CStep m δ' N S) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

lemma isCell_of_mem_support' {δ : ℝ} {c c' : DyBox} (hc : IsCell m δ c) :
    ∀ (p : (cellGraph m δ).Walk c c'), ∀ x ∈ p.support, IsCell m δ x
  | .nil, x, hx => by simp at hx; rw [hx]; exact hc
  | .cons h p, x, hx => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact isCell_of_mem_support' h.2.1 p x hx

lemma boxAt_sub_of_mem {b : DyBox} {v : ℂ} (hb : b.Mem v) {N : ℕ} (h : b.n ≤ N) :
    (boxAt N v).closedBox ⊆ b.closedBox := by
  have e : (boxAt N v).anc b.n = b := by rw [anc_boxAt h]; exact hb.2
  rw [← e]; exact closedBox_sub_anc _ _

/-- A geodesic realizing `min D'_δ(A, B) ≤ R`. -/
lemma exists_walk_of_le {δ : ℝ} {A B : Set ℂ} {R : ℝ}
    (h : ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal R) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ T T' : DyBox, (IsCell m δ T ∧ T.Mem x) ∧ (IsCell m δ T' ∧ T'.Mem y) ∧
      ∃ q : (cellGraph m δ).Walk T T', (((q.length + 1 : ℕ) : ℕ∞) ≤ approxDistSet m δ A B) ∧
        ((q.length + 1 : ℕ) : ℝ) ≤ R := by
  set D := approxDistSet m δ A B with hDdef
  have hD : D ≠ ⊤ := by
    intro h'
    rw [h'] at h
    simp at h
  have hlt : approxDistSet m δ A B < D + 1 := (ENat.lt_add_one_iff hD).2 le_rfl
  simp only [approxDistSet, approxDist, iInf_lt_iff] at hlt
  obtain ⟨x, hx, y, hy, T, T', ⟨hT, hTx⟩, ⟨hT', hT'y⟩, hlt⟩ := hlt
  have hle : (cellGraph m δ).edist T T' + 1 ≤ D := (ENat.lt_add_one_iff hD).1 hlt
  have hne : (cellGraph m δ).edist T T' ≠ ⊤ := fun h' => by
    rw [h', top_add] at hle; exact hD (top_le_iff.1 hle)
  obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hq' : (((q.length + 1 : ℕ) : ℕ∞)) ≤ D := by push_cast; rw [hq]; exact hle
  refine ⟨x, hx, y, hy, T, T', ⟨hT, hTx⟩, ⟨hT', hT'y⟩, q, hq', ?_⟩
  have h2 := (ENat.toENNReal_le.2 hq').trans h
  rw [ENat.toENNReal_coe] at h2
  exact (ENNReal.natCast_le_ofReal (by omega)).1 h2

/-- **The ends of the crossing** (DZZ l. 1058–1066, 1076–1077). -/
theorem end_conn {δ δ' R : ℝ} {N₀ N : ℕ} {A : Set ℂ} (hR : 0 ≤ R) (hAV : A ⊆ dzzV)
    (hA : StartCond m δ δ' R A)
    (hpart' : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀)
    (hN : N₀ ≤ N) {C : DyBox} (hC : IsCell m δ C) (hCN : C.n + 1 ≤ N) {X : Set DyBox}
    (hX : ∀ x ∈ X, x.n = N ∧ x.closedBox ⊆ C.largeBox) {u : ℂ} (hu : u ∈ A)
    (henc : ¬ Esc X C.largeBox (boxAt N u)) :
    ∃ S : Finset DyBox, (S.card : ℝ) ≤ R + 4 ∧ ∃ u' ∈ A, ∃ x ∈ X,
      Relation.ReflTransGen (CStep m δ' N S) (boxAt N u') x ∧ SqIn m δ' N S (boxAt N u') := by
  classical
  -- the cell of a level-`N` square, and the singleton-cell property
  have cell : ∀ s : DyBox, s.n = N → ∃ T, IsSqCell m δ' s T := fun s hs =>
    exists_isSqCell hpart' hN₀ (hs ▸ hN)
  have sqin1 : ∀ (S : Finset DyBox) (s T : DyBox), s.n = N → IsSqCell m δ' s T → T ∈ S →
      SqIn m δ' N S s := fun S s T hs hT hTS =>
    ⟨hs, fun T' hT' => (isSqCell_unique hT hT') ▸ hTS⟩
  rcases hA with ⟨u₀, rfl, hst⟩ | ⟨hconn, hnot⟩
  · -- the point case
    rw [mem_singleton_iff] at hu
    subst hu
    have huV : u ∈ dzzV := hAV rfl
    have huL : u ∈ C.largeBox := by
      have hsub : (boxAt N u).closedBox ⊆ C.largeBox := by
        by_cases hx : boxAt N u ∈ X
        · exact (hX _ hx).2
        · exact sub_of_not_esc hx henc
      exact hsub (mem_closedBox_boxAt huV)
    obtain ⟨u₁, hu₁, w, hwF, T, T', ⟨hT, hTu⟩, ⟨hT', hT'w⟩, q, -, hq⟩ :=
      exists_walk_of_le (hst C hC huL)
    rw [mem_singleton_iff] at hu₁
    subst hu₁
    have hNδ' : ∀ b, IsCell m δ' b → b.n ≤ N := fun b hb => (hN₀ b hb).trans hN
    obtain ⟨M, p, lab, hp0, hpM, -, -, hall, hsteps⟩ := exists_labelled_path hNδ' q hT
      (boxAt N u₁) (boxAt N w) rfl (boxAt_sub_of_mem hTu (hNδ' T hT)) rfl
      (boxAt_sub_of_mem hT'w (hNδ' T' hT'))
    obtain ⟨s', hs'n, hws', hs'out⟩ := exists_out_sq hCN hwF.1 hwF.2
    obtain ⟨c, hcn, -, h1, h2⟩ := sq_join_of_mem (s := boxAt N w) (s' := s') hs'n.symm
      (mem_closedBox_boxAt hwF.2) hws'
    obtain ⟨Tc, hTc⟩ := cell c hcn
    obtain ⟨Ts, hTs⟩ := cell s' hs'n
    set S₀ := q.support.toFinset
    set S := insert Tc (insert Ts S₀)
    have hS₀ : S₀ ⊆ S := fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have hpin : ∀ t ≤ M, SqIn m δ' N S (p t) := by
      intro t ht
      obtain ⟨hn, -, hsub⟩ := hall t ht
      have hV := isCell_of_mem_support' hT q _ (q.getVert_mem_support (lab t))
      refine sqin1 S (p t) _ hn ⟨hV, (hNδ' _ hV).trans hn.ge, anc_eq_of_sub hn (hNδ' _ hV) hsub⟩
        (hS₀ (List.mem_toFinset.2 (q.getVert_mem_support (lab t))))
    have hreach : ∀ t ≤ M, Relation.ReflTransGen (fun a b => SqAdj a b ∧ SqIn m δ' N S b)
        (p 0) (p t) := by
      intro t
      induction t with
      | zero => intro _; exact .refl
      | succ t ih =>
        intro ht
        rcases (hsteps t (by omega)).1 with e | e
        · rw [← e]; exact ih (by omega)
        · exact (ih (by omega)).tail ⟨e, hpin (t + 1) ht⟩
    have hcin : SqIn m δ' N S c := sqin1 S c Tc hcn hTc (Finset.mem_insert_self _ _)
    have hs'in : SqIn m δ' N S s' :=
      sqin1 S s' Ts hs'n hTs (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hr1 : Relation.ReflTransGen (fun a b => SqAdj a b ∧ SqIn m δ' N S b) (p 0) c := by
      have := hreach M le_rfl
      rw [hpM] at this
      rcases h1 with e | e
      · rw [← e]; exact this
      · exact this.tail ⟨e, hcin⟩
    have hr2 : Relation.ReflTransGen (fun a b => SqAdj a b ∧ SqIn m δ' N S b) (p 0) s' := by
      rcases h2 with e | e
      · rw [← e]; exact hr1
      · exact hr1.tail ⟨e, hs'in⟩
    rw [hp0] at hr2
    obtain ⟨x, hxX, hx⟩ := hit_of_reach hr2 henc hs'out
    have h0in : SqIn m δ' N S (boxAt N u₁) := hp0 ▸ hpin 0 (Nat.zero_le _)
    refine ⟨S, ?_, u₁, rfl, x, hxX, cstep_of_reach h0in hx, h0in⟩
    have c1 : S.card ≤ S₀.card + 2 := by
      calc S.card ≤ (insert Ts S₀).card + 1 := Finset.card_insert_le _ _
        _ ≤ S₀.card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
    have c2 : S₀.card ≤ q.length + 1 := by
      rw [← q.length_support]; exact List.toFinset_card_le _
    have : (S.card : ℝ) ≤ ((q.length + 1 : ℕ) : ℝ) + 2 := by exact_mod_cast (by omega)
    linarith
  · -- the connected case (`ℂ_start = ∅`)
    obtain ⟨a, haA, haL⟩ := not_subset.1 (hnot C hC)
    have hreach := sq_reach_of_connected hconn.isPreconnected hAV N hu haA
    have hout : ¬ (boxAt N a).closedBox ⊆ C.largeBox := fun h =>
      haL (h (mem_closedBox_boxAt (hAV haA)))
    obtain ⟨x, hxX, hx⟩ := hit_of_reach hreach henc hout
    have hxA : (x.closedBox ∩ A).Nonempty := by
      clear hxX
      induction hx with
      | refl => exact ⟨u, mem_closedBox_boxAt (hAV hu), hu⟩
      | tail _ h _ => exact h.2
    obtain ⟨a', hxa', ha'⟩ := hxA
    have hxn := (hX x hxX).1
    obtain ⟨c, hcn, -, h1, h2⟩ := sq_join_of_mem (s := boxAt N a') (s' := x) hxn.symm
      (mem_closedBox_boxAt (hAV ha')) hxa'
    obtain ⟨T1, hT1⟩ := cell (boxAt N a') rfl
    obtain ⟨T2, hT2⟩ := cell c hcn
    obtain ⟨T3, hT3⟩ := cell x hxn
    set S : Finset DyBox := {T1, T2, T3}
    have i1 : SqIn m δ' N S (boxAt N a') := sqin1 S _ T1 rfl hT1 (by simp [S])
    have i2 : SqIn m δ' N S c := sqin1 S c T2 hcn hT2 (by simp [S])
    have i3 : SqIn m δ' N S x := sqin1 S x T3 hxn hT3 (by simp [S])
    refine ⟨S, ?_, a', ha', x, hxX, ?_, i1⟩
    · have : S.card ≤ 3 := Finset.card_le_three
      have : (S.card : ℝ) ≤ 3 := by exact_mod_cast this
      linarith
    · have r1 : Relation.ReflTransGen (CStep m δ' N S) (boxAt N a') c := by
        rcases h1 with e | e
        · rw [← e]
        · exact Relation.ReflTransGen.single ⟨e, i1, i2⟩
      rcases h2 with e | e
      · rw [← e]; exact r1
      · exact r1.tail ⟨e, i2, i3⟩

end DZZ
end LQGMetric
