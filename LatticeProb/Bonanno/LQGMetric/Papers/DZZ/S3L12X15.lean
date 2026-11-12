/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X14

/-!
# DZZ Lemma 3.12: `CoarseRingOfCross` (D93 §2, packet P-6a) and DZZ Lemma 3.12

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, the harder case
`𝖢_large ⊆ 𝕍°` (l. 1461–1477), Remark 3.15 (l. 1360–1363), ring form of DEC-93 §2 / D99:
the four cut crossings (`side_pkg`) meet at the corners (`side_meet'`) and are walked around
from the corner of the home region (`coarseRing_of_sideW`), in one of four orders according to
the position of the outer corner of `𝖢` (parities of its indices).

* `distinct_ends`, `rev_mem`; **`coarseRingOfCross_holds`**;
* **`dzz_lemma312_proved`**: DZZ Lemma 3.12 with no open hypothesis.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox PercClip

lemma distinct_ends {L : ℕ} {c : ℤ × ℤ} {e : PercDir} {N : ℤ} (hN : 0 < N)
    {X : List (ℤ × ℤ)} (hX0 : X ≠ []) (hg : ∀ z ∈ X, InGrid L c z)
    (h0 : ∀ a ∈ X.head?, annLong e a = -N) (hW : ∀ b ∈ X.getLast?, annLong e b = N) :
    ∃ z ∈ X, ∃ z' ∈ X, siteBox L c z ≠ siteBox L c z' := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hX0
  set b := (a :: l).getLast (List.cons_ne_nil _ _)
  have hb : b ∈ a :: l := List.getLast_mem _
  refine ⟨a, List.mem_cons_self, b, hb, fun heq => ?_⟩
  have e1 := h0 a rfl
  have e2 := hW b (List.getLast?_eq_some_getLast _)
  have j1 := siteBox_j (hg a List.mem_cons_self)
  have j2 := siteBox_j (hg b hb)
  have k1 := siteBox_k (hg a List.mem_cons_self)
  have k2 := siteBox_k (hg b hb)
  rw [heq] at j1 k1
  cases e <;> simp only [annLong] at e1 e2 <;> omega

lemma rev_mem {α : Type*} (A M B : List α) (z : α) (hz : z ∈ A ++ M ++ B) :
    z ∈ B.reverse ++ M.reverse ++ A.reverse := by
  simp only [List.mem_append, List.mem_reverse] at hz ⊢; tauto

/-- **DEC-93 packet P-6a, coarse form: proved.** -/
theorem coarseRingOfCross_holds : CoarseRingOfCross := by
  intro m δ C k d hC h1 hc hint
  obtain ⟨h, hK, hX⟩ := hc
  set N : ℤ := 2 * (h : ℤ) - 2 with hN
  set sb := siteBox (C.n + k) (l37c C h) with hsb
  set G : Set (ℤ × ℤ) := {z | InGrid (C.n + k) (l37c C h) z ∧
    (fun b' => ∀ bt ∈ boxCollBdry b' d, m bt < δ ^ 2) (sb z)} with hGdef
  have hG : ∀ z ∈ G, ∀ bt ∈ boxCollBdry (sb z) d, m bt < δ ^ 2 := fun z hz => hz.2
  have hact := fun e => active_of_interior hint hK e
  have hlo : ∀ e, clipLo N (l37ext (C.n + k) (l37c C h)) e = -N := fun e => by
    have := hact (clipLoDir e); unfold clipLo; omega
  have hhi : ∀ e, clipHi N (l37ext (C.n + k) (l37c C h)) e = N := fun e => by
    have := hact (clipHiDir e); unfold clipHi; omega
  have hX' : ∀ e, PercClipCross ((h : ℤ) + 2) N e (-N) N G := by
    intro e; have h0 := hX e (hact e); rw [hlo, hhi] at h0; exact h0
  have hh4 : 4 ≤ h := by
    obtain ⟨a, -, -, -, ⟨-, -, a1, a2⟩, -⟩ := hX' .T
    simp only [annDir] at a1 a2; omega
  have hh1 : 1 ≤ h := by omega
  have hh2 : 2 ≤ h := by omega
  have hn0 : (0 : ℤ) ≤ h + 2 := by positivity
  have hnN : (h : ℤ) + 2 ≤ N := by omega
  set sx := spl C.j h with hsx
  set sy := spl C.k h with hsy
  obtain ⟨sx1, sx2⟩ := spl_bounds C.j h
  obtain ⟨sy1, sy2⟩ := spl_bounds C.k h
  have hbx : ∀ a b : ℤ, (a = -N ∨ a = N) → (b = -N ∨ b = N) → annBox N (a, b) := by
    intro a b ha hb; simp only [annBox]; omega
  have hgr : ∀ a b : ℤ, (a = -N ∨ a = N) → (b = -N ∨ b = N) →
      InGrid (C.n + k) (l37c C h) (a, b) :=
    fun a b ha hb => inGrid_of_interior hK hh1 hint (hbx a b ha hb)
  -- the four sides
  obtain ⟨AB, MB, BB, neB, chB, h0B, hWB, rB, mB, aB, bB, eB, loB, hiB⟩ :=
    side_pkg (m := m) (δ := δ) (G := G) h1 hK hh1 hint .B (s := sx) (by omega) (by omega)
      (hX' .B) (hbx (-N) (-N) (Or.inl rfl) (Or.inl rfl)) (hbx N (-N) (Or.inr rfl) (Or.inl rfl))
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩,
          farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩⟩)
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩,
          farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩⟩)
  obtain ⟨AR, MR, BR, neR, chR, h0R, hWR, rR, mR, aR, bR, eR, loR, hiR⟩ :=
    side_pkg (m := m) (δ := δ) (G := G) h1 hK hh1 hint .R (s := sy) (by omega) (by omega)
      (hX' .R) (hbx N (-N) (Or.inr rfl) (Or.inl rfl)) (hbx N N (Or.inr rfl) (Or.inr rfl))
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩,
          farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩⟩)
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩,
          farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩⟩)
  obtain ⟨AT, MT, BT, neT, chT, h0T, hWT, rT, mT, aT, bT, eT, loT, hiT⟩ :=
    side_pkg (m := m) (δ := δ) (G := G) h1 hK hh1 hint .T (s := sx) (by omega) (by omega)
      (hX' .T) (hbx (-N) N (Or.inl rfl) (Or.inr rfl)) (hbx N N (Or.inr rfl) (Or.inr rfl))
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩,
          farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩⟩)
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩,
          farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩⟩)
  obtain ⟨AL, ML, BL, neL, chL, h0L, hWL, rL, mL, aL, bL, eL, loL, hiL⟩ :=
    side_pkg (m := m) (δ := δ) (G := G) h1 hK hh1 hint .L (s := sy) (by omega) (by omega)
      (hX' .L) (hbx (-N) (-N) (Or.inl rfl) (Or.inl rfl)) (hbx (-N) N (Or.inl rfl) (Or.inr rfl))
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩,
          farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩⟩)
      (by
        intro z hz hzs; obtain ⟨⟨a1, a2, a3, a4⟩, hd⟩ := hz; simp only [annLong, annDir] at hzs hd
        exact ⟨farB_eq ⟨fun _ => by dsimp only; omega, fun _ => by omega⟩,
          farB_eq ⟨fun h' => by omega, fun h' => by dsimp only at h'; omega⟩⟩)
  -- the meeting points
  obtain ⟨mBR, hBR1, hBR2⟩ := side_meet' (d := .B) (e := .R) hn0 hnN (Or.inr rfl) (Or.inl rfl)
    neB neR chB chR rB rR h0B hWB h0R hWR
  obtain ⟨mTR, hTR1, hTR2⟩ := side_meet' (d := .T) (e := .R) hn0 hnN (Or.inl rfl) (Or.inl rfl)
    neT neR chT chR rT rR h0T hWT h0R hWR
  obtain ⟨mTL, hTL1, hTL2⟩ := side_meet' (d := .T) (e := .L) hn0 hnN (Or.inl rfl) (Or.inr rfl)
    neT neL chT chL rT rL h0T hWT h0L hWL
  obtain ⟨mBL, hBL1, hBL2⟩ := side_meet' (d := .B) (e := .L) hn0 hnN (Or.inr rfl) (Or.inr rfl)
    neB neL chB chL rB rL h0B hWB h0L hWL
  have lBL_B := loB mBL hBL1 (by have := (rL mBL hBL2).2; simp only [annLong, annDir] at this ⊢; omega)
  have lBR_B := hiB mBR hBR1 (by have := (rR mBR hBR2).2; simp only [annLong, annDir] at this ⊢; omega)
  have lBR_R := loR mBR hBR2 (by have := (rB mBR hBR1).2; simp only [annLong, annDir] at this ⊢; omega)
  have lTR_R := hiR mTR hTR2 (by have := (rT mTR hTR1).2; simp only [annLong, annDir] at this ⊢; omega)
  have lTR_T := hiT mTR hTR1 (by have := (rR mTR hTR2).2; simp only [annLong, annDir] at this ⊢; omega)
  have lTL_T := loT mTL hTL1 (by have := (rL mTL hTL2).2; simp only [annLong, annDir] at this ⊢; omega)
  have lTL_L := hiL mTL hTL2 (by have := (rT mTL hTL1).2; simp only [annLong, annDir] at this ⊢; omega)
  have lBL_L := loL mBL hBL2 (by have := (rB mBL hBL1).2; simp only [annLong, annDir] at this ⊢; omega)
  -- the walk sides
  have W₁ := sideW_fwd hK hh1 hint hG chB rB mB aB bB eB lBL_B lBR_B
  have W₂ := sideW_fwd hK hh1 hint hG chR rR mR aR bR eR lBR_R lTR_R
  have W₃ := sideW_rev hK hh1 hint hG chT rT mT aT bT eT lTR_T lTL_T
  have W₄ := sideW_rev hK hh1 hint hG chL rL mL aL bL eL lTL_L lBL_L
  -- separation
  have hsepAll : ∀ M' : Set DyBox, (∀ z ∈ AB ++ MB ++ BB, sb z ∈ M') →
      (∀ z ∈ AR ++ MR ++ BR, sb z ∈ M') → (∀ z ∈ AT ++ MT ++ BT, sb z ∈ M') →
      (∀ z ∈ AL ++ ML ++ BL, sb z ∈ M') → EnclosesBox C M' := by
    intro M' hB' hR' hT' hL'
    refine enclosesBox_of_hasCross (k := k) h1 ⟨h, hK, fun e he => ?_⟩
    rw [hlo, hhi]
    have gr : ∀ (X : List (ℤ × ℤ)) (e' : PercDir), (∀ z ∈ X, z ∈ annRect ((h : ℤ) + 2) N e') →
        ∀ z ∈ X, InGrid (C.n + k) (l37c C h) z :=
      fun X e' hX z hz => inGrid_of_interior hK hh1 hint (hX z hz).1
    cases e
    · exact cross_of_list hn0 neT chT rT (fun z hz => ⟨gr _ _ rT z hz, hT' z hz⟩) h0T hWT
    · exact cross_of_list hn0 neB chB rB (fun z hz => ⟨gr _ _ rB z hz, hB' z hz⟩) h0B hWB
    · exact cross_of_list hn0 neR chR rR (fun z hz => ⟨gr _ _ rR z hz, hR' z hz⟩) h0R hWR
    · exact cross_of_list hn0 neL chL rL (fun z hz => ⟨gr _ _ rL z hz, hL' z hz⟩) h0L hWL
  -- distinct boxes on each side
  have hN0 : (0 : ℤ) < N := by omega
  have gr' : ∀ (X : List (ℤ × ℤ)) (e' : PercDir), (∀ z ∈ X, z ∈ annRect ((h : ℤ) + 2) N e') →
      ∀ z ∈ X, InGrid (C.n + k) (l37c C h) z :=
    fun X e' hX z hz => inGrid_of_interior hK hh1 hint (hX z hz).1
  have dB := distinct_ends hN0 neB (gr' _ _ rB) h0B hWB
  have dR := distinct_ends hN0 neR (gr' _ _ rR) h0R hWR
  have dT := distinct_ends hN0 neT (gr' _ _ rT) h0T hWT
  have dL := distinct_ends hN0 neL (gr' _ _ rL) h0L hWL
  have drev : ∀ A M B : List (ℤ × ℤ), (∃ z ∈ A ++ M ++ B, ∃ z' ∈ A ++ M ++ B, sb z ≠ sb z') →
      ∃ z ∈ B.reverse ++ M.reverse ++ A.reverse, ∃ z' ∈ B.reverse ++ M.reverse ++ A.reverse,
        sb z ≠ sb z' := by
    rintro A M B ⟨z, hz, z', hz', hne⟩
    exact ⟨z, rev_mem A M B z hz, z', rev_mem A M B z' hz', hne⟩
  -- the home corner and the corners next to it
  have hhome : ∀ a b : ℤ, (a = -N ∨ a = N) → (b = -N ∨ b = N) → farB C.j h a = false →
      farB C.k h b = false → ∀ P, IsParent m δ C P → ¬ (sb (a, b)).closedBox ⊆ P.closedBox :=
    fun a b ha hb hxa hyb P hP => home_not_parent hC h1 hK hh1 (hgr a b ha hb) (hbx a b ha hb)
      hxa hyb P hP
  have fpos : ∀ j : ℕ, farB j h (-N) = decide (j % 2 ≠ 1) := by
    intro j; unfold farB; split_ifs with hj <;> simp [hj] <;> omega
  have fneg : ∀ j : ℕ, farB j h N = decide (j % 2 = 1) := by
    intro j; unfold farB; split_ifs with hj <;> simp [hj] <;> omega
  have opp : ∀ a b a' b' : ℤ, (a = -N ∧ a' = N ∨ a = N ∧ a' = -N) →
      (b = -N ∧ b' = N ∨ b = N ∧ b' = -N) → ∀ P, IsParent m δ C P →
      (sb (a, b)).closedBox ⊆ P.closedBox → (sb (a', b')).closedBox ⊆ P.closedBox → False := by
    intro a b a' b' hx hy P hP h₁ h₂
    have ga : a = -N ∨ a = N := by omega
    have ga' : a' = -N ∨ a' = N := by omega
    have gb : b = -N ∨ b = N := by omega
    have gb' : b' = -N ∨ b' = N := by omega
    exact not_parent_opposite hC hK hh2 hP (hgr a b ga gb) (hgr a' b' ga' gb') hx hy h₁ h₂
  rcases Nat.mod_two_eq_zero_or_one C.j with hj | hj <;>
    rcases Nat.mod_two_eq_zero_or_one C.k with hk | hk
  · -- home `TR`
    exact coarseRing_of_sideW hK W₃ W₄ W₁ W₂
      (hhome N N (Or.inr rfl) (Or.inr rfl) (by rw [fneg]; simp [hj]) (by rw [fneg]; simp [hk]))
      (opp (-N) N N (-N) (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩))
      (fun M' a b c e => hsepAll M' c e (fun z hz => a z (rev_mem _ _ _ z hz))
        (fun z hz => b z (rev_mem _ _ _ z hz)))
      (drev _ _ _ dT)
  · -- home `BR`
    exact coarseRing_of_sideW hK W₂ W₃ W₄ W₁
      (hhome N (-N) (Or.inr rfl) (Or.inl rfl) (by rw [fneg]; simp [hj]) (by rw [fpos]; simp [hk]))
      (opp N N (-N) (-N) (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩))
      (fun M' a b c e => hsepAll M' e a (fun z hz => b z (rev_mem _ _ _ z hz))
        (fun z hz => c z (rev_mem _ _ _ z hz)))
      dR
  · -- home `TL`
    exact coarseRing_of_sideW hK W₄ W₁ W₂ W₃
      (hhome (-N) N (Or.inl rfl) (Or.inr rfl) (by rw [fpos]; simp [hj]) (by rw [fneg]; simp [hk]))
      (opp (-N) (-N) N N (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩))
      (fun M' a b c e => hsepAll M' b c (fun z hz => e z (rev_mem _ _ _ z hz))
        (fun z hz => a z (rev_mem _ _ _ z hz)))
      (drev _ _ _ dL)
  · -- home `BL`
    exact coarseRing_of_sideW hK W₁ W₂ W₃ W₄
      (hhome (-N) (-N) (Or.inl rfl) (Or.inl rfl) (by rw [fpos]; simp [hj]) (by rw [fpos]; simp [hk]))
      (opp N (-N) (-N) N (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩))
      (fun M' a b c e => hsepAll M' a b (fun z hz => c z (rev_mem _ _ _ z hz))
        (fun z hz => e z (rev_mem _ _ _ z hz)))
      dB

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  {W : WhiteNoise.WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.12** (no open hypothesis). -/
theorem dzz_lemma312_proved (hW : WhiteNoise.IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : DZZLemma312 P γ W :=
  dzz_lemma312_of_coarseRing hW hγ hγ2 coarseRingOfCross_holds

end DZZ
end LQGMetric
