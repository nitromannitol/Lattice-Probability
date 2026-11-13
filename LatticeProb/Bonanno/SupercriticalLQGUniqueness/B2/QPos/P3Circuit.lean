/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Circuit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3TubeGeom

 






set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 

theorem sum_Ico_crossVal_zero (w : ℕ → ℤ × ℤ) (c : ℤ × ℤ) (a b : ℕ)
    (h : ∀ k, a ≤ k → k < b → crossVal c (w k) (w (k + 1)) = 0) :
    ∑ k ∈ Ico a b, crossVal c (w k) (w (k + 1)) = 0 :=
  sum_eq_zero (fun k hk => by rw [mem_Ico] at hk; exact h k hk.1 hk.2)

theorem sum_Ico_crossVal_above (w : ℕ → ℤ × ℤ) (hw : ∀ k, latticeAdjacent (w k) (w (k + 1)))
    (c : ℤ × ℤ) (a b : ℕ) (hab : a ≤ b) (h : ∀ k, a ≤ k → k < b → c.2 < (w k).2) :
    ∑ k ∈ Ico a b, crossVal c (w k) (w (k + 1)) = rightInd c (w b) - rightInd c (w a) := by
  rw [sum_Ico_eq_sum_range]
  have := sum_crossVal_above w hw c a (b - a) (fun i hi => h (a + i) (by omega) (by omega))
  rw [show a + (b - a) = b by omega] at this
  rw [← this]

 
def InShell (j : ℕ) (v : ℤ × ℤ) : Prop :=
  |v.1| ≤ 44161 * j ∧ |v.2| ≤ 44161 * j ∧ (36735 * (j : ℤ) ≤ |v.1| ∨ 36735 * (j : ℤ) ≤ |v.2|)

section Boxes

variable {j : ℕ} {z : ℤ × ℤ} {v : ℤ × ℤ}

theorem segBox_0 (hj : 1 ≤ j) (hz : 41 * (1024 * (j : ℤ)) ≤ z.1 ∧ z.1 ≤ 43 * (1024 * (j : ℤ)) ∧
      |z.2| ≤ 1024 * (j : ℤ)) (hv : SegBox (1024 * j) (129 * j) z 0 v) :
    36735 * (j : ℤ) ≤ v.1 ∧ v.1 ≤ 44161 * j ∧ |v.2| ≤ 1153 * j := by
  obtain ⟨h1, h2, h3⟩ := hz
  have h3' := abs_le.mp h3
  simp only [SegBox, routeW] at hv
  obtain ⟨a1, a2, a3, a4⟩ := hv
  rw [abs_le]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | (have := min_le_right z.1 (36 * (1024 * (j : ℤ))); have := min_le_left z.1 (36 * (1024 * (j : ℤ)));
       rcases min_cases z.1 (36 * (1024 * (j : ℤ))) with ⟨e, _⟩ | ⟨e, _⟩ <;>
       rcases max_cases z.1 (36 * (1024 * (j : ℤ))) with ⟨e', _⟩ | ⟨e', _⟩ <;>
       rcases min_cases z.2 0 with ⟨f, _⟩ | ⟨f, _⟩ <;>
       rcases max_cases z.2 0 with ⟨f', _⟩ | ⟨f', _⟩ <;>
       simp only [e, e', f, f'] at a1 a2 a3 a4 <;> omega)

theorem segBox_1 (hj : 1 ≤ j) (hv : SegBox (1024 * j) (129 * j) z 1 v) :
    36735 * (j : ℤ) ≤ v.1 ∧ v.1 ≤ 36993 * j ∧ -129 * (j : ℤ) ≤ v.2 ∧ v.2 ≤ 36993 * j := by
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  obtain ⟨a1, a2, a3, a4⟩ := hv
  simp only [routeW] at a1 a2 a3 a4
  simp only [min_def, max_def] at a1 a2 a3 a4
  split_ifs at a1 a2 a3 a4 <;> omega

theorem segBox_2 (hj : 1 ≤ j) (hv : SegBox (1024 * j) (129 * j) z 2 v) :
    36735 * (j : ℤ) ≤ v.2 ∧ v.2 ≤ 36993 * j ∧ -36993 * (j : ℤ) ≤ v.1 ∧ v.1 ≤ 36993 * j := by
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  obtain ⟨a1, a2, a3, a4⟩ := hv
  simp only [routeW] at a1 a2 a3 a4
  simp only [min_def, max_def] at a1 a2 a3 a4
  split_ifs at a1 a2 a3 a4 <;> omega

theorem segBox_3 (hj : 1 ≤ j) (hv : SegBox (1024 * j) (129 * j) z 3 v) :
    v.1 ≤ -36735 * (j : ℤ) ∧ -36993 * (j : ℤ) ≤ v.1 ∧ -36993 * (j : ℤ) ≤ v.2 ∧ v.2 ≤ 36993 * j := by
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  obtain ⟨a1, a2, a3, a4⟩ := hv
  simp only [routeW] at a1 a2 a3 a4
  simp only [min_def, max_def] at a1 a2 a3 a4
  split_ifs at a1 a2 a3 a4 <;> omega

theorem segBox_4 (hj : 1 ≤ j) (hv : SegBox (1024 * j) (129 * j) z 4 v) :
    v.2 ≤ -36735 * (j : ℤ) ∧ -36993 * (j : ℤ) ≤ v.2 ∧ -36993 * (j : ℤ) ≤ v.1 ∧
      v.1 ≤ 40065 * j := by
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  obtain ⟨a1, a2, a3, a4⟩ := hv
  simp only [routeW] at a1 a2 a3 a4
  simp only [min_def, max_def] at a1 a2 a3 a4
  split_ifs at a1 a2 a3 a4 <;> omega

theorem segBox_5 (hj : 1 ≤ j) (hv : SegBox (1024 * j) (129 * j) z 5 v) :
    39807 * (j : ℤ) ≤ v.1 ∧ v.1 ≤ 40065 * j ∧ -36993 * (j : ℤ) ≤ v.2 ∧ v.2 ≤ 6273 * j := by
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  obtain ⟨a1, a2, a3, a4⟩ := hv
  simp only [routeW] at a1 a2 a3 a4
  simp only [min_def, max_def] at a1 a2 a3 a4
  split_ifs at a1 a2 a3 a4 <;> omega

end Boxes

 


theorem tube_circuit (j : ℕ) (hj : 1 ≤ j) (z : ℤ × ℤ)
    (hz : 41 * (1024 * (j : ℤ)) ≤ z.1 ∧ z.1 ≤ 43 * (1024 * (j : ℤ)) ∧ |z.2| ≤ 1024 * (j : ℤ))
    (ω : Fin (64 * j ^ 2 * (6 * mB)) → Bool × Bool)
    (hT : TubeGood j (64 * j ^ 2) (routeP (1024 * j) z mB) z (6 * mB) ω) :
    (∀ k ≤ 64 * j ^ 2 * (6 * mB), InShell j (wpos z ω k)) ∧
    ∃ l : List (ℤ × ℤ), l.IsChain latticeAdjacent ∧ IsClosed l ∧ l.dropLast.Nodup ∧
      wind (0, 0) l ≠ 0 ∧ (∀ v ∈ l, ∃ k ≤ 64 * j ^ 2 * (6 * mB), wpos z ω k = v) := by
  have htpos : 0 < 64 * j ^ 2 := by positivity
  have hm := mB_pos
  have hw : ∀ k, latticeAdjacent (wpos z ω k) (wpos z ω (k + 1)) := fun k => wpos_adj z ω k
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  obtain ⟨mt, hmt⟩ : ∃ mt, mt = mB * (64 * j ^ 2) := ⟨_, rfl⟩
  have hmtpos : 0 < mt := by rw [hmt]; positivity
  have hN : 64 * j ^ 2 * (6 * mB) = 6 * mt := by rw [hmt]; ring
  have hseg : ∀ q < 6, ∀ k, q * mt ≤ k → k ≤ (q + 1) * mt →
      SegBox (1024 * j) (129 * j) z q (wpos z ω k) := by
    intro q hq k h1 h2
    refine tube_segBox htpos hm hT q hq k ?_ ?_
    · rw [hmt] at h1; linarith [mul_assoc q mB (64 * j ^ 2)]
    · rw [hmt] at h2; linarith [mul_assoc (q + 1) mB (64 * j ^ 2)]
  have hnode : ∀ q, 1 ≤ q → q ≤ 6 →
      |(wpos z ω (q * mt)).1 - (routeW (1024 * j) z q).1| ≤ j ∧
        |(wpos z ω (q * mt)).2 - (routeW (1024 * j) z q).2| ≤ j := by
    intro q h1 h2
    have := tube_node hm hT q h1 h2
    rw [show q * mB * (64 * j ^ 2) = q * mt by rw [hmt]; ring] at this
    exact this
  
  have B0 : ∀ k ≤ mt, 36735 * (j : ℤ) ≤ (wpos z ω k).1 ∧ (wpos z ω k).1 ≤ 44161 * j ∧
      |(wpos z ω k).2| ≤ 1153 * j :=
    fun k hk => segBox_0 hj hz (hseg 0 (by norm_num) k (by simp) (by simpa using hk))
  have B1 : ∀ k, mt ≤ k → k ≤ 2 * mt → _ := fun k h1 h2 =>
    segBox_1 hj (hseg 1 (by norm_num) k (by simpa using h1) h2)
  have B2 : ∀ k, 2 * mt ≤ k → k ≤ 3 * mt → _ := fun k h1 h2 =>
    segBox_2 hj (hseg 2 (by norm_num) k h1 h2)
  have B3 : ∀ k, 3 * mt ≤ k → k ≤ 4 * mt → _ := fun k h1 h2 =>
    segBox_3 hj (hseg 3 (by norm_num) k h1 h2)
  have B4 : ∀ k, 4 * mt ≤ k → k ≤ 5 * mt → _ := fun k h1 h2 =>
    segBox_4 hj (hseg 4 (by norm_num) k h1 h2)
  have B5 : ∀ k, 5 * mt ≤ k → k ≤ 6 * mt → _ := fun k h1 h2 =>
    segBox_5 hj (hseg 5 (by norm_num) k h1 h2)
  
  have hshell : ∀ k ≤ 6 * mt, InShell j (wpos z ω k) := by
    intro k hk
    unfold InShell
    by_cases c1 : k ≤ mt
    · obtain ⟨a, b, c⟩ := B0 k c1
      rw [abs_le] at c; simp only [abs_le]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ?_⟩
      rw [abs_of_nonneg (by omega)]; exact a
    by_cases c2 : k ≤ 2 * mt
    · obtain ⟨a, b, c, d⟩ := B1 k (by omega) c2
      simp only [abs_le]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ?_⟩
      rw [abs_of_nonneg (by omega)]; exact a
    by_cases c3 : k ≤ 3 * mt
    · obtain ⟨a, b, c, d⟩ := B2 k (by omega) c3
      simp only [abs_le]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ?_⟩
      rw [abs_of_nonneg (by omega)]; exact a
    by_cases c4 : k ≤ 4 * mt
    · obtain ⟨a, b, c, d⟩ := B3 k (by omega) c4
      simp only [abs_le]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ?_⟩
      rw [abs_of_neg (by omega)]; omega
    by_cases c5 : k ≤ 5 * mt
    · obtain ⟨a, b, c, d⟩ := B4 k (by omega) c5
      simp only [abs_le]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ?_⟩
      rw [abs_of_neg (by omega)]; omega
    · obtain ⟨a, b, c, d⟩ := B5 k (by omega) hk
      simp only [abs_le]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ?_⟩
      rw [abs_of_nonneg (by omega)]; omega
  refine ⟨fun k hk => hshell k (hN ▸ hk), ?_⟩
  
  have n1x := (hnode 1 le_rfl (by norm_num)).1
  have n2x := (hnode 2 (by norm_num) (by norm_num)).1
  have n3x := (hnode 3 (by norm_num) (by norm_num)).1
  have n5y := (hnode 5 (by norm_num) (by norm_num)).2
  have n6y := (hnode 6 (by norm_num) (by norm_num)).2
  simp only [routeW, one_mul] at n1x n2x n3x n5y n6y
  rw [abs_le] at n1x n2x n3x n5y n6y
  
  obtain ⟨i, hi, i', hi', heq⟩ := strip_crossing (wpos z ω) hw 0 mt (5 * mt) mt
    (1153 * j) (39936 * j) (129 * j) (6273 * j + 1)
    (fun i hi => by simpa using (B0 (0 + i) (by simpa using hi)).2.2)
    (by rw [wpos_zero]; omega)
    (by rw [zero_add]; omega)
    (fun i hi => by
      obtain ⟨a, b, c, d⟩ := B5 (5 * mt + i) (by omega) (by omega)
      exact ⟨by rw [abs_le]; constructor <;> omega, by omega⟩)
    (by omega)
    (by rw [show 5 * mt + mt = 6 * mt by ring]; omega)
    (by omega)
  simp only [zero_add] at heq
  obtain ⟨s, hs⟩ : ∃ s, s = i := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = 5 * mt + i' := ⟨_, rfl⟩
  rw [← hs, ← hs'] at heq
  have hss' : s ≤ s' := by omega
  have hchain : (seg (wpos z ω) s (s' - s)).IsChain latticeAdjacent := seg_isChain _ hw s _
  have hcl : IsClosed (seg (wpos z ω) s (s' - s)) := by
    refine ⟨seg_ne_nil _ _ _, ?_⟩
    rw [seg_head?, seg_getLast?, show s + (s' - s) = s' by omega, heq]
  
  have hwind : wind (0, 0) (seg (wpos z ω) s (s' - s)) = -1 := by
    unfold wind
    rw [stepSum_seg]
    have e : ∑ a ∈ range (s' - s), crossVal (0, 0) (wpos z ω (s + a)) (wpos z ω (s + a + 1)) =
        ∑ k ∈ Ico s s', crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) := by
      rw [sum_Ico_eq_sum_range]
    rw [e, ← sum_Ico_consecutive _ (show s ≤ mt by omega) (show mt ≤ s' by omega),
      ← sum_Ico_consecutive _ (show mt ≤ 2 * mt by omega) (show 2 * mt ≤ s' by omega),
      ← sum_Ico_consecutive _ (show 2 * mt ≤ 3 * mt by omega) (show 3 * mt ≤ s' by omega),
      ← sum_Ico_consecutive _ (show 3 * mt ≤ 4 * mt by omega) (show 4 * mt ≤ s' by omega),
      ← sum_Ico_consecutive _ (show 4 * mt ≤ 5 * mt by omega) (show 5 * mt ≤ s' by omega)]
    have z0 : ∑ k ∈ Ico s mt, crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) = 0 := by
      apply sum_Ico_crossVal_zero; intro k h1 h2
      apply crossVal_eq_zero_of_right
      · have := (B0 k (by omega)).1; show (0 : ℤ) + 1 ≤ _; omega
      · have := (B0 (k + 1) (by omega)).1; show (0 : ℤ) + 1 ≤ _; omega
    have z1 : ∑ k ∈ Ico mt (2 * mt), crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) = 0 := by
      apply sum_Ico_crossVal_zero; intro k h1 h2
      apply crossVal_eq_zero_of_right
      · have := (B1 k h1 (by omega)).1; show (0 : ℤ) + 1 ≤ _; omega
      · have := (B1 (k + 1) (by omega) (by omega)).1; show (0 : ℤ) + 1 ≤ _; omega
    have z2 : ∑ k ∈ Ico (2 * mt) (3 * mt), crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) =
        -1 := by
      rw [sum_Ico_crossVal_above (wpos z ω) hw (0, 0) _ _ (by omega) (fun k h1 h2 => by
        have := (B2 k h1 (by omega)).1
        show (0 : ℤ) < _; omega)]
      simp only [rightInd]
      rw [if_neg (by show ¬ ((0 : ℤ) + 1 ≤ _); omega), if_pos (by show (0 : ℤ) + 1 ≤ _; omega)]
      norm_num
    have z3 : ∑ k ∈ Ico (3 * mt) (4 * mt), crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) = 0 := by
      apply sum_Ico_crossVal_zero; intro k h1 h2
      apply crossVal_eq_zero_of_left
      · have := (B3 k h1 (by omega)).1; show _ ≤ (0 : ℤ); omega
      · have := (B3 (k + 1) (by omega) (by omega)).1; show _ ≤ (0 : ℤ); omega
    have z4 : ∑ k ∈ Ico (4 * mt) (5 * mt), crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) = 0 := by
      apply sum_Ico_crossVal_zero; intro k h1 h2
      apply crossVal_eq_zero_of_below
      have := (B4 k h1 (by omega)).1
      show _ ≤ (0 : ℤ); omega
    have z5 : ∑ k ∈ Ico (5 * mt) s', crossVal (0, 0) (wpos z ω k) (wpos z ω (k + 1)) = 0 := by
      apply sum_Ico_crossVal_zero; intro k h1 h2
      apply crossVal_eq_zero_of_right
      · have := (B5 k h1 (by omega)).1; show (0 : ℤ) + 1 ≤ _; omega
      · have := (B5 (k + 1) (by omega) (by omega)).1; show (0 : ℤ) + 1 ≤ _; omega
    rw [z0, z1, z2, z3, z4, z5]; norm_num
  obtain ⟨l', h1, h2, h3, h4, h5⟩ := exists_simple_loop (0, 0) _ _ le_rfl hchain hcl
    (by rw [hwind]; norm_num)
  refine ⟨l', h1, h2, h3, h5, ?_⟩
  intro v hv
  obtain ⟨a, ha, hva⟩ := mem_seg.mp (h4 v hv)
  exact ⟨s + a, by rw [hN]; omega, hva⟩

end SupercriticalLQGUniqueness.B2.QPos.P3
