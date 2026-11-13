/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2FlipBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2BoxGreen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2FlipReal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2BoxGraph
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree

 







set_option autoImplicit false
noncomputable section

open Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

open WiredConductances

variable (n : ℕ)

abbrev BoxHE (n : ℕ) := DGFFSite n × Fin 4

theorem boxEdgeGraph_precision_diag (v : DGFFSite n) :
    (boxEdgeGraph n).toWired.precision v v = 4 * dgffConductance := by
  rw [boxEdgeGraph_toWired, precision_diag, box_totalRate_eq]
  unfold dgffConductance
  field_simp
  ring

theorem boxEdgeGraph_posDef : (boxEdgeGraph n).toWired.precision.PosDef := by
  rw [boxEdgeGraph_toWired]; exact box_precision_posDef n

theorem boxHalfCond_le (h : BoxHE n) : boxHalfCond n h ≤ dgffConductance := by
  unfold boxHalfCond; split_ifs <;> linarith [dgffConductance_pos]

theorem boxHalfCond_ge (h : BoxHE n) : dgffConductance / 2 ≤ boxHalfCond n h := by
  unfold boxHalfCond; split_ifs <;> linarith [dgffConductance_pos]

theorem boxHalfCond_of_none {h : BoxHE n} (hh : boxNbr n h.1 h.2 = none) :
    boxHalfCond n h = dgffConductance := by
  unfold boxHalfCond; rw [if_pos hh]

 
def tInt (M t : ℝ) : ℝ := 4 * M * dgffConductance * t / ((M / 4) ^ 2 * Real.sqrt (M / 4))

 
def tBdry (M t : ℝ) (J j : ℕ) : ℝ :=
  if j ≤ J then Real.exp (-(4 * M * dgffConductance * t / (1 + 4 * j)))
  else 4 * M * dgffConductance * t / (((j : ℝ) ^ 2 / M) ^ 2 * Real.sqrt ((j : ℝ) ^ 2 / M))

variable {n}

 
def posAvg (M : ℕ) (hM : 2 ≤ M) (u : ℝ) (h : BoxHE n) (q : ℕ) : ℝ :=
  EdgeGraph.vertexAvg ((boxEdgeGraph n).subdiv M hM) (M * boxHalfCond n h) u (u ^ 2 / 2)
    ((boxEdgeGraph n).subPos M h q)

theorem posAvg_nonneg (M : ℕ) (hM : 2 ≤ M) (u : ℝ) (h : BoxHE n) (q : ℕ) :
    0 ≤ posAvg M hM u h q := by
  unfold posAvg
  have hκ : 0 < (M : ℝ) * boxHalfCond n h :=
    mul_pos (by exact_mod_cast (show 0 < M by omega)) ((boxEdgeGraph n).cond_pos h)
  cases ho : (boxEdgeGraph n).subPos M h q with
  | none => exact (Real.exp_pos _).le
  | some p =>
    simp only [EdgeGraph.vertexAvg]
    exact flipBound_nonneg (by positivity)
      (mul_pos (by positivity) (((boxEdgeGraph n).subdiv M hM).toWired.green_diag_pos
        ((boxEdgeGraph n).subdiv_posDef M hM (boxEdgeGraph_posDef n)) p))

theorem kappa_facts (M : ℕ) (hM : 2 ≤ M) (h : BoxHE n) :
    0 < (M : ℝ) * boxHalfCond n h ∧ (M : ℝ) * boxHalfCond n h ≤ M * dgffConductance ∧
      (M : ℝ) * dgffConductance / 2 ≤ (M : ℝ) * boxHalfCond n h := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  refine ⟨mul_pos hM0 ((boxEdgeGraph n).cond_pos h),
    mul_le_mul_of_nonneg_left (boxHalfCond_le n h) hM0.le, ?_⟩
  have := mul_le_mul_of_nonneg_left (boxHalfCond_ge n h) hM0.le
  linarith

 
theorem flip_good_le (M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) (h : BoxHE n)
    (p : EdgeGraph.SubV (DGFFSite n) (BoxHE n) M)
    (hS : (M : ℝ) / 4 ≤ 4 * ((M : ℝ) * boxHalfCond n h) *
      ((boxEdgeGraph n).subdiv M hM).toWired.green p p) :
    flipBound (4 * ((M : ℝ) * boxHalfCond n h) * (u ^ 2 / 2))
        (4 * ((M : ℝ) * boxHalfCond n h) * ((boxEdgeGraph n).subdiv M hM).toWired.green p p) ≤
      tInt M (u ^ 2 / 2) := by
  obtain ⟨hκ0, hκle, -⟩ := kappa_facts M hM h
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ht : 0 < u ^ 2 / 2 := by positivity
  have hS0 : (0 : ℝ) < M / 4 := by positivity
  have hA0 : 0 ≤ 4 * ((M : ℝ) * boxHalfCond n h) * (u ^ 2 / 2) := by positivity
  have hA : 4 * ((M : ℝ) * boxHalfCond n h) * (u ^ 2 / 2) ≤
      4 * M * dgffConductance * (u ^ 2 / 2) := by nlinarith
  refine (flipBound_le_pow hA0 (lt_of_lt_of_le hS0 hS)).trans ?_
  refine (pow_bound_anti hA0 hS0 hS).trans ?_
  unfold tInt
  exact div_le_div_of_nonneg_right hA (by positivity)

theorem flip_inl_le (M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) (h : BoxHE n) (v : DGFFSite n) :
    flipBound (4 * ((M : ℝ) * boxHalfCond n h) * (u ^ 2 / 2))
        (4 * ((M : ℝ) * boxHalfCond n h) *
          ((boxEdgeGraph n).subdiv M hM).toWired.green (Sum.inl v) (Sum.inl v)) ≤
      tInt M (u ^ 2 / 2) := by
  apply flip_good_le M hM hu h
  obtain ⟨-, -, hκge⟩ := kappa_facts M hM h
  have hG := (boxEdgeGraph n).green_inl_ge M hM (boxEdgeGraph_posDef n) v
  rw [boxEdgeGraph_precision_diag] at hG
  have hGp := ((boxEdgeGraph n).subdiv M hM).toWired.green_diag_pos
    ((boxEdgeGraph n).subdiv_posDef M hM (boxEdgeGraph_posDef n)) (Sum.inl v)
  have hc := dgffConductance_pos
  set G := ((boxEdgeGraph n).subdiv M hM).toWired.green (Sum.inl v) (Sum.inl v)
  set κ := (M : ℝ) * boxHalfCond n h
  have h1 : 4 * (M * dgffConductance / 2) * G ≤ 4 * κ * G := by nlinarith
  have h2 : (M : ℝ) / 4 ≤ 4 * (M * dgffConductance / 2) * G := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  linarith

theorem flip_inr_interior_le (M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) (h : BoxHE n)
    (k : Fin (M - 1)) {w : DGFFSite n} (hb : boxNbr n h.1 h.2 = some w) :
    flipBound (4 * ((M : ℝ) * boxHalfCond n h) * (u ^ 2 / 2))
        (4 * ((M : ℝ) * boxHalfCond n h) *
          ((boxEdgeGraph n).subdiv M hM).toWired.green (Sum.inr (h, k)) (Sum.inr (h, k))) ≤
      tInt M (u ^ 2 / 2) := by
  apply flip_good_le M hM hu h
  obtain ⟨-, -, hκge⟩ := kappa_facts M hM h
  have hG := (boxEdgeGraph n).green_inr_ge_interior M hM (boxEdgeGraph_posDef n) h k
    (v := h.1) (w := w) rfl hb
  rw [boxEdgeGraph_precision_diag, boxEdgeGraph_precision_diag] at hG
  have hGp := ((boxEdgeGraph n).subdiv M hM).toWired.green_diag_pos
    ((boxEdgeGraph n).subdiv_posDef M hM (boxEdgeGraph_posDef n)) (Sum.inr (h, k))
  have hc := dgffConductance_pos
  set G := ((boxEdgeGraph n).subdiv M hM).toWired.green (Sum.inr (h, k)) (Sum.inr (h, k))
  set κ := (M : ℝ) * boxHalfCond n h
  have h1 : 4 * (M * dgffConductance / 2) * G ≤ 4 * κ * G := by nlinarith
  have h2 : (M : ℝ) / 4 ≤ 4 * (M * dgffConductance / 2) * G := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  linarith

theorem flip_inr_boundary_le (M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) (J : ℕ) (h : BoxHE n)
    (k : Fin (M - 1)) (hb : boxNbr n h.1 h.2 = none) :
    flipBound (4 * ((M : ℝ) * boxHalfCond n h) * (u ^ 2 / 2))
        (4 * ((M : ℝ) * boxHalfCond n h) *
          ((boxEdgeGraph n).subdiv M hM).toWired.green (Sum.inr (h, k)) (Sum.inr (h, k))) ≤
      tBdry M (u ^ 2 / 2) J (M - (k.val + 1)) := by
  have hk := k.isLt
  have hcond := boxHalfCond_of_none n hb
  rw [hcond]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hc := dgffConductance_pos
  have ht : 0 < u ^ 2 / 2 := by positivity
  have hGlo := (boxEdgeGraph n).green_inr_ge_boundary M hM (boxEdgeGraph_posDef n) h k
    (v := h.1) rfl hb
  rw [boxEdgeGraph_precision_diag] at hGlo
  have hGhi := (boxEdgeGraph n).green_inr_le_boundary M hM (boxEdgeGraph_posDef n) h k hb
  change _ ≤ _ / (M * boxHalfCond n h) at hGhi
  rw [hcond] at hGhi
  have hGp := ((boxEdgeGraph n).subdiv M hM).toWired.green_diag_pos
    ((boxEdgeGraph n).subdiv_posDef M hM (boxEdgeGraph_posDef n)) (Sum.inr (h, k))
  set G := ((boxEdgeGraph n).subdiv M hM).toWired.green (Sum.inr (h, k)) (Sum.inr (h, k))
  set j := M - (k.val + 1) with hj
  have hjr : (j : ℝ) = M - (k.val + 1) := by
    rw [hj, Nat.cast_sub (by omega)]; push_cast; ring
  have hjpos : (0 : ℝ) < j := by
    have : 1 ≤ j := by omega
    exact_mod_cast this
  have hSlo : (j : ℝ) ^ 2 / M ≤ 4 * (M * dgffConductance) * G := by
    rw [hjr]
    have h5 := mul_le_mul_of_nonneg_left hGlo hM0.le
    calc ((M : ℝ) - (k.val + 1)) ^ 2 / M = M * (((M - (k.val + 1) : ℝ) / M) ^ 2) := by
          field_simp
      _ ≤ M * (4 * dgffConductance * G) := h5
      _ = 4 * (M * dgffConductance) * G := by ring
  have hShi : 4 * (M * dgffConductance) * G ≤ 4 * j := by
    rw [hjr]
    have h6 : G * (M * dgffConductance) ≤ M - (k.val + 1) := by
      rwa [le_div_iff₀ (by positivity)] at hGhi
    calc 4 * (M * dgffConductance) * G = 4 * (G * (M * dgffConductance)) := by ring
      _ ≤ 4 * ((M : ℝ) - (k.val + 1)) := by linarith
  have hS0 : 0 < 4 * (M * dgffConductance) * G :=
    mul_pos (mul_pos (by norm_num) (mul_pos hM0 hc)) hGp
  have hA0 : 0 ≤ 4 * ((M : ℝ) * dgffConductance) * (u ^ 2 / 2) := by positivity
  unfold tBdry
  split_ifs with hjJ
  · refine (flipBound_le_exp hS0.le).trans ?_
    refine (exp_bound_mono hA0 hS0.le hShi).trans (le_of_eq ?_)
    congr 2
    ring
  · refine (flipBound_le_pow hA0 hS0).trans ?_
    refine (pow_bound_anti hA0 (div_pos (pow_pos hjpos 2) hM0) hSlo).trans (le_of_eq ?_)
    ring

 
theorem posAvg_le (M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) (J : ℕ) (h : BoxHE n) {q : ℕ}
    (hq : q ≤ M) :
    posAvg M hM u h q ≤ tInt M (u ^ 2 / 2) +
      (if 1 ≤ q ∧ q < M ∧ boxNbr n h.1 h.2 = none then tBdry M (u ^ 2 / 2) J (M - q) else 0) +
      (if q = M ∧ boxNbr n h.1 h.2 = none then
        Real.exp (-2 * (M * dgffConductance) * u ^ 2) else 0) := by
  have hTint0 : 0 ≤ tInt M (u ^ 2 / 2) := by unfold tInt dgffConductance; positivity
  have htB0 : ∀ j, 0 ≤ tBdry M (u ^ 2 / 2) J j := by
    intro j; unfold tBdry; split_ifs
    · exact (Real.exp_pos _).le
    · unfold dgffConductance; positivity
  have hE0 : 0 ≤ Real.exp (-2 * (M * dgffConductance) * u ^ 2) := (Real.exp_pos _).le
  unfold posAvg
  by_cases hq0 : q = 0
  · subst hq0
    rw [(boxEdgeGraph n).subPos_zero]
    change flipBound _ _ ≤ _
    have := flip_inl_le M hM hu h h.1
    have h1 : ¬ (1 ≤ 0 ∧ 0 < M ∧ boxNbr n h.1 h.2 = none) := by omega
    have h2 : ¬ (0 = M ∧ boxNbr n h.1 h.2 = none) := by omega
    rw [if_neg h1, if_neg h2]
    linarith
  by_cases hqM : q < M
  · rw [(boxEdgeGraph n).subPos_of_lt M h hq0 hqM]
    have h2 : ¬ (q = M ∧ boxNbr n h.1 h.2 = none) := by omega
    rw [if_neg h2, add_zero]
    change flipBound _ _ ≤ _
    cases hb : boxNbr n h.1 h.2 with
    | some w =>
      have := flip_inr_interior_le M hM hu h ⟨q - 1, by omega⟩ hb
      have h1 : ¬ (1 ≤ q ∧ q < M ∧ (some w : Option (DGFFSite n)) = none) := by simp
      rw [if_neg h1]
      linarith
    | none =>
      have := flip_inr_boundary_le M hM hu J h ⟨q - 1, by omega⟩ hb
      have hqq : M - ((q - 1) + 1) = M - q := by omega
      simp only [hqq] at this
      have h1 : 1 ≤ q ∧ q < M ∧ (none : Option (DGFFSite n)) = none := ⟨by omega, hqM, rfl⟩
      rw [if_pos h1]
      linarith
  · have hqe : M = q := by omega
    subst hqe
    rw [(boxEdgeGraph n).subPos_M M h (by omega),
      show (boxEdgeGraph n).head h = boxNbr n h.1 h.2 from rfl]
    have h1 : ¬ (1 ≤ M ∧ M < M ∧ boxNbr n h.1 h.2 = none) := by omega
    rw [if_neg h1, add_zero]
    cases hb : boxNbr n h.1 h.2 with
    | some w =>
      change flipBound _ _ ≤ _
      have := flip_inl_le M hM hu h w
      have h2 : ¬ (M = M ∧ (some w : Option (DGFFSite n)) = none) := by simp
      rw [if_neg h2]
      linarith
    | none =>
      change Real.exp _ ≤ _
      have h2 : (M = M ∧ (none : Option (DGFFSite n)) = none) := ⟨rfl, rfl⟩
      rw [if_pos h2, boxHalfCond_of_none n hb]
      linarith

end SupercriticalLQGUniqueness.B2.QPos

namespace SupercriticalLQGUniqueness.B2.QPos

open WiredConductances

variable {n : ℕ}

 
def etaBox (n M : ℕ) (hM : 2 ≤ M) (u : ℝ) : ℝ :=
  ∑ e, (EdgeGraph.vertexAvg ((boxEdgeGraph n).subdiv M hM) (((boxEdgeGraph n).subdiv M hM).cond e)
      u (u ^ 2 / 2) (((boxEdgeGraph n).subdiv M hM).tail e) +
    EdgeGraph.vertexAvg ((boxEdgeGraph n).subdiv M hM) (((boxEdgeGraph n).subdiv M hM).cond e)
      u (u ^ 2 / 2) (((boxEdgeGraph n).subdiv M hM).head e))

 
theorem etaBox_le (M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) (J : ℕ) :
    etaBox n M hM u ≤ 2 * Fintype.card (BoxHE n) *
      ((M + 1) * tInt M (u ^ 2 / 2) + ∑ j ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J j +
        Real.exp (-2 * (M * dgffConductance) * u ^ 2)) := by
  have hE0 : 0 ≤ Real.exp (-2 * (M * dgffConductance) * u ^ 2) := (Real.exp_pos _).le
  have htB0 : ∀ j, 0 ≤ tBdry M (u ^ 2 / 2) J j := by
    intro j; unfold tBdry; split_ifs
    · exact (Real.exp_pos _).le
    · unfold dgffConductance; positivity
  unfold etaBox
  rw [Fintype.sum_prod_type]
  have hrow : ∀ h : BoxHE n, ∑ k : Fin M, (posAvg M hM u h k.val + posAvg M hM u h (k.val + 1)) ≤
      2 * ((M + 1) * tInt M (u ^ 2 / 2) + ∑ j ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J j +
        Real.exp (-2 * (M * dgffConductance) * u ^ 2)) := by
    intro h
    have hsum : ∑ q ∈ Finset.range (M + 1), posAvg M hM u h q ≤
        (M + 1) * tInt M (u ^ 2 / 2) + ∑ j ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J j +
          Real.exp (-2 * (M * dgffConductance) * u ^ 2) := by
      refine (Finset.sum_le_sum fun q hq => posAvg_le M hM hu J h
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast
      have h1 : ∑ q ∈ Finset.range (M + 1), (if 1 ≤ q ∧ q < M ∧ boxNbr n h.1 h.2 = none then
          tBdry M (u ^ 2 / 2) J (M - q) else 0) ≤ ∑ j ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J j := by
        calc ∑ q ∈ Finset.range (M + 1), (if 1 ≤ q ∧ q < M ∧ boxNbr n h.1 h.2 = none then
              tBdry M (u ^ 2 / 2) J (M - q) else 0)
            ≤ ∑ q ∈ Finset.range (M + 1), (if q ∈ Finset.Ico 1 M then
              tBdry M (u ^ 2 / 2) J (M - q) else 0) := by
              apply Finset.sum_le_sum
              intro q _
              split_ifs with ha hb hb
              · exact le_rfl
              · exact absurd (Finset.mem_Ico.mpr ⟨ha.1, ha.2.1⟩) hb
              · exact htB0 _
              · exact le_rfl
          _ = ∑ q ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J (M - q) := by
              rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr]
              intro q hq
              simp only [Finset.mem_Ico] at hq
              exact Finset.mem_range.mpr (by omega)
          _ = ∑ j ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J j := by
              rw [Finset.sum_Ico_reflect _ _ (by omega)]
              congr 1
              ext j
              simp only [Finset.mem_Ico]
              omega
      have h2 : ∑ q ∈ Finset.range (M + 1), (if q = M ∧ boxNbr n h.1 h.2 = none then
          Real.exp (-2 * (M * dgffConductance) * u ^ 2) else 0) ≤
          Real.exp (-2 * (M * dgffConductance) * u ^ 2) := by
        calc ∑ q ∈ Finset.range (M + 1), (if q = M ∧ boxNbr n h.1 h.2 = none then
              Real.exp (-2 * (M * dgffConductance) * u ^ 2) else 0)
            ≤ ∑ q ∈ Finset.range (M + 1), (if q = M then
              Real.exp (-2 * (M * dgffConductance) * u ^ 2) else 0) := by
              apply Finset.sum_le_sum
              intro q _
              split_ifs with ha hb hb
              · exact le_rfl
              · exact absurd ha.1 hb
              · exact hE0
              · exact le_rfl
          _ = Real.exp (-2 * (M * dgffConductance) * u ^ 2) := by
              rw [Finset.sum_ite_eq']; simp
      linarith
    have hnn : ∀ q, 0 ≤ posAvg M hM u h q := posAvg_nonneg M hM u h
    have hA : ∑ k : Fin M, posAvg M hM u h k.val ≤ ∑ q ∈ Finset.range (M + 1), posAvg M hM u h q := by
      rw [Fin.sum_univ_eq_sum_range (fun k => posAvg M hM u h k)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun _ _ _ => hnn _)
    have hB : ∑ k : Fin M, posAvg M hM u h (k.val + 1) ≤
        ∑ q ∈ Finset.range (M + 1), posAvg M hM u h q := by
      rw [Fin.sum_univ_eq_sum_range (fun k => posAvg M hM u h (k + 1)),
        Finset.sum_range_succ' (fun q => posAvg M hM u h q) M]
      linarith [hnn 0]
    rw [Finset.sum_add_distrib]
    linarith
  calc ∑ h : BoxHE n, ∑ k : Fin M, (posAvg M hM u h k.val + posAvg M hM u h (k.val + 1))
      ≤ ∑ _h : BoxHE n, 2 * ((M + 1) * tInt M (u ^ 2 / 2) +
          ∑ j ∈ Finset.Ico 1 M, tBdry M (u ^ 2 / 2) J j +
          Real.exp (-2 * (M * dgffConductance) * u ^ 2)) := Finset.sum_le_sum fun h _ => hrow h
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end SupercriticalLQGUniqueness.B2.QPos
