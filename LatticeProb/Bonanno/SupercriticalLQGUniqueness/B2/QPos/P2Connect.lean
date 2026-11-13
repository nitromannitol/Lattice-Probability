/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Connect at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SignKernel
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2EdgeGraph

 










set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E] (Γ : EdgeGraph W E)

 
def VisOrB (s : Soup (Excursion W)) : Option W → Prop
  | none => True
  | some x => soupVisitCount s x ≠ 0

 
def ahat (u : ℝ) (a : EuclideanSpace ℝ W) : Option W → ℝ
  | none => u
  | some x => a x

 
def sigHat (σ : W → Bool) : Option W → Bool
  | none => true
  | some x => σ x

 
def disBound (u : ℝ) (a : EuclideanSpace ℝ W) (e : E) : ℝ :=
  Real.exp (-2 * Γ.cond e * ahat u a (Γ.tail e) * ahat u a (Γ.head e))

theorem soupVisitCount_ne_zero_iff (s : Soup (Excursion W)) (x : W) :
    soupVisitCount s x ≠ 0 ↔ ∃ i j, (s.2 i).2 j = x := by
  unfold soupVisitCount Excursion.visitCount
  rw [Ne, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    not_forall, not_not]

theorem edgeCond_pos_exists (i j : W) (h : 0 < Γ.edgeCond i j) :
    ∃ e, (Γ.tail e = some i ∧ Γ.head e = some j) ∨ (Γ.tail e = some j ∧ Γ.head e = some i) := by
  by_contra hcon
  push_neg at hcon
  have : Γ.edgeCond i j = 0 := by
    unfold edgeCond
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨h1, h2⟩ := hcon e
    have hA : ind (Γ.tail e) i * ind (Γ.head e) j = 0 := by
      unfold ind
      by_cases ht : Γ.tail e = some i
      · rw [if_neg (h1 ht)]; ring
      · rw [if_neg ht]; ring
    have hB : ind (Γ.tail e) j * ind (Γ.head e) i = 0 := by
      unfold ind
      by_cases ht : Γ.tail e = some j
      · rw [if_neg (h2 ht)]; ring
      · rw [if_neg ht]; ring
    rw [hA, hB]; ring
  linarith

theorem bdryCond_pos_exists (i : W) (h : 0 < Γ.bdryCond i) :
    ∃ e, (Γ.tail e = some i ∧ Γ.head e = none) ∨ (Γ.tail e = none ∧ Γ.head e = some i) := by
  by_contra hcon
  push_neg at hcon
  have : Γ.bdryCond i = 0 := by
    unfold bdryCond
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨h1, h2⟩ := hcon e
    have hA : ind (Γ.tail e) i * (if Γ.head e = none then 1 else 0) = 0 := by
      unfold ind
      by_cases ht : Γ.tail e = some i
      · rw [if_neg (h1 ht)]; ring
      · rw [if_neg ht]; ring
    have hB : (if Γ.tail e = none then 1 else 0) * ind (Γ.head e) i = 0 := by
      unfold ind
      by_cases ht : Γ.tail e = none
      · rw [if_neg (h2 ht)]; ring
      · rw [if_neg ht]; ring
    rw [hA, hB]; ring
  linarith

 
theorem excursionWeight_pos_steps (γ : Excursion W) (hγ : 0 < Γ.toWired.excursionWeight γ) :
    0 < Γ.bdryCond (γ.2 0) ∧ ∀ l : Fin γ.1, 0 < Γ.edgeCond (γ.2 l.castSucc) (γ.2 l.succ) := by
  unfold WiredConductances.excursionWeight at hγ
  have hb := Γ.toWired.boundary_nonneg (γ.2 0)
  have hP : ∀ l : Fin γ.1, 0 ≤ Γ.toWired.killedTransition (γ.2 l.castSucc) (γ.2 l.succ) :=
    fun l => Γ.toWired.killedTransition_nonneg _ _
  have hlast := div_nonneg (Γ.toWired.boundary_nonneg (γ.2 (Fin.last γ.1)))
    (Γ.toWired.totalRate_nonneg (γ.2 (Fin.last γ.1)))
  have hprod := Finset.prod_nonneg fun l (_ : l ∈ Finset.univ) => hP l
  refine ⟨?_, fun l => ?_⟩
  · rcases hb.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_mul] at hγ; exact absurd hγ (lt_irrefl 0)
    · exact h0
  · rcases (hP l).eq_or_lt with h0 | h0
    · rw [Finset.prod_eq_zero (Finset.mem_univ l) h0.symm, mul_zero, zero_mul] at hγ
      exact absurd hγ (lt_irrefl 0)
    · unfold WiredConductances.killedTransition at h0
      by_contra hle
      push_neg at hle
      have : Γ.toWired.edge (γ.2 l.castSucc) (γ.2 l.succ) ≤ 0 := hle
      have := div_nonpos_of_nonpos_of_nonneg this (Γ.toWired.totalRate_nonneg (γ.2 l.castSucc))
      linarith

 

theorem exists_disagree_edge (s : Soup (Excursion W))
    (hs : ∀ i, 0 < Γ.toWired.excursionWeight (s.2 i)) (σ : W → Bool) (x : W)
    (hx : soupVisitCount s x ≠ 0) (hσ : σ x = false) :
    ∃ e, VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) ∧
      sigHat σ (Γ.tail e) ≠ sigHat σ (Γ.head e) := by
  obtain ⟨i, j, hij⟩ := (soupVisitCount_ne_zero_iff s x).mp hx
  obtain ⟨hb, hsteps⟩ := Γ.excursionWeight_pos_steps (s.2 i) (hs i)
  have hvis : ∀ l, soupVisitCount s ((s.2 i).2 l) ≠ 0 :=
    fun l => (soupVisitCount_ne_zero_iff s _).mpr ⟨i, l, rfl⟩
  
  have key : ∀ l : ℕ, ∀ hl : l < (s.2 i).1 + 1, σ ((s.2 i).2 ⟨l, hl⟩) = false →
      ∃ e, VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) ∧
        sigHat σ (Γ.tail e) ≠ sigHat σ (Γ.head e) := by
    intro l
    induction l with
    | zero =>
      intro hl h0
      have h00 : (⟨0, hl⟩ : Fin ((s.2 i).1 + 1)) = 0 := Fin.ext rfl
      rw [h00] at h0
      obtain ⟨e, he⟩ := Γ.bdryCond_pos_exists _ hb
      refine ⟨e, ?_⟩
      rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · rw [ht, hh]
        refine ⟨hvis 0, trivial, ?_⟩
        simp only [sigHat, h0]
        decide
      · rw [ht, hh]
        refine ⟨trivial, hvis 0, ?_⟩
        simp only [sigHat, h0]
        decide
    | succ l ih =>
      intro hl hl0
      by_cases hprev : σ ((s.2 i).2 ⟨l, by omega⟩) = false
      · exact ih (by omega) hprev
      · have hprev' : σ ((s.2 i).2 ⟨l, by omega⟩) = true := by simpa using hprev
        have hstep := hsteps ⟨l, by omega⟩
        have hcs : (⟨l, by omega⟩ : Fin (s.2 i).1).castSucc = ⟨l, by omega⟩ := rfl
        have hsc : (⟨l, by omega⟩ : Fin (s.2 i).1).succ = ⟨l + 1, hl⟩ := rfl
        rw [hcs, hsc] at hstep
        obtain ⟨e, he⟩ := Γ.edgeCond_pos_exists _ _ hstep
        refine ⟨e, ?_⟩
        rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · rw [ht, hh]
          exact ⟨hvis _, hvis _, by simp [sigHat, hprev', hl0]⟩
        · rw [ht, hh]
          exact ⟨hvis _, hvis _, by simp [sigHat, hprev', hl0]⟩
  exact key j.val j.isLt (by rw [show (⟨j.val, j.isLt⟩ : Fin ((s.2 i).1 + 1)) = j from rfl, hij]; exact hσ)

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E] (Γ : EdgeGraph W E)

 
def circEvent (Pc : Set (Finset W)) : Set (EuclideanSpace ℝ W) :=
  {z | ∃ c ∈ Pc, ∀ x ∈ c, 0 ≤ z x}

 
def SoupCirc (Pc : Set (Finset W)) (s : Soup (Excursion W)) : Prop :=
  ∃ c ∈ Pc, ∀ x ∈ c, soupVisitCount s x ≠ 0

theorem edgeCond_ge_cond {e : E} {p q : W} (ht : Γ.tail e = some p) (hh : Γ.head e = some q) :
    Γ.cond e ≤ Γ.edgeCond p q := by
  unfold edgeCond
  have hnn : ∀ e' ∈ Finset.univ, 0 ≤ Γ.cond e' * (ind (Γ.tail e') p * ind (Γ.head e') q +
      ind (Γ.tail e') q * ind (Γ.head e') p) := fun e' _ =>
    mul_nonneg (Γ.cond_pos e').le (add_nonneg (mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _))
      (mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)))
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ e))
  have h1 : ind (Γ.tail e) p * ind (Γ.head e) q = 1 := by simp [ind, ht, hh]
  rw [h1]
  have := mul_nonneg (ind_nonneg (Γ.tail e) q) (ind_nonneg (Γ.head e) p)
  nlinarith [Γ.cond_pos e]

theorem bdryCond_ge_cond_tail {e : E} {p : W} (ht : Γ.tail e = some p) (hh : Γ.head e = none) :
    Γ.cond e ≤ Γ.bdryCond p := by
  unfold bdryCond
  have hnn : ∀ e' ∈ Finset.univ, 0 ≤ Γ.cond e' * (ind (Γ.tail e') p *
      (if Γ.head e' = none then 1 else 0) + (if Γ.tail e' = none then 1 else 0) *
        ind (Γ.head e') p) := fun e' _ =>
    mul_nonneg (Γ.cond_pos e').le (add_nonneg (mul_nonneg (ind_nonneg _ _) (by split_ifs <;> norm_num))
      (mul_nonneg (by split_ifs <;> norm_num) (ind_nonneg _ _)))
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ e))
  simp [ind, ht, hh]

theorem bdryCond_ge_cond_head {e : E} {p : W} (ht : Γ.tail e = none) (hh : Γ.head e = some p) :
    Γ.cond e ≤ Γ.bdryCond p := by
  unfold bdryCond
  have hnn : ∀ e' ∈ Finset.univ, 0 ≤ Γ.cond e' * (ind (Γ.tail e') p *
      (if Γ.head e' = none then 1 else 0) + (if Γ.tail e' = none then 1 else 0) *
        ind (Γ.head e') p) := fun e' _ =>
    mul_nonneg (Γ.cond_pos e').le (add_nonneg (mul_nonneg (ind_nonneg _ _) (by split_ifs <;> norm_num))
      (mul_nonneg (by split_ifs <;> norm_num) (ind_nonneg _ _)))
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ e))
  simp [ind, ht, hh]

theorem disBound_nonneg (u : ℝ) (a : EuclideanSpace ℝ W) (e : E) : 0 ≤ Γ.disBound u a e :=
  (Real.exp_pos _).le

variable (hK : Γ.toWired.precision.PosDef)

 
theorem sum_signKernel_disagree_le_disBound (C : ℝ) (hC : 0 < C) {u : ℝ} (hu : 0 ≤ u)
    (a : EuclideanSpace ℝ W) (ha : ∀ x, 0 ≤ a x) (e : E) :
    ∑ σ : W → Bool, (if sigHat σ (Γ.tail e) ≠ sigHat σ (Γ.head e) then
        signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ else 0) ≤ Γ.disBound u a e := by
  have hne := Γ.tail_ne_head e
  unfold disBound
  rcases ht : Γ.tail e with _ | p <;> rcases hh : Γ.head e with _ | q
  · exact absurd (ht.trans hh.symm) hne
  · 
    have hb := Γ.bdryCond_ge_cond_head ht hh
    have h := Γ.toWired.signKernel_neg_le C hC hu a ha q
    have hfun : ∀ σ : W → Bool, (if sigHat σ none ≠ sigHat σ (some q) then signKernel (fun z => C *
        Γ.toWired.shiftDensity u z) a σ else 0) = if σ q then 0 else
        signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ := by
      intro σ; cases hσ : σ q <;> simp [sigHat, hσ]
    rw [Finset.sum_congr rfl (fun σ _ => hfun σ)]
    show _ ≤ Real.exp (-2 * Γ.cond e * u * a q)
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have : Γ.cond e * u * a q ≤ Γ.bdryCond q * u * a q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hu) (ha q)
    change -2 * (Γ.bdryCond q * u * a q) ≤ -2 * Γ.cond e * u * a q
    linarith
  · 
    have hb := Γ.bdryCond_ge_cond_tail ht hh
    have h := Γ.toWired.signKernel_neg_le C hC hu a ha p
    have hfun : ∀ σ : W → Bool, (if sigHat σ (some p) ≠ sigHat σ none then signKernel (fun z => C *
        Γ.toWired.shiftDensity u z) a σ else 0) = if σ p then 0 else
        signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ := by
      intro σ; cases hσ : σ p <;> simp [sigHat, hσ]
    rw [Finset.sum_congr rfl (fun σ _ => hfun σ)]
    show _ ≤ Real.exp (-2 * Γ.cond e * a p * u)
    refine h.trans (Real.exp_le_exp.mpr ?_)
    change -2 * (Γ.bdryCond p * u * a p) ≤ -2 * Γ.cond e * a p * u
    have : Γ.cond e * u * a p ≤ Γ.bdryCond p * u * a p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hu) (ha p)
    nlinarith
  · 
    have hpq : p ≠ q := fun h => hne (by rw [ht, hh, h])
    have hc := Γ.edgeCond_ge_cond ht hh
    have h := Γ.toWired.signKernel_disagree_le C hC hu a ha hpq
    have hfun : ∀ σ : W → Bool, (if sigHat σ (some p) ≠ sigHat σ (some q) then signKernel
        (fun z => C * Γ.toWired.shiftDensity u z) a σ else 0) = if σ p = σ q then 0 else
        signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ := by
      intro σ; by_cases hs : σ p = σ q <;> simp [sigHat, hs]
    rw [Finset.sum_congr rfl (fun σ _ => hfun σ)]
    show _ ≤ Real.exp (-2 * Γ.cond e * a p * a q)
    refine h.trans (Real.exp_le_exp.mpr ?_)
    change -2 * (Γ.edgeCond p q * a p * a q) ≤ -2 * Γ.cond e * a p * a q
    have : Γ.cond e * a p * a q ≤ Γ.edgeCond p q * a p * a q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (ha p)) (ha q)
    nlinarith

open Classical in
 
theorem signAverage_lower (C : ℝ) (hC : 0 < C) {u : ℝ} (hu : 0 ≤ u) (Pc : Set (Finset W))
    (s : Soup (Excursion W)) (hs : ∀ i, 0 < Γ.toWired.excursionWeight (s.2 i))
    (a : EuclideanSpace ℝ W) (ha : ∀ x, 0 ≤ a x) :
    (if SoupCirc Pc s then 1 else 0) -
        ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then Γ.disBound u a e else 0) ≤
      ∑ σ : W → Bool, signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ *
        (circEvent Pc).indicator 1 (signApply σ a) := by
  classical
  set κ := signKernel (fun z => C * Γ.toWired.shiftDensity u z) a with hκdef
  have hρ : ∀ z, 0 < C * Γ.toWired.shiftDensity u z :=
    fun z => mul_pos hC (Γ.toWired.shiftDensity_pos u z)
  have hκ0 : ∀ σ, 0 ≤ κ σ := fun σ => signKernel_nonneg hρ a σ
  have hκ1 : ∑ σ, κ σ = 1 := sum_signKernel hρ a
  have hΨ0 : 0 ≤ ∑ σ : W → Bool, κ σ * (circEvent Pc).indicator 1 (signApply σ a) :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (hκ0 σ)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hD0 : 0 ≤ ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then
      Γ.disBound u a e else 0) :=
    Finset.sum_nonneg fun e _ => by split_ifs; exact Γ.disBound_nonneg u a e; exact le_rfl
  by_cases hc : SoupCirc Pc s
  · rw [if_pos hc]
    obtain ⟨c, hcPc, hcv⟩ := hc
    set good : (W → Bool) → Prop := fun σ => ∀ x, soupVisitCount s x ≠ 0 → σ x = true
    have hmem : ∀ σ, good σ → signApply σ a ∈ circEvent Pc := by
      intro σ hσ
      refine ⟨c, hcPc, fun x hx => ?_⟩
      have hx' : σ x = true := hσ x (hcv x hx)
      unfold signApply
      simp [hx', ha x]
    have hstep1 : ∑ σ : W → Bool, (if good σ then κ σ else 0) ≤
        ∑ σ : W → Bool, κ σ * (circEvent Pc).indicator 1 (signApply σ a) := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hσ : good σ
      · rw [if_pos hσ, Set.indicator_of_mem (hmem σ hσ)]
        simp
      · rw [if_neg hσ]
        exact mul_nonneg (hκ0 σ) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hstep2 : ∑ σ : W → Bool, (if good σ then κ σ else 0) =
        1 - ∑ σ : W → Bool, (if good σ then 0 else κ σ) := by
      rw [← hκ1, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> ring
    have hstep3 : ∑ σ : W → Bool, (if good σ then 0 else κ σ) ≤
        ∑ σ : W → Bool, ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then
          (if sigHat σ (Γ.tail e) ≠ sigHat σ (Γ.head e) then κ σ else 0) else 0) := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hσ : good σ
      · rw [if_pos hσ]
        exact Finset.sum_nonneg fun e _ => by split_ifs <;> first | exact hκ0 σ | exact le_rfl
      · rw [if_neg hσ]
        simp only [good, not_forall] at hσ
        obtain ⟨x, hx, hσx⟩ := hσ
        have hσx' : σ x = false := by simpa using hσx
        obtain ⟨e, h1, h2, h3⟩ := Γ.exists_disagree_edge s hs σ x hx hσx'
        have hnn : ∀ e' ∈ Finset.univ, 0 ≤ (if VisOrB s (Γ.tail e') ∧ VisOrB s (Γ.head e') then
            (if sigHat σ (Γ.tail e') ≠ sigHat σ (Γ.head e') then κ σ else 0) else 0) :=
          fun e' _ => by split_ifs <;> first | exact hκ0 σ | exact le_rfl
        refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ e))
        rw [if_pos ⟨h1, h2⟩, if_pos h3]
    have hstep4 : ∑ σ : W → Bool, ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then
          (if sigHat σ (Γ.tail e) ≠ sigHat σ (Γ.head e) then κ σ else 0) else 0) ≤
        ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then Γ.disBound u a e else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro e _
      by_cases hv : VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e)
      · simp only [if_pos hv]
        exact Γ.sum_signKernel_disagree_le_disBound C hC hu a ha e
      · simp [hv]
    linarith
  · rw [if_neg hc]
    linarith

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
