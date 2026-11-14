/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkBrownianFailure at commit fdb5cad; local import paths and deprecated lemma names are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianStep

/-! Finite first-failure control for the actual walk/Brownian coupling, with
own-endpoint cell selectors and permanent termination. -/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Preorder
open scoped unitInterval ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- The probability that one of the first k+1 actual coupled excursions
fails is at most (k+1)b. Spatial cell estimates are needed only before failure;
they concern the actual ambient conductance exit law and Brownian exit law. -/
theorem walkBrownianJointLaw_firstFailure_le (N : FiniteConductanceNetwork V)
    (hd : 1 ≤ d) (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n i, MeasurableSet (E n i))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    (choice : ∀ n, Fin (m n) → Option J)
    (hselect : ∀ n, select n = cellSelector (E n) (choice n))
    (k : ℕ) {a b : ℝ} (hb : 0 ≤ b)
    (hdiam : ∀ n ≤ k, ∀ i, ∀ x ∈ E n i, ∀ y ∈ E n i, dist x y ≤ a)
    (hinside : ∀ n < k, ∀ i j, choice n i = some j → E n i ⊆ U j)
    (hcover : ∀ n ≤ k, ∀ j, closure (U j) ⊆ ⋃ i, E n i)
    (herror : ∀ n < k, ∀ i j, choice n i = some j →
      ∀ v : V, pos v ∈ E n i → ∀ y ∈ E n i, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) v).map pos) (E (n + 1) l)).toReal -
        (((stoppedBrownianLaw (U j) y μ).map CurveSpace.endPoint) (E (n + 1) l)).toReal| ≤
          b / (m (n + 1) + 1))
    (initial : J) (v₀ : V) (z : Euc d) (hz : z ∈ U initial)
    (hinit : ∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v₀).map pos) (E 0 i)).toReal -
      (((stoppedBrownianLaw (U initial) z μ).map CurveSpace.endPoint) (E 0 i)).toReal| ≤ b / (m 0 + 1)) :
    N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v₀ z
      {p | ∃ i ≤ k, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤
        (k + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  let ρ := N.walkBrownianInitialCoupling pos B hB U hU μ m E initial v₀ z
  let C := N.walkBrownianCouplingKernel pos hinj B hB U hU μ select hs m E hE hdE
  let Bad := fun n => (goodExcursionPair pos (E n) a)ᶜ
  let ε : ℕ → ℝ≥0∞ := fun n => if n < k then ENNReal.ofReal b else 1
  letI : IsProbabilityMeasure ρ :=
    N.walkBrownianInitialCoupling_isProbability pos B hB U hU μ m E hE hdE initial v₀ z
  have hBad (n : ℕ) : MeasurableSet (Bad n) :=
    (measurableSet_goodExcursionPair pos (E n) (hE n) a).compl
  have hstep : ∀ n h, h ∈ SkeletonCoupling.goodHistory Bad n → C n h (Bad (n + 1)) ≤ ε n := by
    intro n h hg
    by_cases hn : n < k
    · rw [show ε n = ENNReal.ofReal b from ite_eq_left hn]
      let p := h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
      have hp : p ∈ goodExcursionPair pos (E n) a := not_not.mp (hg ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      have hflags := goodExcursionPair_flags pos (E n) a hp
      have hx := goodExcursionPair_walk_in_range pos (E n) a hp
      have hdist := goodExcursionPair_dist_le pos (E n) (hdiam n hn.le) hp
      by_cases hf : p.1.1 = true
      · have hfb : p.2.1 = true := hflags.symm.trans hf
        have hzero := N.walkBrownianCouplingKernel_constant_bad_zero pos hinj B hB select hs
          U hU μ m E hE hdE n h (Or.inl hf) (Or.inl hfb) hx hdist
        exact hzero.le.trans zero_le
      · have hfalse : p.1.1 = false := Bool.eq_false_of_not_eq_true hf
        have hbfalse : p.2.1 = false := hflags.symm.trans hfalse
        obtain ⟨i, hwi, hbi⟩ := goodExcursionPair_active_cell pos (E n) a hp hfalse
        obtain ⟨v, hv⟩ := hx
        have hwsel : select n (pos v) = choice n i := by
          rw [hselect n, hv]
          exact cellSelector_of_label (E n) (choice n)
            ((cellLabel_eq_some_iff (E n) (hdE n) _ i).mpr hwi.2.1)
        have hbsel : select n (p.2.2 1) = choice n i := by
          rw [hselect n]
          exact cellSelector_of_label (E n) (choice n)
            ((cellLabel_eq_some_iff (E n) (hdE n) _ i).mpr hbi.2)
        cases hc : choice n i with
        | none =>
          have hzero := N.walkBrownianCouplingKernel_constant_bad_zero pos hinj B hB select hs
            U hU μ m E hE hdE n h (Or.inr (by rw [← hv]; exact hwsel.trans hc))
            (Or.inr (hbsel.trans hc)) ⟨v, hv⟩ hdist
          exact hzero.le.trans zero_le
        | some j =>
          apply N.walkBrownianCouplingKernel_active_bad_le pos hinj B hB select hs U hU μ
            m E hE hdE hd hμ hUb n h hfalse hbfalse v hv.symm j (hwsel.trans hc)
            (hbsel.trans hc) (hinside n hn i j hc hbi.2)
            (hcover (n + 1) (Nat.succ_le_iff.mpr hn) j) hb
          intro l
          exact herror n hn i j hc v (hv ▸ hwi.2.1) _ hbi.2 l
    · rw [show ε n = 1 from ite_eq_right hn]
      exact prob_le_one
  have hbound := SkeletonCoupling.jointPathLaw_bad_le ρ C Bad hBad ε hstep k
  have hinitbound : ρ (Bad 0) ≤ ENNReal.ofReal b :=
    N.walkBrownianInitialCoupling_bad_le pos B hB U hU μ m E hE hdE hd hμ hUb initial v₀ z hz
      (hcover 0 (Nat.zero_le k) initial) hb hinit a
  apply hbound.trans
  calc
    ρ (Bad 0) + ∑ i ∈ Finset.range k, ε i ≤
        ENNReal.ofReal b + ∑ _i ∈ Finset.range k, ENNReal.ofReal b := by
      apply add_le_add hinitbound
      apply Finset.sum_le_sum
      intro i hi
      exact (ite_eq_left (Finset.mem_range.mp hi)).le
    _ = _ := by simp [nsmul_eq_mul, add_mul, add_comm]

end BouRabeeGwynne.FiniteConductanceNetwork
