/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBChainWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPerimeterOrder
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBMeetDetour

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

 


theorem laneB_chain_walk {ξ : ℝ} {f : ℂ → ℝ} {N : ℕ}
    {W : ℕ → ℝ → ℂ} {U : Set ℂ} {c : ℝ≥0∞}
    (hpiece : ∀ k ≤ N, ∃ a b : ℂ, IsPiecewiseC1Path (W k) a b)
    (hmap : ∀ k ≤ N, MapsTo (W k) (Icc (0 : ℝ) 1) U)
    (hcost : ∀ k ≤ N, lfppLen ξ f (W k) ≤ c)
    (hmeet : ∀ k < N, ∃ s ∈ Icc (0 : ℝ) 1,
      ∃ t ∈ Icc (0 : ℝ) 1, W k s = W (k + 1) t) :
    ∃ (V : ℝ → ℂ) (a b : ℂ),
      IsPiecewiseC1Path V a b ∧
      MapsTo V (Icc (0 : ℝ) 1) U ∧
      (∀ k ≤ N, W k '' Icc (0 : ℝ) 1 ⊆ V '' Icc (0 : ℝ) 1) ∧
      lfppLen ξ f V ≤ ((N + 1 : ℕ) : ℝ≥0∞) * (3 * c) := by
  induction N with
  | zero =>
      obtain ⟨a, b, hp⟩ := hpiece 0 le_rfl
      refine ⟨W 0, a, b, hp, hmap 0 le_rfl, ?_, ?_⟩
      · intro k hk
        have : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        exact subset_rfl
      · simpa using (le_trans (hcost 0 le_rfl) (by
          conv_lhs => rw [← one_mul c]
          gcongr
          norm_num : c ≤ 3 * c))
  | succ n ih =>
      obtain ⟨V, a, b, hpV, hmV, htV, hcV⟩ := ih
        (fun k hk => hpiece k (Nat.le_succ_of_le hk))
        (fun k hk => hmap k (Nat.le_succ_of_le hk))
        (fun k hk => hcost k (Nat.le_succ_of_le hk))
        (fun k hk => hmeet k (Nat.lt_succ_of_lt hk))
      obtain ⟨s, hs, t, ht, he⟩ := hmeet n (Nat.lt_succ_self n)
      obtain ⟨r, hr, her⟩ := htV n le_rfl ⟨s, hs, rfl⟩
      have hme : V r = W (n + 1) t := her.trans he
      obtain ⟨a', b', hpW⟩ := hpiece (n + 1) le_rfl
      let V' := laneBMeetDetour V (W (n + 1)) r t
      have hpV' : IsPiecewiseC1Path V' a b := by
        exact laneB_meetDetour_piecewise hpV hpW hr ht hme
      have hmV' : MapsTo V' (Icc (0 : ℝ) 1) U :=
        laneB_meetDetour_mapsTo hr ht hme hmV (hmap (n + 1) le_rfl)
      have htOld : V '' Icc (0 : ℝ) 1 ⊆ V' '' Icc (0 : ℝ) 1 :=
        laneB_meetDetour_contains_base hr hme
      have htNew : W (n + 1) '' Icc (0 : ℝ) 1 ⊆
          V' '' Icc (0 : ℝ) 1 :=
        laneB_meetDetour_contains_crossing hme
      refine ⟨V', a, b, hpV', hmV', ?_, ?_⟩
      · intro k hk
        rcases lt_or_eq_of_le hk with hlt | heq
        · exact (htV k (Nat.lt_succ_iff.mp hlt)).trans htOld
        · subst k
          exact htNew
      · have hstep : lfppLen ξ f V' ≤
            lfppLen ξ f V + 3 * lfppLen ξ f (W (n + 1)) :=
          laneB_meetDetour_len_le_add hr ht hme
        calc
          lfppLen ξ f V' ≤ lfppLen ξ f V +
              3 * lfppLen ξ f (W (n + 1)) := hstep
          _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (3 * c) + 3 * c := by
            exact add_le_add hcV (by gcongr; exact hcost (n + 1) le_rfl)
          _ = ((n + 1 + 1 : ℕ) : ℝ≥0∞) * (3 * c) := by
            push_cast
            ring

end SupercriticalLQGUniqueness.B2.DG20Conc
