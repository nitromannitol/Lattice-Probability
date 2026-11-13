/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GreedyOscillationModulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GreedyOscillationStops

/-!
# A deterministic modulus bound from greedy oscillation times

This file supplies the pathwise inclusion used by the finite-grid modulus
estimate.  The only extra point beyond the checked stopping-time API is that a
cell may end at the capped horizon, where the last grid jump must be included.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The displacement within a greedy cell is bounded by the threshold plus one
grid jump, including when the right endpoint is the capped horizon. -/
theorem abs_sub_at_most_add_of_between_greedyOscillationStops
    (X : ℕ → Ω → ℝ) {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b)
    (N k j : ℕ) (ω : Ω)
    (hjump : ∀ i < N, |X (i + 1) ω - X i ω| ≤ b)
    (hleft : greedyOscillationStop X ε N k ω ≤ j)
    (hright : j ≤ greedyOscillationStop X ε N (k + 1) ω) :
    |X j ω - X (greedyOscillationStop X ε N k ω) ω| ≤ ε + b := by
  by_cases hj : j < greedyOscillationStop X ε N (k + 1) ω
  · exact (abs_sub_lt_of_between_greedyOscillationStops X hε N k j ω hleft hj).le.trans
      (le_add_of_nonneg_right hb)
  have hjeq : j = greedyOscillationStop X ε N (k + 1) ω := by omega
  subst j
  by_cases hnext : greedyOscillationStop X ε N (k + 1) ω < N
  · exact abs_sub_at_greedyOscillationStop_succ_le X hε hb N k ω hjump hnext
  have hnextN : greedyOscillationStop X ε N (k + 1) ω = N :=
    Nat.le_antisymm (greedyOscillationStop_le X ε N (k + 1) ω) (not_lt.mp hnext)
  by_cases hkN : greedyOscillationStop X ε N k ω = N
  · rw [hnextN, hkN, sub_self, abs_zero]
    linarith
  have hklt : greedyOscillationStop X ε N k ω < N :=
    lt_of_le_of_ne (greedyOscillationStop_le X ε N k ω) hkN
  have hNpos : 0 < N := (Nat.zero_le _).trans_lt hklt
  have hkpred : greedyOscillationStop X ε N k ω ≤ N - 1 := by omega
  have hpredN : N - 1 < N := by omega
  have hbelow :
      |X (N - 1) ω - X (greedyOscillationStop X ε N k ω) ω| < ε :=
    abs_sub_lt_of_between_greedyOscillationStops X hε N k (N - 1) ω
      hkpred (by rw [hnextN]; exact hpredN)
  have hjump_last : |X N ω - X (N - 1) ω| ≤ b := by
    have := hjump (N - 1) hpredN
    rwa [Nat.sub_add_cancel hNpos] at this
  calc
    |X (greedyOscillationStop X ε N (k + 1) ω) ω -
        X (greedyOscillationStop X ε N k ω) ω| =
        |X N ω - X (greedyOscillationStop X ε N k ω) ω| := by rw [hnextN]
    _ =
        |(X N ω - X (N - 1) ω) +
          (X (N - 1) ω - X (greedyOscillationStop X ε N k ω) ω)| := by
            ring_nf
    _ ≤ |X N ω - X (N - 1) ω| +
          |X (N - 1) ω - X (greedyOscillationStop X ε N k ω) ω| :=
        abs_add_le _ _
    _ ≤ b + ε := add_le_add hjump_last hbelow.le
    _ = ε + b := add_comm _ _

/-- The greedy oscillation times are monotone in their counting index. -/
theorem greedyOscillationStop_mono
    (X : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) (ω : Ω) :
    Monotone (fun k => greedyOscillationStop X ε N k ω) := by
  apply monotone_nat_of_le_succ
  exact fun k => greedyOscillationStop_mono_step X hε N k ω

/-- Two grid times in the closure of one greedy cell differ by at most twice
the terminal-safe cell bound. -/
theorem abs_sub_le_two_mul_of_in_greedyOscillationCell
    (X : ℕ → Ω → ℝ) {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b)
    (N k i j : ℕ) (ω : Ω)
    (hjump : ∀ n < N, |X (n + 1) ω - X n ω| ≤ b)
    (hileft : greedyOscillationStop X ε N k ω ≤ i)
    (hiright : i ≤ greedyOscillationStop X ε N (k + 1) ω)
    (hjleft : greedyOscillationStop X ε N k ω ≤ j)
    (hjright : j ≤ greedyOscillationStop X ε N (k + 1) ω) :
    |X i ω - X j ω| ≤ 2 * (ε + b) := by
  have hi := abs_sub_at_most_add_of_between_greedyOscillationStops
    X hε hb N k i ω hjump hileft hiright
  have hj := abs_sub_at_most_add_of_between_greedyOscillationStops
    X hε hb N k j ω hjump hjleft hjright
  calc
    |X i ω - X j ω| =
        |(X i ω - X (greedyOscillationStop X ε N k ω) ω) -
          (X j ω - X (greedyOscillationStop X ε N k ω) ω)| := by ring_nf
    _ ≤ |X i ω - X (greedyOscillationStop X ε N k ω) ω| +
          |-(X j ω - X (greedyOscillationStop X ε N k ω) ω)| := abs_add_le _ _
    _ = |X i ω - X (greedyOscillationStop X ε N k ω) ω| +
          |X j ω - X (greedyOscillationStop X ε N k ω) ω| := by rw [abs_neg]
    _ ≤ (ε + b) + (ε + b) := add_le_add hi hj
    _ = 2 * (ε + b) := by ring

/-- If the `K`-th greedy time reaches the horizon and every earlier completed
excursion lasts more than `L`, the path has the required finite-grid modulus.
This is the pointwise deterministic form of the bad-event inclusion. -/
theorem abs_sub_le_four_mul_of_greedyOscillationStop_eq_horizon
    (X : ℕ → Ω → ℝ) {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b)
    (N K L i j : ℕ) (ω : Ω)
    (hjump : ∀ n < N, |X (n + 1) ω - X n ω| ≤ b)
    (hK : greedyOscillationStop X ε N K ω = N)
    (hgap : ∀ k < K,
      greedyOscillationStop X ε N (k + 1) ω < N →
        L < greedyOscillationStop X ε N (k + 1) ω -
          greedyOscillationStop X ε N k ω)
    (hij : i ≤ j) (hjN : j ≤ N) (hji : j - i ≤ L) :
    |X i ω - X j ω| ≤ 4 * (ε + b) := by
  have hc : 0 ≤ ε + b := by linarith
  by_cases hiN : i = N
  · have hj : j = N := by omega
    subst i
    subst j
    simp [hc]
  have hi_lt_N : i < N := by omega
  let hex : ∃ q : ℕ, i < greedyOscillationStop X ε N q ω :=
    ⟨K, hK.symm ▸ hi_lt_N⟩
  let q := Nat.find hex
  have hqright : i < greedyOscillationStop X ε N q ω := Nat.find_spec hex
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    simpa [hq0] using hqright
  let k := q - 1
  have hkq : k + 1 = q := by simp [k, Nat.sub_add_cancel hqpos]
  have hkleft : greedyOscillationStop X ε N k ω ≤ i := by
    have hk_lt_q : k < q := by omega
    have hnot : ¬i < greedyOscillationStop X ε N k ω :=
      Nat.find_min hex hk_lt_q
    omega
  have hiright : i ≤ greedyOscillationStop X ε N (k + 1) ω := by
    rw [hkq]
    exact hqright.le
  have hqK : q ≤ K := Nat.find_min' hex (hK.symm ▸ hi_lt_N)
  have hkK : k < K := by
    rw [← hkq] at hqK
    omega
  by_cases hjfirst : j ≤ greedyOscillationStop X ε N (k + 1) ω
  · have hsame := abs_sub_le_two_mul_of_in_greedyOscillationCell
      X hε hb N k i j ω hjump hkleft hiright (hkleft.trans hij) hjfirst
    nlinarith
  have hfirstj : greedyOscillationStop X ε N (k + 1) ω ≤ j := by omega
  have hfirstN : greedyOscillationStop X ε N (k + 1) ω < N :=
    (lt_of_not_ge hjfirst).trans_le hjN
  have hk1K : k + 1 < K := by
    by_contra h
    have hKle : K ≤ k + 1 := not_lt.mp h
    have hmono := greedyOscillationStop_mono X hε N ω hKle
    change greedyOscillationStop X ε N K ω ≤
      greedyOscillationStop X ε N (k + 1) ω at hmono
    rw [hK] at hmono
    exact (not_le_of_gt hfirstN) hmono
  have hjsecond : j ≤ greedyOscillationStop X ε N (k + 2) ω := by
    by_contra hnot
    have hsecondj : greedyOscillationStop X ε N (k + 2) ω < j :=
      lt_of_not_ge hnot
    have hsecondN : greedyOscillationStop X ε N (k + 2) ω < N :=
      hsecondj.trans_le hjN
    have hlong : L < greedyOscillationStop X ε N (k + 2) ω -
        greedyOscillationStop X ε N (k + 1) ω := by
      simpa [Nat.add_assoc] using
        hgap (k + 1) hk1K (by simpa [Nat.add_assoc] using hsecondN)
    have hifirst : i ≤ greedyOscillationStop X ε N (k + 1) ω := hiright
    have hdiff : greedyOscillationStop X ε N (k + 2) ω -
        greedyOscillationStop X ε N (k + 1) ω ≤ j - i :=
      tsub_le_tsub hsecondj.le hifirst
    omega
  have hissecond := abs_sub_le_two_mul_of_in_greedyOscillationCell
    X hε hb N k i (greedyOscillationStop X ε N (k + 1) ω) ω hjump
      hkleft hiright
      (greedyOscillationStop_mono_step X hε N k ω)
      le_rfl
  have hjfrom := abs_sub_at_most_add_of_between_greedyOscillationStops
    X hε hb N (k + 1) j ω hjump hfirstj (by simpa [Nat.add_assoc] using hjsecond)
  calc
    |X i ω - X j ω| =
        |(X i ω - X (greedyOscillationStop X ε N (k + 1) ω) ω) +
          (X (greedyOscillationStop X ε N (k + 1) ω) ω - X j ω)| := by ring_nf
    _ ≤ |X i ω - X (greedyOscillationStop X ε N (k + 1) ω) ω| +
          |X (greedyOscillationStop X ε N (k + 1) ω) ω - X j ω| := abs_add_le _ _
    _ ≤ 2 * (ε + b) + (ε + b) := by
      exact add_le_add hissecond (by simpa [abs_sub_comm] using hjfrom)
    _ ≤ 4 * (ε + b) := by nlinarith

end ReflectedGMS.MartingaleLimit
