/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.BoundedAdditive at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 











set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.Polylog

 



theorem bounded_additive_real_slope (x : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ n m : ℕ, x n + x m - c ≤ x (n + m) ∧
      x (n + m) ≤ x n + x m + c) :
    ∃ β : ℝ, ∀ n : ℕ, 0 < n → |x n / n - β| ≤ c / n := by
  have hLower : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * (x 1 - c) + c ≤ x (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := (h (n + 1) 1).1
      push_cast at ih ⊢
      nlinarith
  have hUpper : ∀ n : ℕ, x (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * (x 1 + c) - c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := (h (n + 1) 1).2
      push_cast at ih ⊢
      nlinarith
  let u : ℕ → ℝ := fun n => x n + c
  let v : ℕ → ℝ := fun n => -x n + c
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [(h n m).2]
  have hv : Subadditive v := by
    intro n m
    dsimp [v]
    linarith [(h n m).1]
  have huBdd : BddBelow (Set.range fun n : ℕ => u n / n) := by
    refine ⟨min 0 (x 1 - c), ?_⟩
    rintro z ⟨n, rfl⟩
    rcases n with _ | n
    · simpa only [Nat.cast_zero, div_zero] using (min_le_left (0 : ℝ) (x 1 - c))
    · have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have hh := hLower n
      push_cast at hh
      apply le_trans (min_le_right _ _)
      dsimp [u]
      apply (le_div_iff₀ hn).2
      push_cast
      nlinarith [hh, hc]
  have hvBdd : BddBelow (Set.range fun n : ℕ => v n / n) := by
    refine ⟨min 0 (-(x 1 + c)), ?_⟩
    rintro z ⟨n, rfl⟩
    rcases n with _ | n
    · simpa only [Nat.cast_zero, div_zero] using (min_le_left (0 : ℝ) (-(x 1 + c)))
    · have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have hh := hUpper n
      push_cast at hh
      apply le_trans (min_le_right _ _)
      dsimp [v]
      apply (le_div_iff₀ hn).2
      push_cast
      nlinarith [hh, hc]
  let β := hu.lim
  have huLim : Tendsto (fun n => u n / n) atTop (𝓝 β) := hu.tendsto_lim huBdd
  have hvLim : Tendsto (fun n => v n / n) atTop (𝓝 hv.lim) := hv.tendsto_lim hvBdd
  have hSum : Tendsto (fun n : ℕ => u n / n + v n / n) atTop (𝓝 (β + hv.lim)) :=
    huLim.add hvLim
  have hSumZero : Tendsto (fun n : ℕ => u n / n + v n / n) atTop (𝓝 (0 : ℝ)) := by
    have hcdiv : Tendsto (fun n : ℕ => (2 * c) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    convert hcdiv using 1
    ext n
    dsimp [u, v]
    ring
  have hβv : β + hv.lim = 0 := tendsto_nhds_unique hSum hSumZero
  refine ⟨β, ?_⟩
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle := hu.lim_le_div huBdd (Nat.ne_of_gt hn)
  have hge := hv.lim_le_div hvBdd (Nat.ne_of_gt hn)
  dsimp [u] at hle
  dsimp [v] at hge
  change β ≤ (x n + c) / n at hle
  rw [add_div] at hle
  rw [add_div, neg_div] at hge
  rw [abs_le]
  constructor <;> nlinarith [hβv]

 


end SupercriticalLQGUniqueness.B2.Polylog
