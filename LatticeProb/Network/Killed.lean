/-
The walk killed on leaving a set: reversibility, the survival probability, and
the exponential decay that makes the killed Green function of a finite set a
finite number.

`LatticeProb.Graph.killedHeat G C k x y` is `P_x(X_k = y, τ_C > k)`, defined by
the first-step recursion.  Everything below is proved from that recursion.

* `killedKer G C k x y = p^C_k(x,y)/deg(y)` is the kernel in the normalization
  the Green function uses.  It satisfies the forward recursion, which averages
  the first argument, and `killedKer_backward`, which averages the second; the
  two together give `killedKer_symm`, that is
  `deg(y) p^C_k(x,y) = deg(x) p^C_k(y,x)`.  With `C = Set.univ` this is the
  reversibility of the simple random walk.
* `survival G C k x = ∑_{v ∈ C} p^C_k(x,v)` is `P_x(τ_C > k)`.  On a connected
  graph a finite `C` with nonempty complement has
  `survival G C (k + N) x ≤ θ · survival G C k x` with `θ < 1`, so the partial
  sums of the survival probability are bounded and the killed Green function is
  finite.
-/
import LatticeProb.Network.Basic
import LatticeProb.Graph.Odometer
import LatticeProb.Graph.HeatBasic

open Finset
open scoped ENNReal

namespace LatticeProb.Network

open LatticeProb.Graph
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### Elementary properties of the killed kernel -/

theorem killedHeat_succ (C : Set V) (k : ℕ) (x y : V) :
    killedHeat G C (k + 1) x y =
      if x ∈ C then (∑ z ∈ G.neighborFinset x, killedHeat G C k z y) / G.degree x else 0 := by
  classical
  rfl

theorem killedHeat_zero (C : Set V) (x y : V) :
    killedHeat G C 0 x y = if x ∈ C then (if x = y then 1 else 0) else 0 := by
  classical
  rfl

theorem killedHeat_nonneg (C : Set V) : ∀ (k : ℕ) (x y : V), 0 ≤ killedHeat G C k x y := by
  classical
  intro k
  induction k with
  | zero => intro x y; rw [killedHeat_zero]; split_ifs <;> norm_num
  | succ k ih =>
      intro x y
      rw [killedHeat_succ]
      split_ifs with h
      · exact div_nonneg (Finset.sum_nonneg fun z _ => ih z y) (Nat.cast_nonneg _)
      · exact le_refl 0

theorem killedHeat_of_source_not_mem {C : Set V} {x : V} (hx : x ∉ C) (k : ℕ) (y : V) :
    killedHeat G C k x y = 0 := by
  classical
  cases k with
  | zero => rw [killedHeat_zero, if_neg hx]
  | succ k => rw [killedHeat_succ, if_neg hx]

theorem killedHeat_of_target_not_mem {C : Set V} {y : V} (hy : y ∉ C) :
    ∀ (k : ℕ) (x : V), killedHeat G C k x y = 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro x
      rw [killedHeat_zero]
      by_cases hx : x ∈ C
      · rw [if_pos hx, if_neg (fun h : x = y => hy (h ▸ hx))]
      · rw [if_neg hx]
  | succ k ih =>
      intro x
      rw [killedHeat_succ, Finset.sum_congr rfl (fun z _ => ih z)]
      simp

/-- The unkilled walk is the walk killed on leaving the whole vertex set. -/
theorem killedHeat_univ : ∀ (k : ℕ) (x y : V), killedHeat G (Set.univ) k x y = heat G k x y := by
  classical
  intro k
  induction k with
  | zero => intro x y; rw [killedHeat_zero, if_pos (Set.mem_univ x)]; rfl
  | succ k ih =>
      intro x y
      rw [killedHeat_succ, if_pos (Set.mem_univ x), heat_succ, walkOp,
        Finset.sum_congr rfl (fun z _ => ih z y)]

theorem degree_pos_of_mem_neighborFinset {x z : V} (h : z ∈ G.neighborFinset x) :
    0 < G.degree z := by
  rw [G.degree_pos_iff_exists_adj]
  exact ⟨x, ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm⟩

/-! ### The normalized kernel and reversibility -/

/-- The killed kernel in the normalization of the Green function,
`p^C_k(x,y)/deg(y)`. -/
noncomputable def killedKer (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (k : ℕ) (x y : V) :
    ℝ :=
  killedHeat G C k x y / G.degree y

theorem killedKer_nonneg (C : Set V) (k : ℕ) (x y : V) : 0 ≤ killedKer G C k x y :=
  div_nonneg (killedHeat_nonneg C k x y) (Nat.cast_nonneg _)

theorem killedKer_zero_eq (C : Set V) (z y : V) :
    killedKer G C 0 z y = if z = y then (if y ∈ C then (1 : ℝ) / G.degree y else 0) else 0 := by
  classical
  rw [killedKer, killedHeat_zero]
  by_cases hzy : z = y
  · subst hzy
    by_cases hz : z ∈ C <;> simp [hz]
  · simp [hzy]

theorem sum_killedKer_zero (C : Set V) (S : Finset V) (y : V) :
    ∑ z ∈ S, killedKer G C 0 z y =
      if y ∈ S then (if y ∈ C then (1 : ℝ) / G.degree y else 0) else 0 := by
  classical
  rw [Finset.sum_congr rfl (fun z _ => killedKer_zero_eq C z y)]
  exact Finset.sum_ite_eq' S y (fun _ => if y ∈ C then (1 : ℝ) / G.degree y else 0)

theorem sum_killedKer_zero_right (C : Set V) (S : Finset V) (x : V) :
    ∑ w ∈ S, killedKer G C 0 x w =
      if x ∈ S then (if x ∈ C then (1 : ℝ) / G.degree x else 0) else 0 := by
  rw [Finset.sum_congr rfl (fun w _ => killedKer_zero_eq C x w)]
  exact Finset.sum_ite_eq S x (fun w => if w ∈ C then (1 : ℝ) / G.degree w else 0)

/-- The forward recursion: averaging the first argument. -/
theorem killedKer_succ (C : Set V) (k : ℕ) (x y : V) :
    killedKer G C (k + 1) x y =
      if x ∈ C then (∑ z ∈ G.neighborFinset x, killedKer G C k z y) / G.degree x else 0 := by
  classical
  rw [killedKer, killedHeat_succ]
  by_cases hx : x ∈ C
  · rw [if_pos hx, if_pos hx]
    simp only [killedKer, ← Finset.sum_div]
    rw [div_div, div_div, mul_comm ((G.degree x : ℝ))]
  · rw [if_neg hx, if_neg hx, zero_div]

/-- The backward recursion: the averaging step may be taken at the second
argument instead of the first. -/
theorem killedKer_backward (C : Set V) :
    ∀ (k : ℕ) (x y : V),
      killedKer G C (k + 1) x y =
        if y ∈ C then (∑ w ∈ G.neighborFinset y, killedKer G C k x w) / G.degree y else 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro x y
      rw [killedKer_succ, sum_killedKer_zero, sum_killedKer_zero_right]
      have hxy : y ∈ G.neighborFinset x ↔ x ∈ G.neighborFinset y := by
        rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      by_cases hx : x ∈ C
      · by_cases hy : y ∈ C
        · rw [if_pos hx, if_pos hy, if_pos hy, if_pos hx]
          by_cases hadj : y ∈ G.neighborFinset x
          · rw [if_pos hadj, if_pos (hxy.mp hadj), div_div, div_div, one_div, one_div,
              mul_comm ((G.degree y : ℝ)) ((G.degree x : ℝ))]
          · rw [if_neg hadj, if_neg (fun h => hadj (hxy.mpr h)), zero_div, zero_div]
        · rw [if_pos hx, if_neg hy, if_neg hy]
          simp
      · rw [if_neg hx, if_neg hx]
        by_cases hy : y ∈ C
        · rw [if_pos hy]
          simp
        · rw [if_neg hy]

  | succ k ih =>
      intro x y
      rw [killedKer_succ]
      by_cases hx : x ∈ C
      · by_cases hy : y ∈ C
        · rw [if_pos hx, if_pos hy]
          have hL : ∀ z ∈ G.neighborFinset x, killedKer G C (k + 1) z y
              = (∑ w ∈ G.neighborFinset y, killedKer G C k z w) / G.degree y := by
            intro z _
            rw [ih z y, if_pos hy]
          have hR : ∀ w ∈ G.neighborFinset y, killedKer G C (k + 1) x w
              = (∑ z ∈ G.neighborFinset x, killedKer G C k z w) / G.degree x := by
            intro w _
            rw [killedKer_succ, if_pos hx]
          rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.sum_div,
            ← Finset.sum_div, div_div, div_div, Finset.sum_comm,
            mul_comm ((G.degree y : ℝ)) ((G.degree x : ℝ))]
        · rw [if_pos hx, if_neg hy]
          have hL : ∀ z ∈ G.neighborFinset x, killedKer G C (k + 1) z y = 0 := by
            intro z _
            rw [ih z y, if_neg hy]
          rw [Finset.sum_congr rfl hL, Finset.sum_const_zero, zero_div]
      · rw [if_neg hx]
        by_cases hy : y ∈ C
        · rw [if_pos hy]
          have hR : ∀ w ∈ G.neighborFinset y, killedKer G C (k + 1) x w = 0 := by
            intro w _
            rw [killedKer_succ, if_neg hx]
          rw [Finset.sum_congr rfl hR, Finset.sum_const_zero, zero_div]
        · rw [if_neg hy]

/-- Reversibility of the killed walk in the normalized kernel. -/
theorem killedKer_symm (C : Set V) : ∀ (k : ℕ) (x y : V),
    killedKer G C k x y = killedKer G C k y x := by
  classical
  intro k
  induction k with
  | zero =>
      intro x y
      rw [killedKer_zero_eq, killedKer_zero_eq]
      by_cases h : x = y
      · subst h; rfl
      · rw [if_neg h, if_neg (Ne.symm h)]
  | succ k ih =>
      intro x y
      rw [killedKer_backward C k x y, killedKer_succ]
      by_cases hy : y ∈ C
      · rw [if_pos hy, if_pos hy]
        exact congrArg (fun t => t / (G.degree y : ℝ)) (Finset.sum_congr rfl fun w _ => ih x w)
      · rw [if_neg hy, if_neg hy]

theorem neighborFinset_eq_empty_of_degree_zero {y : V} (hd : G.degree y = 0) :
    G.neighborFinset y = ∅ := by
  rw [← Finset.card_eq_zero, SimpleGraph.card_neighborFinset_eq_degree]
  exact hd

/-- A vertex of degree zero is never reached by the walk from anywhere else. -/
theorem killedHeat_eq_zero_of_target_degree_zero (C : Set V) {v : V} (hd : G.degree v = 0) :
    ∀ (k : ℕ) (y : V), y ≠ v → killedHeat G C k y v = 0 := by
  intro k
  induction k with
  | zero =>
      intro y hyv
      rw [killedHeat_zero]
      by_cases hy : y ∈ C
      · rw [if_pos hy, if_neg hyv]
      · rw [if_neg hy]
  | succ k ih =>
      intro y _
      rw [killedHeat_succ]
      have hz : ∀ z ∈ G.neighborFinset y, killedHeat G C k z v = 0 := by
        intro z hz
        refine ih z fun hzv => ?_
        subst hzv
        have : 0 < G.degree z := degree_pos_of_mem_neighborFinset hz
        omega
      rw [Finset.sum_congr rfl hz]
      simp

/-- Reversibility of the killed walk: `deg(x) p^C_k(x,y) = deg(y) p^C_k(y,x)`. -/
theorem killedHeat_reversible (C : Set V) (k : ℕ) (x y : V) :
    (G.degree x : ℝ) * killedHeat G C k x y = (G.degree y : ℝ) * killedHeat G C k y x := by
  by_cases hx : G.degree x = 0
  · by_cases hxy : y = x
    · subst hxy; rfl
    · rw [hx, killedHeat_eq_zero_of_target_degree_zero C hx k y hxy]
      norm_num
  · by_cases hy : G.degree y = 0
    · have hxy : x ≠ y := fun h => hx (h ▸ hy)
      rw [hy, killedHeat_eq_zero_of_target_degree_zero C hy k x hxy]
      norm_num
    · have h := killedKer_symm (G := G) C k x y
      rw [killedKer, killedKer,
        div_eq_div_iff (Nat.cast_ne_zero.mpr hy) (Nat.cast_ne_zero.mpr hx)] at h
      linarith [h]

/-- Reversibility of the simple random walk on a locally finite graph:
`deg(x) p_k(x,y) = deg(y) p_k(y,x)`. -/
theorem heat_reversible (k : ℕ) (x y : V) :
    (G.degree x : ℝ) * heat G k x y = (G.degree y : ℝ) * heat G k y x := by
  have h := killedHeat_reversible (G := G) (Set.univ) k x y
  rw [killedHeat_univ, killedHeat_univ] at h
  exact h


/-! ### The survival probability -/

/-- The survival probability `P_x(τ_C > k) = ∑_{v ∈ C} p^C_k(x,v)`. -/
noncomputable def survival (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) (k : ℕ)
    (x : V) : ℝ :=
  ∑ v ∈ C, killedHeat G (C : Set V) k x v

theorem survival_nonneg (C : Finset V) (k : ℕ) (x : V) : 0 ≤ survival G C k x :=
  Finset.sum_nonneg fun v _ => killedHeat_nonneg _ k x v

theorem survival_zero (C : Finset V) (x : V) :
    survival G C 0 x = if x ∈ C then 1 else 0 := by
  rw [survival]
  have h : ∀ v ∈ C, killedHeat G (C : Set V) 0 x v = if x = v then (if x ∈ C then (1:ℝ) else 0)
      else 0 := by
    intro v _
    rw [killedHeat_zero]
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx]
  rw [Finset.sum_congr rfl h,
    Finset.sum_ite_eq C x (fun _ => if x ∈ C then (1:ℝ) else 0)]
  by_cases hx : x ∈ C <;> simp [hx]

theorem survival_of_not_mem {C : Finset V} {x : V} (hx : x ∉ C) (k : ℕ) :
    survival G C k x = 0 :=
  Finset.sum_eq_zero fun v _ => killedHeat_of_source_not_mem (by exact_mod_cast hx) k v

theorem survival_succ (C : Finset V) (k : ℕ) (x : V) :
    survival G C (k + 1) x =
      if x ∈ C then (∑ z ∈ G.neighborFinset x, survival G C k z) / G.degree x else 0 := by
  rw [survival]
  have h : ∀ v ∈ C, killedHeat G (C : Set V) (k + 1) x v
      = if x ∈ C then (∑ z ∈ G.neighborFinset x, killedHeat G (C : Set V) k z v) / G.degree x
        else 0 := by
    intro v _
    rw [killedHeat_succ]
    by_cases hx : x ∈ C
    · rw [if_pos (by exact_mod_cast hx : x ∈ (C : Set V)), if_pos hx]
    · rw [if_neg (by exact_mod_cast hx : x ∉ (C : Set V)), if_neg hx]
  rw [Finset.sum_congr rfl h]
  by_cases hx : x ∈ C
  · simp only [if_pos hx]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    rfl
  · simp [hx]

theorem survival_le_one (C : Finset V) : ∀ (k : ℕ) (x : V), survival G C k x ≤ 1 := by
  intro k
  induction k with
  | zero => intro x; rw [survival_zero]; split_ifs <;> norm_num
  | succ k ih =>
      intro x
      rw [survival_succ]
      split_ifs with hx
      · by_cases hd : G.degree x = 0
        · rw [neighborFinset_eq_empty_of_degree_zero hd]
          simp
        · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hd)]
          calc ∑ z ∈ G.neighborFinset x, survival G C k z
              ≤ ∑ _z ∈ G.neighborFinset x, (1:ℝ) := Finset.sum_le_sum fun z _ => ih z
            _ = (G.degree x : ℝ) := by
                rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
                  nsmul_eq_mul, mul_one]
      · norm_num

theorem survival_succ_le (C : Finset V) : ∀ (k : ℕ) (x : V),
    survival G C (k + 1) x ≤ survival G C k x := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [survival_zero]
      by_cases hx : x ∈ C
      · rw [if_pos hx]; exact survival_le_one C 1 x
      · rw [if_neg hx, survival_of_not_mem hx]
  | succ k ih =>
      intro x
      rw [survival_succ, survival_succ]
      split_ifs with hx
      · exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ih z) (by positivity)
          |>.trans_eq rfl
      · exact le_refl 0

theorem survival_antitone (C : Finset V) {m n : ℕ} (hmn : m ≤ n) (x : V) :
    survival G C n x ≤ survival G C m x := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.le_zero.mp hmn
      subst hm
      exact le_refl _
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact (survival_succ_le C n x).trans (ih (by omega))
      · have : m = n + 1 := by omega
        subst this
        exact le_refl _


/-! ### Exponential decay of the survival probability -/

/-- A walk from `x` out of `C` forces the survival probability at that time
below one. -/
theorem exists_survival_lt (C : Finset V) {x q : V} (p : G.Walk x q) (hq : q ∉ C) :
    ∃ ε : ℝ, 0 < ε ∧ survival G C p.length x ≤ 1 - ε := by
  induction p with
  | nil =>
      exact ⟨1, one_pos, by
        rw [SimpleGraph.Walk.length_nil, survival_of_not_mem hq]; norm_num⟩
  | @cons u v w hadj p' ih =>
      by_cases hu : u ∈ C
      · obtain ⟨ε, hε, hle⟩ := ih hq
        have hv : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj
        have hd : 1 ≤ G.degree u := by
          rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
          exact ⟨v, hadj⟩
        have hdR : (0 : ℝ) < G.degree u := by exact_mod_cast hd
        refine ⟨ε / G.degree u, by positivity, ?_⟩
        rw [SimpleGraph.Walk.length_cons, survival_succ, if_pos hu, div_le_iff₀ hdR]
        have hsum : ∑ z ∈ (G.neighborFinset u).erase v, survival G C p'.length z
            ≤ ((G.degree u : ℝ) - 1) := by
          have h1 : ∑ z ∈ (G.neighborFinset u).erase v, survival G C p'.length z
              ≤ ∑ _z ∈ (G.neighborFinset u).erase v, (1 : ℝ) :=
            Finset.sum_le_sum fun z _ => survival_le_one C _ z
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hv,
            SimpleGraph.card_neighborFinset_eq_degree, Nat.cast_sub hd, Nat.cast_one] at h1
          exact h1
        calc ∑ z ∈ G.neighborFinset u, survival G C p'.length z
            = survival G C p'.length v
              + ∑ z ∈ (G.neighborFinset u).erase v, survival G C p'.length z :=
              (Finset.add_sum_erase _ _ hv).symm
          _ ≤ (1 - ε) + ((G.degree u : ℝ) - 1) := add_le_add hle hsum
          _ = (1 - ε / G.degree u) * G.degree u := by field_simp; ring
      · exact ⟨1, one_pos, by
          rw [SimpleGraph.Walk.length_cons, survival_of_not_mem hu]; norm_num⟩

/-- A finite set with a vertex of the graph outside it has a uniform survival
bound strictly below one at a single time. -/
theorem exists_uniform_survival_le (hG : G.Connected) (C : Finset V) {q : V} (hq : q ∉ C) :
    ∃ (N : ℕ) (θ : ℝ), 0 < N ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ x : V, survival G C N x ≤ θ := by
  classical
  have hlen : ∀ x : V, ∃ n : ℕ, ∃ e : ℝ, 0 < e ∧ survival G C n x ≤ 1 - e := by
    intro x
    obtain ⟨p⟩ := hG.preconnected x q
    obtain ⟨e, he, hle⟩ := exists_survival_lt C p hq
    exact ⟨p.length, e, he, hle⟩
  choose l e he hle using hlen
  by_cases hC : C.Nonempty
  · refine ⟨C.sup l + 1, C.sup' hC (fun x => survival G C (C.sup l + 1) x),
      Nat.succ_pos _, ?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hC
      exact le_trans (survival_nonneg C _ x) (Finset.le_sup' _ hx)
    · rw [Finset.sup'_lt_iff]
      intro x hx
      have h1 : survival G C (C.sup l + 1) x ≤ survival G C (l x) x :=
        survival_antitone C (by have := Finset.le_sup (f := l) hx; omega) x
      linarith [hle x, he x]
    · intro x
      by_cases hx : x ∈ C
      · exact Finset.le_sup' _ hx
      · rw [survival_of_not_mem hx]
        obtain ⟨y, hy⟩ := hC
        exact le_trans (survival_nonneg C _ y) (Finset.le_sup' _ hy)
  · refine ⟨1, 0, Nat.one_pos, le_refl 0, zero_lt_one, ?_⟩
    intro x
    rw [Finset.not_nonempty_iff_eq_empty] at hC
    rw [survival, hC, Finset.sum_empty]

/-- The one-step contraction iterated: the survival probability contracts by
`θ` every `N` steps. -/
theorem survival_add_le {C : Finset V} {N : ℕ} {θ : ℝ}
    (hθ : ∀ x : V, survival G C N x ≤ θ) :
    ∀ (m : ℕ) (x : V), survival G C (m + N) x ≤ θ * survival G C m x := by
  intro m
  induction m with
  | zero =>
      intro x
      rw [Nat.zero_add, survival_zero]
      by_cases hx : x ∈ C
      · rw [if_pos hx, mul_one]; exact hθ x
      · rw [if_neg hx, mul_zero, survival_of_not_mem hx]
  | succ m ih =>
      intro x
      rw [show m + 1 + N = (m + N) + 1 by omega, survival_succ, survival_succ]
      by_cases hx : x ∈ C
      · have hsum : ∑ z ∈ G.neighborFinset x, survival G C (m + N) z
            ≤ θ * ∑ z ∈ G.neighborFinset x, survival G C m z := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun z _ => ih z
        rw [if_pos hx, if_pos hx, ← mul_div_assoc, div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hsum (by positivity)
      · simp [hx]

theorem survival_le_pow {C : Finset V} {N : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ x : V, survival G C N x ≤ θ) :
    ∀ (j k : ℕ) (x : V), survival G C (k + j * N) x ≤ θ ^ j := by
  intro j
  induction j with
  | zero => intro k x; simpa using survival_le_one C k x
  | succ j ih =>
      intro k x
      have hstep : survival G C ((k + j * N) + N) x ≤ θ * survival G C (k + j * N) x :=
        survival_add_le hθ _ x
      have : k + (j + 1) * N = (k + j * N) + N := by ring
      rw [this]
      calc survival G C ((k + j * N) + N) x ≤ θ * survival G C (k + j * N) x := hstep
        _ ≤ θ * θ ^ j := by
            exact mul_le_mul_of_nonneg_left (ih k x) hθ0
        _ = θ ^ (j + 1) := by ring


/-! ### Summability of the killed Green function -/

theorem sum_range_survival_le {C : Finset V} {N : ℕ} {θ : ℝ} (hN : 0 < N) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hθ : ∀ x : V, survival G C N x ≤ θ) (x : V) (n : ℕ) :
    ∑ k ∈ Finset.range n, survival G C k x ≤ (N : ℝ) / (1 - θ) := by
  have hsub : (0 : ℝ) < 1 - θ := by linarith
  have hblock : ∀ J : ℕ, ∑ k ∈ Finset.range (N * J), survival G C k x
      ≤ ∑ j ∈ Finset.range J, (N : ℝ) * θ ^ j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
        have hsplit : N * (J + 1) = N * J + N := by ring
        rw [hsplit, Finset.sum_range_add, Finset.sum_range_succ]
        refine add_le_add ih ?_
        have hterm : ∀ i ∈ Finset.range N, survival G C (N * J + i) x ≤ θ ^ J := by
          intro i _
          have hcomm : N * J + i = i + J * N := by ring
          rw [hcomm]
          exact survival_le_pow hθ0 hθ J i x
        calc ∑ i ∈ Finset.range N, survival G C (N * J + i) x
            ≤ ∑ _i ∈ Finset.range N, θ ^ J := Finset.sum_le_sum hterm
          _ = (N : ℝ) * θ ^ J := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeom : ∀ J : ℕ, ∑ j ∈ Finset.range J, (N : ℝ) * θ ^ j ≤ (N : ℝ) / (1 - θ) := by
    intro J
    rw [← Finset.mul_sum]
    have hg : (∑ j ∈ Finset.range J, θ ^ j) * (1 - θ) = 1 - θ ^ J := by
      have h := geom_sum_mul θ J
      linear_combination -h
    have hle : (∑ j ∈ Finset.range J, θ ^ j) ≤ 1 / (1 - θ) := by
      rw [le_div_iff₀ hsub, hg]
      have : 0 ≤ θ ^ J := pow_nonneg hθ0 J
      linarith
    calc (N : ℝ) * ∑ j ∈ Finset.range J, θ ^ j ≤ (N : ℝ) * (1 / (1 - θ)) := by
          exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      _ = (N : ℝ) / (1 - θ) := by ring
  have hn : n ≤ N * n := Nat.le_mul_of_pos_left n hN
  calc ∑ k ∈ Finset.range n, survival G C k x
      ≤ ∑ k ∈ Finset.range (N * n), survival G C k x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro k hk; simp only [Finset.mem_range] at hk ⊢; omega)
          (fun k _ _ => survival_nonneg C k x)
    _ ≤ ∑ j ∈ Finset.range n, (N : ℝ) * θ ^ j := hblock n
    _ ≤ (N : ℝ) / (1 - θ) := hgeom n

theorem killedHeat_le_survival (C : Finset V) {v : V} (hv : v ∈ C) (k : ℕ) (x : V) :
    killedHeat G (C : Set V) k x v ≤ survival G C k x :=
  Finset.single_le_sum (f := fun w => killedHeat G (C : Set V) k x w)
    (fun w _ => killedHeat_nonneg _ k x w) hv

/-- On a connected graph, the local time of the walk killed on leaving a finite
proper subset is summable. -/
theorem summable_killedHeat (hG : G.Connected) (C : Finset V) {q : V} (hq : q ∉ C) (x v : V) :
    Summable (fun k => killedHeat G (C : Set V) k x v) := by
  by_cases hv : v ∈ C
  · obtain ⟨N, θ, hN, hθ0, hθ1, hθ⟩ := exists_uniform_survival_le hG C hq
    refine summable_of_sum_range_le (c := (N : ℝ) / (1 - θ))
      (fun k => killedHeat_nonneg _ k x v) (fun n => ?_)
    calc ∑ k ∈ Finset.range n, killedHeat G (C : Set V) k x v
        ≤ ∑ k ∈ Finset.range n, survival G C k x :=
          Finset.sum_le_sum fun k _ => killedHeat_le_survival C hv k x
      _ ≤ (N : ℝ) / (1 - θ) := sum_range_survival_le hN hθ0 hθ1 hθ x n
  · have : (fun k => killedHeat G (C : Set V) k x v) = fun _ => (0 : ℝ) := by
      funext k
      exact killedHeat_of_target_not_mem (by exact_mod_cast hv) k x
    rw [this]
    exact summable_zero

/-- The killed Green function of a finite proper subset is finite, and equals
the real sum of the local times. -/
theorem killedGreenReal_eq_tsum (hG : G.Connected) (C : Finset V) {q : V} (hq : q ∉ C)
    (x v : V) :
    killedGreenReal G (C : Set V) x v
      = (∑' k : ℕ, killedHeat G (C : Set V) k x v) / G.degree v := by
  have hsum := summable_killedHeat hG C hq x v
  have hnn : ∀ k, 0 ≤ killedHeat G (C : Set V) k x v := fun k => killedHeat_nonneg _ k x v
  have h1 : (∑' k : ℕ, ENNReal.ofReal (killedHeat G (C : Set V) k x v))
      = ENNReal.ofReal (∑' k : ℕ, killedHeat G (C : Set V) k x v) :=
    (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm
  rw [killedGreenReal, killedGreen, h1, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (tsum_nonneg hnn), ENNReal.toReal_natCast]

omit [G.LocallyFinite] in
/-- A connected graph with two distinct vertices has no isolated vertex. -/
theorem exists_adj_of_connected (hG : G.Connected) {v w : V} (hvw : v ≠ w) :
    ∃ u, G.Adj v u := by
  obtain ⟨p⟩ := hG.preconnected v w
  cases p with
  | nil => exact absurd rfl hvw
  | cons h _ => exact ⟨_, h⟩

theorem degree_pos_of_ne (hG : G.Connected) {x y : V} (hxy : x ≠ y) (v : V) :
    0 < G.degree v := by
  rw [G.degree_pos_iff_exists_adj]
  by_cases hv : v = x
  · subst hv
    exact exists_adj_of_connected hG hxy
  · exact exists_adj_of_connected hG (fun h => hv h)

theorem killedGreen_ne_top (hG : G.Connected) (C : Finset V) {q : V} (hq : q ∉ C)
    {v : V} (hdeg : 0 < G.degree v) (x : V) : killedGreen G (C : Set V) x v ≠ ⊤ := by
  have hsum := summable_killedHeat hG C hq x v
  have hnn : ∀ k, 0 ≤ killedHeat G (C : Set V) k x v := fun k => killedHeat_nonneg _ k x v
  rw [killedGreen, (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm]
  refine (ENNReal.div_lt_top ENNReal.ofReal_ne_top ?_).ne
  simpa using hdeg.ne'

end LatticeProb.Network
