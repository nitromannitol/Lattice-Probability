/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TreeInequalityAux at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Auxiliary lemmas for node `J42` (`TreeInequality`)

* Combinatorics of well-formed cut trees (`CutTree.WF`): prefix closure, positivity of the
  chord lengths, consecutive child times, the unit flow, and the decomposition of the leaves
  below an internal node into the leaves below its children.
* An abstract "tree Jensen" inequality (`tree_jensen_root`): if a node function `L` is additive
  over children and dominates `R_v e^{F v}` at leaves, then
  `F [] + Σ_v θ(v) Σ_{j<|v|} Y(v.take j) ≤ log L []` whenever
  `Y u ≤ A_u + Σ_i q_i F(u i) - F u` at internal nodes.
* Analytic facts about admissible paths: integrability of `|γ'|`, chord ≤ arclength, additivity
  of the LFPP length over the tree, and the leaf bound.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Classical

namespace LQGDimension.TreeIneqJ42

open Blueprint.Draft

/-! ## Combinatorics of well-formed cut trees -/

section Tree

variable {T : CutTree} {γ : ℝ → ℂ} {M : ℕ} {ε : ℝ}

theorem prefix_mem_aux (hT : T.WF γ M ε) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n →
      ∀ (w : List ℕ) (i : ℕ), w ++ [i] <+: v → w ∈ T.nodes ∧ i < T.nch w := by
  induction n with
  | zero =>
    intro v _ hlen w i hp
    have := hp.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  | succ n ih =>
    intro v hv hlen w i hp
    rcases hT.is_child v hv with rfl | ⟨u, hu, i', hi', rfl⟩
    · simp at hlen
    · rcases List.prefix_concat_iff.1 hp with h | h
      · obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
        injection h2 with h3
        subst h3
        exact ⟨hu, hi'⟩
      · exact ih u hu (by simpa using hlen) w i h

/-- Every strict prefix of a node is a node, and the next letter is a valid child index. -/
theorem prefix_mem (hT : T.WF γ M ε) {v : List ℕ} (hv : v ∈ T.nodes) {w : List ℕ} {i : ℕ}
    (hp : w ++ [i] <+: v) : w ∈ T.nodes ∧ i < T.nch w :=
  prefix_mem_aux hT _ v hv rfl w i hp

theorem exists_child_prefix (hT : T.WF γ M ε) {u v : List ℕ} (hv : v ∈ T.nodes)
    (hp : u <+: v) (hne : u ≠ v) : ∃ i < T.nch u, u ++ [i] <+: v := by
  have hlt : u.length < v.length :=
    lt_of_le_of_ne hp.length_le (fun h => hne (hp.eq_of_length h))
  have hu : v.take u.length = u := (List.prefix_iff_eq_take.1 hp).symm
  have heq : v.take u.length ++ [v[u.length]] = v.take (u.length + 1) :=
    List.take_append_getElem hlt
  rw [hu] at heq
  have hpre : u ++ [v[u.length]] <+: v := heq ▸ List.take_prefix _ _
  exact ⟨_, (prefix_mem hT hv hpre).2, hpre⟩

/-- Consecutive child times of a node: `ctime u i = t₀ (u ++ [i])` for `i < nch u`, and
`ctime u (nch u) = t₁ u`. -/
def ctime (T : CutTree) (u : List ℕ) (j : ℕ) : ℝ :=
  if j < T.nch u then T.t₀ (u ++ [j]) else T.t₁ u

theorem ctime_zero (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    ctime T u 0 = T.t₀ u := by
  rw [ctime, ite_eq_left hn, (hT.consecutive u hu hn).1]

theorem ctime_nch (u : List ℕ) : ctime T u (T.nch u) = T.t₁ u := by
  rw [ctime, ite_eq_right (lt_irrefl _)]

theorem t₀_child {u : List ℕ} {i : ℕ} (hi : i < T.nch u) : T.t₀ (u ++ [i]) = ctime T u i := by
  rw [ctime, ite_eq_left hi]

theorem t₁_child (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ} (hi : i < T.nch u) :
    T.t₁ (u ++ [i]) = ctime T u (i + 1) := by
  have hn : 0 < T.nch u := by omega
  obtain ⟨_, hlast, hcons⟩ := hT.consecutive u hu hn
  by_cases h : i + 1 < T.nch u
  · rw [ctime, ite_eq_left h, hcons i h]
  · have : i = T.nch u - 1 := by omega
    rw [ctime, ite_eq_right h, this]
    exact hlast

theorem ctime_mono (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ T.nch u) : ctime T u i ≤ ctime T u j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have hjn : j < T.nch u := by omega
    calc ctime T u i ≤ ctime T u j := ih (by omega)
      _ = T.t₀ (u ++ [j]) := (t₀_child hjn).symm
      _ ≤ T.t₁ (u ++ [j]) := hT.time_le _ (hT.child_mem u hu j hjn)
      _ = ctime T u (j + 1) := t₁_child hT hu hjn

theorem times_mem_aux (hT : T.WF γ M ε) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n → 0 ≤ T.t₀ v ∧ T.t₁ v ≤ 1 := by
  induction n with
  | zero =>
    intro v _ hlen
    rw [List.eq_nil_of_length_eq_zero hlen, hT.root_time.1, hT.root_time.2]
    exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    intro v hv hlen
    rcases hT.is_child v hv with rfl | ⟨u, hu, i, hi, rfl⟩
    · simp at hlen
    · obtain ⟨h0, h1⟩ := ih u hu (by simpa using hlen)
      have hn : 0 < T.nch u := by omega
      refine ⟨?_, ?_⟩
      · calc (0 : ℝ) ≤ T.t₀ u := h0
          _ = ctime T u 0 := (ctime_zero hT hu hn).symm
          _ ≤ ctime T u i := ctime_mono hT hu (Nat.zero_le _) hi.le
          _ = T.t₀ (u ++ [i]) := (t₀_child hi).symm
      · calc T.t₁ (u ++ [i]) = ctime T u (i + 1) := t₁_child hT hu hi
          _ ≤ ctime T u (T.nch u) := ctime_mono hT hu (by omega) le_rfl
          _ = T.t₁ u := ctime_nch u
          _ ≤ 1 := h1

/-- All node times lie in `[0,1]`. -/
theorem times_mem (hT : T.WF γ M ε) {v : List ℕ} (hv : v ∈ T.nodes) :
    0 ≤ T.t₀ v ∧ T.t₀ v ≤ T.t₁ v ∧ T.t₁ v ≤ 1 :=
  have h := times_mem_aux hT _ v hv rfl
  ⟨h.1, hT.time_le v hv, h.2⟩

theorem ctime_mem (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u)
    {j : ℕ} (hj : j ≤ T.nch u) : 0 ≤ ctime T u j ∧ ctime T u j ≤ 1 := by
  obtain ⟨h0, -, h1⟩ := times_mem hT hu
  constructor
  · calc (0 : ℝ) ≤ T.t₀ u := h0
      _ = ctime T u 0 := (ctime_zero hT hu hn).symm
      _ ≤ ctime T u j := ctime_mono hT hu (Nat.zero_le _) hj
  · calc ctime T u j ≤ ctime T u (T.nch u) := ctime_mono hT hu hj le_rfl
      _ = T.t₁ u := ctime_nch u
      _ ≤ 1 := h1

/-- Chord lengths of the children dominate the chord of the parent (triangle inequality). -/
theorem R_le_S (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    T.R γ u ≤ T.S γ u := by
  have key : ∑ i ∈ Finset.range (T.nch u), (γ (ctime T u (i + 1)) - γ (ctime T u i)) =
      T.y γ u - T.x γ u := by
    rw [Finset.sum_range_sub (fun j => γ (ctime T u j)), ctime_nch, ctime_zero hT hu hn]
    rfl
  unfold CutTree.R CutTree.S
  rw [← key]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
  rw [Finset.mem_range] at hi
  simp only [CutTree.R, CutTree.x, CutTree.y, t₀_child hi, t₁_child hT hu hi]

/-- Hypotheses on the tree used throughout. -/
structure TreeHyp (T : CutTree) (γ : ℝ → ℂ) (M : ℕ) (ε : ℝ) : Prop where
  wf : T.WF γ M ε
  src : γ 0 = 0
  tgt : γ 1 = 1
  Mpos : 0 < M

theorem R_root (hT : TreeHyp T γ M ε) : T.R γ [] = 1 := by
  simp [CutTree.R, CutTree.x, CutTree.y, hT.wf.root_time.1, hT.wf.root_time.2, hT.src, hT.tgt]

theorem R_pos_aux (hT : TreeHyp T γ M ε) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n → 0 < T.R γ v := by
  induction n with
  | zero =>
    intro v _ hlen
    rw [List.eq_nil_of_length_eq_zero hlen, R_root hT]
    exact one_pos
  | succ n ih =>
    intro v hv hlen
    rcases hT.wf.is_child v hv with rfl | ⟨u, hu, i, hi, rfl⟩
    · simp at hlen
    · have h1 := (hT.wf.scale u hu i hi).1
      have h2 := ih u hu (by simpa using hlen)
      have hM' : (0 : ℝ) < 2 * M := by
        have : (0 : ℝ) < M := Nat.cast_pos.2 hT.Mpos
        linarith
      exact lt_of_lt_of_le (div_pos h2 hM') h1

theorem R_pos (hT : TreeHyp T γ M ε) {v : List ℕ} (hv : v ∈ T.nodes) : 0 < T.R γ v :=
  R_pos_aux hT _ v hv rfl

theorem S_pos (hT : TreeHyp T γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    0 < T.S γ u :=
  lt_of_lt_of_le (R_pos hT hu) (R_le_S hT.wf hu hn)

theorem A_nonneg (hT : TreeHyp T γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    0 ≤ T.A γ u :=
  Real.log_nonneg ((one_le_div (R_pos hT hu)).2 (R_le_S hT.wf hu hn))

theorem q_sum (hT : TreeHyp T γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u = 1 := by
  rw [← Finset.sum_div]
  exact div_self (S_pos hT hu hn).ne'

theorem q_pos (hT : TreeHyp T γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) : 0 < T.R γ (u ++ [i]) / T.S γ u :=
  div_pos (R_pos hT (hT.wf.child_mem u hu i hi)) (S_pos hT hu (by omega))

theorem flow_nil : T.flow γ [] = 1 := by
  simp [CutTree.flow]

theorem flow_child (u : List ℕ) (i : ℕ) :
    T.flow γ (u ++ [i]) = T.flow γ u * (T.R γ (u ++ [i]) / T.S γ u) := by
  unfold CutTree.flow
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (l₂ := [i]) (show j + 1 ≤ u.length by omega),
      List.take_append_of_le_length (l₂ := [i]) (show j ≤ u.length by omega)]
  · have e1 : (u ++ [i]).take (u.length + 1) = u ++ [i] := List.take_of_length_le (by simp)
    have e2 : (u ++ [i]).take u.length = u := List.take_left
    rw [e1, e2]

theorem flow_pos_aux (hT : TreeHyp T γ M ε) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n → 0 < T.flow γ v := by
  induction n with
  | zero =>
    intro v _ hlen
    rw [List.eq_nil_of_length_eq_zero hlen, flow_nil]
    exact one_pos
  | succ n ih =>
    intro v hv hlen
    rcases hT.wf.is_child v hv with rfl | ⟨u, hu, i, hi, rfl⟩
    · simp at hlen
    · rw [flow_child]
      exact mul_pos (ih u hu (by simpa using hlen)) (q_pos hT hu hi)

theorem flow_pos (hT : TreeHyp T γ M ε) {v : List ℕ} (hv : v ∈ T.nodes) : 0 < T.flow γ v :=
  flow_pos_aux hT _ v hv rfl

/-! ### Leaves below a node -/

/-- The leaves having `u` as a prefix. -/
def below (T : CutTree) (u : List ℕ) : Finset (List ℕ) := T.leaves.filter fun v => u <+: v

theorem mem_below {u v : List ℕ} : v ∈ below T u ↔ v ∈ T.leaves ∧ u <+: v :=
  Finset.mem_filter

theorem below_nil : below T [] = T.leaves :=
  Finset.filter_true_of_mem fun _ _ => List.nil_prefix

theorem below_leaf (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.leaves) : below T u = {u} := by
  ext v
  simp only [mem_below, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hp⟩
    by_contra hne
    obtain ⟨i, hi, -⟩ := exists_child_prefix hT (Finset.mem_filter.1 hv).1 hp (Ne.symm hne)
    rw [(Finset.mem_filter.1 hu).2] at hi
    exact Nat.not_lt_zero _ hi
  · rintro rfl
    exact ⟨hu, List.prefix_refl _⟩

theorem below_internal (hT : T.WF γ M ε) {u : List ℕ} (_hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    below T u = (Finset.range (T.nch u)).biUnion fun i => below T (u ++ [i]) := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_below]
  constructor
  · rintro ⟨hv, hp⟩
    have hne : u ≠ v := by
      rintro rfl
      rw [(Finset.mem_filter.1 hv).2] at hn
      exact lt_irrefl _ hn
    obtain ⟨i, hi, hpi⟩ := exists_child_prefix hT (Finset.mem_filter.1 hv).1 hp hne
    exact ⟨i, hi, hv, hpi⟩
  · rintro ⟨i, _, hv, hp⟩
    exact ⟨hv, (List.prefix_append u [i]).trans hp⟩

theorem below_disjoint (u : List ℕ) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint fun i => below T (u ++ [i]) := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have h1 := (mem_below.1 hvi).2
  have h2 := (mem_below.1 hvj).2
  have : u ++ [i] = u ++ [j] := by
    rw [List.prefix_iff_eq_take] at h1 h2
    rw [h1, h2]
    simp
  simp at this
  exact hij this

theorem sum_below_internal (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes)
    (hn : 0 < T.nch u) (f : List ℕ → ℝ) :
    ∑ v ∈ below T u, f v = ∑ i ∈ Finset.range (T.nch u), ∑ v ∈ below T (u ++ [i]), f v := by
  rw [below_internal hT hu hn, Finset.sum_biUnion (below_disjoint u _)]

/-! ### Chain sums and the tree Jensen inequality -/

/-- `Σ_{v leaf below u} θ(v) Σ_{|u| ≤ j < |v|} Y(v.take j)`. -/
def chainSum (T : CutTree) (γ : ℝ → ℂ) (Y : List ℕ → ℝ) (u : List ℕ) : ℝ :=
  ∑ v ∈ below T u, T.flow γ v * ∑ j ∈ Finset.Ico u.length v.length, Y (v.take j)

theorem chainSum_leaf (hT : T.WF γ M ε) {Y : List ℕ → ℝ} {u : List ℕ} (hu : u ∈ T.leaves) :
    chainSum T γ Y u = 0 := by
  simp [chainSum, below_leaf hT hu]

theorem chainSum_internal (hT : T.WF γ M ε) {Y : List ℕ → ℝ} {u : List ℕ} (hu : u ∈ T.nodes)
    (hn : 0 < T.nch u) :
    chainSum T γ Y u = ∑ i ∈ Finset.range (T.nch u),
      ((∑ v ∈ below T (u ++ [i]), T.flow γ v) * Y u + chainSum T γ Y (u ++ [i])) := by
  unfold chainSum
  rw [sum_below_internal hT hu hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hp := (mem_below.1 hv).2
  have hlen : (u ++ [i]).length ≤ v.length := hp.length_le
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : u.length < v.length)]
  have : v.take u.length = u :=
    (List.prefix_iff_eq_take.1 ((List.prefix_append u [i]).trans hp)).symm
  rw [this]
  ring

/-- The inductive statement of the tree Jensen inequality at node `u`. -/
def Claim (T : CutTree) (γ : ℝ → ℂ) (L F Y : List ℕ → ℝ) (u : List ℕ) : Prop :=
  ∑ v ∈ below T u, T.flow γ v = T.flow γ u ∧ 0 < L u ∧
    T.flow γ u * (Real.log (T.R γ u) + F u) + chainSum T γ Y u ≤ T.flow γ u * Real.log (L u)

theorem claim_leaf (hT : TreeHyp T γ M ε) {L F Y : List ℕ → ℝ}
    (hLleaf : ∀ v ∈ T.leaves, T.R γ v * Real.exp (F v) ≤ L v) {u : List ℕ}
    (hu : u ∈ T.leaves) : Claim T γ L F Y u := by
  have hun : u ∈ T.nodes := (Finset.mem_filter.1 hu).1
  have hR := R_pos hT hun
  have hθ := flow_pos hT hun
  have hRe : 0 < T.R γ u * Real.exp (F u) := mul_pos hR (Real.exp_pos _)
  have hL : 0 < L u := lt_of_lt_of_le hRe (hLleaf u hu)
  refine ⟨by simp [below_leaf hT.wf hu], hL, ?_⟩
  rw [chainSum_leaf hT.wf hu, add_zero]
  refine mul_le_mul_of_nonneg_left ?_ hθ.le
  have := Real.log_le_log hRe (hLleaf u hu)
  rwa [Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp] at this

theorem claim_internal (hT : TreeHyp T γ M ε) {L F Y : List ℕ → ℝ}
    (hLsum : ∀ u ∈ T.nodes, 0 < T.nch u → L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]))
    (hY : ∀ u ∈ T.nodes, 0 < T.nch u → Y u ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * F (u ++ [i]) - F u))
    {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u)
    (ih : ∀ i < T.nch u, Claim T γ L F Y (u ++ [i])) : Claim T γ L F Y u := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ i, q i = T.R γ (u ++ [i]) / T.S γ u := ⟨_, fun _ => rfl⟩
  have hR := R_pos hT hu
  have hSpos := S_pos hT hu hn
  have hθ := flow_pos hT hu
  have hRi : ∀ i ∈ Finset.range (T.nch u), 0 < T.R γ (u ++ [i]) := fun i hi =>
    R_pos hT (hT.wf.child_mem u hu i (Finset.mem_range.1 hi))
  have hq_pos : ∀ i ∈ Finset.range (T.nch u), 0 < q i := fun i hi => by
    rw [hq]; exact q_pos hT hu (Finset.mem_range.1 hi)
  have hq_sum : ∑ i ∈ Finset.range (T.nch u), q i = 1 := by
    simp only [hq]; exact q_sum hT hu hn
  have hθi : ∀ i, T.flow γ (u ++ [i]) = T.flow γ u * q i := fun i => by
    rw [hq]; exact flow_child u i
  have hsum_i : ∀ i ∈ Finset.range (T.nch u),
      ∑ v ∈ below T (u ++ [i]), T.flow γ v = T.flow γ u * q i := fun i hi =>
    (ih i (Finset.mem_range.1 hi)).1.trans (hθi i)
  have hLi : ∀ i ∈ Finset.range (T.nch u), 0 < L (u ++ [i]) := fun i hi =>
    (ih i (Finset.mem_range.1 hi)).2.1
  -- flow conservation
  have hflow : ∑ v ∈ below T u, T.flow γ v = T.flow γ u := by
    rw [sum_below_internal hT.wf hu hn, Finset.sum_congr rfl hsum_i, ← Finset.mul_sum, hq_sum,
      mul_one]
  -- additivity and positivity of `L`
  have hLu : L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]) := hLsum u hu hn
  have hLpos : 0 < L u := by
    rw [hLu]; exact Finset.sum_pos hLi (Finset.nonempty_range_iff.2 hn.ne')
  refine ⟨hflow, hLpos, ?_⟩
  -- chain sums
  have hchain : chainSum T γ Y u =
      T.flow γ u * Y u + ∑ i ∈ Finset.range (T.nch u), chainSum T γ Y (u ++ [i]) := by
    rw [chainSum_internal hT.wf hu hn, Finset.sum_add_distrib]
    congr 1
    calc ∑ i ∈ Finset.range (T.nch u), (∑ v ∈ below T (u ++ [i]), T.flow γ v) * Y u
        = ∑ i ∈ Finset.range (T.nch u), T.flow γ u * q i * Y u :=
          Finset.sum_congr rfl fun i hi => by rw [hsum_i i hi]
      _ = T.flow γ u * Y u := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hq_sum, mul_one]
  -- induction hypotheses, rearranged
  have hIH : ∀ i ∈ Finset.range (T.nch u), chainSum T γ Y (u ++ [i]) ≤
      T.flow γ u * (q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) -
        F (u ++ [i]))) := by
    intro i hi
    have h := (ih i (Finset.mem_range.1 hi)).2.2
    rw [hθi i] at h
    linarith
  -- Jensen for the concave logarithm with weights `q`
  have hJ : ∑ i ∈ Finset.range (T.nch u), q i * Real.log (L (u ++ [i]) / q i) ≤
      Real.log (L u) := by
    have := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.range (T.nch u))
      (w := q) (p := fun i => L (u ++ [i]) / q i) (fun i hi => (hq_pos i hi).le) hq_sum
      (fun i hi => div_pos (hLi i hi) (hq_pos i hi))
    simp only [smul_eq_mul] at this
    rw [hLu]
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (hq_pos i hi).ne'
    field_simp
  have hlogq : ∀ i ∈ Finset.range (T.nch u), q i * Real.log (L (u ++ [i]) / q i) =
      q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) - F (u ++ [i])) +
        q i * F (u ++ [i]) + q i * Real.log (T.S γ u) := by
    intro i hi
    rw [Real.log_div (hLi i hi).ne' (hq_pos i hi).ne', hq,
      Real.log_div (hRi i hi).ne' hSpos.ne']
    ring
  have e2 : ∑ i ∈ Finset.range (T.nch u), q i * Real.log (L (u ++ [i]) / q i) =
      ∑ i ∈ Finset.range (T.nch u),
          q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) - F (u ++ [i])) +
        ∑ i ∈ Finset.range (T.nch u), q i * F (u ++ [i]) + Real.log (T.S γ u) := by
    rw [Finset.sum_congr rfl hlogq, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hq_sum, one_mul]
  have hA : T.A γ u = Real.log (T.S γ u) - Real.log (T.R γ u) :=
    Real.log_div hSpos.ne' hR.ne'
  have hYu := hY u hu hn
  simp only [← hq] at hYu
  rw [hA] at hYu
  have h1 := mul_le_mul_of_nonneg_left hYu hθ.le
  have h2 := mul_le_mul_of_nonneg_left hJ hθ.le
  rw [e2] at h2
  have h3 : ∑ i ∈ Finset.range (T.nch u), chainSum T γ Y (u ++ [i]) ≤
      T.flow γ u * ∑ i ∈ Finset.range (T.nch u),
        q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) - F (u ++ [i])) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hIH
  rw [hchain]
  linarith

theorem claim_all (hT : TreeHyp T γ M ε) {L F Y : List ℕ → ℝ}
    (hLsum : ∀ u ∈ T.nodes, 0 < T.nch u → L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]))
    (hLleaf : ∀ v ∈ T.leaves, T.R γ v * Real.exp (F v) ≤ L v)
    (hY : ∀ u ∈ T.nodes, 0 < T.nch u → Y u ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * F (u ++ [i]) - F u)) :
    ∀ u ∈ T.nodes, Claim T γ L F Y u := by
  suffices H : ∀ m : ℕ, ∀ u ∈ T.nodes, T.nodes.sup List.length - u.length ≤ m →
      Claim T γ L F Y u from fun u hu => H _ u hu le_rfl
  intro m
  induction m with
  | zero =>
    intro u hu hm
    have hleaf : T.nch u = 0 := by
      by_contra h
      have hc := hT.wf.child_mem u hu 0 (Nat.pos_of_ne_zero h)
      have := Finset.le_sup (f := List.length) hc
      simp only [List.length_append, List.length_singleton] at this
      omega
    exact claim_leaf hT hLleaf (Finset.mem_filter.2 ⟨hu, hleaf⟩)
  | succ m ih =>
    intro u hu hm
    by_cases hleaf : T.nch u = 0
    · exact claim_leaf hT hLleaf (Finset.mem_filter.2 ⟨hu, hleaf⟩)
    · refine claim_internal hT hLsum hY hu (Nat.pos_of_ne_zero hleaf) fun i hi =>
        ih _ (hT.wf.child_mem u hu i hi) ?_
      have := Finset.le_sup (f := List.length) (hT.wf.child_mem u hu i hi)
      simp only [List.length_append, List.length_singleton] at this ⊢
      omega

/-- **Tree Jensen inequality** at the root. -/
theorem tree_jensen_root (hT : TreeHyp T γ M ε) {L F Y : List ℕ → ℝ}
    (hLsum : ∀ u ∈ T.nodes, 0 < T.nch u → L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]))
    (hLleaf : ∀ v ∈ T.leaves, T.R γ v * Real.exp (F v) ≤ L v)
    (hY : ∀ u ∈ T.nodes, 0 < T.nch u → Y u ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * F (u ++ [i]) - F u)) :
    ∑ v ∈ T.leaves, T.flow γ v = 1 ∧ 0 < L [] ∧
      F [] + ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length, Y (v.take j) ≤
        Real.log (L []) := by
  obtain ⟨hs, hL, hineq⟩ := claim_all hT hLsum hLleaf hY [] hT.wf.root_mem
  rw [below_nil, flow_nil] at hs
  refine ⟨hs, hL, ?_⟩
  unfold chainSum at hineq
  simp only [below_nil, flow_nil, R_root hT, Real.log_one, zero_add, one_mul,
    List.length_nil, Nat.Ico_zero_eq_range] at hineq
  exact hineq

/-! ### The local bound (4.3) -/

/-- `-(A_u + ξ Δ_u) ≤ δ² (δ^{-1/2} G_u - k_u)` at an internal node, with `ξ = δ^{3/2}`, written
with the potential `F = ξ H - c` (the constant `c` cancels because `Σ_i q_i = 1`). -/
theorem local_bound (hT : TreeHyp T γ M ε) {φ : ℂ → ℝ} {δ : ℝ} (hδ : 0 < δ) {u : List ℕ}
    (hu : u ∈ T.nodes) (hn : 0 < T.nch u) (c : ℝ) :
    -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ u - T.kbin γ δ u)) ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u *
          (δ ^ (3 / 2 : ℝ) * T.H γ φ (u ++ [i]) - c) - (δ ^ (3 / 2 : ℝ) * T.H γ φ u - c)) := by
  have hq_sum := q_sum hT hu hn
  have hξ : 0 ≤ δ ^ (3 / 2 : ℝ) := (Real.rpow_pos_of_pos hδ _).le
  have hδξ : δ ^ 2 * δ ^ (-(1 / 2 : ℝ)) = δ ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ]; norm_num
  have hsum : ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u *
        (δ ^ (3 / 2 : ℝ) * T.H γ φ (u ++ [i]) - c) =
      δ ^ (3 / 2 : ℝ) * ∑ i ∈ Finset.range (T.nch u),
        T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) - c := by
    calc _ = ∑ i ∈ Finset.range (T.nch u), (δ ^ (3 / 2 : ℝ) *
            (T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i])) -
            T.R γ (u ++ [i]) / T.S γ u * c) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = δ ^ (3 / 2 : ℝ) * ∑ i ∈ Finset.range (T.nch u),
            T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) -
            (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u) * c := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = _ := by rw [hq_sum, one_mul]
  -- `G_u ≥ -Δ_u`
  have hG : T.H γ φ u - ∑ i ∈ Finset.range (T.nch u),
      T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) ≤ T.G γ φ u := by
    rw [CutTree.G]
    split_ifs with hA1
    · exact le_rfl
    · have hbdd : BddAbove (Set.range fun i : Fin (T.nch u) =>
          T.H γ φ u - T.H γ φ (u ++ [(i : ℕ)])) := (Set.finite_range _).bddAbove
      have hle : ∀ i ∈ Finset.range (T.nch u), T.H γ φ u - T.H γ φ (u ++ [i]) ≤
          ⨆ j : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(j : ℕ)])) := fun i hi =>
        le_ciSup hbdd (⟨i, Finset.mem_range.1 hi⟩ : Fin (T.nch u))
      calc T.H γ φ u - ∑ i ∈ Finset.range (T.nch u),
            T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i])
          = ∑ i ∈ Finset.range (T.nch u),
            T.R γ (u ++ [i]) / T.S γ u * (T.H γ φ u - T.H γ φ (u ++ [i])) := by
            simp only [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq_sum, one_mul]
        _ ≤ ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u *
            ⨆ j : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(j : ℕ)])) :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hle i hi)
              (q_pos hT hu (Finset.mem_range.1 hi)).le
        _ = ⨆ j : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(j : ℕ)])) := by
            rw [← Finset.sum_mul, hq_sum, one_mul]
  -- `δ² k_u ≤ A_u`
  have hk : δ ^ 2 * (T.kbin γ δ u : ℝ) ≤ T.A γ u := by
    have hA := A_nonneg hT hu hn
    have hδ2 : 0 < δ ^ 2 := by positivity
    have h1 : (T.kbin γ δ u : ℝ) ≤ min (T.A γ u) 1 / δ ^ 2 :=
      Nat.floor_le (div_nonneg (le_min hA zero_le_one) hδ2.le)
    rw [le_div_iff₀ hδ2] at h1
    linarith [min_le_left (T.A γ u) 1]
  have h4 : δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ u - T.kbin γ δ u) =
      δ ^ (3 / 2 : ℝ) * T.G γ φ u - δ ^ 2 * T.kbin γ δ u := by
    rw [mul_sub, ← mul_assoc, hδξ]
  rw [hsum, h4]
  have h3 := mul_le_mul_of_nonneg_left hG hξ
  linarith

end Tree

/-! ## Analytic lemmas on admissible paths -/

section Path

variable {γ : ℝ → ℂ}

theorem norm_le_three_of_mem_U {z : ℂ} (hz : z ∈ LQGDimension.U) : ‖z‖ ≤ 3 := by
  obtain ⟨h1, h2⟩ := hz
  have hre : z.re ^ 2 < 4 := by
    have := sq_abs z.re
    nlinarith [abs_nonneg z.re]
  have him : z.im ^ 2 < 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have := Complex.sq_norm_sub_sq_re z
    linarith
  nlinarith [norm_nonneg z]

theorem abs_sub_le_osc {φ : ℂ → ℝ} (hφ : Continuous φ) {r : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ 3)
    (hw : ‖w‖ ≤ 3) (hzw : ‖z - w‖ ≤ r) : |φ z - φ w| ≤ osc φ r := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn
    hφ.continuousOn
  refine le_csSup ⟨2 * C, ?_⟩ ⟨z, w, hz, hw, hzw, rfl⟩
  rintro x ⟨z', w', hz', hw', -, rfl⟩
  have h1 := hC z' (mem_closedBall_zero_iff.2 hz')
  have h2 := hC w' (mem_closedBall_zero_iff.2 hw')
  rw [Real.norm_eq_abs] at h1 h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

theorem norm_chord_le {a b : ℂ} (ha : ‖a‖ ≤ 3) (hb : ‖b‖ ≤ 3) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖a + (s : ℂ) * (b - a)‖ ≤ 3 := by
  have e : a + (s : ℂ) * (b - a) = ((1 - s : ℝ) : ℂ) * a + (s : ℂ) * b := by
    push_cast; ring
  rw [e]
  calc _ ≤ ‖((1 - s : ℝ) : ℂ) * a‖ + ‖(s : ℂ) * b‖ := norm_add_le _ _
    _ = (1 - s) * ‖a‖ + s * ‖b‖ := by
        rw [norm_mul, norm_mul, Complex.norm_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith [hs.2]),
          Complex.norm_of_nonneg hs.1]
    _ ≤ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 hs.2),
          mul_le_mul_of_nonneg_left hb hs.1]

/-- A point within distance `r` of every point of a chord (all in the disc of radius `3`) has
`φ ≥ ⟨φ, ν_chord⟩ - osc φ r`. -/
theorem segAvg_sub_osc_le {φ : ℂ → ℝ} (hφ : Continuous φ) {a b p : ℂ} (ha : ‖a‖ ≤ 3)
    (hb : ‖b‖ ≤ 3) (hp : ‖p‖ ≤ 3) {r : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, ‖p - (a + (s : ℂ) * (b - a))‖ ≤ r) :
    segAvg φ a b - osc φ r ≤ φ p := by
  have hc : Continuous fun s : ℝ => φ (a + (s : ℂ) * (b - a)) :=
    hφ.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hle : segAvg φ a b ≤ ∫ _ in (0 : ℝ)..1, (φ p + osc φ r) := by
    unfold segAvg
    refine intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable _ _)
      intervalIntegrable_const fun s hs => ?_
    have := abs_sub_le_osc hφ hp (norm_chord_le ha hb hs) (hd s hs)
    obtain ⟨h1, h2⟩ := abs_le.1 this
    linarith
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hle
  linarith

theorem exists_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) :
    ∃ i : Fin k, t i.castSucc < x ∧ x < t i.succ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (k + 1)), S = Finset.univ.filter fun j => t j < x :=
    ⟨_, rfl⟩
  have hmem : ∀ j, j ∈ S ↔ t j < x := fun j => by simp [hS]
  have hne : S.Nonempty := ⟨0, (hmem 0).2 (by rw [ht0]; exact hx.1)⟩
  have hm : t (S.max' hne) < x := (hmem _).1 (S.max'_mem hne)
  have hml : S.max' hne ≠ Fin.last k := by
    intro h
    rw [h, htk] at hm
    linarith [hx.2]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hml
  refine ⟨i, by rw [hi]; exact hm, ?_⟩
  rcases lt_or_ge x (t i.succ) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h | h
    · have : i.succ ≤ S.max' hne := S.le_max' _ ((hmem _).2 h)
      rw [← hi] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · exact hxt ⟨_, h⟩

theorem hasDerivAt_of_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ)))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) : HasDerivAt γ (deriv γ x) x := by
  obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
  exact ((hC i).contDiffAt (Icc_mem_nhds h1 h2)).differentiableAt_one.hasDerivAt

theorem deriv_bound_piece {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Ioo a b, ‖deriv γ x‖ ≤ C := by
  obtain ⟨C, hC'⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact (hC' x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _)

/-- `γ'` is integrable on `[0,1]` for an admissible path. -/
theorem deriv_intervalIntegrable (hγ : IsAdmissiblePath γ) :
    IntervalIntegrable (deriv γ) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv γ x‖ ≤ C :=
    fun i => deriv_bound_piece (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv γ x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv γ).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

/-- The LFPP integrand `e^{ξ φ(γ t)} |γ'(t)|`. -/
def lenIntegrand (ξ : ℝ) (φ : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖

theorem lenIntegrand_intervalIntegrable (hγ : IsAdmissiblePath γ) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (ξ : ℝ) : IntervalIntegrable (lenIntegrand ξ φ γ) volume 0 1 := by
  have hc : ContinuousOn (fun t => Real.exp (ξ * φ (γ t))) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul hφ).comp_continuousOn hγ.continuousOn)
  exact (deriv_intervalIntegrable hγ).norm.continuousOn_mul hc

theorem intervalIntegrable_of_sub {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntervalIntegrable f volume 0 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f volume a b :=
  hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha hb)

/-- Chord ≤ arclength. -/
theorem chord_le_arclength (hγ : IsAdmissiblePath γ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : ‖γ b - γ a‖ ≤ ∫ t in a..b, ‖deriv γ t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hI := intervalIntegrable_of_sub (deriv_intervalIntegrable hγ) ha hab hb
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le γ (deriv γ) hab
    (countable_range t) (hγ.continuousOn.mono (Icc_subset_Icc ha hb))
    (fun x hx => hasDerivAt_of_piece ht0 htk hC
      ⟨lt_of_le_of_lt ha hx.1.1, lt_of_lt_of_le hx.1.2 hb⟩ hx.2) hI
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-! ### The LFPP length along the tree -/

variable {T : CutTree} {M : ℕ} {ε : ℝ}

/-- LFPP length of the subpath of node `u`. -/
def Lnode (T : CutTree) (ξ : ℝ) (φ : ℂ → ℝ) (γ : ℝ → ℂ) (u : List ℕ) : ℝ :=
  ∫ t in T.t₀ u..T.t₁ u, lenIntegrand ξ φ γ t

theorem Lnode_root (hT : T.WF γ M ε) (ξ : ℝ) (φ : ℂ → ℝ) :
    Lnode T ξ φ γ [] = lfppLength ξ φ γ := by
  unfold Lnode lfppLength lenIntegrand
  rw [hT.root_time.1, hT.root_time.2]

/-- Additivity of the LFPP length over the children of an internal node. -/
theorem Lnode_sum (hT : T.WF γ M ε) (hγ : IsAdmissiblePath γ) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (ξ : ℝ) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    Lnode T ξ φ γ u = ∑ i ∈ Finset.range (T.nch u), Lnode T ξ φ γ (u ++ [i]) := by
  have hint := lenIntegrand_intervalIntegrable hγ hφ ξ
  have e : ∀ i ∈ Finset.range (T.nch u), Lnode T ξ φ γ (u ++ [i]) =
      ∫ t in ctime T u i..ctime T u (i + 1), lenIntegrand ξ φ γ t := by
    intro i hi
    rw [Lnode, t₀_child (Finset.mem_range.1 hi), t₁_child hT hu (Finset.mem_range.1 hi)]
  show ∫ t in T.t₀ u..T.t₁ u, lenIntegrand ξ φ γ t = _
  rw [Finset.sum_congr rfl e, intervalIntegral.sum_integral_adjacent_intervals
    (a := ctime T u) (f := lenIntegrand ξ φ γ) ?_, ctime_zero hT hu hn, ctime_nch]
  intro i hi
  obtain ⟨h0, -⟩ := ctime_mem hT hu hn hi.le
  obtain ⟨-, h1⟩ := ctime_mem hT hu hn (show i + 1 ≤ T.nch u by omega)
  exact intervalIntegrable_of_sub hint h0 (ctime_mono hT hu (Nat.le_succ i) (by omega)) h1

/-- The leaf bound: the LFPP length of a leaf subpath is at least `R_v e^{ξ (H_v - ω)}`. -/
theorem Lnode_leaf (hT : T.WF γ M ε) (hγ : IsAdmissiblePath γ) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hε : 0 < ε) {ξ : ℝ} (hξ : 0 ≤ ξ) {v : List ℕ} (hv : v ∈ T.leaves) :
    T.R γ v * Real.exp (ξ * T.H γ φ v - ξ * osc φ (8 * ε)) ≤ Lnode T ξ φ γ v := by
  have hvn : v ∈ T.nodes := (Finset.mem_filter.1 hv).1
  have hnch : T.nch v = 0 := (Finset.mem_filter.1 hv).2
  obtain ⟨h0, hle, h1⟩ := times_mem hT hvn
  have hRε : T.R γ v ≤ ε := by
    by_contra h
    have := (hT.internal_iff v hvn).2 (not_le.1 h)
    omega
  have hint := intervalIntegrable_of_sub (lenIntegrand_intervalIntegrable hγ hφ ξ) h0 hle h1
  have hD := intervalIntegrable_of_sub (deriv_intervalIntegrable hγ) h0 hle h1
  have hU : ∀ s ∈ Icc (0 : ℝ) 1, ‖γ s‖ ≤ 3 := fun s hs =>
    norm_le_three_of_mem_U (hγ.mapsTo hs)
  have hx3 : ‖T.x γ v‖ ≤ 3 := hU _ ⟨h0, hle.trans h1⟩
  have hy3 : ‖T.y γ v‖ ≤ 3 := hU _ ⟨h0.trans hle, h1⟩
  have hpt : ∀ s ∈ Icc (T.t₀ v) (T.t₁ v),
      ξ * T.H γ φ v - ξ * osc φ (8 * ε) ≤ ξ * φ (γ s) := by
    intro s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨h0.trans hs.1, hs.2.trans h1⟩
    have hball := hT.ball v hvn s hs
    have key := segAvg_sub_osc_le hφ hx3 hy3 (hU s hs01) (r := 8 * ε) (fun σ hσ => by
      have h2 : ‖(σ : ℂ) * (T.y γ v - T.x γ v)‖ ≤ T.R γ v := by
        rw [norm_mul, Complex.norm_of_nonneg hσ.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hσ.2
      calc ‖γ s - (T.x γ v + (σ : ℂ) * (T.y γ v - T.x γ v))‖
          = ‖(γ s - T.x γ v) - (σ : ℂ) * (T.y γ v - T.x γ v)‖ := by rw [sub_add_eq_sub_sub]
        _ ≤ ‖γ s - T.x γ v‖ + ‖(σ : ℂ) * (T.y γ v - T.x γ v)‖ := norm_sub_le _ _
        _ ≤ 8 * ε := by linarith)
    have := mul_le_mul_of_nonneg_left key hξ
    unfold CutTree.H
    linarith
  calc T.R γ v * Real.exp (ξ * T.H γ φ v - ξ * osc φ (8 * ε))
      ≤ Real.exp (ξ * T.H γ φ v - ξ * osc φ (8 * ε)) *
          ∫ t in T.t₀ v..T.t₁ v, ‖deriv γ t‖ := by
        rw [mul_comm (T.R γ v)]
        exact mul_le_mul_of_nonneg_left (chord_le_arclength hγ h0 hle h1) (Real.exp_pos _).le
    _ = ∫ t in T.t₀ v..T.t₁ v, Real.exp (ξ * T.H γ φ v - ξ * osc φ (8 * ε)) * ‖deriv γ t‖ :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ Lnode T ξ φ γ v :=
        intervalIntegral.integral_mono_on hle (hD.norm.const_mul _) hint fun s hs =>
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hpt s hs)) (norm_nonneg _)

end Path

end LQGDimension.TreeIneqJ42
