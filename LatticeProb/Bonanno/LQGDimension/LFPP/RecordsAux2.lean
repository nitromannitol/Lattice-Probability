/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordsAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

/-!
# Records (node `R44`), auxiliary part 2: partition trees

Facts about well-formed partition trees (`CutTree.WF`) used to build chain records:

* the ancestry of a node (`wf_take`), child time intervals, and bounds along a chain;
* the child polygon `childPoly` of an internal node (vertices `x_{u i}`, then `y_u`), its
  length `S_u`, and the identities `G_u = ⟨φ, ν_{[x,y]} - ν_{Q_u}⟩` (small excess) and
  `G_u = ⟨φ, ν_{[x,y]} - ν_{[x_v,y_v]}⟩` for an adverse child `v` (large excess);
* consequences of `A_u ≤ 1`: at most `3M` children, `S_u - R_u ≤ 2 R_u A_u`, bins.
-/

noncomputable section

open Real Set
open scoped Classical

namespace LQGDimension.LFPPRecords

open Blueprint.Draft

variable {γ : ℝ → ℂ} {M : ℕ} {ε : ℝ} {T : CutTree}

/-! ## Ancestry -/

theorem wf_take (hT : T.WF γ M ε) (N : ℕ) : ∀ v ∈ T.nodes, v.length = N →
    ∀ j < N, v.take j ∈ T.nodes ∧ ∃ i < T.nch (v.take j), v.take (j + 1) = v.take j ++ [i] := by
  induction N with
  | zero => intro v _ _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ N ih =>
    intro v hv hlen j hj
    rcases hT.is_child v hv with h0 | ⟨u, hu, i, hi, rfl⟩
    · subst h0; simp at hlen
    · have hlu : u.length = N := by simpa using hlen
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hjN
      · obtain ⟨h1, i', hi', h2⟩ := ih u hu hlu j hj'
        have e1 : (u ++ [i]).take j = u.take j := List.take_append_of_le_length (by omega)
        have e2 : (u ++ [i]).take (j + 1) = u.take (j + 1) :=
          List.take_append_of_le_length (by omega)
        rw [e1, e2]; exact ⟨h1, i', hi', h2⟩
      · obtain rfl : j = u.length := by omega
        have e1 : (u ++ [i]).take u.length = u := by simp
        have e2 : (u ++ [i]).take (u.length + 1) = u ++ [i] := by simp
        rw [e1, e2]
        exact ⟨hu, i, hi, rfl⟩

theorem child_t0_ge (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) :
    ∀ i < T.nch u, T.t₀ u ≤ T.t₀ (u ++ [i]) := by
  intro i
  induction i with
  | zero => intro h; rw [(hT.consecutive u hu (by omega)).1]
  | succ i ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hT.time_le _ (hT.child_mem u hu i (by omega))
    rw [← (hT.consecutive u hu (by omega)).2.2 i h]
    linarith

theorem child_t1_le (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) :
    ∀ i < T.nch u, T.t₁ (u ++ [i]) ≤ T.t₁ u := by
  suffices H : ∀ d i, i + d + 1 = T.nch u → T.t₁ (u ++ [i]) ≤ T.t₁ u by
    intro i hi; exact H (T.nch u - 1 - i) i (by omega)
  intro d
  induction d with
  | zero =>
    intro i hi
    have := (hT.consecutive u hu (by omega)).2.1
    rw [show i = T.nch u - 1 by omega, this]
  | succ d ih =>
    intro i hi
    have h1 := ih (i + 1) (by omega)
    have h2 := hT.time_le _ (hT.child_mem u hu (i + 1) (by omega))
    rw [(hT.consecutive u hu (by omega)).2.2 i (by omega)]
    linarith

theorem R_nonneg (u : List ℕ) : 0 ≤ T.R γ u := norm_nonneg _

theorem R_child_le (hT : T.WF γ M ε) (hM : 2 ≤ M) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) : T.R γ (u ++ [i]) ≤ T.R γ u := by
  have h := (hT.scale u hu i hi).2
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hR := R_nonneg (T := T) (γ := γ) u
  calc T.R γ (u ++ [i]) ≤ 3 * T.R γ u / (2 * M) := h
    _ ≤ T.R γ u := by rw [div_le_iff₀ (by positivity)]; nlinarith

/-- Along the ancestry of a node: membership, times in `[0,1]`, chords at most the root chord. -/
theorem chain_props (hT : T.WF γ M ε) (hM : 2 ≤ M) {v : List ℕ} (hv : v ∈ T.nodes) :
    ∀ j ≤ v.length, v.take j ∈ T.nodes ∧ 0 ≤ T.t₀ (v.take j) ∧ T.t₁ (v.take j) ≤ 1 ∧
      T.R γ (v.take j) ≤ T.R γ [] := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [List.take_zero]
    exact ⟨hT.root_mem, hT.root_time.1.ge, hT.root_time.2.le, le_rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    obtain ⟨_, i, hi, he⟩ := wf_take hT v.length v hv rfl j (by omega)
    rw [he]
    refine ⟨hT.child_mem _ h1 i hi, ?_, ?_, ?_⟩
    · linarith [child_t0_ge hT h1 i hi]
    · linarith [child_t1_le hT h1 i hi]
    · linarith [R_child_le hT hM h1 hi]

theorem root_R (hT : T.WF γ M ε) (hγ0 : γ 0 = 0) (hγ1 : γ 1 = 1) : T.R γ [] = 1 := by
  simp [CutTree.R, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2, hγ0, hγ1]

theorem root_x (hT : T.WF γ M ε) (hγ0 : γ 0 = 0) : T.x γ [] = 0 := by
  simp [CutTree.x, hT.root_time.1, hγ0]

theorem root_y (hT : T.WF γ M ε) (hγ1 : γ 1 = 1) : T.y γ [] = 1 := by
  simp [CutTree.y, hT.root_time.2, hγ1]

theorem norm_path_le_four (hT : T.WF γ M ε) (hγ0 : γ 0 = 0) (hγ1 : γ 1 = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖γ t‖ ≤ 4 := by
  have := hT.ball [] hT.root_mem t (by rw [hT.root_time.1, hT.root_time.2]; exact ⟨ht0, ht1⟩)
  rwa [root_x hT hγ0, root_R hT hγ0 hγ1, sub_zero, mul_one] at this

/-- Child endpoints lie in the ball `B(x_u, 4 R_u)`. -/
theorem child_ball (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) :
    ‖T.x γ (u ++ [i]) - T.x γ u‖ ≤ 4 * T.R γ u ∧ ‖T.y γ (u ++ [i]) - T.x γ u‖ ≤ 4 * T.R γ u := by
  have h0 := child_t0_ge hT hu i hi
  have h1 := child_t1_le hT hu i hi
  have hc := hT.time_le _ (hT.child_mem u hu i hi)
  exact ⟨hT.ball u hu _ ⟨h0, by linarith⟩, hT.ball u hu _ ⟨by linarith, h1⟩⟩

/-! ## The child polygon -/

/-- Vertices of the child polygon of `u`: `x_{u0}, x_{u1}, …, x_{u(m-1)}, y_u`. -/
def vf (T : CutTree) (γ : ℝ → ℂ) (u : List ℕ) (i : ℕ) : ℂ :=
  if i < T.nch u then T.x γ (u ++ [i]) else T.y γ u

/-- The child polygon `Q_u`. -/
def childPoly (T : CutTree) (γ : ℝ → ℂ) (u : List ℕ) : List ℂ :=
  (List.range (T.nch u + 1)).map (vf T γ u)

section childPoly

variable (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hm : 0 < T.nch u)
include hT hu hm

theorem vf_zero : vf T γ u 0 = T.x γ u := by
  simp only [vf, hm, ↓reduceIte, CutTree.x]
  rw [(hT.consecutive u hu hm).1]

omit hT hu hm in
theorem vf_nch : vf T γ u (T.nch u) = T.y γ u := by
  simp [vf]

omit hT hu hm in
theorem vf_of_lt {i : ℕ} (hi : i < T.nch u) : vf T γ u i = T.x γ (u ++ [i]) := by
  simp [vf, hi]

theorem vf_succ {i : ℕ} (hi : i < T.nch u) : vf T γ u (i + 1) = T.y γ (u ++ [i]) := by
  by_cases h : i + 1 < T.nch u
  · simp only [vf, h, ↓reduceIte, CutTree.x, CutTree.y]
    rw [(hT.consecutive u hu hm).2.2 i h]
  · have e : i = T.nch u - 1 := by omega
    rw [show i + 1 = T.nch u by omega, vf_nch]
    simp only [CutTree.y]
    rw [e, (hT.consecutive u hu hm).2.1]

theorem vf_edge {i : ℕ} (hi : i < T.nch u) :
    ‖vf T γ u (i + 1) - vf T γ u i‖ = T.R γ (u ++ [i]) := by
  rw [vf_succ hT hu hm hi, vf_of_lt hi]
  rfl

theorem vf_chord : ‖vf T γ u (T.nch u) - vf T γ u 0‖ = T.R γ u := by
  rw [vf_nch, vf_zero hT hu hm]; rfl

theorem vf_sum : ∑ i ∈ Finset.range (T.nch u), ‖vf T γ u (i + 1) - vf T γ u i‖ = T.S γ u :=
  Finset.sum_congr rfl fun _ hi => vf_edge hT hu hm (Finset.mem_range.mp hi)

theorem polyAvg_childPoly (φ : ℂ → ℝ) :
    polyAvg φ (childPoly T γ u) =
      ∑ i ∈ Finset.range (T.nch u), (T.R γ (u ++ [i]) / T.S γ u) * T.H γ φ (u ++ [i]) := by
  rw [childPoly, polyAvg_range_map, vf_sum hT hu hm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [vf_edge hT hu hm hi', vf_of_lt hi', vf_succ hT hu hm hi']
  rfl

theorem R_le_S : T.R γ u ≤ T.S γ u := by
  rw [← vf_chord hT hu hm, ← vf_sum hT hu hm, ← Finset.sum_range_sub]
  exact norm_sum_le _ _

theorem G_small (hR : 0 < T.R γ u) (φ : ℂ → ℝ) (hA : T.A γ u ≤ 1) :
    T.G γ φ u = polyAvg φ [T.x γ u, T.y γ u] - polyAvg φ (childPoly T γ u) := by
  have hxy : T.x γ u ≠ T.y γ u := by
    intro h; rw [CutTree.R, h, sub_self, norm_zero] at hR; exact lt_irrefl _ hR
  rw [CutTree.G]
  simp only [hA, ↓reduceIte]
  rw [polyAvg_pair φ hxy, polyAvg_childPoly hT hu hm]
  rfl

theorem G_large (hM : 0 < M) (hR : 0 < T.R γ u) (φ : ℂ → ℝ) (hA : ¬ T.A γ u ≤ 1) :
    ∃ i < T.nch u, T.G γ φ u =
      polyAvg φ [T.x γ u, T.y γ u] - polyAvg φ [T.x γ (u ++ [i]), T.y γ (u ++ [i])] := by
  have : Nonempty (Fin (T.nch u)) := ⟨⟨0, hm⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin (T.nch u) => T.H γ φ u - T.H γ φ (u ++ [(i : ℕ)]))
  refine ⟨i, i.2, ?_⟩
  have hxy : T.x γ u ≠ T.y γ u := by
    intro h; rw [CutTree.R, h, sub_self, norm_zero] at hR; exact lt_irrefl _ hR
  have hRi : 0 < T.R γ (u ++ [(i : ℕ)]) := by
    have := (hT.scale u hu i i.2).1
    have : 0 < T.R γ u / (2 * M) := by
      apply div_pos hR
      have : (0 : ℝ) < M := by exact_mod_cast hM
      linarith
    linarith
  have hxy' : T.x γ (u ++ [(i : ℕ)]) ≠ T.y γ (u ++ [(i : ℕ)]) := by
    intro h; rw [CutTree.R, h, sub_self, norm_zero] at hRi; exact lt_irrefl _ hRi
  rw [CutTree.G]
  simp only [hA, ↓reduceIte]
  rw [← hi, polyAvg_pair φ hxy, polyAvg_pair φ hxy']
  rfl

end childPoly

/-! ## Consequences of small excess -/

section excess

variable (hT : T.WF γ M ε) {u : List ℕ} (hu : u ∈ T.nodes) (hm : 0 < T.nch u)
  (hR : 0 < T.R γ u)
include hT hu hm hR

theorem S_pos : 0 < T.S γ u := lt_of_lt_of_le hR (R_le_S hT hu hm)

theorem A_nonneg : 0 ≤ T.A γ u := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hR, one_mul]
  exact R_le_S hT hu hm

theorem S_div_R : T.S γ u / T.R γ u = Real.exp (T.A γ u) := by
  rw [CutTree.A, Real.exp_log (div_pos (S_pos hT hu hm hR) hR)]

theorem S_sub_R_le (hA : T.A γ u ≤ 1) : T.S γ u - T.R γ u ≤ 2 * T.R γ u * T.A γ u := by
  have h0 := A_nonneg hT hu hm hR
  have h1 : |Real.exp (T.A γ u) - 1| ≤ 2 * |T.A γ u| :=
    Real.abs_exp_sub_one_le (by rw [abs_of_nonneg h0]; exact hA)
  rw [abs_of_nonneg h0] at h1
  have h2 := (abs_le.mp h1).2
  have hS : T.S γ u = T.R γ u * Real.exp (T.A γ u) := by
    rw [← S_div_R hT hu hm hR]; field_simp
  rw [hS]
  nlinarith

theorem nch_le (hM : 2 ≤ M) (hA : T.A γ u ≤ 1) : T.nch u ≤ 3 * M := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hS : T.S γ u ≤ 3 * T.R γ u := by
    have h1 := S_sub_R_le hT hu hm hR hA
    nlinarith
  -- lower bound on `S` from the regular children
  set m := T.nch u with hmdef
  have hsplit : T.S γ u = ∑ i ∈ Finset.range (m - 1), T.R γ (u ++ [i]) + T.R γ (u ++ [m - 1]) := by
    rw [CutTree.S, ← hmdef, show m = (m - 1) + 1 by omega, Finset.sum_range_succ]
    simp
  have hreg : ∑ i ∈ Finset.range (m - 1), T.R γ (u ++ [i]) = (m - 1 : ℕ) * (T.R γ u / M) := by
    have : ∀ i ∈ Finset.range (m - 1), T.R γ (u ++ [i]) = T.R γ u / M := fun i hi =>
      hT.regular u hu i (by rw [Finset.mem_range] at hi; omega)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hlast := (hT.scale u hu (m - 1) (by omega)).1
  have key : ((m - 1 : ℕ) : ℝ) * (T.R γ u / M) + T.R γ u / (2 * M) ≤ 3 * T.R γ u := by
    rw [hsplit, hreg] at hS; linarith
  have key2 : (((m - 1 : ℕ) : ℝ) + 1 / 2) ≤ 3 * M := by
    have e : ((m - 1 : ℕ) : ℝ) * (T.R γ u / M) + T.R γ u / (2 * M) =
        (((m - 1 : ℕ) : ℝ) + 1 / 2) * T.R γ u / M := by
      field_simp
    rw [e, div_le_iff₀ hMpos] at key
    nlinarith
  have : ((m - 1 : ℕ) : ℝ) < 3 * M := by linarith
  have : m - 1 < 3 * M := by exact_mod_cast this
  omega

end excess

/-! ## Bins -/

theorem kbin_small {δ : ℝ} (hδ : 0 < δ) {u : List ℕ} (hA0 : 0 ≤ T.A γ u) (hA : T.A γ u ≤ 1) :
    (T.kbin γ δ u : ℝ) * δ ^ 2 ≤ T.A γ u ∧ T.A γ u < ((T.kbin γ δ u : ℝ) + 1) * δ ^ 2 := by
  have hd : 0 < δ ^ 2 := by positivity
  have e : T.kbin γ δ u = ⌊T.A γ u / δ ^ 2⌋₊ := by rw [CutTree.kbin, min_eq_left hA]
  rw [e]
  constructor
  · have := Nat.floor_le (div_nonneg hA0 hd.le)
    rwa [le_div_iff₀ hd] at this
  · have := Nat.lt_floor_add_one (T.A γ u / δ ^ 2)
    rwa [div_lt_iff₀ hd] at this

theorem kbin_large {δ : ℝ} {u : List ℕ} (hA : ¬ T.A γ u ≤ 1) :
    T.kbin γ δ u = ⌊δ ^ (-2 : ℤ)⌋₊ := by
  rw [CutTree.kbin, min_eq_right (le_of_lt (not_le.mp hA))]
  congr 1
  rw [zpow_neg, zpow_ofNat, one_div]

theorem kbin_le {δ : ℝ} (u : List ℕ) : T.kbin γ δ u ≤ ⌊δ ^ (-2 : ℤ)⌋₊ := by
  rw [CutTree.kbin, zpow_neg, zpow_ofNat, ← one_div]
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg δ)

end LQGDimension.LFPPRecords
