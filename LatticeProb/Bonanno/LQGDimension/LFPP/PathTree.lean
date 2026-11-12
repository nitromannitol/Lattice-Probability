/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.PathTree at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
# The partition tree of Section 4.1: nodes `T41` (`PathTreeExists`) and `CL`

* `pathTreeExists : Blueprint.Draft.PathTreeExists` — the recursive first-exit construction:
  a node on `[a, b]` with chord `R > ε` is cut at the successive first times the path is at
  distance `r = R / M` from the previous cut point; the terminal residual piece is kept if its
  chord exceeds `r / 2`, and otherwise merged with the preceding complete piece.
  Finiteness of the number of complete pieces comes from uniform continuity of the path on
  `[0, 1]` (each complete piece has chord `r`, hence time-length at least some `η > 0`).

* `chainLengthBounds : Blueprint.Draft.ChainLengthBounds` — depth bounds for leaves.  (The
  node assumes `IsAdmissiblePath γ`, which excludes the constant path; only `γ 0 = 0`, `γ 1 = 1`
  is used.)
-/

noncomputable section

open Set

namespace LQGDimension.LFPPTree

open Blueprint.Draft

/-! ## Chain lengths (node `CL`) -/

section ChainLength

variable {γ : ℝ → ℂ} {M : ℕ} {ε : ℝ} {T : CutTree}

/-- Along the ancestry, chords shrink by a factor in `[1/(2M), 3/(2M)]` per generation. -/
theorem wf_R_bounds (hT : T.WF γ M ε) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n →
      (1 / (2 * (M : ℝ))) ^ n * T.R γ [] ≤ T.R γ v ∧
        T.R γ v ≤ (3 / (2 * (M : ℝ))) ^ n * T.R γ [] := by
  induction n with
  | zero =>
    intro v _ hv
    cases v with
    | nil => simp
    | cons a l => simp at hv
  | succ n ih =>
    intro v hv hlen
    rcases hT.is_child v hv with h0 | ⟨u, hu, i, hi, rfl⟩
    · subst h0; simp at hlen
    · have hlu : u.length = n := by simpa using hlen
      obtain ⟨ih1, ih2⟩ := ih u hu hlu
      obtain ⟨hs1, hs2⟩ := hT.scale u hu i hi
      constructor
      · calc (1 / (2 * (M : ℝ))) ^ (n + 1) * T.R γ []
            = (1 / (2 * (M : ℝ))) * ((1 / (2 * (M : ℝ))) ^ n * T.R γ []) := by ring
          _ ≤ (1 / (2 * (M : ℝ))) * T.R γ u := by gcongr
          _ = T.R γ u / (2 * M) := by ring
          _ ≤ T.R γ (u ++ [i]) := hs1
      · calc T.R γ (u ++ [i]) ≤ 3 * T.R γ u / (2 * M) := hs2
          _ = (3 / (2 * (M : ℝ))) * T.R γ u := by ring
          _ ≤ (3 / (2 * (M : ℝ))) * ((3 / (2 * (M : ℝ))) ^ n * T.R γ []) := by gcongr
          _ = (3 / (2 * (M : ℝ))) ^ (n + 1) * T.R γ [] := by ring

/-- The depth bounds of `CL`, for a well-formed tree whose root chord has length `1`. -/
theorem chainLength_of_rootChord (hM : 16 ≤ M) (hε : ε ∈ Ioo (0 : ℝ) 1) (hT : T.WF γ M ε)
    (hroot : T.R γ [] = 1) {v : List ℕ} (hv : v ∈ T.leaves) :
    Real.log (1 / ε) / Real.log (2 * M) ≤ v.length ∧
      (v.length : ℝ) ≤ Real.log (1 / ε) / Real.log (2 * M / 3) + 1 := by
  obtain ⟨hε0, hε1⟩ := hε
  simp only [CutTree.leaves, Finset.mem_filter] at hv
  obtain ⟨hvn, hv0⟩ := hv
  have hMr : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hRv : T.R γ v ≤ ε := by
    by_contra h
    have := (hT.internal_iff v hvn).mpr (lt_of_not_ge h)
    omega
  have hinvε : Real.log (1 / ε) = - Real.log ε := by rw [one_div, Real.log_inv]
  constructor
  · have hlow := (wf_R_bounds hT v.length v hvn rfl).1
    rw [hroot, mul_one] at hlow
    have h1 : (1 / (2 * (M : ℝ))) ^ v.length ≤ ε := hlow.trans hRv
    have hlog2M : 0 < Real.log (2 * M) := Real.log_pos (by linarith)
    rw [div_le_iff₀ hlog2M, hinvε]
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, one_div, Real.log_inv, mul_neg] at this
    linarith
  · rcases hT.is_child v hvn with h0 | ⟨u, hu, i, hi, rfl⟩
    · subst h0
      have : 0 ≤ Real.log (1 / ε) / Real.log (2 * M / 3) :=
        div_nonneg (Real.log_nonneg (one_le_one_div hε0 hε1.le)) (Real.log_nonneg (by linarith))
      simp only [List.length_nil, Nat.cast_zero]
      linarith
    · have hRu : ε < T.R γ u := (hT.internal_iff u hu).mp (by omega)
      have hup := (wf_R_bounds hT u.length u hu rfl).2
      rw [hroot, mul_one] at hup
      have h2 : ε < (3 / (2 * (M : ℝ))) ^ u.length := hRu.trans_le hup
      have hlog : 0 < Real.log (2 * M / 3) := Real.log_pos (by linarith)
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      rw [add_le_add_iff_right, le_div_iff₀ hlog, hinvε]
      have := Real.log_lt_log hε0 h2
      have e : (3 / (2 * (M : ℝ))) = (2 * (M : ℝ) / 3)⁻¹ := by rw [inv_div]
      rw [Real.log_pow, e, Real.log_inv, mul_neg] at this
      linarith

/-- **Node `CL`.** -/
theorem chainLengthBounds : ChainLengthBounds := by
  intro γ hγ M hM ε hε T hT v hv
  refine chainLength_of_rootChord hM hε hT ?_ hv
  simp [CutTree.R, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2, hγ.source, hγ.target]

end ChainLength

/-! ## One level of the construction: first-exit cuts -/

section Cuts

variable (γ : ℝ → ℂ) (b r : ℝ)

/-- Times in `[s, b]` at which the path is at distance at least `r` from `γ s`. -/
def exitSet (s : ℝ) : Set ℝ := {t | t ∈ Icc s b ∧ r ≤ ‖γ t - γ s‖}

open scoped Classical in
/-- The first time after `s` at which the path is at distance `r` from `γ s`, or `b` if there
is none. -/
def nextCut (s : ℝ) : ℝ := if (exitSet γ b r s).Nonempty then sInf (exitSet γ b r s) else b

/-- The successive cut times, starting at `a`. -/
def cutSeq (a : ℝ) : ℕ → ℝ
  | 0 => a
  | k + 1 => nextCut γ b r (cutSeq a k)

variable {γ b r}

theorem cutSeq_zero (a : ℝ) : cutSeq γ b r a 0 = a := rfl

theorem cutSeq_succ (a : ℝ) (k : ℕ) :
    cutSeq γ b r a (k + 1) = nextCut γ b r (cutSeq γ b r a k) := rfl

theorem nextCut_bounds {s : ℝ} (hs : s ≤ b) : s ≤ nextCut γ b r s ∧ nextCut γ b r s ≤ b := by
  unfold nextCut
  split_ifs with hne
  · have hbdd : BddBelow (exitSet γ b r s) := ⟨s, fun t ht => ht.1.1⟩
    obtain ⟨t, ht⟩ := hne
    exact ⟨le_csInf ⟨t, ht⟩ fun t' ht' => ht'.1.1, (csInf_le hbdd ht).trans ht.1.2⟩
  · exact ⟨hs, le_rfl⟩

theorem isClosed_exitSet {a s : ℝ} (hγ : ContinuousOn γ (Icc a b)) (has : a ≤ s) :
    IsClosed (exitSet γ b r s) := by
  have hc : ContinuousOn (fun t => ‖γ t - γ s‖) (Icc s b) :=
    ((hγ.mono (Icc_subset_Icc_left has)).sub continuousOn_const).norm
  exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici

/-- A complete first-exit piece: its chord is exactly `r`, and the path stays in the closed
`r`-ball around its starting point. -/
theorem nextCut_spec {a s : ℝ} (hγ : ContinuousOn γ (Icc a b)) (has : a ≤ s)
    (hne : (exitSet γ b r s).Nonempty) (hr : 0 ≤ r) :
    ‖γ (nextCut γ b r s) - γ s‖ = r ∧ ∀ t ∈ Icc s (nextCut γ b r s), ‖γ t - γ s‖ ≤ r := by
  have hbdd : BddBelow (exitSet γ b r s) := ⟨s, fun t ht => ht.1.1⟩
  have hmem : sInf (exitSet γ b r s) ∈ exitSet γ b r s :=
    (isClosed_exitSet hγ has).csInf_mem hne hbdd
  have hnc : nextCut γ b r s = sInf (exitSet γ b r s) := by rw [nextCut, ite_eq_left hne]
  rw [hnc]
  obtain ⟨⟨hsτ, hτb⟩, hrτ⟩ := hmem
  have hc : ContinuousOn (fun t => ‖γ t - γ s‖) (Icc s (sInf (exitSet γ b r s))) :=
    ((hγ.mono (Icc_subset_Icc has hτb)).sub continuousOn_const).norm
  have heq : ‖γ (sInf (exitSet γ b r s)) - γ s‖ = r := by
    obtain ⟨c, ⟨hsc, hcτ⟩, hcr⟩ :=
      intermediate_value_Icc hsτ hc ⟨by simpa using hr, hrτ⟩
    have hcE : c ∈ exitSet γ b r s := ⟨⟨hsc, hcτ.trans hτb⟩, hcr.ge⟩
    have hτc : sInf (exitSet γ b r s) ≤ c := csInf_le hbdd hcE
    have hcτ' : c = sInf (exitSet γ b r s) := le_antisymm hcτ hτc
    rw [← hcτ']
    exact hcr
  refine ⟨heq, fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h, heq]
  · by_contra hlt
    have htE : t ∈ exitSet γ b r s := ⟨⟨ht.1, h.le.trans hτb⟩, (lt_of_not_ge hlt).le⟩
    exact (not_le.mpr h) (csInf_le hbdd htE)

/-- The terminal residual piece: the path stays in the open `r`-ball. -/
theorem nextCut_of_empty {s : ℝ} (hne : ¬(exitSet γ b r s).Nonempty) :
    nextCut γ b r s = b ∧ ∀ t ∈ Icc s b, ‖γ t - γ s‖ < r := by
  refine ⟨by rw [nextCut, ite_eq_right hne], fun t ht => ?_⟩
  by_contra h
  exact hne ⟨t, ht, not_lt.mp h⟩

/-- Uniform continuity: complete pieces have time-length bounded below. -/
theorem exists_gap {a : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hr : 0 < r) :
    ∃ η > 0, ∀ s ∈ Icc a b, (exitSet γ b r s).Nonempty → s + η ≤ nextCut γ b r s := by
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ) r hr
  refine ⟨η, hη, fun s hs hne => ?_⟩
  obtain ⟨h1, h2⟩ := nextCut_bounds (γ := γ) (r := r) hs.2
  have hspec := (nextCut_spec hγ hs.1 hne hr.le).1
  by_contra hlt
  push Not at hlt
  have hd : dist (nextCut γ b r s) s < η := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have := hU _ ⟨hs.1.trans h1, h2⟩ s hs hd
  rw [dist_eq_norm, hspec] at this
  exact lt_irrefl _ this

theorem cutSeq_mem {a : ℝ} (hab : a ≤ b) (k : ℕ) : cutSeq γ b r a k ∈ Icc a b := by
  induction k with
  | zero => exact ⟨le_rfl, hab⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := nextCut_bounds (γ := γ) (r := r) ih.2
    exact ⟨ih.1.trans h1, h2⟩

theorem cutSeq_le_succ {a : ℝ} (hab : a ≤ b) (k : ℕ) :
    cutSeq γ b r a k ≤ cutSeq γ b r a (k + 1) :=
  (nextCut_bounds (cutSeq_mem hab k).2).1

/-- There are only finitely many complete first-exit pieces. -/
theorem exists_stop {a : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b) (hr : 0 < r) :
    ∃ k, ¬(exitSet γ b r (cutSeq γ b r a k)).Nonempty := by
  obtain ⟨η, hη, hgap⟩ := exists_gap hγ hr
  by_contra hall
  have hall' : ∀ k, (exitSet γ b r (cutSeq γ b r a k)).Nonempty :=
    fun k => not_not.mp fun h => hall ⟨k, h⟩
  have hgrow : ∀ k : ℕ, a + k * η ≤ cutSeq γ b r a k := by
    intro k
    induction k with
    | zero => simp [cutSeq_zero]
    | succ k ih =>
      have := hgap _ (cutSeq_mem hab k) (hall' k)
      rw [Nat.cast_succ, cutSeq_succ]
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / η)
  have h1 := hgrow k
  have h2 := (cutSeq_mem (γ := γ) (r := r) hab k).2
  rw [div_lt_iff₀ hη] at hk
  linarith

/-- The children of one node: `n` consecutive time intervals `c 0, …, c (n-1)` of `[a, b]`
with the properties required by `CutTree.WF` (with `r = R / M`). -/
structure IsCutting (γ : ℝ → ℂ) (a b r : ℝ) (n : ℕ) (c : ℕ → ℝ × ℝ) : Prop where
  pos : 0 < n
  first : (c 0).1 = a
  last : (c (n - 1)).2 = b
  consec : ∀ i, i + 1 < n → (c i).2 = (c (i + 1)).1
  mem : ∀ i < n, a ≤ (c i).1 ∧ (c i).1 ≤ (c i).2 ∧ (c i).2 ≤ b
  chord : ∀ i < n, r / 2 ≤ ‖γ (c i).2 - γ (c i).1‖ ∧ ‖γ (c i).2 - γ (c i).1‖ ≤ 3 * r / 2
  regular : ∀ i, i + 1 < n → ‖γ (c i).2 - γ (c i).1‖ = r
  ball : ∀ i < n, ∀ t ∈ Icc (c i).1 (c i).2,
    ‖γ t - γ (c i).1‖ ≤ 4 * ‖γ (c i).2 - γ (c i).1‖

/-- **One step of the construction of Section 4.1.**  Cut at successive first displacements of
length `r`; keep the terminal residual piece if its chord exceeds `r / 2`, and otherwise merge
it with the preceding complete piece. -/
theorem exists_isCutting {a : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b) (hr : 0 < r)
    (hR : r ≤ ‖γ b - γ a‖) : ∃ n c, IsCutting γ a b r n c := by
  set s := cutSeq γ b r a with hs_def
  obtain ⟨m, hm, hlt⟩ : ∃ m, ¬(exitSet γ b r (s m)).Nonempty ∧
      ∀ k < m, (exitSet γ b r (s k)).Nonempty := by
    classical
    exact ⟨Nat.find (exists_stop hγ hab hr), Nat.find_spec (exists_stop hγ hab hr),
      fun k hk => not_not.mp (Nat.find_min (exists_stop hγ hab hr) hk)⟩
  have hmem : ∀ k, s k ∈ Icc a b := cutSeq_mem hab
  have hsucc : ∀ k, s (k + 1) = nextCut γ b r (s k) := fun k => rfl
  have hcomp : ∀ k < m, ‖γ (s (k + 1)) - γ (s k)‖ = r ∧
      ∀ t ∈ Icc (s k) (s (k + 1)), ‖γ t - γ (s k)‖ ≤ r := by
    intro k hk
    rw [hsucc]
    exact nextCut_spec hγ (hmem k).1 (hlt k hk) hr.le
  have hle : ∀ k, s k ≤ s (k + 1) := fun k => cutSeq_le_succ hab k
  obtain ⟨hlast, hres⟩ := nextCut_of_empty hm
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      subst h
      exact hm ⟨b, ⟨(hmem 0).2, le_rfl⟩, hR⟩
    · exact h
  have hρ : ‖γ b - γ (s m)‖ < r := hres b ⟨(hmem m).2, le_rfl⟩
  by_cases hkeep : r / 2 < ‖γ b - γ (s m)‖
  · -- keep the residual piece
    have hsm1 : s (m + 1) = b := by rw [hsucc]; exact hlast
    refine ⟨m + 1, fun i => (s i, s (i + 1)), Nat.succ_pos m, rfl, ?_, fun i _ => rfl,
      ?_, ?_, ?_, ?_⟩
    · simpa using hsm1
    · intro i _
      exact ⟨(hmem i).1, hle i, (hmem (i + 1)).2⟩
    · intro i hi
      dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(hcomp i hi).1]; constructor <;> linarith
      · rw [hsm1]; constructor <;> linarith
    · intro i hi
      exact (hcomp i (by omega)).1
    · intro i hi t ht
      dsimp only at ht ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have := (hcomp i hi).2 t ht
        rw [(hcomp i hi).1]; linarith
      · rw [hsm1] at ht ⊢
        have := hres t ht
        linarith
  · -- merge the residual piece with the last complete piece
    push Not at hkeep
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm0
    refine ⟨m, fun i => (s i, if i + 1 = m then b else s (i + 1)), hm0, rfl, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · dsimp only; rw [ite_eq_left hm1]
    · intro i hi; dsimp only; rw [ite_eq_right (by omega)]
    · intro i _
      dsimp only
      refine ⟨(hmem i).1, ?_, ?_⟩
      · split_ifs
        · exact (hmem i).2
        · exact hle i
      · split_ifs
        · exact le_rfl
        · exact (hmem (i + 1)).2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hc := (hcomp i (by omega)).1
        rw [h] at hc
        have t1 := norm_sub_le_norm_sub_add_norm_sub (γ b) (γ (s m)) (γ (s i))
        have t2 := norm_sub_le_norm_sub_add_norm_sub (γ (s m)) (γ b) (γ (s i))
        rw [norm_sub_rev (γ (s m)) (γ b)] at t2
        constructor <;> linarith
      · rw [(hcomp i (by omega)).1]; constructor <;> linarith
    · intro i hi
      dsimp only
      rw [ite_eq_right (by omega)]
      exact (hcomp i (by omega)).1
    · intro i hi t ht
      dsimp only at ht ⊢
      split_ifs at ht ⊢ with h
      · have hc := hcomp i (by omega)
        rw [h] at hc
        have t2 := norm_sub_le_norm_sub_add_norm_sub (γ (s m)) (γ b) (γ (s i))
        rw [norm_sub_rev (γ (s m)) (γ b)] at t2
        rcases le_total t (s m) with htm | htm
        · have := hc.2 t ⟨ht.1, htm⟩
          linarith
        · have h3 := hres t ⟨htm, ht.2⟩
          have t3 := norm_sub_le_norm_sub_add_norm_sub (γ t) (γ (s m)) (γ (s i))
          linarith
      · have := (hcomp i (by omega)).2 t ht
        rw [(hcomp i (by omega)).1]; linarith

end Cuts

/-! ## The tree -/

section Tree

variable (γ : ℝ → ℂ) (M : ℕ) (ε : ℝ)

/-- Chord length of the subpath on the time interval `I`. -/
def chordLen (I : ℝ × ℝ) : ℝ := ‖γ I.2 - γ I.1‖

/-- The time interval `I ⊆ [0, 1]` is an internal node (its chord exceeds `ε`). -/
def IsSplit (I : ℝ × ℝ) : Prop := 0 ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ 1 ∧ ε < chordLen γ I

open scoped Classical in
/-- Number of children and children's time intervals of the node with time interval `I`. -/
def cutData (I : ℝ × ℝ) : ℕ × (ℕ → ℝ × ℝ) :=
  if h : IsSplit γ ε I ∧
      ∃ p : ℕ × (ℕ → ℝ × ℝ), IsCutting γ I.1 I.2 (chordLen γ I / M) p.1 p.2
  then h.2.choose else (0, fun _ => I)

/-- Time interval of the node with address `u`. -/
def ival (u : List ℕ) : ℝ × ℝ := u.foldl (fun I i => (cutData γ M ε I).2 i) (0, 1)

/-- Number of children of the node with address `u`. -/
def nchT (u : List ℕ) : ℕ := (cutData γ M ε (ival γ M ε u)).1

/-- The addresses at depth `d`. -/
def lvl : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | d + 1 => (lvl d).biUnion fun u => (Finset.range (nchT γ M ε u)).image fun i => u ++ [i]

/-- The partition tree, truncated at depth `D`. -/
def treeOf (D : ℕ) : CutTree where
  nodes := (Finset.range (D + 1)).biUnion (lvl γ M ε)
  t₀ u := (ival γ M ε u).1
  t₁ u := (ival γ M ε u).2
  nch := nchT γ M ε

variable {γ M ε}

theorem ival_append (u : List ℕ) (i : ℕ) :
    ival γ M ε (u ++ [i]) = (cutData γ M ε (ival γ M ε u)).2 i := by
  simp [ival, List.foldl_append]

theorem cutData_spec {I : ℝ × ℝ} (hsplit : IsSplit γ ε I)
    (hex : ∃ n c, IsCutting γ I.1 I.2 (chordLen γ I / M) n c) :
    IsCutting γ I.1 I.2 (chordLen γ I / M) (cutData γ M ε I).1 (cutData γ M ε I).2 := by
  have h : IsSplit γ ε I ∧
      ∃ p : ℕ × (ℕ → ℝ × ℝ), IsCutting γ I.1 I.2 (chordLen γ I / M) p.1 p.2 := by
    obtain ⟨n, c, hc⟩ := hex
    exact ⟨hsplit, ⟨(n, c), hc⟩⟩
  rw [cutData, dite_eq_left h]
  exact h.2.choose_spec

theorem cutData_of_not {I : ℝ × ℝ} (h : ¬ IsSplit γ ε I) : (cutData γ M ε I).1 = 0 := by
  rw [cutData, dite_eq_right (fun h' => h h'.1)]

theorem isCutting_of_split (hγc : ContinuousOn γ (Icc 0 1)) (hM : 1 ≤ M) (hε : 0 < ε)
    {I : ℝ × ℝ} (hI : IsSplit γ ε I) :
    IsCutting γ I.1 I.2 (chordLen γ I / M) (cutData γ M ε I).1 (cutData γ M ε I).2 := by
  apply cutData_spec hI
  obtain ⟨h0, h01, h1, hR⟩ := hI
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRpos : 0 < chordLen γ I := hε.trans hR
  exact exists_isCutting (hγc.mono (Icc_subset_Icc h0 h1)) h01 (div_pos hRpos (by linarith))
    (div_le_self hRpos.le hMr)

theorem lvl_inv (hγ0 : γ 0 = 0) (hγ1 : γ 1 = 1) (hγc : ContinuousOn γ (Icc 0 1)) (hM : 1 ≤ M)
    (hε : 0 < ε) (d : ℕ) :
    ∀ u ∈ lvl γ M ε d, u.length = d ∧ 0 ≤ (ival γ M ε u).1 ∧
      (ival γ M ε u).1 ≤ (ival γ M ε u).2 ∧ (ival γ M ε u).2 ≤ 1 ∧
      chordLen γ (ival γ M ε u) ≤ (3 / (2 * (M : ℝ))) ^ d := by
  induction d with
  | zero =>
    intro u hu
    simp only [lvl, Finset.mem_singleton] at hu
    subst hu
    simp [ival, chordLen, hγ0, hγ1]
  | succ d ih =>
    intro u hu
    simp only [lvl, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨w, hw, i, hi, rfl⟩ := hu
    obtain ⟨hlen, h0, h01, h1, hR⟩ := ih w hw
    have hsplit : IsSplit γ ε (ival γ M ε w) := by
      by_contra hns
      have := cutData_of_not (M := M) hns
      unfold nchT at hi
      omega
    have hC := isCutting_of_split hγc hM hε hsplit
    obtain ⟨hm1, hm2, hm3⟩ := hC.mem i hi
    have hch := (hC.chord i hi).2
    rw [ival_append]
    refine ⟨by simp [hlen], by linarith, hm2, by linarith, ?_⟩
    calc chordLen γ ((cutData γ M ε (ival γ M ε w)).2 i)
        ≤ 3 * (chordLen γ (ival γ M ε w) / M) / 2 := hch
      _ = (3 / (2 * (M : ℝ))) * chordLen γ (ival γ M ε w) := by ring
      _ ≤ (3 / (2 * (M : ℝ))) * (3 / (2 * (M : ℝ))) ^ d := by gcongr
      _ = (3 / (2 * (M : ℝ))) ^ (d + 1) := by ring

theorem treeOf_WF {γ : ℝ → ℂ} (hγ : IsAdmissiblePath γ) {M : ℕ} (hM : 16 ≤ M) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) {D : ℕ} (hD : (3 / (2 * (M : ℝ))) ^ D < ε) :
    (treeOf γ M ε D).WF γ M ε := by
  have hM1 : 1 ≤ M := by omega
  have hε0 := hε.1
  have hlvl := lvl_inv hγ.source hγ.target hγ.continuousOn hM1 hε0
  have hnodes : ∀ u, u ∈ (treeOf γ M ε D).nodes ↔ ∃ d, d ≤ D ∧ u ∈ lvl γ M ε d := by
    intro u
    simp only [treeOf, Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff]
  have hinv : ∀ u ∈ (treeOf γ M ε D).nodes, 0 ≤ (ival γ M ε u).1 ∧
      (ival γ M ε u).1 ≤ (ival γ M ε u).2 ∧ (ival γ M ε u).2 ≤ 1 := by
    intro u hu
    obtain ⟨d, -, hd⟩ := (hnodes u).mp hu
    obtain ⟨-, h0, h01, h1, -⟩ := hlvl d u hd
    exact ⟨h0, h01, h1⟩
  have hsplit : ∀ u, 0 < nchT γ M ε u → IsSplit γ ε (ival γ M ε u) := by
    intro u hpos
    by_contra hns
    have := cutData_of_not (M := M) hns
    unfold nchT at hpos
    omega
  have hcut : ∀ u, 0 < nchT γ M ε u →
      IsCutting γ (ival γ M ε u).1 (ival γ M ε u).2 (chordLen γ (ival γ M ε u) / M)
        (nchT γ M ε u) (fun i => ival γ M ε (u ++ [i])) := by
    intro u hpos
    have e : (fun i => ival γ M ε (u ++ [i])) = (cutData γ M ε (ival γ M ε u)).2 :=
      funext fun i => ival_append u i
    rw [e]
    exact isCutting_of_split hγ.continuousOn hM1 hε0 (hsplit u hpos)
  have hleaf : ∀ u ∈ lvl γ M ε D, nchT γ M ε u = 0 := by
    intro u hu
    obtain ⟨-, -, -, -, hR⟩ := hlvl D u hu
    apply cutData_of_not
    rintro ⟨-, -, -, hεR⟩
    linarith
  have hchild : ∀ v ∈ (treeOf γ M ε D).nodes, v = [] ∨ ∃ u ∈ (treeOf γ M ε D).nodes,
      ∃ i < (treeOf γ M ε D).nch u, v = u ++ [i] := by
    intro v hv
    obtain ⟨d, hdD, hd⟩ := (hnodes v).mp hv
    cases d with
    | zero =>
      left
      simpa [lvl] using hd
    | succ k =>
      right
      simp only [lvl, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hd
      obtain ⟨w, hw, i, hi, rfl⟩ := hd
      exact ⟨w, (hnodes w).mpr ⟨k, by omega, hw⟩, i, hi, rfl⟩
  refine
    { root_mem := (hnodes []).mpr ⟨0, Nat.zero_le _, by simp [lvl]⟩
      root_time := ⟨rfl, rfl⟩
      child_mem := ?_
      is_child := hchild
      time_le := fun u hu => (hinv u hu).2.1
      consecutive := ?_
      internal_iff := ?_
      scale := ?_
      regular := ?_
      ball := ?_ }
  · intro u hu i hi
    obtain ⟨d, hdD, hd⟩ := (hnodes u).mp hu
    rcases eq_or_lt_of_le hdD with h | h
    · subst h
      have := hleaf u hd
      change i < nchT γ M ε u at hi
      omega
    · refine (hnodes _).mpr ⟨d + 1, h, ?_⟩
      simp only [lvl, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
      exact ⟨u, hd, i, hi, rfl⟩
  · intro u _ hpos
    have hC := hcut u hpos
    exact ⟨hC.first, hC.last, hC.consec⟩
  · intro u hu
    change 0 < nchT γ M ε u ↔ ε < chordLen γ (ival γ M ε u)
    constructor
    · intro hpos
      exact (hsplit u hpos).2.2.2
    · intro hR
      obtain ⟨h0, h01, h1⟩ := hinv u hu
      exact (isCutting_of_split hγ.continuousOn hM1 hε0 ⟨h0, h01, h1, hR⟩).pos
  · intro u _ i hi
    have hC := hcut u (by change i < nchT γ M ε u at hi; omega)
    obtain ⟨h1, h2⟩ := hC.chord i hi
    change chordLen γ (ival γ M ε u) / (2 * M) ≤ chordLen γ (ival γ M ε (u ++ [i])) ∧
      chordLen γ (ival γ M ε (u ++ [i])) ≤ 3 * chordLen γ (ival γ M ε u) / (2 * M)
    constructor
    · calc chordLen γ (ival γ M ε u) / (2 * M) = chordLen γ (ival γ M ε u) / M / 2 := by ring
        _ ≤ _ := h1
    · calc _ ≤ 3 * (chordLen γ (ival γ M ε u) / M) / 2 := h2
        _ = _ := by ring
  · intro u _ i hi
    exact (hcut u (by change i + 1 < nchT γ M ε u at hi; omega)).regular i hi
  · intro v hv t ht
    rcases hchild v hv with rfl | ⟨u, _, i, hi, rfl⟩
    · change t ∈ Icc 0 1 at ht
      change ‖γ t - γ 0‖ ≤ 4 * ‖γ 1 - γ 0‖
      rw [hγ.source, hγ.target, sub_zero, sub_zero, norm_one, mul_one]
      have hU := hγ.mapsTo ht
      simp only [U, Set.mem_ofPred_eq] at hU
      have := Complex.norm_le_abs_re_add_abs_im (γ t)
      linarith [hU.1, hU.2]
    · exact (hcut u (by change i < nchT γ M ε u at hi; omega)).ball i hi t ht

end Tree

/-- **Node `T41`.** Every admissible path has a partition tree. -/
theorem pathTreeExists : PathTreeExists := by
  intro γ hγ M hM ε hε
  have hMr : (16 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε.1
    (show 3 / (2 * (M : ℝ)) < 1 by rw [div_lt_one (by positivity)]; linarith)
  exact ⟨treeOf γ M ε D, treeOf_WF hγ hM hε hD⟩

end LQGDimension.LFPPTree

