import Mathlib

/-!
# Crossing times of a path and their invariance under increasing time changes

For a path `f : ℝ≥0 → E` in a pseudo-metric space and `ε : ℝ`, the successive `ε`-crossing times
are defined by `σ₀ = 0` and
`σ_{k+1} = inf {s > σ_k : ε ≤ dist (f s) (f σ_k)}` (with `inf ∅ = ⊤`, and `σ_{k+1} = ⊤` if
`σ_k = ⊤`).  The crossing count `crossCount ε f u` is the number of crossings in `[0, u]`.

The crossing times do not depend on the parametrisation of the path: if `g = f ∘ τ` for a
continuous strictly increasing `τ` with `τ 0 = 0`, then `σ^g_k` is the preimage of `σ^f_k`
(`⊤` when `σ^f_k` lies beyond the range of `τ`), and `crossCount ε g u = crossCount ε f (τ u)`.
For paths in a normed group, the crossing count is also invariant under translation of the path.
-/

open scoped NNReal ENNReal

namespace LatticeProb

section Crossing

variable {E : Type*} [PseudoMetricSpace E]

/-- The first time strictly after `a` at which `f` is at distance at least `ε` from `f a`;
`⊤` if there is no such time (in particular if `a = ⊤`). -/
noncomputable def nextCrossTime (ε : ℝ) (f : ℝ≥0 → E) (a : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : a < s ∧ ε ≤ dist (f s) (f a.toNNReal)), (s : ℝ≥0∞)

/-- The `k`-th `ε`-crossing time of `f`. -/
noncomputable def crossTime (ε : ℝ) (f : ℝ≥0 → E) (k : ℕ) : ℝ≥0∞ :=
  (nextCrossTime ε f)^[k] 0

/-- The number of `ε`-crossings of `f` in `[0, u]`. -/
noncomputable def crossCount (ε : ℝ) (f : ℝ≥0 → E) (u : ℝ≥0) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : crossTime ε f k ≤ u), (k : ℕ∞)

theorem nextCrossTime_lt_iff {ε : ℝ} {f : ℝ≥0 → E} {a c : ℝ≥0∞} :
    nextCrossTime ε f a < c ↔
      ∃ s : ℝ≥0, a < s ∧ ε ≤ dist (f s) (f a.toNNReal) ∧ (s : ℝ≥0∞) < c := by
  simp only [nextCrossTime, iInf_lt_iff, exists_prop, and_assoc]

theorem le_nextCrossTime_iff {ε : ℝ} {f : ℝ≥0 → E} {a c : ℝ≥0∞} :
    c ≤ nextCrossTime ε f a ↔
      ∀ s : ℝ≥0, a < s → ε ≤ dist (f s) (f a.toNNReal) → c ≤ s := by
  simp only [nextCrossTime, le_iInf_iff, and_imp]

theorem nextCrossTime_le_of_lt {ε : ℝ} {f : ℝ≥0 → E} {a : ℝ≥0∞} {s : ℝ≥0} (h1 : a < s)
    (h2 : ε ≤ dist (f s) (f a.toNNReal)) : nextCrossTime ε f a ≤ s :=
  iInf₂_le s ⟨h1, h2⟩

theorem le_nextCrossTime (ε : ℝ) (f : ℝ≥0 → E) (a : ℝ≥0∞) : a ≤ nextCrossTime ε f a :=
  le_nextCrossTime_iff.2 fun _ hs _ => hs.le

theorem nextCrossTime_top (ε : ℝ) (f : ℝ≥0 → E) : nextCrossTime ε f ⊤ = ⊤ :=
  top_le_iff.1 (le_nextCrossTime ε f ⊤)

theorem nextCrossTime_coe_lt_iff {ε : ℝ} {f : ℝ≥0 → E} {u : ℝ≥0} {c : ℝ≥0∞} :
    nextCrossTime ε f u < c ↔ ∃ s : ℝ≥0, u < s ∧ ε ≤ dist (f s) (f u) ∧ (s : ℝ≥0∞) < c := by
  rw [nextCrossTime_lt_iff]
  simp [ENNReal.toNNReal_coe]

theorem le_nextCrossTime_coe_iff {ε : ℝ} {f : ℝ≥0 → E} {u : ℝ≥0} {c : ℝ≥0∞} :
    c ≤ nextCrossTime ε f u ↔ ∀ s : ℝ≥0, u < s → ε ≤ dist (f s) (f u) → c ≤ s := by
  rw [le_nextCrossTime_iff]
  simp [ENNReal.toNNReal_coe]

theorem crossTime_zero (ε : ℝ) (f : ℝ≥0 → E) : crossTime ε f 0 = 0 := rfl

theorem crossTime_succ (ε : ℝ) (f : ℝ≥0 → E) (k : ℕ) :
    crossTime ε f (k + 1) = nextCrossTime ε f (crossTime ε f k) :=
  Function.iterate_succ_apply' _ _ _

theorem crossTime_mono (ε : ℝ) (f : ℝ≥0 → E) : Monotone (crossTime ε f) :=
  monotone_nat_of_le_succ fun k => by
    rw [crossTime_succ]
    exact le_nextCrossTime ε f _

theorem crossCount_mono (ε : ℝ) (f : ℝ≥0 → E) : Monotone (crossCount ε f) := by
  intro u v huv
  refine iSup_mono fun k => iSup_mono' fun hk => ⟨hk.trans ?_, le_rfl⟩
  exact_mod_cast huv

/-- The relation between the crossing times of `f ∘ τ` (the first entry) and of `f`: the time
`a` of `f ∘ τ` corresponds to the time `τ a` of `f`, and `⊤` corresponds to anything beyond the
range of `τ`. -/
private def TimeChangeRel (τ : ℝ≥0 → ℝ≥0) (a b : ℝ≥0∞) : Prop :=
  (∃ u : ℝ≥0, a = u ∧ b = τ u) ∨ (a = ⊤ ∧ ∀ u : ℝ≥0, (τ u : ℝ≥0∞) ≤ b)

private theorem timeChangeRel_next {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) {ε : ℝ} {f : ℝ≥0 → E} {a b : ℝ≥0∞} (h : TimeChangeRel τ a b) :
    TimeChangeRel τ (nextCrossTime ε (f ∘ τ) a) (nextCrossTime ε f b) := by
  have hivt : ∀ t v : ℝ≥0, t ≤ τ v → ∃ s, s ≤ v ∧ τ s = t := by
    intro t v htv
    obtain ⟨s, hs, hst⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ v from zero_le) hτc.continuousOn
      ⟨by rw [hτ0]; exact zero_le, htv⟩
    exact ⟨s, hs.2, hst⟩
  rcases h with ⟨u, rfl, rfl⟩ | ⟨rfl, hb⟩
  · by_cases hS : ∃ s : ℝ≥0, u < s ∧ ε ≤ dist (f (τ s)) (f (τ u))
    · obtain ⟨s₀, hs₀1, hs₀2⟩ := hS
      have hlt : nextCrossTime ε (f ∘ τ) u < ⊤ :=
        nextCrossTime_coe_lt_iff.2 ⟨s₀, hs₀1, hs₀2, ENNReal.coe_lt_top⟩
      obtain ⟨w, hw⟩ : ∃ w : ℝ≥0, (w : ℝ≥0∞) = nextCrossTime ε (f ∘ τ) u :=
        ⟨_, ENNReal.coe_toNNReal hlt.ne⟩
      refine Or.inl ⟨w, hw.symm, ?_⟩
      refine le_antisymm ?_ ?_
      · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
        have hev : ∀ᶠ x in nhds w, τ x < τ w + δ :=
          (hτc.tendsto w).eventually_lt_const (lt_add_of_pos_right _ hδ)
        obtain ⟨w', hww', hw'⟩ := hev.exists_gt
        have hc : nextCrossTime ε (f ∘ τ) u < (w' : ℝ≥0∞) := by
          rw [← hw]; exact_mod_cast hww'
        obtain ⟨s, hus, hs, hsw'⟩ := nextCrossTime_coe_lt_iff.1 hc
        have hsw : s < w' := by exact_mod_cast hsw'
        have h1 : nextCrossTime ε f (τ u : ℝ≥0) ≤ (τ s : ℝ≥0) :=
          nextCrossTime_le_of_lt (by exact_mod_cast hτm hus) (by simpa using hs)
        refine h1.trans ?_
        have : τ s ≤ τ w + δ := ((hτm hsw).trans hw').le
        exact_mod_cast this
      · refine le_nextCrossTime_coe_iff.2 fun t hut hdist => ?_
        by_contra hcon
        have htw : t < τ w := by exact_mod_cast not_le.1 hcon
        obtain ⟨s, hsw, hst⟩ := hivt t w htw.le
        subst hst
        have hsw' : s < w := lt_of_le_of_ne hsw fun h => by simp [h] at htw
        have hus : u < s := hτm.lt_iff_lt.1 hut
        have hc : nextCrossTime ε (f ∘ τ) u < (w : ℝ≥0∞) :=
          nextCrossTime_coe_lt_iff.2 ⟨s, hus, hdist, by exact_mod_cast hsw'⟩
        rw [← hw] at hc
        exact lt_irrefl _ hc
    · have htop : nextCrossTime ε (f ∘ τ) u = ⊤ := by
        by_contra hne
        obtain ⟨s, hus, hs, -⟩ := nextCrossTime_coe_lt_iff.1
          (lt_top_iff_ne_top.2 hne)
        exact hS ⟨s, hus, hs⟩
      refine Or.inr ⟨htop, fun v => le_nextCrossTime_coe_iff.2 fun t hut hdist => ?_⟩
      by_contra hcon
      have htv : t < τ v := by exact_mod_cast not_le.1 hcon
      obtain ⟨s, -, hst⟩ := hivt t v htv.le
      subst hst
      exact hS ⟨s, hτm.lt_iff_lt.1 hut, hdist⟩
  · refine Or.inr ⟨by simp [nextCrossTime_top], fun u => (hb u).trans (le_nextCrossTime ε f b)⟩

private theorem timeChangeRel_crossTime {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ)
    (hτm : StrictMono τ) (hτ0 : τ 0 = 0) (ε : ℝ) (f : ℝ≥0 → E) (k : ℕ) :
    TimeChangeRel τ (crossTime ε (f ∘ τ) k) (crossTime ε f k) := by
  induction k with
  | zero => exact Or.inl ⟨0, by simp [crossTime_zero], by simp [crossTime_zero, hτ0]⟩
  | succ k ih =>
    rw [crossTime_succ, crossTime_succ]
    exact timeChangeRel_next hτc hτm hτ0 ih

/-- Under a continuous strictly increasing time change `τ` with `τ 0 = 0`, the `k`-th crossing time
of `f ∘ τ` is at most `u` iff the `k`-th crossing time of `f` is at most `τ u`. -/
theorem crossTime_comp_le_iff {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) (ε : ℝ) (f : ℝ≥0 → E) (k : ℕ) (u : ℝ≥0) :
    crossTime ε (f ∘ τ) k ≤ u ↔ crossTime ε f k ≤ τ u := by
  rcases timeChangeRel_crossTime hτc hτm hτ0 ε f k with ⟨v, hv1, hv2⟩ | ⟨hv1, hv2⟩
  · rw [hv1, hv2]
    simp [hτm.le_iff_le]
  · rw [hv1]
    refine iff_of_false (by simp) fun h => ?_
    have h1 := (hv2 (u + 1)).trans h
    have h2 : τ (u + 1) ≤ τ u := by exact_mod_cast h1
    exact absurd (hτm (lt_add_one u)) (not_lt.2 h2)

/-- The number of `ε`-crossings does not depend on the parametrisation of the path. -/
theorem crossCount_comp {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) (ε : ℝ) (f : ℝ≥0 → E) (u : ℝ≥0) :
    crossCount ε (f ∘ τ) u = crossCount ε f (τ u) := by
  unfold crossCount
  simp only [crossTime_comp_le_iff hτc hτm hτ0]

/-- The crossing times are unchanged under an isometric embedding of the target space. -/
theorem nextCrossTime_comp_isometry {F : Type*} [PseudoMetricSpace F] {φ : E → F}
    (hφ : Isometry φ) (ε : ℝ) (f : ℝ≥0 → E) :
    nextCrossTime ε (φ ∘ f) = nextCrossTime ε f := by
  funext a
  simp only [nextCrossTime, Function.comp_apply, hφ.dist_eq]

theorem crossTime_comp_isometry {F : Type*} [PseudoMetricSpace F] {φ : E → F}
    (hφ : Isometry φ) (ε : ℝ) (f : ℝ≥0 → E) : crossTime ε (φ ∘ f) = crossTime ε f := by
  funext k
  simp only [crossTime, nextCrossTime_comp_isometry hφ]

theorem crossCount_comp_isometry {F : Type*} [PseudoMetricSpace F] {φ : E → F}
    (hφ : Isometry φ) (ε : ℝ) (f : ℝ≥0 → E) : crossCount ε (φ ∘ f) = crossCount ε f := by
  funext u
  simp only [crossCount, crossTime_comp_isometry hφ]

/-- Adding a constant to a path does not change its crossing count. -/
theorem crossCount_add_const {G : Type*} [SeminormedAddCommGroup G] (ε : ℝ) (f : ℝ≥0 → G)
    (c : G) (u : ℝ≥0) : crossCount ε (fun s => f s + c) u = crossCount ε f u :=
  congrFun (crossCount_comp_isometry (φ := fun x : G => x + c)
    (IsometryEquiv.addRight c).isometry ε f) u

/-- A continuous path has only finitely many `ε`-crossings on a bounded interval (`ε > 0`). -/
theorem crossCount_lt_top {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) (u : ℝ≥0) :
    crossCount ε f u < ⊤ := by
  have huc : UniformContinuousOn f (Set.Icc 0 (u + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  obtain ⟨δ, hδpos, hδ1, hδf⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      ∀ x y : ℝ≥0, x ≤ u + 1 → y ≤ u + 1 → dist x y < δ → dist (f x) (f y) < ε := by
    refine ⟨min δ₀.toNNReal 1, lt_min (Real.toNNReal_pos.2 hδ₀) one_pos, min_le_right _ _,
      fun x y hx hy hxy => hδ x ⟨zero_le, hx⟩ y ⟨zero_le, hy⟩ ?_⟩
    calc dist x y < ((min δ₀.toNNReal 1 : ℝ≥0) : ℝ) := hxy
      _ ≤ δ₀ := (NNReal.coe_le_coe.2 (min_le_left _ _)).trans (Real.coe_toNNReal _ hδ₀.le).le
  have hgap : ∀ k : ℕ, crossTime ε f k ≤ u → (k : ℝ≥0∞) * δ ≤ crossTime ε f k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : crossTime ε f k ≤ u := (crossTime_mono ε f (Nat.le_succ k)).trans hk
      have ih' := ih hk'
      obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (a : ℝ≥0∞) = crossTime ε f k :=
        ⟨_, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hk')⟩
      rw [crossTime_succ, ← ha]
      rw [← ha] at hk' ih'
      have hau : a ≤ u := by exact_mod_cast hk'
      have hnext : ((a + δ : ℝ≥0) : ℝ≥0∞) ≤ nextCrossTime ε f a := by
        refine le_nextCrossTime_coe_iff.2 fun s has hdist => ?_
        by_contra hlt
        have hs : s < a + δ := by exact_mod_cast not_le.1 hlt
        have hs' : (s : ℝ) < a + δ := by exact_mod_cast hs
        have hlt' : dist (f s) (f a) < ε :=
          hδf s a (hs.le.trans (add_le_add hau hδ1)) (hau.trans le_self_add) (by
            rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 has))]
            linarith)
        linarith
      calc (((k + 1 : ℕ) : ℝ≥0∞) * δ) = (k : ℝ≥0∞) * δ + δ := by push_cast; ring
        _ ≤ a + δ := by gcongr
        _ ≤ _ := by exact_mod_cast hnext
  obtain ⟨N, hN⟩ := Archimedean.arch u hδpos
  have hbound : crossCount ε f u ≤ (N : ℕ∞) := by
    refine iSup₂_le fun k hk => ?_
    have h1 : (k : ℝ≥0∞) * δ ≤ u := (hgap k hk).trans hk
    have h2 : (k : ℝ≥0) * δ ≤ u := by exact_mod_cast h1
    have h3 : (k : ℝ≥0) * δ ≤ N * δ := by
      refine h2.trans (hN.trans ?_)
      simp
    have h4 : (k : ℝ≥0) ≤ N := le_of_mul_le_mul_right h3 hδpos
    exact_mod_cast h4
  exact lt_of_le_of_lt hbound (ENat.natCast_lt_top N)

/-- For a continuous path and `ε > 0`, the first crossing time after `a` is attained whenever it
is finite. -/
theorem exists_nextCrossTime_eq {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    {a : ℝ≥0} (h : nextCrossTime ε f a < ⊤) :
    ∃ s : ℝ≥0, a < s ∧ ε ≤ dist (f s) (f a) ∧ nextCrossTime ε f a = s := by
  obtain ⟨s₀, hs₀a, hs₀, -⟩ := nextCrossTime_coe_lt_iff.1 h
  have hSeq : {s : ℝ≥0 | a < s ∧ ε ≤ dist (f s) (f a)} =
      Set.Ici a ∩ {s | ε ≤ dist (f s) (f a)} := by
    ext s
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.le, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_ne h1 fun hsa => ?_, h2⟩
      have h3 : ε ≤ dist (f s) (f a) := h2
      rw [← hsa, dist_self] at h3
      linarith
  have hclosed : IsClosed {s : ℝ≥0 | a < s ∧ ε ≤ dist (f s) (f a)} := by
    rw [hSeq]
    exact isClosed_Ici.inter (isClosed_le continuous_const (hf.dist continuous_const))
  have hne : ({s : ℝ≥0 | a < s ∧ ε ≤ dist (f s) (f a)}).Nonempty := ⟨s₀, hs₀a, hs₀⟩
  have hbdd : BddBelow {s : ℝ≥0 | a < s ∧ ε ≤ dist (f s) (f a)} := ⟨a, fun s hs => hs.1.le⟩
  have hmem := hclosed.csInf_mem hne hbdd
  refine ⟨_, hmem.1, hmem.2, le_antisymm
    (nextCrossTime_le_of_lt (by exact_mod_cast hmem.1) (by simpa using hmem.2)) ?_⟩
  refine le_nextCrossTime_coe_iff.2 fun s has hs => ?_
  exact_mod_cast csInf_le hbdd ⟨has, hs⟩

/-- For a continuous path, the first crossing after `a` happens by time `u` iff `f` is at distance
at least `ε` from `f a` at some time in `(a, u]`. -/
theorem nextCrossTime_le_iff_exists {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    (a u : ℝ≥0) :
    nextCrossTime ε f a ≤ u ↔ ∃ s : ℝ≥0, a < s ∧ s ≤ u ∧ ε ≤ dist (f s) (f a) := by
  constructor
  · intro h
    obtain ⟨s, has, hs, hEq⟩ :=
      exists_nextCrossTime_eq hf hε (lt_of_le_of_lt h ENNReal.coe_lt_top)
    refine ⟨s, has, ?_, hs⟩
    rw [hEq] at h
    exact_mod_cast h
  · rintro ⟨s, has, hsu, hs⟩
    exact (nextCrossTime_le_of_lt (by exact_mod_cast has) (by simpa using hs)).trans
      (by exact_mod_cast hsu)

theorem nextCrossTime_le_iff_of_eqOn {f g : ℝ≥0 → E} (hf : Continuous f) (hg : Continuous g)
    {ε : ℝ} (hε : 0 < ε) {a u : ℝ≥0} (hau : a ≤ u) (hfg : ∀ s ≤ u, f s = g s) :
    nextCrossTime ε f a ≤ u ↔ nextCrossTime ε g a ≤ u := by
  rw [nextCrossTime_le_iff_exists hf hε, nextCrossTime_le_iff_exists hg hε]
  refine exists_congr fun s => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [← hfg s h2, ← hfg a hau]⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [hfg s h2, hfg a hau]⟩

theorem nextCrossTime_eq_of_eqOn {f g : ℝ≥0 → E} (hf : Continuous f) (hg : Continuous g)
    {ε : ℝ} (hε : 0 < ε) {a u : ℝ≥0} (hau : a ≤ u) (hfg : ∀ s ≤ u, f s = g s)
    (h : nextCrossTime ε f a ≤ u) : nextCrossTime ε f a = nextCrossTime ε g a := by
  have hg' : nextCrossTime ε g a ≤ u := (nextCrossTime_le_iff_of_eqOn hf hg hε hau hfg).1 h
  obtain ⟨s, has, hs, hEq⟩ := exists_nextCrossTime_eq hf hε (lt_of_le_of_lt h ENNReal.coe_lt_top)
  obtain ⟨s', has', hs', hEq'⟩ :=
    exists_nextCrossTime_eq hg hε (lt_of_le_of_lt hg' ENNReal.coe_lt_top)
  have hsu : s ≤ u := by
    rw [hEq] at h
    exact_mod_cast h
  have hsu' : s' ≤ u := by
    rw [hEq'] at hg'
    exact_mod_cast hg'
  refine le_antisymm ?_ ?_
  · rw [hEq']
    refine nextCrossTime_le_of_lt (by exact_mod_cast has') ?_
    simpa [hfg s' hsu', hfg a hau] using hs'
  · rw [hEq]
    refine nextCrossTime_le_of_lt (by exact_mod_cast has) ?_
    simpa [← hfg s hsu, ← hfg a hau] using hs

private theorem crossTime_eq_of_eqOn_aux {f g : ℝ≥0 → E} (hf : Continuous f)
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) {u : ℝ≥0} (hfg : ∀ s ≤ u, f s = g s) (k : ℕ)
    (h : crossTime ε f k ≤ u) : crossTime ε f k = crossTime ε g k := by
  induction k with
  | zero => simp [crossTime_zero]
  | succ k ih =>
    have hk : crossTime ε f k ≤ u := (crossTime_mono ε f (Nat.le_succ k)).trans h
    have ihk := ih hk
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (a : ℝ≥0∞) = crossTime ε f k :=
      ⟨_, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hk)⟩
    rw [crossTime_succ, crossTime_succ, ← ihk, ← ha]
    rw [crossTime_succ, ← ha] at h
    rw [← ha] at hk
    exact nextCrossTime_eq_of_eqOn hf hg hε (by exact_mod_cast hk) hfg h

/-- Two continuous paths that agree on `[0, u]` have the same crossing times in `[0, u]`. -/
theorem crossTime_le_iff_of_eqOn {f g : ℝ≥0 → E} (hf : Continuous f) (hg : Continuous g)
    {ε : ℝ} (hε : 0 < ε) {u : ℝ≥0} (hfg : ∀ s ≤ u, f s = g s) (k : ℕ) :
    crossTime ε f k ≤ u ↔ crossTime ε g k ≤ u := by
  constructor
  · intro h
    rw [← crossTime_eq_of_eqOn_aux hf hg hε hfg k h]
    exact h
  · intro h
    rw [← crossTime_eq_of_eqOn_aux hg hf hε (fun s hs => (hfg s hs).symm) k h]
    exact h

theorem crossTime_eq_of_eqOn {f g : ℝ≥0 → E} (hf : Continuous f) (hg : Continuous g)
    {ε : ℝ} (hε : 0 < ε) {u : ℝ≥0} (hfg : ∀ s ≤ u, f s = g s) (k : ℕ)
    (h : crossTime ε f k ≤ u) : crossTime ε f k = crossTime ε g k :=
  crossTime_eq_of_eqOn_aux hf hg hε hfg k h

/-- The number of `ε`-crossings in `[0, u]` of a continuous path depends only on the path on
`[0, u]`. -/
theorem crossCount_congr {f g : ℝ≥0 → E} (hf : Continuous f) (hg : Continuous g) {ε : ℝ}
    (hε : 0 < ε) {u : ℝ≥0} (hfg : ∀ s ≤ u, f s = g s) :
    crossCount ε f u = crossCount ε g u := by
  unfold crossCount
  refine iSup_congr fun k => ?_
  by_cases h : crossTime ε f k ≤ u
  · rw [iSup_pos h, iSup_pos ((crossTime_le_iff_of_eqOn hf hg hε hfg k).1 h)]
  · have h' : ¬ crossTime ε g k ≤ u := fun h'' => h ((crossTime_le_iff_of_eqOn hf hg hε hfg k).2 h'')
    rw [iSup_neg h, iSup_neg h']

/-- The crossing times in `[0, u]` of a continuous path are those of the path stopped at `u`. -/
theorem crossTime_le_iff_stopped {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    (u : ℝ≥0) (k : ℕ) :
    crossTime ε f k ≤ u ↔ crossTime ε (fun s => f (min s u)) k ≤ u :=
  crossTime_le_iff_of_eqOn hf (hf.comp (continuous_id.min continuous_const)) hε
    (fun s hs => by simp [min_eq_left hs]) k

theorem crossCount_stopped {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) (u : ℝ≥0) :
    crossCount ε (fun s => f (min s u)) u = crossCount ε f u :=
  (crossCount_congr hf (hf.comp (continuous_id.min continuous_const)) hε
    (fun s hs => by simp [min_eq_left hs])).symm

end Crossing

end LatticeProb
