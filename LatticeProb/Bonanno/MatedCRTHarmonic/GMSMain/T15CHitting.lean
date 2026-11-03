/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15CHitting at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Bound
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Walk

/-!
# [18] Theorem 3.9, boundary estimate: the hitting estimate (3.38)

Source: [18] , proof of Theorem 3.9, `[18]`, equation (3.38): for
`t > 2 dist(η(x), ∂D)`, the walk from `x` first hits `VG^ε(∂D)` inside `VG^ε(∂D ∩ B_t(η(x)))` with probability
`≥ 1 − A (t / dist(η(x), ∂D))^{−ξ}`, "by applying the Markov property of `X^ε` and (3.35) with `r = e^{−k}`".

Deterministic layer, for a cellular embedding `H` of `G` with (LC) (`H.PointConnected`):

* `t15cDisconnectionAt G H p z r`: [18] (3.35) at one centre `z` and one radius `r` — from every vertex of
  `V(B_r(z))`, with probability `≥ p` the vertices visited before the first visit to `V(∂B_{2r}(z))` graph-disconnect
  `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` (frozen `LFMultigraph.Disconnects`, `walkTrace`).
* `t15cExitBefore G H D z b`: the walk visits a cell not contained in `D` strictly before its first visit to
  `V(∂B_b(z))`; `t15c_disconnects_subset_exitBefore`: by the key geometric step (`T15CGeometry`), the event of (3.35)
  is contained in it as soon as `ℂ \ D` is preconnected, unbounded and comes within `r/2` of `z`.
* `t15c_hitDist_compl_le` (**the iteration, generic radii**): scales `j < K` with outer radii `b j ≤ t`; if from every
  vertex of a start set `S j` (with `x ∈ S 0` and `V(∂B_{b j}(z)) ⊆ S (j+1)`) the exit event at scale `j` has
  probability `≥ p`, then `P_x[X_{T_{V(∂D)}} ∉ V(D) ∩ V(∂D ∩ B_t(z))] ≤ (1 − p)^K` (`hitDist` of the complement).
  Proof: the strong Markov property at the successive hitting times `σ_{j+1}` of `V(∂B_{b j}(z))` (using the scale-success iteration in `GoodScales/Bound.lean`): `P(reach_{n+1}) ≤ (1 − p) P(reach_n)`; a success at scale `j` forces the first hit
  of `V(∂D)` before `σ_{j+1}`, hence inside `B_{b j}(z) ⊆ B_t(z)` (chain and confinement steps).
* `t15c_hitDist_compl_le_of_disconnectionAt` (**(3.38), [18]'s scales**): the same with `r_j = 4^j r₀`, `S j =
  V(B_{r_j}(z))`, `b j = 2 r_j`, from `t15cDisconnectionAt` at the radii `r_j` (ratio `4` instead of [18]'s `e`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain

open Markov LFMultigraph GoodScales HarmonicInfinity

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-! ### Definitions -/

section Defs

variable (G) (H : CellularEmbedding G o)

/-- **[18] (3.35) at one centre and one radius**: from every vertex of `V(B_r(z))`, with probability
at least `p`, the walk disconnects `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` (graph disconnection, frozen
`LFMultigraph.Disconnects`) before hitting `V(∂B_{2r}(z))` (the trace `walkTrace` of the visits strictly before the
first visit). -/
def t15cDisconnectionAt (p : ℝ) (z : ℂ) (r : ℝ) : Prop :=
  ∀ y ∈ verticesMeeting H.cell (ball z r), ENNReal.ofReal p ≤ G.walkLaw y
    {ω | G.Disconnects (walkTrace G (verticesMeeting H.cell (sphere z (2 * r))) ω)
      (verticesMeeting H.cell (sphere z (r / 2))) (verticesMeeting H.cell (sphere z (2 * r)))}

/-- The walk visits a cell not contained in `D` strictly before its first visit to `V(∂B_b(z))`. -/
def t15cExitBefore (D : Set ℂ) (z : ℂ) (b : ℝ) : Set (ℕ → G.State) :=
  {ω | ∃ m : ℕ, (m : ℕ∞) < hitTime (verticesMeeting H.cell (sphere z b)) (G.vertexPath ω) ∧
    ¬ H.cell (G.vertexPath ω m) ⊆ D}

/-- The scale times: `σ 0 = 0` and `σ (j+1)` is the first visit to `V(∂B_{b j}(z))` at or after `σ j`. -/
def t15cSig (z : ℂ) (b : ℕ → ℝ) : ℕ → (ℕ → G.State) → ℕ∞
  | 0 => fun _ => ((0 : ℕ) : ℕ∞)
  | j + 1 => thenTime (t15cSig z b j) (hitTime (vset G (verticesMeeting H.cell (sphere z (b j)))))

/-- Success at scale `j`: the path restarted at `σ j` exits `D` before reaching `V(∂B_{b j}(z))`. -/
def t15cSucc (D : Set ℂ) (z : ℂ) (b : ℕ → ℝ) (j : ℕ) : Set (ℕ → G.State) :=
  {ω | t15cSig G H z b j ω < ⊤} ∩ stopShift (t15cSig G H z b j) ⁻¹' t15cExitBefore G H D z (b j)

/-- Scale `n` is reached from `x` after failing at the scales `< n`. -/
def t15cReach (x : V) (D : Set ℂ) (z : ℂ) (b : ℕ → ℝ) (n : ℕ) : Set (ℕ → G.State) :=
  {ω | t15cSig G H z b n ω < ⊤ ∧ G.stateVertex (ω 0) = x ∧ ∀ i < n, ω ∉ t15cSucc G H D z b i}

end Defs

/-! ### The event of (3.35) forces an exit from `D` -/

section Geometry

variable {H : CellularEmbedding G o}

/-- A bounded set has, in its complement, points at any prescribed distance from `z` or more. -/
theorem t15c_exists_far_notMem {D : Set ℂ} (hDb : Bornology.IsBounded D) (z : ℂ) (R : ℝ) :
    ∃ w ∉ D, R ≤ dist w z := by
  obtain ⟨C, hC⟩ := hDb.subset_closedBall z
  set s : ℝ := max (max R C) 0 + 1 with hs
  have hs0 : 0 < s := by have := le_max_right (max R C) 0; linarith
  have hds : dist (z + (s : ℂ)) z = s := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  refine ⟨z + (s : ℂ), fun hw => ?_, ?_⟩
  · have h1 := mem_closedBall.mp (hC hw)
    rw [hds] at h1
    have := le_max_right R C
    have := le_max_left (max R C) 0
    linarith
  · rw [hds]
    have := le_max_left R C
    have := le_max_left (max R C) 0
    linarith

/-- **The event of (3.35) forces an exit from `D` before `V(∂B_{2r}(z))`**, when `ℂ \ D` is
preconnected, `D` is bounded and `ℂ \ D` has a point within `r/2` of `z`. -/
theorem t15c_disconnects_subset_exitBefore (hLC : H.PointConnected) {D : Set ℂ} (hDc : IsPreconnected Dᶜ)
    (hDb : Bornology.IsBounded D) {z : ℂ} {r : ℝ} (hr : 0 < r) {w₀ : ℂ} (hw₀ : w₀ ∉ D)
    (hw₀r : dist w₀ z ≤ r / 2) :
    {ω | G.Disconnects (walkTrace G (verticesMeeting H.cell (sphere z (2 * r))) ω)
      (verticesMeeting H.cell (sphere z (r / 2))) (verticesMeeting H.cell (sphere z (2 * r)))} ⊆
      t15cExitBefore G H D z (2 * r) := by
  intro ω hω
  obtain ⟨w₁, hw₁, hw₁r⟩ := t15c_exists_far_notMem hDb z (2 * r)
  obtain ⟨y, ⟨m, hm, hmy⟩, hy⟩ := t15c_exists_mem_not_subset_of_disconnects hLC hDc
    (by linarith : r / 2 ≤ 2 * r) hw₀ hw₀r hw₁ hw₁r hω
  exact ⟨m, hm, by rw [hmy]; exact hy⟩

/-- **(3.35) gives the exit bound at one scale.** -/
theorem t15c_le_walkLaw_exitBefore {p : ℝ} (hLC : H.PointConnected) {D : Set ℂ}
    (hDc : IsPreconnected Dᶜ) (hDb : Bornology.IsBounded D) {z : ℂ} {r : ℝ} (hr : 0 < r) {w₀ : ℂ}
    (hw₀ : w₀ ∉ D) (hw₀r : dist w₀ z ≤ r / 2) (h35 : t15cDisconnectionAt G H p z r) :
    ∀ y ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw y (t15cExitBefore G H D z (2 * r)) := fun y hy =>
  (h35 y hy).trans (measure_mono (t15c_disconnects_subset_exitBefore hLC hDc hDb hr hw₀ hw₀r))

end Geometry

/-! ### Stopping times and measurability -/

section Measurability

variable {H : CellularEmbedding G o} {D : Set ℂ} {z : ℂ} {b : ℕ → ℝ}

theorem t15c_isStoppingTime_sig :
    ∀ j, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => G.State)) (t15cSig G H z b j)
  | 0 => isStoppingTime_const _ (0 : ℕ)
  | j + 1 => isStoppingTime_thenTime (t15c_isStoppingTime_sig j) (isStoppingTime_hitTime_vset _)

theorem t15c_sig_le_succ (j : ℕ) (ω : ℕ → G.State) : t15cSig G H z b j ω ≤ t15cSig G H z b (j + 1) ω :=
  le_thenTime ω

theorem t15c_sig_mono : Monotone fun j => t15cSig G H z b j := by
  refine monotone_nat_of_le_succ fun j => ?_
  intro ω
  exact t15c_sig_le_succ j ω

theorem t15c_sig_zero (ω : ℕ → G.State) : t15cSig G H z b 0 ω = 0 := rfl

theorem t15c_stopShift_sig_zero (ω : ℕ → G.State) : stopShift (t15cSig G H z b 0) ω = ω := by
  funext m
  show walkShift (((0 : ℕ) : ℕ∞)).toNat ω m = ω m
  rw [walkShift_apply]
  simp

theorem t15c_measurableSet_exitBefore [Countable G.State] (D : Set ℂ) (z : ℂ) (c : ℝ) :
    MeasurableSet (t15cExitBefore G H D z c) := by
  have hset : t15cExitBefore G H D z c = ⋃ m : ℕ,
      ({ω | (m : ℕ∞) < hitTime (vset G (verticesMeeting H.cell (sphere z c))) ω} ∩
        (fun ω : ℕ → G.State => ω m) ⁻¹' {s | ¬ H.cell (G.stateVertex s) ⊆ D}) := by
    ext ω
    simp only [t15cExitBefore, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    rfl
  rw [hset]
  refine MeasurableSet.iUnion fun m => MeasurableSet.inter ?_ ?_
  · exact measurable_hitTime (MeasurableSet.of_discrete) (MeasurableSet.of_discrete :
      MeasurableSet {x : ℕ∞ | (m : ℕ∞) < x})
  · exact measurable_pi_apply m MeasurableSet.of_discrete

/-- The exit event is an event of the hitting time of `V(∂B_c(z))`. -/
theorem t15c_measurableSet_exitBefore_stopping [Countable G.State] (D : Set ℂ) (z : ℂ) (c : ℝ) :
    MeasurableSet[(isStoppingTime_hitTime_vset (G := G)
      (verticesMeeting H.cell (sphere z c))).measurableSpace] (t15cExitBefore G H D z c) := by
  refine measurableSet_stopping_of_forall_eq _ (t15c_measurableSet_exitBefore D z c) ?_
  rintro ω ω' hlt hagree ⟨m, hm, hmD⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  have hn' : hitTime (vset G (verticesMeeting H.cell (sphere z c))) ω' = n :=
    hitTime_eq_of_forall_eq hn.symm fun k hk => hagree k (by rw [← hn]; exact_mod_cast hk)
  have hmn : m < n := by
    have : (m : ℕ∞) < n := by rw [hn]; exact hm
    exact_mod_cast this
  refine ⟨m, ?_, ?_⟩
  · show (m : ℕ∞) < hitTime (vset G (verticesMeeting H.cell (sphere z c))) ω'
    rw [hn']
    exact_mod_cast hmn
  · show ¬ H.cell (G.stateVertex (ω' m)) ⊆ D
    rw [← hagree m (by rw [← hn]; exact_mod_cast hmn.le)]
    exact hmD

/-- A success at scale `i` is an event of `ℱ_{σ (i+1)}`. -/
theorem t15c_measurableSet_succ_succ [Countable G.State] (i : ℕ) :
    MeasurableSet[(t15c_isStoppingTime_sig (G := G) (H := H) (z := z) (b := b) (i + 1)).measurableSpace]
      (t15cSucc G H D z b i) :=
  measurableSet_thenTime_of_stopShift (t15c_isStoppingTime_sig i) (isStoppingTime_hitTime_vset _)
    (t15c_measurableSet_exitBefore_stopping D z (b i))

/-- A success at scale `i < n` is an event of `ℱ_{σ n}`. -/
theorem t15c_measurableSet_succ_sig [Countable G.State] {i n : ℕ} (hin : i < n) :
    MeasurableSet[(t15c_isStoppingTime_sig (G := G) (H := H) (z := z) (b := b) n).measurableSpace]
      (t15cSucc G H D z b i) :=
  IsStoppingTime.measurableSpace_mono (t15c_isStoppingTime_sig (i + 1)) (t15c_isStoppingTime_sig n)
    (t15c_sig_mono (Nat.succ_le_of_lt hin)) _ (t15c_measurableSet_succ_succ i)

theorem t15c_measurableSet_succ [Countable G.State] (i : ℕ) : MeasurableSet (t15cSucc G H D z b i) :=
  measurableSet_of_measurableSet_stopping (t15c_isStoppingTime_sig (i + 1)) (t15c_measurableSet_succ_succ i)

/-- The start vertex is an event of `ℱ_{σ n}`. -/
theorem t15c_measurableSet_start_sig [Countable G.State] (x : V) (n : ℕ) :
    MeasurableSet[(t15c_isStoppingTime_sig (G := G) (H := H) (z := z) (b := b) n).measurableSpace]
      {ω : ℕ → G.State | G.stateVertex (ω 0) = x} := by
  have hm : MeasurableSet ((fun ω : ℕ → G.State => ω 0) ⁻¹' {s : G.State | G.stateVertex s = x}) :=
    measurable_pi_apply 0 MeasurableSet.of_discrete
  refine measurableSet_stopping_of_forall_eq _ hm ?_
  intro ω ω' _ hagree hω
  show G.stateVertex (ω' 0) = x
  rw [← hagree 0 (by simp)]
  exact hω

/-- `reach n` is an event of `ℱ_{σ n}`. -/
theorem t15c_measurableSet_reach_sig [Countable G.State] (x : V) (n : ℕ) :
    MeasurableSet[(t15c_isStoppingTime_sig (G := G) (H := H) (z := z) (b := b) n).measurableSpace]
      (t15cReach G H x D z b n) := by
  have hset : t15cReach G H x D z b n = ({ω | t15cSig G H z b n ω < ⊤} ∩
      {ω : ℕ → G.State | G.stateVertex (ω 0) = x}) ∩
        ⋂ i, ⋂ (_ : i < n), (t15cSucc G H D z b i)ᶜ := by
    ext ω
    simp only [t15cReach, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    tauto
  rw [hset]
  exact ((measurableSet_lt_top_stopping (t15c_isStoppingTime_sig n)).inter
    (t15c_measurableSet_start_sig x n)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => (t15c_measurableSet_succ_sig hi).compl)

theorem t15c_measurableSet_reach [Countable G.State] (x : V) (n : ℕ) :
    MeasurableSet (t15cReach G H x D z b n) :=
  measurableSet_of_measurableSet_stopping (t15c_isStoppingTime_sig n) (t15c_measurableSet_reach_sig x n)

end Measurability

/-! ### The strong Markov recursion -/

section Recursion

variable {H : CellularEmbedding G o} {D : Set ℂ} {z : ℂ} {b : ℕ → ℝ}

/-- At a finite scale time `σ (j+1)` the walk is at a vertex of `V(∂B_{b j}(z))`. -/
theorem t15c_stopState_sig_succ_mem {j : ℕ} {ω : ℕ → G.State} (h : t15cSig G H z b (j + 1) ω < ⊤) :
    G.stateVertex (stopState (t15cSig G H z b (j + 1)) ω) ∈ verticesMeeting H.cell (sphere z (b j)) := by
  have h' := h
  change thenTime (t15cSig G H z b j) (hitTime (vset G (verticesMeeting H.cell (sphere z (b j))))) ω < ⊤
    at h'
  change G.stateVertex (stopState (thenTime (t15cSig G H z b j)
    (hitTime (vset G (verticesMeeting H.cell (sphere z (b j)))))) ω) ∈ _
  rw [stopState_thenTime h'.ne]
  exact stopState_hitTime_mem (thenTime_lt_top_iff.mp h').2.ne

/-- **Strong Markov step**: `p · P_x(reach n) ≤ P_x(reach n ∩ succ n)`, if the exit bound at scale `n` holds from
every vertex of `S n`, with `x ∈ S 0` and `V(∂B_{b j}(z)) ⊆ S (j + 1)`. -/
theorem t15c_ofReal_mul_reach_le [Countable G.State] {p : ℝ} {S : ℕ → Set V} {x : V} (hx : x ∈ S 0)
    (hS : ∀ j, verticesMeeting H.cell (sphere z (b j)) ⊆ S (j + 1)) {n : ℕ}
    (hsucc : ∀ y ∈ S n, ENNReal.ofReal p ≤ G.walkLaw y (t15cExitBefore G H D z (b n))) :
    ENNReal.ofReal p * G.walkLaw x (t15cReach G H x D z b n) ≤
      G.walkLaw x (t15cReach G H x D z b n ∩ t15cSucc G H D z b n) := by
  have h := le_chainLaw_inter_stopShift_preimage G.walkKernel (Sum.inl x)
    (t15c_isStoppingTime_sig (G := G) (H := H) (z := z) (b := b) n)
    (t15c_measurableSet_reach_sig (D := D) x n) (t15c_measurableSet_exitBefore (H := H) D z (b n))
    (p := ENNReal.ofReal p) ?_
  · have hset1 : t15cReach G H x D z b n ∩ {ω | t15cSig G H z b n ω < ⊤} = t15cReach G H x D z b n :=
      Set.inter_eq_left.mpr fun _ h => h.1
    have hset2 : t15cReach G H x D z b n ∩ {ω | t15cSig G H z b n ω < ⊤} ∩
        stopShift (t15cSig G H z b n) ⁻¹' t15cExitBefore G H D z (b n) =
        t15cReach G H x D z b n ∩ t15cSucc G H D z b n := by
      ext ω
      simp only [t15cSucc, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [hset2, hset1] at h
    exact h
  · rintro ω ⟨⟨hlt, h0, -⟩, -⟩
    have hmem : G.stateVertex (stopState (t15cSig G H z b n) ω) ∈ S n := by
      cases n with
      | zero =>
        have : stopState (t15cSig G H z b 0) ω = ω 0 := by
          show ω (((0 : ℕ) : ℕ∞)).toNat = ω 0
          simp
        rw [this, h0]
        exact hx
      | succ j => exact hS j (t15c_stopState_sig_succ_mem hlt)
    calc ENNReal.ofReal p
        ≤ G.walkLaw (G.stateVertex (stopState (t15cSig G H z b n) ω)) (t15cExitBefore G H D z (b n)) :=
          hsucc _ hmem
      _ = chainLaw G.walkKernel (stopState (t15cSig G H z b n) ω) (t15cExitBefore G H D z (b n)) :=
          chainLaw_vertexEvent_eq G (s := Sum.inl (G.stateVertex (stopState (t15cSig G H z b n) ω)))
            (s' := stopState (t15cSig G H z b n) ω) rfl
            (Q := fun X => ∃ m : ℕ, (m : ℕ∞) < hitTime (verticesMeeting H.cell (sphere z (b n))) X ∧
              ¬ H.cell (X m) ⊆ D)
            (t15c_measurableSet_exitBefore (H := H) D z (b n))

/-- **The recursion**: `P_x(reach n) ≤ (1 − p)^n`. -/
theorem t15c_walkLaw_reach_le [Countable G.State] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {S : ℕ → Set V}
    {x : V} (hx : x ∈ S 0) (hS : ∀ j, verticesMeeting H.cell (sphere z (b j)) ⊆ S (j + 1)) {K : ℕ}
    (hsucc : ∀ j < K, ∀ y ∈ S j, ENNReal.ofReal p ≤ G.walkLaw y (t15cExitBefore G H D z (b j))) :
    ∀ n ≤ K, G.walkLaw x (t15cReach G H x D z b n) ≤ ENNReal.ofReal ((1 - p) ^ n) := by
  set P := G.walkLaw x with hP
  have hq : ENNReal.ofReal (1 - p) = 1 - ENNReal.ofReal p := by
    rw [ENNReal.ofReal_sub 1 hp0, ENNReal.ofReal_one]
  intro n
  induction n with
  | zero =>
    intro _
    rw [pow_zero, ENNReal.ofReal_one]
    exact prob_le_one
  | succ n ih =>
    intro hn
    have hsub : t15cReach G H x D z b (n + 1) ⊆ t15cReach G H x D z b n \ t15cSucc G H D z b n := by
      rintro ω ⟨hlt, h0, hfail⟩
      exact ⟨⟨lt_of_le_of_lt (t15c_sig_le_succ n ω) hlt, h0, fun i hi => hfail i (by omega)⟩,
        hfail n (by omega)⟩
    have hstep := t15c_ofReal_mul_reach_le (D := D) hx hS (n := n) (hsucc n (by omega))
    have hdiff : P (t15cReach G H x D z b n \ t15cSucc G H D z b n) =
        P (t15cReach G H x D z b n) - P (t15cReach G H x D z b n ∩ t15cSucc G H D z b n) := by
      have heq : t15cReach G H x D z b n \ t15cSucc G H D z b n =
          t15cReach G H x D z b n \ (t15cReach G H x D z b n ∩ t15cSucc G H D z b n) := by
        ext ω
        simp only [Set.mem_sdiff, Set.mem_inter_iff]
        tauto
      rw [heq, measure_sdiff Set.inter_subset_left
        ((t15c_measurableSet_reach x n).inter (t15c_measurableSet_succ n)).nullMeasurableSet
        (measure_ne_top P _)]
    calc P (t15cReach G H x D z b (n + 1))
        ≤ P (t15cReach G H x D z b n \ t15cSucc G H D z b n) := measure_mono hsub
      _ = P (t15cReach G H x D z b n) - P (t15cReach G H x D z b n ∩ t15cSucc G H D z b n) := hdiff
      _ ≤ P (t15cReach G H x D z b n) - ENNReal.ofReal p * P (t15cReach G H x D z b n) :=
          tsub_le_tsub_left hstep _
      _ = ENNReal.ofReal (1 - p) * P (t15cReach G H x D z b n) := by
          rw [hq, ENNReal.sub_mul (fun _ _ => measure_ne_top P _), one_mul]
      _ ≤ ENNReal.ofReal (1 - p) * ENNReal.ofReal ((1 - p) ^ n) :=
          mul_le_mul_right (ih (by omega)) _
      _ = ENNReal.ofReal ((1 - p) ^ (n + 1)) := by
          rw [← ENNReal.ofReal_mul (by linarith), pow_succ', mul_comm]

end Recursion

/-! ### Paths: scale times, first hits, and the bad event -/

section Paths

variable {H : CellularEmbedding G o} {D : Set ℂ} {z : ℂ} {b : ℕ → ℝ}

/-- Along a path with admissible steps from a cell containing `z`, the hitting times of `V(∂B_c(z))` increase with
`c > 0`. -/
theorem t15c_hitTime_sphere_mono {X : ℕ → V} (hX : ∀ n, StepOK G (X n) (X (n + 1))) (hz : z ∈ H.cell (X 0))
    {c c' : ℝ} (hc : 0 < c) (hcc' : c ≤ c') :
    hitTime (verticesMeeting H.cell (sphere z c)) X ≤ hitTime (verticesMeeting H.cell (sphere z c')) X := by
  rcases eq_or_ne (hitTime (verticesMeeting H.cell (sphere z c')) X) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    have hmem := (hitTime_eq_coe_iff.mp hn.symm).1
    obtain ⟨k, hkn, hk⟩ := t15c_exists_sphere_of_meet H hX hz hc hcc' hmem
    rw [← hn]
    exact (hitTime_le_of_mem (show X k ∈ verticesMeeting H.cell (sphere z c) from hk)).trans
      (by exact_mod_cast hkn)

/-- On a path from `x` with admissible steps and `z ∈ H_x`, with positive increasing radii, `σ (j+1)` is the hitting
time of `V(∂B_{b j}(z))`. -/
theorem t15c_sig_succ_eq_hitTime {x : V} {ω : ℕ → G.State} (h0 : G.vertexPath ω 0 = x)
    (hstep : ∀ n, StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))) (hz : z ∈ H.cell x) {K : ℕ}
    (hb0 : ∀ j < K, 0 < b j) (hbm : ∀ j, j + 1 < K → b j ≤ b (j + 1)) :
    ∀ j < K, t15cSig G H z b (j + 1) ω =
      hitTime (verticesMeeting H.cell (sphere z (b j))) (G.vertexPath ω) := by
  intro j
  induction j with
  | zero =>
    intro _
    show thenTime (t15cSig G H z b 0) (hitTime (vset G (verticesMeeting H.cell (sphere z (b 0))))) ω = _
    rw [thenTime_eq_of_eq (n := 0) (by rfl), Nat.cast_zero, zero_add]
    have hsh : walkShift 0 ω = ω := by
      funext m
      rw [walkShift_apply, zero_add]
    rw [hsh]
    rfl
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    show thenTime (t15cSig G H z b (j + 1))
      (hitTime (vset G (verticesMeeting H.cell (sphere z (b (j + 1)))))) ω = _
    rw [thenTime_hitTime_eq_hitTime]
    · rfl
    · rw [hprev]
      exact t15c_hitTime_sphere_mono hstep (h0 ▸ hz) (hb0 j (by omega)) (hbm j hj)

/-- If the cell at time `m` is not contained in the open set `D` (and the first cell meets `D`), the walk has hit
`V(∂D)` by time `m`. -/
theorem t15c_hitTime_frontier_le (hDo : IsOpen D) {X : ℕ → V} (hX : ∀ n, StepOK G (X n) (X (n + 1)))
    (h0 : (H.cell (X 0) ∩ D).Nonempty) {m : ℕ} (hm : ¬ H.cell (X m) ⊆ D) :
    hitTime (verticesMeeting H.cell (frontier D)) X ≤ m := by
  obtain ⟨k, hkm, hk⟩ := t15c_exists_frontier_of_not_subset H hDo hX h0 hm
  exact (hitTime_le_of_mem (show X k ∈ verticesMeeting H.cell (frontier D) from hk)).trans
    (by exact_mod_cast hkm)

/-- **The first hit of `V(∂D)` lies in `V(D)`** (along a path with admissible steps from a cell meeting the open
set `D`). -/
theorem t15c_firstHit_meets (hDo : IsOpen D) {X : ℕ → V} (hX : ∀ n, StepOK G (X n) (X (n + 1)))
    (h0 : (H.cell (X 0) ∩ D).Nonempty) {T : ℕ} (hT : hitTime (verticesMeeting H.cell (frontier D)) X = T) :
    (H.cell (X T) ∩ D).Nonempty := by
  have hmin := (hitTime_eq_coe_iff.mp hT).2
  cases T with
  | zero => exact h0
  | succ k =>
    have hsub := t15c_cell_subset_of_forall_not_meet_frontier H hDo hX h0 k
      (fun j hj => hmin j (by omega)) k le_rfl
    obtain ⟨c, hc1, hc2⟩ := t15c_inter_nonempty_of_stepOK H (hX k)
    exact ⟨c, hc2, hsub hc1⟩

/-- **A bad first hit reaches every scale**: on a path from `x` with admissible steps, `z ∈ H_x`,
`H_x ∩ D ≠ ∅`, positive increasing radii `b j ≤ t` (`j < K`), if the walk hits `V(∂D)` but not inside
`V(D) ∩ V(∂D ∩ B_t(z))`, then the path reaches scale `K` after failing at all earlier scales. -/
theorem t15c_mem_reach_of_bad (hDo : IsOpen D) {x : V} (hxD : (H.cell x ∩ D).Nonempty) (hz : z ∈ H.cell x)
    {t : ℝ} {K : ℕ} (hb0 : ∀ j < K, 0 < b j) (hbm : ∀ j, j + 1 < K → b j ≤ b (j + 1))
    (hbt : ∀ j < K, b j ≤ t) {ω : ℕ → G.State} (h00 : G.stateVertex (ω 0) = x)
    (hstep : ∀ n, StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1)))
    (hT : hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω) ≠ ⊤)
    (hbad : G.vertexPath ω (hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω)).toNat ∉
      verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t)) :
    ω ∈ t15cReach G H x D z b K := by
  set X := G.vertexPath ω with hXdef
  have h0 : X 0 = x := h00
  obtain ⟨T, hTeq⟩ := ENat.ne_top_iff_exists.mp hT
  have hTeq' : hitTime (verticesMeeting H.cell (frontier D)) X = T := hTeq.symm
  rw [← hTeq, ENat.toNat_natCast] at hbad
  have hx0 : (H.cell (X 0) ∩ D).Nonempty := by rw [h0]; exact hxD
  -- (a) the first hit is in `V(D)` but not in `V(∂D ∩ B_t(z))`
  have hTD : X T ∈ verticesMeeting H.cell D := t15c_firstHit_meets hDo hstep hx0 hTeq'
  have hTfr : (H.cell (X T) ∩ frontier D).Nonempty := (hitTime_eq_coe_iff.mp hTeq').1
  have hTnot : ¬ (H.cell (X T) ∩ (frontier D ∩ ball z t)).Nonempty := fun h => hbad ⟨hTD, h⟩
  -- (b) every scale is hit by time `T`
  have hscale : ∀ j < K, hitTime (verticesMeeting H.cell (sphere z (b j))) X ≤ T := by
    intro j hj
    by_contra hlt
    push Not at hlt
    have hav : ∀ k ≤ T, ¬ (H.cell (X k) ∩ sphere z (b j)).Nonempty := fun k hk =>
      coe_lt_hitTime_iff.mp hlt k hk
    have hsub := t15c_cell_subset_ball_of_forall_not_meet H hstep (h0 ▸ hz) (hb0 j hj) T hav T le_rfl
    obtain ⟨q, hq, hqf⟩ := hTfr
    refine hTnot ⟨q, hq, hqf, ?_⟩
    exact ball_subset_ball (hbt j hj) (hsub hq)
  have hsig : ∀ j < K, t15cSig G H z b (j + 1) ω = hitTime (verticesMeeting H.cell (sphere z (b j))) X :=
    t15c_sig_succ_eq_hitTime h0 hstep hz hb0 hbm
  refine ⟨?_, h00, fun i hi => ?_⟩
  · -- (e) the last scale time is finite
    cases K with
    | zero => exact ENat.natCast_lt_top 0
    | succ j =>
      rw [hsig j (by omega)]
      exact lt_of_le_of_lt (hscale j (by omega)) (ENat.natCast_lt_top T)
  · -- (d) no success at a scale `i < K`
    rintro ⟨hlt, m, hm, hmD⟩
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    rw [stopShift_eq_of_eq hn.symm] at hm hmD
    have hXm : G.vertexPath (walkShift n ω) m = X (n + m) := rfl
    rw [hXm] at hmD
    have h1 : (T : ℕ∞) ≤ (n + m : ℕ) := by
      rw [← hTeq']
      exact t15c_hitTime_frontier_le hDo hstep hx0 hmD
    have h2 : t15cSig G H z b (i + 1) ω =
        n + hitTime (vset G (verticesMeeting H.cell (sphere z (b i)))) (walkShift n ω) :=
      thenTime_eq_of_eq hn.symm
    have h3 : ((n + m : ℕ) : ℕ∞) < t15cSig G H z b (i + 1) ω := by
      rw [h2, Nat.cast_add]
      exact (ENat.add_lt_add_iff_left (ENat.natCast_ne_top n)).mpr hm
    have h4 := hscale i hi
    rw [← hsig i hi] at h4
    exact absurd (lt_of_le_of_lt h1 h3) (not_lt.mpr h4)

/-- **(3.38), iteration with generic radii.** Let `D` be open, `H_x ∩ D ≠ ∅`, `z ∈ H_x`, and let the radii `b j`
(`j < K`) be positive, increasing and `≤ t`. If the exit bound at scale `j` holds with probability `≥ p` from every
vertex of `S j`, where `x ∈ S 0` and `V(∂B_{b j}(z)) ⊆ S (j + 1)`, then the walk from `x` first hits `V(∂D)` outside
`V(D) ∩ V(∂D ∩ B_t(z))` with probability at most `(1 − p)^K`. -/
theorem t15c_hitDist_compl_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hDo : IsOpen D) {x : V}
    (hxD : (H.cell x ∩ D).Nonempty) (hz : z ∈ H.cell x) {t : ℝ} {K : ℕ} (hb0 : ∀ j < K, 0 < b j)
    (hbm : ∀ j, j + 1 < K → b j ≤ b (j + 1)) (hbt : ∀ j < K, b j ≤ t) {S : ℕ → Set V} (hx : x ∈ S 0)
    (hS : ∀ j, verticesMeeting H.cell (sphere z (b j)) ⊆ S (j + 1))
    (hsucc : ∀ j < K, ∀ y ∈ S j, ENNReal.ofReal p ≤ G.walkLaw y (t15cExitBefore G H D z (b j))) :
    hitDist G (verticesMeeting H.cell (frontier D)) x
      (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ ≤
      ENNReal.ofReal ((1 - p) ^ K) := by
  have : Countable V := GMS3.countable_vertex H
  have : Countable G.State := countable_state G
  set Bad : Set (ℕ → G.State) := {ω | hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω) ≠ ⊤ ∧
    G.vertexPath ω (hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω)).toNat ∈
      (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ} with hBad
  have hsub : Bad ∩ goodPath G x ⊆ t15cReach G H x D z b K := by
    rintro ω ⟨⟨hT, hbad⟩, h0, hstep⟩
    exact t15c_mem_reach_of_bad hDo hxD hz hb0 hbm hbt (by rw [h0]; rfl) hstep hT hbad
  calc hitDist G (verticesMeeting H.cell (frontier D)) x
        (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ
      = G.walkLaw x Bad := rfl
    _ = G.walkLaw x (Bad ∩ goodPath G x) := (measure_inter_conull (walkLaw_compl_goodPath x)).symm
    _ ≤ G.walkLaw x (t15cReach G H x D z b K) := measure_mono hsub
    _ ≤ ENNReal.ofReal ((1 - p) ^ K) := t15c_walkLaw_reach_le hp0 hp1 hx hS hsucc K le_rfl

/-- **(3.38) at [18]'s scales** (`[18]`, with ratio `4` between consecutive radii instead of `e`): let `D` be
open and bounded with `ℂ \ D` preconnected, `H_x ∩ D ≠ ∅`, `z ∈ H_x`, `r₀ > 0`, and let `ℂ \ D` have a point within
`r₀/2` of `z`. If [18] (3.35) holds at `z` for the radii `4^j r₀` (`j < K`) and `2 · 4^j r₀ ≤ t`, then
`P_x[X first hits V(∂D) in V(D) ∩ V(∂D ∩ B_t(z))]ᶜ ≤ (1 − p)^K`. -/
theorem t15c_hitDist_compl_le_of_disconnectionAt (hLC : H.PointConnected) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hDo : IsOpen D) (hDb : Bornology.IsBounded D) (hDc : IsPreconnected Dᶜ) {x : V}
    (hxD : (H.cell x ∩ D).Nonempty) (hz : z ∈ H.cell x) {r₀ : ℝ} (hr₀ : 0 < r₀) {w₀ : ℂ} (hw₀ : w₀ ∉ D)
    (hw₀r : dist w₀ z ≤ r₀ / 2) {t : ℝ} {K : ℕ} (ht : ∀ j < K, 2 * (4 ^ j * r₀) ≤ t)
    (h35 : ∀ j < K, t15cDisconnectionAt G H p z (4 ^ j * r₀)) :
    hitDist G (verticesMeeting H.cell (frontier D)) x
      (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ ≤
      ENNReal.ofReal ((1 - p) ^ K) := by
  have hrj : ∀ j : ℕ, 0 < 4 ^ j * r₀ := fun j => by positivity
  have hr₀j : ∀ j : ℕ, r₀ ≤ 4 ^ j * r₀ := fun j =>
    le_mul_of_one_le_left hr₀.le (one_le_pow₀ (by norm_num))
  refine t15c_hitDist_compl_le (b := fun j => 2 * (4 ^ j * r₀))
    (S := fun j => verticesMeeting H.cell (ball z (4 ^ j * r₀))) hp0 hp1 hDo hxD hz
    (fun j _ => by have := hrj j; positivity) (fun j _ => ?_) ht ?_ (fun j => ?_) (fun j hj => ?_)
  · show 2 * (4 ^ j * r₀) ≤ 2 * (4 ^ (j + 1) * r₀)
    have : 4 ^ j * r₀ ≤ 4 ^ (j + 1) * r₀ := by
      rw [pow_succ]
      nlinarith [hrj j]
    linarith
  · exact ⟨z, hz, by rw [pow_zero, one_mul]; exact mem_ball_self hr₀⟩
  · rintro y ⟨q, hq, hqs⟩
    refine ⟨q, hq, ?_⟩
    rw [mem_ball, mem_sphere.mp hqs, pow_succ]
    nlinarith [hrj j]
  · exact t15c_le_walkLaw_exitBefore hLC hDc hDb (hrj j) hw₀
      (hw₀r.trans (by linarith [hr₀j j])) (h35 j hj)

end Paths

end MatedCRTHarmonic.GMSMain
