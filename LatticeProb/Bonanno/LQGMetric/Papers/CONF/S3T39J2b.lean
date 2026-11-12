/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J2b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J2
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Rational chain classes of `closure Γ ∖ P` and their Effros-measurability (DEC-120 §4, J3)

The arcs of the canonical subdivision (CONF C:1740–1744, DV-D120-1) are the components of
`Γ ∖ P_L`, `P_L = {t39jPt j Γ | j < L valid}` (the cut set, `t39jCut`). To make their hit events
Effros-measurable, components are described by **rational chains**: `t39jRC L Γ x y` says that
for some `η > 0` and every `ε > 0` there is a chain of rational points `w₀, …, w_n`, each with
`Γ ∩ B_δ(w_i) ≠ ∅` and `dist(w_i, P_L) > η + δ`, steps `< ε − 2δ`, from near `x` to near `y`.
`t39jClass L Γ x = {y ∈ closure Γ ∖ P_L | t39jRC L Γ x y}`.

* `t39j_rc_meas`: `{Γ | t39jRC L Γ (x Γ) (y Γ)}` is Effros-measurable for measurable `x, y`;
* `t39j_class_hit_meas`: the hit events of `t39jClass L Γ (x Γ)` are Effros-measurable
  (limit argument in the compact `closure Γ ∩ closedBall`, no assumption on `Γ`).

That rational chain classes are the components of `Γ ∖ P_L` for a Jordan curve `Γ` is in
S3T39J3b. Own elementary arguments (the ε-chain description of components of compact sets).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology Function

namespace LQGMetric.CONF

attribute [local instance 2000] effrosSigma

/-- rational points of `ℂ` -/
def t39jRq (v : ℚ × ℚ) : ℂ := ⟨(v.1 : ℝ), (v.2 : ℝ)⟩

/-- the cut set of level `L`: the valid selected points of index `< L` -/
def t39jCut (L : ℕ) (Γ : Set ℂ) : Set ℂ := {p | ∃ j < L, t39jValid j Γ ∧ p = t39jPt j Γ}

/-- a good chain point -/
def t39jGood (L : ℕ) (η δ : ℝ) (Γ : Set ℂ) (w : ℂ) : Prop :=
  w ∈ range t39jRq ∧ (Γ ∩ ball w δ).Nonempty ∧ ∀ p ∈ t39jCut L Γ, η + δ < dist w p

/-- `n`-step rational chains -/
def t39jReach (L : ℕ) (η ε δ : ℝ) (Γ : Set ℂ) : ℕ → ℂ → ℂ → Prop
  | 0, w, w' => w = w'
  | n + 1, w, w' => ∃ v, t39jReach L η ε δ Γ n w v ∧ t39jGood L η δ Γ v ∧
      t39jGood L η δ Γ w' ∧ dist v w' + 2 * δ < ε

/-- the rational chain relation -/
def t39jRC (L : ℕ) (Γ : Set ℂ) (x y : ℂ) : Prop :=
  ∃ η : ℚ, 0 < η ∧ ∀ ε : ℚ, 0 < ε → ∃ δ : ℚ, 0 < δ ∧ ∃ w w' : ℂ, ∃ n : ℕ,
    t39jGood L η δ Γ w ∧ t39jGood L η δ Γ w' ∧ dist x w + δ < ε ∧ dist w' y + δ < ε ∧
      t39jReach L η ε δ Γ n w w'

/-- the rational chain class of `x` in `closure Γ ∖ P_L` -/
def t39jClass (L : ℕ) (Γ : Set ℂ) (x : ℂ) : Set ℂ :=
  {y | y ∈ closure Γ ∧ y ∉ t39jCut L Γ ∧ t39jRC L Γ x y}

theorem t39jGood_mono {L : ℕ} {η η' δ : ℝ} {Γ : Set ℂ} {w : ℂ} (h : t39jGood L η δ Γ w)
    (hη : η' ≤ η) : t39jGood L η' δ Γ w :=
  ⟨h.1, h.2.1, fun p hp => lt_of_le_of_lt (by linarith) (h.2.2 p hp)⟩

theorem t39jReach_mono {L : ℕ} {η η' ε ε' δ : ℝ} {Γ : Set ℂ} (hη : η' ≤ η) (hε : ε ≤ ε') :
    ∀ n w w', t39jReach L η ε δ Γ n w w' → t39jReach L η' ε' δ Γ n w w'
  | 0, _, _, h => h
  | n + 1, w, w', ⟨v, hv, hg, hg', hd⟩ =>
    ⟨v, t39jReach_mono hη hε n w v hv, t39jGood_mono hg hη, t39jGood_mono hg' hη, by linarith⟩

/-! ### measurability -/

theorem t39j_cutAvoid_meas (L : ℕ) (c : ℝ) {w : Set ℂ → ℂ} (hw : Measurable[effrosSigma] w) :
    MeasurableSet[effrosSigma] {Γ | ∀ p ∈ t39jCut L Γ, c < dist (w Γ) p} := by
  have heq : {Γ | ∀ p ∈ t39jCut L Γ, c < dist (w Γ) p} =
      ⋂ j ∈ Finset.range L, ({Γ | t39jValid j Γ}ᶜ ∪ {Γ | c < dist (w Γ) (t39jPt j Γ)}) := by
    ext Γ
    simp only [t39jCut, mem_setOf_eq, mem_iInter, Finset.mem_range, mem_union, mem_compl_iff]
    constructor
    · intro h j hj
      by_cases hv : t39jValid j Γ
      · exact Or.inr (h _ ⟨j, hj, hv, rfl⟩)
      · exact Or.inl hv
    · rintro h p ⟨j, hj, hv, rfl⟩
      exact (h j hj).resolve_left (not_not.2 hv)
  rw [heq]
  refine Finset.measurableSet_biInter _ fun j _ => (t39jValid_meas j).compl.union ?_
  exact measurableSet_lt measurable_const (hw.dist (t39jPt_meas j))

theorem t39j_good_meas (L : ℕ) (η δ : ℝ) (v : ℚ × ℚ) :
    MeasurableSet[effrosSigma] {Γ | t39jGood L η δ Γ (t39jRq v)} := by
  have heq : {Γ | t39jGood L η δ Γ (t39jRq v)} =
      {Γ | (Γ ∩ ball (t39jRq v) δ).Nonempty} ∩
        {Γ | ∀ p ∈ t39jCut L Γ, η + δ < dist ((fun _ => t39jRq v) Γ) p} := by
    ext Γ; simp [t39jGood]
  rw [heq]
  exact (t39j_hit_open isOpen_ball).inter (t39j_cutAvoid_meas L _ measurable_const)

theorem t39j_reach_meas (L : ℕ) (η ε δ : ℝ) (n : ℕ) (v v' : ℚ × ℚ) :
    MeasurableSet[effrosSigma] {Γ | t39jReach L η ε δ Γ n (t39jRq v) (t39jRq v')} := by
  induction n generalizing v' with
  | zero => exact MeasurableSet.const _
  | succ n ih =>
    have heq : {Γ | t39jReach L η ε δ Γ (n + 1) (t39jRq v) (t39jRq v')} =
        ⋃ u : ℚ × ℚ, ({Γ | t39jReach L η ε δ Γ n (t39jRq v) (t39jRq u)} ∩
          {Γ | t39jGood L η δ Γ (t39jRq u)} ∩ {Γ | t39jGood L η δ Γ (t39jRq v')} ∩
          {_Γ | dist (t39jRq u) (t39jRq v') + 2 * δ < ε}) := by
      ext Γ
      simp only [t39jReach, mem_setOf_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨w, hw, hg, hg', hd⟩
        obtain ⟨u, rfl⟩ := hg.1
        exact ⟨u, ⟨⟨hw, hg⟩, hg'⟩, hd⟩
      · rintro ⟨u, ⟨⟨hw, hg⟩, hg'⟩, hd⟩
        exact ⟨_, hw, hg, hg', hd⟩
    rw [heq]
    exact MeasurableSet.iUnion fun u => (((ih u).inter (t39j_good_meas L η δ u)).inter
      (t39j_good_meas L η δ v')).inter (MeasurableSet.const _)

/-- the core countable description: `∃ δ w w' n` with endpoint conditions `E₁ w`, `E₂ w'` -/
theorem t39j_chain_meas (L : ℕ) (η ε δ : ℝ) (E₁ E₂ : Set ℂ → ℂ → Prop)
    (h₁ : ∀ v, MeasurableSet[effrosSigma] {Γ | E₁ Γ (t39jRq v)})
    (h₂ : ∀ v, MeasurableSet[effrosSigma] {Γ | E₂ Γ (t39jRq v)}) :
    MeasurableSet[effrosSigma] {Γ | ∃ w w' : ℂ, ∃ n : ℕ, t39jGood L η δ Γ w ∧
      t39jGood L η δ Γ w' ∧ E₁ Γ w ∧ E₂ Γ w' ∧ t39jReach L η ε δ Γ n w w'} := by
  have heq : {Γ | ∃ w w' : ℂ, ∃ n : ℕ, t39jGood L η δ Γ w ∧
      t39jGood L η δ Γ w' ∧ E₁ Γ w ∧ E₂ Γ w' ∧ t39jReach L η ε δ Γ n w w'} =
      ⋃ v : ℚ × ℚ, ⋃ v' : ℚ × ℚ, ⋃ n : ℕ, ({Γ | t39jGood L η δ Γ (t39jRq v)} ∩
        {Γ | t39jGood L η δ Γ (t39jRq v')} ∩ {Γ | E₁ Γ (t39jRq v)} ∩ {Γ | E₂ Γ (t39jRq v')} ∩
        {Γ | t39jReach L η ε δ Γ n (t39jRq v) (t39jRq v')}) := by
    ext Γ
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨w, w', n, hg, hg', h1, h2, hr⟩
      obtain ⟨v, rfl⟩ := hg.1
      obtain ⟨v', rfl⟩ := hg'.1
      exact ⟨v, v', n, ⟨⟨⟨hg, hg'⟩, h1⟩, h2⟩, hr⟩
    · rintro ⟨v, v', n, ⟨⟨⟨hg, hg'⟩, h1⟩, h2⟩, hr⟩
      exact ⟨_, _, n, hg, hg', h1, h2, hr⟩
  rw [heq]
  exact MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun v' => MeasurableSet.iUnion fun n =>
    (((((t39j_good_meas L η δ v).inter (t39j_good_meas L η δ v')).inter (h₁ v)).inter
      (h₂ v')).inter (t39j_reach_meas L η ε δ n v v'))

/-- **the rational chain relation between measurable points is Effros-measurable** -/
theorem t39j_rc_meas (L : ℕ) {x y : Set ℂ → ℂ} (hx : Measurable[effrosSigma] x)
    (hy : Measurable[effrosSigma] y) :
    MeasurableSet[effrosSigma] {Γ | t39jRC L Γ (x Γ) (y Γ)} := by
  have heq : {Γ | t39jRC L Γ (x Γ) (y Γ)} = ⋃ η : ℚ, ⋃ (_ : 0 < η), ⋂ ε : ℚ, ⋂ (_ : 0 < ε),
      ⋃ δ : ℚ, ⋃ (_ : 0 < δ), {Γ | ∃ w w' : ℂ, ∃ n : ℕ, t39jGood L η δ Γ w ∧
        t39jGood L η δ Γ w' ∧ dist (x Γ) w + δ < ε ∧ dist w' (y Γ) + δ < ε ∧
          t39jReach L η ε δ Γ n w w'} := by
    ext Γ; simp only [t39jRC, mem_setOf_eq, mem_iUnion, mem_iInter, exists_prop]
  rw [heq]
  refine MeasurableSet.iUnion fun η => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun ε =>
    MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun δ => MeasurableSet.iUnion fun _ =>
      t39j_chain_meas L _ _ _ (fun Γ w => dist (x Γ) w + δ < ε) (fun Γ w' => dist w' (y Γ) + δ < ε)
        (fun v => measurableSet_lt ((hx.dist measurable_const).add_const _) measurable_const)
        (fun v => measurableSet_lt ((measurable_const.dist hy).add_const _) measurable_const)

/-- the hit formula of a chain class -/
def t39jHitF (L : ℕ) (Γ : Set ℂ) (x : ℂ) (U : Set ℂ) : Prop :=
  ∃ j, t39jBall j ⊆ U ∧ ∃ η : ℚ, 0 < η ∧ ∀ ε : ℚ, 0 < ε → ∃ δ : ℚ, 0 < δ ∧ ∃ w w' : ℂ, ∃ n : ℕ,
    t39jGood L η δ Γ w ∧ t39jGood L η δ Γ w' ∧ dist x w + δ < ε ∧
      dist w' (t39jBc j) + δ < t39jBr j + ε ∧ t39jReach L η ε δ Γ n w w'

theorem t39j_hitF_meas (L : ℕ) {x : Set ℂ → ℂ} (hx : Measurable[effrosSigma] x) (U : Set ℂ) :
    MeasurableSet[effrosSigma] {Γ | t39jHitF L Γ (x Γ) U} := by
  have heq : {Γ | t39jHitF L Γ (x Γ) U} = ⋃ j : ℕ, ⋃ (_ : t39jBall j ⊆ U), ⋃ η : ℚ,
      ⋃ (_ : 0 < η), ⋂ ε : ℚ, ⋂ (_ : 0 < ε), ⋃ δ : ℚ, ⋃ (_ : 0 < δ),
        {Γ | ∃ w w' : ℂ, ∃ n : ℕ, t39jGood L η δ Γ w ∧ t39jGood L η δ Γ w' ∧
          dist (x Γ) w + δ < ε ∧ dist w' (t39jBc j) + δ < t39jBr j + ε ∧
            t39jReach L η ε δ Γ n w w'} := by
    ext Γ; simp only [t39jHitF, mem_setOf_eq, mem_iUnion, mem_iInter, exists_prop]
  rw [heq]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun η =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun ε => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun δ => MeasurableSet.iUnion fun _ =>
        t39j_chain_meas L _ _ _ (fun Γ w => dist (x Γ) w + δ < ε)
          (fun _ w' => dist w' (t39jBc j) + δ < t39jBr j + ε)
          (fun v => measurableSet_lt ((hx.dist measurable_const).add_const _) measurable_const)
          (fun v => MeasurableSet.const _)

/-- **the hit formula describes the hit events of a chain class** (any `Γ`) -/
theorem t39j_class_hit_iff (L : ℕ) (Γ : Set ℂ) (x : ℂ) {U : Set ℂ} (hU : IsOpen U) :
    (t39jClass L Γ x ∩ U).Nonempty ↔ t39jHitF L Γ x U := by
  constructor
  · rintro ⟨y, ⟨-, -, η, hη, H⟩, hyU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hyU
    obtain ⟨j, hyj, hj⟩ := t39j_ball_basis y hr
    refine ⟨j, hj.trans hrU, η, hη, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, w, w', n, hg, hg', h1, h2, hr'⟩ := H ε hε
    refine ⟨δ, hδ, w, w', n, hg, hg', h1, ?_, hr'⟩
    have := dist_triangle w' y (t39jBc j)
    rw [t39jBall, mem_closedBall] at hyj
    linarith
  · rintro ⟨j, hjU, η, hη, H⟩
    have hεn : ∀ k : ℕ, (0 : ℚ) < 1 / ((k : ℚ) + 1) := fun k => by positivity
    choose δ hδ w w' n hg hg' h1 h2 hr using fun k : ℕ => H _ (hεn k)
    choose z hzΓ hzw using fun k => (hg' k).2.1
    have hzK : ∀ k, z k ∈ closure Γ ∩ closedBall (t39jBc j) (t39jBr j + 1) := by
      intro k
      refine ⟨subset_closure (hzΓ k), ?_⟩
      rw [mem_closedBall]
      have := dist_triangle (z k) (w' k) (t39jBc j)
      have h3 := mem_ball.1 (hzw k)
      have h4 := h2 k
      have h5 : ((1 / ((k : ℚ) + 1) : ℚ) : ℝ) ≤ 1 := by
        push_cast; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      linarith
    obtain ⟨y, hyK, φ, hφ, hlim⟩ :=
      ((isCompact_closedBall (t39jBc j) (t39jBr j + 1)).inter_left isClosed_closure).tendsto_subseq
        hzK
    have hεR : ∀ k : ℕ, ((1 / ((k : ℚ) + 1) : ℚ) : ℝ) = 1 / ((k : ℝ) + 1) := fun k => by push_cast; rfl
    have hδε : ∀ k, (δ k : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by
      have := h1 k; rw [hεR] at this; linarith [dist_nonneg (x := x) (y := w k)]
    have hzP : ∀ k, ∀ p ∈ t39jCut L Γ, (η : ℝ) < dist (z k) p := fun k p hp => by
      have := (hg' k).2.2 p hp
      have h3 := mem_ball.1 (hzw k)
      linarith [dist_triangle (w' k) (z k) p, dist_comm (w' k) (z k)]
    have hzc : ∀ k, dist (z k) (t39jBc j) < t39jBr j + 1 / ((k : ℝ) + 1) := fun k => by
      have := h2 k; rw [hεR] at this
      have h3 := mem_ball.1 (hzw k)
      linarith [dist_triangle (z k) (w' k) (t39jBc j)]
    have hε0 : Tendsto (fun i => 1 / ((φ i : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
    have hyP : ∀ p ∈ t39jCut L Γ, (η : ℝ) ≤ dist y p := fun p hp =>
      ge_of_tendsto ((hlim.dist tendsto_const_nhds)) (Eventually.of_forall fun i => (hzP _ p hp).le)
    have hyc : dist y (t39jBc j) ≤ t39jBr j := by
      refine le_of_tendsto_of_tendsto (hlim.dist tendsto_const_nhds)
        (by simpa using (tendsto_const_nhds (x := t39jBr j)).add hε0) ?_
      exact Eventually.of_forall fun i => by simpa only [Function.comp_apply, one_div] using (hzc (φ i)).le
    have hη0 : (0 : ℝ) < η := by exact_mod_cast hη
    refine ⟨y, ⟨hyK.1, fun hyc' => ?_, η / 2, by positivity, fun ε hε => ?_⟩, hjU hyc⟩
    · have := hyP y hyc'; rw [dist_self] at this; linarith
    · have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
      obtain ⟨i, hi1, hi2⟩ := ((hlim.eventually (ball_mem_nhds y (show (0 : ℝ) < ε / 3 by
        positivity))).and (hε0.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by
        positivity)))).exists
      set k := φ i
      have hη2 : (((η / 2 : ℚ)) : ℝ) ≤ η := by push_cast; linarith
      have hεk : ((1 / ((k : ℚ) + 1) : ℚ) : ℝ) ≤ ε := by rw [hεR]; linarith
      refine ⟨δ k, hδ k, w k, w' k, n k, t39jGood_mono (hg k) hη2, t39jGood_mono (hg' k) hη2,
        lt_of_lt_of_le (h1 k) hεk, ?_, t39jReach_mono hη2 hεk _ _ _ (hr k)⟩
      have h3 := mem_ball.1 (hzw k)
      have hi1 : dist (z k) y < ε / 3 := hi1
      have := hδε k
      linarith [dist_triangle (w' k) (z k) y, dist_comm (w' k) (z k)]

/-- **hit events of the chain class of a measurable point are Effros-measurable** -/
theorem t39j_class_hit_meas (L : ℕ) {x : Set ℂ → ℂ} (hx : Measurable[effrosSigma] x)
    {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet[effrosSigma] {Γ | (t39jClass L Γ (x Γ) ∩ U).Nonempty} := by
  have : {Γ | (t39jClass L Γ (x Γ) ∩ U).Nonempty} = {Γ | t39jHitF L Γ (x Γ) U} := by
    ext Γ; exact t39j_class_hit_iff L Γ (x Γ) hU
  rw [this]; exact t39j_hitF_meas L hx U

/-- **the arc-choice interface** (DEC-120 §4), with `subset` in the form `⊆ closure Γ`
(P2-CONFJ3): every Effros-measurable event is closure-invariant, so `meas` forces
`closure (arcs m i Γ) = closure (arcs m i (closure Γ))`; with `arcs m i Γ ⊆ Γ` for all `Γ` this
excludes one-point arcs `{p}` of a Jordan curve `K` (take `Γ = K ∖ {p}`), while every covering
partition of `K` into finitely many disjoint connected pieces has a non-open piece. The consumer
(`T39JRestData.hI₀`, `Γ = ∂𝓑^•_τ` closed) only uses closed `Γ`, where both forms agree. -/
structure T39JArcChoice where
  arcs : (m : ℕ) → Fin m → Set ℂ → Set ℂ
  subset : ∀ m i Γ, arcs m i Γ ⊆ closure Γ
  meas : ∀ m i (U : Set ℂ), IsOpen U →
    MeasurableSet[effrosSigma] {Γ | (arcs m i Γ ∩ U).Nonempty}
  conn : ∀ m i Γ, JordanMap.IsJordanCurve Γ → (arcs m i Γ).Nonempty →
    IsPreconnected (arcs m i Γ)
  disj : ∀ m Γ, JordanMap.IsJordanCurve Γ → Pairwise (Disjoint on fun i => arcs m i Γ)
  sep : ∀ Γ, JordanMap.IsJordanCurve Γ → ∀ F : Finset ℂ, (F : Set ℂ) ⊆ Γ →
    ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ arcs m i Γ) ∧
      ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ arcs m i Γ → y ∈ arcs m i Γ → x = y

end LQGMetric.CONF
