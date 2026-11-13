/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RatShiftBridgeCadlag at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.Fintype.Pigeonhole

/-!
# A measurable rational-time criterion for a càdlàg extension

The rational-shift bridge (`CellRootedRegenerativeInvariance.RatShiftBridge`) asks for a càdlàg
configuration with prescribed rational-time readings.  Its a.s. validity has to be transferred
from the sample space to the law on the regularity subtype, which needs a MEASURABLE event.  "The
rational readings extend to a càdlàg path" is such an event:

* `RatCadlag a`: right-continuity at every rational through the rationals, and for every window
  `[-N, N]` and every `1/(m+1)` a bound on the length of chains of rationals with all
  consecutive jumps above `1/(m+1)` (a countable oscillation criterion);
* `measurableSet_ratCadlag`: it is a measurable subset of `ℚ → E`;
* `ratCadlag_of_isCadlag`: the rational readings of a càdlàg path satisfy it (compactness of
  `[-N, N]` and pigeonhole over the finitely many one-sided pieces of a finite subcover);
* `exists_cadlag_of_ratCadlag`: conversely, in a complete space the one-sided limits through the
  rationals exist everywhere, and the right-limit function is a càdlàg extension.

Reuse: mathlib's `IsCadlag`, `Metric.cauchy_iff`, `CompleteSpace.complete`,
`IsCompact.elim_finite_subcover`, `Fintype.exists_ne_map_eq_of_card_lt`,
`Fin.strictMono_iff_lt_succ`.  No existing criterion of this kind was found in mathlib or in the
project (searched: `IsCadlag`, `ratEval`, `limUnder`, `Cauchy` over the rationals).
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace ReflectedGMS.RatShiftBridgeCadlag

variable {E : Type*} [PseudoMetricSpace E]

/-- Right-continuity at every rational, through the rationals. -/
def RatRightCont (a : ℚ → E) : Prop :=
  ∀ (q : ℚ) (m : ℕ), ∃ j : ℕ, ∀ r : ℚ, q < r → r < q + 1 / ((j : ℚ) + 1) →
    dist (a r) (a q) < 1 / ((m : ℝ) + 1)

/-- No chain of `K + 1` rationals in `[-N, N]` has all its consecutive jumps above `ε`. -/
def ChainBound (a : ℚ → E) (ε : ℝ) (N K : ℕ) : Prop :=
  ∀ r : Fin (K + 1) → ℚ, StrictMono r → (∀ i, |r i| ≤ N) →
    ∃ i : Fin K, dist (a (r i.succ)) (a (r i.castSucc)) ≤ ε

/-- **The rational-time càdlàg criterion.** -/
def RatCadlag (a : ℚ → E) : Prop :=
  RatRightCont a ∧ ∀ N m : ℕ, ∃ K : ℕ, ChainBound a (1 / ((m : ℝ) + 1)) N K

/-! ### 1. Measurability -/

theorem measurableSet_ratCadlag [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] : MeasurableSet {a : ℚ → E | RatCadlag a} := by
  have hd : ∀ r q : ℚ, Measurable fun a : ℚ → E => dist (a r) (a q) :=
    fun r q => (measurable_pi_apply r).dist (measurable_pi_apply q)
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · refine Measurable.forall fun q => Measurable.forall fun m => Measurable.exists fun j =>
      Measurable.forall fun r => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1 (measurableSet_lt (hd r q) measurable_const)
  · refine Measurable.forall fun N => Measurable.forall fun m => Measurable.exists fun K =>
      Measurable.forall fun r => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact Measurable.exists fun i =>
      measurableSet_setOfPred.1 (measurableSet_le (hd _ _) measurable_const)

/-! ### 2. The readings of a càdlàg path satisfy the criterion -/

theorem ratRightCont_of_isCadlag {Z : ℝ → E} (hZ : IsCadlag Z) :
    RatRightCont fun q : ℚ => Z q := by
  intro q m
  have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hZ.isRightContinuous (q : ℝ)) _ hm
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨j, fun r hqr hr => hball (show (q : ℝ) < r by exact_mod_cast hqr) ?_⟩
  have hr' : (r : ℝ) < q + 1 / ((j : ℝ) + 1) := by
    have h := (Rat.cast_lt (K := ℝ)).2 hr
    push_cast at h
    exact h
  have hqr' : (q : ℝ) < r := by exact_mod_cast hqr
  rw [Real.dist_eq, abs_of_pos (sub_pos.2 hqr')]
  linarith

theorem chainBound_of_isCadlag {Z : ℝ → E} (hZ : IsCadlag Z) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ChainBound (fun q : ℚ => Z q) ε N K := by
  have hloc : ∀ s : ℝ, ∃ δ > 0, (∀ t, s ≤ t → t < s + δ → dist (Z t) (Z s) < ε / 2) ∧
      ∃ l : E, ∀ t, s - δ < t → t < s → dist (Z t) l < ε / 2 := by
    intro s
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousWithinAt_iff.1 (hZ.isRightContinuous s) _ hε2
    obtain ⟨l, hl⟩ := hZ.tendsto_nhdsLT s
    obtain ⟨δ2, hδ2, h2⟩ := Metric.tendsto_nhdsWithin_nhds.1 hl _ hε2
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun t hst hts => ?_, l, fun t hts hts' => ?_⟩
    · rcases eq_or_lt_of_le hst with h | h
      · rw [← h, dist_self]
        exact hε2
      · refine h1 (show t ∈ Ioi s from h) ?_
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 h)]
        linarith [min_le_left δ1 δ2]
    · refine h2 (show t ∈ Iio s from hts') ?_
      rw [Real.dist_eq, abs_of_neg (sub_neg.2 hts')]
      linarith [min_le_right δ1 δ2]
  choose δ hδ hR l hL using hloc
  obtain ⟨F, hF⟩ := (isCompact_Icc (a := -(N : ℝ)) (b := N)).elim_finite_subcover
    (fun s => Ioo (s - δ s) (s + δ s)) (fun _ => isOpen_Ioo)
    (fun x _ => mem_iUnion.2 ⟨x, ⟨by linarith [hδ x], by linarith [hδ x]⟩⟩)
  refine ⟨2 * F.card, fun r hr hN => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ i, ∃ s ∈ F, (r i : ℝ) ∈ Ioo (s - δ s) (s + δ s) := by
    intro i
    have hi : (r i : ℝ) ∈ Icc (-(N : ℝ)) N := by
      have h := abs_le.1 (hN i)
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    obtain ⟨s, hs, hsm⟩ := mem_iUnion₂.1 (hF hi)
    exact ⟨s, hs, hsm⟩
  choose s hsF hsI using hmem
  let pc : Fin (2 * F.card + 1) → F × Bool := fun i => (⟨s i, hsF i⟩, decide ((r i : ℝ) < s i))
  have key : ∀ i j : Fin (2 * F.card + 1), i < j → pc i = pc j → False := by
    intro i j hij hpc
    have hi : i.val < 2 * F.card := by
      have := j.isLt
      have : i.val < j.val := hij
      omega
    let i' : Fin (2 * F.card) := ⟨i.val, hi⟩
    have hic : i'.castSucc = i := Fin.ext rfl
    have hsucc : i'.succ ≤ j := by
      show i.val + 1 ≤ j.val
      exact hij
    have hlt : (r i : ℝ) < r i'.succ := by
      have : r i < r i'.succ := hr (show i < i'.succ from Fin.lt_iff_val_lt_val.2 (by simp [i']))
      exact_mod_cast this
    have hle : (r i'.succ : ℝ) ≤ r j := by
      exact_mod_cast hr.monotone hsucc
    have hs_eq : s i = s j := congrArg Subtype.val (congrArg Prod.fst hpc)
    have hd_eq : decide ((r i : ℝ) < s i) = decide ((r j : ℝ) < s j) := congrArg Prod.snd hpc
    have hbad : ε < dist (Z (r i'.succ : ℝ)) (Z (r i : ℝ)) := by
      have h := hcon i'
      rw [hic] at h
      exact h
    set σ := s i with hσ
    have hIi := hsI i
    have hIj := hsI j
    rw [← hs_eq] at hIj
    by_cases hri : (r i : ℝ) < σ
    · have hrj : (r j : ℝ) < σ := by
        have h := hd_eq
        rw [← hs_eq] at h
        simpa [hri] using h.symm
      have h1 := hL σ (r i'.succ) (by linarith [hIi.1]) (by linarith)
      have h2 := hL σ (r i) hIi.1 hri
      have h3 := dist_triangle_right (Z (r i'.succ)) (Z (r i)) (l σ)
      linarith
    · have hri' : σ ≤ (r i : ℝ) := not_lt.1 hri
      have h1 := hR σ (r i'.succ) (by linarith) (by linarith [hIj.2])
      have h2 := hR σ (r i) hri' hIi.2
      have h3 := dist_triangle_right (Z (r i'.succ)) (Z (r i)) (Z σ)
      linarith
  obtain ⟨i, j, hij, hpc⟩ := Fintype.exists_ne_map_eq_of_card_lt pc (by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Fintype.card_fin]
    omega)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hpc
  · exact key j i h hpc.symm

/-- **The rational readings of a càdlàg path satisfy the criterion.** -/
theorem ratCadlag_of_isCadlag {Z : ℝ → E} (hZ : IsCadlag Z) : RatCadlag fun q : ℚ => Z q :=
  ⟨ratRightCont_of_isCadlag hZ, fun N m => chainBound_of_isCadlag hZ N (by positivity)⟩

/-! ### 3. The criterion gives a càdlàg extension -/

/-- Chain bounds are invariant under time reversal. -/
theorem chainBound_neg {a : ℚ → E} {ε : ℝ} {N K : ℕ} (h : ChainBound a ε N K) :
    ChainBound (fun q => a (-q)) ε N K := by
  intro r hr hN
  obtain ⟨i, hi⟩ := h (fun i => -r (Fin.rev i)) (fun i j hij => by
    have : r (Fin.rev j) < r (Fin.rev i) := hr (Fin.rev_lt_rev.2 hij)
    show -r (Fin.rev i) < -r (Fin.rev j)
    linarith) (fun i => by
    show |-r (Fin.rev i)| ≤ (N : ℚ)
    rw [abs_neg]
    exact hN _)
  refine ⟨Fin.rev i, ?_⟩
  simp only [Fin.rev_succ, Fin.rev_castSucc] at hi
  rw [dist_comm]
  exact hi

/-- **Oscillation just right of any point is small** (from the chain bounds). -/
theorem right_small {a : ℚ → E} (hK : ∀ N m : ℕ, ∃ K : ℕ, ChainBound a (1 / ((m : ℝ) + 1)) N K)
    (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r r' : ℚ, s < r → (r : ℝ) < s + δ → s < r' → (r' : ℝ) < s + δ →
      dist (a r) (a r') < ε := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge (|s| + 1)
  obtain ⟨K, hK⟩ := hK N m
  have chain : ∀ k : ℕ, ∀ u : ℝ, s < u → ∃ r : Fin (k + 1) → ℚ, StrictMono r ∧
      (∀ i, s < r i ∧ (r i : ℝ) < u) ∧
        ∀ i : Fin k, ε / 3 < dist (a (r i.succ)) (a (r i.castSucc)) := by
    intro k
    induction k with
    | zero =>
      intro u hu
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu
      refine ⟨fun _ => q, fun i j hij => ?_, fun _ => ⟨hq1, hq2⟩, fun i => i.elim0⟩
      exact absurd hij (by
        have := i.isLt
        have := j.isLt
        rw [Fin.lt_iff_val_lt_val]
        omega)
    | succ k ih =>
      intro u hu
      obtain ⟨r, hr, hb, hd⟩ := ih u hu
      obtain ⟨x, y, hx1, hx2, hy1, hy2, hxy⟩ := hcon ((r 0 : ℝ) - s) (by linarith [(hb 0).1])
      have hfar : ε / 3 < dist (a (r 0)) (a x) ∨ ε / 3 < dist (a (r 0)) (a y) := by
        by_contra h
        push_neg at h
        obtain ⟨h1, h2⟩ := h
        have := dist_triangle_left (a x) (a y) (a (r 0))
        linarith
      have hmk : ∀ z : ℚ, s < z → (z : ℝ) < r 0 → ε / 3 < dist (a (r 0)) (a z) →
          ∃ r' : Fin (k + 1 + 1) → ℚ, StrictMono r' ∧ (∀ i, s < r' i ∧ (r' i : ℝ) < u) ∧
            ∀ i : Fin (k + 1), ε / 3 < dist (a (r' i.succ)) (a (r' i.castSucc)) := by
        intro z hz1 hz2 hz3
        refine ⟨Fin.cons z r, Fin.strictMono_iff_lt_succ.2 fun i => ?_, fun i => ?_,
          fun i => ?_⟩
        · refine Fin.cases ?_ (fun j => ?_) i
          · show z < r 0
            exact_mod_cast hz2
          · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
            exact hr (Fin.castSucc_lt_succ (i := j))
        · refine Fin.cases ⟨hz1, lt_trans hz2 (hb 0).2⟩ (fun j => ?_) i
          rw [Fin.cons_succ]
          exact hb j
        · refine Fin.cases ?_ (fun j => ?_) i
          · simp only [Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero]
            exact hz3
          · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
            exact hd j
      rcases hfar with h | h
      · exact hmk x hx1 (by linarith) h
      · exact hmk y hy1 (by linarith) h
  obtain ⟨r, hr, hb, hd⟩ := chain K (s + 1) (by linarith)
  obtain ⟨i, hi⟩ := hK r hr (fun i => by
    have h1 := (hb i).1
    have h2 := (hb i).2
    have hs := le_abs_self s
    have hs' := neg_abs_le s
    rw [abs_le]
    constructor
    · have : (-(N : ℝ)) ≤ r i := by linarith
      exact_mod_cast this
    · have : (r i : ℝ) ≤ N := by linarith
      exact_mod_cast this)
  linarith [hd i]

/-- **Oscillation just left of any point is small**, by time reversal. -/
theorem left_small {a : ℚ → E} (hK : ∀ N m : ℕ, ∃ K : ℕ, ChainBound a (1 / ((m : ℝ) + 1)) N K)
    (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r r' : ℚ, s - δ < r → (r : ℝ) < s → s - δ < r' → (r' : ℝ) < s →
      dist (a r) (a r') < ε := by
  have hK' : ∀ N m : ℕ, ∃ K : ℕ, ChainBound (fun q => a (-q)) (1 / ((m : ℝ) + 1)) N K :=
    fun N m => (hK N m).imp fun _ h => chainBound_neg h
  obtain ⟨δ, hδ, h⟩ := right_small hK' (-s) hε
  refine ⟨δ, hδ, fun r r' h1 h2 h3 h4 => ?_⟩
  have := h (-r) (-r') (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith)
  simpa only [neg_neg] using this

/-- The rationals approaching `s` from the right. -/
abbrev rightF (s : ℝ) : Filter ℚ := comap (fun q : ℚ => (q : ℝ)) (𝓝[>] s)

/-- The rationals approaching `s` from the left. -/
abbrev leftF (s : ℝ) : Filter ℚ := comap (fun q : ℚ => (q : ℝ)) (𝓝[<] s)

theorem comap_nhdsGT_neBot (s : ℝ) : (rightF s).NeBot := by
  refine comap_neBot fun t ht => ?_
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < u from hu)
  exact ⟨q, hsub ⟨hq1, hq2⟩⟩

theorem comap_nhdsLT_neBot (s : ℝ) : (leftF s).NeBot := by
  refine comap_neBot fun t ht => ?_
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 ht
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < s from hu)
  exact ⟨q, hsub ⟨hq1, hq2⟩⟩

theorem exists_tendsto_of_small [CompleteSpace E] {a : ℚ → E} {F : Filter ℚ} [F.NeBot]
    (h : ∀ ε > 0, ∃ t ∈ F, ∀ r ∈ t, ∀ r' ∈ t, dist (a r) (a r') < ε) :
    ∃ z, Tendsto a F (𝓝 z) := by
  have hc : Cauchy (map a F) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨t, ht, hsm⟩ := h ε hε
    refine ⟨a '' t, mem_map.2 (mem_of_superset ht (subset_preimage_image _ _)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hsm x hx y hy
  exact CompleteSpace.complete hc

theorem ball_of_tendsto_right {a : ℚ → E} {s : ℝ} {z : E}
    (h : Tendsto a (rightF s) (𝓝 z)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℚ, s < r → (r : ℝ) < s + δ → dist (a r) z < ε := by
  obtain ⟨t, ht, hsub⟩ := mem_comap.1 (h (Metric.ball_mem_nhds z hε))
  obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht
  refine ⟨u - s, sub_pos.2 hu, fun r h1 h2 => ?_⟩
  exact Metric.mem_ball.1 (hsub (hIoo ⟨h1, by linarith⟩))

theorem ball_of_tendsto_left {a : ℚ → E} {s : ℝ} {z : E}
    (h : Tendsto a (leftF s) (𝓝 z)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℚ, s - δ < r → (r : ℝ) < s → dist (a r) z < ε := by
  obtain ⟨t, ht, hsub⟩ := mem_comap.1 (h (Metric.ball_mem_nhds z hε))
  obtain ⟨u, hu, hIoo⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 ht
  refine ⟨s - u, sub_pos.2 hu, fun r h1 h2 => ?_⟩
  exact Metric.mem_ball.1 (hsub (hIoo ⟨by linarith, h2⟩))

/-- **The criterion gives a càdlàg extension** (complete state space). -/
theorem exists_cadlag_of_ratCadlag [CompleteSpace E] [T2Space E] {a : ℚ → E} (ha : RatCadlag a) :
    ∃ Z : ℝ → E, IsCadlag Z ∧ ∀ q : ℚ, Z q = a q := by
  have : Nonempty E := ⟨a 0⟩
  have hlimr : ∀ s, ∃ z, Tendsto a (rightF s) (𝓝 z) := by
    intro s
    have := comap_nhdsGT_neBot s
    refine exists_tendsto_of_small fun ε hε => ?_
    obtain ⟨δ, hδ, hsm⟩ := right_small ha.2 s hε
    refine ⟨(fun q : ℚ => (q : ℝ)) ⁻¹' Ioo s (s + δ),
      preimage_mem_comap (Ioo_mem_nhdsGT (by linarith)), fun r hr r' hr' => ?_⟩
    exact hsm r r' hr.1 hr.2 hr'.1 hr'.2
  have hliml : ∀ s, ∃ z, Tendsto a (leftF s) (𝓝 z) := by
    intro s
    have := comap_nhdsLT_neBot s
    refine exists_tendsto_of_small fun ε hε => ?_
    obtain ⟨δ, hδ, hsm⟩ := left_small ha.2 s hε
    refine ⟨(fun q : ℚ => (q : ℝ)) ⁻¹' Ioo (s - δ) s,
      preimage_mem_comap (Ioo_mem_nhdsLT (by linarith)), fun r hr r' hr' => ?_⟩
    exact hsm r r' hr.1 hr.2 hr'.1 hr'.2
  let Z : ℝ → E := fun s => limUnder (rightF s) a
  have hZ : ∀ s, Tendsto a (rightF s) (𝓝 (Z s)) := fun s => tendsto_nhds_limUnder (hlimr s)
  -- values at a later point are controlled by the readings just right of it
  have hctrl : ∀ (t b : ℝ) (z : E) (c : ℝ), t < b →
      (∀ r : ℚ, t < r → (r : ℝ) < b → dist (a r) z < c) → dist (Z t) z ≤ c := by
    intro t b z c htb hbd
    have := comap_nhdsGT_neBot t
    have hconv : Tendsto (fun r => dist (a r) z) (rightF t) (𝓝 (dist (Z t) z)) :=
      (hZ t).dist tendsto_const_nhds
    refine le_of_tendsto hconv ?_
    have hmem : (fun q : ℚ => (q : ℝ)) ⁻¹' Ioo t b ∈ rightF t :=
      preimage_mem_comap (Ioo_mem_nhdsGT htb)
    filter_upwards [hmem] with r hr
    exact (hbd r hr.1 hr.2).le
  refine ⟨Z, ⟨fun s => ?_, fun s => ?_⟩, fun q => ?_⟩
  · -- right-continuity
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hb⟩ := ball_of_tendsto_right (hZ s) (show 0 < ε / 2 by positivity)
    refine ⟨δ, hδ, fun {t} ht hts => ?_⟩
    have hst : s < t := ht
    have htδ : t < s + δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hst)] at hts
      linarith
    have := hctrl t (s + δ) (Z s) (ε / 2) htδ fun r h1 h2 =>
      hb r (lt_trans hst h1) h2
    linarith
  · -- left limits
    obtain ⟨l, hl⟩ := hliml s
    refine ⟨l, Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := ball_of_tendsto_left hl (show 0 < ε / 2 by positivity)
    refine ⟨δ, hδ, fun {t} ht hts => ?_⟩
    have hts' : t < s := ht
    have htδ : s - δ < t := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.2 hts')] at hts
      linarith
    have := hctrl t s l (ε / 2) hts' fun r h1 h2 => hb r (lt_trans htδ h1) h2
    linarith
  · -- the extension agrees with the readings at the rationals
    have := comap_nhdsGT_neBot (q : ℝ)
    refine tendsto_nhds_unique (hZ q) ?_
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨j, hj⟩ := ha.1 q m
    have hmem : (fun q : ℚ => (q : ℝ)) ⁻¹' Ioo (q : ℝ) ((q : ℝ) + 1 / ((j : ℝ) + 1)) ∈ rightF q :=
      preimage_mem_comap (Ioo_mem_nhdsGT (by
        have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        linarith))
    filter_upwards [hmem] with r hr
    have h1 : q < r := by
      have h : (q : ℝ) < r := hr.1
      exact_mod_cast h
    have h2 : r < q + 1 / ((j : ℚ) + 1) := by
      have h : (r : ℝ) < q + 1 / ((j : ℝ) + 1) := hr.2
      have e : ((q + 1 / ((j : ℚ) + 1) : ℚ) : ℝ) = (q : ℝ) + 1 / ((j : ℝ) + 1) := by
        push_cast
        ring
      exact (Rat.cast_lt (K := ℝ)).1 (by rw [e]; exact h)
    exact lt_trans (hj r h1 h2) hm

end ReflectedGMS.RatShiftBridgeCadlag
