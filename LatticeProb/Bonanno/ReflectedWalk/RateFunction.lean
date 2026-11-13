/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.RateFunction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Coupling
import LatticeProb.Bonanno.ReflectedWalk.Recurrence
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Data.Finsupp.Interval
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The rate function `w*` and Lemma 3.5 (Gwynne–Sung, arXiv:2506.18827, Section 3.3)

Section 3.3 fixes a rate function `w : VG → (0,∞)` and attaches to the discrete-time walk
`Y : Ξ → VG` of (3.13) the holding times `T_ξ ~ Exponential(w(Y_ξ))`, conditionally
independent given the paths.  **Lemma 3.5** asserts the existence of `w* : VG → (0,∞)` such
that whenever `w ≥ w*` off a finite set, for every starting point `z`, `P_z`-a.s.

  `∑_{ξ ∈ Ξ} T_ξ = ∞`  and  `∑_{ξ ∈ Ξ, ξ ≤ η} T_ξ < ∞` for every `η ∈ Ξ`.   (3.16)

This is the keystone of the existence half of Theorem 1.6: it is what makes the continuous-time
walk (3.26) reach `∞` in finite time and return.  **Lemma 3.6** (the corollary) is the
dominated-convergence consequence (3.23).

## The model

Following `IndexSet.lean`, the holding times are realised as `T_a := E_a / w(Y_a)` for an
i.i.d. `Exponential(1)` family `E : (ℕ →₀ ℕ) → ℝ` indexed by the fixed countable address space
and independent of the paths:

* `expFamily := Measure.infinitePi (fun _ => expMeasure 1)` is the law of `E`;
* the sample space is `(ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)` with the product law
  `Exhaustion.jointLaw hG n₀ z := (E.coupling hG n₀ z).prod expFamily` — the paper's `P_z`
  (base level `n₀ = n_z`) extended by the exponential clocks;
* the conclusion (3.16) for one sample is `IndexSet.HoldingTimesSummable Gs ω w e`.

`IndexSet.holdingTimesSummable_of` reduces (3.16), deterministically in the sample, to

* **(i)** `∑' k, holding (addr 0 k) = ⊤` — divergence of the level-`0` holding times, and
* **(ii)** `∀ K, ∑' n, layerTime (n+1) (addr 0 K) < ⊤` — for every level-`0` time `K`, the
  times spent before `[(0,K)]` in the layers `G_{n_z+n+1} \ G_{n_z+n}` are summable.

## Proof

**Step 0, (i)** (`coupling_prod_ae_tsum_holding_addr_zero_eq_top`).  By recurrence of the
level-`0` chain (`Exhaustion.chainLaw_ae_exists_gt_eq`, Remark 3.1) the set
`K = {k : Y⁰_k = z}` is a.s. infinite, and along `K` the holding times are `E_{[(0,k)]} / w(z)`.
For a fixed path this is a countable sum of i.i.d. exponentials: the events
`{E_{[(0,k)]} > 1}`, `k ∈ K`, are independent (`iIndepFun_eval_expFamily`) with divergent
total mass, so by the second Borel–Cantelli lemma (`ProbabilityTheory.measure_limsup_eq_one`)
infinitely many of them occur and the sum is `∞` (`expFamily_ae_tsum_div_eq_top`).  Fubini
(`Measure.ae_prod_iff_ae_ae`) turns the path-by-path statement into a joint a.s. statement.

**Step 2, the rates** (`IndexSet.exists_layer_threshold`).  Fix the level offset `n`, the
level-`0` time `K`, and `ε, δ > 0`.  Since `J^{0,n+1}_K` is a finite (measurable) time, there
is `N` with `P(J^{0,n+1}_K > N) ≤ δ/2`.  On `{J^{0,n+1}_K ≤ N}` every address contributing to
`layerTime (n+1) [(0,K)]` is `[(n+1, j)]` with `j ≤ N` (by (3.14)), and all such addresses lie
in the *finite, deterministic* box `Finset.Icc 0 (bnd (n+1) N)` (`addr_le_bnd`): so, if
`w ≥ C` on the layer, `layerTime ≤ ∑_{a ∈ box} E_a / C`.  A union bound over the box and the
tail of the exponential law give `P(layerTime > ε) ≤ δ` once `C` is large.  This is the
paper's "`S_n → 0` in distribution as `min w → ∞`", made quantitative without computing the
law of the excursion, without any measurability of the random address `ω ↦ addr ω (n+1) j`,
and without the strong Markov reduction to `η₁` of the paper's Step 1: stating (ii) for every
`K` and choosing the constants uniformly over the finitely many `K ≤ n` at each layer makes
that reduction unnecessary.

**The function `w*`** (`Exhaustion.rateFunction`).  For paper level `m ≥ 1` the layer
`G_m \ G_{m-1}` is `layer (levelSets n₀) (n+1)` with `n₀ + n + 1 = m`, for each base level
`n₀ < m`.  `layerConst n₀ z n K` is the threshold of Step 2 for `ε = δ = 2⁻ⁿ`, and
`layerBound m` is the sum of `layerConst n₀ z (m-n₀-1) K` over the finitely many `n₀ < m`,
`z ∈ G_{n₀}`, `K < m - n₀` — the paper's `C_m = max_{z ∈ G_m} C_m(z)` (3.21), with a sum in
place of the max so that each term is dominated.  Finally `w*(x) := max 1 (layerBound (n_x))`
where `n_x = min{m : x ∈ G_m}` (`Exhaustion.nz`), so `x ∈ G_m \ G_{m-1}` forces `n_x = m`.

**Step 3, (ii)** (`rateFunction_ae_tsum_layerTime_lt_top`).  If `w ≥ w*` off a finite set
`F ⊆ G_M`, then for `n ≥ max K M` the rate `w` dominates `layerConst n₀ z n K` on the whole
layer `n+1`, so `P(layerTime (n+1) [(0,K)] > 2⁻ⁿ) ≤ 2⁻ⁿ`; the first Borel–Cantelli lemma
(`MeasureTheory.ae_eventually_notMem`, (3.22)) gives a.s. `layerTime (n+1) ≤ 2⁻ⁿ` eventually,
and each `layerTime (n+1) [(0,K)]` is a finite sum (`layerTime_succ_addr_zero_lt_top`), so the
series converges.

**Lemma 3.6** (`IndexSet.tendsto_outsideTime`) is deterministic given (3.16): the time spent
outside `G_n` before `η` is a tail of the convergent series `τ_η = ∑_m layerTime m η`.

## The `w*` discrepancy

The printed Theorem 1.6 requires `w(x) ≥ w*(x)` for **all** `x ∈ VG`; Lemma 3.5 and the
existence proof only use it for all but finitely many `x`.  Lemma 3.5 is proved here in the
paper's cofinite form (`exists_rateFunction`, hypothesis `∀ᶠ x in cofinite, w* x ≤ w x`,
equivalently `{x | w x < w* x}.Finite`), which is the stronger statement; the `∀ x` form
consumed by `Theorem16Statement` is the trivial specialisation `exists_rateFunction_forall`.

## Conventions

`V` is countable with measurable singletons, never locally finite; `B₁Gₙ` may be infinite.
The base level `n₀` is arbitrary subject to `z ∈ VG_{n₀}` (the paper's `P_z` is `n₀ = n_z`,
`Exhaustion.Pz`); `w*` does not depend on `z` or `n₀`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace ReflectedWalk

/-! ### The i.i.d. `Exponential(1)` family `E : Ξ₀ → ℝ` -/

/-- `Exponential(1)` is a probability measure. -/
instance instIsProbabilityMeasureExpMeasureOne : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The law of the unit holding times: an i.i.d. `Exponential(1)` family indexed by the
address space `ℕ →₀ ℕ` (Section 3.3, "conditionally independent … exponential"). -/
noncomputable def expFamily : Measure ((ℕ →₀ ℕ) → ℝ) :=
  Measure.infinitePi fun _ : ℕ →₀ ℕ => expMeasure 1

instance expFamily_isProbabilityMeasure : IsProbabilityMeasure expFamily := by
  unfold expFamily
  infer_instance

/-- Each coordinate of the family has law `Exponential(1)`. -/
lemma expFamily_eval_apply (a : ℕ →₀ ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    expFamily ((fun e : (ℕ →₀ ℕ) → ℝ => e a) ⁻¹' s) = expMeasure 1 s := by
  rw [← Measure.map_apply (measurable_pi_apply a) hs, expFamily, Measure.infinitePi_map_eval]

/-- The coordinates of the family are independent. -/
lemma iIndepFun_eval_expFamily :
    iIndepFun (fun (a : ℕ →₀ ℕ) (e : (ℕ →₀ ℕ) → ℝ) => e a) expFamily := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun a => measurable_pi_apply a]
  simp only [expFamily, Measure.infinitePi_map_eval]
  exact Measure.map_id

/-- `P(Exponential(1) > 1) = e⁻¹ ≠ 0`. -/
lemma expMeasure_one_Ioi_one_ne_zero : expMeasure 1 (Set.Ioi (1 : ℝ)) ≠ 0 := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq one_pos]
  simp only [zero_le_one, ite_true, one_mul]
  refine (tsub_pos_iff_lt.mpr ?_).ne'
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by linarith [Real.exp_pos (-1 : ℝ)])

/-- The tail of `Exponential(1)` vanishes at infinity (continuity from above). -/
lemma expMeasure_one_tendsto_Ioi :
    Tendsto (fun m : ℕ => expMeasure 1 (Set.Ioi (m : ℝ))) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := expMeasure 1) (s := fun m : ℕ => Set.Ioi (m : ℝ))
    (fun _ => measurableSet_Ioi.nullMeasurableSet)
    (fun _ _ hmm' => Set.Ioi_subset_Ioi (Nat.cast_le.mpr hmm')) ⟨0, measure_ne_top _ _⟩
  have he : ⋂ m : ℕ, Set.Ioi (m : ℝ) = ∅ := Set.iInter_eq_empty_iff.mpr fun x => by
    obtain ⟨m, hm⟩ := exists_nat_ge x
    exact ⟨m, not_lt.mpr hm⟩
  rw [he, measure_empty] at h
  exact h

/-- `limsup` of a sequence of measurable sets is measurable. -/
lemma measurableSet_limsup_atTop {α : Type*} [MeasurableSpace α] {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) : MeasurableSet (limsup s atTop) := by
  rw [limsup_eq_iInf_iSup_of_nat]
  exact MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i

/-- An a.s. property of the first coordinate transfers to a product with a probability
measure. -/
lemma ae_prod_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν] {q : α → Prop} (h : ∀ᵐ x ∂μ, q x) :
    ∀ᵐ p ∂μ.prod ν, q p.1 := by
  have h' : ∀ᵐ x ∂(μ.prod ν).map Prod.fst, q x := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact h
  exact ae_of_ae_map measurable_fst.aemeasurable h'

/-- Comparison of rescaled holding times: a larger rate gives a smaller holding time, in
`[0,∞]` (so no sign condition on `x` is needed). -/
lemma ofReal_div_le_ofReal_div {x c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    ENNReal.ofReal (x / d) ≤ ENNReal.ofReal (x / c) := by
  rw [ENNReal.ofReal_div_of_pos (lt_of_lt_of_le hc hcd), ENNReal.ofReal_div_of_pos hc]
  exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hcd) _

/-! ### Step 0: a countable sum of i.i.d. exponentials along an infinite index set diverges

This is the one genuinely new probabilistic fact of Lemma 3.5 (p. 21, "`∑_j T_{[(n,j)]}`
stochastically dominates a countable sum of `exponential(w(x))` random variables, hence is
a.s. infinite"), proved by the second Borel–Cantelli lemma on the events `{E_{[(0,k)]} > 1}`. -/

/-- **Divergence of a countable sum of i.i.d. exponentials.**  For an infinite set `K ⊆ ℕ` and
rates `g` bounded by `D` on `K`, `∑_k E_{[(0,k)]} / g(k) = ∞` almost surely. -/
theorem expFamily_ae_tsum_div_eq_top {K : Set ℕ} (hK : K.Infinite) (g : ℕ → ℝ) {D : ℝ}
    (hD : 0 < D) (hg : ∀ k ∈ K, 0 < g k ∧ g k ≤ D) :
    ∀ᵐ e ∂expFamily, ∑' k, ENNReal.ofReal (e (Finsupp.single 0 k) / g k) = ⊤ := by
  classical
  let T : ℕ → Set ℝ := fun k => {x | k ∈ K ∧ 1 < x}
  have hTm : ∀ k, MeasurableSet (T k) := fun k => by
    have : T k = {_x : ℝ | k ∈ K} ∩ Set.Ioi 1 := by
      ext x
      simp [T]
    rw [this]
    exact (MeasurableSet.const _).inter measurableSet_Ioi
  let s : ℕ → Set ((ℕ →₀ ℕ) → ℝ) :=
    fun k => (fun e : (ℕ →₀ ℕ) → ℝ => e (Finsupp.single 0 k)) ⁻¹' T k
  have hsm : ∀ k, MeasurableSet (s k) := fun k => measurable_pi_apply _ (hTm k)
  have hind : iIndepSet s expFamily := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact (iIndepFun_eval_expFamily.precomp
      (Finsupp.single_injective 0)).measure_inter_preimage_eq_mul S (fun k _ => hTm k)
  have hsum : ∑' k, expFamily (s k) = ⊤ := by
    have := hK.to_subtype
    apply top_le_iff.mp
    calc (⊤ : ℝ≥0∞) = ∑' k, K.indicator (fun _ => expMeasure 1 (Set.Ioi (1 : ℝ))) k := by
          rw [← tsum_subtype]
          exact (ENNReal.tsum_const_eq_top_of_ne_zero expMeasure_one_Ioi_one_ne_zero).symm
      _ ≤ ∑' k, expFamily (s k) := ENNReal.tsum_le_tsum fun k => ?_
    by_cases hk : k ∈ K
    · rw [Set.indicator_of_mem hk]
      have hT : T k = Set.Ioi 1 := by
        ext x
        simp [T, hk]
      show expMeasure 1 (Set.Ioi 1) ≤
        expFamily ((fun e : (ℕ →₀ ℕ) → ℝ => e (Finsupp.single 0 k)) ⁻¹' T k)
      rw [expFamily_eval_apply _ (hTm k), hT]
    · rw [Set.indicator_of_notMem hk]
      exact zero_le
  have h1 := measure_limsup_eq_one hsm hind hsum
  have h2 : ∀ᵐ e ∂expFamily, e ∈ limsup s atTop := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (measurableSet_limsup_atTop hsm)).mpr h1
  filter_upwards [h2] with e he
  rw [mem_limsup_iff_frequently_mem] at he
  have hinf : {k | e ∈ s k}.Infinite := Nat.frequently_atTop_iff_infinite.mp he
  have := hinf.to_subtype
  apply top_le_iff.mp
  calc (⊤ : ℝ≥0∞) = ∑' k, {k | e ∈ s k}.indicator (fun _ => ENNReal.ofReal (1 / D)) k := by
        rw [← tsum_subtype]
        exact (ENNReal.tsum_const_eq_top_of_ne_zero
          (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hD)).ne').symm
    _ ≤ ∑' k, ENNReal.ofReal (e (Finsupp.single 0 k) / g k) := ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : e ∈ s k
  · rw [Set.indicator_of_mem (show k ∈ {k | e ∈ s k} from hk)]
    obtain ⟨hkK, h1e⟩ : k ∈ K ∧ 1 < e (Finsupp.single 0 k) := hk
    obtain ⟨hg0, hgD⟩ := hg k hkK
    apply ENNReal.ofReal_le_ofReal
    calc 1 / D ≤ 1 / g k := one_div_le_one_div_of_le hg0 hgD
      _ ≤ e (Finsupp.single 0 k) / g k := div_le_div_of_nonneg_right h1e.le hg0.le
  · rw [Set.indicator_of_notMem (show k ∉ {k | e ∈ s k} from hk)]
    exact zero_le

namespace IndexSet

variable {V : Type*} (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)

/-! ### Deterministic bounds on addresses and on the layer times -/

/-- Every coordinate of the address of `(n, j)` is at most `j`. -/
lemma addr_apply_le (n j i : ℕ) : addr Gs Y n j i ≤ j := by
  induction n generalizing j with
  | zero =>
    rw [addr_zero, Finsupp.single_apply]
    split_ifs <;> omega
  | succ n ih =>
    rw [addr_succ, Finsupp.add_apply]
    have hk : coarsenPred (Gs n) (Y (n + 1)) j ≤ j :=
      le_trans (self_le_coarsen (Gs n) (Y (n + 1)) _) (coarsen_coarsenPred_le (Gs n) (Y (n + 1)) j)
    by_cases hi : n + 1 = i
    · subst hi
      rw [addr_apply_of_lt Gs Y (Nat.lt_succ_self n), Finsupp.single_eq_same, Nat.zero_add]
      exact Nat.sub_le _ _
    · rw [Finsupp.single_apply, ite_eq_right hi, Nat.add_zero]
      exact le_trans (ih _) hk

/-- The bounding address: `N` on the coordinates `≤ n`, `0` beyond.  Every address of a pair
`(n', j)` with `n' ≤ n`, `j ≤ N` lies below it. -/
noncomputable def bnd (n N : ℕ) : ℕ →₀ ℕ := ∑ i ∈ Finset.range (n + 1), Finsupp.single i N

lemma bnd_apply (n N i : ℕ) : bnd n N i = if i ≤ n then N else 0 := by
  simp [bnd, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The addresses of level-`n` pairs with time `≤ N` lie in the box below `bnd n N`. -/
lemma addr_le_bnd {n j N : ℕ} (hj : j ≤ N) : addr Gs Y n j ≤ bnd n N := by
  rw [Finsupp.le_def]
  intro i
  rw [bnd_apply]
  split_ifs with hi
  · exact le_trans (addr_apply_le Gs Y n j i) hj
  · rw [addr_apply_of_lt Gs Y (not_le.mp hi)]

variable (w : V → ℝ) (E : (ℕ →₀ ℕ) → ℝ)

/-- Under consistency, the time spent in layer `n+1` before `[(0,K)]` is a finite sum over the
classes `[(n+1, j)]`, `j < J^{0,n+1}_K` (by (3.14), every class with `Y_ξ ∈ G_{n+1}` has a
level-`(n+1)` representative, and `[(0,K)] = [(n+1, J^{0,n+1}_K)]`). -/
lemma layerTime_succ_addr_zero_eq (h : Consistent Gs Y) (hG : Monotone Gs) (n K : ℕ) :
    layerTime Gs Y w E (n + 1) (addr Gs Y 0 K) =
      ∑ a ∈ (Finset.range (J Gs Y 0 (n + 1) K)).image (addr Gs Y (n + 1)),
        (below Gs Y (addr Gs Y 0 K) ∩ {a | Yxi Gs Y a ∈ layer Gs (n + 1)}).indicator
          (holding Gs Y w E) a := by
  unfold layerTime
  apply tsum_eq_sum
  intro a ha
  apply Set.indicator_of_notMem
  rintro ⟨⟨hreal, hlt⟩, hmem⟩
  obtain ⟨j, rfl⟩ := h.exists_addr_eq_of_mem Gs Y hG hreal (layer_subset Gs (n + 1) hmem)
  apply ha
  have e := addr_J Gs Y 0 (n + 1) K
  rw [Nat.zero_add] at e
  rw [← e] at hlt
  exact Finset.mem_image.mpr
    ⟨j, Finset.mem_range.mpr ((addr_lt_addr_iff Gs Y).mp hlt), rfl⟩

/-- Each `layerTime (n+1) [(0,K)]` is finite, being a finite sum of finite terms. -/
lemma layerTime_succ_addr_zero_lt_top (h : Consistent Gs Y) (hG : Monotone Gs) (n K : ℕ) :
    layerTime Gs Y w E (n + 1) (addr Gs Y 0 K) < ⊤ := by
  rw [layerTime_succ_addr_zero_eq Gs Y w E h hG n K]
  exact ENNReal.sum_lt_top.mpr fun a _ =>
    lt_of_le_of_lt (Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le))
      (lt_top_iff_ne_top.mpr (holding_ne_top Gs Y w E a))

/-- **The key deterministic bound** (Step 2): if `J^{0,n+1}_K ≤ N` and the rate is at least
`C > 0` on the layer `G_{n+1} \ G_n`, then the time spent in that layer before `[(0,K)]` is at
most `∑_{a ∈ box} E_a / C` over the finite, deterministic box `Icc 0 (bnd (n+1) N)`. -/
lemma layerTime_succ_addr_zero_le (h : Consistent Gs Y) (hG : Monotone Gs) {n K N : ℕ}
    (hJ : J Gs Y 0 (n + 1) K ≤ N) {C : ℝ} (hC : 0 < C)
    (hw : ∀ x ∈ layer Gs (n + 1), C ≤ w x) :
    layerTime Gs Y w E (n + 1) (addr Gs Y 0 K) ≤
      ∑ a ∈ Finset.Icc (0 : ℕ →₀ ℕ) (bnd (n + 1) N), ENNReal.ofReal (E a / C) := by
  rw [layerTime_succ_addr_zero_eq Gs Y w E h hG n K]
  calc ∑ a ∈ (Finset.range (J Gs Y 0 (n + 1) K)).image (addr Gs Y (n + 1)),
        (below Gs Y (addr Gs Y 0 K) ∩ {a | Yxi Gs Y a ∈ layer Gs (n + 1)}).indicator
          (holding Gs Y w E) a
      ≤ ∑ a ∈ (Finset.range (J Gs Y 0 (n + 1) K)).image (addr Gs Y (n + 1)),
          ENNReal.ofReal (E a / C) := by
        apply Finset.sum_le_sum
        intro a _
        refine Set.indicator_apply_le' (fun hmem => ?_) (fun _ => zero_le)
        exact ofReal_div_le_ofReal_div hC (hw _ hmem.2)
    _ ≤ ∑ a ∈ Finset.Icc (0 : ℕ →₀ ℕ) (bnd (n + 1) N), ENNReal.ofReal (E a / C) := by
        apply Finset.sum_le_sum_of_subset
        intro a ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_Icc.mpr ⟨zero_le,
          addr_le_bnd Gs Y (le_trans (Finset.mem_range.mp hj).le hJ)⟩

/-! ### Measurability of the composite coarsening times -/

variable [MeasurableSpace V]

/-- `ω ↦ J^{m,m+d}_K` is a measurable function of the sample. -/
lemma measurable_J (hGs : ∀ i, MeasurableSet (Gs i)) (m d K : ℕ) :
    Measurable fun ω : ℕ → ℕ → V => J Gs ω m d K := by
  induction d with
  | zero => exact measurable_const
  | succ d ih =>
    have h1 : Measurable fun q : (ℕ → ℕ → V) × ℕ =>
        coarsen (Gs (m + d)) (q.1 (m + d + 1)) q.2 :=
      measurable_from_prod_countable_left fun k =>
        (measurable_coarsen (hGs (m + d)) k).comp (measurable_pi_apply (m + d + 1))
    exact h1.comp (measurable_id.prodMk ih)

/-! ### Step 2: choosing the rates -/

omit [MeasurableSpace V] in
/-- If `ε < ∑_{a ∈ B} f a` then some term exceeds `ε / |B|`. -/
lemma exists_lt_of_lt_sum {ι : Type*} {B : Finset ι} {f : ι → ℝ≥0∞} {ε : ℝ≥0∞}
    (hb0 : (B.card : ℝ≥0∞) ≠ 0) (hbtop : (B.card : ℝ≥0∞) ≠ ⊤) (hlt : ε < ∑ a ∈ B, f a) :
    ∃ a ∈ B, ε / B.card < f a := by
  by_contra hcon
  have hall : ∀ a ∈ B, f a ≤ ε / B.card := fun a ha => not_lt.mp fun h => hcon ⟨a, ha, h⟩
  have := Finset.sum_le_card_nsmul B _ _ hall
  rw [nsmul_eq_mul, ENNReal.mul_div_cancel' (fun h => absurd h hb0) (fun h => absurd h hbtop)]
    at this
  exact absurd hlt (not_lt.mpr this)

/-- **Step 2 of Lemma 3.5** (p. 22, (3.19)–(3.20)), for one level offset `n` and one level-`0`
time `K`: for every `ε, δ > 0` there is a threshold `C > 0` such that whenever the rate
function is at least `C` on the layer `G_{n+1} \ G_n`, the time spent in that layer before
`[(0,K)]` exceeds `ε` with probability at most `δ`.  Generic in the law `μ` of the paths,
which only needs to be a.s. consistent. -/
theorem exists_layer_threshold (hGs : ∀ i, MeasurableSet (Gs i)) (hG : Monotone Gs)
    (μ : Measure (ℕ → ℕ → V)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂μ, Consistent Gs ω)
    (n K : ℕ) {ε δ : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ⊤) (hδ : δ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : V → ℝ, (∀ x ∈ layer Gs (n + 1), C ≤ w x) →
      μ.prod expFamily {p | ε < layerTime Gs p.1 w p.2 (n + 1) (addr Gs p.1 0 K)} ≤ δ := by
  classical
  -- Step A: a deterministic time bound `N` on `J^{0,n+1}_K`, up to probability `δ/2`.
  have hJm : Measurable fun ω : ℕ → ℕ → V => J Gs ω 0 (n + 1) K := measurable_J Gs hGs 0 (n + 1) K
  have htend : Tendsto (fun N : ℕ => μ {ω | N < J Gs ω 0 (n + 1) K}) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun N : ℕ => {ω : ℕ → ℕ → V | N < J Gs ω 0 (n + 1) K})
      (fun N => (hJm (MeasurableSet.of_discrete (s := Set.Ioi N))).nullMeasurableSet)
      (fun _ _ hNN' _ hω => lt_of_le_of_lt hNN' hω) ⟨0, measure_ne_top _ _⟩
    have he : ⋂ N : ℕ, {ω : ℕ → ℕ → V | N < J Gs ω 0 (n + 1) K} = ∅ :=
      Set.iInter_eq_empty_iff.mpr fun ω => ⟨J Gs ω 0 (n + 1) K, fun h =>
        lt_irrefl _ (show J Gs ω 0 (n + 1) K < J Gs ω 0 (n + 1) K from h)⟩
    rw [he, measure_empty] at h
    exact h
  obtain ⟨N, hN⟩ := ((tendsto_order.1 htend).2 (δ / 2) (ENNReal.half_pos hδ)).exists
  -- Step B: the finite box of addresses and the threshold `C`.
  set B := Finset.Icc (0 : ℕ →₀ ℕ) (bnd (n + 1) N) with hB
  have hB0 : (0 : ℕ →₀ ℕ) ∈ B := Finset.mem_Icc.mpr ⟨le_rfl, zero_le⟩
  have hb0 : (B.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨0, hB0⟩).ne'
  have hbtop : (B.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set c₀ : ℝ := (ε / B.card).toReal with hc₀
  have hc₀pos : 0 < c₀ :=
    ENNReal.toReal_pos (ENNReal.div_pos_iff.mpr ⟨hε, hbtop⟩).ne' (ENNReal.div_ne_top hε' hb0)
  have hδ' : 0 < δ / 2 / B.card :=
    ENNReal.div_pos_iff.mpr ⟨(ENNReal.half_pos hδ).ne', hbtop⟩
  obtain ⟨m₀, hm₀⟩ := ((tendsto_order.1 expMeasure_one_tendsto_Ioi).2 _ hδ').exists
  set C : ℝ := max 1 ((m₀ : ℝ) / c₀) with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCm : (m₀ : ℝ) ≤ C * c₀ := by
    rw [← div_le_iff₀ hc₀pos]
    exact le_max_right _ _
  refine ⟨C, hCpos, fun w hw => ?_⟩
  -- Step C: the a.e. inclusion of the bad event in `{J > N} ∪ ⋃_{a ∈ B} {E_a > m₀}`.
  have hincl : ∀ᵐ p ∂μ.prod expFamily,
      p ∈ {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) |
          ε < layerTime Gs p.1 w p.2 (n + 1) (addr Gs p.1 0 K)} →
        p ∈ {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | N < J Gs p.1 0 (n + 1) K} ∪
          ⋃ a ∈ B, {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | (m₀ : ℝ) < p.2 a} := by
    filter_upwards [ae_prod_fst (ν := expFamily) hμ] with p hp hlt
    by_cases hJ : N < J Gs p.1 0 (n + 1) K
    · exact Or.inl hJ
    · right
      have hle := layerTime_succ_addr_zero_le Gs p.1 w p.2 hp hG (not_lt.mp hJ) hCpos hw
      obtain ⟨a, haB, ha⟩ := exists_lt_of_lt_sum hb0 hbtop (lt_of_lt_of_le hlt hle)
      refine Set.mem_iUnion₂.mpr ⟨a, haB, ?_⟩
      show (m₀ : ℝ) < p.2 a
      rw [ENNReal.lt_ofReal_iff_toReal_lt (ENNReal.div_ne_top hε' hb0), ← hc₀,
        lt_div_iff₀ hCpos] at ha
      linarith [mul_comm C c₀]
  -- Step D: the union bound.
  calc μ.prod expFamily {p | ε < layerTime Gs p.1 w p.2 (n + 1) (addr Gs p.1 0 K)}
      ≤ μ.prod expFamily ({p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | N < J Gs p.1 0 (n + 1) K} ∪
          ⋃ a ∈ B, {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | (m₀ : ℝ) < p.2 a}) :=
        measure_mono_ae hincl
    _ ≤ μ.prod expFamily {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | N < J Gs p.1 0 (n + 1) K} +
          μ.prod expFamily (⋃ a ∈ B, {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | (m₀ : ℝ) < p.2 a}) :=
        measure_union_le _ _
    _ ≤ δ / 2 + ∑ a ∈ B, δ / 2 / B.card := by
        gcongr
        · have e : {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | N < J Gs p.1 0 (n + 1) K} =
              {ω : ℕ → ℕ → V | N < J Gs ω 0 (n + 1) K} ×ˢ Set.univ := by
            ext p
            simp
          rw [e, Measure.prod_prod, measure_univ, mul_one]
          exact hN.le
        · refine (measure_biUnion_finset_le B _).trans (Finset.sum_le_sum fun a _ => ?_)
          have e : {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) | (m₀ : ℝ) < p.2 a} =
              Set.univ ×ˢ ((fun e : (ℕ →₀ ℕ) → ℝ => e a) ⁻¹' Set.Ioi (m₀ : ℝ)) := by
            ext p
            simp
          rw [e, Measure.prod_prod, measure_univ, one_mul, expFamily_eval_apply _ measurableSet_Ioi]
          exact hm₀.le
    _ = δ / 2 + B.card * (δ / 2 / B.card) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ δ / 2 + δ / 2 := by gcongr; exact ENNReal.mul_div_le
    _ = δ := ENNReal.add_halves δ

omit [MeasurableSpace V] in
/-- A series in `[0,∞]` with finite terms that is eventually dominated by `2⁻ⁿ` converges. -/
lemma tsum_lt_top_of_eventually_le {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n < ⊤) {N : ℕ}
    (h : ∀ n, N ≤ n → f n ≤ (2⁻¹ : ℝ≥0∞) ^ n) : ∑' n, f n < ⊤ := by
  classical
  have hle : ∀ n, f n ≤ (if n < N then f n else 0) + (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    split_ifs with hn
    · exact le_add_right le_rfl
    · rw [zero_add]
      exact h n (not_lt.mp hn)
  calc ∑' n, f n ≤ ∑' n, ((if n < N then f n else 0) + (2⁻¹ : ℝ≥0∞) ^ n) :=
        ENNReal.tsum_le_tsum hle
    _ = ∑' n, (if n < N then f n else 0) + ∑' n, (2⁻¹ : ℝ≥0∞) ^ n := ENNReal.tsum_add
    _ < ⊤ := by
        rw [ENNReal.add_lt_top]
        constructor
        · rw [tsum_eq_sum (s := Finset.range N)
            (fun n hn => ite_eq_right (not_lt.mpr (by simpa using hn)))]
          refine ENNReal.sum_lt_top.mpr fun n _ => ?_
          split_ifs
          · exact hf n
          · exact ENNReal.zero_lt_top
        · rw [ENNReal.tsum_geometric]
          exact ENNReal.inv_lt_top.mpr
            (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two))

/-! ### Lemma 3.6: the time spent outside `G_n` before `η` vanishes as `n → ∞` -/

omit [MeasurableSpace V] in
/-- `∑{T_ξ : ξ ∈ Ξ, ξ ≤ η, Y_ξ ∉ G_n}`, the quantity of (3.23). -/
noncomputable def outsideTime (n : ℕ) (η : ℕ →₀ ℕ) : ℝ≥0∞ :=
  ∑' a, ({a | Realized Gs Y a ∧ toLex a ≤ toLex η} ∩ {a | Yxi Gs Y a ∉ Gs n}).indicator
    (holding Gs Y w E) a

omit [MeasurableSpace V] in
/-- Once `Y_η ∈ G_n`, the time spent outside `G_n` up to `η` is dominated by the tail
`∑_{m > n} layerTime m η` of the layer decomposition of `τ_η` (p. 22, "for each `ξ ∈ Ξ` there
exists `n` such that `Y_ξ ∈ G_n`"). -/
lemma outsideTime_le (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) {n : ℕ} {η : ℕ →₀ ℕ}
    (hη : Yxi Gs Y η ∈ Gs n) :
    outsideTime Gs Y w E n η ≤ ∑' k, layerTime Gs Y w E (k + (n + 1)) η := by
  unfold outsideTime layerTime
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ {a | Realized Gs Y a ∧ toLex a ≤ toLex η} ∩ {a | Yxi Gs Y a ∉ Gs n}
  · rw [Set.indicator_of_mem ha]
    obtain ⟨⟨hreal, hle⟩, hnot⟩ := ha
    have hlt : toLex a < toLex η := lt_of_le_of_ne hle fun h => hnot (by
      rw [toLex_inj.mp h]
      exact hη)
    obtain ⟨m, hm⟩ := exists_mem_layer Gs hcov (Yxi Gs Y a)
    have hmn : n + 1 ≤ m := by
      by_contra hc
      exact hnot (hG (Nat.lt_succ_iff.mp (not_le.mp hc)) (layer_subset Gs m hm))
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hmn
    have hmem : a ∈ below Gs Y η ∩ {a | Yxi Gs Y a ∈ layer Gs (k + (n + 1))} :=
      ⟨⟨hreal, hlt⟩, hm⟩
    calc holding Gs Y w E a
        = (below Gs Y η ∩ {a | Yxi Gs Y a ∈ layer Gs (k + (n + 1))}).indicator
            (holding Gs Y w E) a := (Set.indicator_of_mem hmem (holding Gs Y w E)).symm
      _ ≤ ∑' k, (below Gs Y η ∩ {a | Yxi Gs Y a ∈ layer Gs (k + (n + 1))}).indicator
            (holding Gs Y w E) a :=
          ENNReal.le_tsum (f := fun k => (below Gs Y η ∩
            {a | Yxi Gs Y a ∈ layer Gs (k + (n + 1))}).indicator (holding Gs Y w E) a) k
  · rw [Set.indicator_of_notMem ha]
    exact zero_le

omit [MeasurableSpace V] in
/-- **Lemma 3.6** (Gwynne–Sung, (3.23)), deterministic form: under (3.16), for every `η ∈ Ξ`,
`∑{T_ξ : ξ ≤ η, Y_ξ ∉ G_n} → 0` as `n → ∞`.  The paper invokes dominated convergence; here
the quantity is dominated by a tail of the convergent series `τ_η = ∑_m layerTime m η`
(`tau_eq_tsum_layerTime`). -/
theorem tendsto_outsideTime (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hsum : HoldingTimesSummable Gs Y w E) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) :
    Tendsto (fun n => outsideTime Gs Y w E n η) atTop (𝓝 0) := by
  have hτ : ∑' m, layerTime Gs Y w E m η ≠ ⊤ := by
    rw [← tau_eq_tsum_layerTime Gs Y w E hG hcov η]
    exact (hsum.2 η hη).ne
  have htail : Tendsto (fun n => ∑' k, layerTime Gs Y w E (k + (n + 1)) η) atTop (𝓝 0) :=
    (ENNReal.tendsto_sum_nat_add (fun m => layerTime Gs Y w E m η) hτ).comp
      (tendsto_add_atTop_nat 1)
  obtain ⟨n₀, hn₀⟩ := hcov (Yxi Gs Y η)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop n₀] with n hn
  exact outsideTime_le Gs Y w E hG hcov (hG hn hn₀)

end IndexSet

/-! ### Lemma 3.5 for the coupled chains of an exhaustion -/

namespace ConductanceGraph.Exhaustion

open IndexSet

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)

/-- **The joint law of the paths and the unit holding times**: the coupling `P_z` of Lemma 3.4
(base level `n₀`) extended by the independent i.i.d. `Exponential(1)` family — the probability
space of Section 3.3. -/
noncomputable abbrev jointLaw (n₀ : ℕ) (z : V) :
    Measure ((ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)) :=
  (E.coupling hG n₀ z).prod expFamily

/-- Under the joint law the paths are a.s. consistent, (3.12). -/
theorem jointLaw_ae_consistent (n₀ : ℕ) (z : V) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, Consistent (E.levelSets n₀) p.1 :=
  ae_prod_fst (E.coupling_ae_consistent hG n₀ z)

/-- **Lemma 3.5, Step 0** (p. 21): the level-`0` holding times diverge a.s.  The level-`0`
chain visits `z` infinitely often (Remark 3.1), so the holding-time series dominates a
countable sum of i.i.d. `Exponential(w(z))` variables, which is a.s. infinite. -/
theorem jointLaw_ae_tsum_holding_addr_zero_eq_top (n₀ : ℕ) {z : V} (hz : z ∈ E.Gsub n₀)
    (w : V → ℝ) (hw : ∀ x, 0 < w x) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z,
      ∑' k, holding (E.levelSets n₀) p.1 w p.2 (addr (E.levelSets n₀) p.1 0 k) = ⊤ := by
  have hmeas : MeasurableSet {p : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) |
      ∑' k, holding (E.levelSets n₀) p.1 w p.2 (addr (E.levelSets n₀) p.1 0 k) = ⊤} := by
    refine (Measurable.ennreal_tsum fun k => ?_) (measurableSet_singleton ⊤)
    simp only [addr_zero, holding]
    exact ENNReal.measurable_ofReal.comp (((measurable_pi_apply _).comp measurable_snd).div
      ((measurable_of_countable w).comp
        ((LevelCoupling.measurable_Yxi _ (E.measurableSet_levelSets n₀) _).comp measurable_fst)))
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  filter_upwards [E.coupling_ae_consistent hG n₀ z,
    E.coupling_ae_of_ae hG n₀ z 0 (E.chainLaw_ae_exists_gt_eq hG n₀ hz z)] with ω hcons hrec
  have hK : {k | ω 0 k = z}.Infinite :=
    Set.infinite_of_forall_exists_gt fun N => let ⟨k, hk, h⟩ := hrec N; ⟨k, h, hk⟩
  have h := expFamily_ae_tsum_div_eq_top hK (fun k => w (ω 0 k)) (hw z)
    (fun k hk => by
      have hk' : ω 0 k = z := hk
      rw [hk']
      exact ⟨hw z, le_rfl⟩)
  show ∀ᵐ e ∂expFamily,
    ∑' k, holding (E.levelSets n₀) ω w e (addr (E.levelSets n₀) ω 0 k) = ⊤
  filter_upwards [h] with e he
  simp only [holding, hcons.Yxi_addr]
  exact he

/-! ### The constants of Step 2 and the rate function `w*` -/

/-- **Step 2, existence of `C_n(z)`** ((3.19)–(3.20), for the level-`0` time `K`): with
`ε = δ = 2⁻ⁿ`. -/
theorem exists_layerConst (n₀ : ℕ) (z : V) (n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : V → ℝ, (∀ x ∈ layer (E.levelSets n₀) (n + 1), C ≤ w x) →
      E.jointLaw hG n₀ z {p | (2⁻¹ : ℝ≥0∞) ^ n <
        layerTime (E.levelSets n₀) p.1 w p.2 (n + 1) (addr (E.levelSets n₀) p.1 0 K)} ≤
          (2⁻¹ : ℝ≥0∞) ^ n :=
  exists_layer_threshold (E.levelSets n₀) (E.measurableSet_levelSets n₀) (E.levelSets_mono n₀)
    (E.coupling hG n₀ z) (E.coupling_ae_consistent hG n₀ z) n K
    (pow_ne_zero n (ENNReal.inv_ne_zero.mpr (by simp)))
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero))
    (pow_ne_zero n (ENNReal.inv_ne_zero.mpr (by simp)))

/-- The constant `C_{n₀+n+1}(z)` of (3.19), for the base level `n₀`, the layer offset `n` and
the level-`0` time `K`: a rate threshold on `G_{n₀+n+1} \ G_{n₀+n}` under which
`P_z(layerTime (n+1) [(0,K)] > 2⁻ⁿ) ≤ 2⁻ⁿ`. -/
noncomputable def layerConst (n₀ : ℕ) (z : V) (n K : ℕ) : ℝ :=
  Classical.choose (E.exists_layerConst hG n₀ z n K)

theorem layerConst_pos (n₀ : ℕ) (z : V) (n K : ℕ) : 0 < E.layerConst hG n₀ z n K :=
  (Classical.choose_spec (E.exists_layerConst hG n₀ z n K)).1

/-- (3.20): the defining property of `layerConst`. -/
theorem layerConst_spec (n₀ : ℕ) (z : V) (n K : ℕ) (w : V → ℝ)
    (hw : ∀ x ∈ layer (E.levelSets n₀) (n + 1), E.layerConst hG n₀ z n K ≤ w x) :
    E.jointLaw hG n₀ z {p | (2⁻¹ : ℝ≥0∞) ^ n <
      layerTime (E.levelSets n₀) p.1 w p.2 (n + 1) (addr (E.levelSets n₀) p.1 0 K)} ≤
        (2⁻¹ : ℝ≥0∞) ^ n :=
  (Classical.choose_spec (E.exists_layerConst hG n₀ z n K)).2 w hw

/-- The constant `C_m` of (3.21) for the layer `G_m \ G_{m-1}`: the paper's
`max_{z ∈ G_m} C_m(z)`, taken here over the finitely many base levels `n₀ < m`, starting
points `z ∈ G_{n₀}` and level-`0` times `K < m - n₀` (so that `K ≤ n` where
`m = n₀ + n + 1`), and as a sum of the positive constants rather than a maximum. -/
noncomputable def layerBound (m : ℕ) : ℝ :=
  ∑ n₀ ∈ Finset.range m, ∑ z ∈ E.Gsub n₀, ∑ K ∈ Finset.range (m - n₀),
    E.layerConst hG n₀ z (m - n₀ - 1) K

theorem layerConst_le_layerBound {m n₀ : ℕ} (hn₀ : n₀ < m) {z : V} (hz : z ∈ E.Gsub n₀)
    {K : ℕ} (hK : K < m - n₀) :
    E.layerConst hG n₀ z (m - n₀ - 1) K ≤ E.layerBound hG m := by
  unfold layerBound
  have hpos : ∀ n₀' z' K', 0 ≤ E.layerConst hG n₀' z' (m - n₀' - 1) K' :=
    fun _ _ _ => (E.layerConst_pos hG _ _ _ _).le
  calc E.layerConst hG n₀ z (m - n₀ - 1) K
      ≤ ∑ K' ∈ Finset.range (m - n₀), E.layerConst hG n₀ z (m - n₀ - 1) K' :=
        Finset.single_le_sum (fun K' _ => hpos n₀ z K') (Finset.mem_range.mpr hK)
    _ ≤ ∑ z' ∈ E.Gsub n₀, ∑ K' ∈ Finset.range (m - n₀), E.layerConst hG n₀ z' (m - n₀ - 1) K' :=
        Finset.single_le_sum (fun z' _ => Finset.sum_nonneg fun K' _ => hpos n₀ z' K') hz
    _ ≤ ∑ n₀' ∈ Finset.range m, ∑ z' ∈ E.Gsub n₀', ∑ K' ∈ Finset.range (m - n₀'),
          E.layerConst hG n₀' z' (m - n₀' - 1) K' :=
        Finset.single_le_sum (f := fun n₀' => ∑ z' ∈ E.Gsub n₀', ∑ K' ∈ Finset.range (m - n₀'),
            E.layerConst hG n₀' z' (m - n₀' - 1) K')
          (fun n₀' _ => Finset.sum_nonneg fun z' _ => Finset.sum_nonneg fun K' _ => hpos n₀' z' K')
          (Finset.mem_range.mpr hn₀)

/-- **The rate function `w*` of Lemma 3.5**: `w*(x) := max 1 (C_{n_x})` where
`n_x = min{m : x ∈ VG_m}` is the level of the layer containing `x` and `C_m` is (3.21).  It
depends only on the exhaustion (and the chains), not on the starting point. -/
noncomputable def rateFunction (x : V) : ℝ := max 1 (E.layerBound hG (E.nz x))

theorem rateFunction_pos (x : V) : 0 < E.rateFunction hG x :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- (3.21) ⟹ (3.19): on the layer `G_{n₀+n+1} \ G_{n₀+n}` the rate function dominates every
constant `C_{n₀+n+1}(z)` with `z ∈ G_{n₀}` and `K ≤ n`. -/
theorem layerConst_le_rateFunction {n₀ : ℕ} {z : V} (hz : z ∈ E.Gsub n₀) {n K : ℕ} (hK : K ≤ n)
    {x : V} (hx : x ∈ layer (E.levelSets n₀) (n + 1)) :
    E.layerConst hG n₀ z n K ≤ E.rateFunction hG x := by
  have hx1 : x ∈ E.Gsub (n₀ + n + 1) := hx.1
  have hx2 : x ∉ E.Gsub (n₀ + n) := hx.2
  have hnz : E.nz x = n₀ + n + 1 := by
    apply le_antisymm (E.nz_le hx1)
    by_contra h
    exact hx2 (E.mono (Nat.lt_succ_iff.mp (not_le.mp h)) (E.mem_Gsub_nz x))
  have h := E.layerConst_le_layerBound hG (m := n₀ + n + 1)
    (Nat.lt_succ_of_le (Nat.le_add_right n₀ n)) hz (K := K) (by omega)
  rw [show n₀ + n + 1 - n₀ - 1 = n by omega] at h
  unfold rateFunction
  rw [hnz]
  exact le_trans h (le_max_right _ _)

/-! ### Step 3: Borel–Cantelli, and Lemma 3.5 -/

/-- **Lemma 3.5, Steps 2–3** ((3.20)–(3.22)): if `w ≥ w*` off a finite set, then for every
level-`0` time `K` the times spent before `[(0,K)]` in the layers `G_{n₀+n+1} \ G_{n₀+n}` are
a.s. summable — input (ii) of `IndexSet.holdingTimesSummable_of`. -/
theorem rateFunction_ae_tsum_layerTime_lt_top (w : V → ℝ)
    (hfin : {x | w x < E.rateFunction hG x}.Finite) (n₀ : ℕ) {z : V} (hz : z ∈ E.Gsub n₀) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, ∀ K, ∑' n,
      layerTime (E.levelSets n₀) p.1 w p.2 (n + 1) (addr (E.levelSets n₀) p.1 0 K) < ⊤ := by
  rw [ae_all_iff]
  intro K
  -- the finitely many exceptional vertices lie in some `G_M`
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, w x < E.rateFunction hG x → x ∈ E.Gsub M := by
    obtain ⟨M, hM⟩ := (hfin.image fun x => E.nz x).bddAbove
    exact ⟨M, fun x hx => E.mono (hM (Set.mem_image_of_mem _ hx)) (E.mem_Gsub_nz x)⟩
  have hle : ∀ n, E.jointLaw hG n₀ z (if max K M ≤ n then
      {p | (2⁻¹ : ℝ≥0∞) ^ n <
        layerTime (E.levelSets n₀) p.1 w p.2 (n + 1) (addr (E.levelSets n₀) p.1 0 K)}
      else ∅) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    split_ifs with hn
    · apply E.layerConst_spec hG n₀ z n K w
      intro x hx
      have hK : K ≤ n := le_trans (le_max_left _ _) hn
      have hxF : ¬ w x < E.rateFunction hG x := fun h =>
        hx.2 (E.mono (le_trans (le_max_right K M) (hn.trans (Nat.le_add_left n n₀))) (hM x h))
      exact le_trans (E.layerConst_le_rateFunction hG hz hK hx) (not_lt.mp hxF)
    · rw [measure_empty]
      exact zero_le
  have hsum : ∑' n, E.jointLaw hG n₀ z (if max K M ≤ n then
      {p | (2⁻¹ : ℝ≥0∞) ^ n <
        layerTime (E.levelSets n₀) p.1 w p.2 (n + 1) (addr (E.levelSets n₀) p.1 0 K)}
      else ∅) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr
      (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two)).ne'
  filter_upwards [ae_eventually_notMem hsum, E.jointLaw_ae_consistent hG n₀ z] with p hev hcons
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  refine tsum_lt_top_of_eventually_le
    (fun n => layerTime_succ_addr_zero_lt_top _ _ _ _ hcons (E.levelSets_mono n₀) n K)
    (N := max (max K M) N₁) fun n hn => ?_
  have h := hN₁ n (le_trans (le_max_right _ _) hn)
  rw [ite_eq_left (le_trans (le_max_left _ _) hn)] at h
  exact not_lt.mp h

/-- **Lemma 3.5** (Gwynne–Sung, p. 21), for the rate function `rateFunction` and in the paper's
**cofinite** form: if `w : VG → (0,∞)` satisfies `w(x) ≥ w*(x)` for all but finitely many `x`,
then for every starting point `z` (and every base level `n₀` with `z ∈ VG_{n₀}`, in particular
the paper's `n_z`), almost surely under the joint law of the coupled chains and the holding
times, (3.16) holds: `∑_{ξ ∈ Ξ} T_ξ = ∞` and `∑_{ξ < η} T_ξ < ∞` for every `η ∈ Ξ`. -/
theorem rateFunction_ae_holdingTimesSummable (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (hfin : {x | w x < E.rateFunction hG x}.Finite) (n₀ : ℕ) {z : V} (hz : z ∈ E.Gsub n₀) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, HoldingTimesSummable (E.levelSets n₀) p.1 w p.2 := by
  filter_upwards [E.jointLaw_ae_consistent hG n₀ z,
    E.jointLaw_ae_tsum_holding_addr_zero_eq_top hG n₀ hz w hw,
    E.rateFunction_ae_tsum_layerTime_lt_top hG w hfin n₀ hz] with p hcons h0 h3
  exact holdingTimesSummable_of _ _ _ _ hcons (E.levelSets_mono n₀) (E.exists_mem_levelSets n₀)
    h0 h3

/-- **Lemma 3.5** as stated in the paper (existential form, cofinite hypothesis
`w(x) ≥ w*(x)` for all but finitely many `x`): there is `w* : VG → (0,∞)` such that for every
rate function `w : VG → (0,∞)` with `w ≥ w*` off a finite set and every starting point, (3.16)
holds almost surely. -/
theorem exists_rateFunction :
    ∃ wstar : V → ℝ, (∀ x, 0 < wstar x) ∧
      ∀ w : V → ℝ, (∀ x, 0 < w x) → (∀ᶠ x in cofinite, wstar x ≤ w x) →
        ∀ (n₀ : ℕ) (z : V), z ∈ E.Gsub n₀ →
          ∀ᵐ p ∂E.jointLaw hG n₀ z, HoldingTimesSummable (E.levelSets n₀) p.1 w p.2 :=
  ⟨E.rateFunction hG, E.rateFunction_pos hG, fun w hw hcof n₀ z hz =>
    E.rateFunction_ae_holdingTimesSummable hG w hw
      (by simpa only [eventually_cofinite, not_le] using hcof) n₀ hz⟩

/-- **Lemma 3.5 with the hypothesis of the printed Theorem 1.6** (`w(x) ≥ w*(x)` for **all**
`x`): the trivial specialisation of `exists_rateFunction`, in the form consumed by
`Theorem16Statement`. -/
theorem exists_rateFunction_forall :
    ∃ wstar : V → ℝ, (∀ x, 0 < wstar x) ∧
      ∀ w : V → ℝ, (∀ x, 0 < w x) → (∀ x, wstar x ≤ w x) →
        ∀ (n₀ : ℕ) (z : V), z ∈ E.Gsub n₀ →
          ∀ᵐ p ∂E.jointLaw hG n₀ z, HoldingTimesSummable (E.levelSets n₀) p.1 w p.2 :=
  let ⟨wstar, hpos, h⟩ := E.exists_rateFunction hG
  ⟨wstar, hpos, fun w hw hall => h w hw (Eventually.of_forall hall)⟩

/-- **Lemma 3.5 under the paper's `P_z`** (base level `n_z`): the case `n₀ = n_z` of
`rateFunction_ae_holdingTimesSummable`. -/
theorem Pz_ae_holdingTimesSummable (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (hfin : {x | w x < E.rateFunction hG x}.Finite) (z : V) :
    ∀ᵐ p ∂(E.Pz hG z).prod expFamily, HoldingTimesSummable (E.levelSets (E.nz z)) p.1 w p.2 :=
  E.rateFunction_ae_holdingTimesSummable hG w hw hfin (E.nz z) (E.mem_Gsub_nz z)

/-- **Lemma 3.6** (Gwynne–Sung, (3.23)): almost surely, for each `η ∈ Ξ`,
`lim_{n → ∞} ∑{T_ξ : ξ ∈ Ξ, ξ ≤ η, Y_ξ ∉ G_{n₀+n}} = 0`. -/
theorem rateFunction_ae_tendsto_outsideTime (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (hfin : {x | w x < E.rateFunction hG x}.Finite) (n₀ : ℕ) {z : V} (hz : z ∈ E.Gsub n₀) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, ∀ η, Realized (E.levelSets n₀) p.1 η →
      Tendsto (fun n => outsideTime (E.levelSets n₀) p.1 w p.2 n η) atTop (𝓝 0) := by
  filter_upwards [E.rateFunction_ae_holdingTimesSummable hG w hw hfin n₀ hz] with p hp η hη
  exact tendsto_outsideTime _ _ _ _ (E.levelSets_mono n₀) (E.exists_mem_levelSets n₀) hp hη

end ConductanceGraph.Exhaustion

end ReflectedWalk
