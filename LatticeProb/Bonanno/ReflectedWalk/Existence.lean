/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Existence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Coupling
import LatticeProb.Bonanno.ReflectedWalk.Recurrence
import LatticeProb.Bonanno.ReflectedWalk.RateFunction
import LatticeProb.Bonanno.ReflectedWalk.PathProperties
import LatticeProb.Bonanno.ReflectedWalk.RightContinuityAtInfty
import LatticeProb.Bonanno.ReflectedWalk.Theorem16Statement
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Order.CompleteLattice.Finset

/-!
# The existence half of Theorem 1.6 (Gwynne–Sung, arXiv:2506.18827, Section 3.4)

Section 3.4 of the paper checks that the process `X : [0,∞) → VG ∪ {∞}` of (3.26) satisfies
properties (i)–(vi) of Theorem 1.6.  This file builds the probability space and the process
family of `Theorem16Statement.lean` from the pieces already proved —

* the coupling `P_z` of Lemma 3.4 (`Coupling.lean`) and the i.i.d. `Exponential(1)` unit
  holding times `expFamily` (`RateFunction.lean`), i.e. the joint law
  `E.jointLaw hG (E.nz z) z = P_z ⊗ expFamily` of Section 3.3, under which the holding times
  `T_ξ = E_ξ / w(Y_ξ) ~ Exponential(w(Y_ξ))` are `IndexSet.holding`;
* the clock (3.25), the successor (3.24) and the process (3.26) of `IndexSet.lean`, made a
  stochastic process in `PathProperties.lean` (`PathProperties.process`);
* Lemma 3.5 (`Exhaustion.exists_rateFunction_forall`), properties (i) and (ii)
  (`PathProperties.almostEverywhereDefined`, `PathProperties.rightContinuous`) —

and proves, for the process under every `P_z`, **property (v)** (recurrence), **property
(vi)** (relation to harmonic functions, from Lemma 3.2), **property (iii)** (exponential first
step) and `X_0 = z`, discharges the independence and absolute-continuity inputs of Lemma 3.7,
and assembles the existence half of Theorem 1.6.  The only hypothesis carried is property (iv),
the Markov property.

## The sample space

`Sample V := (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)`: a sample is the family of paths
`Y : level ↦ time ↦ vertex` (level `i` is the paper's `n_z + i`) together with the unit holding
times `E : Ξ₀ → ℝ`.  Under `sampleLaw E hG z := E.jointLaw hG (E.nz z) z` the paths have the
coupled law of Lemma 3.4 started at `z`, and the holding times are independent of the paths —
the paper's "conditional on `{Yⁿ}`, `{T_ξ}` are conditionally independent with
`T_ξ ~ Exponential(w(Y_ξ))`".

## One process for all starting points

`Theorem16Statement.ProcessFamily` has a single process and one measure per starting point,
whereas the paper's construction re-indexes levels from `n_z`.  The process reads the base level
off the sample: `process E w t ω` is `PathProperties.process` computed with
`Gs := VG_{n_{Y⁰₀} + ·}`, where `Y⁰₀` is the starting vertex.  Under `P_z`, `Y⁰₀ = z` almost
surely, so this is the paper's process started at `z`.

## Hypothesis carried, and who discharges it

* Property (iv) — the Markov property (p. 25: from the Markov property of each `Xⁿ`, Lemma 3.8
  and convergence of conditional laws), for every `w > 0` satisfying (3.16) almost surely.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk

namespace Existence

open IndexSet

variable {V : Type u}

/-! ### Deterministic facts about the clock (3.25) and the process (3.26)

Everything in this section is a function of one sample `(Y, E)`; the a.s. inputs are explicit
hypotheses, as in `IndexSet.lean`. -/

section deterministic

variable (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (E : (ℕ →₀ ℕ) → ℝ)

/-- The holding time `T_ξ = E_ξ / w(Y_ξ)` is positive when `E_ξ > 0` and `w > 0`. -/
lemma holding_pos (hw : ∀ x, 0 < w x) {a : ℕ →₀ ℕ} (ha : 0 < E a) :
    0 < holding Gs Y w E a :=
  ENNReal.ofReal_pos.mpr (div_pos ha (hw _))

/-- `X_t = x ∈ VG` forces `t ∈ [τ_η, τ_η̂)` with `Y_η = x` for some `η ∈ Ξ` (from (3.26)). -/
lemma exists_inInterval_of_X_eq_some {t : ℝ≥0} {x : V} (h : X Gs Y w E t = some x) :
    ∃ η, InInterval Gs Y w E η t ∧ Yxi Gs Y η = x := by
  by_cases hx : ∃ η, InInterval Gs Y w E η t
  · rw [X, dite_eq_left hx] at h
    exact ⟨Classical.choose hx, Classical.choose_spec hx, Option.some_injective V h⟩
  · rw [X, dite_eq_right hx] at h
    exact absurd h (by simp)

/-- `J^{m,m+d}_0 = 0`. -/
lemma J_apply_zero (m d : ℕ) : J Gs Y m d 0 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => rw [J_succ, ih]; exact coarsen_zero _ _

/-- The successor of the least element `ξ₀ = 0` is `[(0, 1)]` when `Y⁰₀ ∈ G_0` (the paper's
`z ∈ VG_{n_z}`). -/
lemma succ_zero_eq (h : Consistent Gs Y) (hG : Monotone Gs) (h0 : Y 0 0 ∈ Gs 0) :
    succ Gs Y 0 = addr Gs Y 0 1 := by
  have hx : ∃ m, level (0 : ℕ →₀ ℕ) ≤ m ∧ Yxi Gs Y 0 ∈ Gs m :=
    ⟨0, le_rfl, by rw [Yxi_zero]; exact h0⟩
  unfold succ
  rw [dite_eq_left hx]
  generalize Classical.choose hx = m
  have htm : tm Gs Y m 0 = 0 := by
    have := tm_addr Gs Y m 0
    rwa [addr_zero_eq_zero] at this
  have hJ : J Gs Y 0 m 1 = 1 := by
    have := h.J_succ_of_mem Gs Y hG h0 m
    rw [J_apply_zero] at this
    exact this
  show addr Gs Y m (tm Gs Y m 0 + 1) = addr Gs Y 0 1
  rw [htm, zero_add]
  have := addr_J Gs Y 0 m 1
  rw [zero_add, hJ] at this
  exact this

/-- **Property (v), deterministic core** (p. 25): if `Ξ` contains arbitrarily large `ξ` with
`Y_ξ = z` (from recurrence of the level-`0` chain), the clock is unbounded and every clock value
is finite, then `X_t = z` for arbitrarily large `t`. -/
lemma exists_ge_X_eq (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hsum : HoldingTimesSummable Gs Y w E) (hE : ∀ a, 0 < E a) (hw : ∀ x, 0 < w x) {z : V}
    (hrec : ∀ k, ∃ k', k < k' ∧ Y 0 k' = z) (T : ℝ≥0) :
    ∃ t : ℝ≥0, T ≤ t ∧ X Gs Y w E t = some z := by
  obtain ⟨K, hK⟩ := PathProperties.exists_lt_tau_addr_zero Gs Y w E hsum.1
    (ENNReal.coe_ne_top (r := T))
  obtain ⟨η, hη, hz⟩ := h.exists_gt_Yxi_eq Gs Y hrec
    ⟨toLex (addr Gs Y 0 K), realized_addr Gs Y 0 K⟩
  have hreal : Realized Gs Y (ofLex η.1) := η.2
  have hτ : tau Gs Y w E (addr Gs Y 0 K) ≤ tau Gs Y w E (ofLex η.1) :=
    tau_mono Gs Y w E (le_of_lt hη)
  have hne : tau Gs Y w E (ofLex η.1) ≠ ⊤ := (hsum.2 _ hreal).ne
  refine ⟨(tau Gs Y w E (ofLex η.1)).toNNReal, ?_, ?_⟩
  · rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
    exact le_trans hK.le hτ
  · rw [h.X_eq_of_inInterval Gs Y w E hG hcov ⟨hreal, ?_, ?_⟩, hz]
    · rw [ENNReal.coe_toNNReal hne]
    · rw [ENNReal.coe_toNNReal hne, PathProperties.tau_succ Gs Y w E h hG hcov hreal]
      exact ENNReal.lt_add_right hne (holding_pos Gs Y w E hw (hE _)).ne'

/-- A hitting time from time `0`: if `u` avoids `s` strictly before `t₀` and hits it at `t₀`,
then `hittingAfter u s 0 ω = t₀`. -/
lemma hittingAfter_eq_coe {Ω β : Type*} {u : ℝ≥0 → Ω → β} {s : Set β} {ω : Ω} {t₀ : ℝ≥0}
    (hlt : ∀ t < t₀, u t ω ∉ s) (ht₀ : u t₀ ω ∈ s) :
    hittingAfter u s 0 ω = (t₀ : WithTop ℝ≥0) := by
  refine le_antisymm (hittingAfter_le_of_mem zero_le ht₀) (le_of_not_gt fun hlt' => ?_)
  obtain ⟨j, hj, hjs⟩ := hittingAfter_lt_iff.mp hlt'
  exact hlt j hj.2 hjs

/-- **Property (vi), deterministic core** (p. 25): if `A ⊆ G_n` and `Yⁿ` first hits `A` at time
`j`, then `X` first hits `A` at `τ_{[(n,j)]}` and `X_τ = Yⁿ_j`, the first point of `A` hit by
`Yⁿ` — "the first point `X_τ` of `A` hit by `X` is the same as the first point of `A` hit by
`Yⁿ`".  Stated for any process `u` whose sample path at `ω` is (3.26). -/
lemma hittingAfter_eq_of_hitTime {Ω : Type*} {u : ℝ≥0 → Ω → Option V} {ω : Ω}
    (hu : ∀ t, u t ω = X Gs Y w E t) (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hsum : HoldingTimesSummable Gs Y w E) (hE : ∀ a, 0 < E a)
    (hw : ∀ x, 0 < w x) {A : Set V} {n : ℕ} (hAn : A ⊆ Gs n)
    (hhit : MarkovChain.hitTime A (Y n) ≠ ⊤) :
    hittingAfter u (some '' A) 0 ω =
        ((tau Gs Y w E (addr Gs Y n (MarkovChain.hitIndex A (Y n)))).toNNReal : WithTop ℝ≥0) ∧
      u (tau Gs Y w E (addr Gs Y n (MarkovChain.hitIndex A (Y n)))).toNNReal ω =
        some (MarkovChain.hitVertex A (Y n)) := by
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hhit
  have hj' : MarkovChain.hitTime A (Y n) = WithTop.some j := hj.symm
  have hidx : MarkovChain.hitIndex A (Y n) = j := MarkovChain.hitIndex_eq_of_eq hj'
  obtain ⟨hmem, hlt⟩ := MarkovChain.hitTime_eq_coe_iff.mp hj'
  have hne : tau Gs Y w E (addr Gs Y n j) ≠ ⊤ := (hsum.2 _ (realized_addr Gs Y n j)).ne
  have hX : X Gs Y w E (tau Gs Y w E (addr Gs Y n j)).toNNReal = some (Y n j) := by
    rw [h.X_eq_of_inInterval Gs Y w E hG hcov ⟨realized_addr Gs Y n j, ?_, ?_⟩, h.Yxi_addr]
    · rw [ENNReal.coe_toNNReal hne]
    · rw [ENNReal.coe_toNNReal hne,
        PathProperties.tau_succ Gs Y w E h hG hcov (realized_addr Gs Y n j)]
      exact ENNReal.lt_add_right hne (holding_pos Gs Y w E hw (hE _)).ne'
  rw [hidx]
  refine ⟨hittingAfter_eq_coe (fun t ht hts => ?_) ?_, ?_⟩
  · obtain ⟨x, hxA, hxt⟩ := hts
    rw [hu] at hxt
    obtain ⟨η, hη, hηx⟩ := exists_inInterval_of_X_eq_some Gs Y w E hxt.symm
    obtain ⟨k, rfl⟩ := h.exists_addr_eq_of_mem Gs Y hG hη.1 (by rw [hηx]; exact hAn hxA)
    have hk : k < j := by
      rw [← addr_lt_addr_iff Gs Y]
      by_contra hle
      have h1 : tau Gs Y w E (addr Gs Y n j) ≤ (t : ℝ≥0∞) :=
        (tau_mono Gs Y w E (not_lt.mp hle)).trans hη.2.1
      have h2 : (t : ℝ≥0∞) < tau Gs Y w E (addr Gs Y n j) := by
        rw [← ENNReal.coe_toNNReal hne]
        exact ENNReal.coe_lt_coe.mpr ht
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
    exact hlt k hk (by rw [← h.Yxi_addr Gs Y n k, hηx]; exact hxA)
  · rw [hu, hX]
    exact ⟨Y n j, hmem, rfl⟩
  · rw [hu, hX, MarkovChain.hitVertex, hidx]

/-- **Property (iii), deterministic core** (p. 24): `X_t = Y⁰₀` for `t ∈ [0, T_{ξ₀})` with
`T_{ξ₀} = E_{ξ₀} / w(Y⁰₀)`, and `X_{T_{ξ₀}} = Y⁰₁`; so if `Y⁰₁ ≠ Y⁰₀`, the exit time from `Y⁰₀`
is `T_{ξ₀}` and the position at the exit time is `Y⁰₁`.  This is the paper's "`Xⁿ_t = X_t` for
`t ∈ [0, T_{ξ₀}]`", specialised to what property (iii) needs. -/
lemma exitTime_eq_of {Ω : Type*} {u : ℝ≥0 → Ω → Option V} {ω : Ω}
    (hu : ∀ t, u t ω = X Gs Y w E t) (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hE : ∀ a, 0 < E a) (hw : ∀ x, 0 < w x)
    (h0 : Y 0 0 ∈ Gs 0) (h1 : Y 0 1 ≠ Y 0 0) :
    hittingAfter u {s | s ≠ some (Y 0 0)} 0 ω = Theorem16.toWithTop (E 0 / w (Y 0 0)) ∧
      u (E 0 / w (Y 0 0)).toNNReal ω = some (Y 0 1) := by
  have hh0 : holding Gs Y w E 0 = ENNReal.ofReal (E 0 / w (Y 0 0)) := by
    rw [holding, Yxi_zero]
  have hne : holding Gs Y w E 0 ≠ ⊤ := holding_ne_top Gs Y w E 0
  have hτ1 : tau Gs Y w E (succ Gs Y 0) = holding Gs Y w E 0 := by
    rw [PathProperties.tau_succ Gs Y w E h hG hcov (realized_zero Gs Y),
      PathProperties.tau_zero, zero_add]
  have hreal1 : Realized Gs Y (succ Gs Y 0) :=
    (h.succ_spec Gs Y hG hcov (realized_zero Gs Y)).1
  have hcoe : ((E 0 / w (Y 0 0)).toNNReal : ℝ≥0∞) = holding Gs Y w E 0 := by
    rw [hh0]
    rfl
  have hX : X Gs Y w E (E 0 / w (Y 0 0)).toNNReal = some (Y 0 1) := by
    rw [h.X_eq_of_inInterval Gs Y w E hG hcov ⟨hreal1, ?_, ?_⟩, succ_zero_eq Gs Y h hG h0,
      h.Yxi_addr]
    · rw [hcoe, hτ1]
    · rw [hcoe, PathProperties.tau_succ Gs Y w E h hG hcov hreal1, hτ1]
      exact ENNReal.lt_add_right hne (holding_pos Gs Y w E hw (hE _)).ne'
  unfold Theorem16.toWithTop
  refine ⟨hittingAfter_eq_coe (fun t ht hts => ?_) ?_, ?_⟩
  · apply hts
    rw [hu, h.X_eq_of_inInterval Gs Y w E hG hcov ⟨realized_zero Gs Y, ?_, ?_⟩, Yxi_zero]
    · rw [PathProperties.tau_zero]
      exact zero_le
    · rw [hτ1, ← hcoe]
      exact ENNReal.coe_lt_coe.mpr ht
  · rw [hu, hX]
    exact fun hc => h1 (Option.some_injective V hc)
  · rw [hu, hX]

end deterministic

/-! ### The sample space and the process -/

section space

/-- The sample space: the paths `Y : level ↦ time ↦ vertex` of the coupled chains and the unit
holding times `E : Ξ₀ → ℝ` (the carrier of `Exhaustion.jointLaw`). -/
abbrev Sample (V : Type u) : Type u := (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)

/-- Each unit holding time has law `Exponential(1)`. -/
lemma expFamily_map_eval (a : ℕ →₀ ℕ) :
    expFamily.map (fun e : (ℕ →₀ ℕ) → ℝ => e a) = ProbabilityTheory.expMeasure 1 := by
  rw [expFamily, Measure.infinitePi_map_eval]

/-- `Exponential(1)` gives no mass to `(-∞, 0]`. -/
lemma expMeasure_one_Iic_zero : ProbabilityTheory.expMeasure 1 (Set.Iic 0) = 0 := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos]
  simp

/-- Almost surely every unit holding time is positive. -/
lemma expFamily_ae_pos : ∀ᵐ e ∂expFamily, ∀ a, 0 < e a := by
  rw [ae_all_iff]
  intro a
  rw [ae_iff]
  have h : {e : (ℕ →₀ ℕ) → ℝ | ¬ 0 < e a} = (fun e => e a) ⁻¹' Set.Iic 0 := by
    ext e
    simp
  rw [h, ← Measure.map_apply (measurable_pi_apply a) measurableSet_Iic, expFamily_map_eval,
    expMeasure_one_Iic_zero]

/-- `Exponential(1)` scaled by `1/r` is `Exponential(r)`: the holding time `T_ξ = E_ξ / w(Y_ξ)`
has the law prescribed in Section 3.3. -/
lemma expMeasure_one_map_div {r : ℝ} (hr : 0 < r) :
    (ProbabilityTheory.expMeasure 1).map (fun x => x / r) = ProbabilityTheory.expMeasure r := by
  have hr' : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  have hm : Measurable fun x : ℝ => x / r := measurable_id.div_const r
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hm measurableSet_Iic]
  have e : (fun x : ℝ => x / r) ⁻¹' Set.Iic a = Set.Iic (a * r) := by
    ext x
    simp [div_le_iff₀ hr]
  rw [e, ← ofReal_cdf, ← ofReal_cdf, cdf_expMeasure_eq one_pos, cdf_expMeasure_eq hr]
  congr 1
  by_cases ha : 0 ≤ a
  · rw [ite_eq_left ha, ite_eq_left (mul_nonneg ha hr.le), one_mul, mul_comm]
  · rw [ite_eq_right ha, ite_eq_right (not_le.mpr (mul_neg_of_neg_of_pos (not_le.mp ha) hr))]

/-- **`E_{ξ₀}` is independent of the other unit holding times**: in the i.i.d. family, the
coordinate `0` is independent of the family with coordinate `0` replaced by `0`.  (The
coordinates are independent, `iIndepFun_eval_expFamily`, and the second map is measurable
with respect to the σ-algebra generated by the coordinates `≠ 0`.) -/
lemma expFamily_indepFun_eval_update :
    IndepFun (fun e : (ℕ →₀ ℕ) → ℝ => e 0)
      (fun e : (ℕ →₀ ℕ) → ℝ => Function.update e 0 0) expFamily := by
  have hind : iIndep (fun a : ℕ →₀ ℕ =>
      MeasurableSpace.comap (fun e : (ℕ →₀ ℕ) → ℝ => e a) inferInstance) expFamily :=
    iIndepFun_eval_expFamily.iIndep
  have hle : ∀ a : ℕ →₀ ℕ, MeasurableSpace.comap (fun e : (ℕ →₀ ℕ) → ℝ => e a) inferInstance ≤
      (inferInstance : MeasurableSpace ((ℕ →₀ ℕ) → ℝ)) :=
    fun a => measurable_iff_comap_le.mp (measurable_pi_apply a)
  have h := indep_iSup_of_disjoint hle hind (S := {0}) (T := {0}ᶜ) disjoint_compl_right
  change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) expFamily
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact le_iSup_of_le 0 (le_iSup_of_le rfl le_rfl)
  · rw [← measurable_iff_comap_le]
    refine (@measurable_pi_iff ((ℕ →₀ ℕ) → ℝ) (ℕ →₀ ℕ) (fun _ => ℝ)
      (⨆ i ∈ ({0} : Set (ℕ →₀ ℕ))ᶜ,
        MeasurableSpace.comap (fun e : (ℕ →₀ ℕ) → ℝ => e i) inferInstance) _ _).mpr fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simp only [Function.update_self]
      exact measurable_const
    · have e : (fun e : (ℕ →₀ ℕ) → ℝ => Function.update e 0 0 i) = fun e => e i :=
        funext fun e => Function.update_of_ne hi 0 e
      rw [e]
      exact Measurable.mono (measurable_iff_comap_le.mpr le_rfl)
        (le_iSup_of_le i (le_iSup_of_le hi le_rfl)) le_rfl

/-- Lifting independence from the second factor of a product: if `f` and `g` are independent
under `ν`, then `f ∘ snd` is independent of `(fst, g ∘ snd)` under `μ ⊗ ν`. -/
lemma indepFun_snd_prod_of_indepFun {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g ν) :
    IndepFun (fun ω : α × β => f ω.2) (fun ω : α × β => (ω.1, g ω.2)) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hms : MeasurableSet ((fun ω : α × β => f ω.2) ⁻¹' s) := (hf.comp measurable_snd) hs
  have hmt : MeasurableSet ((fun ω : α × β => (ω.1, g ω.2)) ⁻¹' t) :=
    (measurable_fst.prodMk (hg.comp measurable_snd)) ht
  rw [Measure.prod_apply (hms.inter hmt), Measure.prod_apply hms, Measure.prod_apply hmt]
  have hslice : ∀ x : α, Prod.mk x ⁻¹' ((fun ω : α × β => f ω.2) ⁻¹' s ∩
      (fun ω : α × β => (ω.1, g ω.2)) ⁻¹' t) = f ⁻¹' s ∩ g ⁻¹' (Prod.mk x ⁻¹' t) :=
    fun _ => rfl
  have hslice_s : ∀ x : α, Prod.mk x ⁻¹' ((fun ω : α × β => f ω.2) ⁻¹' s) = f ⁻¹' s :=
    fun _ => rfl
  have hslice_t : ∀ x : α, Prod.mk x ⁻¹' ((fun ω : α × β => (ω.1, g ω.2)) ⁻¹' t) =
      g ⁻¹' (Prod.mk x ⁻¹' t) := fun _ => rfl
  simp_rw [hslice, hslice_s, hslice_t]
  have hmul : ∀ x : α, ν (f ⁻¹' s ∩ g ⁻¹' (Prod.mk x ⁻¹' t)) =
      ν (f ⁻¹' s) * ν (g ⁻¹' (Prod.mk x ⁻¹' t)) :=
    fun x => h.measure_inter_preimage_eq_mul s _ hs (measurable_prodMk_left ht)
  simp_rw [hmul]
  rw [lintegral_const_mul' _ _ (measure_ne_top ν _), lintegral_const, measure_univ, mul_one]

end space

section process

variable {G : ConductanceGraph V} (E : G.Exhaustion) (w : V → ℝ)

/-- **The process (3.26)** as a single stochastic process for all starting points: the process
`PathProperties.process` of (3.26), with the base level of the exhaustion `n_{Y⁰₀}` read off the
starting vertex `Y⁰₀` of the sample. -/
noncomputable def process (t : ℝ≥0) (ω : Sample V) : Option V :=
  PathProperties.process (E.levelSets (E.nz (ω.1 0 0))) w Prod.fst Prod.snd t ω

/-- On the event `Y⁰₀ = z`, the process is `PathProperties.process` with base level `n_z`. -/
lemma process_eq_of_start {z : V} {ω : Sample V} (h0 : ω.1 0 0 = z) (t : ℝ≥0) :
    process E w t ω = PathProperties.process (E.levelSets (E.nz z)) w Prod.fst Prod.snd t ω := by
  rw [process, h0]

/-- On the full-measure event `Y⁰₀ = z`, (3.12), the process is (3.26) with base level `n_z`. -/
lemma process_eq {z : V} {ω : Sample V} (h0 : ω.1 0 0 = z)
    (hc : Consistent (E.levelSets (E.nz z)) ω.1) (t : ℝ≥0) :
    process E w t ω = X (E.levelSets (E.nz z)) ω.1 w ω.2 t := by
  rw [process_eq_of_start E w h0, PathProperties.process_of_consistent _ _ _ _ hc]

/-- Every `EnergyMinimizer` bundle is Proposition 1.3's `energyMin` on non-empty `A`
(Contract A's `energyMin_unique`); property (vi) is therefore the same statement for every
bundle. -/
lemma energyMinimizer_eq (hG : G.toSimpleGraph.Connected) (hmin : G.EnergyMinimizer)
    {A : Finset V} (hA : A.Nonempty) (φ : V → ℝ) : hmin A φ = G.energyMin hG A φ :=
  G.energyMin_unique hG hA φ (hmin.hasFiniteEnergy hA φ) (hmin.eqOn hA φ)
    fun _ hg hgA => hmin.le_energy hA φ hg hgA

end process

/-! ### Measurability of the process -/

section measurability

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

omit [Countable V] [MeasurableSingletonClass V] in
/-- `ω ↦ Yⁿ_j` is measurable. -/
lemma measurable_Y (n j : ℕ) : Measurable fun ω : Sample V => ω.1 n j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply n).comp measurable_fst)

/-- **Each `X_t` is a random variable**: the family process is measurable, by decomposing
along the countably many values of the starting vertex `Y⁰₀` and using
`PathProperties.measurable_process` for each base level. -/
lemma measurable_process {G : ConductanceGraph V} (E : G.Exhaustion) (w : V → ℝ) (t : ℝ≥0) :
    Measurable (process E w t) := by
  have h : process E w t = fun ω : Sample V =>
      (fun p : Sample V × V =>
        PathProperties.process (E.levelSets (E.nz p.2)) w Prod.fst Prod.snd t p.1) (ω, ω.1 0 0) :=
    rfl
  rw [h]
  have hpair : Measurable fun ω : Sample V => (ω, ω.1 0 0) :=
    measurable_id.prodMk (measurable_Y (V := V) 0 0)
  have hF : Measurable fun p : Sample V × V =>
      PathProperties.process (E.levelSets (E.nz p.2)) w Prod.fst Prod.snd t p.1 := by
    refine measurable_from_prod_countable_left fun v => ?_
    exact PathProperties.measurable_process (E.levelSets (E.nz v)) w
      (measurable_fst : Measurable (Prod.fst : Sample V → ℕ → ℕ → V))
      (measurable_snd : Measurable (Prod.snd : Sample V → (ℕ →₀ ℕ) → ℝ))
      (E.levelSets_mono _) (E.exists_mem_levelSets _) t
  exact hF.comp hpair

end measurability

section probabilistic

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  {G : ConductanceGraph V} (E : G.Exhaustion) (hG : G.toSimpleGraph.Connected) (w : V → ℝ)

/-- **The paper's probability space `P_z` of Section 3.3**: the joint law
`Exhaustion.jointLaw` with base level `n_z` — the coupling `P_z` of Lemma 3.4 tensored with the
i.i.d. `Exponential(1)` unit holding times, so that, conditional on the paths,
`T_ξ = E_ξ / w(Y_ξ)` are independent `Exponential(w(Y_ξ))` variables. -/
noncomputable abbrev sampleLaw (z : V) : Measure (Sample V) := E.jointLaw hG (E.nz z) z

/-- The paths have the law `P_z` of Lemma 3.4. -/
lemma sampleLaw_map_fst (z : V) : (sampleLaw E hG z).map Prod.fst = E.Pz hG z := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The unit holding times have the i.i.d. `Exponential(1)` law. -/
lemma sampleLaw_map_snd (z : V) : (sampleLaw E hG z).map Prod.snd = expFamily := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Almost-sure properties of the coupled paths transfer to the sample. -/
lemma sampleLaw_ae_fst {z : V} {q : (ℕ → ℕ → V) → Prop} (h : ∀ᵐ y ∂E.Pz hG z, q y) :
    ∀ᵐ ω ∂sampleLaw E hG z, q ω.1 := by
  rw [← sampleLaw_map_fst E hG z] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- (3.12) holds almost surely (Lemma 3.4). -/
lemma sampleLaw_ae_consistent (z : V) :
    ∀ᵐ ω ∂sampleLaw E hG z, Consistent (E.levelSets (E.nz z)) ω.1 :=
  sampleLaw_ae_fst E hG (E.coupling_ae_consistent hG (E.nz z) z)

/-- Every level starts at `z` almost surely. -/
lemma sampleLaw_ae_start (z : V) : ∀ᵐ ω ∂sampleLaw E hG z, ∀ i, ω.1 i 0 = z :=
  sampleLaw_ae_fst E hG (E.coupling_ae_start hG (E.nz z) z)

/-- The level-`i` path has the law of `Y^{n_z+i}` started at `z`. -/
lemma sampleLaw_map_level (z : V) (i : ℕ) :
    (sampleLaw E hG z).map (fun ω => ω.1 i) = E.chainLaw hG (E.nz z + i) z := by
  have h1 : (fun ω : Sample V => ω.1 i) = (fun y : ℕ → ℕ → V => y i) ∘ Prod.fst := rfl
  rw [h1, ← Measure.map_map (measurable_pi_apply i) measurable_fst, sampleLaw_map_fst]
  exact E.coupling_map_apply hG (E.nz z) z i

/-- Almost-sure properties of `Y^{n_z+i}` transfer to the sample. -/
lemma sampleLaw_ae_level {z : V} (i : ℕ) {q : (ℕ → V) → Prop}
    (h : ∀ᵐ p ∂E.chainLaw hG (E.nz z + i) z, q p) :
    ∀ᵐ ω ∂sampleLaw E hG z, q (ω.1 i) :=
  sampleLaw_ae_fst E hG (E.coupling_ae_of_ae hG (E.nz z) z i h)

/-- Almost surely every unit holding time is positive. -/
lemma sampleLaw_ae_pos (z : V) : ∀ᵐ ω ∂sampleLaw E hG z, ∀ a, 0 < ω.2 a := by
  have h := expFamily_ae_pos
  rw [← sampleLaw_map_snd E hG z] at h
  exact ae_of_ae_map measurable_snd.aemeasurable h

/-- The unit holding time `E_{ξ₀}` of the least element of `Ξ` has law `Exponential(1)`. -/
lemma sampleLaw_map_E0 (z : V) :
    (sampleLaw E hG z).map (fun ω => ω.2 0) = ProbabilityTheory.expMeasure 1 := by
  have h : (fun ω : Sample V => ω.2 0) = (fun e : (ℕ →₀ ℕ) → ℝ => e 0) ∘ Prod.snd := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply 0) measurable_snd, sampleLaw_map_snd,
    expFamily_map_eval]

/-- **Input of Lemma 3.7, absolute continuity**: the law of `E_{ξ₀}` is absolutely continuous
with respect to Lebesgue measure on `(0, ∞)`. -/
lemma sampleLaw_E0_absolutelyContinuous (z : V) :
    (sampleLaw E hG z).map (fun ω => ω.2 0) ≪ volume.restrict (Set.Ioi 0) := by
  rw [sampleLaw_map_E0]
  exact PathProperties.expMeasure_absolutelyContinuous 1

/-- **Input of Lemma 3.7, independence**: `E_{ξ₀}` is independent of the paths and of the other
unit holding times (`PathProperties.rest`), by the product structure of `P_z ⊗ expFamily` and
`expFamily_indepFun_eval_update`. -/
lemma sampleLaw_indepFun_E0_rest (z : V) :
    IndepFun (fun ω : Sample V => ω.2 0) (PathProperties.rest Prod.fst Prod.snd)
      (sampleLaw E hG z) :=
  indepFun_snd_prod_of_indepFun (μ := E.coupling hG (E.nz z) z) (ν := expFamily)
    (measurable_pi_apply 0) (measurable_update'.comp (measurable_id.prodMk measurable_const))
    expFamily_indepFun_eval_update

/-- **Remark 3.1 at level `n_z`**: almost surely the level-`0` chain `Y^{n_z}` visits `z` at
arbitrarily large times. -/
lemma sampleLaw_ae_rec (z : V) :
    ∀ᵐ ω ∂sampleLaw E hG z, ∀ k, ∃ k', k < k' ∧ ω.1 0 k' = z :=
  sampleLaw_ae_level E hG 0 (E.chainLaw_ae_exists_gt_eq hG (E.nz z + 0) (E.mem_Gsub_nz z) z)

/-- Under `P_z` the family process agrees with `PathProperties.process` at base level `n_z`,
for all times simultaneously. -/
lemma ae_process_eq (z : V) : ∀ᵐ ω ∂sampleLaw E hG z, ∀ t,
    process E w t ω = PathProperties.process (E.levelSets (E.nz z)) w Prod.fst Prod.snd t ω :=
  (sampleLaw_ae_start E hG z).mono fun _ h0 t => process_eq_of_start E w (h0 0) t

/-! #### Properties (i) and (ii), from `PathProperties` -/

omit [Countable V] [MeasurableSingletonClass V] [Nontrivial V] in
/-- Property (i) transfers along an a.s. identity of processes. -/
lemma almostEverywhereDefined_congr {P : Measure (Sample V)}
    {X X' : ℝ≥0 → Sample V → Option V} (h : ∀ᵐ ω ∂P, ∀ t, X t ω = X' t ω)
    (hX' : Theorem16.AlmostEverywhereDefined P X') : Theorem16.AlmostEverywhereDefined P X := by
  intro t
  filter_upwards [h, hX' t] with ω hω hω'
  obtain ⟨h1, ε, hε, h2⟩ := hω'
  refine ⟨by rw [hω t]; exact h1, ε, hε, fun s hs => ?_⟩
  rw [hω s, hω t]
  exact h2 s hs

omit [Countable V] [MeasurableSingletonClass V] [Nontrivial V] in
/-- Property (ii) transfers along an a.s. identity of processes. -/
lemma rightContinuous_congr {P : Measure (Sample V)}
    {X X' : ℝ≥0 → Sample V → Option V} (h : ∀ᵐ ω ∂P, ∀ t, X t ω = X' t ω)
    (hX' : Theorem16.RightContinuous P X') : Theorem16.RightContinuous P X := by
  filter_upwards [h, hX'] with ω hω hω' t ht
  rw [hω t] at ht ⊢
  obtain ⟨ε, hε, h2⟩ := hω' t ht
  refine ⟨ε, hε, fun s hs => ?_⟩
  rw [hω s]
  exact h2 s hs

/-- **Theorem 1.6, property (i)** for the family process under `P_z`:
`PathProperties.almostEverywhereDefined` (Lemma 3.7), with the summability (3.16) of Lemma 3.5
as the hypothesis `hsum`, and the independence and absolute continuity of `E_{ξ₀}` discharged
here. -/
theorem almostEverywhereDefined (hw : ∀ x, 0 < w x) (z : V)
    (hsum : ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) :
    Theorem16.AlmostEverywhereDefined (sampleLaw E hG z) (process E w) :=
  almostEverywhereDefined_congr (ae_process_eq E hG w z)
    (PathProperties.almostEverywhereDefined (sampleLaw E hG z) (E.levelSets (E.nz z)) w
      measurable_fst measurable_snd (E.levelSets_mono _) (E.exists_mem_levelSets _) hw
      (sampleLaw_ae_consistent E hG z) hsum (sampleLaw_indepFun_E0_rest E hG z)
      (sampleLaw_E0_absolutelyContinuous E hG z))

/-- **Theorem 1.6, property (ii)** for the family process under `P_z`:
`PathProperties.rightContinuous`. -/
theorem rightContinuous (z : V) :
    Theorem16.RightContinuous (sampleLaw E hG z) (process E w) :=
  rightContinuous_congr (ae_process_eq E hG w z)
    (PathProperties.rightContinuous (sampleLaw E hG z) (E.levelSets (E.nz z)) w Prod.fst
      Prod.snd (E.levelSets_mono _) (E.exists_mem_levelSets _) (sampleLaw_ae_consistent E hG z))

/-! #### Property (v) -/

/-- **Theorem 1.6, property (v) (Recurrence)** for the process (3.26) under `P_z` (p. 25):
almost surely there are arbitrarily large `t` with `X_t = z`.  The a.s. summability (3.16) of
Lemma 3.5 is the hypothesis `hsum`. -/
theorem recurrent (hw : ∀ x, 0 < w x) (z : V)
    (hsum : ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) :
    Theorem16.Recurrent z (sampleLaw E hG z) (process E w) := by
  filter_upwards [sampleLaw_ae_consistent E hG z, sampleLaw_ae_start E hG z,
    sampleLaw_ae_pos E hG z, sampleLaw_ae_rec E hG z, hsum] with ω hc h0 hpos hrec hs
  intro T
  obtain ⟨t, hTt, hXt⟩ := exists_ge_X_eq (E.levelSets (E.nz z)) ω.1 w ω.2 hc
    (E.levelSets_mono _) (E.exists_mem_levelSets _) hs hpos hw hrec T
  exact ⟨t, hTt, by rw [process_eq E w (h0 0) hc]; exact hXt⟩

/-! #### Property (vi) -/

/-- **Theorem 1.6, property (vi) (Relation to harmonic functions)** for the process (3.26)
under `P_z` (p. 25).  For `n` with `A ⊆ VG_{n_z+n}`, the first point of `A` hit by `X` is the
first point of `A` hit by `Y^{n_z+n}` (`hittingAfter_eq_of_hitTime`), and Lemma 3.2
(`Exhaustion.energyMin_eq_integral_hitVertex`) identifies its law with the energy-minimising
harmonic measure.  The a.s. summability (3.16) of Lemma 3.5 is the hypothesis `hsum`. -/
theorem harmonicHitting (hw : ∀ x, 0 < w x) (hmin : G.EnergyMinimizer) (z : V)
    (hsum : ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) :
    Theorem16.HarmonicHitting G hmin z (sampleLaw E hG z) (process E w) := by
  intro A hA
  obtain ⟨N, hN⟩ : ∃ N, ∀ x ∈ A, x ∈ E.Gsub N := by
    classical
    refine ⟨A.sup fun x => Nat.find (E.exists_mem x), fun x hx => ?_⟩
    exact E.mono (Finset.le_sup (f := fun x => Nat.find (E.exists_mem x)) hx)
      (Nat.find_spec (E.exists_mem x))
  have hAn : A ⊆ E.Gsub (E.nz z + N) := fun x hx => E.mono (Nat.le_add_left N _) (hN x hx)
  have hAn' : (↑A : Set V) ⊆ E.levelSets (E.nz z) N :=
    fun x hx => Finset.mem_coe.mpr (hAn (Finset.mem_coe.mp hx))
  have hhit : ∀ᵐ ω ∂sampleLaw E hG z, MarkovChain.hitTime (↑A : Set V) (ω.1 N) ≠ ⊤ :=
    sampleLaw_ae_level E hG N (E.hitTime_ae_ne_top hG (E.nz z + N) hA hAn z)
  have key : ∀ᵐ ω ∂sampleLaw E hG z,
      stoppedValue (process E w) (Theorem16.hittingTime (process E w) A) ω =
          some (MarkovChain.hitVertex (↑A : Set V) (ω.1 N)) ∧
        Theorem16.hittingTime (process E w) A ω ≠ ⊤ ∧
        MarkovChain.hitVertex (↑A : Set V) (ω.1 N) ∈ A := by
    filter_upwards [sampleLaw_ae_consistent E hG z, sampleLaw_ae_start E hG z,
      sampleLaw_ae_pos E hG z, hsum, hhit] with ω hc h0 hpos hs hh
    have hu : ∀ t, process E w t ω = X (E.levelSets (E.nz z)) ω.1 w ω.2 t :=
      process_eq E w (h0 0) hc
    obtain ⟨h1, h2⟩ := hittingAfter_eq_of_hitTime (E.levelSets (E.nz z)) ω.1 w ω.2 hu hc
      (E.levelSets_mono _) (E.exists_mem_levelSets _) hs hpos hw hAn' hh
    refine ⟨?_, ?_, Finset.mem_coe.mp (MarkovChain.hitVertex_mem hh)⟩
    · show process E w (Theorem16.hittingTime (process E w) A ω).untopA ω = _
      rw [Theorem16.hittingTime, h1]
      exact h2
    · rw [Theorem16.hittingTime, h1]
      exact WithTop.coe_ne_top
  refine ⟨?_, fun φ => ?_⟩
  · filter_upwards [key] with ω h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h2, by rw [h1]; exact ⟨_, Finset.mem_coe.mpr h3, rfl⟩⟩
  · have hmeas : Measurable fun p : ℕ → V => φ (MarkovChain.hitVertex (↑A : Set V) p) :=
      (measurable_of_countable φ).comp (MarkovChain.measurable_hitVertex _)
    have hm : Measurable fun ω : Sample V => ω.1 N := (measurable_pi_apply N).comp measurable_fst
    have hae : (fun ω : Sample V =>
        (stoppedValue (process E w) (Theorem16.hittingTime (process E w) A) ω).elim 0 φ)
          =ᵐ[sampleLaw E hG z]
        fun ω : Sample V => φ (MarkovChain.hitVertex (↑A : Set V) (ω.1 N)) := by
      filter_upwards [key] with ω h
      rw [h.1]
      rfl
    refine ⟨?_, ?_⟩
    · -- Integrability: a.e. the integrand equals `φ` at a vertex of the finite set `A`,
      -- hence is a.e. bounded by `sup'` of `|φ|` over `A`.
      refine (integrable_const (A.sup' hA fun y => |φ y|)).mono'
        ((hmeas.comp hm).aestronglyMeasurable.congr hae.symm) ?_
      filter_upwards [key] with ω h
      rw [h.1]
      rw [Real.norm_eq_abs]
      exact Finset.le_sup' (fun y => |φ y|) h.2.2
    · rw [energyMinimizer_eq hG hmin hA φ,
        E.energyMin_eq_integral_hitVertex hG (E.nz z + N) hA hAn φ z,
        ← sampleLaw_map_level E hG z N, integral_map hm.aemeasurable hmeas.aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [key] with ω h
      rw [h.1]
      rfl

/-! #### Property (iii) -/

/-- `P_z[Y^{n_z}_1 = x] = c(z,x)/π(z)`: the first step of the level-`n_z` chain is a step of the
random walk on `G` from `z ∈ VG_{n_z}`, by (3.2). -/
lemma sampleLaw_level_one (z x : V) :
    sampleLaw E hG z {ω | ω.1 0 1 = x} = ENNReal.ofReal (G.c z x / G.pi z) := by
  have hm : Measurable fun ω : Sample V => ω.1 0 := (measurable_pi_apply 0).comp measurable_fst
  have e : {ω : Sample V | ω.1 0 1 = x} = (fun ω : Sample V => ω.1 0) ⁻¹' {p | p 1 = x} := rfl
  have e2 : {p : ℕ → V | p 1 = x} = (fun p : ℕ → V => p 1) ⁻¹' {x} := rfl
  have hs : MeasurableSet {p : ℕ → V | p 1 = x} := by
    rw [e2]
    exact measurable_pi_apply 1 (measurableSet_singleton x)
  have hlaw := sampleLaw_map_level E hG z 0
  rw [Nat.add_zero] at hlaw
  rw [e, ← Measure.map_apply hm hs, hlaw, ConductanceGraph.Exhaustion.chainLaw, e2,
    ← Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton x),
    MarkovChain.chainLaw_marginal_one, E.stepKernel_singleton,
    ConductanceGraph.Exhaustion.transProb, G.transProb_of_mem hG (E.mem_Gsub_nz z)]

omit [Nontrivial V] in
/-- `a ↦ some (g a)` is measurable for the power-set σ-algebra on `Option V`. -/
lemma measurable_some_comp {α : Type*} [MeasurableSpace α] {g : α → V} (hg : Measurable g) :
    Measurable fun a => (some (g a) : Option V) := by
  refine measurable_to_countable' fun o => ?_
  cases o with
  | none =>
    have h : (fun a => (some (g a) : Option V)) ⁻¹' {none} = ∅ := by
      ext a
      simp
    rw [h]
    exact MeasurableSet.empty
  | some v =>
    have h : (fun a => (some (g a) : Option V)) ⁻¹' {some v} = g ⁻¹' {v} := by
      ext a
      simp
    rw [h]
    exact hg (measurableSet_singleton v)

/-- **Theorem 1.6, property (iii) (Continuous-time random walk)** for the process (3.26) under
`P_z` (p. 24): with `τ` the exit time from `z`, `τ` and `X_τ` are independent, `τ` is
`Exponential(w(z))`, and `P_z[X_τ = x] = c(z,x)/π(z)`.  Before the first jump `X` sits at `z`
for the time `T_{ξ₀} = E_{ξ₀}/w(z)` and then jumps to `Y^{n_z}_1` (`exitTime_eq_of`); `E_{ξ₀}` is
`Exponential(1)` and independent of the paths, and `Y^{n_z}_1` is one step of the random walk
from `z`. -/
theorem exponentialFirstStep (hw : ∀ x, 0 < w x) (z : V) :
    Theorem16.ExponentialFirstStep G w z (sampleLaw E hG z) (process E w) := by
  have hne : ∀ᵐ ω ∂sampleLaw E hG z, ω.1 0 1 ≠ z := by
    rw [ae_iff]
    have e : {ω : Sample V | ¬ ω.1 0 1 ≠ z} = {ω | ω.1 0 1 = z} := by
      ext ω
      simp
    rw [e, sampleLaw_level_one, G.c_self, zero_div, ENNReal.ofReal_zero]
  have key : ∀ᵐ ω ∂sampleLaw E hG z,
      Theorem16.exitTime (process E w) z ω = Theorem16.toWithTop (ω.2 0 / w z) ∧
        stoppedValue (process E w) (Theorem16.exitTime (process E w) z) ω = some (ω.1 0 1) := by
    filter_upwards [sampleLaw_ae_consistent E hG z, sampleLaw_ae_start E hG z,
      sampleLaw_ae_pos E hG z, hne] with ω hc h0 hpos hn
    have hu : ∀ t, process E w t ω = X (E.levelSets (E.nz z)) ω.1 w ω.2 t :=
      process_eq E w (h0 0) hc
    have hz0 : ω.1 0 0 ∈ E.levelSets (E.nz z) 0 := by
      rw [h0 0]
      exact Finset.mem_coe.mpr (E.mem_Gsub_nz z)
    have hn' : ω.1 0 1 ≠ ω.1 0 0 := by
      rw [h0 0]
      exact hn
    obtain ⟨h1, h2⟩ := exitTime_eq_of (E.levelSets (E.nz z)) ω.1 w ω.2 hu hc
      (E.levelSets_mono _) (E.exists_mem_levelSets _) hpos hw hz0 hn'
    rw [h0 0] at h1 h2
    refine ⟨h1, ?_⟩
    show process E w (Theorem16.exitTime (process E w) z ω).untopA ω = _
    rw [Theorem16.exitTime, h1]
    exact h2
  -- the measurable representatives
  have hE0 : Measurable fun ω : Sample V => ω.2 0 := (measurable_pi_apply 0).comp measurable_snd
  have htop : Measurable Theorem16.toWithTop := measurable_real_toNNReal.withTop_coe
  have hdiv : Measurable fun x : ℝ => x / w z := measurable_id.div_const _
  have hf : Measurable fun ω : Sample V => Theorem16.toWithTop (ω.2 0 / w z) :=
    htop.comp (hdiv.comp hE0)
  have hg : Measurable fun ω : Sample V => (some (ω.1 0 1) : Option V) :=
    measurable_some_comp
      ((measurable_pi_apply 1).comp ((measurable_pi_apply 0).comp measurable_fst))
  have hfe : (fun ω : Sample V => Theorem16.toWithTop (ω.2 0 / w z)) =ᵐ[sampleLaw E hG z]
      Theorem16.exitTime (process E w) z :=
    key.mono fun ω h => h.1.symm
  have hge : (fun ω : Sample V => (some (ω.1 0 1) : Option V)) =ᵐ[sampleLaw E hG z]
      stoppedValue (process E w) (Theorem16.exitTime (process E w) z) :=
    key.mono fun ω h => h.2.symm
  refine ⟨hf.aemeasurable.congr hfe, hg.aemeasurable.congr hge, ?_, ?_, fun x => ?_⟩
  · -- independence: a function of the holding times against a function of the paths
    have hind : IndepFun (fun ω : Sample V => Theorem16.toWithTop (ω.2 0 / w z))
        (fun ω : Sample V => (some (ω.1 0 1) : Option V)) (sampleLaw E hG z) :=
      (indepFun_prod (μ := E.Pz hG z) (ν := expFamily)
        (X := fun y : ℕ → ℕ → V => (some (y 0 1) : Option V))
        (Y := fun e : (ℕ →₀ ℕ) → ℝ => Theorem16.toWithTop (e 0 / w z))
        (measurable_some_comp ((measurable_pi_apply 1).comp (measurable_pi_apply 0)))
        (htop.comp (hdiv.comp (measurable_pi_apply 0)))).symm
    exact hind.congr hfe hge
  · -- the law of the exit time
    rw [← Measure.map_congr hfe]
    have h : (fun ω : Sample V => Theorem16.toWithTop (ω.2 0 / w z)) =
        Theorem16.toWithTop ∘ (fun x : ℝ => x / w z) ∘ (fun ω : Sample V => ω.2 0) := rfl
    rw [h, ← Measure.map_map htop (hdiv.comp hE0), ← Measure.map_map hdiv hE0, sampleLaw_map_E0,
      expMeasure_one_map_div (hw z)]
  · -- the law of the position at the exit time
    have e : {ω : Sample V | stoppedValue (process E w) (Theorem16.exitTime (process E w) z) ω =
        some x} =ᵐ[sampleLaw E hG z] {ω | ω.1 0 1 = x} := by
      filter_upwards [key] with ω h
      show (stoppedValue (process E w) (Theorem16.exitTime (process E w) z) ω = some x) =
        (ω.1 0 1 = x)
      rw [h.2]
      exact propext Option.some_inj
    rw [measure_congr e, sampleLaw_level_one]

end probabilistic

/-! ### An exhaustion of a countable connected graph (Section 2.3, p. 16)

The paper takes "an increasing family of finite, connected subgraphs `{Gₙ}` whose union is all
of `G`" as given.  For a countable connected graph one exists: enumerate the vertices, choose a
walk from the first vertex to each, and let `Gₙ` be the union of the first `n + 1` walks. -/

section exhaustion

variable {G : ConductanceGraph V}

/-- A countable connected graph has an exhaustion (Section 2.3). -/
theorem exists_exhaustion [Countable V] [Nonempty V] (hG : G.toSimpleGraph.Connected) :
    Nonempty G.Exhaustion := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat V
  have hp : ∀ i, Nonempty (G.toSimpleGraph.Walk (e 0) (e i)) :=
    fun i => hG.preconnected (e 0) (e i)
  let p : ∀ i, G.toSimpleGraph.Walk (e 0) (e i) := fun i => (hp i).some
  let H : ℕ → G.toSimpleGraph.Subgraph := fun n => ⨆ i ∈ Finset.range (n + 1), (p i).toSubgraph
  have hverts : ∀ n, (H n).verts = ⋃ i ∈ Finset.range (n + 1), {w | w ∈ (p i).support} := by
    intro n
    simp only [H, SimpleGraph.Subgraph.verts_iSup, SimpleGraph.Walk.verts_toSubgraph]
  have hfin : ∀ n, (H n).verts.Finite := by
    intro n
    rw [hverts]
    exact (Finset.finite_toSet _).biUnion fun i _ => List.finite_toSet _
  have hmono : Monotone H := fun n m hnm =>
    biSup_mono fun i hi => Finset.range_mono (Nat.succ_le_succ hnm) hi
  have hstart : ∀ n, e 0 ∈ (H n).verts := by
    intro n
    rw [hverts]
    exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.succ_pos n)) (p 0).start_mem_support
  have hconn : ∀ n, (H n).Connected := by
    intro n
    induction n with
    | zero =>
      have h0 : H 0 = (p 0).toSubgraph := by
        show (⨆ i ∈ Finset.range 1, (p i).toSubgraph) = (p 0).toSubgraph
        rw [Finset.range_one, Finset.iSup_singleton]
      rw [h0]
      exact (p 0).toSubgraph_connected
    | succ n ih =>
      have h1 : H (n + 1) = (p (n + 1)).toSubgraph ⊔ H n := by
        show (⨆ i ∈ Finset.range (n + 1 + 1), (p i).toSubgraph) = _
        rw [Finset.range_add_one, Finset.iSup_insert]
      rw [h1]
      exact SimpleGraph.Subgraph.connected_sup (p (n + 1)).toSubgraph_connected.preconnected
        ih.preconnected ⟨e 0, (p (n + 1)).start_mem_verts_toSubgraph, hstart n⟩
  refine ⟨⟨fun n => (hfin n).toFinset, fun n m hnm => ?_, fun n => ?_, fun x => ?_⟩⟩
  · exact Set.Finite.toFinset_subset_toFinset.mpr (SimpleGraph.Subgraph.verts_mono (hmono hnm))
  · rw [Set.Finite.coe_toFinset, SimpleGraph.induce_eq_coe_induce_top]
    exact SimpleGraph.Subgraph.connected_iff'.mp
      ((hconn n).mono SimpleGraph.Subgraph.le_induce_top_verts rfl)
  · obtain ⟨i, rfl⟩ := he x
    refine ⟨i, ?_⟩
    rw [Set.Finite.mem_toFinset, hverts]
    exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self i)) (p i).end_mem_support

end exhaustion

/-! ### The process family and the assembly of the existence half -/

section assembly

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  {G : ConductanceGraph V} (E : G.Exhaustion) (hG : G.toSimpleGraph.Connected) (w : V → ℝ)

/-- **The process family of Theorem 1.6**: the process (3.26) on the sample space `Sample V`,
with the paper's `P_z = E.jointLaw hG (E.nz z) z` as the law started at `z`. -/
noncomputable def processFamily : ProcessFamily V where
  Ω := Sample V
  X := process E w
  measurable_X := measurable_process E w
  P := sampleLaw E hG

/-- The law of the trajectory started at `z`, unfolded. -/
lemma processFamily_law (z : V) :
    (processFamily E hG w).law z = (sampleLaw E hG z).map (fun ω t => process E w t ω) := rfl

/-- `X_0 = z` almost surely under `P_z`: at time `0` the process is in the first holding
interval `[0, T_{ξ₀})`, where it equals `Y⁰₀ = z`. -/
theorem ae_process_zero (hw : ∀ x, 0 < w x) (z : V) :
    ∀ᵐ ω ∂sampleLaw E hG z, process E w 0 ω = some z := by
  filter_upwards [sampleLaw_ae_consistent E hG z, sampleLaw_ae_start E hG z,
    sampleLaw_ae_pos E hG z] with ω hc h0 hpos
  rw [process_eq E w (h0 0) hc, hc.X_eq_of_inInterval _ _ _ _ (E.levelSets_mono _)
    (E.exists_mem_levelSets _) (PathProperties.inInterval_zero _ _ _ _ hc (E.levelSets_mono _)
      (E.exists_mem_levelSets _) (hw _) (hpos 0)), Yxi_zero, h0 0]

/-- **Right continuity at `∞` for the constructed process under `P_z`** — the `∞`-side of
property (ii), the conjunct `Theorem16.RightContinuousAtInfty` of `IsReflectedWalk` — given
(3.16) a.s. (the hypothesis `hsum` in the shape of `recurrent`).  The deterministic core is
`X_rightContinuousAtInfty` (`RightContinuityAtInfty.lean`, the content of the paper's
Lemma 3.11.1 for the process (3.26)); the probabilistic inputs are the a.s. coupling identity
(3.12) and the divergence `∑_{ξ ∈ Ξ} T_ξ = ∞` of (3.16). -/
theorem rightContinuousAtInfty (z : V)
    (hsum : ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) :
    Theorem16.RightContinuousAtInfty (sampleLaw E hG z) (process E w) := by
  filter_upwards [sampleLaw_ae_consistent E hG z, sampleLaw_ae_start E hG z, hsum]
    with ω hc h0 hs
  intro t ht y
  simp only [process_eq E w (h0 0) hc] at ht ⊢
  exact X_rightContinuousAtInfty _ _ _ _ hc (E.levelSets_mono _) (E.exists_mem_levelSets _)
    hs.1 t ht y

/-- The same, with (3.16) discharged by **Lemma 3.5** for `w ≥ w*` off a finite set. -/
theorem rightContinuousAtInfty_of_rateFunction (hw : ∀ x, 0 < w x)
    (hfin : {x | w x < E.rateFunction hG x}.Finite) (z : V) :
    Theorem16.RightContinuousAtInfty (sampleLaw E hG z) (process E w) :=
  rightContinuousAtInfty E hG w z (E.Pz_ae_holdingTimesSummable hG w hw hfin z)

/-- **Theorem 1.6, existence — properties (i)–(vi) for the constructed family**, for a rate
function `w > 0` satisfying (3.16) almost surely (`hsum`, Lemma 3.5, discharged for `w ≥ w*` by
`Exhaustion.exists_rateFunction_forall`).  Properties (i), (ii) — including its `∞`-side
`RightContinuousAtInfty` (`rightContinuousAtInfty`) —, (iii), (v), (vi) and `X_0 = z` are
proved; property (iv), the Markov property, is the hypothesis `hiv`, stated with `μ x` the law
of the family started at `x` (`processFamily_law`). -/
theorem isReflectedWalk (hw : ∀ x, 0 < w x) (hmin : G.EnergyMinimizer)
    (hsum : ∀ z, ∀ᵐ ω ∂sampleLaw E hG z,
      HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2)
    (hiv : ∀ z, Theorem16.MarkovProperty
      (fun x => (sampleLaw E hG x).map (fun ω t => process E w t ω))
      (sampleLaw E hG z) (process E w)) :
    IsReflectedWalk G w hmin (processFamily E hG w) :=
  fun z => ⟨ae_process_zero E hG w hw z, almostEverywhereDefined E hG w hw z (hsum z),
    rightContinuous E hG w z, rightContinuousAtInfty E hG w z (hsum z),
    exponentialFirstStep E hG w hw z, hiv z,
    recurrent E hG w hw z (hsum z), harmonicHitting E hG w hw hmin z (hsum z)⟩

set_option linter.unusedVariables false in
/-- **The existence half of Theorem 1.6** (p. 24, "Proof of Theorem 1.6, existence"), in the
form of the existential clause of `Theorem16Statement`: there is a rate function `w*` such that
for every `w ≥ w*` and every starting point `z` there is a process family satisfying (i)–(vi).
`w*` is Lemma 3.5's (`Exhaustion.exists_rateFunction_forall`); the exhaustion `E` is the
standing choice of Section 2.3.  The one hypothesis carried is property (iv):
* `hiv` — the Markov property of the family process, for every rate function `w > 0` for which
  (3.16) holds `P_z`-a.s. for every `z` (which Lemma 3.5 provides for `w ≥ w*`). -/
theorem existence (hmin : G.EnergyMinimizer)
    (hiv : ∀ w : V → ℝ, (∀ x, 0 < w x) →
      (∀ z, ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) →
      ∀ z, Theorem16.MarkovProperty
        (fun x => (sampleLaw E hG x).map (fun ω t => process E w t ω))
        (sampleLaw E hG z) (process E w)) :
    ∃ wstar : V → ℝ, (∀ x, 0 < wstar x) ∧
      ∀ w : V → ℝ, (∀ x, 0 < w x) → (∀ x, wstar x ≤ w x) →
        ∀ z : V, ∃ 𝓧 : ProcessFamily V, IsReflectedWalk G w hmin 𝓧 := by
  obtain ⟨wstar, hpos, h⟩ := E.exists_rateFunction_forall hG
  refine ⟨wstar, hpos, fun w hw hww _z => ⟨processFamily E hG w, ?_⟩⟩
  have hsum : ∀ z, ∀ᵐ ω ∂sampleLaw E hG z,
      HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2 :=
    fun z => h w hw hww (E.nz z) z (E.mem_Gsub_nz z)
  exact isReflectedWalk E hG w hw hmin hsum (hiv w hw hsum)

end assembly

section main

set_option linter.unusedVariables false in
/-- **The existence half of Theorem 1.6 in the exact shape of `Theorem16Statement`** (the
existential clause, without the uniqueness conjunct): for a countably infinite connected `G`,
there is `w* : VG → (0,∞)` such that for every `w ≥ w*` and every starting point `z` there is a
process family satisfying (i)–(vi).  The σ-algebra on `VG` is the power set and the exhaustion
is `exists_exhaustion`.  The one hypothesis carried is property (iv), the Markov property, for
every σ-algebra with measurable singletons, exhaustion, and rate function `w > 0` satisfying
(3.16) almost surely. -/
theorem existence_half (G : ConductanceGraph V) (hmin : G.EnergyMinimizer)
    (hiv : ∀ [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Nontrivial V]
      (E : G.Exhaustion) (hG : G.toSimpleGraph.Connected) (w : V → ℝ), (∀ x, 0 < w x) →
      (∀ z, ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) →
      ∀ z, Theorem16.MarkovProperty
        (fun x => (sampleLaw E hG x).map (fun ω t => process E w t ω))
        (sampleLaw E hG z) (process E w)) :
    Countable V → Infinite V → G.toSimpleGraph.Connected →
      ∃ wstar : V → ℝ, (∀ x, 0 < wstar x) ∧
        ∀ w : V → ℝ, (∀ x, 0 < w x) → (∀ x, wstar x ≤ w x) →
          ∀ z : V, ∃ 𝓧 : ProcessFamily V, IsReflectedWalk G w hmin 𝓧 := by
  intro hV hinf hG
  let _ : MeasurableSpace V := ⊤
  have _ : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  obtain ⟨E⟩ := exists_exhaustion hG
  exact existence E hG hmin (hiv E hG)

end main

end Existence

end ReflectedWalk
