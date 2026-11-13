/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.UniquenessSkeleton at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov

/-!
# Towards the uniqueness half of Theorem 1.6 (Gwynne–Sung, Section 3.4, pp. 25–26)

The uniqueness proof takes a process `X̃` satisfying the properties of Theorem 1.6 and, for
each `n ≥ n_z`, builds from it the stopping times `tⁿ_j` and holding times `Tⁿ_j` of (3.31):

> `tⁿ_0 = 0`; if `X̃_{tⁿ_j} ∈ G_n`, `tⁿ_{j+1}` is the first time `t ≥ tⁿ_j` with
> `X̃_t ≠ X̃_{tⁿ_j}`; otherwise `tⁿ_{j+1}` is the smallest `t ≥ tⁿ_j` with `X̃_t ∈ G_n`;
> `Tⁿ_j := min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}} − tⁿ_j`.

It then applies the strong Markov property (Lemma 3.10) at each `tⁿ_j` together with
properties (iii) and (vi) to identify the law of `(Tⁿ_j, X̃_{tⁿ_{j+1}})` given the past, and
concludes that the time-changed process `X̃ⁿ` of (3.32) is the continuous-time chain `Xⁿ` of
(3.15).

## What this file provides

The input Lemma 3.10 needs about these times is that they are **stopping times** (for the
completion of the natural filtration, `IsAEStoppingTime`) and **random variables**
(`AEMeasurable`).  For a process on an arbitrary sample space, whose regularity is only
almost sure, this is genuinely a lemma and not a triviality: the hitting time of a set
involves an uncountable infimum.  We prove it for hitting times of *admissible targets* —
finite sets of vertices, and complements of finite sets of vertices (which contain `∞`) —
which are exactly the two kinds occurring in (3.31): `{X̃_t ≠ X̃_{tⁿ_j}}` and `VG_n`.  The
regularity used is right continuity (ii) together with right continuity at `∞`
(`RightContinuousAtInfty`), the standing extra hypothesis of `StrongMarkov.lean`.

* `AdmissibleTarget`, `RightRegularAt`: the target sets and the pointwise regularity.
* `hittingAfter_le_iff_of_rightRegular`: at a regular outcome, `{τ ≤ t}` for the hitting
  time `τ` of an admissible target after a deterministic time is decided by the values of
  `X` at `t` and at the points of a countable dense set before `t`.
* `hitAfter X S σ`: the first time `t ≥ σ` with `X_t ∈ S`, for a random start `σ`; this is
  the building block of the recursion (3.31).
* `isAEStoppingTime_hitAfter`, `aemeasurable_hitAfter`: it is a stopping time up to null
  sets and a.e.-measurable whenever `σ` is.
* `stepTime`, `holdingTime`: the recursion (3.31); `isAEStoppingTime_stepTime`,
  `aemeasurable_stepTime` by induction on `j`.
* `stepTime_strongMarkov`: Lemma 3.10 at `tⁿ_j` — the first sentence of the second paragraph
  of Step 1 ("by the strong Markov property, for each `j` and each `x ∈ B₁G_n`, on the event
  `{X̃_{tⁿ_j} = x}` the conditional distribution of `{X̃_{s+tⁿ_j}}_{s≥0}` given
  `{X̃_s}_{s ≤ tⁿ_j}` is the law of `X̃` under `P_x`").

What is **not** here: the identification of the law of `X̃ⁿ` with that of `Xⁿ` (which needs
the construction (3.15) of `Xⁿ`, built concurrently in `ApproximatingChain.lean`), and
Step 2 (the convergence `X̃ⁿ → X̃`), which needs the `L¹_loc` machinery of `PathSpace.lean`
and a Fubini argument requiring joint measurability of `(s, ω) ↦ X̃_s(ω)` that the
properties (i)–(vi) do not provide.  See the report accompanying this file.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk
namespace Theorem16

variable {V : Type u} {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {X : ℝ≥0 → Ω → Option V} {P : Measure Ω}

/-! ### Admissible targets and pointwise regularity -/

/-- Sets of states whose hitting times are stopping times of a right-continuous process: a
finite set of vertices, or the complement of a finite set of vertices (which contains `∞`).
Both kinds occur in (3.31): `VG_n` and `{s ≠ X̃_{tⁿ_j}}`. -/
def AdmissibleTarget (S : Set (Option V)) : Prop :=
  (∃ A : Finset V, S = some '' (A : Set V)) ∨ (∃ A : Finset V, S = (some '' (A : Set V))ᶜ)

omit mΩ in
/-- The exit set `{s ≠ z}` of property (iii) is admissible. -/
lemma admissibleTarget_ne (z : V) : AdmissibleTarget {s : Option V | s ≠ some z} :=
  Or.inr ⟨{z}, by ext s; simp⟩

omit mΩ in
/-- The hitting set `A ⊆ VG` of property (vi) is admissible. -/
lemma admissibleTarget_image (A : Finset V) : AdmissibleTarget (some '' (A : Set V)) :=
  Or.inl ⟨A, rfl⟩

/-- The pointwise content of properties (ii) and (R) at one outcome. -/
def RightRegularAt (X : ℝ≥0 → Ω → Option V) (ω : Ω) : Prop :=
  (∀ t : ℝ≥0, (∃ x : V, X t ω = some x) →
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω) ∧
  (∀ t : ℝ≥0, X t ω = none →
    ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y)

lemma ae_rightRegularAt (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) :
    ∀ᵐ ω ∂P, RightRegularAt X ω :=
  hii.and hR

omit mΩ in
/-- Finitely many right-neighbourhood conditions hold on a common right neighbourhood. -/
lemma exists_Ioo_forall_finset {ω : Ω} {t : ℝ≥0} (A : Finset V)
    (h : ∀ y ∈ A, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), ∀ y ∈ A, X s ω ≠ some y := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun s _ y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert a A _ ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨ε₂, hε₂, h₂⟩ := ih fun y hy => h y (Finset.mem_insert_of_mem hy)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hs y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h₁ s ⟨hs.1, lt_of_lt_of_le hs.2 (by gcongr; exact min_le_left _ _)⟩
    · exact h₂ s ⟨hs.1, lt_of_lt_of_le hs.2 (by gcongr; exact min_le_right _ _)⟩ y hy

omit mΩ in
/-- At a regular outcome, for an admissible target `S` the predicate `X_s ∈ S` is
right-continuous in `s`: on a right neighbourhood `[t, t + ε)` it agrees with its value at
`t`. -/
lemma exists_Ico_iff_mem_of_rightRegular {ω : Ω} (hω : RightRegularAt X ω)
    {S : Set (Option V)} (hS : AdmissibleTarget S) (t : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), (X s ω ∈ S ↔ X t ω ∈ S) := by
  by_cases hnone : X t ω = none
  · rcases hS with ⟨A, rfl⟩ | ⟨A, rfl⟩
    · obtain ⟨ε, hε, hεs⟩ := exists_Ioo_forall_finset A fun y _ => hω.2 t hnone y
      refine ⟨ε, hε, fun s hs => ?_⟩
      rcases eq_or_lt_of_le hs.1 with rfl | hlt
      · exact Iff.rfl
      · have h1 : X s ω ∉ some '' (A : Set V) := by
          rintro ⟨y, hy, hys⟩
          exact hεs s ⟨hlt, hs.2⟩ y (Finset.mem_coe.1 hy) hys.symm
        have h2 : X t ω ∉ some '' (A : Set V) := by rw [hnone]; simp
        exact iff_of_false h1 h2
    · obtain ⟨ε, hε, hεs⟩ := exists_Ioo_forall_finset A fun y _ => hω.2 t hnone y
      refine ⟨ε, hε, fun s hs => ?_⟩
      rcases eq_or_lt_of_le hs.1 with rfl | hlt
      · exact Iff.rfl
      · have h1 : X s ω ∈ (some '' (A : Set V))ᶜ := by
          rintro ⟨y, hy, hys⟩
          exact hεs s ⟨hlt, hs.2⟩ y (Finset.mem_coe.1 hy) hys.symm
        have h2 : X t ω ∈ (some '' (A : Set V))ᶜ := by rw [hnone]; simp
        exact iff_of_true h1 h2
  · obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.1 hnone
    obtain ⟨ε, hε, hεs⟩ := hω.1 t ⟨y', hy'⟩
    exact ⟨ε, hε, fun s hs => by rw [hεs s hs]⟩

/-! ### Hitting times of admissible targets -/

omit mΩ in
/-- At a regular outcome and for an admissible target, `{τ ≤ t}` for the hitting time
`τ = min{s ≥ t₀ : X_s ∈ S}` is decided by `X_t` and by the values of `X` at the points of a
dense set `D` in `[t₀, t)`.  This is what makes hitting times stopping times of the natural
filtration. -/
lemma hittingAfter_le_iff_of_rightRegular {ω : Ω} (hω : RightRegularAt X ω)
    {S : Set (Option V)} (hS : AdmissibleTarget S) {D : Set ℝ≥0} (hD : Dense D)
    {t₀ t : ℝ≥0} (ht : t₀ ≤ t) :
    hittingAfter X S t₀ ω ≤ t ↔ X t ω ∈ S ∨ ∃ d ∈ D, t₀ ≤ d ∧ d < t ∧ X d ω ∈ S := by
  constructor
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt
      right
      obtain ⟨ε, hε, hεs⟩ := exists_Ico_iff_mem_of_rightRegular hω hS j
      have hjm : j < min (j + ε) t := lt_min (lt_add_of_pos_right j hε) hj.2
      obtain ⟨d, hdD, hjd, hdlt⟩ := hD.exists_between hjm
      refine ⟨d, hdD, hj.1.trans hjd.le, lt_of_lt_of_le hdlt (min_le_right _ _), ?_⟩
      exact (hεs d ⟨hjd.le, lt_of_lt_of_le hdlt (min_le_left _ _)⟩).2 hjS
    · left
      by_contra hnot
      obtain ⟨ε, hε, hεs⟩ := exists_Ico_iff_mem_of_rightRegular hω hS t
      have hlt' : hittingAfter X S t₀ ω < ((t + ε : ℝ≥0) : WithTop ℝ≥0) := by
        rw [heq]; exact WithTop.coe_lt_coe.2 (lt_add_of_pos_right t hε)
      obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt'
      have htj : t ≤ j := by
        by_contra hlt2
        exact notMem_of_lt_hittingAfter
          (by rw [heq]; exact WithTop.coe_lt_coe.2 (not_le.1 hlt2)) hj.1 hjS
      exact hnot ((hεs j ⟨htj, hj.2⟩).1 hjS)
  · rintro (h | ⟨d, _, hd₀, hdt, hdS⟩)
    · exact hittingAfter_le_of_mem ht h
    · exact (hittingAfter_le_of_mem hd₀ hdS).trans (WithTop.coe_le_coe.2 hdt.le)

omit mΩ in
/-- At a regular outcome, a finite hitting time of an admissible target is attained. -/
lemma mem_of_hittingAfter_eq_of_rightRegular {ω : Ω} (hω : RightRegularAt X ω)
    {S : Set (Option V)} (hS : AdmissibleTarget S) {t₀ j : ℝ≥0}
    (h : hittingAfter X S t₀ ω = j) : X j ω ∈ S := by
  obtain ⟨D, -, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have ht₀ : t₀ ≤ j := WithTop.coe_le_coe.1 (h ▸ le_hittingAfter ω)
  rcases (hittingAfter_le_iff_of_rightRegular hω hS hDd ht₀).1 h.le with hj | ⟨d, _, hd₀, hdj, hdS⟩
  · exact hj
  · exact absurd (hittingAfter_le_of_mem hd₀ hdS) (by rw [h]; exact not_le.2 (WithTop.coe_lt_coe.2 hdj))

/-- The first time `t ≥ σ` at which `X_t ∈ S`, for a random start `σ` (`⊤` on `{σ = ⊤}`).
This is `min{t ≥ σ : X_t ∈ S}` of (3.31). -/
noncomputable def hitAfter (X : ℝ≥0 → Ω → Option V) (S : Set (Option V))
    (σ : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  WithTop.recTopCoe ⊤ (fun t₀ => hittingAfter X S t₀ ω) (σ ω)

variable {S : Set (Option V)} {σ : Ω → WithTop ℝ≥0}

omit mΩ in
lemma hitAfter_top {ω : Ω} (h : σ ω = ⊤) : hitAfter X S σ ω = ⊤ := by
  rw [hitAfter, h]; rfl

omit mΩ in
lemma hitAfter_coe {ω : Ω} {t₀ : ℝ≥0} (h : σ ω = t₀) :
    hitAfter X S σ ω = hittingAfter X S t₀ ω := by
  rw [hitAfter, h]; rfl

omit mΩ in
lemma le_hitAfter (ω : Ω) : σ ω ≤ hitAfter X S σ ω := by
  cases h : σ ω with
  | top => rw [hitAfter_top h]
  | coe t₀ => rw [hitAfter_coe h]; exact le_hittingAfter ω

omit mΩ in
/-- `hittingAfter` with deterministic start `t₀` is `hitAfter` with constant start. -/
lemma hitAfter_const (t₀ : ℝ≥0) : hitAfter X S (fun _ => (t₀ : WithTop ℝ≥0)) = hittingAfter X S t₀ :=
  funext fun _ => hitAfter_coe rfl

omit mΩ in
/-- The a.s. description of `{hitAfter X S σ ≤ t}` at a regular outcome. -/
lemma hitAfter_le_iff_of_rightRegular {ω : Ω} (hω : RightRegularAt X ω)
    (hS : AdmissibleTarget S) {D : Set ℝ≥0} (hD : Dense D) (t : ℝ≥0) :
    hitAfter X S σ ω ≤ t ↔
      σ ω ≤ t ∧ (X t ω ∈ S ∨ ∃ d ∈ D, σ ω ≤ d ∧ d < t ∧ X d ω ∈ S) := by
  cases h : σ ω with
  | top =>
    rw [hitAfter_top h]
    exact iff_of_false (WithTop.not_top_le_coe t) fun h' => WithTop.not_top_le_coe t h'.1
  | coe t₀ =>
    rw [hitAfter_coe h]
    by_cases ht : t₀ ≤ t
    · rw [hittingAfter_le_iff_of_rightRegular hω hS hD ht]
      simp only [WithTop.coe_le_coe, ht, true_and]
    · have : ¬ hittingAfter X S t₀ ω ≤ t := fun hle =>
        ht (WithTop.coe_le_coe.1 ((le_hittingAfter ω).trans hle))
      simp only [this, WithTop.coe_le_coe, ht, false_and]

omit mΩ in
/-- `{X_t ∈ S}` belongs to `σ(X_s : s ≤ t)`. -/
lemma measurableSet_pastSigma_eval (t : ℝ≥0) (S : Set (Option V)) :
    MeasurableSet[pastSigma X t] {ω | X t ω ∈ S} :=
  measurableSet_pastSigma_iff.2
    ⟨{f | f ⟨t, Set.mem_Iic.2 le_rfl⟩ ∈ S}, measurable_pi_apply _ (measurableSet_option _), rfl⟩

/-- **Hitting times are stopping times up to null sets.**  If `σ` is a stopping time of the
completed natural filtration and `S` is admissible, then so is `hitAfter X S σ`, under
right continuity (ii)+(R). -/
theorem isAEStoppingTime_hitAfter (hX : ∀ t, Measurable (X t)) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (hS : AdmissibleTarget S)
    (hσ : IsAEStoppingTime (naturalFiltration X hX) P σ) :
    IsAEStoppingTime (naturalFiltration X hX) P (hitAfter X S σ) := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  choose G hG hGe using hσ
  intro t
  refine ⟨G t ∩ ({ω | X t ω ∈ S} ∪ ⋃ p : {d : D // (d.1 : ℝ≥0) < t},
    (G p.1 ∩ {ω | X p.1 ω ∈ S})), ?_, ?_⟩
  · refine (hG t).inter (MeasurableSet.union (measurableSet_pastSigma_eval t S)
      (MeasurableSet.iUnion fun p => pastSigma_mono X p.2.le _ ?_))
    exact (hG p.1).inter (measurableSet_pastSigma_eval _ S)
  · have hK : {ω | hitAfter X S σ ω ≤ t} =ᵐ[P] {ω | σ ω ≤ (t : WithTop ℝ≥0)} ∩
        ({ω | X t ω ∈ S} ∪ ⋃ p : {d : D // (d.1 : ℝ≥0) < t},
          ({ω | σ ω ≤ ((p.1 : ℝ≥0) : WithTop ℝ≥0)} ∩ {ω | X p.1 ω ∈ S})) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [ae_rightRegularAt hii hR] with ω hω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_union, mem_iUnion]
      rw [hitAfter_le_iff_of_rightRegular hω hS hDd t]
      refine and_congr_right fun _ => or_congr_right ?_
      constructor
      · rintro ⟨d, hd, h1, h2, h3⟩
        exact ⟨⟨⟨d, hd⟩, h2⟩, h1, h3⟩
      · rintro ⟨⟨⟨d, hd⟩, h2⟩, h1, h3⟩
        exact ⟨d, hd, h1, h2, h3⟩
    refine hK.trans ?_
    exact ae_eq_set_inter (hGe t) (ae_eq_set_union EventuallyEqSet.rfl
      (EventuallyEqSet.countable_iUnion fun p => ae_eq_set_inter (hGe p.1) EventuallyEqSet.rfl))

open scoped Classical in
/-- The measurable candidate for `hitAfter X S σ'`: the infimum over the points `d` of a
countable dense set with `σ' ≤ d` and `X_d ∈ S`. -/
noncomputable def denseHitAfter (X : ℝ≥0 → Ω → Option V) (S : Set (Option V))
    (σ' : Ω → WithTop ℝ≥0) (D : Set ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ d : D, if σ' ω ≤ ((d.1 : ℝ≥0) : WithTop ℝ≥0) ∧ X d.1 ω ∈ S then ((d.1 : ℝ≥0) : WithTop ℝ≥0)
    else ⊤

lemma measurable_denseHitAfter (hX : ∀ t, Measurable (X t)) {σ' : Ω → WithTop ℝ≥0}
    (hσ' : Measurable σ') {D : Set ℝ≥0} (hD : D.Countable) :
    Measurable (denseHitAfter X S σ' D) := by
  classical
  have : Countable D := hD.to_subtype
  refine Measurable.iInf fun d => Measurable.ite ?_ measurable_const measurable_const
  exact (hσ' measurableSet_Iic).inter (hX _ (measurableSet_option _))

omit mΩ in
/-- `x ≤ j` in `[0,∞]` as soon as `x ≤ c` for every `c > j`. -/
lemma WithTop.le_coe_of_forall_lt {x : WithTop ℝ≥0} {j : ℝ≥0}
    (h : ∀ c : ℝ≥0, j < c → x ≤ (c : WithTop ℝ≥0)) : x ≤ (j : WithTop ℝ≥0) := by
  cases x with
  | top => exact absurd (h (j + 1) (lt_add_one j)) (WithTop.not_top_le_coe _)
  | coe a =>
    rw [WithTop.coe_le_coe]
    exact le_of_forall_gt_imp_ge_of_dense fun c hc => WithTop.coe_le_coe.1 (h c hc)

omit mΩ in
/-- At a regular outcome with `σ = σ'`, the hitting time equals its measurable candidate. -/
lemma hitAfter_eq_denseHitAfter_of_rightRegular {ω : Ω} (hω : RightRegularAt X ω)
    (hS : AdmissibleTarget S) {σ' : Ω → WithTop ℝ≥0} (hσσ' : σ ω = σ' ω)
    {D : Set ℝ≥0} (hDd : Dense D) :
    hitAfter X S σ ω = denseHitAfter X S σ' D ω := by
  classical
  cases h : σ ω with
  | top =>
    rw [hitAfter_top h]
    have h' : σ' ω = ⊤ := hσσ' ▸ h
    refine (iInf_eq_top.2 fun d => ?_).symm
    split_ifs with hd
    · exact absurd (h' ▸ hd.1) (WithTop.not_top_le_coe _)
    · rfl
  | coe t₀ =>
    rw [hitAfter_coe h]
    have h' : σ' ω = t₀ := hσσ' ▸ h
    apply le_antisymm
    · refine le_iInf fun d => ?_
      split_ifs with hd
      · exact hittingAfter_le_of_mem (WithTop.coe_le_coe.1 (h' ▸ hd.1)) hd.2
      · exact le_top
    · cases hj : hittingAfter X S t₀ ω with
      | top => exact le_top
      | coe j =>
        have hjS : X j ω ∈ S := mem_of_hittingAfter_eq_of_rightRegular hω hS hj
        have ht₀j : t₀ ≤ j := WithTop.coe_le_coe.1 (hj ▸ le_hittingAfter ω)
        obtain ⟨ε, hε, hεs⟩ := exists_Ico_iff_mem_of_rightRegular hω hS j
        refine WithTop.le_coe_of_forall_lt fun c hc => ?_
        have hjm : j < min (j + ε) c := lt_min (lt_add_of_pos_right j hε) hc
        obtain ⟨d, hdD, hjd, hdlt⟩ := hDd.exists_between hjm
        have hdS : X d ω ∈ S :=
          (hεs d ⟨hjd.le, lt_of_lt_of_le hdlt (min_le_left _ _)⟩).2 hjS
        have hle : denseHitAfter X S σ' D ω ≤ ((d : ℝ≥0) : WithTop ℝ≥0) := by
          refine iInf_le_of_le ⟨d, hdD⟩ ?_
          rw [ite_eq_left_of_eq_true _ _
            (eq_true ⟨by rw [h']; exact WithTop.coe_le_coe.2 (ht₀j.trans hjd.le), hdS⟩)]
        exact hle.trans (WithTop.coe_le_coe.2 (lt_of_lt_of_le hdlt (min_le_right _ _)).le)

/-- **Hitting times are random variables**: `hitAfter X S σ` is a.e.-measurable for
a.e.-measurable `σ`, under right continuity (ii)+(R). -/
theorem aemeasurable_hitAfter (hX : ∀ t, Measurable (X t)) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (hS : AdmissibleTarget S) (hσ : AEMeasurable σ P) :
    AEMeasurable (hitAfter X S σ) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  refine ⟨denseHitAfter X S (hσ.mk σ) D, measurable_denseHitAfter hX hσ.measurable_mk hDc, ?_⟩
  filter_upwards [ae_rightRegularAt hii hR, hσ.ae_eq_mk] with ω hω hσω
  exact hitAfter_eq_denseHitAfter_of_rightRegular hω hS hσω hDd

/-! ### The exit and hitting times of properties (iii) and (vi) -/

omit mΩ in
lemma exitTime_eq_hitAfter (z : V) :
    exitTime X z = hitAfter X {s | s ≠ some z} (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) :=
  (hitAfter_const 0).symm

omit mΩ in
lemma hittingTime_eq_hitAfter (A : Finset V) :
    hittingTime X A = hitAfter X (some '' (A : Set V)) (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) :=
  (hitAfter_const 0).symm

lemma isAEStoppingTime_const (hX : ∀ t, Measurable (X t)) (t₀ : ℝ≥0) :
    IsAEStoppingTime (naturalFiltration X hX) P (fun _ => (t₀ : WithTop ℝ≥0)) := by
  intro t
  by_cases h : t₀ ≤ t
  · have hs : {ω : Ω | (fun _ : Ω => (t₀ : WithTop ℝ≥0)) ω ≤ (t : WithTop ℝ≥0)} = univ :=
      Set.eq_univ_of_forall fun _ => WithTop.coe_le_coe.2 h
    exact ⟨univ, @MeasurableSet.univ Ω (naturalFiltration X hX t), hs ▸ EventuallyEqSet.rfl⟩
  · have hs : {ω : Ω | (fun _ : Ω => (t₀ : WithTop ℝ≥0)) ω ≤ (t : WithTop ℝ≥0)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun _ hω => h (WithTop.coe_le_coe.1 hω)
    exact ⟨∅, @MeasurableSet.empty Ω (naturalFiltration X hX t), hs ▸ EventuallyEqSet.rfl⟩

/-- The exit time `τ = min{t > 0 : X_t ≠ z}` of property (iii) is a stopping time of the
completed natural filtration. -/
theorem isAEStoppingTime_exitTime (hX : ∀ t, Measurable (X t)) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (z : V) :
    IsAEStoppingTime (naturalFiltration X hX) P (exitTime X z) := by
  rw [exitTime_eq_hitAfter]
  exact isAEStoppingTime_hitAfter hX hii hR (admissibleTarget_ne z) (isAEStoppingTime_const hX 0)

/-- The exit time of property (iii) is a random variable. -/
theorem aemeasurable_exitTime (hX : ∀ t, Measurable (X t)) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (z : V) : AEMeasurable (exitTime X z) P := by
  rw [exitTime_eq_hitAfter]
  exact aemeasurable_hitAfter hX hii hR (admissibleTarget_ne z) aemeasurable_const

/-- The hitting time `τ = min{t ≥ 0 : X_t ∈ A}` of property (vi) is a stopping time of the
completed natural filtration. -/
theorem isAEStoppingTime_hittingTime (hX : ∀ t, Measurable (X t)) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (A : Finset V) :
    IsAEStoppingTime (naturalFiltration X hX) P (hittingTime X A) := by
  rw [hittingTime_eq_hitAfter]
  exact isAEStoppingTime_hitAfter hX hii hR (admissibleTarget_image A)
    (isAEStoppingTime_const hX 0)

/-- The hitting time of property (vi) is a random variable. -/
theorem aemeasurable_hittingTime (hX : ∀ t, Measurable (X t)) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (A : Finset V) : AEMeasurable (hittingTime X A) P := by
  rw [hittingTime_eq_hitAfter]
  exact aemeasurable_hitAfter hX hii hR (admissibleTarget_image A) aemeasurable_const


/-! ### Closure properties of the stopped σ-algebra up to null sets -/

section stoppedSigma

variable {ℱ : Filtration ℝ≥0 mΩ} {τ ρ : Ω → WithTop ℝ≥0} {F F' : Set Ω}

lemma ae_eq_set_countable_iInter {ι : Sort*} [Countable ι] {s t : ι → Set Ω}
    (h : ∀ i, s i =ᵐ[P] t i) : (⋂ i, s i) =ᵐ[P] ⋂ i, t i := by
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_all_iff.2 fun i => Filter.eventuallyEqSet_iff.1 (h i)] with ω hω
  simp only [mem_iInter]
  exact forall_congr' hω

lemma AEMeasurableSetStopped.compl (hτ : IsAEStoppingTime ℱ P τ)
    (hF : AEMeasurableSetStopped ℱ P τ F) : AEMeasurableSetStopped ℱ P τ Fᶜ := by
  intro t
  obtain ⟨G, hG, hGe⟩ := hτ t
  obtain ⟨G', hG', hG'e⟩ := hF t
  refine ⟨G \ G', hG.diff hG', ?_⟩
  have : Fᶜ ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} =
      {ω | τ ω ≤ (t : WithTop ℝ≥0)} \ (F ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) := by
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq]
    exact ⟨fun h => ⟨h.2, fun h' => h.1 h'.1⟩, fun h => ⟨fun h' => h.2 ⟨h', h.1⟩, h.1⟩⟩
  rw [this]
  exact EventuallyEqSet.diff hGe hG'e

lemma AEMeasurableSetStopped.iUnion {ι : Sort*} [Countable ι] {F : ι → Set Ω}
    (hF : ∀ i, AEMeasurableSetStopped ℱ P τ (F i)) :
    AEMeasurableSetStopped ℱ P τ (⋃ i, F i) := by
  intro t
  choose G hG hGe using fun i => hF i t
  refine ⟨⋃ i, G i, MeasurableSet.iUnion hG, ?_⟩
  rw [Set.iUnion_inter]
  exact EventuallyEqSet.countable_iUnion hGe

lemma AEMeasurableSetStopped.inter (hF : AEMeasurableSetStopped ℱ P τ F)
    (hF' : AEMeasurableSetStopped ℱ P τ F') : AEMeasurableSetStopped ℱ P τ (F ∩ F') := by
  intro t
  obtain ⟨G, hG, hGe⟩ := hF t
  obtain ⟨G', hG', hG'e⟩ := hF' t
  refine ⟨G ∩ G', hG.inter hG', ?_⟩
  have : F ∩ F' ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} =
      (F ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) ∩ (F' ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) := by
    ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
  rw [this]
  exact ae_eq_set_inter hGe hG'e

/-- A set of the stopped σ-algebra of `τ` is also in that of any later stopping time `ρ ≥ τ`
(the standard monotonicity `𝓕_τ ⊆ 𝓕_ρ`). -/
lemma AEMeasurableSetStopped.mono (hF : AEMeasurableSetStopped ℱ P τ F)
    (hρ : IsAEStoppingTime ℱ P ρ) (hle : ∀ ω, τ ω ≤ ρ ω) : AEMeasurableSetStopped ℱ P ρ F := by
  intro t
  obtain ⟨G, hG, hGe⟩ := hF t
  obtain ⟨G', hG', hG'e⟩ := hρ t
  refine ⟨G ∩ G', hG.inter hG', ?_⟩
  have : F ∩ {ω | ρ ω ≤ (t : WithTop ℝ≥0)} =
      (F ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) ∩ {ω | ρ ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.1, (hle ω).trans h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [this]
  exact ae_eq_set_inter hGe hG'e

end stoppedSigma

/-! ### The stopped position `X_τ` is measurable for the stopped σ-algebra (up to null sets) -/

omit mΩ in
/-- `{τ < t}` through a dense set. -/
lemma setOf_lt_eq_iUnion {D : Set ℝ≥0} (hD : Dense D) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    {ω | τ ω < (t : WithTop ℝ≥0)} =
      ⋃ p : {d : D // (d.1 : ℝ≥0) < t}, {ω | τ ω ≤ ((p.1.1 : ℝ≥0) : WithTop ℝ≥0)} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    cases hτ : τ ω with
    | top => exact absurd (hτ ▸ h) not_top_lt
    | coe a =>
      have ha : a < t := WithTop.coe_lt_coe.1 (hτ ▸ h)
      obtain ⟨d, hdD, had, hdt⟩ := hD.exists_between ha
      exact ⟨⟨⟨d, hdD⟩, hdt⟩, WithTop.coe_le_coe.2 had.le⟩
  · rintro ⟨⟨⟨d, hdD⟩, hdt⟩, h⟩
    exact lt_of_le_of_lt h (WithTop.coe_lt_coe.2 hdt)

/-- For a stopping time up to null sets, `{τ < q}` is a.s. in `ℱ_q`. -/
lemma exists_pastSigma_lt (hX : ∀ t, Measurable (X t)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ) {D : Set ℝ≥0} (hDc : D.Countable)
    (hDd : Dense D) (q : ℝ≥0) :
    ∃ G, MeasurableSet[pastSigma X q] G ∧ {ω | τ ω < (q : WithTop ℝ≥0)} =ᵐ[P] G := by
  have : Countable D := hDc.to_subtype
  choose G hG hGe using hτ
  refine ⟨⋃ p : {d : D // (d.1 : ℝ≥0) < q}, G p.1,
    MeasurableSet.iUnion fun p => pastSigma_mono X p.2.le _ (hG p.1), ?_⟩
  rw [setOf_lt_eq_iUnion hDd]
  exact EventuallyEqSet.countable_iUnion fun p => hGe p.1

/-- **The stopped position is stopped-measurable.**  For a stopping time `τ` up to null sets
and a vertex `x`, the event `{X_τ = x}` belongs to the stopped σ-algebra up to null sets,
under right continuity (ii)+(R).  This is the classical fact that `X_τ` is
`𝓕_τ`-measurable for a right-continuous adapted process. -/
theorem aemeasurableSetStopped_stoppedValue_eq (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ) (x : V) :
    AEMeasurableSetStopped (naturalFiltration X hX) P τ {ω | stoppedValue X τ ω = some x} := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  choose G hG hGe using hτ
  choose G' hG' hG'e using exists_pastSigma_lt hX (fun t => ⟨G t, hG t, hGe t⟩) hDc hDd
  intro t
  refine ⟨({ω | X t ω = some x} ∩ (G t \ G' t)) ∪
    ⋃ q : {d : D // (d.1 : ℝ≥0) < t}, (G' q.1 ∩
      ⋂ d : {d : D // (d.1 : ℝ≥0) < q.1}, ((G' d.1)ᶜ ∪ {ω | X d.1 ω = some x})), ?_, ?_⟩
  · refine MeasurableSet.union ((measurableSet_pastSigma_eval t {some x}).inter ((hG t).diff (hG' t)))
      (MeasurableSet.iUnion fun q => (pastSigma_mono X q.2.le _ (hG' q.1)).inter
        (MeasurableSet.iInter fun d => MeasurableSet.union ?_ ?_))
    · exact pastSigma_mono X (d.2.le.trans q.2.le) _ (hG' d.1).compl
    · exact pastSigma_mono X (d.2.le.trans q.2.le) _ (measurableSet_pastSigma_eval d.1.1 {some x})
  · have hK : {ω | stoppedValue X τ ω = some x} ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} =ᵐ[P]
        ({ω | X t ω = some x} ∩
          ({ω | τ ω ≤ (t : WithTop ℝ≥0)} \ {ω | τ ω < (t : WithTop ℝ≥0)})) ∪
        ⋃ q : {d : D // (d.1 : ℝ≥0) < t}, ({ω | τ ω < ((q.1.1 : ℝ≥0) : WithTop ℝ≥0)} ∩
          ⋂ d : {d : D // (d.1 : ℝ≥0) < q.1},
            ({ω | τ ω < ((d.1.1 : ℝ≥0) : WithTop ℝ≥0)}ᶜ ∪ {ω | X d.1 ω = some x})) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [ae_rightRegularAt hii hR] with ω hω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff, mem_iUnion, mem_iInter,
        mem_compl_iff]
      constructor
      · rintro ⟨hval, hle⟩
        cases hτ : τ ω with
        | top => exact absurd (hτ ▸ hle) (WithTop.not_top_le_coe t)
        | coe a =>
          have hval' : X a ω = some x := by rwa [stoppedValue_of_eq hτ] at hval
          have hat : a ≤ t := WithTop.coe_le_coe.1 (hτ ▸ hle)
          rcases hat.lt_or_eq with hlt | rfl
          · right
            obtain ⟨ε, hε, hεs⟩ := hω.1 a ⟨x, hval'⟩
            have ham : a < min (a + ε) t := lt_min (lt_add_of_pos_right a hε) hlt
            obtain ⟨q, hqD, haq, hqm⟩ := hDd.exists_between ham
            refine ⟨⟨⟨q, hqD⟩, lt_of_lt_of_le hqm (min_le_right _ _)⟩,
              WithTop.coe_lt_coe.2 haq, fun d => ?_⟩
            by_cases had : (a : WithTop ℝ≥0) < ((d.1.1 : ℝ≥0) : WithTop ℝ≥0)
            · right
              have had' : a < d.1.1 := WithTop.coe_lt_coe.1 had
              rw [hεs d.1.1 ⟨had'.le, lt_of_lt_of_le (d.2.trans hqm) (min_le_left _ _)⟩]
              exact hval'
            · exact Or.inl had
          · left
            exact ⟨hval', le_rfl, fun h => lt_irrefl _ h⟩
      · rintro (⟨hXt, hle, hnlt⟩ | ⟨q, hq, hall⟩)
        · have hτt : τ ω = t := le_antisymm hle (not_lt.1 hnlt)
          exact ⟨by rw [stoppedValue_of_eq hτt]; exact hXt, hle⟩
        · cases hτ : τ ω with
          | top => exact absurd (hτ ▸ hq) (not_top_lt)
          | coe a =>
            have haq : a < q.1.1 := WithTop.coe_lt_coe.1 (hτ ▸ hq)
            have hval' : X a ω = some x := by
              -- the dense points of `(a, q)` all carry the value `x`
              have hdense : ∀ d : D, a < d.1 → d.1 < q.1.1 → X d.1 ω = some x := by
                intro d had hdq
                rcases hall ⟨d, hdq⟩ with h | h
                · exact absurd (WithTop.coe_lt_coe.2 had) (hτ ▸ h)
                · exact h
              by_cases hnone : X a ω = none
              · obtain ⟨ε, hε, hεs⟩ := hω.2 a hnone x
                have ham : a < min (a + ε) q.1.1 := lt_min (lt_add_of_pos_right a hε) haq
                obtain ⟨d, hdD, had, hdm⟩ := hDd.exists_between ham
                exact absurd (hdense ⟨d, hdD⟩ had (lt_of_lt_of_le hdm (min_le_right _ _)))
                  (hεs d ⟨had, lt_of_lt_of_le hdm (min_le_left _ _)⟩)
              · obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.1 hnone
                obtain ⟨ε, hε, hεs⟩ := hω.1 a ⟨y', hy'⟩
                have ham : a < min (a + ε) q.1.1 := lt_min (lt_add_of_pos_right a hε) haq
                obtain ⟨d, hdD, had, hdm⟩ := hDd.exists_between ham
                have h1 := hdense ⟨d, hdD⟩ had (lt_of_lt_of_le hdm (min_le_right _ _))
                rw [hεs d ⟨had.le, lt_of_lt_of_le hdm (min_le_left _ _)⟩] at h1
                exact h1
            refine ⟨by rw [stoppedValue_of_eq hτ]; exact hval', ?_⟩
            exact WithTop.coe_le_coe.2 (haq.trans q.2).le
    refine hK.trans ?_
    refine ae_eq_set_union (ae_eq_set_inter EventuallyEqSet.rfl (EventuallyEqSet.diff (hGe t) (hG'e t)))
      (EventuallyEqSet.countable_iUnion fun q => ae_eq_set_inter (hG'e q.1)
        (ae_eq_set_countable_iInter fun d => ae_eq_set_union (hG'e d.1).compl EventuallyEqSet.rfl))

/-! ### The recursion (3.31) -/

open scoped Classical in
/-- One step of (3.31): from the stopping time `σ`, the exit time from the current position
if it lies in `Gn`, otherwise the hitting time of `Gn`. -/
noncomputable def nextStep (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (σ : Ω → WithTop ℝ≥0)
    (ω : Ω) : WithTop ℝ≥0 :=
  if stoppedValue X σ ω ∈ some '' (Gn : Set V) then
    hitAfter X {s | s ≠ stoppedValue X σ ω} σ ω
  else hitAfter X (some '' (Gn : Set V)) σ ω

/-- The stopping times `tⁿ_j` of (3.31): `tⁿ_0 = 0`, `tⁿ_{j+1} = nextStep tⁿ_j`. -/
noncomputable def stepTime (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)
  | j + 1 => nextStep X Gn (stepTime X Gn j)

/-- The exit time `min{t ≥ σ : X_t ≠ X_σ}` from the position at `σ`; the paper's holding
time `Tⁿ_j` is `exitAfter X tⁿ_j − tⁿ_j`. -/
noncomputable def exitAfter (X : ℝ≥0 → Ω → Option V) (σ : Ω → WithTop ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 :=
  hitAfter X {s | s ≠ stoppedValue X σ ω} σ ω

omit mΩ in
lemma le_nextStep (Gn : Finset V) (σ : Ω → WithTop ℝ≥0) (ω : Ω) : σ ω ≤ nextStep X Gn σ ω := by
  unfold nextStep
  split_ifs <;> exact le_hitAfter ω

omit mΩ in
lemma nextStep_eq_of_eq {Gn : Finset V} {σ : Ω → WithTop ℝ≥0} {ω : Ω} {x : V} (hx : x ∈ Gn)
    (h : stoppedValue X σ ω = some x) :
    nextStep X Gn σ ω = hitAfter X {s | s ≠ some x} σ ω := by
  rw [nextStep, ite_eq_left_of_eq_true _ _ (eq_true (by rw [h]; exact ⟨x, Finset.mem_coe.2 hx, rfl⟩)), h]

omit mΩ in
lemma nextStep_eq_of_notMem {Gn : Finset V} {σ : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : stoppedValue X σ ω ∉ some '' (Gn : Set V)) :
    nextStep X Gn σ ω = hitAfter X (some '' (Gn : Set V)) σ ω := by
  rw [nextStep, ite_eq_right_of_eq_false _ _ (eq_false h)]

instance instMeasurableSingletonClassOption : MeasurableSingletonClass (Option V) :=
  ⟨fun _ => measurableSet_option _⟩

/-- `nextStep` of a stopping time (up to null sets) is a stopping time (up to null sets). -/
theorem isAEStoppingTime_nextStep [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (Gn : Finset V) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsAEStoppingTime (naturalFiltration X hX) P σ) :
    IsAEStoppingTime (naturalFiltration X hX) P (nextStep X Gn σ) := by
  classical
  -- the pieces
  have hx : ∀ x : V, AEMeasurableSetStopped (naturalFiltration X hX) P σ
      {ω | stoppedValue X σ ω = some x} :=
    aemeasurableSetStopped_stoppedValue_eq hX hii hR hσ
  have hnot : AEMeasurableSetStopped (naturalFiltration X hX) P σ
      {ω | stoppedValue X σ ω ∉ some '' (Gn : Set V)} := by
    have : {ω | stoppedValue X σ ω ∉ some '' (Gn : Set V)} =
        (⋃ x : Gn, {ω | stoppedValue X σ ω = some (x.1 : V)})ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, mem_image, Finset.mem_coe]
      constructor
      · rintro h ⟨⟨x, hxG⟩, hx⟩; exact h ⟨x, hxG, hx.symm⟩
      · rintro h ⟨x, hxG, hx⟩; exact h ⟨⟨x, hxG⟩, hx.symm⟩
    rw [this]
    exact (AEMeasurableSetStopped.iUnion fun x : Gn => hx x.1).compl hσ
  have hexit : ∀ x : V, IsAEStoppingTime (naturalFiltration X hX) P
      (hitAfter X {s | s ≠ some x} σ) := fun x =>
    isAEStoppingTime_hitAfter hX hii hR (admissibleTarget_ne x) hσ
  have hhit : IsAEStoppingTime (naturalFiltration X hX) P (hitAfter X (some '' (Gn : Set V)) σ) :=
    isAEStoppingTime_hitAfter hX hii hR (admissibleTarget_image Gn) hσ
  intro t
  choose Gx hGx hGxe using fun x : Gn => (hx x).mono (hexit x) (fun ω => le_hitAfter ω) t
  choose Gn' hGn' hGn'e using hnot.mono hhit (fun ω => le_hitAfter ω) t
  choose Hx hHx hHxe using fun x : Gn => hexit x t
  obtain ⟨H', hH', hH'e⟩ := hhit t
  refine ⟨(⋃ x : Gn, Gx x ∩ Hx x) ∪ (Gn' ∩ H'),
    (MeasurableSet.iUnion fun x => (hGx x).inter (hHx x)).union (hGn'.inter hH'), ?_⟩
  have hdecomp : {ω | nextStep X Gn σ ω ≤ (t : WithTop ℝ≥0)} =
      (⋃ x : Gn, ({ω | stoppedValue X σ ω = some x} ∩
          {ω | hitAfter X {s | s ≠ some x} σ ω ≤ (t : WithTop ℝ≥0)}) ∩
        {ω | hitAfter X {s | s ≠ some x} σ ω ≤ (t : WithTop ℝ≥0)}) ∪
      (({ω | stoppedValue X σ ω ∉ some '' (Gn : Set V)} ∩
          {ω | hitAfter X (some '' (Gn : Set V)) σ ω ≤ (t : WithTop ℝ≥0)}) ∩
        {ω | hitAfter X (some '' (Gn : Set V)) σ ω ≤ (t : WithTop ℝ≥0)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff]
    by_cases hmem : stoppedValue X σ ω ∈ some '' (Gn : Set V)
    · obtain ⟨x, hxG, hxω⟩ := hmem
      rw [nextStep_eq_of_eq (Finset.mem_coe.1 hxG) hxω.symm]
      constructor
      · intro h; exact Or.inl ⟨⟨x, hxG⟩, ⟨hxω.symm, h⟩, h⟩
      · rintro (⟨⟨y, hyG⟩, ⟨hyω, hy⟩, -⟩ | ⟨⟨hn, -⟩, -⟩)
        · have : y = x := Option.some_inj.1 (hyω.symm.trans hxω.symm)
          subst this; exact hy
        · exact absurd ⟨x, hxG, hxω⟩ hn
    · rw [nextStep_eq_of_notMem hmem]
      constructor
      · intro h; exact Or.inr ⟨⟨hmem, h⟩, h⟩
      · rintro (⟨⟨x, hxG⟩, ⟨hxω, -⟩, -⟩ | ⟨⟨-, h⟩, -⟩)
        · exact absurd ⟨x, hxG, hxω.symm⟩ hmem
        · exact h
  rw [hdecomp]
  exact ae_eq_set_union (EventuallyEqSet.countable_iUnion fun x =>
      ae_eq_set_inter (hGxe x) (hHxe x)) (ae_eq_set_inter hGn'e hH'e)

/-- The stopped position `X_σ` is a random variable (for a.e.-measurable `σ`, under (ii)+(R)). -/
lemma aemeasurable_stoppedValue [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) {σ : Ω → WithTop ℝ≥0}
    (hσ : AEMeasurable σ P) : AEMeasurable (stoppedValue X σ) P := by
  have h := (measurable_pi_apply (0 : ℝ≥0)).comp_aemeasurable
    (aemeasurable_futureAt hX hii hR hσ.measurable_mk)
  have heq : futureAt X (hσ.mk σ) =ᵐ[P] futureAt X σ := by
    filter_upwards [hσ.ae_eq_mk] with ω hω
    funext s; simp only [futureAt, hω]
  refine (h.congr ?_)
  filter_upwards [heq] with ω hω
  show futureAt X (hσ.mk σ) ω 0 = stoppedValue X σ ω
  rw [hω, futureAt_apply_zero]

/-- `nextStep` of an a.e.-measurable stopping time is a.e.-measurable. -/
theorem aemeasurable_nextStep [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V)
    {σ : Ω → WithTop ℝ≥0} (hσ : AEMeasurable σ P) : AEMeasurable (nextStep X Gn σ) P := by
  classical
  -- the branch as a function of the current position
  let Φ : Option V → Ω → WithTop ℝ≥0 := fun a ω =>
    if a ∈ some '' (Gn : Set V) then hitAfter X {s | s ≠ a} σ ω
    else hitAfter X (some '' (Gn : Set V)) σ ω
  have hΦ : ∀ a, AEMeasurable (Φ a) P := by
    intro a
    by_cases ha : a ∈ some '' (Gn : Set V)
    · obtain ⟨x, hxG, hxa⟩ := ha
      have : Φ a = hitAfter X {s | s ≠ a} σ := by
        funext ω
        exact ite_eq_left_of_eq_true _ _ (eq_true ⟨x, hxG, hxa⟩)
      rw [this, ← hxa]
      exact aemeasurable_hitAfter hX hii hR (admissibleTarget_ne x) hσ
    · have : Φ a = hitAfter X (some '' (Gn : Set V)) σ := by
        funext ω
        exact ite_eq_right_of_eq_false _ _ (eq_false ha)
      rw [this]
      exact aemeasurable_hitAfter hX hii hR (admissibleTarget_image Gn) hσ
  have hval : AEMeasurable (stoppedValue X σ) P := aemeasurable_stoppedValue hX hii hR hσ
  -- measurable versions
  set g := hval.mk _ with hg
  have hΦm : Measurable fun p : Ω × Option V => (hΦ p.2).mk _ p.1 :=
    measurable_from_prod_countable_left fun a => (hΦ a).measurable_mk
  refine ⟨fun ω => (hΦ (g ω)).mk _ ω, hΦm.comp (measurable_id.prodMk hval.measurable_mk), ?_⟩
  filter_upwards [hval.ae_eq_mk, ae_all_iff.2 fun a => (hΦ a).ae_eq_mk] with ω hω hΦω
  have : nextStep X Gn σ ω = Φ (stoppedValue X σ ω) ω := by
    simp only [Φ, nextStep]
  rw [this, hω, ← hΦω]

/-- The times `tⁿ_j` of (3.31) are stopping times up to null sets and random variables. -/
theorem stepTime_isAEStoppingTime_aemeasurable [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V) (j : ℕ) :
    IsAEStoppingTime (naturalFiltration X hX) P (stepTime X Gn j) ∧
      AEMeasurable (stepTime X Gn j) P := by
  induction j with
  | zero => exact ⟨isAEStoppingTime_const hX 0, aemeasurable_const⟩
  | succ j ih =>
    exact ⟨isAEStoppingTime_nextStep hX hii hR Gn ih.1, aemeasurable_nextStep hX hii hR Gn ih.2⟩

/-! ### Lemma 3.10 at the times `tⁿ_j` -/

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}

/-- **The strong Markov property at `tⁿ_j`** (Section 3.4, Step 1, second paragraph): for a
process satisfying the properties of Theorem 1.6 and right continuous at `∞`, for every `j`
and `x ∈ VG`, on `{X̃_{tⁿ_j} = x}` the `P_z`-conditional law of `{X̃_{s+tⁿ_j}}_{s≥0}` given
`{X̃_s}_{s ≤ tⁿ_j}` is the law of `X̃` under `P_x`. -/
theorem stepTime_strongMarkov [Countable V] (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : RightContinuousAtInfty (𝓧.P z) 𝓧.X) (Gn : Finset V) (j : ℕ) (x : V)
    {F : Set 𝓧.Ω}
    (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) (stepTime 𝓧.X Gn j) F)
    {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩ futureAt 𝓧.X (stepTime 𝓧.X Gn j) ⁻¹' B) =
      𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) * 𝓧.law x B :=
  strongMarkov_completed h z hR
    (stepTime_isAEStoppingTime_aemeasurable 𝓧.measurable_X (h z).2.2.1 hR Gn j).2
    (stepTime_isAEStoppingTime_aemeasurable 𝓧.measurable_X (h z).2.2.1 hR Gn j).1 x hF hB

end Theorem16
end ReflectedWalk
