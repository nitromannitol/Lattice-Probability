/-
# The multiparameter `Lᵖ` maximal bound (`KrengelLpBall`): reduction and ℓ¹-ball geometry

This file is the start of the library-side attack on the second named gap of
`LatticeProb/Prob/AkcogluKrengelAE/BallMaximalLp.lean`, `KrengelLpBall d` (the multiparameter
`Lᵖ` maximal bound for `ℓ¹`-ball averages).  It does two things.

## 1. The Marcinkiewicz reduction

`KrengelLpBall d` follows from a multiparameter **weak-type `(1,1)`** input for the `ℓ¹`-ball
maximal, `KrengelLpBallWeakType d`, exactly as the one-parameter `BirkhoffLpMaximal` followed from
its weak type.  The layer-cake / Tonelli / Hölder step is the dimension-agnostic
`LatticeProb.marcinkiewicz_abstract` already proved in
`LatticeProb/Prob/AkcogluKrengelAE/BirkhoffLpMaximalProved.lean`.

## 2. The centred anchored-box maximal input and the ℓ¹-ball geometry

The multiparameter weak-type input is intended to come from the **centred anchored-box** maximal
inequality (`KrengelMaximalInputCentred` below).  The library's `AnchoredBoxMaximal`
(`AnchoredBoxMean.lean:28`) is *false as stated* (landed errata `dcf09c9`, `4dee008`), because the
anchored box `∏ᵢ [0, ⌈N cᵢ⌉)` has cardinality `∏ᵢ ⌈N cᵢ⌉`, which equals `N^d ∏ᵢ cᵢ` only
asymptotically; the `N = 1` witness refutes it.  The centred form normalises by the *actual* box
cardinality and subtracts the true mean `∫ h`, which removes the defect.

`KrengelMaximalInputCentred` is deliberately NOT called `AnchoredBoxMaximalCentred`: ds3 has
landed `LatticeProb.AnchoredBoxMaximalCentred` on branch `ds-errata` (tip
`b651026229c65fc4f734f697f045e457a9cd503d`), but on a separate worktree/branch that this branch
cannot import, and duplicating the name in the same namespace would recreate exactly the defect
the fleet is repairing (`AnchoredBoxMaximal` is declared twice, at `AnchoredBoxMean.lean:28` and
`AnchoredBoxMaximal.lean:37`).  This statement is to be identified with, and later replaced by,
`AnchoredBoxMaximalCentred` once both branches reach `main`; there must be exactly one such
declaration in `namespace LatticeProb`.

Note also that `AnchoredBoxMaximalCentred` is *named but not proved*: it is the open
multiparameter strong-`Lᵖ` maximal theorem.  The reduction here names it (in the shape of its
weak-type half) as the input, which is the right shape.

The geometric content proved here is:

* `anchoredBox_subset_l1Ball`: an anchored box lies inside an `ℓ¹` ball;
* `l1Ball_subset_boxFinset` / `card_l1Ball_le`: the `ℓ¹` ball lies inside the `ℓ∞` box
  `∏ᵢ [-⌈R⌉₊, ⌈R⌉₊]`, with cardinality at most `(2⌈R⌉₊+1)^d`;
* `orthantBox` and `boxFinset_eq_biUnion_orthantBox`: the `ℓ∞` box is the union of the `2^d`
  orthant boxes, each a translate of an anchored box, with total volume `(2⌈R⌉₊+1)^d`.

The cover constant in the pass from box averages to ball averages is `2^d · d!` (the `2^d` orthant
pieces times the simplex-to-cube volume ratio `d!`), independent of `R` and `N`; it is recorded in
`L1BallCoverTransfer`, the stated geometric transfer.  The tiling-to-average comparison of the
library's `UpperBound.lean:103` (`cubeRatio_le_gridAvg_add_defect`) is a *different* (grid)
tiling and is not directly the cover used here.

The geometry lemmas below are all fully proved; the only unproved inputs are the two named `Prop`s `KrengelMaximalInputCentred` and `L1BallCoverTransfer`.
-/
import LatticeProb.Prob.AkcogluKrengelAE.BirkhoffLpMaximalProved
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Walk.Range

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ENNReal NNReal

namespace LatticeProb

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-! ### The `ℓ¹`-ball maximal function and its weak type -/

/-- The `ℓ¹`-ball maximal function `Mf ω = ⨆_{1 ≤ R} avg (B¹_R(0)) (f ∘ T_·)(ω)`. -/
noncomputable def l1BallMax (T : Site d → Ω → Ω) (f : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (R : ℕ) (_ : 1 ≤ R), avg (l1Ball (0 : Site d) R) (fun y => f (T y ω))

/-- The multiparameter **weak-type `(1,1)`** input for the `ℓ¹`-ball maximal. -/
def KrengelLpBallWeakType (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (T : Site d → Ω → Ω),
      (∀ x, MeasurePreserving (T x) μ μ) →
      (∀ x y, T (x + y) = T x ∘ T y) →
      ∀ f : Ω → ℝ≥0∞, Measurable f →
        ∀ t : ℝ, 0 < t →
          ENNReal.ofReal t * μ {ω | ENNReal.ofReal t < l1BallMax T f ω} ≤
            ∫⁻ ω, ({ω | ENNReal.ofReal t < l1BallMax T f ω}.indicator f) ω ∂μ

/-- Measurability of the `ℓ¹`-ball maximal function. -/
theorem measurable_l1BallMax {T : Site d → Ω → Ω} (hT : ∀ x, Measurable (T x))
    {f : Ω → ℝ≥0∞} (hf : Measurable f) : Measurable (l1BallMax T f) := by
  refine Measurable.iSup fun R => ?_
  refine Measurable.iSup_Prop (1 ≤ R) ?_
  exact measurable_const.mul (Finset.measurable_sum _ fun y _ => hf.comp (hT y))

/-- **The Marcinkiewicz reduction.** -/
theorem KrengelLpBall_of_weakType (hweak : KrengelLpBallWeakType d) : KrengelLpBall d := by
  intro p hp
  refine ⟨(p / (p - 1)) ^ p, by positivity, ?_⟩
  intro Ω _ μ hprob T hT hadd f hf
  exact marcinkiewicz_abstract μ (l1BallMax T f) f p hp
    (measurable_l1BallMax (fun x => (hT x).measurable) hf) hf
    (hweak μ hprob T hT hadd f hf)

/-! ### The centred anchored-box maximal input -/

/-- The centred anchored-box average: the uniform average of `h` over `∏ᵢ [0, ⌈N cᵢ⌉)`, minus the
true mean `∫ h`. -/
noncomputable def anchoredBoxAvgCentred {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω → ℝ) (τ : Site d → Ω → Ω) (c : Fin d → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (((anchoredBox c N).card : ℝ))⁻¹ * ∑ x ∈ anchoredBox c N, h (τ x ω) - ∫ ω, h ω ∂μ

/-- **The centred anchored-box weak-type `(1,1)` input** (the true replacement for the false
`AnchoredBoxMaximal`).  To be identified with, and later replaced by,
`LatticeProb.AnchoredBoxMaximalCentred` (`AnchoredBoxMean.lean`, branch `ds-errata`) once both
branches reach `main`. -/
def KrengelMaximalInputCentred (d : ℕ) (c : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∀ t : ℝ, 0 < t →
        ENNReal.ofReal t * μ {ω | ENNReal.ofReal t <
            ⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgCentred μ h τ c N ω|} ≤
          ∫⁻ ω, ({ω | ENNReal.ofReal t <
            ⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgCentred μ h τ c N ω|}.indicator
              (fun ω => ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|)) ω ∂μ

/-! ### The `ℓ¹`-ball geometry against anchored boxes -/

omit [MeasurableSpace Ω] in
/-- **The ball contains an anchored box.** -/
theorem anchoredBox_subset_l1Ball (c : Fin d → ℝ) (N : ℕ) (hc : ∀ i, 0 ≤ c i) :
    anchoredBox c N ⊆ l1Ball (0 : Site d) (∑ i, (((⌈(N : ℝ) * c i⌉ : ℤ) : ℝ))) := by
  intro y hy
  have hybox : ∀ i, y i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * c i⌉ := by
    simpa only [anchoredBox, Fintype.mem_piFinset] using hy
  have hy0 : ∀ i, 0 ≤ y i := fun i => (Finset.mem_Ico.mp (hybox i)).1
  have hceil0 : ∀ i, (0 : ℤ) ≤ ⌈(N : ℝ) * c i⌉ :=
    fun i => Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) (hc i))
  set R : ℝ := ∑ i, (((⌈(N : ℝ) * c i⌉ : ℤ) : ℝ)) with hR
  rw [l1Ball, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro i
    rw [Finset.mem_Icc]
    simp only [Pi.zero_apply, zero_sub, zero_add]
    constructor
    · have : (0 : ℤ) ≤ y i := hy0 i
      omega
    · have hle : y i ≤ ∑ j, ⌈(N : ℝ) * c j⌉ :=
        le_trans (le_of_lt (Finset.mem_Ico.mp (hybox i)).2)
          (Finset.single_le_sum (fun j _ => hceil0 j) (Finset.mem_univ i))
      have hRle : ((∑ j, ⌈(N : ℝ) * c j⌉ : ℤ) : ℝ) ≤ (⌈R⌉₊ : ℝ) := by
        rw [hR]; push_cast; exact Nat.le_ceil _
      have : (y i : ℝ) ≤ (⌈R⌉₊ : ℝ) := le_trans (by exact_mod_cast hle) hRle
      exact_mod_cast this
  · rw [sub_zero]
    have hgn : ((graphNorm y : ℕ) : ℤ) = ∑ i, y i := by
      rw [graphNorm]
      push_cast
      exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hy0 i)
    have hle : (∑ i, y i) ≤ (∑ i, ⌈(N : ℝ) * c i⌉ : ℤ) :=
      Finset.sum_le_sum fun i _ => le_of_lt (Finset.mem_Ico.mp (hybox i)).2
    have hRsum : ((∑ i, ⌈(N : ℝ) * c i⌉ : ℤ) : ℝ) = R := by
      rw [hR]; push_cast; rfl
    calc ((graphNorm y : ℕ) : ℝ) = (((graphNorm y : ℕ) : ℤ) : ℝ) := by norm_cast
      _ = ((∑ i, y i : ℤ) : ℝ) := by rw [hgn]
      _ ≤ (((∑ i, ⌈(N : ℝ) * c i⌉ : ℤ)) : ℝ) := by exact_mod_cast hle
      _ = R := hRsum

omit [MeasurableSpace Ω] in
/-- **The ball is inside the `ℓ∞` box.** -/
theorem l1Ball_subset_boxFinset {R : ℝ} :
    l1Ball (0 : Site d) R ⊆ boxFinset (0 : Site d) ⌈R⌉₊ := by
  intro y hy
  rw [l1Ball, Finset.mem_filter] at hy
  obtain ⟨-, hnorm⟩ := hy
  refine mem_boxFinset_of_graphNorm_le ?_
  have h : ((graphNorm y : ℕ) : ℝ) ≤ R := by simpa using hnorm
  exact_mod_cast (le_trans h (Nat.le_ceil R))

omit [MeasurableSpace Ω] in
/-- The `ℓ¹` ball of radius `R` has cardinality at most `(2⌈R⌉₊+1)^d`. -/
theorem card_l1Ball_le {R : ℝ} :
    (l1Ball (0 : Site d) R).card ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
  calc (l1Ball (0 : Site d) R).card ≤ (boxFinset (0 : Site d) ⌈R⌉₊).card :=
        Finset.card_le_card l1Ball_subset_boxFinset
    _ = (2 * ⌈R⌉₊ + 1) ^ d := card_boxFinset_zero _

omit [MeasurableSpace Ω] in
/-- The `ℓ∞` box with side `2r+1` splits into the `2^d` orthant boxes. -/
def orthantBox (s : Fin d → Bool) (r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => if s i then Finset.Ico (0 : ℤ) (r + 1) else Finset.Ico (-(r : ℤ)) 0

omit [MeasurableSpace Ω] in
theorem mem_orthantBox {s : Fin d → Bool} {r : ℕ} {x : Site d} :
    x ∈ orthantBox s r ↔ ∀ i, x i ∈ (if s i then Finset.Ico (0 : ℤ) (r + 1)
      else Finset.Ico (-(r : ℤ)) 0) :=
  Fintype.mem_piFinset

omit [MeasurableSpace Ω] in
theorem card_orthantBox (s : Fin d → Bool) (r : ℕ) :
    (orthantBox s r).card = ∏ i, if s i then r + 1 else r := by
  rw [orthantBox, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : s i = true
  · simp [h, Int.card_Ico]
  · simp [h, Int.card_Ico]

omit [MeasurableSpace Ω] in
/-- **The `ℓ∞` box is the union of the `2^d` orthant boxes.** -/
theorem boxFinset_eq_biUnion_orthantBox (r : ℕ) :
    boxFinset (0 : Site d) r = Finset.univ.biUnion (fun s : Fin d → Bool => orthantBox s r) := by
  ext x
  rw [Finset.mem_biUnion, mem_boxFinset_iff]
  constructor
  · intro hx
    refine ⟨fun i => decide (0 ≤ x i), Finset.mem_univ _, ?_⟩
    rw [mem_orthantBox]
    intro i
    have hi : |x i| ≤ (r : ℤ) := by have := hx i; simpa using this
    have hle := abs_le.mp hi
    by_cases h : 0 ≤ x i
    · rw [if_pos (by simpa [decide_eq_true_iff] using h), Finset.mem_Ico]
      exact ⟨h, by omega⟩
    · rw [if_neg (by simp [h]), Finset.mem_Ico]
      push Not at h
      exact ⟨by omega, h⟩
  · rintro ⟨s, -, hx⟩
    rw [mem_orthantBox] at hx
    intro i
    have hi := hx i
    by_cases h : s i = true
    · rw [if_pos h, Finset.mem_Ico] at hi
      simp only [Pi.zero_apply, sub_zero]
      rw [abs_of_nonneg hi.1]; omega
    · rw [if_neg h, Finset.mem_Ico] at hi
      simp only [Pi.zero_apply, sub_zero]
      rw [abs_of_neg hi.2]; omega

/-! ### Cardinality of the `ℓ∞` box as the sum over orthant boxes -/

omit [MeasurableSpace Ω] in
/-- **Volume lower bound.**  The positive orthant box `{0 ≤ xᵢ ≤ R/d}` sits inside the `ℓ¹` ball
of radius `R`, so `(R/d + 1)^d ≤ (l1Ball 0 R).card`. -/
theorem orthantBox_true_subset_l1Ball (R : ℕ) :
    orthantBox (fun _ : Fin d => true) (R / d) ⊆ l1Ball (0 : Site d) R := by
  intro x hx
  have hxbox : ∀ i, x i ∈ Finset.Ico (0 : ℤ) ((R / d : ℕ) + 1) := by
    intro i
    have := (mem_orthantBox.mp hx) i
    simpa using this
  have hx0 : ∀ i, 0 ≤ x i := fun i => (Finset.mem_Ico.mp (hxbox i)).1
  have hxle : ∀ i, x i ≤ (R / d : ℤ) := fun i => by
    have := (Finset.mem_Ico.mp (hxbox i)).2; omega
  rw [l1Ball, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro i
    rw [Finset.mem_Icc]
    simp only [Pi.zero_apply, zero_sub, zero_add]
    constructor
    · have : (0 : ℤ) ≤ x i := hx0 i
      omega
    · have h1 : x i ≤ (R : ℤ) := by
        have := hxle i
        have : (R / d : ℤ) ≤ (R : ℤ) := by exact_mod_cast Nat.div_le_self R d
        omega
      have hRceil : (R : ℤ) ≤ (⌈((R : ℕ) : ℝ)⌉₊ : ℤ) := by
        exact_mod_cast Nat.le_ceil ((R : ℕ) : ℝ)
      omega
  · rw [sub_zero]
    have hgn : graphNorm x ≤ d * (R / d) := by
      rw [graphNorm]
      calc ∑ i, (x i).natAbs ≤ ∑ _i : Fin d, (R / d) :=
            Finset.sum_le_sum fun i _ => by
              have h1 : ((x i).natAbs : ℤ) = x i := Int.natAbs_of_nonneg (hx0 i)
              have h2 : ((x i).natAbs : ℤ) ≤ (R / d : ℤ) := by rw [h1]; exact hxle i
              exact_mod_cast h2
        _ = d * (R / d) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact_mod_cast (le_trans hgn (Nat.mul_div_le R d))

omit [MeasurableSpace Ω] in
theorem card_l1Ball_ge (R : ℕ) : (R / d + 1) ^ d ≤ (l1Ball (0 : Site d) R).card := by
  calc (R / d + 1) ^ d = (orthantBox (fun _ : Fin d => true) (R / d)).card := by
        rw [card_orthantBox]; simp
    _ ≤ (l1Ball (0 : Site d) R).card := Finset.card_le_card (orthantBox_true_subset_l1Ball R)

omit [MeasurableSpace Ω] in
/-- Membership in an orthant box, split by the sign choice in each coordinate. -/
theorem mem_orthantBox_iff {s : Fin d → Bool} {r : ℕ} {x : Site d} :
    x ∈ orthantBox s r ↔
      (∀ i, s i = true → 0 ≤ x i ∧ x i < (r : ℤ) + 1) ∧
      (∀ i, s i = false → -(r : ℤ) ≤ x i ∧ x i < 0) := by
  rw [mem_orthantBox]
  constructor
  · intro h
    exact ⟨fun i hi => by have := h i; rw [hi] at this; simpa using this,
           fun i hi => by have := h i; rw [hi] at this; simpa using this⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : s i = true
    · rw [hi]; simpa using h1 i hi
    · have hf : s i = false := by cases h : s i <;> simp_all
      rw [hf]; simpa using h2 i hf

omit [MeasurableSpace Ω] in
/-- The `2^d` orthant boxes are pairwise disjoint. -/
theorem pairwiseDisjoint_orthantBox (R : ℕ) :
    ((Finset.univ : Finset (Fin d → Bool)) : Set (Fin d → Bool)).PairwiseDisjoint
      (fun s : Fin d → Bool => orthantBox s R) := by
  intro s _ t _ hst
  change Disjoint (orthantBox s R) (orthantBox t R)
  rw [Finset.disjoint_left]
  intro x hs ht
  apply hst
  funext i
  have hs' := mem_orthantBox_iff.mp hs
  have ht' := mem_orthantBox_iff.mp ht
  cases hsi : s i <;> cases hti : t i
  · rfl
  · exact absurd (ht'.1 i hti).1 (not_le.mpr (hs'.2 i hsi).2)
  · exact absurd (hs'.1 i hsi).1 (not_le.mpr (ht'.2 i hti).2)
  · rfl

omit [MeasurableSpace Ω] in
/-- `card B * avg B f = ∑_{x∈B} f x`, valid also for empty `B`. -/
theorem card_mul_avg (B : Finset (Site d)) (f : Site d → ℝ≥0∞) :
    (B.card : ℝ≥0∞) * avg B f = ∑ x ∈ B, f x := by
  rw [avg]
  by_cases h : B.card = 0
  · have hemp : B = ∅ := Finset.card_eq_zero.mp h
    rw [h, hemp]; simp
  · rw [← mul_assoc, ENNReal.mul_inv_cancel (by simpa using h) (by simp), one_mul]

omit [MeasurableSpace Ω] in
/-- **Cover / average comparison.**  For `R ≥ 1` and `d ≥ 1`, the average over the `ℓ¹` ball of
radius `R` is at most `(2d)^d` times the maximum of the averages over the `2^d` orthant boxes
`orthantBox s R`. -/
theorem avg_l1Ball_le_orthantBoxMax (R : ℕ) (hd : 1 ≤ d) (f : Site d → ℝ≥0∞) :
    avg (l1Ball (0 : Site d) R) f ≤
      (((2 * d) ^ d : ℕ) : ℝ≥0∞) *
        (Finset.univ.sup fun s : Fin d → Bool => avg (orthantBox s R) f) := by
  set X : ℝ≥0∞ := Finset.univ.sup (fun s : Fin d → Bool => avg (orthantBox s R) f) with hX
  have hXle : ∀ s : Fin d → Bool, avg (orthantBox s R) f ≤ X := fun s =>
    Finset.le_sup (f := fun s : Fin d → Bool => avg (orthantBox s R) f) (Finset.mem_univ s)
  have hdisj := pairwiseDisjoint_orthantBox (d := d) R
  have hBsub : l1Ball (0 : Site d) R ⊆
      Finset.univ.biUnion (fun s : Fin d → Bool => orthantBox s R) := by
    rw [← boxFinset_eq_biUnion_orthantBox]
    simpa using l1Ball_subset_boxFinset (d := d) (R := (R : ℝ))
  have hsum : ∑ x ∈ l1Ball (0 : Site d) R, f x ≤ (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞) * X := by
    calc ∑ x ∈ l1Ball (0 : Site d) R, f x
        ≤ ∑ x ∈ Finset.univ.biUnion (fun s : Fin d → Bool => orthantBox s R), f x :=
          Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun x _ _ => zero_le)
      _ = ∑ s : Fin d → Bool, ∑ x ∈ orthantBox s R, f x := Finset.sum_biUnion hdisj
      _ = ∑ s : Fin d → Bool, ((orthantBox s R).card : ℝ≥0∞) * avg (orthantBox s R) f := by
          refine Finset.sum_congr rfl fun s _ => ?_
          exact (card_mul_avg (orthantBox s R) f).symm
      _ ≤ ∑ s : Fin d → Bool, ((orthantBox s R).card : ℝ≥0∞) * X := by
          refine Finset.sum_le_sum fun s _ => ?_
          exact mul_le_mul' le_rfl (hXle s)
      _ = (∑ s : Fin d → Bool, ((orthantBox s R).card : ℝ≥0∞)) * X :=
          (Finset.sum_mul _ _ _).symm
      _ = (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞) * X := by
          congr 1
          have hc : (∑ s : Fin d → Bool, (orthantBox s R).card) = (2 * R + 1) ^ d := by
            rw [← Finset.card_biUnion hdisj, ← boxFinset_eq_biUnion_orthantBox, card_boxFinset_zero]
          rw [← hc]
          push_cast
          rfl
  have hvol : ((l1Ball (0 : Site d) R).card : ℝ≥0∞)⁻¹ * (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞)
      ≤ (((2 * d) ^ d : ℕ) : ℝ≥0∞) := by
    have hcard : (((R / d + 1) ^ d : ℕ) : ℝ≥0∞) ≤ ((l1Ball (0 : Site d) R).card : ℝ≥0∞) := by
      exact_mod_cast card_l1Ball_ge (d := d) R
    have h2R : (2 * R + 1 : ℕ) ≤ 2 * d * (R / d + 1) := by
      have hM : R + 1 ≤ d * (R / d + 1) := by
        have hmod := Nat.div_add_mod R d
        have hlt := Nat.mod_lt R (by omega : 0 < d)
        have he : d * (R / d + 1) = d * (R / d) + d := by ring
        omega
      calc 2 * R + 1 ≤ 2 * (R + 1) := by omega
        _ ≤ 2 * (d * (R / d + 1)) := by omega
        _ = 2 * d * (R / d + 1) := by ring
    have hA : ((((R / d + 1) ^ d : ℕ) : ℝ≥0∞))⁻¹ * (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞)
        ≤ ((((R / d + 1) ^ d : ℕ) : ℝ≥0∞))⁻¹ *
          (((2 * d * (R / d + 1)) ^ d : ℕ) : ℝ≥0∞) := by
      refine mul_le_mul' le_rfl ?_
      exact_mod_cast Nat.pow_le_pow_left h2R d
    have hB : ((((R / d + 1) ^ d : ℕ) : ℝ≥0∞))⁻¹ *
          (((2 * d * (R / d + 1)) ^ d : ℕ) : ℝ≥0∞)
        ≤ (((2 * d) ^ d : ℕ) : ℝ≥0∞) := by
      have hpow : (2 * d * (R / d + 1)) ^ d = (2 * d) ^ d * (R / d + 1) ^ d := by rw [mul_pow]
      rw [hpow, Nat.cast_mul]
      calc ((↑((R / d + 1) ^ d) : ℝ≥0∞))⁻¹ * ((↑((2 * d) ^ d) : ℝ≥0∞) * ↑((R / d + 1) ^ d))
          = (↑((2 * d) ^ d) : ℝ≥0∞) *
              (((↑((R / d + 1) ^ d) : ℝ≥0∞))⁻¹ * ↑((R / d + 1) ^ d)) := by ring
        _ ≤ (↑((2 * d) ^ d) : ℝ≥0∞) * 1 := by
            gcongr
            by_cases h0 : (↑((R / d + 1) ^ d) : ℝ≥0∞) = 0
            · rw [h0]; simp
            · rw [ENNReal.inv_mul_cancel h0 (by simp)]
        _ = (↑((2 * d) ^ d) : ℝ≥0∞) := by rw [mul_one]
    calc ((l1Ball (0 : Site d) R).card : ℝ≥0∞)⁻¹ * (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞)
        ≤ ((((R / d + 1) ^ d : ℕ) : ℝ≥0∞))⁻¹ * (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞) := by
          gcongr
      _ ≤ ((((R / d + 1) ^ d : ℕ) : ℝ≥0∞))⁻¹ *
            (((2 * d * (R / d + 1)) ^ d : ℕ) : ℝ≥0∞) := hA
      _ ≤ (((2 * d) ^ d : ℕ) : ℝ≥0∞) := hB
  rw [avg]
  calc ((l1Ball (0 : Site d) R).card : ℝ≥0∞)⁻¹ * ∑ x ∈ l1Ball (0 : Site d) R, f x
      ≤ ((l1Ball (0 : Site d) R).card : ℝ≥0∞)⁻¹ * ((((2 * R + 1) ^ d : ℕ) : ℝ≥0∞) * X) := by
        gcongr
    _ = (((l1Ball (0 : Site d) R).card : ℝ≥0∞)⁻¹ * (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞)) * X := by
        ring
    _ ≤ (((2 * d) ^ d : ℕ) : ℝ≥0∞) * X := by
        gcongr

omit [MeasurableSpace Ω] in
/-- **Translation bookkeeping (finite sets).**  Averaging over a translate `B + z` is averaging
the shifted function over `B`. -/
theorem avg_map_addRight (B : Finset (Site d)) (z : Site d) (f : Site d → ℝ≥0∞) :
    avg (B.map (Equiv.addRight z).toEmbedding) f = avg B (fun x => f (x + z)) := by
  unfold avg
  rw [Finset.card_map, Finset.sum_map]
  rfl


/-! ### The stated geometric transfer -/

/-- **The geometry transfer, stated.**  Assuming the centred anchored-box weak-type input for
every side vector `c`, the `ℓ¹`-ball weak type holds.  The finite-set geometry is now fully proved:
the cover `l1Ball 0 R ⊆ ⋃_s orthantBox s R` (`l1Ball_subset_boxFinset` +
`boxFinset_eq_biUnion_orthantBox`), the volume lower bound `card_l1Ball_ge`, and the average
comparison `avg_l1Ball_le_orthantBoxMax` with explicit constant `(2d)^d`, independent of the radius
(so no `d!` is needed).  What remains isolated here is only the action/measure-theoretic step:
replacing `f (x + z)` by `f (τ z ·)` via the measure-preserving additive action `τ`
(`avg_map_addRight` is the finite-set core of that). -/
def L1BallCoverTransfer (d : ℕ) : Prop :=
  (∀ c : Fin d → ℝ, KrengelMaximalInputCentred d c) → KrengelLpBallWeakType d

/-- **The full reduction.** -/
theorem KrengelLpBall_of_centredBox (htransfer : L1BallCoverTransfer d)
    (hbox : ∀ c : Fin d → ℝ, KrengelMaximalInputCentred d c) : KrengelLpBall d :=
  KrengelLpBall_of_weakType (htransfer hbox)

#print axioms KrengelLpBall_of_weakType
#print axioms KrengelLpBall_of_centredBox
#print axioms boxFinset_eq_biUnion_orthantBox
#print axioms anchoredBox_subset_l1Ball
#print axioms orthantBox_true_subset_l1Ball
#print axioms card_l1Ball_ge
#print axioms card_orthantBox
#print axioms avg_map_addRight
#print axioms mem_orthantBox_iff
#print axioms pairwiseDisjoint_orthantBox
#print axioms card_mul_avg
#print axioms avg_l1Ball_le_orthantBoxMax

end

end LatticeProb
