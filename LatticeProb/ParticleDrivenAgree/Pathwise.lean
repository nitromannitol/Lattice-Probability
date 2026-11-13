/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Pathwise at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDrivenAgree.OneParticle
import LatticeProb.ParticleDrivenAgree.Error
import LatticeProb.Prob.InfinitePiSplit

/-!
# Lemma 5.1: the corrected odometer stays within `w^\star`

Lemma 5.1 of `parking.tex`: the odometer, corrected by the error field, stays
within `w^\star` of the divisible odometer.

The argument is a Bellman comparison.  Writing `V_k = U_k - w_k`, the parallel
identity and the recursion for `w` give
`V_{k+1} = (η + P V_k) ∨ (-w_{k+1})`, beside `u_{k+1} = (η + P u_k) ∨ 0`, and
two maxima differ by at most the larger of the differences of their arguments.
So `|V_{k+1} - u_{k+1}|` is at most the larger of `|w_{k+1}|` and
`P|V_k - u_k|`, and the two facts that close the induction are that `w^\star`
dominates `|w|` and that it dominates one application of `P` to itself.

The second is the Markov property of the walk at time one, which
`LatticeProb.integral_infinitePi_nat_head_tail` supplies: the direction
sequence is one direction followed by an independent copy of itself, and the
maximum along the walk from `x` is at least the maximum along the walk from the
site the first step reaches.  The integrands are measurable because they read
only finitely many directions, and bounded because a walk of `n` steps from `x`
stays in the box of radius `n`.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ### The walk law is a probability measure -/

/-- The uniform direction law `stepLaw d` gives total mass one to the universe, since it
is `(2d)⁻¹` times a sum of `2d` Dirac masses. -/
theorem stepLaw_univ (hd : 1 ≤ d) : stepLaw d Set.univ = 1 := by
  have hcard : (Finset.univ : Finset (Fin d × Bool)).card = 2 * d := by
    simp [Finset.card_univ, Nat.mul_comm]
  simp only [stepLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ, Finset.sum_const, smul_eq_mul,
    Pi.one_apply, nsmul_eq_mul, mul_one, hcard]
  have h2d : (2 * (d : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    exact ⟨two_ne_zero, by omega⟩
  have h2d' : (2 * (d : ℝ≥0∞)) ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  rw [show ((2 * d : ℕ) : ℝ≥0∞) = 2 * (d : ℝ≥0∞) by push_cast; ring]
  exact ENNReal.inv_mul_cancel h2d h2d'

/-- `stepLaw d` is a probability measure, from `stepLaw_univ`. -/
theorem stepLaw_isProbability (hd : 1 ≤ d) : IsProbabilityMeasure (stepLaw d) :=
  ⟨stepLaw_univ hd⟩

/-! ### The neighbour sum -/

/-- The sum of `f` over the `2d` lattice neighbours of `x` splits as the sum, over each
coordinate direction `i`, of `f` at the forward and backward neighbours along that
axis. -/
theorem nbrFinset_sum (f : Site d → ℝ) (x : Site d) :
    ∑ y ∈ nbrFinset x, f y = ∑ i : Fin d, (f (x + unit i) + f (x - unit i)) := by
  classical
  rw [nbrFinset, Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.sum_pair (by
        intro hc
        have := congrFun hc i
        simp [unit, Pi.single_eq_same] at this
        omega)]
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun z hz hz' => hij ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    have key : ∀ (a b : Fin d) (sa sb : ℤ), sa ≠ 0 → sb ≠ 0 →
        x + sa • unit a = x + sb • unit b → a = b := by
      intro a b sa sb ha hb hab
      by_contra hne
      have h1 := congrFun hab a
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
      exact ha h1
    rcases hz with rfl | rfl <;> rcases hz' with h | h
    · exact key i j 1 1 one_ne_zero one_ne_zero (by simpa using h)
    · exact key i j 1 (-1) one_ne_zero (by norm_num) (by simpa [sub_eq_add_neg] using h)
    · exact key i j (-1) 1 (by norm_num) one_ne_zero (by simpa [sub_eq_add_neg] using h)
    · exact key i j (-1) (-1) (by norm_num) (by norm_num) (by simpa [sub_eq_add_neg] using h)

/-- The Markov averaging operator `walkOp f x` is the mean of `f` over the neighbours of
`x`, i.e. the neighbour sum `nbrSum f x` divided by `2d`. -/
theorem walkOp_eq_nbrFinset (f : Site d → ℝ) (x : Site d) :
    walkOp f x = (∑ y ∈ nbrFinset x, f y) / (2 * d) := by
  rw [walkOp, nbrSum, nbrFinset_sum]

/-! ### The maximal error along the walk -/

/-- The position `walkPath x p j` of the walk from `x` after `j` steps is a measurable
function of the direction sequence `p`, by induction on `j`. -/
theorem measurable_walkPath (x : Site d) (j : ℕ) :
    Measurable fun p : ℕ → Fin d × Bool => walkPath x p j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      have h2 : Measurable fun p : ℕ → Fin d × Bool => stepVec (p j) :=
        (Measurable.of_discrete : Measurable (stepVec (d := d))).comp (measurable_pi_apply j)
      exact ih.add h2

/-- Prepending one direction `u` to the sequence `p` and taking `j + 1` steps from `x`
agrees with taking `j` steps of `p` from the site `x + stepVec u` the first step
reaches. -/
theorem walkPath_consNat (x : Site d) (u : Fin d × Bool) (p : ℕ → Fin d × Bool) (j : ℕ) :
    walkPath x (consNat u p) (j + 1) = walkPath (x + stepVec u) p j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [walkPath, ih, walkPath, consNat_succ]

/-- The integrand of `w^\star`. -/
def wMax (ω : Data d) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) : ℝ :=
  ⨆ j ∈ Finset.range (n + 1), |wErr ω (n - j) (walkPath x p j)|

/-- `wStar` unfolds to its defining integral of `wMax` against the walk law. -/
theorem wStar_eq (ω : Data d) (n : ℕ) (x : Site d) :
    wStar ω n x = ∫ p, wMax ω n x p ∂(walkLaw d) := rfl

/-- A crude bound on the error along any walk of `n` steps from `x`. -/
def wBound (ω : Data d) (n : ℕ) (x : Site d) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), ∑ z ∈ boxFinset x n, |wErr ω m z|

/-- The crude bound `wBound` is nonnegative, being a sum of absolute values. -/
theorem wBound_nonneg (ω : Data d) (n : ℕ) (x : Site d) : 0 ≤ wBound ω n x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The walk from `x` stays inside the box of radius `n` for its first `n` steps, since
each step changes each coordinate by at most one. -/
theorem walkPath_mem_box (x : Site d) (p : ℕ → Fin d × Bool) {j n : ℕ} (hj : j ≤ n) :
    walkPath x p j ∈ boxFinset x n := by
  rw [mem_boxFinset_iff]
  intro i
  have : ∀ k : ℕ, |walkPath x p k i - x i| ≤ (k : ℤ) := by
    intro k
    induction k with
    | zero => simp [walkPath]
    | succ k ih =>
        have hstep : |walkPath x p (k + 1) i - walkPath x p k i| ≤ 1 := by
          show |(walkPath x p k + stepVec (p k)) i - walkPath x p k i| ≤ 1
          simpa using abs_stepVec_le_one (p k) i
        have hrw : walkPath x p (k + 1) i - x i
            = (walkPath x p (k + 1) i - walkPath x p k i) + (walkPath x p k i - x i) := by ring
        calc |walkPath x p (k + 1) i - x i|
            ≤ |walkPath x p (k + 1) i - walkPath x p k i| + |walkPath x p k i - x i| := by
              rw [hrw]; exact abs_add_le _ _
          _ ≤ 1 + (k : ℤ) := by linarith
          _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  exact le_trans (this j) (by exact_mod_cast hj)

/-- Each term of the supremum defining `wMax` is bounded by the crude bound `wBound`,
since the walk stays in the box that `wBound` sums over. -/
theorem term_le_wBound (ω : Data d) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool)
    {j : ℕ} (hj : j ≤ n) : |wErr ω (n - j) (walkPath x p j)| ≤ wBound ω n x := by
  have h1 : |wErr ω (n - j) (walkPath x p j)| ≤ ∑ z ∈ boxFinset x n, |wErr ω (n - j) z| :=
    Finset.single_le_sum (f := fun z => |wErr ω (n - j) z|)
      (fun _ _ => abs_nonneg _) (walkPath_mem_box x p hj)
  have h2 : (∑ z ∈ boxFinset x n, |wErr ω (n - j) z|) ≤ wBound ω n x :=
    Finset.single_le_sum (f := fun m => ∑ z ∈ boxFinset x n, |wErr ω m z|)
      (fun m _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  exact h1.trans h2

/-- The family of terms whose supremum defines `wMax` is bounded above by `wBound`, so
that supremum exists. -/
theorem wMax_bdd (ω : Data d) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) :
    BddAbove (Set.range fun j : ℕ => ⨆ _ : j ∈ Finset.range (n + 1),
      |wErr ω (n - j) (walkPath x p j)|) := by
  refine ⟨wBound ω n x, ?_⟩
  rintro b ⟨j, rfl⟩
  dsimp only
  by_cases hj : j ∈ Finset.range (n + 1)
  · rw [ciSup_pos hj]
    exact term_le_wBound ω n x p (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj)
  · rw [ciSup_neg hj, Real.sSup_empty]
    exact wBound_nonneg ω n x

/-- `wMax` is bounded above by the crude bound `wBound`, from `term_le_wBound` applied to
every term of its defining supremum. -/
theorem wMax_le (ω : Data d) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) :
    wMax ω n x p ≤ wBound ω n x := by
  refine ciSup_le fun j => ?_
  by_cases hj : j ∈ Finset.range (n + 1)
  · rw [ciSup_pos hj]
    exact term_le_wBound ω n x p (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj)
  · rw [ciSup_neg hj, Real.sSup_empty]
    exact wBound_nonneg ω n x

/-- `wMax` is nonnegative: the term of its supremum at `j = 0` is `|wErr ω n x|`, which is
itself nonnegative. -/
theorem wMax_nonneg (ω : Data d) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) :
    0 ≤ wMax ω n x p := by
  refine le_ciSup_of_le ⟨wBound ω n x, ?_⟩ 0 ?_
  · rintro b ⟨j, rfl⟩
    dsimp only
    by_cases hj : j ∈ Finset.range (n + 1)
    · rw [ciSup_pos hj]
      exact term_le_wBound ω n x p (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj)
    · rw [ciSup_neg hj, Real.sSup_empty]
      exact wBound_nonneg ω n x
  · rw [ciSup_pos (Finset.mem_range.mpr (Nat.succ_pos n))]
    exact abs_nonneg _

/-- The walk's position after `j` steps depends only on the first `j` directions of the
sequence driving it. -/
theorem walkPath_congr (x : Site d) {p q : ℕ → Fin d × Bool} {j : ℕ}
    (h : ∀ i, i < j → p i = q i) : walkPath x p j = walkPath x q j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [walkPath, walkPath, ih (fun i hi => h i (by omega)), h j (by omega)]

/-- `wMax` depends only on the first `n` directions of the sequence, via
`walkPath_congr`. -/
theorem wMax_congr (ω : Data d) (n : ℕ) (x : Site d) {p q : ℕ → Fin d × Bool}
    (h : ∀ i, i < n → p i = q i) : wMax ω n x p = wMax ω n x q := by
  unfold wMax
  refine iSup_congr fun j => iSup_congr fun hj => ?_
  rw [walkPath_congr x (fun i hi => h i (by
    have := Finset.mem_range.mp hj; omega))]

/-- A real function of a direction sequence that reads only the first `n`
directions is measurable. -/
theorem measurable_of_finite_dependence (hd : 1 ≤ d) (n : ℕ)
    (f : (ℕ → Fin d × Bool) → ℝ)
    (h : ∀ p q : ℕ → Fin d × Bool, (∀ i, i < n → p i = q i) → f p = f q) :
    Measurable f := by
  classical
  haveI : Nonempty (Fin d × Bool) := ⟨(⟨0, by omega⟩, true)⟩
  set e : (Fin n → Fin d × Bool) → (ℕ → Fin d × Bool) :=
    fun c i => if hi : i < n then c ⟨i, hi⟩ else Classical.arbitrary _ with he
  have hfac : f = (fun c : Fin n → Fin d × Bool => f (e c))
      ∘ (fun (p : ℕ → Fin d × Bool) (i : Fin n) => p (i : ℕ)) := by
    funext p
    refine (h _ _ fun i hi => ?_).symm
    simp only [he, dif_pos hi]
  rw [hfac]
  exact Measurable.of_discrete.comp (Measurable.of_eval fun i => measurable_pi_apply _)

/-- `wMax ω n x` is measurable, by `measurable_of_finite_dependence` applied to its
finite dependence on the first `n` directions (`wMax_congr`). -/
theorem measurable_wMax (hd : 1 ≤ d) (ω : Data d) (n : ℕ) (x : Site d) :
    Measurable (wMax ω n x) :=
  measurable_of_finite_dependence hd n _ fun _ _ hpq => wMax_congr ω n x hpq

/-- `wMax ω n x` is integrable under the walk law, being measurable and bounded by the
constant `wBound ω n x`. -/
theorem integrable_wMax (hd : 1 ≤ d) (ω : Data d) (n : ℕ) (x : Site d) :
    Integrable (wMax ω n x) (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by
    unfold walkLaw; infer_instance
  refine (integrable_const (wBound ω n x)).mono'
    (measurable_wMax hd ω n x).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (wMax_nonneg ω n x p)]
  exact wMax_le ω n x p

/-- The error field is dominated by `wStar`: `|wErr ω n x|` is itself one of the terms of
the supremum defining `wMax ω n x p` for any direction sequence `p`, so it is at most the
mean of `wMax` over the walk law, which is `wStar`. -/
theorem abs_wErr_le_wStar (hd : 1 ≤ d) (ω : Data d) (n : ℕ) (x : Site d) :
    |wErr ω n x| ≤ wStar ω n x := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by
    unfold walkLaw; infer_instance
  have hpt : ∀ p, |wErr ω n x| ≤ wMax ω n x p := by
    intro p
    refine le_ciSup_of_le ⟨wBound ω n x, ?_⟩ 0 ?_
    · rintro b ⟨j, rfl⟩
      dsimp only
      by_cases hj : j ∈ Finset.range (n + 1)
      · rw [ciSup_pos hj]
        exact term_le_wBound ω n x p (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj)
      · rw [ciSup_neg hj, Real.sSup_empty]
        exact wBound_nonneg ω n x
    · rw [ciSup_pos (Finset.mem_range.mpr (Nat.succ_pos n))]
      simp [walkPath]
  calc |wErr ω n x| = ∫ _p, |wErr ω n x| ∂(walkLaw d) := by simp
    _ ≤ ∫ p, wMax ω n x p ∂(walkLaw d) :=
        integral_mono (integrable_const _) (integrable_wMax hd ω n x) hpt
    _ = wStar ω n x := rfl

/-- `wStar` vanishes at horizon `0`, since the only term of `wMax ω 0 x p` is
`|wErr ω 0 x| = 0`. -/
theorem wStar_zero (ω : Data d) (x : Site d) : wStar ω 0 x = 0 := by
  have hmax : ∀ p, wMax ω 0 x p = 0 := by
    intro p
    unfold wMax
    refine le_antisymm (ciSup_le fun j => ?_) ?_
    · by_cases hj : j ∈ Finset.range 1
      · rw [ciSup_pos hj]
        simp [wErr]
      · rw [ciSup_neg hj, Real.sSup_empty]
    · refine le_ciSup_of_le ⟨0, ?_⟩ 0 ?_
      · rintro b ⟨j, rfl⟩
        dsimp only
        by_cases hj : j ∈ Finset.range 1
        · rw [ciSup_pos hj]
          have : j = 0 := by simpa using Finset.mem_range.mp hj
          subst this
          simp [wErr]
        · rw [ciSup_neg hj, Real.sSup_empty]
      · rw [ciSup_pos (Finset.mem_range.mpr Nat.one_pos)]
        simp [wErr]
  show ∫ p, wMax ω 0 x p ∂(walkLaw d) = 0
  simp [hmax]

/-! ### The Markov step -/

/-- The expectation of `g` under the uniform direction law is the average of `g` over all
`2d` directions. -/
theorem integral_stepLaw (hd : 1 ≤ d) (g : Fin d × Bool → ℝ) :
    ∫ u, g u ∂(stepLaw d) = (∑ b : Fin d × Bool, g b) / (2 * d) := by
  haveI := stepLaw_isProbability hd
  have hfin : ∀ b : Fin d × Bool, Integrable g (Measure.dirac b) := fun b =>
    integrable_dirac (by simp)
  rw [stepLaw, integral_smul_measure, integral_finsetSum_measure (fun b _ => hfin b)]
  simp only [integral_dirac]
  have h2d : (2 * (d : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    exact ⟨two_ne_zero, by omega⟩
  have h2d' : (2 * (d : ℝ≥0∞)) ≠ ⊤ := by simp [ENNReal.mul_eq_top]
  rw [smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  rw [div_eq_inv_mul]

/-- Summing `g` over each of the `2d` translates of `x` by a signed direction equals the
neighbour sum `nbrSum g x`. -/
theorem sum_stepVec (g : Site d → ℝ) (x : Site d) :
    (∑ b : Fin d × Bool, g (x + stepVec b)) = nbrSum g x := by
  rw [nbrSum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [stepVec, sub_eq_add_neg]

/-- One application of the Markov averaging operator to `wStar` at horizon `k` is
dominated by `wStar` at horizon `k + 1`: by the Markov property of the walk at time one
(`integral_infinitePi_nat_head_tail`), the walk from `x` splits as one step followed by an
independent copy of itself, so the mean of `wMax` after that first step is one of the
terms of the supremum defining `wMax` at the longer horizon. -/
theorem walkOp_wStar_le (hd : 1 ≤ d) (ω : Data d) (k : ℕ) (x : Site d) :
    walkOp (wStar ω k) x ≤ wStar ω (k + 1) x := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  set f : (ℕ → Fin d × Bool) → ℝ := fun p => wMax ω k (x + stepVec (p 0)) (tailNat p) with hf
  have hshift : ∀ (p : ℕ → Fin d × Bool) (j : ℕ),
      walkPath (x + stepVec (p 0)) (tailNat p) j = walkPath x p (j + 1) := by
    intro p j
    rw [← walkPath_consNat, consNat_head_tail]
  have hfcongr : ∀ p q : ℕ → Fin d × Bool, (∀ i, i < k + 1 → p i = q i) → f p = f q := by
    intro p q hpq
    show wMax ω k (x + stepVec (p 0)) (tailNat p) = wMax ω k (x + stepVec (q 0)) (tailNat q)
    rw [hpq 0 (by omega)]
    exact wMax_congr ω k _ fun i hi => hpq (i + 1) (by omega)
  have hfmeas : Measurable f := measurable_of_finite_dependence hd (k + 1) f hfcongr
  have hfnonneg : ∀ p, 0 ≤ f p := fun p => wMax_nonneg ω k _ _
  have hfbound : ∀ p, f p ≤ ∑ b : Fin d × Bool, wBound ω k (x + stepVec b) := by
    intro p
    refine le_trans (wMax_le ω k _ _) ?_
    exact Finset.single_le_sum (f := fun b => wBound ω k (x + stepVec b))
      (fun b _ => wBound_nonneg ω k _) (Finset.mem_univ (p 0))
  have hfint : Integrable f (walkLaw d) := by
    refine (integrable_const (∑ b : Fin d × Bool, wBound ω k (x + stepVec b))).mono'
      hfmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg p)]
    exact hfbound p
  have hle : ∀ p, f p ≤ wMax ω (k + 1) x p := by
    intro p
    show wMax ω k (x + stepVec (p 0)) (tailNat p) ≤ wMax ω (k + 1) x p
    refine ciSup_le fun j => ?_
    by_cases hj : j ∈ Finset.range (k + 1)
    · rw [ciSup_pos hj, hshift p j]
      refine le_ciSup_of_le (wMax_bdd ω (k + 1) x p) (j + 1) ?_
      rw [ciSup_pos (Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hj; omega))]
      exact le_of_eq (by rw [show k + 1 - (j + 1) = k - j by omega])
    · rw [ciSup_neg hj, Real.sSup_empty]
      exact wMax_nonneg ω (k + 1) x p
  have hsplit : ∫ p, f p ∂(walkLaw d) = ∫ u, wStar ω k (x + stepVec u) ∂(stepLaw d) := by
    have htail : ∀ (u : Fin d × Bool) (p : ℕ → Fin d × Bool), tailNat (consNat u p) = p := by
      intro u p; funext m; rfl
    rw [show walkLaw d = Measure.infinitePi fun _ : ℕ => stepLaw d from rfl]
    rw [integral_infinitePi_nat_head_tail (stepLaw d) f
      (by rwa [show (Measure.infinitePi fun _ : ℕ => stepLaw d) = walkLaw d from rfl])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ∫ p, wMax ω k (x + stepVec (consNat u p 0)) (tailNat (consNat u p))
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) = wStar ω k (x + stepVec u)
    simp only [consNat_zero, htail]
    rfl
  calc walkOp (wStar ω k) x
      = ∫ u, wStar ω k (x + stepVec u) ∂(stepLaw d) := by
        rw [integral_stepLaw hd, sum_stepVec, walkOp]
    _ = ∫ p, f p ∂(walkLaw d) := hsplit.symm
    _ ≤ ∫ p, wMax ω (k + 1) x p ∂(walkLaw d) :=
        integral_mono hfint (integrable_wMax hd ω (k + 1) x) hle
    _ = wStar ω (k + 1) x := rfl

/-! ### The Bellman comparison -/

/-- Two maxima of pairs differ by at most the larger of the differences of their
respective arguments. -/
theorem abs_max_sub_max_le (a₁ a₂ b₁ b₂ : ℝ) :
    |max a₁ a₂ - max b₁ b₂| ≤ max |a₁ - b₁| |a₂ - b₂| := by
  have h1 : max a₁ a₂ ≤ max b₁ b₂ + max |a₁ - b₁| |a₂ - b₂| := by
    refine max_le ?_ ?_
    · calc a₁ = b₁ + (a₁ - b₁) := by ring
        _ ≤ max b₁ b₂ + max |a₁ - b₁| |a₂ - b₂| :=
            add_le_add (le_max_left _ _) ((le_abs_self _).trans (le_max_left _ _))
    · calc a₂ = b₂ + (a₂ - b₂) := by ring
        _ ≤ max b₁ b₂ + max |a₁ - b₁| |a₂ - b₂| :=
            add_le_add (le_max_right _ _) ((le_abs_self _).trans (le_max_right _ _))
  have h2 : max b₁ b₂ ≤ max a₁ a₂ + max |a₁ - b₁| |a₂ - b₂| := by
    refine max_le ?_ ?_
    · calc b₁ = a₁ + (b₁ - a₁) := by ring
        _ ≤ max a₁ a₂ + max |a₁ - b₁| |a₂ - b₂| :=
            add_le_add (le_max_left _ _)
              ((neg_le_abs (a₁ - b₁)).trans' (by linarith) |>.trans (le_max_left _ _))
    · calc b₂ = a₂ + (b₂ - a₂) := by ring
        _ ≤ max a₁ a₂ + max |a₁ - b₁| |a₂ - b₂| :=
            add_le_add (le_max_right _ _)
              ((neg_le_abs (a₂ - b₂)).trans' (by linarith) |>.trans (le_max_right _ _))
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The Markov averaging operator is additive: it commutes with pointwise
subtraction. -/
theorem walkOp_sub (f g : Site d → ℝ) (x : Site d) :
    walkOp (fun y => f y - g y) x = walkOp f x - walkOp g x := by
  rw [walkOp, walkOp, walkOp, nbrSum, nbrSum, nbrSum, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Markov averaging operator is monotone in its argument. -/
theorem walkOp_mono (hd : 1 ≤ d) {f g : Site d → ℝ} (hfg : ∀ y, f y ≤ g y) (x : Site d) :
    walkOp f x ≤ walkOp g x := by
  have h2d : (0 : ℝ) < 2 * d := by positivity
  rw [walkOp, walkOp, div_le_div_iff_of_pos_right h2d, nbrSum, nbrSum]
  exact Finset.sum_le_sum fun i _ => add_le_add (hfg _) (hfg _)

/-- The Markov averaging operator does not increase absolute value: `|walkOp f x|` is at
most the average of `|f|` over the neighbours of `x`. -/
theorem abs_walkOp_le (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    |walkOp f x| ≤ walkOp (fun y => |f y|) x := by
  have h2d : (0 : ℝ) < 2 * d := by positivity
  rw [walkOp, walkOp, abs_div, abs_of_pos h2d, div_le_div_iff_of_pos_right h2d, nbrSum, nbrSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact abs_add_le _ _

/-- The odometer identity in real form. -/
theorem U_succ_real {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (k : ℕ) (x : Site d) :
    (U ω (k + 1) x : ℝ)
      = max 0 ((ω.1 x : ℝ) + ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω k y) : ℝ)) := by
  have h := (parallel_of_labelOrder (D := toDriver ω) (labelOrder d) hstep).2 k x
  have := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at this
  exact this

/-- The error field, rewritten with the neighbour sum. -/
theorem wErr_succ_eq {ω : Data d} (k : ℕ) (x : Site d) :
    wErr ω (k + 1) x
      = (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω k y) : ℝ))
        - walkOp (fun y => ((U ω k y : ℝ) - wErr ω k y)) x := by
  have hsplit : ∑ y ∈ nbrFinset x,
      ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * d))
      = (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω k y) : ℝ))
        - walkOp (fun y => (U ω k y : ℝ)) x := by
    rw [walkOp_eq_nbrFinset, Finset.sum_sub_distrib, Finset.sum_div]
  show walkOp (wErr ω k) x + ∑ y ∈ nbrFinset x,
      ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * d)) = _
  rw [hsplit, walkOp_sub]
  ring

/-- The Bellman recursion for the corrected odometer. -/
theorem V_succ {ω : Data d} (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    (k : ℕ) (x : Site d) :
    (U ω (k + 1) x : ℝ) - wErr ω (k + 1) x
      = max (-(wErr ω (k + 1) x))
        ((ω.1 x : ℝ) + walkOp (fun y => (U ω k y : ℝ) - wErr ω k y) x) := by
  rw [U_succ_real hstep k x]
  set A := ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω k y) : ℝ) with hA
  set W := walkOp (fun y => (U ω k y : ℝ) - wErr ω k y) x with hW
  have hw : wErr ω (k + 1) x = A - W := wErr_succ_eq k x
  rw [hw, ← max_sub_sub_right]
  congr 1
  · ring
  · ring

/-- The corrected integer odometer stays within `wStar` of the divisible odometer, for a
realization whose instructions are neighbours of the site carrying them: the induction
step is the Bellman comparison `V_succ` together with `abs_max_sub_max_le`,
`abs_wErr_le_wStar`, and the monotone bound `walkOp_wStar_le`. -/
theorem pathwise_of_labelOrder (hd : 1 ≤ d) {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    ∀ x : Site d, |(U ω n x : ℝ) - wErr ω n x - uOf ω n x| ≤ wStar ω n x := by
  induction n with
  | zero =>
      intro x
      rw [wStar_zero ω x]
      show |((0 : ℕ) : ℝ) - 0 - 0| ≤ 0
      simp
  | succ k ih =>
      intro x
      have hV := V_succ hstep k x
      have hu : uOf ω (k + 1) x = max 0 ((ω.1 x : ℝ) + walkOp (uOf ω k) x) := rfl
      rw [show (U ω (k + 1) x : ℝ) - wErr ω (k + 1) x - uOf ω (k + 1) x
          = ((U ω (k + 1) x : ℝ) - wErr ω (k + 1) x) - uOf ω (k + 1) x from rfl, hV, hu]
      refine (abs_max_sub_max_le _ _ _ _).trans (max_le ?_ ?_)
      · rw [sub_zero, abs_neg]
        exact abs_wErr_le_wStar hd ω (k + 1) x
      · have hdiff : ((ω.1 x : ℝ) + walkOp (fun y => (U ω k y : ℝ) - wErr ω k y) x)
            - ((ω.1 x : ℝ) + walkOp (uOf ω k) x)
            = walkOp (fun y => ((U ω k y : ℝ) - wErr ω k y) - uOf ω k y) x := by
          conv_rhs => rw [walkOp_sub]
          ring
        rw [hdiff]
        refine (abs_walkOp_le hd _ x).trans ?_
        refine le_trans (walkOp_mono hd (fun y => ih y) x) ?_
        exact walkOp_wStar_le hd ω k x

/-- Lemma 5.1 of the paper, for a realization whose instructions are
neighbours of the site carrying them. -/
theorem pathwise_comparison_of_labelOrder (hd : 1 ≤ d) {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) (x : Site d) :
    |(U ω n x : ℝ) - wErr ω n x - uOf ω n x| ≤ wStar ω n x ∧
      |(U ω n x : ℝ) - uOf ω n x| ≤ 2 * wStar ω n x := by
  refine ⟨pathwise_of_labelOrder hd hstep n x, ?_⟩
  have h1 := pathwise_of_labelOrder hd hstep n x
  have h2 := abs_wErr_le_wStar hd ω n x
  calc |(U ω n x : ℝ) - uOf ω n x|
      = |((U ω n x : ℝ) - wErr ω n x - uOf ω n x) + wErr ω n x| := by congr 1; ring
    _ ≤ |(U ω n x : ℝ) - wErr ω n x - uOf ω n x| + |wErr ω n x| := abs_add_le _ _
    _ ≤ wStar ω n x + wStar ω n x := add_le_add h1 h2
    _ = 2 * wStar ω n x := by ring

end LatticeProb.ParticleDrivenAgree

end
