import LatticeProb.Analysis.ContractionSemigroup

/-!
# Backward recursion under varying-space semigroup convergence

Finite backward products of bounded multipliers and contraction semigroups preserve
varying-space convergence. All gaps are nonnegative, including the optional initial gap.
-/

namespace LatticeProb.ContractionSemigroup

open Filter Topology
open scoped NNReal

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
variable {Ln : ℕ → Type*}
  [∀ n, NormedAddCommGroup (Ln n)] [∀ n, NormedSpace ℝ (Ln n)]
  [∀ n, CompleteSpace (Ln n)]

/-- Uniform convergence on bounded time intervals implies convergence at each fixed time. -/
theorem UniformSemigroupConvergence.varyingConverges
    {π : ∀ n, L →L[ℝ] Ln n} {T : StronglyContinuousContractionSemigroup L}
    {Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n)}
    (h : UniformSemigroupConvergence π T Tn) (t : ℝ≥0) (f : L) :
    VaryingConverges π (fun n => (Tn n).operator t (π n f)) (T.operator t f) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (norm_nonneg _))
  · intro b hb
    exact (h f t b hb).mono (fun n hn => hn t le_rfl)

omit [CompleteSpace L] [∀ n, CompleteSpace (Ln n)] in
/-- Uniformly bounded compatible operators preserve varying-space convergence. -/
theorem VaryingConverges.map
    {π : ∀ n, L →L[ℝ] Ln n} {fn : ∀ n, Ln n} {f : L}
    (hf : VaryingConverges π fn f) (A : L →L[ℝ] L)
    (An : ∀ n, Ln n →L[ℝ] Ln n) {K : ℝ} (hK : ∀ n, ‖An n‖ ≤ K)
    (hA : ∀ g, VaryingConverges π (fun n => An n (π n g)) (A g)) :
    VaryingConverges π (fun n => An n (fn n)) (A f) := by
  have hlim := (hf.const_mul K).add (hA f)
  rw [mul_zero, zero_add] at hlim
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  calc
    ‖An n (fn n) - π n (A f)‖ ≤
        ‖An n (fn n) - An n (π n f)‖ + ‖An n (π n f) - π n (A f)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K * ‖fn n - π n f‖ + ‖An n (π n f) - π n (A f)‖ := by
      rw [← map_sub]
      exact add_le_add (((An n).le_of_opNorm_le (hK n) _)) le_rfl

/-- A fixed nonnegative semigroup time preserves convergence of varying input vectors. -/
theorem VaryingConverges.semigroup
    {π : ∀ n, L →L[ℝ] Ln n} {fn : ∀ n, Ln n} {f : L}
    (hf : VaryingConverges π fn f) (T : StronglyContinuousContractionSemigroup L)
    (Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n)) (t : ℝ≥0)
    (hT : ∀ g, VaryingConverges π (fun n => (Tn n).operator t (π n g))
      (T.operator t g)) :
    VaryingConverges π (fun n => (Tn n).operator t (fn n)) (T.operator t f) :=
  hf.map (T.operator t) (fun n => (Tn n).operator t)
    (fun n => (Tn n).norm_le_one t) hT

/-- Backward vectors indexed from zero to the terminal index; each step first evolves,
then multiplies. The terminal vector is the supplied `ξ`. -/
def backwardRecursion (T : StronglyContinuousContractionSemigroup L) :
    (m : ℕ) → (Fin m → L →L[ℝ] L) → (Fin m → ℝ≥0) → L → Fin (m + 1) → L
  | 0, _, _, ξ => fun _ => ξ
  | m + 1, M, Δ, ξ =>
    let tail := backwardRecursion T m (fun j => M j.succ) (fun j => Δ j.succ) ξ
    Fin.cases (M 0 (T.operator (Δ 0) (tail 0))) tail

/-- Every vector of the finite backward recursion converges, from compatibility of
multipliers, fixed-time semigroup convergence, and convergence of terminal vectors. -/
theorem varyingConverges_backwardRecursion
    (π : ∀ n, L →L[ℝ] Ln n) (T : StronglyContinuousContractionSemigroup L)
    (Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n))
    (hT : ∀ t g, VaryingConverges π (fun n => (Tn n).operator t (π n g))
      (T.operator t g))
    (m : ℕ) (M : Fin m → L →L[ℝ] L)
    (Mn : ∀ n, Fin m → Ln n →L[ℝ] Ln n) (Δ : Fin m → ℝ≥0)
    (K : ℝ) (hK : ∀ n j, ‖Mn n j‖ ≤ K)
    (hM : ∀ j g, VaryingConverges π (fun n => Mn n j (π n g)) (M j g))
    (ξ : L) (ξn : ∀ n, Ln n) (hξ : VaryingConverges π ξn ξ) :
    ∀ j, VaryingConverges π (fun n => backwardRecursion (Tn n) m (Mn n) Δ (ξn n) j)
      (backwardRecursion T m M Δ ξ j) := by
  induction m with
  | zero => intro j; exact hξ
  | succ m ih =>
    have htail := ih (fun j => M j.succ) (fun n j => Mn n j.succ)
      (fun j => Δ j.succ) (fun n j => hK n j.succ) (fun j => hM j.succ)
    intro j
    refine Fin.cases ?_ (fun j => htail j) j
    exact ((htail 0).semigroup T Tn (Δ 0) (hT (Δ 0))).map
      (M 0) (fun n => Mn n 0) (fun n => hK n 0) (hM 0)

/-- The convergent backward recursion may be preceded by one further semigroup step,
without a multiplier, as needed for the initial pairing. -/
theorem varyingConverges_semigroup_backwardRecursion
    (π : ∀ n, L →L[ℝ] Ln n) (T : StronglyContinuousContractionSemigroup L)
    (Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n))
    (hT : ∀ t g, VaryingConverges π (fun n => (Tn n).operator t (π n g))
      (T.operator t g))
    (m : ℕ) (M : Fin m → L →L[ℝ] L)
    (Mn : ∀ n, Fin m → Ln n →L[ℝ] Ln n) (Δ : Fin m → ℝ≥0)
    (K : ℝ) (hK : ∀ n j, ‖Mn n j‖ ≤ K)
    (hM : ∀ j g, VaryingConverges π (fun n => Mn n j (π n g)) (M j g))
    (ξ : L) (ξn : ∀ n, Ln n) (hξ : VaryingConverges π ξn ξ)
    (t : ℝ≥0) (j : Fin (m + 1)) :
    VaryingConverges π
      (fun n => (Tn n).operator t (backwardRecursion (Tn n) m (Mn n) Δ (ξn n) j))
      (T.operator t (backwardRecursion T m M Δ ξ j)) :=
  (varyingConverges_backwardRecursion π T Tn hT m M Mn Δ K hK hM ξ ξn hξ j).semigroup
    T Tn t (hT t)

end LatticeProb.ContractionSemigroup
