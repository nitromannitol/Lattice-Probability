/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanLimitAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux

/-!
# Node `M46` (`Draft.RecordMeanLimit`), auxiliary part 2: the parameter space

A constrained configuration is encoded by a vector `p : Fin (M + 4) → ℝ`, `M = 16 ^ n`:

* `p j` for `0 < j < M` are the node values `f (j / M)` of the profile (`p 0` is ignored);
* `p M + i p (M+1)` and `p (M+2) + i p (M+3)` are the endpoint offsets `p₀`, `p₁`.

The profile `fOf n p ∈ V n` is the mesh interpolation (`Subadd.coarse`) of the node values.  We
prove membership in `V n`, the node identity, sup-norm bounds, Lipschitz dependence on `p`, the
discrete formula for the energy, continuity, and compactness of the parameter set `Kset`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RML

open Blueprint.Draft

/-! ## Node values and the profile -/

/-- Node values of a parameter vector: `p j` for `0 < j < M`, and `0` otherwise. -/
def nodeV (M : ℕ) (p : Fin (M + 4) → ℝ) (j : ℕ) : ℝ :=
  if h : 0 < j ∧ j < M then p ⟨j, by omega⟩ else 0

/-- A function on `ℝ` with the node values at the mesh points `j / M`. -/
def nodeF (M : ℕ) (p : Fin (M + 4) → ℝ) (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then nodeV M p ⌊(M : ℝ) * x⌋₊ else 0

/-- The profile of a parameter vector. -/
def fOf (n : ℕ) (p : Fin (16 ^ n + 4) → ℝ) : ℝ → ℝ := Subadd.coarse n (nodeF (16 ^ n) p)

/-- The offset `p₀` of a parameter vector. -/
def p0Of (M : ℕ) (p : Fin (M + 4) → ℝ) : ℂ :=
  (p ⟨M, by omega⟩ : ℂ) + (p ⟨M + 1, by omega⟩ : ℂ) * Complex.I

/-- The offset `p₁` of a parameter vector. -/
def p1Of (M : ℕ) (p : Fin (M + 4) → ℝ) : ℂ :=
  (p ⟨M + 2, by omega⟩ : ℂ) + (p ⟨M + 3, by omega⟩ : ℂ) * Complex.I

variable {M : ℕ}

@[simp] lemma p0Of_re (p : Fin (M + 4) → ℝ) : (p0Of M p).re = p ⟨M, by omega⟩ := by
  simp [p0Of]

@[simp] lemma p0Of_im (p : Fin (M + 4) → ℝ) : (p0Of M p).im = p ⟨M + 1, by omega⟩ := by
  simp [p0Of]

@[simp] lemma p1Of_re (p : Fin (M + 4) → ℝ) : (p1Of M p).re = p ⟨M + 2, by omega⟩ := by
  simp [p1Of]

@[simp] lemma p1Of_im (p : Fin (M + 4) → ℝ) : (p1Of M p).im = p ⟨M + 3, by omega⟩ := by
  simp [p1Of]

lemma nodeF_out (p : Fin (M + 4) → ℝ) {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : nodeF M p x = 0 := by
  unfold nodeF
  rw [if_neg]
  rintro ⟨h0, h1⟩
  exact hx ⟨h0.le, h1.le⟩

lemma nodeF_zero (p : Fin (M + 4) → ℝ) : nodeF M p 0 = 0 := by
  simp [nodeF]

lemma nodeF_one (p : Fin (M + 4) → ℝ) : nodeF M p 1 = 0 := by
  simp [nodeF]

lemma nodeF_node (hM : 0 < M) (p : Fin (M + 4) → ℝ) (j : ℕ) :
    nodeF M p ((j : ℝ) / M) = nodeV M p j := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold nodeF
  split_ifs with h
  · congr 1
    rw [mul_div_cancel₀ _ hM'.ne', Nat.floor_natCast]
  · unfold nodeV
    rw [dif_neg]
    rintro ⟨hj0, hjM⟩
    apply h
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hM']
    exact_mod_cast hjM

lemma fOf_mem (n : ℕ) (p : Fin (16 ^ n + 4) → ℝ) : fOf n p ∈ V n :=
  Subadd.coarse_mem n (nodeF_zero p) (nodeF_one p) fun _ hx => nodeF_out p hx

lemma fOf_node (n : ℕ) (p : Fin (16 ^ n + 4) → ℝ) (i : ℕ) :
    fOf n p ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) = nodeV (16 ^ n) p i := by
  have e : ((16 ^ n : ℕ) : ℝ) = (16 : ℝ) ^ n := by push_cast; ring
  rw [e]
  unfold fOf
  rw [Subadd.coarse_node n _ (i : ℝ) ⟨i, by simp⟩, ← e]
  exact nodeF_node (by positivity) p i

lemma fOf_zero (n : ℕ) (p : Fin (16 ^ n + 4) → ℝ) : fOf n p 0 = 0 := (fOf_mem n p).1

/-! ## Bounds -/

lemma abs_nodeV_le {p : Fin (M + 4) → ℝ} {B : ℝ} (h : ∀ i, |p i| ≤ B) (hB : 0 ≤ B) (j : ℕ) :
    |nodeV M p j| ≤ B := by
  unfold nodeV
  split_ifs
  · exact h _
  · simpa using hB

lemma abs_nodeF_le {p : Fin (M + 4) → ℝ} {B : ℝ} (h : ∀ i, |p i| ≤ B) (hB : 0 ≤ B) (x : ℝ) :
    |nodeF M p x| ≤ B := by
  unfold nodeF
  split_ifs
  · exact abs_nodeV_le h hB _
  · simpa using hB

lemma abs_coarse_le (n : ℕ) {g : ℝ → ℝ} {B : ℝ} (hg : ∀ y, |g y| ≤ B) (x : ℝ) :
    |Subadd.coarse n g x| ≤ B := by
  unfold Subadd.coarse
  set r : ℝ := (16 : ℝ) ^ n * x
  have h1 := Int.floor_le r
  have h2 := Int.lt_floor_add_one r
  set t : ℝ := r - ((⌊r⌋ : ℤ) : ℝ)
  have ht0 : 0 ≤ t := by simp only [t]; linarith
  have ht1 : 0 ≤ 1 - t := by simp only [t]; linarith
  set a := g (((⌊r⌋ : ℤ) : ℝ) / 16 ^ n)
  set b := g ((((⌊r⌋ : ℤ) : ℝ) + 1) / 16 ^ n)
  have ha : |a| ≤ B := hg _
  have hb : |b| ≤ B := hg _
  calc |(1 - t) * a + t * b| ≤ |(1 - t) * a| + |t * b| := abs_add_le _ _
    _ = (1 - t) * |a| + t * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht1]
    _ ≤ (1 - t) * B + t * B := by gcongr
    _ = B := by ring

lemma coarse_sub (n : ℕ) (g g' : ℝ → ℝ) (x : ℝ) :
    Subadd.coarse n g x - Subadd.coarse n g' x = Subadd.coarse n (fun y => g y - g' y) x := by
  unfold Subadd.coarse
  ring

lemma abs_fOf_le (n : ℕ) {p : Fin (16 ^ n + 4) → ℝ} {B : ℝ} (h : ∀ i, |p i| ≤ B) (hB : 0 ≤ B)
    (x : ℝ) : |fOf n p x| ≤ B :=
  abs_coarse_le n (abs_nodeF_le h hB) x

lemma abs_fOf_sub_le (n : ℕ) (p q : Fin (16 ^ n + 4) → ℝ) (x : ℝ) :
    |fOf n p x - fOf n q x| ≤ ‖p - q‖ := by
  unfold fOf
  rw [coarse_sub]
  refine abs_coarse_le n (fun y => ?_) x
  unfold nodeF
  split_ifs
  · unfold nodeV
    split_ifs
    · have := norm_le_pi_norm (p - q) ⟨⌊((16 ^ n : ℕ) : ℝ) * y⌋₊, by omega⟩
      simpa [Real.norm_eq_abs] using this
    · simp
  · simp

/-! ## Energy -/

lemma energy_fOf (n : ℕ) (p : Fin (16 ^ n + 4) → ℝ) :
    energy (fOf n p) = (16 ^ n / 2) * ∑ k ∈ Finset.range (16 ^ n),
      (nodeV (16 ^ n) p (k + 1) - nodeV (16 ^ n) p k) ^ 2 := by
  rw [Subadd.V_energy (fOf_mem n p)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ((16 : ℝ) ^ n) = ((16 ^ n : ℕ) : ℝ) := by push_cast; ring
  have e1 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, e1, fOf_node, fOf_node]

lemma continuous_nodeV (j : ℕ) : Continuous fun p : Fin (M + 4) → ℝ => nodeV M p j := by
  unfold nodeV
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma continuous_energy_fOf (n : ℕ) :
    Continuous fun p : Fin (16 ^ n + 4) → ℝ => energy (fOf n p) := by
  have e : (fun p : Fin (16 ^ n + 4) → ℝ => energy (fOf n p)) = fun p =>
      (16 ^ n / 2) * ∑ k ∈ Finset.range (16 ^ n),
        (nodeV (16 ^ n) p (k + 1) - nodeV (16 ^ n) p k) ^ 2 :=
    funext fun p => energy_fOf n p
  rw [e]
  exact continuous_const.mul (continuous_finset_sum _ fun k _ =>
    ((continuous_nodeV _).sub (continuous_nodeV _)).pow 2)

lemma continuous_p0Of : Continuous (p0Of M) := by
  unfold p0Of
  fun_prop

lemma continuous_p1Of : Continuous (p1Of M) := by
  unfold p1Of
  fun_prop

lemma norm_cplx_sub_le (a b a' b' : ℝ) :
    ‖((a : ℂ) + (b : ℂ) * Complex.I) - ((a' : ℂ) + (b' : ℂ) * Complex.I)‖ ≤ |a - a'| + |b - b'| := by
  have e : ((a : ℂ) + (b : ℂ) * Complex.I) - ((a' : ℂ) + (b' : ℂ) * Complex.I) =
      ((a - a' : ℝ) : ℂ) + ((b - b' : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

lemma norm_p0Of_sub_le (p q : Fin (M + 4) → ℝ) : ‖p0Of M p - p0Of M q‖ ≤ 2 * ‖p - q‖ := by
  refine (norm_cplx_sub_le _ _ _ _).trans ?_
  have h1 := norm_le_pi_norm (p - q) ⟨M, by omega⟩
  have h2 := norm_le_pi_norm (p - q) ⟨M + 1, by omega⟩
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h1 h2
  linarith

lemma norm_p1Of_sub_le (p q : Fin (M + 4) → ℝ) : ‖p1Of M p - p1Of M q‖ ≤ 2 * ‖p - q‖ := by
  refine (norm_cplx_sub_le _ _ _ _).trans ?_
  have h1 := norm_le_pi_norm (p - q) ⟨M + 2, by omega⟩
  have h2 := norm_le_pi_norm (p - q) ⟨M + 3, by omega⟩
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h1 h2
  linarith

/-! ## The compact parameter set -/

/-- The compact parameter set: box `B`, energy at most `k + 2`, offsets of norm at most `ρ`. -/
def Kset (n k : ℕ) (B ρ : ℝ) : Set (Fin (16 ^ n + 4) → ℝ) :=
  {p | (∀ i, |p i| ≤ B) ∧ energy (fOf n p) ≤ k + 2 ∧ ‖p0Of (16 ^ n) p‖ ≤ ρ ∧
    ‖p1Of (16 ^ n) p‖ ≤ ρ}

lemma isCompact_Kset (n k : ℕ) {B : ℝ} (hB : 0 ≤ B) (ρ : ℝ) : IsCompact (Kset n k B ρ) := by
  refine (isCompact_closedBall (0 : Fin (16 ^ n + 4) → ℝ) B).of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {p : Fin (16 ^ n + 4) → ℝ | ∀ i, |p i| ≤ B} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const
    have h2 : IsClosed {p : Fin (16 ^ n + 4) → ℝ | energy (fOf n p) ≤ k + 2} :=
      isClosed_le (continuous_energy_fOf n) continuous_const
    have h3 : IsClosed {p : Fin (16 ^ n + 4) → ℝ | ‖p0Of (16 ^ n) p‖ ≤ ρ} :=
      isClosed_le continuous_p0Of.norm continuous_const
    have h4 : IsClosed {p : Fin (16 ^ n + 4) → ℝ | ‖p1Of (16 ^ n) p‖ ≤ ρ} :=
      isClosed_le continuous_p1Of.norm continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  · intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB]
    intro i
    rw [Real.norm_eq_abs]
    exact hp.1 i

end LQGDimension.RML
