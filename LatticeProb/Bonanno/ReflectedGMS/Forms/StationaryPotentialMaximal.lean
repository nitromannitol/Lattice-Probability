/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryPotentialMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryGridMaximal
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryGridReversal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Maximal energy bound for the actual stationary grid potential

The centered Doob martingale controls only the martingale part of the decoded
potential.  Stationary path reversal turns the discrete forward/backward
compensation identity into a finite-grid maximal bound for the potential
itself: the compensated forward and backward parts are two evaluations of one
scalar functional of the finite grid path, and the stationary reversal identity
for finite-dimensional laws transfers the second moment of that functional.
The remaining drift terms are summed and controlled by the semigroup quadratic
deficit.
-/

-- Merged from `ReflectedGMS/Forms/ReversibleDiscreteDecomposition.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ReversibleDiscreteDecomposition

/-! The finite-path algebra behind the forward/backward martingale
decomposition. The endpoint drift correction is retained exactly. -/
set_option autoImplicit false

namespace ReflectedGMS

private theorem sum_reverse_prefix (d : ℕ → ℝ) {n N : ℕ} (hn : n ≤ N) :
    (∑ i ∈ Finset.range n, d (N - i)) =
      ∑ i ∈ Finset.range n, d (N - n + i + 1) := by
  calc
    _ = ∑ i ∈ Finset.range n, d (N - (n - 1 - i)) :=
      (Finset.sum_range_reflect (fun i => d (N - i)) n).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 1
      omega

/-- For discrete compensation by a drift sequence, the forward/backward
identity has an endpoint correction. This algebraic statement can be applied
to the existing `martingalePart` after identifying its predictable term. -/
theorem reversible_discrete_compensation_identity
    (u d : ℕ → ℝ) {k N : ℕ} (hk : k ≤ N) :
    let M : ℕ → ℝ := fun j => u j - u 0 - ∑ i ∈ Finset.range j, d i
    let R : ℕ → ℝ := fun j =>
      u (N - j) - u N - ∑ i ∈ Finset.range j, d (N - i)
    u k - u 0 = (1 / 2 : ℝ) * (M k - (R N - R (N - k))) -
      (1 / 2 : ℝ) * (d k - d 0) := by
  have hsN := sum_reverse_prefix d (n := N) le_rfl
  simp only [Nat.sub_self, Nat.zero_add] at hsN
  have hsNk := sum_reverse_prefix d (n := N - k) (Nat.sub_le N k)
  rw [Nat.sub_sub_self hk] at hsNk
  have hsplit := Finset.sum_range_add (fun i => d (i + 1)) k (N - k)
  have hnk : k + (N - k) = N := by omega
  rw [hnk] at hsplit
  have hleft := Finset.sum_range_succ d k
  have hright := Finset.sum_range_succ' d k
  dsimp only
  simp only [Nat.sub_self, Nat.sub_sub_self hk]
  linarith only [hsN, hsNk, hsplit, hleft, hright]

end ReflectedGMS

end Merged_ReversibleDiscreteDecomposition

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ### Deterministic scalar estimates -/

/- The forward/backward compensation identity turns uniform bounds on the two
compensated parts and on the drift into a bound for the actual increment. -/
theorem abs_sub_le_of_compensation
    (u d : ℕ → ℝ) {k N : ℕ} (hk : k ≤ N) {a b c : ℝ}
    (ha : ∀ j, j ≤ N →
      |u j - u 0 - ∑ i ∈ Finset.range j, d i| ≤ a)
    (hb : ∀ j, j ≤ N →
      |u (N - j) - u N - ∑ i ∈ Finset.range j, d (N - i)| ≤ b)
    (hc : ∀ j, j ≤ N → |d j| ≤ c) :
    |u k - u 0| ≤ a / 2 + b + c := by
  have hid : u k - u 0 =
      (1 / 2 : ℝ) * ((u k - u 0 - ∑ i ∈ Finset.range k, d i) -
          ((u (N - N) - u N - ∑ i ∈ Finset.range N, d (N - i)) -
            (u (N - (N - k)) - u N -
              ∑ i ∈ Finset.range (N - k), d (N - i)))) -
        (1 / 2 : ℝ) * (d k - d 0) :=
    reversible_discrete_compensation_identity u d hk
  have h1 := abs_le.1 (ha k hk)
  have h2 := abs_le.1 (hb N le_rfl)
  have h3 := abs_le.1 (hb (N - k) (Nat.sub_le N k))
  have h4 := abs_le.1 (hc k hk)
  have h5 := abs_le.1 (hc 0 (Nat.zero_le N))
  rw [abs_le]
  constructor
  · rw [hid]; linarith
  · rw [hid]; linarith

/- Generic scalar integral algebra for a three-term dominating bound, kept
separate from the semigroup expressions it is applied to. -/
theorem integral_three_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {F A B S : Ω → ℝ} {ca cb cs : ℝ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hS : Integrable S μ)
    (hF0 : ∀ ω, 0 ≤ F ω)
    (hF : ∀ ω, F ω ≤ 3 / 4 * A ω + 3 * B ω + 3 * S ω)
    (hAle : (∫ ω, A ω ∂μ) ≤ ca) (hBle : (∫ ω, B ω ∂μ) ≤ cb)
    (hSle : (∫ ω, S ω ∂μ) ≤ cs) :
    (∫ ω, F ω ∂μ) ≤ 3 / 4 * ca + 3 * cb + 3 * cs := by
  have hint : Integrable (fun ω => 3 / 4 * A ω + 3 * B ω + 3 * S ω) μ :=
    ((hA.const_mul _).add (hB.const_mul _)).add (hS.const_mul _)
  calc
    (∫ ω, F ω ∂μ) ≤ ∫ ω, (3 / 4 * A ω + 3 * B ω + 3 * S ω) ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall hF0) hint
        (Eventually.of_forall hF)
    _ = 3 / 4 * (∫ ω, A ω ∂μ) + 3 * (∫ ω, B ω ∂μ) +
        3 * ∫ ω, S ω ∂μ := by
      rw [integral_add (f := fun ω => 3 / 4 * A ω + 3 * B ω)
          (g := fun ω => 3 * S ω)
          ((hA.const_mul _).add (hB.const_mul _)) (hS.const_mul _),
        integral_add (f := fun ω => 3 / 4 * A ω) (g := fun ω => 3 * B ω)
          (hA.const_mul _) (hB.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ 3 / 4 * ca + 3 * cb + 3 * cs := by linarith

/- Generic square expansion for the three-term maximal bound. -/
theorem sq_le_of_three_bound {A a b c S : ℝ} (hA0 : 0 ≤ A)
    (hAle : A ≤ a / 2 + b + c) (hc2 : c ^ 2 ≤ S) :
    A ^ 2 ≤ 3 / 4 * a ^ 2 + 3 * b ^ 2 + 3 * S := by
  nlinarith [mul_self_le_mul_self hA0 hAle, sq_nonneg (a / 2 - b),
    sq_nonneg (a / 2 - c), sq_nonneg (b - c)]

/-! ### Scalar functionals of a finite grid path -/

/-- The one-step semigroup drift vector of a full-energy potential. -/
noncomputable def gridDriftVector (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) : ValueSpace V :=
  fullFormSemigroup G m δ (valueInclusion G m U) - valueInclusion G m U

/-- The decoded potential of a finite grid path at a time index. -/
noncomputable def gridPathPotential (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) {N : ℕ} (p : Fin (N + 1) → Option V) (j : ℕ) : ℝ :=
  if h : j < N + 1 then
    (p ⟨j, h⟩).elim 0 (unweight m (valueInclusion G m U)) else 0

/-- The decoded one-step drift of a finite grid path at a time index. -/
noncomputable def gridPathDrift (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ} (p : Fin (N + 1) → Option V)
    (j : ℕ) : ℝ :=
  if h : j < N + 1 then
    (p ⟨j, h⟩).elim 0 (unweight m (gridDriftVector G m U δ)) else 0

/-- The compensated potential increment of a finite grid path. -/
noncomputable def gridPathCompensated (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ} (p : Fin (N + 1) → Option V)
    (j : ℕ) : ℝ :=
  gridPathPotential G m U p j - gridPathPotential G m U p 0 -
    ∑ i ∈ Finset.range j, gridPathDrift G m U δ p i

/-- The finite maximal compensated increment of a grid path. -/
noncomputable def gridPathMaxCompensated (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ}
    (p : Fin (N + 1) → Option V) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |gridPathCompensated G m U δ p k|)

/-- The finite maximal decoded drift of a grid path. -/
noncomputable def gridPathMaxDrift (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ}
    (p : Fin (N + 1) → Option V) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |gridPathDrift G m U δ p k|)

theorem abs_gridPathCompensated_le (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ} (p : Fin (N + 1) → Option V)
    {j : ℕ} (hj : j ≤ N) :
    |gridPathCompensated G m U δ p j| ≤ gridPathMaxCompensated G m U δ p :=
  Finset.le_sup' (fun k => |gridPathCompensated G m U δ p k|)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem abs_gridPathDrift_le (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ} (p : Fin (N + 1) → Option V)
    {j : ℕ} (hj : j ≤ N) :
    |gridPathDrift G m U δ p j| ≤ gridPathMaxDrift G m U δ p :=
  Finset.le_sup' (fun k => |gridPathDrift G m U δ p k|)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem gridPathMaxCompensated_nonneg (G : ConductanceGraph V)
    (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ}
    (p : Fin (N + 1) → Option V) :
    0 ≤ gridPathMaxCompensated G m U δ p :=
  le_trans (abs_nonneg _) (abs_gridPathCompensated_le G m U δ p (Nat.zero_le N))

theorem gridPathMaxCompensated_le_sum (G : ConductanceGraph V)
    (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ}
    (p : Fin (N + 1) → Option V) :
    gridPathMaxCompensated G m U δ p ≤
      ∑ k ∈ Finset.range (N + 1), |gridPathCompensated G m U δ p k| := by
  apply (Finset.sup'_le_iff Finset.nonempty_range_add_one _).2
  intro k hk
  exact Finset.single_le_sum
    (f := fun i => |gridPathCompensated G m U δ p i|)
    (fun i _ => abs_nonneg _) hk

theorem gridPathMaxDrift_sq_le_sum (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) {N : ℕ} (p : Fin (N + 1) → Option V) :
    (gridPathMaxDrift G m U δ p) ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1), (gridPathDrift G m U δ p j) ^ 2 := by
  obtain ⟨j, hj, hval⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_add_one (n := N))
    (fun k => |gridPathDrift G m U δ p k|)
  have hmax : gridPathMaxDrift G m U δ p = |gridPathDrift G m U δ p j| := hval
  rw [hmax, sq_abs]
  exact Finset.single_le_sum (fun i _ => sq_nonneg _) hj

/-! ### Evaluation on the actual forward and reversed grids -/

theorem gridPathPotential_forward (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) {j : ℕ} (hj : j ≤ N) :
    gridPathPotential G m U (reflectedGridPath PF δ N ω) j =
      stationaryGridPotential PF G m U δ j ω := by
  rw [gridPathPotential, dif_pos (Nat.lt_succ_of_le hj)]
  rfl

theorem gridPathDrift_forward (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) {j : ℕ} (hj : j ≤ N) :
    gridPathDrift G m U δ (reflectedGridPath PF δ N ω) j =
      stationaryGridDrift PF G m U δ j ω := by
  rw [gridPathDrift, dif_pos (Nat.lt_succ_of_le hj)]
  rfl

theorem gridPathPotential_reverse (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) {j : ℕ} (hj : j ≤ N) :
    gridPathPotential G m U (reflectedReverseGridPath PF δ N ω) j =
      stationaryGridPotential PF G m U δ (N - j) ω := by
  have hj' : j < N + 1 := Nat.lt_succ_of_le hj
  have hrev : ((⟨j, hj'⟩ : Fin (N + 1)).rev : ℕ) = N - j := by
    change N + 1 - (j + 1) = N - j
    omega
  rw [gridPathPotential, dif_pos hj']
  show (PF.X ((((⟨j, hj'⟩ : Fin (N + 1)).rev : ℕ) : ℝ≥0) * δ) ω).elim 0
      (unweight m (valueInclusion G m U)) = _
  rw [hrev]
  rfl

theorem gridPathDrift_reverse (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) {j : ℕ} (hj : j ≤ N) :
    gridPathDrift G m U δ (reflectedReverseGridPath PF δ N ω) j =
      stationaryGridDrift PF G m U δ (N - j) ω := by
  have hj' : j < N + 1 := Nat.lt_succ_of_le hj
  have hrev : ((⟨j, hj'⟩ : Fin (N + 1)).rev : ℕ) = N - j := by
    change N + 1 - (j + 1) = N - j
    omega
  rw [gridPathDrift, dif_pos hj']
  show (PF.X ((((⟨j, hj'⟩ : Fin (N + 1)).rev : ℕ) : ℝ≥0) * δ) ω).elim 0
      (unweight m (gridDriftVector G m U δ)) = _
  rw [hrev]
  rfl

theorem gridPathCompensated_forward (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) {k : ℕ} (hk : k ≤ N) :
    gridPathCompensated G m U δ (reflectedGridPath PF δ N ω) k =
      stationaryGridPotential PF G m U δ k ω -
        stationaryGridPotential PF G m U δ 0 ω -
        ∑ i ∈ Finset.range k, stationaryGridDrift PF G m U δ i ω := by
  rw [gridPathCompensated, gridPathPotential_forward PF G m U δ N ω hk,
    gridPathPotential_forward PF G m U δ N ω (Nat.zero_le N)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact gridPathDrift_forward PF G m U δ N ω
    (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))

theorem gridPathCompensated_reverse (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) {k : ℕ} (hk : k ≤ N) :
    gridPathCompensated G m U δ (reflectedReverseGridPath PF δ N ω) k =
      stationaryGridPotential PF G m U δ (N - k) ω -
        stationaryGridPotential PF G m U δ N ω -
        ∑ i ∈ Finset.range k, stationaryGridDrift PF G m U δ (N - i) ω := by
  rw [gridPathCompensated, gridPathPotential_reverse PF G m U δ N ω hk,
    gridPathPotential_reverse PF G m U δ N ω (Nat.zero_le N), Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact gridPathDrift_reverse PF G m U δ N ω
    (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))

/-! ### The pointwise maximal decomposition -/

/-- Pathwise forward/backward decomposition of the actual grid potential: the
maximal potential increment is bounded by the forward compensated maximum, the
reversed compensated maximum and the maximal drift. -/
theorem stationaryGridPotential_max_abs_le (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) (δ : ℝ≥0)
    (N : ℕ) (ω : PF.Ω) :
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |stationaryGridPotential PF G m U δ k ω -
          stationaryGridPotential PF G m U δ 0 ω|) ≤
      gridPathMaxCompensated G m U δ (reflectedGridPath PF δ N ω) / 2 +
        gridPathMaxCompensated G m U δ (reflectedReverseGridPath PF δ N ω) +
        gridPathMaxDrift G m U δ (reflectedGridPath PF δ N ω) := by
  have ha : ∀ j, j ≤ N →
      |stationaryGridPotential PF G m U δ j ω -
        stationaryGridPotential PF G m U δ 0 ω -
        ∑ i ∈ Finset.range j, stationaryGridDrift PF G m U δ i ω| ≤
      gridPathMaxCompensated G m U δ (reflectedGridPath PF δ N ω) := by
    intro j hj
    rw [← gridPathCompensated_forward PF G m U δ N ω hj]
    exact abs_gridPathCompensated_le G m U δ _ hj
  have hb : ∀ j, j ≤ N →
      |stationaryGridPotential PF G m U δ (N - j) ω -
        stationaryGridPotential PF G m U δ N ω -
        ∑ i ∈ Finset.range j, stationaryGridDrift PF G m U δ (N - i) ω| ≤
      gridPathMaxCompensated G m U δ (reflectedReverseGridPath PF δ N ω) := by
    intro j hj
    rw [← gridPathCompensated_reverse PF G m U δ N ω hj]
    exact abs_gridPathCompensated_le G m U δ _ hj
  have hc : ∀ j, j ≤ N →
      |stationaryGridDrift PF G m U δ j ω| ≤
      gridPathMaxDrift G m U δ (reflectedGridPath PF δ N ω) := by
    intro j hj
    rw [← gridPathDrift_forward PF G m U δ N ω hj]
    exact abs_gridPathDrift_le G m U δ _ hj
  apply (Finset.sup'_le_iff Finset.nonempty_range_add_one _).2
  intro k hk
  exact abs_sub_le_of_compensation
    (fun j => stationaryGridPotential PF G m U δ j ω)
    (fun j => stationaryGridDrift PF G m U δ j ω)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) ha hb hc

/-! ### Stationary second moments -/

/- Marginal stationarity: the decoded square of any weighted `L²` vector has the
exact ambient norm at every grid time. -/
theorem integral_sq_unweight_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (W : ValueSpace V) (t : ℝ≥0) :
    (∫ ω, ((PF.X t ω).elim 0 (unweight m W)) ^ 2 ∂reflectedSpeedLaw PF m) =
      ‖W‖ ^ 2 := by
  have hraw : Measurable (fun q : Option V => q.elim 0 (unweight m W)) :=
    measurable_of_countable _
  calc
    (∫ ω, ((PF.X t ω).elim 0 (unweight m W)) ^ 2 ∂reflectedSpeedLaw PF m) =
        ∫ q, (q.elim 0 (unweight m W)) ^ 2
          ∂(reflectedSpeedLaw PF m).map (PF.X t) :=
      (integral_map (PF.measurable_X t).aemeasurable
        (hraw.pow_const 2).aestronglyMeasurable).symm
    _ = ∫ q, (q.elim 0 (unweight m W)) ^ 2
          ∂(vertexSpeedMeasure m).map (some : V → Option V) := by
      rw [reflectedSpeedLaw_map_position h hG hm hmsum t]
    _ = ∫ x, (unweight m W x) ^ 2 ∂vertexSpeedMeasure m := by
      simpa only [Option.elim_some] using
        integral_map (measurable_of_countable (some : V → Option V)).aemeasurable
          (hraw.pow_const 2).aestronglyMeasurable
    _ = ‖weightedValue m (unweight m W) (hasSpeedL2_unweight m hm W)‖ ^ 2 := by
      rw [vertexSpeedMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
      simp only [ENNReal.toReal_ofReal (hm _).le, smul_eq_mul]
      exact (weightedValue_norm_sq m hm (unweight m W)
        (hasSpeedL2_unweight m hm W)).symm
    _ = ‖W‖ ^ 2 := by rw [weightedValue_unweight m hm W]

/-- The stationary second moment of the one-step semigroup drift is controlled
by the quadratic energy deficit. -/
theorem norm_gridDriftVector_sq_le (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (U : hilbertDomain G m) (δ : ℝ≥0) :
    ‖gridDriftVector G m U δ‖ ^ 2 ≤
      2 * ((δ : ℝ) * G.Energy (unweight m (valueInclusion G m U))) := by
  have hdef := fullFormSemigroup_quadratic_deficit_le_energy G m hm U δ
  have hcontr :
      ‖fullFormSemigroup G m δ (valueInclusion G m U)‖ ≤
        ‖valueInclusion G m U‖ := by
    calc ‖fullFormSemigroup G m δ (valueInclusion G m U)‖ ≤
        ‖fullFormSemigroup G m δ‖ * ‖valueInclusion G m U‖ :=
      ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖valueInclusion G m U‖ :=
        mul_le_mul_of_nonneg_right (fullFormSemigroup_norm_le_one G m δ)
          (norm_nonneg _)
      _ = ‖valueInclusion G m U‖ := one_mul _
  have hsq : ‖fullFormSemigroup G m δ (valueInclusion G m U)‖ ^ 2 ≤
      ‖valueInclusion G m U‖ ^ 2 := by
    nlinarith [norm_nonneg (fullFormSemigroup G m δ (valueInclusion G m U)),
      hcontr]
  have hsymm :
      ⟪fullFormSemigroup G m δ (valueInclusion G m U),
        valueInclusion G m U⟫_ℝ =
      ⟪valueInclusion G m U,
        fullFormSemigroup G m δ (valueInclusion G m U)⟫_ℝ :=
    real_inner_comm _ _
  unfold gridDriftVector
  rw [norm_sub_sq_real, hsymm]
  linarith

/-! ### Integrability and second moments of the path functionals -/

theorem memLp_two_stationaryGridDrift
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (j : ℕ) :
    MemLp (stationaryGridDrift PF G m U δ j) 2 (reflectedSpeedLaw PF m) :=
  memLp_two_reflected_unweight_speedLaw h hG hm hmsum
    (gridDriftVector G m U δ) (stationaryGridTime δ j)

theorem memLp_two_gridPathCompensated_forward
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (N : ℕ)
    {k : ℕ} (hk : k ≤ N) :
    MemLp (fun ω =>
        gridPathCompensated G m U δ (reflectedGridPath PF δ N ω) k) 2
      (reflectedSpeedLaw PF m) := by
  have heq : (fun ω =>
      gridPathCompensated G m U δ (reflectedGridPath PF δ N ω) k) =
      fun ω => stationaryGridPotential PF G m U δ k ω -
        stationaryGridPotential PF G m U δ 0 ω -
        ∑ i ∈ Finset.range k, stationaryGridDrift PF G m U δ i ω := by
    funext ω
    exact gridPathCompensated_forward PF G m U δ N ω hk
  rw [heq]
  have hY : ∀ j, MemLp (stationaryGridPotential PF G m U δ j) 2
      (reflectedSpeedLaw PF m) := fun j =>
    memLp_two_reflected_unweight_speedLaw h hG hm hmsum
      (valueInclusion G m U) (stationaryGridTime δ j)
  have hsum : MemLp (fun ω =>
      ∑ i ∈ Finset.range k, stationaryGridDrift PF G m U δ i ω) 2
      (reflectedSpeedLaw PF m) :=
    memLp_finsetSum (Finset.range k) fun i _ =>
      memLp_two_stationaryGridDrift h hG hm hmsum U δ i
  exact ((hY k).sub (hY 0)).sub hsum

theorem memLp_two_gridPathMaxCompensated_forward
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (N : ℕ) :
    MemLp (fun ω =>
        gridPathMaxCompensated G m U δ (reflectedGridPath PF δ N ω)) 2
      (reflectedSpeedLaw PF m) := by
  have hdom : MemLp (fun ω =>
      ∑ k ∈ Finset.range (N + 1),
        |gridPathCompensated G m U δ (reflectedGridPath PF δ N ω) k|) 2
      (reflectedSpeedLaw PF m) :=
    memLp_finsetSum (Finset.range (N + 1)) fun k hk => by
      simpa only [Real.norm_eq_abs] using
        (memLp_two_gridPathCompensated_forward h hG hm hmsum U δ N
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).norm
  refine MemLp.mono' hdom ?_ (Eventually.of_forall fun ω => ?_)
  · exact ((measurable_of_countable
      (fun p : Fin (N + 1) → Option V =>
        gridPathMaxCompensated G m U δ p)).comp
      (measurable_reflectedGridPath PF δ N)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (gridPathMaxCompensated_nonneg G m U δ _)]
    exact gridPathMaxCompensated_le_sum G m U δ _

/-- Stationary reversal transfers the second moment of the compensated maximal
functional from the forward grid to the reversed grid. -/
theorem integral_sq_gridPathMaxCompensated_reverse_eq
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (N : ℕ) :
    (∫ ω, (gridPathMaxCompensated G m U δ
        (reflectedReverseGridPath PF δ N ω)) ^ 2 ∂reflectedSpeedLaw PF m) =
      ∫ ω, (gridPathMaxCompensated G m U δ
        (reflectedGridPath PF δ N ω)) ^ 2 ∂reflectedSpeedLaw PF m := by
  have hq : Measurable (fun p : Fin (N + 1) → Option V =>
      (gridPathMaxCompensated G m U δ p) ^ 2) := measurable_of_countable _
  calc
    (∫ ω, (gridPathMaxCompensated G m U δ
        (reflectedReverseGridPath PF δ N ω)) ^ 2 ∂reflectedSpeedLaw PF m) =
        ∫ p, (gridPathMaxCompensated G m U δ p) ^ 2
          ∂(reflectedSpeedLaw PF m).map (reflectedReverseGridPath PF δ N) :=
      (integral_map (measurable_reflectedReverseGridPath PF δ N).aemeasurable
        hq.aestronglyMeasurable).symm
    _ = ∫ p, (gridPathMaxCompensated G m U δ p) ^ 2
          ∂(reflectedSpeedLaw PF m).map (reflectedGridPath PF δ N) := by
      rw [reflectedSpeedLaw_map_reflectedGridPath_reverse h hG hm hmsum δ N]
    _ = ∫ ω, (gridPathMaxCompensated G m U δ
          (reflectedGridPath PF δ N ω)) ^ 2 ∂reflectedSpeedLaw PF m :=
      integral_map (measurable_reflectedGridPath PF δ N).aemeasurable
        hq.aestronglyMeasurable

theorem integrable_sq_gridPathMaxCompensated_reverse
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (N : ℕ) :
    Integrable (fun ω => (gridPathMaxCompensated G m U δ
        (reflectedReverseGridPath PF δ N ω)) ^ 2) (reflectedSpeedLaw PF m) := by
  have hfwd : Integrable (fun ω => (gridPathMaxCompensated G m U δ
      (reflectedGridPath PF δ N ω)) ^ 2) (reflectedSpeedLaw PF m) :=
    (memLp_two_gridPathMaxCompensated_forward h hG hm hmsum U δ N).integrable_sq
  have hq : Measurable (fun p : Fin (N + 1) → Option V =>
      (gridPathMaxCompensated G m U δ p) ^ 2) := measurable_of_countable _
  have h1 : Integrable (fun p : Fin (N + 1) → Option V =>
      (gridPathMaxCompensated G m U δ p) ^ 2)
      ((reflectedSpeedLaw PF m).map (reflectedGridPath PF δ N)) :=
    (integrable_map_measure hq.aestronglyMeasurable
      (measurable_reflectedGridPath PF δ N).aemeasurable).2 hfwd
  rw [reflectedSpeedLaw_map_reflectedGridPath_reverse h hG hm hmsum δ N] at h1
  exact (integrable_map_measure hq.aestronglyMeasurable
    (measurable_reflectedReverseGridPath PF δ N).aemeasurable).1 h1

/- The forward compensated maximal functional is the producer's martingale
maximum, almost everywhere. -/
theorem integral_sq_gridPathMaxCompensated_forward_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (N : ℕ) :
    (∫ ω, (gridPathMaxCompensated G m U δ
        (reflectedGridPath PF δ N ω)) ^ 2 ∂reflectedSpeedLaw PF m) ≤
      32 * N * (δ : ℝ) * G.Energy (unweight m (valueInclusion G m U)) := by
  have hprod := stationaryGridMartingale_maximal_sq_integral_le
    h hG hm hmsum U δ C hbounded N
  refine le_trans (le_of_eq ?_) hprod
  have hall : ∀ᵐ ω ∂reflectedSpeedLaw PF m, ∀ k,
      stationaryGridMartingale PF G m U δ k ω =
        stationaryGridPotential PF G m U δ k ω -
          stationaryGridPotential PF G m U δ 0 ω -
          ∑ i ∈ Finset.range k, stationaryGridDrift PF G m U δ i ω :=
    ae_all_iff.2 fun k =>
      stationaryGridMartingale_ae_eq_compensated h hG hm hmsum U δ C hbounded k
  apply integral_congr_ae
  filter_upwards [hall] with ω hω
  have hfun : ∀ k ∈ Finset.range (N + 1),
      |gridPathCompensated G m U δ (reflectedGridPath PF δ N ω) k| =
        |stationaryGridMartingale PF G m U δ k ω| := by
    intro k hk
    rw [gridPathCompensated_forward PF G m U δ N ω
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), hω k]
  have hsup : gridPathMaxCompensated G m U δ (reflectedGridPath PF δ N ω) =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |stationaryGridMartingale PF G m U δ k ω|) :=
    Finset.sup'_congr Finset.nonempty_range_add_one rfl hfun
  rw [hsup]

theorem integral_driftSqSum_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (N : ℕ) :
    (∫ ω, ∑ j ∈ Finset.range (N + 1),
        (stationaryGridDrift PF G m U δ j ω) ^ 2
        ∂reflectedSpeedLaw PF m) ≤
      (N + 1) * (2 * ((δ : ℝ) *
        G.Energy (unweight m (valueInclusion G m U)))) := by
  have hone : ∀ j, (∫ ω, (stationaryGridDrift PF G m U δ j ω) ^ 2
      ∂reflectedSpeedLaw PF m) = ‖gridDriftVector G m U δ‖ ^ 2 := fun j =>
    integral_sq_unweight_reflectedSpeedLaw h hG hm hmsum
      (gridDriftVector G m U δ) (stationaryGridTime δ j)
  rw [integral_finset_sum (Finset.range (N + 1)) (fun j _ =>
    (memLp_two_stationaryGridDrift h hG hm hmsum U δ j).integrable_sq)]
  calc
    (∑ j ∈ Finset.range (N + 1), ∫ ω,
        (stationaryGridDrift PF G m U δ j ω) ^ 2 ∂reflectedSpeedLaw PF m) =
        ∑ _j ∈ Finset.range (N + 1), ‖gridDriftVector G m U δ‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ => hone j
    _ = ((N : ℝ) + 1) * ‖gridDriftVector G m U δ‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ ((N : ℝ) + 1) * (2 * ((δ : ℝ) *
        G.Energy (unweight m (valueInclusion G m U)))) := by
      apply mul_le_mul_of_nonneg_left
        (norm_gridDriftVector_sq_le G m hm U δ)
      positivity

/-! ### The stationary maximal potential bound -/

/-- Finite-grid maximal energy bound for the actual stationary potential of a
full-energy vector.  The constant is not optimized. -/
theorem stationaryGridPotential_maximal_sq_integral_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (N : ℕ) :
    (∫ ω, ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |stationaryGridPotential PF G m U δ k ω -
          stationaryGridPotential PF G m U δ 0 ω|)) ^ 2
        ∂reflectedSpeedLaw PF m) ≤
      1024 * ((N : ℝ) + 1) * (δ : ℝ) *
        G.Energy (unweight m (valueInclusion G m U)) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hafwd : Integrable (fun ω => (gridPathMaxCompensated G m U δ
      (reflectedGridPath PF δ N ω)) ^ 2) (reflectedSpeedLaw PF m) :=
    (memLp_two_gridPathMaxCompensated_forward h hG hm hmsum U δ N).integrable_sq
  have habwd : Integrable (fun ω => (gridPathMaxCompensated G m U δ
      (reflectedReverseGridPath PF δ N ω)) ^ 2) (reflectedSpeedLaw PF m) :=
    integrable_sq_gridPathMaxCompensated_reverse h hG hm hmsum U δ N
  have hS : Integrable (fun ω => ∑ j ∈ Finset.range (N + 1),
      (stationaryGridDrift PF G m U δ j ω) ^ 2) (reflectedSpeedLaw PF m) :=
    integrable_finset_sum (Finset.range (N + 1)) fun j _ =>
      (memLp_two_stationaryGridDrift h hG hm hmsum U δ j).integrable_sq
  have hpoint : ∀ ω,
      ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |stationaryGridPotential PF G m U δ k ω -
          stationaryGridPotential PF G m U δ 0 ω|)) ^ 2 ≤
      3 / 4 * (gridPathMaxCompensated G m U δ
          (reflectedGridPath PF δ N ω)) ^ 2 +
        3 * (gridPathMaxCompensated G m U δ
          (reflectedReverseGridPath PF δ N ω)) ^ 2 +
        3 * ∑ j ∈ Finset.range (N + 1),
          (stationaryGridDrift PF G m U δ j ω) ^ 2 := by
    intro ω
    have hA0 : 0 ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |stationaryGridPotential PF G m U δ k ω -
          stationaryGridPotential PF G m U δ 0 ω|) :=
      le_trans (abs_nonneg _)
        (Finset.le_sup' (fun k => |stationaryGridPotential PF G m U δ k ω -
          stationaryGridPotential PF G m U δ 0 ω|)
          (Finset.mem_range.mpr (Nat.succ_pos N)))
    have hdrift : (gridPathMaxDrift G m U δ (reflectedGridPath PF δ N ω)) ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1),
          (stationaryGridDrift PF G m U δ j ω) ^ 2 := by
      refine le_trans (gridPathMaxDrift_sq_le_sum G m U δ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro j hj
      rw [gridPathDrift_forward PF G m U δ N ω
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    exact sq_le_of_three_bound hA0
      (stationaryGridPotential_max_abs_le PF G m U δ N ω) hdrift
  have hfwd := integral_sq_gridPathMaxCompensated_forward_le
    h hG hm hmsum U δ C hbounded N
  have hrev : (∫ ω, (gridPathMaxCompensated G m U δ
      (reflectedReverseGridPath PF δ N ω)) ^ 2 ∂reflectedSpeedLaw PF m) ≤
      32 * N * (δ : ℝ) *
        G.Energy (unweight m (valueInclusion G m U)) := by
    rw [integral_sq_gridPathMaxCompensated_reverse_eq h hG hm hmsum U δ N]
    exact hfwd
  have hdrift := integral_driftSqSum_le h hG hm hmsum U δ N
  have hmain := integral_three_bound hafwd habwd hS
    (fun ω => sq_nonneg _) hpoint hfwd hrev hdrift
  have hdeficit : (0 : ℝ) ≤ (δ : ℝ) *
      G.Energy (unweight m (valueInclusion G m U)) := by
    have h0 := sq_nonneg ‖gridDriftVector G m U δ‖
    have hle := norm_gridDriftVector_sq_le G m hm U δ
    linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : (0 : ℝ) ≤ (N : ℝ) *
      ((δ : ℝ) * G.Energy (unweight m (valueInclusion G m U))) :=
    mul_nonneg hNnn hdeficit
  nlinarith [hmain, hdeficit, hprod]

end ReflectedGMS
