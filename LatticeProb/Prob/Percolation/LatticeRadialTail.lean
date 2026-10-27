import LatticeProb.Prob.Percolation.LatticeClusterBall
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Radial tail bounds for lattice fields

A pointwise tail estimate can be summed over the ambient lattice without any
independence assumption.
-/

open MeasureTheory Filter Asymptotics
open scoped ENNReal

namespace LatticeProb.Percolation

noncomputable section

/-- Euclidean lattice distances are invariant under translation. -/
theorem latticeEuclideanEmbedding_sub {d : ℕ} (x y : Vertex d) :
    latticeEuclideanEmbedding (x - y) =
      latticeEuclideanEmbedding x - latticeEuclideanEmbedding y := by
  ext i
  change ((x i - y i : ℤ) : ℝ) = (x i : ℝ) - (y i : ℝ)
  exact Int.cast_sub _ _

/-- Some negative power of the actual Euclidean lattice norm is summable. -/
theorem summable_latticeEuclideanEmbedding_rpow (d : ℕ) : ∃ r : ℝ, r < 0 ∧
    Summable (fun x : Vertex d => ‖latticeEuclideanEmbedding x‖ ^ r) := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let L := Submodule.span ℤ (Set.range b)
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r]; linarith
  have hp : ∀ x : Vertex d, latticeEuclideanEmbedding x ∈ L := by
    intro x
    apply (b.mem_span_iff_repr_mem ℤ _).2
    intro i
    exact ⟨x i, rfl⟩
  let f : Vertex d → L := fun x => ⟨latticeEuclideanEmbedding x, hp x⟩
  have hf : Function.Injective f := by
    intro x y h
    apply latticeEuclideanEmbedding.injective
    exact congrArg Subtype.val h
  have hr0 : r < 0 := hr.trans_le (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hs : Summable (fun z : L => ‖z‖ ^ r) := ZLattice.summable_norm_rpow L r hr
  have hs' := hs.comp_injective hf
  exact ⟨r, hr0, hs'⟩

private theorem exp_rpow_littleO {p c r : ℝ} (hp : 0 < p) (hc : 0 < c) :
    (fun t : ℝ => Real.exp (-c * t ^ p)) =o[atTop] (fun t : ℝ => t ^ r) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (r / p)).comp_tendsto
    (tendsto_rpow_atTop hp)
  refine h.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change (t ^ p) ^ (r / p) = t ^ r
  rw [← Real.rpow_mul ht]
  congr 1
  field_simp

private theorem lattice_norm_tendsto (d : ℕ) :
    Tendsto (fun x : Vertex d => ‖latticeEuclideanEmbedding x‖) cofinite atTop := by
  apply tendsto_atTop.2
  intro b
  apply eventually_cofinite.2
  have hf := finite_latticeEuclideanBall (0 : Vertex d) (b + 1)
  apply hf.subset
  intro x hx
  have h : ‖latticeEuclideanEmbedding x‖ < b + 1 := by
    change ¬ b ≤ ‖latticeEuclideanEmbedding x‖ at hx
    exact (not_le.mp hx).trans (lt_add_one b)
  have hz : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  change dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding 0) < b + 1
  simpa only [dist_eq_norm, hz, sub_zero] using h

/-- Every positive stretched-exponential kernel is summable on the Euclidean lattice. -/
theorem summable_exp_latticeEuclideanEmbedding (d : ℕ) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    Summable (fun x : Vertex d => Real.exp (-c * ‖latticeEuclideanEmbedding x‖ ^ p)) := by
  obtain ⟨r, _, hs⟩ := summable_latticeEuclideanEmbedding_rpow d
  have ho := (exp_rpow_littleO hp hc (r := r)).isBigO.comp_tendsto (lattice_norm_tendsto d)
  exact summable_of_isBigO hs ho

private theorem radial_kernel_split {d : ℕ} (y : Vertex d) {R p c : ℝ}
    (hR : 0 ≤ R) (hp : 0 ≤ p) (hc : 0 ≤ c) :
    (∑' x : {x : Vertex d // R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖},
      ENNReal.ofReal (Real.exp (-(2 * c) * ‖latticeEuclideanEmbedding x.val -
        latticeEuclideanEmbedding y‖ ^ p))) ≤
    ENNReal.ofReal (Real.exp (-c * R ^ p)) *
      ∑' x : Vertex d,
        ENNReal.ofReal (Real.exp (-c * ‖latticeEuclideanEmbedding x‖ ^ p)) := by
  let I := {x : Vertex d // R ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖}
  let g : Vertex d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-c * ‖latticeEuclideanEmbedding x‖ ^ p))
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-c * R ^ p))
  have hpoint (x : I) :
      ENNReal.ofReal (Real.exp (-(2 * c) * ‖latticeEuclideanEmbedding x.val -
        latticeEuclideanEmbedding y‖ ^ p)) ≤ a * g (x.val - y) := by
    have hp' : R ^ p ≤ ‖latticeEuclideanEmbedding x.val -
        latticeEuclideanEmbedding y‖ ^ p := Real.rpow_le_rpow hR x.property hp
    have hm := mul_nonneg hc (sub_nonneg.mpr hp')
    have he : -(2 * c) * ‖latticeEuclideanEmbedding x.val -
        latticeEuclideanEmbedding y‖ ^ p ≤ -c * R ^ p +
        -c * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ p := by
      nlinarith
    dsimp [a, g]
    rw [latticeEuclideanEmbedding_sub, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)
  calc
    _ ≤ ∑' x : I, a * g (x.val - y) := ENNReal.tsum_le_tsum hpoint
    _ = a * ∑' x : I, g (x.val - y) := ENNReal.tsum_mul_left
    _ ≤ a * ∑' x : Vertex d, g x := by
      gcongr
      apply ENNReal.tsum_comp_le_tsum_of_injective
      intro x z h
      apply Subtype.ext
      exact (Equiv.subRight y).injective h

/-- The radial bad-point event is bounded by the sum of the individual tail bounds. -/
theorem measure_radial_bad_le_tsum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Vertex d → Ω → ℝ) (A s α : ℝ)
    (h : ∀ x t, 0 < t → μ {ω | t ≤ X x ω} ≤
      ENNReal.ofReal (A * Real.exp (-(t ^ s) / A)))
    (y : Vertex d) (R : ℝ) (hR : 0 < R) :
    μ {ω | ∃ x : Vertex d, R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} ≤
    ∑' x : {x : Vertex d // R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖},
      ENNReal.ofReal (A * Real.exp
        (-(‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ α) ^ s / A)) := by
  let I := {x : Vertex d // R ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖}
  let f : I → Set Ω := fun x => {ω | ‖latticeEuclideanEmbedding x.val -
    latticeEuclideanEmbedding y‖ ^ α ≤ X x.val ω}
  have heq : {ω | ∃ x : Vertex d, R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} =
      ⋃ x : I, f x := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hX⟩
      exact ⟨⟨x, hx⟩, hX⟩
    · rintro ⟨x, hx⟩
      exact ⟨x.val, x.property, hx⟩
  rw [heq]
  calc
    μ (⋃ x : I, f x) ≤ ∑' x : I, μ (f x) := measure_iUnion_le f
    _ ≤ _ := ENNReal.tsum_le_tsum fun x =>
      h x.val _ (Real.rpow_pos_of_pos (lt_of_lt_of_le hR x.property) _)

/-- A uniform pointwise stretched-exponential tail controls the radial bad-point event. -/
theorem measure_radial_bad_stretched_exp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A s α : ℝ) (hA : 0 < A) (hs : 0 < s) (hα : 0 < α) :
    ∃ B : ℝ, 0 < B ∧ ∀ (μ : Measure Ω) (X : Vertex d → Ω → ℝ),
      (∀ x t, 0 < t → μ {ω | t ≤ X x ω} ≤
        ENNReal.ofReal (A * Real.exp (-(t ^ s) / A))) →
      ∀ (y : Vertex d) (R : ℝ), 1 ≤ R →
        μ {ω | ∃ x : Vertex d, R ≤ ‖latticeEuclideanEmbedding x -
          latticeEuclideanEmbedding y‖ ∧
          ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} ≤
        ENNReal.ofReal (B * Real.exp (-(R ^ (α * s)) / B)) := by
  let p := α * s
  let c := 1 / (2 * A)
  let k : Vertex d → ℝ := fun x => Real.exp (-c * ‖latticeEuclideanEmbedding x‖ ^ p)
  let K := ∑' x, k x
  let B := max (2 * A) (A * K + 1)
  have hp : 0 < p := mul_pos hα hs
  have hc : 0 < c := by dsimp [c]; positivity
  have hk : Summable k := summable_exp_latticeEuclideanEmbedding d hp hc
  have hB : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2 * A) (le_max_left _ _)
  have hBA : 2 * A ≤ B := le_max_left _ _
  have hBK : A * K ≤ B := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro μ X h y R hR
  let I := {x : Vertex d // R ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖}
  have ht (x : I) :
      ENNReal.ofReal (A * Real.exp
        (-(‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ α) ^ s / A)) =
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp (-(2 * c) *
        ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ p)) := by
    rw [← ENNReal.ofReal_mul hA.le]
    congr 2
    rw [← Real.rpow_mul (norm_nonneg _)]
    dsimp [p, c]
    congr 1
    field_simp
  have hsum := radial_kernel_split y (p := p) (c := c) (R := R)
    (le_trans (by norm_num) hR) hp.le hc.le
  have htot : μ {ω | ∃ x : Vertex d, R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} ≤
      ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (-c * R ^ p)) * ENNReal.ofReal K) := by
    calc
      _ ≤ ∑' x : I, ENNReal.ofReal (A * Real.exp
          (-(‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ α) ^ s / A)) :=
        measure_radial_bad_le_tsum μ X A s α h y R (lt_of_lt_of_le zero_lt_one hR)
      _ = ENNReal.ofReal A * ∑' x : I, ENNReal.ofReal (Real.exp (-(2 * c) *
          ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ p)) := by
        simp_rw [ht, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (-c * R ^ p)) *
          ∑' x : Vertex d, ENNReal.ofReal (k x)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hk]
  have hpow : 0 ≤ R ^ p := Real.rpow_nonneg (le_trans (by norm_num) hR) _
  have hdiv : R ^ p / B ≤ R ^ p / (2 * A) :=
    div_le_div_of_nonneg_left hpow (by positivity) hBA
  have he : Real.exp (-c * R ^ p) ≤ Real.exp (-(R ^ p) / B) := by
    apply Real.exp_le_exp.mpr
    dsimp [c]
    rw [one_div, neg_mul, mul_comm, ← div_eq_mul_inv, neg_div]
    exact neg_le_neg hdiv
  have hreal : A * (Real.exp (-c * R ^ p) * K) ≤ B * Real.exp (-(R ^ p) / B) := by
    calc
      _ = (A * K) * Real.exp (-c * R ^ p) := by ring
      _ ≤ B * Real.exp (-(R ^ p) / B) :=
        mul_le_mul hBK he (Real.exp_pos _).le hB.le
  apply htot.trans
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hA.le]
  exact ENNReal.ofReal_le_ofReal hreal

end
end LatticeProb.Percolation
