import LatticeProb.Graph.LongRangeKernel.WeightedGraph
import LatticeProb.Graph.LongRangeKernel.Scale
import LatticeProb.Graph.Zd
import LatticeProb.Walk.SRWDiag

/-!
# Lattice reference walk normalization

Nearest-neighbour weights `1/(2d)` give vertex mass one and reference transition
probability `1/(2d)`. The graph is the library's actual nearest-neighbour lattice.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The polynomial comparison profile at all radii, including the value one at zero. -/
def latticeVolumeProfile (d : ℕ) (r : ℝ) : ℝ := (1 + r) ^ d

/-- Positive-dimensional polynomial growth gives a genuine continuous doubling profile. -/
theorem latticeVolumeProfile_isVolumeProfile (hd : 0 < d) :
    IsVolumeProfile (latticeVolumeProfile d) := by
  refine ⟨?_, ?_, ?_, 2 ^ d + 1, ?_, ?_⟩
  · unfold latticeVolumeProfile
    fun_prop
  · intro a ha b _ hab
    exact pow_lt_pow_left₀ (by linarith : 1 + a < 1 + b)
      (by have ha0 : 0 ≤ a := ha; linarith) (Nat.ne_of_gt hd)
  · intro r hr
    exact pow_pos (by linarith) d
  · have htwo : (0 : ℝ) < 2 ^ d := by positivity
    linarith
  · intro r hr
    change (1 + 2 * r) ^ d ≤ (2 ^ d + 1) * (1 + r) ^ d
    calc
      (1 + 2 * r) ^ d ≤ (2 * (1 + r)) ^ d :=
        pow_le_pow_left₀ (by linarith) (by linarith) d
      _ = 2 ^ d * (1 + r) ^ d := mul_pow _ _ _
      _ ≤ (2 ^ d + 1) * (1 + r) ^ d := by
        have hp : 0 ≤ (1 + r) ^ d := by positivity
        nlinarith

/-- Constant nearest-neighbour weights, with no loops or extra edges. -/
def latticeWeight (d : ℕ) (x y : Site d) : ℝ≥0 :=
  by
    classical
    exact if (lattice d).Adj x y then (2 * (d : ℝ≥0))⁻¹ else 0

/-- The weighted nearest-neighbour lattice, for positive dimension. -/
def weightedLattice (d : ℕ) (hd : 0 < d) : WeightedGraph (Site d) where
  graph := lattice d
  locallyFinite := LatticeProb.Graph.Zd.latticeLocallyFinite d
  weight := latticeWeight d
  symmetric := by
    classical
    intro x y
    simp only [latticeWeight, (lattice d).adj_comm]
  positive_iff := by
    classical
    intro x y
    have hpos : 0 < (2 * (d : ℝ≥0))⁻¹ := by positivity
    simp only [latticeWeight]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => hpos⟩
    · exact ⟨fun hzero => (lt_irrefl 0 hzero).elim, fun htrue => (h htrue).elim⟩

/-- The induced vertex mass is exactly one, rather than `2d`. -/
theorem weightedLattice_mass (hd : 0 < d) (x : Site d) :
    (weightedLattice d hd).mass x = 1 := by
  classical
  have hne : 2 * (d : ℝ≥0) ≠ 0 := by positivity
  change (∑ y ∈ (lattice d).neighborFinset x, latticeWeight d x y) = 1
  have hsum : (∑ y ∈ (lattice d).neighborFinset x, latticeWeight d x y) =
      ∑ _y ∈ (lattice d).neighborFinset x, (2 * (d : ℝ≥0))⁻¹ := by
    apply Finset.sum_congr rfl
    intro y hy
    exact if_pos (((lattice d).mem_neighborFinset x y).mp hy)
  rw [hsum, Finset.sum_const, ← SimpleGraph.degree, LatticeProb.Graph.Zd.degree_eq,
    nsmul_eq_mul]
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_inv_cancel₀ hne]

/-- The counting-measure comparison holds with the exact constant one. -/
theorem weightedLattice_counting (hd : 0 < d) :
    ∃ C_μ : ℝ, 1 ≤ C_μ ∧ ∀ x,
      C_μ⁻¹ ≤ ((weightedLattice d hd).mass x : ℝ) ∧
        ((weightedLattice d hd).mass x : ℝ) ≤ C_μ := by
  refine ⟨1, le_rfl, fun x => ?_⟩
  rw [weightedLattice_mass hd x]
  norm_num

/-- The reference density is the constant edge probability, since vertex masses equal one. -/
theorem weightedLattice_referenceDensity (hd : 0 < d) (x y : Site d) :
    (weightedLattice d hd).referenceDensity x y =
      if (lattice d).Adj x y then (2 * (d : ℝ≥0∞))⁻¹ else 0 := by
  rw [WeightedGraph.referenceDensity, weightedLattice_mass, weightedLattice_mass]
  simp only [ENNReal.coe_one, mul_one, div_one]
  change ((latticeWeight d x y : ℝ≥0) : ℝ≥0∞) = _
  unfold latticeWeight
  split_ifs
  · rw [ENNReal.coe_inv (by positivity), ENNReal.coe_mul, ENNReal.coe_ofNat,
      ENNReal.coe_natCast]
  · rfl

/-- The normalized nearest-neighbour density has total mass one at every actual site. -/
theorem weightedLattice_isMarkovDensity (hd : 0 < d) :
    IsMarkovDensity (weightedLattice d hd).mass
      (weightedLattice d hd).referenceDensity := by
  classical
  intro x
  simp_rw [weightedLattice_referenceDensity, weightedLattice_mass,
    ENNReal.coe_one, mul_one]
  rw [tsum_eq_sum (s := (lattice d).neighborFinset x)]
  · have heq : (∑ y ∈ (lattice d).neighborFinset x,
        if (lattice d).Adj x y then (2 * (d : ℝ≥0∞))⁻¹ else 0) =
        ∑ _y ∈ (lattice d).neighborFinset x, (2 * (d : ℝ≥0∞))⁻¹ := by
      apply Finset.sum_congr rfl
      intro y hy
      exact if_pos (((lattice d).mem_neighborFinset x y).mp hy)
    rw [heq, Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree,
      LatticeProb.Graph.Zd.degree_eq]
    push_cast
    exact ENNReal.mul_inv_cancel (by positivity)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top d))
  · intro y hy
    exact if_neg (fun hxy => hy (((lattice d).mem_neighborFinset x y).mpr hxy))

/-- The edge-transition lower bound is exactly `p₀ = 1/(2d)`. -/
theorem weightedLattice_edge_lower (hd : 0 < d) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ x y, (weightedLattice d hd).graph.Adj x y →
      p₀ ≤ ((weightedLattice d hd).weight x y : ℝ) /
        ((weightedLattice d hd).mass x : ℝ) := by
  refine ⟨(2 * (d : ℝ))⁻¹, by positivity, ?_⟩
  intro x y hxy
  change (lattice d).Adj x y at hxy
  rw [weightedLattice_mass]
  change (2 * (d : ℝ))⁻¹ ≤ (latticeWeight d x y : ℝ) / 1
  rw [latticeWeight, if_pos hxy]
  simp only [NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, div_one]
  exact le_rfl

/-- The reference lattice is connected for every positive dimension. -/
theorem weightedLattice_connected (hd : 0 < d) :
    (weightedLattice d hd).graph.Connected := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  exact LatticeProb.Graph.Zd.latticeConnected d

/-- The site carrier is infinite for every positive dimension. -/
theorem weightedLattice_infinite (hd : 0 < d) : Infinite (Site d) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  exact LatticeProb.Graph.Zd.latticeInfinite d

/-- Below graph radius one, the closed ball has exactly mass one, including radius zero. -/
theorem weightedLattice_volume_small (hd : 0 < d) (x : Site d) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) : (weightedLattice d hd).volume x r = 1 := by
  classical
  have hconn := weightedLattice_connected hd
  have hball : ∀ y, y ∈ (weightedLattice d hd).ball x r ↔ y = x := by
    intro y
    constructor
    · intro hy
      have hyR : ((weightedLattice d hd).graph.dist x y : ℝ) < 1 := lt_of_le_of_lt hy hr1
      have hyN : (weightedLattice d hd).graph.dist x y < 1 := by exact_mod_cast hyR
      exact ((hconn.dist_eq_zero_iff).mp (by omega)).symm
    · intro hy
      subst y
      change ((weightedLattice d hd).graph.dist x x : ℝ) ≤ r
      simpa only [SimpleGraph.dist_self, Nat.cast_zero] using hr
  unfold WeightedGraph.volume
  simp_rw [hball, weightedLattice_mass, ENNReal.coe_one]
  exact tsum_ite_eq x (fun _ => (1 : ℝ≥0∞))

/-- At zero time the density at every site is one, providing a nonzero actual object. -/
theorem weightedLattice_heat_zero_self (hd : 0 < d) (x : Site d) :
    (weightedLattice d hd).heat 0 x x = 1 := by
  rw [WeightedGraph.heat, densityPower_zero_self, weightedLattice_mass]
  simp only [ENNReal.coe_one, inv_one]

/-- The lattice Gaussian upper bound has a denominator linear in time uniformly for `n≥1`. -/
theorem srwHeat_gaussian_linear_time (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n)
    (x : Site d) :
    srwHeat d n x ≤ 3 ^ d * greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2) *
      Real.exp (-((graphNorm x : ℝ) ^ 2) / (8 * (1 + 2 * d) * n)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hden : 8 * ((n : ℝ) + 2 * d) ≤ 8 * (1 + 2 * d) * n := by
    nlinarith
  have hexp : -((graphNorm x : ℝ) ^ 2) / (8 * ((n : ℝ) + 2 * d)) ≤
      -((graphNorm x : ℝ) ^ 2) / (8 * (1 + 2 * d) * n) := by
    simpa only [neg_div] using
      neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg (graphNorm x : ℝ))
        (by positivity) hden)
  have hg : 0 ≤ greenConst d := greenConst_nonneg d
  apply (srwHeat_gaussian hd hn x).trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

end

end LatticeProb.Graph.LongRangeKernel
