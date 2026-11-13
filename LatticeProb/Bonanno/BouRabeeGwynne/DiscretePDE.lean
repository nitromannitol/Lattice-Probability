/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.DiscretePDE at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Tactic.Ring
import LatticeProb.Bonanno.BouRabeeGwynne.LocalRegion
import LatticeProb.Bonanno.BouRabeeGwynne.FacetMeasure

open scoped BigOperators ENNReal

namespace BouRabeeGwynne

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The real-valued conductance in (1.1), extended by zero off the edge set. -/
noncomputable def conductanceReal (v w : T.V) : ℝ := by
  classical
  exact if T.adj v w then
    (T.facetVolume v w).toReal / ‖T.pos w - T.pos v‖
  else 0

lemma conductanceReal_of_adj {v w : T.V} (hvw : T.adj v w) :
    T.conductanceReal v w =
      (T.facetVolume v w).toReal / ‖T.pos w - T.pos v‖ := by
  simp [conductanceReal, hvw]

lemma pos_ne_of_adj {v w : T.V} (hvw : T.adj v w) : T.pos v ≠ T.pos w := by
  intro h
  exact hvw.1 (T.toTilingData.pos_injective h)

lemma edge_norm_pos {v w : T.V} (hvw : T.adj v w) :
    0 < ‖T.pos w - T.pos v‖ := by
  rw [norm_pos_iff]
  intro h
  have : T.pos w = T.pos v := sub_eq_zero.mp h
  exact (T.pos_ne_of_adj hvw) this.symm

lemma conductanceReal_nonneg (v w : T.V) : 0 ≤ T.conductanceReal v w := by
  by_cases h : T.adj v w
  · rw [T.conductanceReal_of_adj h]
    exact div_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · simp [conductanceReal, h]

/-- Actual contact geometry gives positive real conductance on every edge. -/
lemma conductanceReal_pos {v w : T.V} (hvw : T.adj v w) :
    0 < T.conductanceReal v w := by
  rw [T.conductanceReal_of_adj hvw]
  exact div_pos (T.toTilingData.facetVolume_toReal_pos hvw) (T.edge_norm_pos hvw)

@[simp] lemma conductanceReal_self (v : T.V) : T.conductanceReal v v = 0 := by
  simp [conductanceReal, T.toTilingData.adj_irrefl]

lemma conductanceReal_pos_iff {v w : T.V} :
    0 < T.conductanceReal v w ↔ T.adj v w := by
  constructor
  · intro h
    by_contra hvw
    simpa [conductanceReal, hvw] using h
  · exact T.conductanceReal_pos

lemma conductanceReal_symm (v w : T.V) :
    T.conductanceReal v w = T.conductanceReal w v := by
  by_cases h : T.adj v w
  · have h' := T.toTilingData.adj_symm h
    rw [T.conductanceReal_of_adj h, T.conductanceReal_of_adj h']
    have hvol : T.facetVolume v w = T.facetVolume w v :=
      T.toTilingData.facetVolume_symm v w
    rw [hvol, norm_sub_rev]
  · have h' : ¬ T.adj w v := by
      intro hwv
      exact h (T.toTilingData.adj_symm hwv)
    simp [conductanceReal, h, h']

/-- Equation (1.4), with the finite neighbor sum furnished by local finiteness. -/
noncomputable def discreteLaplacian (f : T.V → ℝ) (v : T.V)
    (hv : (T.neighbors v).Finite) : ℝ :=
  ∑ w ∈ T.neighborFinset v hv, T.conductanceReal v w * (f w - f v)

/-- The paper's weighted discrete gradient (2.2), extended by zero off edges. -/
noncomputable def weightedDiscreteGradient (f : T.V → ℝ) (w v : T.V) : ℝ :=
  T.conductanceReal w v * (f w - f v)

lemma weightedDiscreteGradient_antisymm (f : T.V → ℝ) (w v : T.V) :
    T.weightedDiscreteGradient f w v = - T.weightedDiscreteGradient f v w := by
  rw [weightedDiscreteGradient, weightedDiscreteGradient, T.conductanceReal_symm]
  ring

lemma discreteLaplacian_eq_sum_adj (f : T.V → ℝ) (v : T.V)
    (hv : (T.neighbors v).Finite) :
    T.discreteLaplacian f v hv =
      ∑ w ∈ T.neighborFinset v hv, T.weightedDiscreteGradient f w v := by
  simp only [discreteLaplacian, weightedDiscreteGradient]
  apply Finset.sum_congr rfl
  intro w hw
  rw [T.conductanceReal_symm]

/-- `Δ_a^G f = 0` on a set of vertices. -/
def DiscreteHarmonicOn (f : T.V → ℝ) (A : Set T.V) : Prop :=
  ∀ v ∈ A, ∃ hv : (T.neighbors v).Finite, T.discreteLaplacian f v hv = 0

/-- The finite Dirichlet problem with explicitly supplied graph-boundary data.
Theorem B(a) samples its neighborhood extension at vertex positions; B(b) samples
its continuous boundary trace at nearest points of the closed continuum domain. -/
def SolvesDirichlet (U : Set (Euc d)) (boundaryData hD : T.V → ℝ) : Prop :=
  T.DiscreteHarmonicOn hD (T.interiorVertices U) ∧
    ∀ v ∈ T.boundaryVertices U, hD v = boundaryData v

/-- Uniform error appearing in (1.5), phrased directly without an error-sequence proxy. -/
def DirichletError (U : Set (Euc d)) (hC : Euc d → ℝ) (hD : T.V → ℝ)
    (η : ℝ) : Prop :=
  ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤ η

/-- Equation (1.5) for a sequence of actual discrete solutions. -/
def DirichletConverges {d : ℕ} (G : TilingSequence d) (U : Set (Euc d))
    (hC : Euc d → ℝ) (hD : ∀ n, (G.tiling n).V → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N, ∀ n, N ≤ n →
    (G.tiling n).DirichletError U hC (hD n) η

end OrthogonalTiling

end BouRabeeGwynne
