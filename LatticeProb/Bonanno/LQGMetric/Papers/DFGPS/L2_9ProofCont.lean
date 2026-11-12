/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofCont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofGeom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9, first conjunct: continuity of `D_h^ε(·,·;W̄)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) Lemma 2.9 (T:903–906) speaks of laws
on `C(W̄ × W̄, ℝ)`, i.e. the internal metrics `𝔞_ε⁻¹ D_h^ε(·,·;W̄)` are (a.s.) continuous on
`W̄ × W̄`. For connected `W̄` (a finite union of closed squares) and continuous `h*_ε`:
finiteness by connectedness (the set of points at finite distance from `x` is clopen) and the
local bound `exists_lfppDOn_union_le` (T:914–925) give a local Lipschitz bound, hence continuity
(own elementary argument, as `continuous_lfppDOn_toReal` for squares; DEVIATIONS).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

theorem dyadic_squares_closedSq {𝒮 : Finset (Set ℂ)} (h𝒮 : ∀ S ∈ 𝒮, IsDyadicSquare S) :
    ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s := fun S hS => by
  obtain ⟨k, j, rfl⟩ := h𝒮 S hS
  exact ⟨_, _, zpow_pos two_pos k, dfDyadicSq_eq_closedSq k j⟩

/-- **finiteness** of `D_φ(·,·;K)` on a connected finite union `K` of closed squares -/
theorem lfppDOn_union_ne_top {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) (hK : IsPreconnected (⋃ S ∈ 𝒮, S)) :
    ∀ x ∈ ⋃ S ∈ 𝒮, S, ∀ y ∈ ⋃ S ∈ 𝒮, S, lfppDOn ξ φ (⋃ S ∈ 𝒮, S) x y ≠ ⊤ := by
  set K := ⋃ S ∈ 𝒮, S
  obtain ⟨δ, hδ, B, hB0, hB⟩ := exists_lfppDOn_union_le (ξ := ξ) hφ 𝒮 h𝒮
  have hloc : ∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ < δ → lfppDOn ξ φ K y z ≠ ⊤ := fun y hy z hz h =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB y hy z hz h)
  intro x hx
  haveI := isPreconnected_iff_preconnectedSpace.1 hK
  set A : Set K := {y | lfppDOn ξ φ K x y ≠ ⊤}
  have hAo : IsOpen A := by
    refine Metric.isOpen_iff.2 fun y hy => ⟨δ, hδ, fun z hz => ?_⟩
    rw [mem_ball, Subtype.dist_eq, dist_eq_norm] at hz
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy, hloc y y.2 z z.2 hz⟩)
      (lfppDOn_triangle x y z)
  have hAc : IsClosed A := by
    refine isOpen_compl_iff.1 (Metric.isOpen_iff.2 fun y hy => ⟨δ, hδ, fun z hz hzA => hy ?_⟩)
    rw [mem_ball, Subtype.dist_eq, dist_eq_norm] at hz
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hzA, hloc z z.2 y y.2
      (by rw [norm_sub_rev]; exact hz)⟩) (lfppDOn_triangle x z y)
  have hxA : (⟨x, hx⟩ : K) ∈ A := hloc x hx x hx (by simpa using hδ)
  have hU := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨_, hxA⟩
  intro y hy
  have : (⟨y, hy⟩ : K) ∈ A := hU ▸ mem_univ _
  exact this

/-- **continuity** of `(x, y) ↦ c · D_φ(x, y; K)` on `K × K`, `K` a connected finite union of
closed squares -/
theorem continuous_lfppDOn_union_toReal {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    (𝒮 : Finset (Set ℂ)) (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s)
    (hK : IsPreconnected (⋃ S ∈ 𝒮, S)) (c : ℝ) :
    Continuous fun p : (⋃ S ∈ 𝒮, S) × (⋃ S ∈ 𝒮, S) =>
      c * (lfppDOn ξ φ (⋃ S ∈ 𝒮, S) p.1 p.2).toReal := by
  set K := ⋃ S ∈ 𝒮, S
  obtain ⟨δ, hδ, B, hB0, hB⟩ := exists_lfppDOn_union_le (ξ := ξ) hφ 𝒮 h𝒮
  have hfin := lfppDOn_union_ne_top (ξ := ξ) hφ 𝒮 h𝒮 hK
  set D : K → K → ℝ := fun x y => (lfppDOn ξ φ K x y).toReal
  have htri : ∀ x y z : K, D x z ≤ D x y + D y z := fun x y z => by
    simp only [D]
    rw [← ENNReal.toReal_add (hfin x x.2 y y.2) (hfin y y.2 z z.2)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x x.2 y y.2, hfin y y.2 z z.2⟩)
      (lfppDOn_triangle _ _ _)
  have hcomm : ∀ x y : K, D x y = D y x := fun x y => by simp only [D, lfppDOn_comm]
  have hle : ∀ x y : K, dist x y < δ → D x y ≤ 2 * B * dist x y := fun x y h => by
    rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at h ⊢
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hB x x.2 y y.2 h)
  have hlip : ∀ p q : K × K, dist p q < δ → |D p.1 p.2 - D q.1 q.2| ≤ 4 * B * dist p q := by
    intro p q h
    have d1 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
    have d2 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    have e1 := hle p.1 q.1 (d1.trans_lt h)
    have e2 := hle p.2 q.2 (d2.trans_lt h)
    have f1 : 2 * B * dist p.1 q.1 ≤ 2 * B * dist p q := mul_le_mul_of_nonneg_left d1 (by positivity)
    have f2 : 2 * B * dist p.2 q.2 ≤ 2 * B * dist p q := mul_le_mul_of_nonneg_left d2 (by positivity)
    have t1 := htri p.1 q.1 p.2
    have t2 := htri q.1 q.2 p.2
    have t3 := htri q.1 p.1 q.2
    have t4 := htri p.1 p.2 q.2
    have c1 := hcomm q.1 p.1
    have c2 := hcomm q.2 p.2
    rw [abs_le]
    constructor <;> linarith
  refine continuous_const.mul (Metric.continuous_iff.2 fun q e he => ?_)
  refine ⟨min δ (e / (4 * B + 1)), lt_min hδ (by positivity), fun p hp => ?_⟩
  rw [Real.dist_eq]
  have h1 := hlip p q (lt_of_lt_of_le hp (min_le_left _ _))
  have h2 : dist p q < e / (4 * B + 1) := lt_of_lt_of_le hp (min_le_right _ _)
  have h3 : (4 * B + 1) * dist p q < e := by
    rw [lt_div_iff₀ (by positivity)] at h2; linarith
  nlinarith [dist_nonneg (x := p) (y := q)]

/-- **DFGPS Lemma 2.9, first conjunct** (T:903–906): for each `ε ∈ (0,1)`, a.s. the rescaled
internal LFPP metric is continuous on `W̄ × W̄` (`W̄` connected). -/
theorem lem2_9_continuous {γ : ℝ} {W : Set ℂ} (hW : IsDyadicDomain W)
    (hWc : IsConnected (closure W)) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous fun p : closure W × closure W =>
      (aEpsDF (xiGamma γ) ε)⁻¹ *
        (LFPP.lfppDOn (xiGamma γ) (heatMollify ε (h ω)) (closure W) p.1 p.2).toReal := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := hW
  rw [closure_dyadicDomain_eq h𝒮] at hWc ⊢
  intro ε hε
  filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'] with ω hω
  exact continuous_lfppDOn_union_toReal hω.2 𝒮 (dyadic_squares_closedSq h𝒮) hWc.isPreconnected _

end LQGMetric.DFGPS
