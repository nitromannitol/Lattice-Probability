/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.WindowModulusGridTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WindowModulusUniformScales
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Measure.Tight
import LatticeProb.Bonanno.ReflectedGMS.Limit.SquareMartingaleMaximal
import LatticeProb.Bonanno.ReflectedGMS.Limit.UniformGridOscillation

/-!
# The window modulus of a continuous interpolation from a localized martingale array

`ReflectedGMS.WindowModulusUniformScales.rescaledWindowModulusTail_Ioc_of_sequential` reduces
the consumer input `RescaledWindowModulusTail μ (Set.Ioc 0 1)` to a *sequential* statement:
along every positive null sequence of scales `ε n`, the unrescaled law `μ` has, for all large
`n`, a small probability of oscillating by more than `c / ε n` across a lag `< ε n⁻² d` inside
the window `[0, ε n⁻² m]`.  The checked martingale-array estimate
`MartingaleLimit.uniform_grid_oscillation_probability_le` instead controls **scalar grid-lag
oscillations of a martingale array on a deterministic mesh**.  This file welds the two, with no
reference to the reflected walk.

The pathwise comparison (`preimage_windowModulusFailure_subset`) is: a continuous path `f`
(the interpolation) oscillating by more than `a` at lag `< Δ` in `[0, b]` forces one of

* `f` far from a comparison path `g` (the harmonic martingale) at some time before a horizon;
* `f` oscillating by more than `κ₂` inside **one mesh cell** of size `δ`;
* `g` oscillating by more than `a - 2κ₁ - 2κ₂` over a **grid lag** `≤ L`,

where `L δ ≥ Δ + δ`.  The grid event of the plane-valued `g` splits into the two coordinate
events at half the threshold (`gridLag_subset_coordinates`), and each coordinate event is, up to
a disagreement event, the grid-lag event of a scalar array (`coordEvent_subset_disagree_union_core`).

The probabilistic assembly (`eventually_window_tail_of_localized_arrays`) chooses **one
deterministic mesh per row** from the single-law window modulus of the continuous interpolation
itself (`exists_mesh_for_row`).  The same choice makes the maximal grid jump of each localized
coordinate array vanish in probability, *derived* from the closeness hypothesis
(`tendsto_gridJump_of_close_mesh`), so that premise of the core estimate is not an input.

## Inputs, named

* `hclose` — the interpolation `I` and the comparison process `G` are uniformly close after
  diffusive scaling, in probability, on every horizon.  At the reflected walk this is the
  corrector/interpolation transfer of manuscript `tex:1648-1652`
  (`Limit/CorrectorInterpolationTransfer`) on the compact containment event.
* `harray` — `LocalizedMartingaleArray`: for each coordinate and horizon, a scalar martingale
  array with a compensator making `Y² - B` a martingale, uniform terminal second moments, an
  integrable bracket-error envelope with vanishing mean, and agreeing with the rescaled
  coordinate of `G` on `[0, H]` with probability tending to one.  These are exactly the outputs
  of the threshold-stopped lane (`ThresholdStoppedMartingaleMoments`, `StoppedCadlagPaths`,
  `UCPBracketLocalization`, `LocalizedBracketEnvelope`).  The array may live on another
  measurable structure `Q` with the same outer measure as `P` (e.g. the completion).

**This file certifies no tightness estimate for the reflected walk**; it is an implication.
-/

-- Merged from `ReflectedGMS/Limit/MartingaleInterpolationTightness.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MartingaleInterpolationTightness

/-!
# Tightness of interpolated martingale-array laws

This file composes the checked uniform grid-oscillation estimate with the
checked continuous-interpolation tightness criterion.  It proves tightness of
the actual pushforward laws, without identifying their subsequential limits.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

/-- If a positive mesh is at most one eighth of a physical window, an integer
lag can be chosen whose duration absorbs the interpolation slack while staying
inside that window. -/
theorem exists_nat_lag_for_interpolation
    {D d : ℝ≥0} (hD : 0 < D) (hd : 0 < d) (hsmall : d ≤ D / 8) :
    ∃ L : ℕ, D / 4 + 2 * d ≤ (L : ℝ≥0) * d ∧ (L : ℝ≥0) * d ≤ D := by
  let L : ℕ := Nat.ceil (D / (2 * d))
  refine ⟨L, ?_, ?_⟩
  · have hceil : D / (2 * d) ≤ (L : ℝ≥0) := by
      exact Nat.le_ceil _
    have hbase : D ≤ (L : ℝ≥0) * (2 * d) :=
      (div_le_iff₀ (by positivity : 0 < (2 : ℝ≥0) * d)).mp hceil
    have hhalf : D / 2 ≤ (L : ℝ≥0) * d := by
      apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ≥0))).mpr
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
    calc
      D / 4 + 2 * d ≤ D / 4 + 2 * (D / 8) := by gcongr
      _ = D / 2 := by ring
      _ ≤ (L : ℝ≥0) * d := hhalf
  · have hceil : (L : ℝ≥0) < D / (2 * d) + 1 := by
      exact Nat.ceil_lt_add_one (by positivity)
    have hupper : (L : ℝ≥0) * d ≤ D / 2 + d := by
      calc
        (L : ℝ≥0) * d ≤ (D / (2 * d) + 1) * d :=
          mul_le_mul_of_nonneg_right hceil.le d.2
        _ = D / 2 + d := by
          rw [add_mul, one_mul]
          field_simp
    calc
      (L : ℝ≥0) * d ≤ D / 2 + d := hupper
      _ ≤ D / 2 + D / 8 := by gcongr
      _ = (5 / 8 : ℝ≥0) * D := by ring
      _ ≤ 1 * D := mul_le_mul_of_nonneg_right (by
        apply (div_le_iff₀ (by norm_num : 0 < (8 : ℝ≥0))).mpr
        norm_num) D.2
      _ = D := one_mul D

variable {Ω : Type*} {m : MeasurableSpace Ω}

end ReflectedGMS.MartingaleLimit

end Merged_MartingaleInterpolationTightness

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.WindowModulusGridTransfer

open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.DiffusiveModulusTranslation
open ReflectedGMS.WindowModulusUniformScales

/-! ## Coordinates of the plane -/

/-- The Euclidean norm on the plane is at most the sum of the two absolute coordinates. -/
theorem norm_le_abs_zero_add_abs_one (x : BouRabeeGwynne.Euc 2) :
    ‖x‖ ≤ |x 0| + |x 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

/-- A plane distance above `a` forces one coordinate difference above `a / 2`. -/
theorem half_lt_abs_sub_zero_or_one {x y : BouRabeeGwynne.Euc 2} {a : ℝ}
    (h : a < dist x y) : a / 2 < |x 0 - y 0| ∨ a / 2 < |x 1 - y 1| := by
  by_contra hcon
  obtain ⟨h0, h1⟩ := not_or.mp hcon
  have hle := norm_le_abs_zero_add_abs_one (x - y)
  simp only [PiLp.sub_apply] at hle
  rw [← dist_eq_norm] at hle
  linarith [not_lt.mp h0, not_lt.mp h1]

/-- Each coordinate difference is at most the plane distance. -/
theorem abs_sub_apply_le_dist (x y : BouRabeeGwynne.Euc 2) (k : Fin 2) :
    |x k - y k| ≤ dist x y := by
  rw [← Real.dist_eq]
  exact PiLp.dist_apply_le x y k

/-! ## The pathwise grid comparison -/

/-- Five-term triangle inequality through a comparison path at two grid points. -/
theorem dist_le_of_five {f g : ℝ≥0 → BouRabeeGwynne.Euc 2} {s t p q : ℝ≥0} {κ₁ κ₂ a : ℝ}
    (hs : dist (f s) (f p) ≤ κ₂) (ht : dist (f t) (f q) ≤ κ₂)
    (hp : dist (f p) (g p) ≤ κ₁) (hq : dist (f q) (g q) ≤ κ₁)
    (hg : dist (g q) (g p) ≤ a) :
    dist (f t) (f s) ≤ a + 2 * κ₁ + 2 * κ₂ := by
  have e1 := dist_triangle (f t) (f q) (f s)
  have e2 := dist_triangle (f q) (g q) (f s)
  have e3 := dist_triangle (g q) (g p) (f s)
  have e4 := dist_triangle (g p) (f p) (f s)
  rw [dist_comm (g p) (f p), dist_comm (f p) (f s)] at e4
  linarith

/-- **Ordered pathwise grid comparison.**  For `s ≤ t ≤ b` with `t - s < Δ`, the path `f`
moves by at most the grid-lag oscillation of `g` plus twice the closeness and twice the
one-cell oscillation, on the grid of mesh `δ`, provided `N δ ≥ b`, `b < H` and `L δ ≥ Δ + δ`. -/
theorem dist_le_of_grid_bounds {f g : ℝ≥0 → BouRabeeGwynne.Euc 2} {b H δ : ℝ≥0}
    {Δ κ₁ κ₂ a : ℝ} {N L : ℕ}
    (hδ : 0 < δ) (hNb : (b : ℝ) ≤ (N : ℝ) * δ) (hbH : b < H)
    (hL : Δ + (δ : ℝ) ≤ (L : ℝ) * δ)
    (hclose : ∀ r < H, dist (f r) (g r) ≤ κ₁)
    (hmesh : ∀ s ≤ b, ∀ t ≤ b, dist s t < (δ : ℝ) → dist (f s) (f t) ≤ κ₂)
    (hgrid : ∀ i j : ℕ, i ≤ j → j ≤ N → j - i ≤ L →
      dist (g ((j : ℝ≥0) * δ)) (g ((i : ℝ≥0) * δ)) ≤ a)
    {s t : ℝ≥0} (hsb : s ≤ b) (htb : t ≤ b) (hst : s ≤ t) (hlag : (t : ℝ) - s < Δ) :
    dist (f t) (f s) ≤ a + 2 * κ₁ + 2 * κ₂ := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hsR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have htbR : (t : ℝ) ≤ (b : ℝ) := by exact_mod_cast htb
  have hgridpt : ∀ (u : ℝ≥0) (k : ℕ), (k : ℝ) * δ ≤ u → (u : ℝ) < (k : ℝ) * δ + δ →
      (k : ℝ≥0) * δ ≤ u ∧ dist u ((k : ℝ≥0) * δ) < (δ : ℝ) := by
    intro u k hle hlt
    have hcoe : (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) = (k : ℝ) * δ := by
      rw [NNReal.coe_mul, NNReal.coe_natCast]
    refine ⟨?_, ?_⟩
    · have h : (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) ≤ (u : ℝ) := by
        rw [hcoe]
        exact hle
      exact_mod_cast h
    · rw [NNReal.dist_eq, hcoe, abs_of_nonneg (sub_nonneg.2 hle)]
      linarith
  obtain ⟨i, hi_le, hi_lt⟩ : ∃ i : ℕ, (i : ℝ) * δ ≤ s ∧ (s : ℝ) < (i : ℝ) * δ + δ := by
    refine ⟨⌊(s : ℝ) / δ⌋₊, (le_div_iff₀ hδR).1 (Nat.floor_le (div_nonneg s.2 δ.2)), ?_⟩
    have h := (div_lt_iff₀ hδR).1 (Nat.lt_floor_add_one ((s : ℝ) / δ))
    rw [add_mul, one_mul] at h
    exact h
  obtain ⟨j, hj_le, hj_lt⟩ : ∃ j : ℕ, (j : ℝ) * δ ≤ t ∧ (t : ℝ) < (j : ℝ) * δ + δ := by
    refine ⟨⌊(t : ℝ) / δ⌋₊, (le_div_iff₀ hδR).1 (Nat.floor_le (div_nonneg t.2 δ.2)), ?_⟩
    have h := (div_lt_iff₀ hδR).1 (Nat.lt_floor_add_one ((t : ℝ) / δ))
    rw [add_mul, one_mul] at h
    exact h
  have hij : i ≤ j := by
    have h1 : (i : ℝ) * δ < ((j : ℝ) + 1) * δ := by
      rw [add_mul, one_mul]
      linarith
    have h2 : (i : ℝ) < (j : ℝ) + 1 := lt_of_mul_lt_mul_right h1 hδR.le
    have h3 : i < j + 1 := by exact_mod_cast h2
    omega
  have hjN : j ≤ N := by
    have h1 : (j : ℝ) * δ ≤ (N : ℝ) * δ := by linarith
    have h2 : (j : ℝ) ≤ (N : ℝ) := le_of_mul_le_mul_right h1 hδR
    exact_mod_cast h2
  have hjiL : j - i ≤ L := by
    have h1 : ((j : ℝ) - i) * δ < (L : ℝ) * δ := by
      have h1' : (j : ℝ) * δ - (i : ℝ) * δ < (L : ℝ) * δ := by linarith
      rwa [← sub_mul] at h1'
    have h2 : (j : ℝ) - i < L := lt_of_mul_lt_mul_right h1 hδR.le
    have h3 : ((j - i : ℕ) : ℝ) < L := by
      rw [Nat.cast_sub hij]
      exact h2
    have h4 : j - i < L := by exact_mod_cast h3
    exact h4.le
  obtain ⟨hpi, hdi⟩ := hgridpt s i hi_le hi_lt
  obtain ⟨hqj, hdj⟩ := hgridpt t j hj_le hj_lt
  have hpb : (i : ℝ≥0) * δ ≤ b := hpi.trans hsb
  have hqb : (j : ℝ≥0) * δ ≤ b := hqj.trans htb
  exact dist_le_of_five (hmesh s hsb _ hpb hdi) (hmesh t htb _ hqb hdj)
    (hclose _ (lt_of_le_of_lt hpb hbH)) (hclose _ (lt_of_le_of_lt hqb hbH))
    (hgrid i j hij hjN hjiL)

/-- **The pathwise grid comparison, as an inclusion of events.**  A window-modulus failure of
the continuous path `I ω` forces a closeness failure against `G` before the horizon `H`, a
one-cell modulus failure of `I ω`, or a grid-lag failure of `G`. -/
theorem preimage_windowModulusFailure_subset {Ω : Type*}
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    {b H δ : ℝ≥0} {Δ a κ₁ κ₂ : ℝ} {N L : ℕ}
    (hδ : 0 < δ) (hNb : (b : ℝ) ≤ (N : ℝ) * δ) (hbH : b < H)
    (hL : Δ + (δ : ℝ) ≤ (L : ℝ) * δ) :
    I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) b a Δ ⊆
      ({ω | ∃ r < H, κ₁ < dist (I ω r) (G r ω)} ∪
        I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) b κ₂ δ) ∪
        {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
          a - 2 * κ₁ - 2 * κ₂ < dist (G ((j : ℝ≥0) * δ) ω) (G ((i : ℝ≥0) * δ) ω)} := by
  intro ω hω
  obtain ⟨s, hs, t, ht, hst, hlt⟩ := hω
  by_cases hA : ∃ r < H, κ₁ < dist (I ω r) (G r ω)
  · exact Or.inl (Or.inl hA)
  by_cases hB : I ω ∈ windowModulusFailure (E := BouRabeeGwynne.Euc 2) b κ₂ δ
  · exact Or.inl (Or.inr hB)
  by_cases hC : ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
      a - 2 * κ₁ - 2 * κ₂ < dist (G ((j : ℝ≥0) * δ) ω) (G ((i : ℝ≥0) * δ) ω)
  · exact Or.inr hC
  exfalso
  have hclose : ∀ r < H, dist (I ω r) (G r ω) ≤ κ₁ :=
    fun r hr => not_lt.1 fun h => hA ⟨r, hr, h⟩
  have hmesh : ∀ s ≤ b, ∀ t ≤ b, dist s t < (δ : ℝ) → dist (I ω s) (I ω t) ≤ κ₂ :=
    fun s hs t ht hst => not_lt.1 fun h => hB ⟨s, hs, t, ht, hst, h⟩
  have hgrid : ∀ i j : ℕ, i ≤ j → j ≤ N → j - i ≤ L →
      dist (G ((j : ℝ≥0) * δ) ω) (G ((i : ℝ≥0) * δ) ω) ≤ a - 2 * κ₁ - 2 * κ₂ :=
    fun i j hij hjN hji => not_lt.1 fun h => hC ⟨i, j, hij, hjN, hji, h⟩
  rcases le_total s t with hst' | hts'
  · have hsR : (s : ℝ) ≤ t := by exact_mod_cast hst'
    have hlag : (t : ℝ) - s < Δ := by
      rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hsR)] at hst
      exact hst
    have key := dist_le_of_grid_bounds hδ hNb hbH hL hclose hmesh hgrid hs ht hst' hlag
    rw [dist_comm] at key
    linarith
  · have htR : (t : ℝ) ≤ s := by exact_mod_cast hts'
    have hlag : (s : ℝ) - t < Δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 htR)] at hst
      exact hst
    have key := dist_le_of_grid_bounds hδ hNb hbH hL hclose hmesh hgrid ht hs hts' hlag
    linarith

/-- **The plane grid-lag event splits into the two coordinate events**, after diffusive
scaling by `ε` of the values and dilation by `ε⁻²` of the grid. -/
theorem gridLag_subset_coordinates {Ω : Type*} (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    {ε : ℝ≥0} (hε : 0 < ε) (d : ℝ≥0) (N L : ℕ) (a : ℝ) :
    {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
        a < dist (G ((j : ℝ≥0) * (ε⁻¹ ^ 2 * d)) ω) (G ((i : ℝ≥0) * (ε⁻¹ ^ 2 * d)) ω)} ⊆
      {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
        (ε : ℝ) * (a / 2) < |(ε : ℝ) * G (ε⁻¹ ^ 2 * ((j : ℝ≥0) * d)) ω 0 -
          (ε : ℝ) * G (ε⁻¹ ^ 2 * ((i : ℝ≥0) * d)) ω 0|} ∪
      {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
        (ε : ℝ) * (a / 2) < |(ε : ℝ) * G (ε⁻¹ ^ 2 * ((j : ℝ≥0) * d)) ω 1 -
          (ε : ℝ) * G (ε⁻¹ ^ 2 * ((i : ℝ≥0) * d)) ω 1|} := by
  rintro ω ⟨i, j, hij, hjN, hji, hlt⟩
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  rw [mul_left_comm (j : ℝ≥0), mul_left_comm (i : ℝ≥0)] at hlt
  have hscale : ∀ x y : ℝ, a / 2 < |x - y| →
      (ε : ℝ) * (a / 2) < |(ε : ℝ) * x - (ε : ℝ) * y| := by
    intro x y hxy
    rw [← mul_sub, abs_mul, abs_of_pos hεR]
    exact mul_lt_mul_of_pos_left hxy hεR
  rcases half_lt_abs_sub_zero_or_one hlt with h0 | h1
  · exact Or.inl ⟨i, j, hij, hjN, hji, hscale _ _ h0⟩
  · exact Or.inr ⟨i, j, hij, hjN, hji, hscale _ _ h1⟩

/-- **A coordinate grid-lag event is a scalar array grid-lag event up to disagreement.**  If the
scalar path `Y` agrees with the rescaled coordinate on `[0, H]`, and the grid ends at `H`, the
coordinate event at threshold `θ` is contained in the array event at any threshold `θ' ≤ θ`. -/
theorem coordEvent_subset_disagree_union_core {Ω : Type*}
    (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (Y : ℝ≥0 → Ω → ℝ) {ε : ℝ≥0} (d H : ℝ≥0)
    (N L : ℕ) (hNd : (N : ℝ≥0) * d = H) (k : Fin 2) {θ θ' : ℝ} (hθ : θ' ≤ θ) :
    {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
        θ < |(ε : ℝ) * G (ε⁻¹ ^ 2 * ((j : ℝ≥0) * d)) ω k -
          (ε : ℝ) * G (ε⁻¹ ^ 2 * ((i : ℝ≥0) * d)) ω k|} ⊆
      {ω | ∃ t ≤ H, Y t ω ≠ (ε : ℝ) * G (ε⁻¹ ^ 2 * t) ω k} ∪
        {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
          θ' < |Y ((j : ℝ≥0) * d) ω - Y ((i : ℝ≥0) * d) ω|} := by
  rintro ω ⟨i, j, hij, hjN, hji, hlt⟩
  by_cases hdis : ∃ t ≤ H, Y t ω ≠ (ε : ℝ) * G (ε⁻¹ ^ 2 * t) ω k
  · exact Or.inl hdis
  · have hag : ∀ t ≤ H, Y t ω = (ε : ℝ) * G (ε⁻¹ ^ 2 * t) ω k :=
      fun t ht => not_not.1 fun h => hdis ⟨t, ht, h⟩
    have hjH : (j : ℝ≥0) * d ≤ H := by
      rw [← hNd]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) zero_le
    have hiH : (i : ℝ≥0) * d ≤ H := by
      rw [← hNd]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij.trans hjN) zero_le
    refine Or.inr ⟨i, j, hij, hjN, hji, ?_⟩
    rw [hag _ hjH, hag _ hiH]
    exact lt_of_le_of_lt hθ hlt

/-! ## The localized martingale array -/

/-- **A localized scalar martingale array for the target array `X` on the horizon `[0, H]`.**

`Y n` is a martingale for the filtration `F n`; `B n` is a compensator making
`Y n ^ 2 - B n` a martingale (the same bracket a bracket law of large numbers speaks about);
the terminal second moments at `H` are uniformly bounded; the bracket error against the linear
bracket `v t` has an integrable envelope `R n` with vanishing mean; and `Y n` agrees with `X n`
on `[0, H]` with probability tending to one.

These are exactly the outputs of the project's threshold-stopped lane:
`MartingaleLimit.threshold_stopped_martingale_tightness_inputs_with_cadlag` (martingale,
compensated square, `L²`, càdlàg, terminal moment) and
`MartingaleLimit.exists_threshold_bracket_localization_of_ucp` (rare exits, bounded stopped
bracket, integrable envelope with vanishing mean). -/
structure LocalizedMartingaleArray {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : @Measure Ω mΩ) (X : ℕ → ℝ≥0 → Ω → ℝ) (H : ℝ≥0) where
  /-- The filtrations of the rows. -/
  F : ℕ → Filtration ℝ≥0 mΩ
  /-- The martingale rows. -/
  Y : ℕ → ℝ≥0 → Ω → ℝ
  /-- The compensators of the squares. -/
  B : ℕ → ℝ≥0 → Ω → ℝ
  /-- The bracket-error envelopes. -/
  R : ℕ → Ω → ℝ
  /-- The terminal second-moment bound. -/
  C : ℝ
  /-- The slope of the limiting bracket. -/
  v : ℝ
  martingale : ∀ n, Martingale (Y n) (F n) P
  compensated : ∀ n, Martingale (fun t ω => Y n t ω * Y n t ω - B n t ω) (F n) P
  cadlag : ∀ n, ∀ᵐ ω ∂P, IsCadlag (fun t => Y n t ω)
  rightContinuous_compensated : ∀ n, ∀ᵐ ω ∂P,
    IsRightContinuous (fun t => Y n t ω * Y n t ω - B n t ω)
  memLp : ∀ n t, MemLp (Y n t) 2 P
  terminal : ∀ n, ∫ ω, (Y n H ω) ^ 2 ∂P ≤ C
  v_nonneg : 0 ≤ v
  integrable_error : ∀ n, Integrable (R n) P
  error : ∀ n, ∀ᵐ ω ∂P, ∀ t ≤ H, |B n t ω - v * (t : ℝ)| ≤ R n ω
  error_mean : Tendsto (fun n => ∫ ω, R n ω ∂P) atTop (𝓝 0)
  agree : Tendsto (fun n => P {ω | ∃ t ≤ H, Y n t ω ≠ X n t ω}) atTop (𝓝 0)

/-! ## The probabilistic weld -/

/-- **One deterministic mesh per row.**  The single law of a measurable continuous
interpolation has a window modulus (`finite_measure_windowModulusFailure_tail`), so a mesh
`H / N` can be chosen at most `ℓ` and fine enough for a prescribed one-cell budget. -/
theorem exists_mesh_for_row {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    {ε H : ℝ≥0} (hε : 0 < ε) (hH : 0 < H) {θ : ℝ} (hθ : 0 < θ) {τ : ℝ≥0∞} (hτ : 0 < τ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ N : ℕ, 0 < N ∧ ((H / (N : ℝ≥0) : ℝ≥0) : ℝ) ≤ ℓ ∧
      P (I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) (ε⁻¹ ^ 2 * H)
        (θ / (ε : ℝ)) (2 * ((ε⁻¹ ^ 2 * (H / (N : ℝ≥0)) : ℝ≥0) : ℝ))) ≤ τ := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  obtain ⟨δs, hδs, hbound⟩ := finite_measure_windowModulusFailure_tail (P.map I)
    (ε⁻¹ ^ 2 * H) (div_pos hθ hεR) hτ
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((H : ℝ) / ℓ) (2 * (((ε : ℝ))⁻¹ ^ 2 * H) / δs))
  have hmax0 : (0 : ℝ) ≤ max ((H : ℝ) / ℓ) (2 * (((ε : ℝ))⁻¹ ^ 2 * H) / δs) :=
    le_max_of_le_left (div_nonneg hHR.le hℓ.le)
  have hNR : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt hmax0 hN
  have hN1 : (H : ℝ) / ℓ < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 * (((ε : ℝ))⁻¹ ^ 2 * H) / δs < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hcoe : ((H / (N : ℝ≥0) : ℝ≥0) : ℝ) = (H : ℝ) / (N : ℝ) := by
    rw [NNReal.coe_div, NNReal.coe_natCast]
  refine ⟨N, by exact_mod_cast hNR, ?_, ?_⟩
  · rw [hcoe, div_le_iff₀ hNR]
    rw [div_lt_iff₀ hℓ] at hN1
    linarith
  · rw [← Measure.map_apply hI
      (measurableSet_windowModulusFailure (E := BouRabeeGwynne.Euc 2) _ _ _)]
    refine le_trans (measure_mono (windowModulusFailure_mono le_rfl le_rfl ?_)) hbound
    have key : 2 * (((ε : ℝ))⁻¹ ^ 2 * ((H : ℝ) / N)) ≤ δs := by
      rw [div_lt_iff₀ hδs] at hN2
      rw [show 2 * (((ε : ℝ))⁻¹ ^ 2 * ((H : ℝ) / N)) = 2 * (((ε : ℝ))⁻¹ ^ 2 * H) / N by ring,
        div_le_iff₀ hNR]
      linarith
    rw [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv, hcoe]
    exact key

/-- **The maximal grid jump of a localized coordinate array vanishes in probability**, derived
from closeness of the interpolation to the comparison process and a row mesh whose one-cell
failures (threshold `θ n → 0`, probability `τ n → 0`) are rare.  No jump bound of the
comparison process is assumed. -/
theorem tendsto_gridJump_of_close_mesh {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {mQ : MeasurableSpace Ω} {Q : @Measure Ω mQ} (hQP : ∀ s : Set Ω, Q s = P s)
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n) (H : ℝ≥0) (k : Fin 2)
    (Y : ℕ → ℝ≥0 → Ω → ℝ) (d : ℕ → ℝ≥0) (N : ℕ → ℕ)
    (hd : ∀ n, 0 < d n) (hNd : ∀ n, (N n : ℝ≥0) * d n = H)
    (hagree : Tendsto (fun n => Q {ω | ∃ t ≤ H,
      Y n t ω ≠ (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω k}) atTop (𝓝 0))
    (hclose : ∀ κ : ℝ, 0 < κ → Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * (H + 1),
      κ < (ε n : ℝ) * dist (I ω r) (G r ω)}) atTop (𝓝 0))
    (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0)) (τ : ℕ → ℝ≥0∞) (hτ : Tendsto τ atTop (𝓝 0))
    (hmesh : ∀ n, P (I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2)
      ((ε n)⁻¹ ^ 2 * H) (θ n / (ε n : ℝ)) (2 * (((ε n)⁻¹ ^ 2 * d n : ℝ≥0) : ℝ))) ≤ τ n) :
    ∀ b : ℝ, 0 < b → Tendsto (fun n => Q {ω | ∃ i < N n,
      b < |Y n (((i + 1 : ℕ) : ℝ≥0) * d n) ω - Y n ((i : ℝ≥0) * d n) ω|}) atTop (𝓝 0) := by
  intro b hb
  have hb4 : (0 : ℝ) < b / 4 := div_pos hb (by norm_num)
  have hup : Tendsto (fun n => Q {ω | ∃ t ≤ H, Y n t ω ≠ (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω k} +
      P {ω | ∃ r < (ε n)⁻¹ ^ 2 * (H + 1), b / 4 < (ε n : ℝ) * dist (I ω r) (G r ω)} + τ n)
      atTop (𝓝 0) := by
    simpa only [add_zero] using (hagree.add (hclose (b / 4) hb4)).add hτ
  have hθev : ∀ᶠ n in atTop, θ n ≤ b / 4 :=
    ((tendsto_order.1 hθ).2 (b / 4) hb4).mono fun _ h => h.le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hθev] with n hθn
  have hεn : (0 : ℝ) < (ε n : ℝ) := by exact_mod_cast hεpos n
  have hsub : {ω | ∃ i < N n,
      b < |Y n (((i + 1 : ℕ) : ℝ≥0) * d n) ω - Y n ((i : ℝ≥0) * d n) ω|} ⊆
      ({ω | ∃ t ≤ H, Y n t ω ≠ (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω k} ∪
        {ω | ∃ r < (ε n)⁻¹ ^ 2 * (H + 1), b / 4 < (ε n : ℝ) * dist (I ω r) (G r ω)}) ∪
        I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * H)
          (θ n / (ε n : ℝ)) (2 * (((ε n)⁻¹ ^ 2 * d n : ℝ≥0) : ℝ)) := by
    rintro ω ⟨i, hi, hjump⟩
    by_cases h1 : ∃ t ≤ H, Y n t ω ≠ (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω k
    · exact Or.inl (Or.inl h1)
    by_cases h2 : ∃ r < (ε n)⁻¹ ^ 2 * (H + 1), b / 4 < (ε n : ℝ) * dist (I ω r) (G r ω)
    · exact Or.inl (Or.inr h2)
    by_cases h3 : I ω ∈ windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * H)
        (θ n / (ε n : ℝ)) (2 * (((ε n)⁻¹ ^ 2 * d n : ℝ≥0) : ℝ))
    · exact Or.inr h3
    exfalso
    have hag : ∀ t ≤ H, Y n t ω = (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω k :=
      fun t ht => not_not.1 fun h => h1 ⟨t, ht, h⟩
    have hcl : ∀ r < (ε n)⁻¹ ^ 2 * (H + 1), (ε n : ℝ) * dist (I ω r) (G r ω) ≤ b / 4 :=
      fun r hr => not_lt.1 fun h => h2 ⟨r, hr, h⟩
    have hme : ∀ s ≤ (ε n)⁻¹ ^ 2 * H, ∀ t ≤ (ε n)⁻¹ ^ 2 * H,
        dist s t < 2 * (((ε n)⁻¹ ^ 2 * d n : ℝ≥0) : ℝ) →
          dist (I ω s) (I ω t) ≤ θ n / (ε n : ℝ) :=
      fun s hs t ht hst => not_lt.1 fun h => h3 ⟨s, hs, t, ht, hst, h⟩
    have hiN : ((i + 1 : ℕ) : ℝ≥0) * d n ≤ H := by
      rw [← hNd n]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) zero_le
    have hiN' : (i : ℝ≥0) * d n ≤ H := by
      rw [← hNd n]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) zero_le
    have hepos : 0 < (ε n)⁻¹ ^ 2 := pow_pos (inv_pos.2 (hεpos n)) 2
    have hwin₁ : (ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n) ≤ (ε n)⁻¹ ^ 2 * H :=
      mul_le_mul_of_nonneg_left hiN zero_le
    have hwin₀ : (ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n) ≤ (ε n)⁻¹ ^ 2 * H :=
      mul_le_mul_of_nonneg_left hiN' zero_le
    have hHlt : (ε n)⁻¹ ^ 2 * H < (ε n)⁻¹ ^ 2 * (H + 1) :=
      mul_lt_mul_of_pos_left (lt_add_one H) hepos
    have hsplit : (ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n) =
        (ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n) + (ε n)⁻¹ ^ 2 * d n := by
      push_cast
      ring
    have hdist : dist ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n))
        ((ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n)) < 2 * (((ε n)⁻¹ ^ 2 * d n : ℝ≥0) : ℝ) := by
      rw [hsplit, NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left,
        abs_of_nonneg (NNReal.coe_nonneg _)]
      have hpos : (0 : ℝ) < (((ε n)⁻¹ ^ 2 * d n : ℝ≥0) : ℝ) := by
        exact_mod_cast mul_pos hepos (hd n)
      linarith
    have hc₁ := hcl _ (lt_of_le_of_lt hwin₁ hHlt)
    have hc₀ := hcl _ (lt_of_le_of_lt hwin₀ hHlt)
    have hm := hme _ hwin₁ _ hwin₀ hdist
    rw [le_div_iff₀' hεn] at hm
    rw [hag _ hiN, hag _ hiN'] at hjump
    have hcoord : |(ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)) ω k -
        (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n)) ω k| ≤
        (ε n : ℝ) * dist (G ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)) ω)
          (G ((ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n)) ω) := by
      rw [← mul_sub, abs_mul, abs_of_pos hεn]
      exact mul_le_mul_of_nonneg_left (abs_sub_apply_le_dist _ _ k) hεn.le
    have htri := dist_triangle (G ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)) ω)
      (I ω ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)))
      (G ((ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n)) ω)
    have htri' := dist_triangle (I ω ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)))
      (I ω ((ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n)))
      (G ((ε n)⁻¹ ^ 2 * ((i : ℝ≥0) * d n)) ω)
    rw [dist_comm (G ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)) ω)
      (I ω ((ε n)⁻¹ ^ 2 * (((i + 1 : ℕ) : ℝ≥0) * d n)))] at htri
    have hmul₁ := mul_le_mul_of_nonneg_left htri hεn.le
    have hmul₂ := mul_le_mul_of_nonneg_left htri' hεn.le
    rw [mul_add] at hmul₁ hmul₂
    linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add le_rfl (hQP _).le))
    ((hQP _).le.trans (hmesh n))))

/-- **The sequential window modulus of a continuous interpolation from localized martingale
arrays for the two coordinates of a comparison process.**

CONDITIONAL on `hclose` and `harray` (see the module docstring); this is an implication and
certifies no tightness estimate for the reflected walk.  The maximal-grid-jump premise of the
core estimate is *derived* here, not assumed. -/
theorem eventually_window_tail_of_localized_arrays
    {Ω : Type*} {mQ : MeasurableSpace Ω} {Q : @Measure Ω mQ} [@IsProbabilityMeasure Ω mQ Q]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hQP : ∀ s : Set Ω, Q s = P s)
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hclose : ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ → Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      κ < (ε n : ℝ) * dist (I ω r) (G r ω)}) atTop (𝓝 0))
    (harray : ∀ (k : Fin 2) (H : ℝ≥0), Nonempty (LocalizedMartingaleArray Q
      (fun n u ω => (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * u) ω k) H))
    (m : ℕ) (c : ℝ) (hc : 0 < c) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in atTop,
      P (I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * (m : ℝ≥0))
        (c / (ε n : ℝ)) (((ε n : ℝ))⁻¹ ^ 2 * d)) ≤ η := by
  obtain ⟨H, hH⟩ : ∃ H : ℝ≥0, H = (m : ℝ≥0) + 1 := ⟨_, rfl⟩
  have hHpos : 0 < H := by
    rw [hH]
    exact add_pos_of_nonneg_of_pos zero_le one_pos
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = c / 16 := ⟨_, rfl⟩
  have hκpos : 0 < κ := by
    rw [hκ]
    exact div_pos hc (by norm_num)
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hη4 : 0 < η / 2 / 2 := ENNReal.half_pos hη2.ne'
  have hη8 : 0 < η / 2 / 2 / 2 := ENNReal.half_pos hη4.ne'
  obtain ⟨ρ, hρ, hρη⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ ≤ η / 2 / 2 / 2 := by
    by_cases htop : η / 2 / 2 / 2 = ⊤
    · exact ⟨1, one_pos, by simp [htop]⟩
    · refine ⟨(η / 2 / 2 / 2).toReal / 2,
        div_pos (ENNReal.toReal_pos hη8.ne' htop) (by norm_num), ?_⟩
      calc ENNReal.ofReal ((η / 2 / 2 / 2).toReal / 2)
          ≤ ENNReal.ofReal (η / 2 / 2 / 2).toReal :=
            ENNReal.ofReal_le_ofReal (half_le_self ENNReal.toReal_nonneg)
        _ = η / 2 / 2 / 2 := ENNReal.ofReal_toReal htop
  obtain ⟨A0⟩ := harray 0 H
  obtain ⟨A1⟩ := harray 1 H
  have hsel : ∀ n : ℕ, ∃ N : ℕ, 0 < N ∧ ((H / (N : ℝ≥0) : ℝ≥0) : ℝ) ≤ 1 / ((n : ℝ) + 1) ∧
      P (I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * H)
        (1 / ((n : ℝ) + 1) / (ε n : ℝ))
        (2 * (((ε n)⁻¹ ^ 2 * (H / (N : ℝ≥0)) : ℝ≥0) : ℝ))) ≤ (n : ℝ≥0∞)⁻¹ := fun n =>
    exists_mesh_for_row P I hI (hεpos n) hHpos (by positivity)
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)) (by positivity)
  choose N hNpos hNsmall hNmesh using hsel
  have hdpos : ∀ n, 0 < H / (N n : ℝ≥0) := fun n =>
    div_pos hHpos (by exact_mod_cast hNpos n)
  have hNd : ∀ n, (N n : ℝ≥0) * (H / (N n : ℝ≥0)) = H := fun n =>
    mul_div_cancel₀ H (by exact_mod_cast (hNpos n).ne')
  have hjump : ∀ (k : Fin 2) (A : LocalizedMartingaleArray Q
      (fun n u ω => (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * u) ω k) H),
      ∀ b : ℝ, 0 < b → Tendsto (fun n => Q {ω | ∃ i < N n,
        b < |A.Y n (((i + 1 : ℕ) : ℝ≥0) * (H / (N n : ℝ≥0))) ω -
          A.Y n ((i : ℝ≥0) * (H / (N n : ℝ≥0))) ω|}) atTop (𝓝 0) := fun k A =>
    tendsto_gridJump_of_close_mesh hQP I G ε hεpos H k A.Y (fun n => H / (N n : ℝ≥0)) N
      hdpos hNd A.agree (fun κ hκ => hclose (H + 1) κ hκ) (fun n => 1 / ((n : ℝ) + 1))
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun n => (n : ℝ≥0∞)⁻¹)
      ENNReal.tendsto_inv_nat_nhds_zero hNmesh
  have hcore : ∀ (k : Fin 2) (A : LocalizedMartingaleArray Q
      (fun n u ω => (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * u) ω k) H),
      ∃ D : ℝ≥0, 0 < D ∧ ∀ᶠ n in atTop, ∀ L : ℕ, (L : ℝ≥0) * (H / (N n : ℝ≥0)) ≤ D →
        Q {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N n ∧ j - i ≤ L ∧
          c / 4 < |A.Y n ((j : ℝ≥0) * (H / (N n : ℝ≥0))) ω -
            A.Y n ((i : ℝ≥0) * (H / (N n : ℝ≥0))) ω|} ≤ ENNReal.ofReal ρ := by
    intro k A
    exact uniform_grid_oscillation_probability_le (P := Q) (F := A.F) (M := A.Y) (B := A.B)
      (fun n => H / (N n : ℝ≥0)) N A.martingale A.compensated
      (fun n => (A.cadlag n).mono fun _ h => h.isRightContinuous)
      A.rightContinuous_compensated (fun n => A.memLp n _) (C := A.C)
      (fun n => by simp only [hNd n]; exact A.terminal n) (v := A.v) A.v_nonneg (R := A.R)
      A.integrable_error (fun n => by simp only [hNd n]; exact A.error n) A.error_mean
      (hjump k A) (c / 4) (div_pos hc (by norm_num)) ρ hρ
  obtain ⟨D0, hD0, hosc0⟩ := hcore 0 A0
  obtain ⟨D1, hD1, hosc1⟩ := hcore 1 A1
  have hD : 0 < min D0 D1 := lt_min hD0 hD1
  have hDR : (0 : ℝ) < ((min D0 D1 : ℝ≥0) : ℝ) := by exact_mod_cast hD
  refine ⟨((min D0 D1 : ℝ≥0) : ℝ) / 4, div_pos hDR (by norm_num), ?_⟩
  have hev_close : ∀ᶠ n in atTop, P {ω | ∃ r < (ε n)⁻¹ ^ 2 * (H + 1),
      κ < (ε n : ℝ) * dist (I ω r) (G r ω)} < η / 2 / 2 :=
    (tendsto_order.1 (hclose (H + 1) κ hκpos)).2 _ hη4
  have hev_inv : ∀ᶠ n : ℕ in atTop, (n : ℝ≥0∞)⁻¹ < η / 2 / 2 :=
    (tendsto_order.1 ENNReal.tendsto_inv_nat_nhds_zero).2 _ hη4
  have hev_ag0 : ∀ᶠ n in atTop, Q {ω | ∃ t ≤ H,
      A0.Y n t ω ≠ (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω 0} < η / 2 / 2 / 2 :=
    (tendsto_order.1 A0.agree).2 _ hη8
  have hev_ag1 : ∀ᶠ n in atTop, Q {ω | ∃ t ≤ H,
      A1.Y n t ω ≠ (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * t) ω 1} < η / 2 / 2 / 2 :=
    (tendsto_order.1 A1.agree).2 _ hη8
  have hev_thr : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ κ :=
    ((tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 κ hκpos).mono
      fun _ h => h.le
  have hev_msh : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ((min D0 D1 : ℝ≥0) : ℝ) / 8 :=
    ((tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _
      (div_pos hDR (by norm_num))).mono fun _ h => h.le
  filter_upwards [hev_close, hev_inv, hev_ag0, hev_ag1, hev_thr, hev_msh, hosc0, hosc1]
    with n hcl hinv hag0 hag1 hthr hmsh ho0 ho1
  have hεn : (0 : ℝ) < (ε n : ℝ) := by exact_mod_cast hεpos n
  have hepos : 0 < (ε n)⁻¹ ^ 2 := pow_pos (inv_pos.2 (hεpos n)) 2
  have he0 : (0 : ℝ) ≤ ((ε n : ℝ))⁻¹ ^ 2 := sq_nonneg _
  have hdsmall : H / (N n : ℝ≥0) ≤ min D0 D1 / 8 := by
    have h1 : ((H / (N n : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((min D0 D1 : ℝ≥0) : ℝ) / 8 :=
      (hNsmall n).trans hmsh
    have h2 : ((min D0 D1 / 8 : ℝ≥0) : ℝ) = ((min D0 D1 : ℝ≥0) : ℝ) / 8 := by
      rw [NNReal.coe_div]
      norm_num
    rw [← h2] at h1
    exact_mod_cast h1
  obtain ⟨L, hLlow, hLup⟩ := exists_nat_lag_for_interpolation hD (hdpos n) hdsmall
  have hδ : 0 < (ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) := mul_pos hepos (hdpos n)
  have hNdR : (N n : ℝ) * ((H / (N n : ℝ≥0) : ℝ≥0) : ℝ) = (H : ℝ) := by
    have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) (hNd n)
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using h
  have hHR : (H : ℝ) = (m : ℝ) + 1 := by
    rw [hH, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  have hNb : (((ε n)⁻¹ ^ 2 * (m : ℝ≥0) : ℝ≥0) : ℝ) ≤
      (N n : ℝ) * (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ) := by
    have e1 : (N n : ℝ) * (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ) =
        ((ε n : ℝ))⁻¹ ^ 2 * ((m : ℝ) + 1) := by
      rw [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv, mul_left_comm, hNdR, hHR]
    rw [e1, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast]
    exact mul_le_mul_of_nonneg_left (by linarith) he0
  have hbH : (ε n)⁻¹ ^ 2 * (m : ℝ≥0) < (ε n)⁻¹ ^ 2 * (H + 1) := by
    refine mul_lt_mul_of_pos_left ?_ hepos
    rw [hH]
    exact (lt_add_one (m : ℝ≥0)).trans (lt_add_one _)
  have hL : ((ε n : ℝ))⁻¹ ^ 2 * (((min D0 D1 : ℝ≥0) : ℝ) / 4) +
      (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ) ≤
      (L : ℝ) * (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ) := by
    have hLlowR : ((min D0 D1 : ℝ≥0) : ℝ) / 4 + 2 * ((H / (N n : ℝ≥0) : ℝ≥0) : ℝ) ≤
        (L : ℝ) * ((H / (N n : ℝ≥0) : ℝ≥0) : ℝ) := by
      exact_mod_cast hLlow
    have hdn : (0 : ℝ) ≤ ((H / (N n : ℝ≥0) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    rw [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
    nlinarith [mul_le_mul_of_nonneg_left hLlowR he0, mul_nonneg he0 hdn]
  have hincl := preimage_windowModulusFailure_subset I G
    (b := (ε n)⁻¹ ^ 2 * (m : ℝ≥0)) (H := (ε n)⁻¹ ^ 2 * (H + 1))
    (δ := (ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)))
    (Δ := ((ε n : ℝ))⁻¹ ^ 2 * (((min D0 D1 : ℝ≥0) : ℝ) / 4))
    (a := c / (ε n : ℝ)) (κ₁ := κ / (ε n : ℝ)) (κ₂ := κ / (ε n : ℝ)) (N := N n) (L := L)
    hδ hNb hbH hL
  have hSclose : {ω | ∃ r < (ε n)⁻¹ ^ 2 * (H + 1), κ / (ε n : ℝ) < dist (I ω r) (G r ω)} ⊆
      {ω | ∃ r < (ε n)⁻¹ ^ 2 * (H + 1), κ < (ε n : ℝ) * dist (I ω r) (G r ω)} := by
    rintro ω ⟨r, hr, hlt⟩
    exact ⟨r, hr, (div_lt_iff₀' hεn).1 hlt⟩
  have hSmesh : I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2)
      ((ε n)⁻¹ ^ 2 * (m : ℝ≥0)) (κ / (ε n : ℝ))
      (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ) ⊆
      I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * H)
        (1 / ((n : ℝ) + 1) / (ε n : ℝ))
        (2 * (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ)) := by
    refine Set.preimage_mono (windowModulusFailure_mono ?_ ?_ ?_)
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      rw [hH]
      exact le_self_add
    · exact div_le_div_of_nonneg_right hthr hεn.le
    · have h0 : (0 : ℝ) ≤ (((ε n)⁻¹ ^ 2 * (H / (N n : ℝ≥0)) : ℝ≥0) : ℝ) :=
        NNReal.coe_nonneg _
      linarith
  have hθ : c / 4 ≤ (ε n : ℝ) *
      ((c / (ε n : ℝ) - 2 * (κ / (ε n : ℝ)) - 2 * (κ / (ε n : ℝ))) / 2) := by
    have e1 : c / (ε n : ℝ) - 2 * (κ / (ε n : ℝ)) - 2 * (κ / (ε n : ℝ)) =
        (c - 4 * κ) / (ε n : ℝ) := by ring
    rw [e1, ← mul_div_assoc, mul_div_cancel₀ (c - 4 * κ) hεn.ne', hκ]
    linarith
  have hgrid := (gridLag_subset_coordinates G (hεpos n) (H / (N n : ℝ≥0)) (N n) L
      (c / (ε n : ℝ) - 2 * (κ / (ε n : ℝ)) - 2 * (κ / (ε n : ℝ)))).trans
    (Set.union_subset_union
      (coordEvent_subset_disagree_union_core G (A0.Y n) (ε := ε n) (H / (N n : ℝ≥0)) H
        (N n) L (hNd n) 0 hθ)
      (coordEvent_subset_disagree_union_core G (A1.Y n) (ε := ε n) (H / (N n : ℝ≥0)) H
        (N n) L (hNd n) 1 hθ))
  have hsum : (η / 2 / 2 + η / 2 / 2) + ((η / 2 / 2 / 2 + η / 2 / 2 / 2) +
      (η / 2 / 2 / 2 + η / 2 / 2 / 2)) = η := by
    simp only [ENNReal.add_halves]
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans
    (le_trans (add_le_add ?_ ?_) hsum.le))
  · exact (measure_union_le _ _).trans (add_le_add ((measure_mono hSclose).trans hcl.le)
      ((measure_mono hSmesh).trans ((hNmesh n).trans hinv.le)))
  · refine (measure_mono hgrid).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
    · refine (hQP _).symm.le.trans ((measure_union_le _ _).trans (add_le_add hag0.le ?_))
      exact (ho0 L (hLup.trans (min_le_left _ _))).trans hρη
    · refine (hQP _).symm.le.trans ((measure_union_le _ _).trans (add_le_add hag1.le ?_))
      exact (ho1 L (hLup.trans (min_le_right _ _))).trans hρη

/-- **The consumer's `RescaledWindowModulusTail` for the law of a continuous interpolation**,
from closeness to a comparison process and localized coordinate arrays along every positive
null sequence of scales.

CONDITIONAL on `hclose` and `harray`; this certifies no tightness estimate. -/
theorem rescaledWindowModulusTail_of_localized_arrays
    {Ω : Type*} {mQ : MeasurableSpace Ω} {Q : @Measure Ω mQ} [@IsProbabilityMeasure Ω mQ Q]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hQP : ∀ s : Set Ω, Q s = P s)
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (hclose : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ → Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
        κ < (ε n : ℝ) * dist (I ω r) (G r ω)}) atTop (𝓝 0))
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0), Nonempty (LocalizedMartingaleArray Q
        (fun n u ω => (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    RescaledWindowModulusTail (P.toProbabilityMeasure.map I) (Set.Ioc 0 1) := by
  refine rescaledWindowModulusTail_Ioc_of_sequential _ ?_
  intro ε hεpos hεlim m c hc η hη
  obtain ⟨d, hd, hev⟩ := eventually_window_tail_of_localized_arrays hQP I hI G ε hεpos
    (hclose ε hεpos hεlim) (harray ε hεpos hεlim) m c hc η hη
  refine ⟨d, hd, hev.mono fun n hn => ?_⟩
  change (P.map I) _ ≤ η
  rw [Measure.map_apply hI
    (measurableSet_windowModulusFailure (E := BouRabeeGwynne.Euc 2) _ _ _)]
  exact hn

end ReflectedGMS.WindowModulusGridTransfer
