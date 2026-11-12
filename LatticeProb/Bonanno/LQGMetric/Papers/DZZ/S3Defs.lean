/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Eta
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# DZZ §3 setup: dyadic partition, approximate LGD `D'`, ξ-admissible pairs (P2-DZZ3A, WP-113)

Ding–Zeitouni–Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph distance*
(arXiv:1807.00422, `LBM_LGDarXiv.tex`), §3.1, l. 765–798, notation §1.3 l. 287–316.

* `dzzV` = `𝕍 = [0,1]²` (l. 90).
* `DyBox`: the dyadic boxes of `𝕍` (l. 303–313): level `n`, column `j`, row `k` (`j, k < 2ⁿ`),
  side `2^{-n}`, center in `𝔠_n` (l. 307; level 0 is `𝕍` itself, where the partition starts).
* Membership of a point (`DyBox.Mem`): DZZ leave open whether boxes are closed, open or neither
  (l. 778). Convention: box `(n, j, k)` contains `v ∈ 𝕍` iff `⌊2ⁿ v.re⌋ ∧ (2ⁿ − 1) = j` and
  likewise for `k` (half-open boxes, closed at the right/top edge of `𝕍`), so that the boxes of
  each level partition `𝕍` (DEVIATIONS: convention).
* `approxLQG γ W ω b = M_{γ, s_b}(b) = s_b² exp(γ η_{s_b}(c_b) − γ²/2 Var η_{s_b}(c_b))`
  (eq-def-approximate-LQG, l. 769–772); `etaVar ε v = π ‖K^η_{ε,v}‖²` is `Var η_ε(v)` under a
  white noise (`etaInf = √π W(K^η)`).
* The δ-partition `𝒱_δ` (l. 776–783) for an arbitrary box-mass function `m`: a box is a cell iff
  `m b < δ²` and every strict ancestor `a` has `m a ≥ δ²` (`IsCell`): exactly the boxes on which the
  iterative splitting procedure halts.
* `cellGraph m δ`: cells, adjacent iff their closures meet in a non-trivial segment (l. 784–786:
  for distinct dyadic boxes with disjoint interiors, "non-empty relative interior" = "not a
  subsingleton").
* `approxDist m δ u v` = `D'_{γ,δ}(u, v)`, the graph distance between the cells `𝖢_{u,δ}`,
  `𝖢_{v,δ}` (l. 787–790), **counted in cells** (= edge distance `+ 1`), as DZZ use it (proof of
  Lemma 3.5, l. 1086: "`D'(u,v) = d` … `𝖢_1, …, 𝖢_d` neighbouring cells joining `u` to `v`"),
  and so that `D' ≥ 1` like `D` (DEVIATIONS: reading). `⊤` if `u` or `v` lies in no cell.
* `cellSide m δ v = s_{v,δ}` (junk `0` if `v` lies in no cell).
* `dzzVXi ξ = 𝕍^ξ`, `IsXiAdmissible ξ A B` (l. 791–797), `HighProb` (l. 288–290).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- `𝕍 = [0,1]²` (DZZ l. 90). -/
def dzzV : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- A dyadic box of `𝕍`: level `n` (side `2^{-n}`), column `j`, row `k`. -/
@[ext]
structure DyBox where
  n : ℕ
  j : ℕ
  k : ℕ
  hj : j < 2 ^ n
  hk : k < 2 ^ n
deriving DecidableEq

namespace DyBox

/-- `s_B = 2^{-n}`. -/
def side (b : DyBox) : ℝ := (2 : ℝ)⁻¹ ^ b.n

/-- `c_B ∈ 𝔠_n` (DZZ (eq-def-mathfrak-C), l. 307). -/
def center (b : DyBox) : ℂ := ⟨(b.j + 1 / 2) * b.side, (b.k + 1 / 2) * b.side⟩

/-- The closure of the box. -/
def closedBox (b : DyBox) : Set ℂ :=
  {z | b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side ∧
    b.k * b.side ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side}

/-- The root box `𝕍`. -/
def root : DyBox := ⟨0, 0, 0, by norm_num, by norm_num⟩

lemma div_two_pow_lt {n i j : ℕ} (hj : j < 2 ^ n) : j / 2 ^ (n - i) < 2 ^ (min i n) := by
  rcases le_total i n with h | h
  · rw [min_eq_left h, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.add_sub_cancel' h]
    exact hj
  · rw [min_eq_right h, Nat.sub_eq_zero_of_le h, pow_zero, Nat.div_one]
    exact hj

/-- The ancestor of `b` at level `i` (`b` itself if `i ≥ n`). -/
def anc (b : DyBox) (i : ℕ) : DyBox :=
  ⟨min i b.n, b.j / 2 ^ (b.n - i), b.k / 2 ^ (b.n - i), div_two_pow_lt b.hj, div_two_pow_lt b.hk⟩

/-- The column/row index at level `n` of a coordinate `x ∈ [0,1]`. -/
def idx (n : ℕ) (x : ℝ) : ℕ := min ⌊x * 2 ^ n⌋₊ (2 ^ n - 1)

lemma idx_lt (n : ℕ) (x : ℝ) : idx n x < 2 ^ n :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) one_pos)

/-- The level-`n` box containing `v`. -/
def boxAt (n : ℕ) (v : ℂ) : DyBox := ⟨n, idx n v.re, idx n v.im, idx_lt n _, idx_lt n _⟩

/-- `v` lies in the box `b` (half-open convention, see the module docstring). -/
def Mem (v : ℂ) (b : DyBox) : Prop := v ∈ dzzV ∧ boxAt b.n v = b

/-- Neighbouring boxes: distinct, closures meeting in a non-trivial segment (DZZ l. 784–786). -/
def Neighbour (b b' : DyBox) : Prop := b ≠ b' ∧ ¬ (b.closedBox ∩ b'.closedBox).Subsingleton

lemma Neighbour.symm {b b' : DyBox} (h : Neighbour b b') : Neighbour b' b :=
  ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩

end DyBox

open DyBox

/-! ### The δ-partition driven by a box-mass function `m` -/

section Partition

variable (m : DyBox → ℝ) (δ : ℝ)

/-- `b ∈ 𝒱_δ`: `m b < δ²` and every strict ancestor was split (`m ≥ δ²`) (DZZ l. 776–783). -/
def IsCell (b : DyBox) : Prop := m b < δ ^ 2 ∧ ∀ i < b.n, δ ^ 2 ≤ m (b.anc i)

/-- The cell graph of `𝒱_δ` (on all dyadic boxes; only cells have edges). -/
def cellGraph : SimpleGraph DyBox where
  Adj b b' := IsCell m δ b ∧ IsCell m δ b' ∧ Neighbour b b'
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- **`D'_{γ,δ}(u, v)`** (DZZ l. 787–790), counted in cells: `⨅` over cells `b ∋ u`, `b' ∋ v` of
the graph distance plus one. -/
def approxDist (u v : ℂ) : ℕ∞ :=
  ⨅ (b : DyBox) (b' : DyBox) (_ : IsCell m δ b ∧ b.Mem u) (_ : IsCell m δ b' ∧ b'.Mem v),
    (cellGraph m δ).edist b b' + 1

/-- `min_{x ∈ A, y ∈ B} D'(x, y)`. -/
def approxDistSet (A B : Set ℂ) : ℕ∞ := ⨅ x ∈ A, ⨅ y ∈ B, approxDist m δ x y

open Classical in
/-- `s_{v,δ}`, the side of the cell `𝖢_{v,δ}` containing `v` (junk `0` if there is none). -/
def cellSide (v : ℂ) : ℝ :=
  if h : ∃ b, IsCell m δ b ∧ b.Mem v then h.choose.side else 0

end Partition

/-! ### The approximate LQG mass `M_{γ,ε}` -/

/-- `Var η_ε(v) = π ‖K^η_{ε,v}‖²` (deterministic; equals the variance under a white noise). -/
def etaVar (ε : ℝ) (v : ℂ) : ℝ := Real.pi * ‖etaKernelL2 (Ioi (ε ^ 2)) v‖ ^ 2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **DZZ (eq-def-approximate-LQG)**:
`M_{γ,s_B}(B) = s_B² e^{γ η_{s_B}(c_B) − γ²/2 Var η_{s_B}(c_B)}`. -/
def approxLQG (γ : ℝ) (W : WNSpace → Ω → ℝ) (ω : Ω) (b : DyBox) : ℝ :=
  b.side ^ 2 * Real.exp (γ * etaInf W b.side b.center ω - γ ^ 2 / 2 * etaVar b.side b.center)

/-- DZZ's `D'_{γ,δ}(u, v)` for the field `η` of the white noise `W`. -/
def approxLGD (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (u v : ℂ) (ω : Ω) : ℕ∞ :=
  approxDist (approxLQG γ W ω) δ u v

/-- `min_{x ∈ A, y ∈ B} D'_{γ,δ}(x, y)`. -/
def approxLGDSet (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ) (ω : Ω) : ℕ∞ :=
  approxDistSet (approxLQG γ W ω) δ A B

/-! ### ξ-admissible pairs and high probability -/

/-- `𝕍^ξ = {v ∈ 𝕍 : |v − ∂𝕍| ≥ ξ}` (DZZ l. 791). -/
def dzzVXi (ξ : ℝ) : Set ℂ := {v | v ∈ dzzV ∧ ξ ≤ Metric.infDist v (frontier dzzV)}

/-- A single point, or a connected set of diameter at least `δ^ξ` (DZZ l. 793). -/
def IsXiAdmissibleSet (ξ δ : ℝ) (A : Set ℂ) : Prop :=
  (∃ a, A = {a}) ∨ (IsConnected A ∧ δ ^ ξ ≤ Metric.diam A)

/-- **ξ-admissible pairs** `(A_δ, B_δ) ⊆ 𝕍^ξ × 𝕍^ξ`, `δ ∈ (0,1)` (DZZ l. 791–797). -/
structure IsXiAdmissible (ξ : ℝ) (A B : ℝ → Set ℂ) : Prop where
  subset_left : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ dzzVXi ξ
  subset_right : ∀ δ ∈ Ioo (0 : ℝ) 1, B δ ⊆ dzzVXi ξ
  adm_left : ∀ δ ∈ Ioo (0 : ℝ) 1, IsXiAdmissibleSet ξ δ (A δ)
  adm_right : ∀ δ ∈ Ioo (0 : ℝ) 1, IsXiAdmissibleSet ξ δ (B δ)
  dist_ge : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ a ∈ A δ, ∀ b ∈ B δ, ξ ≤ dist a b

/-- Events `E_δ` occur **with high probability** (DZZ l. 288–290): `P(E_δᶜ) ≤ δ^c` for some
`c > 0` and all small `δ > 0`. -/
def HighProb (P : Measure Ω) (E : ℝ → Set Ω) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ ∈ Ioo (0 : ℝ) δ₀, P (E δ)ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- Events occur with **`α`-high probability** (DZZ l. 292–294). -/
def AlphaHighProb (P : Measure Ω) (α : ℝ) (E : ℝ → Set Ω) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, P (E δ)ᶜ ≤ ENNReal.ofReal (δ ^ α)

end DZZ
end LQGMetric
