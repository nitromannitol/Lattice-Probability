/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B3
import Mathlib.Data.ENat.BigOperators

/-!
# DZZ Lemma 5.3, part 1: the deterministic layer (P2-DZZ53E)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.3, l. 2382–2410.
DZZ work on `𝒟 = 𝒟₁ ∩ 𝒟₂`, where (Eq.calD1) bounds the number `d` of pieces,
`log d ≤ (log δ⁻¹)^{0.95} + E log D̃_δ(u,v)`, and (eq-union-bound-distance) bounds every piece,
`log D^{𝕍̃_{u,v}}_{δδ̃}(x_i, x_{i+1}) ≤ E log D̃_{δ̃}(u,v) + 4 (log δ⁻¹)^{0.98}`; the triangle
inequality (eq-triangle-inequality) then gives
`log D̃_{δδ̃}(u,v) ≤ E log D̃_δ + E log D̃_{δ̃} + 5 (log δ⁻¹)^{0.98}` on `𝒟` (l. 2405–2410).

* `lgdDZZ_chain_le`: the triangle inequality along a chain `x₀, …, x_d` (from `lgdDZZ_triangle`, S5L54G1).
* `l53ChainEvent ν u v δ T₁ T₂`: the event `𝒟` in chain form: there are `d ≥ 1` with `d ≤ e^{T₁}`
  and `x₀ = u, …, x_d = v` with every piece finite and `≤ e^{T₂}`.
* `logMinLGD_le_of_mem_l53ChainEvent`: on it, `log D_δ(u,v) ≤ T₁ + T₂` (l. 2405–2410).
* **`dzzLem53Event_of_chain`**: `DZZLem53Event` from `P(𝒟ᶜ) ≤ 2 e^{−(log δ⁻¹)^{0.22}}` with
  `T₁ = E X_k + (k log 2)^{0.95}`, `T₂ = E X_l + 4 (k log 2)^{0.98}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- **(eq-triangle-inequality)** along a chain (DZZ l. 2396–2398). -/
lemma lgdDZZ_chain_le (μ : Measure ℂ) (δ : ℝ) (x : ℕ → ℂ) {d : ℕ} (hd : 1 ≤ d) :
    lgdDZZ μ δ (x 0) (x d) ≤ ∑ i ∈ Finset.range d, lgdDZZ μ δ (x i) (x (i + 1)) := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    exact (lgdDZZ_triangle μ δ _ (x n) _).trans (add_le_add_left ih _)

/-- The relation "`D_δ(x, y)` is finite and at most `e^T`". -/
def lgdLeExp (μ : Measure ℂ) (δ T : ℝ) (x y : ℂ) : Prop :=
  lgdDZZ μ δ x y ≠ ⊤ ∧ ((lgdDZZ μ δ x y).toNat : ℝ) ≤ Real.exp T

lemma lgdLeExp.mono {μ : Measure ℂ} {δ T T' : ℝ} (h : T ≤ T') {x y : ℂ}
    (hxy : lgdLeExp μ δ T x y) : lgdLeExp μ δ T' x y :=
  ⟨hxy.1, hxy.2.trans (Real.exp_le_exp.2 h)⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The event `𝒟 = 𝒟₁ ∩ 𝒟₂` of DZZ l. 2389–2405 in chain form**: a chain `u = x₀, …, x_d = v`
with `d ≤ e^{T₁}` pieces, each of `D_δ`-length at most `e^{T₂}`. -/
def l53ChainEvent (ν : Ω → Measure ℂ) (u v : ℂ) (δ T₁ T₂ : ℝ) : Set Ω :=
  {ω | ∃ d : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ Real.exp T₁ ∧ ∃ x : ℕ → ℂ, x 0 = u ∧ x d = v ∧
    ∀ i < d, lgdLeExp (ν ω) δ T₂ (x i) (x (i + 1))}

omit [MeasurableSpace Ω] in
/-- DZZ l. 2405–2410: on `𝒟`, `log D_δ(u,v) ≤ T₁ + T₂`. -/
lemma logMinLGD_le_of_mem_l53ChainEvent {ν : Ω → Measure ℂ} {u v : ℂ} {δ T₁ T₂ : ℝ}
    (hT : 0 ≤ T₁ + T₂) {ω : Ω} (hω : ω ∈ l53ChainEvent ν u v δ T₁ T₂) :
    logMinLGD (ν ω) δ {u} {v} ≤ T₁ + T₂ := by
  obtain ⟨d, hd1, hdT, x, hx0, hxd, hx⟩ := hω
  unfold logMinLGD
  rw [lgdMinSet_singleton]
  have hchain := lgdDZZ_chain_le (ν ω) δ x hd1
  rw [hx0, hxd] at hchain
  have hfin : ∀ i ∈ Finset.range d, lgdDZZ (ν ω) δ (x i) (x (i + 1)) ≠ ⊤ :=
    fun i hi => (hx i (Finset.mem_range.1 hi)).1
  have hsum_ne : ∑ i ∈ Finset.range d, lgdDZZ (ν ω) δ (x i) (x (i + 1)) ≠ ⊤ :=
    ENat.sum_ne_top.2 hfin
  have hN : (lgdDZZ (ν ω) δ u v).toNat ≤
      ∑ i ∈ Finset.range d, (lgdDZZ (ν ω) δ (x i) (x (i + 1))).toNat := by
    rw [← ENat.toNat_sum hfin]; exact ENat.toNat_le_toNat hchain hsum_ne
  have hNR : ((lgdDZZ (ν ω) δ u v).toNat : ℝ) ≤ d * Real.exp T₂ := by
    have h1 : ((lgdDZZ (ν ω) δ u v).toNat : ℝ) ≤
        ∑ i ∈ Finset.range d, ((lgdDZZ (ν ω) δ (x i) (x (i + 1))).toNat : ℝ) := by
      exact_mod_cast hN
    refine h1.trans ?_
    have := Finset.sum_le_sum (s := Finset.range d)
      (fun i hi => (hx i (Finset.mem_range.1 hi)).2)
    simpa using this
  rcases Nat.eq_zero_or_pos (lgdDZZ (ν ω) δ u v).toNat with h0 | hpos
  · rw [h0]; simpa using hT
  have hpos' : (0 : ℝ) < (lgdDZZ (ν ω) δ u v).toNat := by exact_mod_cast hpos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  calc Real.log ((lgdDZZ (ν ω) δ u v).toNat : ℝ) ≤ Real.log (d * Real.exp T₂) :=
        Real.log_le_log hpos' hNR
    _ = Real.log d + T₂ := by rw [Real.log_mul hd0.ne' (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ T₁ + T₂ := by
        have := Real.log_le_log hd0 hdT
        rw [Real.log_exp] at this; linarith

end DZZ
end LQGMetric
