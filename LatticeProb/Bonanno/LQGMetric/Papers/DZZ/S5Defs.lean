/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Glue
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls0
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32X

/-!
# DZZ §5–§6: boxes, restricted distances, the exponent statements of Lemmas 5.3, 5.4, 6.1, and
their "probability → 1" consequences (P2-DZZ56)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, §5 l. 2252–2304, Appendix l. 2584–2610.

Notation (DZZ l. 2263–2268):
* `sqBox c λ`: the closed box `𝕍_{c,λ}` centred at `c` with side `λ`; `dzzVbar = 𝕍̄`, the box
  concentric with `𝕍` of side `1/20`.
* `tildeBox u v = 𝕍̃_{u,v}`: the closed box centred at `(u+v)/2`, of side `2|u−v|`, with two sides
  parallel to `[u, v]` (coordinates along/perpendicular to `v − u`: `(z − (u+v)/2)·conj(v−u)`
  has real and imaginary parts in `[−|v−u|², |v−u|²]`).
* `D^A_{γ,δ}` (balls *contained in `A`*, l. 2268) is `lgdDZZ (dzzWall A μ)` (decision D97,
  `dzzWall_ball_of_subset`, `dzzWall_ball_of_not_subset`): `D̃_{γ,δ}(u,v) = D^{𝕍̃_{u,v}}`,
  `D̄^{x,λ} = D^{𝕍_{x,λ}}`.

Statements (the measure `μ ω` is `M_γ` or `M_{γ,η}` of the white-noise field; DZZ prove them for
both, and DG use the zero-boundary-GFF version):
* `DZZLem53Exp P μ χ`: the `D̃_{γ,δ,η}` half of **DZZ Lemma 5.3** (l. 2292–2297). (The `D̃'` half
  needs the dyadic partition of the rotated box `𝕍̃_{u,v}`, not defined here; DG use only `D̃`,
  DG:1206.)
* `DZZLem54Exp P μ χ`: **DZZ Lemma 5.4** (l. 2299–2304).
* `DZZLem61Exp P μ α χ`: **DZZ Lemma 6.1** (l. 2584–2590), reading `𝕍̄_u = 𝕍_{u,1/20}`,
  `𝕍̄_{u,α} = 𝕍_{u,α/20}` (the translate of `𝕍̄` to `u` and its `α`-scaling).

Consumers (DG L3.12, L3.20 inputs, DEC-105 N9): `dzz_lem53_upper_whp`, `dzz_lem61_lower_whp`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- The closed box `𝕍_{c,λ}` centred at `c` with side `λ` (DZZ l. 2264). -/
def sqBox (c : ℂ) (l : ℝ) : Set ℂ := {z | |z.re - c.re| ≤ l / 2 ∧ |z.im - c.im| ≤ l / 2}

/-- `𝕍̄`: the box concentric with `𝕍 = [0,1]²` of side `1/20` (DZZ l. 2263). -/
def dzzVbar : Set ℂ := sqBox ⟨1 / 2, 1 / 2⟩ (1 / 20)

/-- `𝕍̃_{u,v}`: the closed box centred at `(u+v)/2`, of side `2|u−v|`, two sides parallel to the
segment `[u,v]` (DZZ l. 2265–2266). -/
def tildeBox (u v : ℂ) : Set ℂ :=
  {z | |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).re| ≤ ‖v - u‖ ^ 2 ∧
    |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).im| ≤ ‖v - u‖ ^ 2}

lemma isClosed_sqBox (c : ℂ) (l : ℝ) : IsClosed (sqBox c l) := by
  show IsClosed ({z : ℂ | |z.re - c.re| ≤ l / 2} ∩ {z : ℂ | |z.im - c.im| ≤ l / 2})
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

lemma isClosed_tildeBox (u v : ℂ) : IsClosed (tildeBox u v) := by
  show IsClosed ({z : ℂ | |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).re| ≤ ‖v - u‖ ^ 2} ∩
    {z : ℂ | |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).im| ≤ ‖v - u‖ ^ 2})
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

lemma lgdMinSet_singleton (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) :
    lgdMinSet μ δ {u} {v} = lgdDZZ μ δ u v := by
  simp [lgdMinSet]

lemma isXiAdmissible_const_singleton {ξ : ℝ} {u v : ℂ} (hu : u ∈ dzzVXi ξ) (hv : v ∈ dzzVXi ξ)
    (huv : ξ ≤ dist u v) : IsXiAdmissible ξ (fun _ => {u}) (fun _ => {v}) where
  subset_left _ _ := singleton_subset_iff.mpr hu
  subset_right _ _ := singleton_subset_iff.mpr hv
  adm_left _ _ := Or.inl ⟨u, rfl⟩
  adm_right _ _ := Or.inl ⟨v, rfl⟩
  dist_ge _ _ a ha b hb := by rw [mem_singleton_iff.mp ha, mem_singleton_iff.mp hb]; exact huv

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **DZZ Lemma 5.3** (`lem-existence-exponent`, l. 2292–2297), the `D̃_{γ,δ,η}` half:
for all `u, v ∈ 𝕍̄`, `E log D̃_δ(u,v) / log δ⁻¹ → χ` as `δ → 0`, where `D̃` uses the balls inside
`𝕍̃_{u,v}`. (DZZ write `u, v ∈ 𝕍̄`; `u ≠ v` is implicit, `𝕍̃_{u,u}` being a point.) -/
def DZZLem53Exp (P : Measure Ω) (μ : Ω → Measure ℂ) (χ : ℝ) : Prop :=
  ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
    Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ {u} {v} ∂P) /
      Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)

/-- **DZZ Lemma 5.4** (`lem-exponent-point-to-boundary`, l. 2299–2304), `λ = 1/20`:
`E log min_{x ∈ ∂𝕍_{u,λ}} D̄^{u,2λ}_δ(u,x) / log δ⁻¹ → χ`. -/
def DZZLem54Exp (P : Measure Ω) (μ : Ω → Measure ℂ) (χ : ℝ) : Prop :=
  ∀ u ∈ dzzVbar,
    Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (sqBox u (1 / 10)) (μ ω)) δ {u}
      (frontier (sqBox u (1 / 20))) ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)

/-- **DZZ Proposition 3.17 + Lemma 5.3 ⇒ DG Lemma 3.12's input** (DG:1206): for `u ≠ v ∈ 𝕍̄`
in `𝕍^ξ` at distance `≥ ξ`, `P[D̃_δ(u,v) > δ^{−χ−ι}] → 0` (DZZ Remark 5.2: Proposition 3.17 for
the tilde distance, i.e. for the walled measure, at pairs inside `𝕍̃_{u,v}^ξ`, DEC-123 §2). -/
theorem dzz_lem53_upper_whp {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ χ : ℝ}
    (hL : DZZLem53Exp P μ χ) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox u v) (μ ω)) (tildeBox u v) ξ)
    (huK : u ∈ kXi (tildeBox u v) ξ) (hvK : v ∈ kXi (tildeBox u v) ξ)
    (huξ : u ∈ dzzVXi ξ) (hvξ : v ∈ dzzVXi ξ) (hd : ξ ≤ dist u v)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, lgdDZZ (dzzWall (tildeBox u v) (μ ω)) δ u v < ⊤)
    {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | ¬ ((lgdDZZ (dzzWall (tildeBox u v) (μ ω)) δ u v : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}) (𝓝[>] 0) (𝓝 0) := by
  have := dzz_lgd_upper_whpIn h317 (isXiAdmissible_const_singleton huξ hvξ hd)
    (fun _ _ => ⟨singleton_subset_iff.mpr huK, singleton_subset_iff.mpr hvK⟩) (hL u hu v hv huv)
    (by simpa only [lgdMinSet_singleton] using hfin) hι
  simpa only [lgdMinSet_singleton] using this

end DZZ
end LQGMetric
