/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.Prop61Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Thm19

/-!
# GM Proposition 6.1, deterministic steps 2–4 (task P2-M2O)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 6.1, l. 3611–3643.

* `le_upperRatio_mul`: `D̃_g ≤ C_*(g) D_g` everywhere (definition (1.21), with bi-Lipschitz
  bounds so that `C_*` is a genuine supremum);
* `away_sep` (GM (6.4) `eqn-away-sep`, l. 3617–3624): along a `D_g`-geodesic `P` from `𝕫` to `𝕨`
  with times `s < t` such that `D̃(P(s),P(t)) ≤ c₂' D(P(s),P(t))`,
  `D̃(𝕫,𝕨) ≤ C_* D(𝕫,𝕨) − (C_* − c₂') D(P(s),P(t))`. GM write the `D̃`-length of `P|_{[0,s]}`;
  we use the triangle inequality `D̃(𝕫,𝕨) ≤ D̃(𝕫,P(s)) + D̃(P(s),P(t)) + D̃(P(t),𝕨)` and
  `D̃ ≤ C_* D` pointwise, which is the same bound.
* `away_transfer` (GM (6.5)–(6.7), l. 3628–3643): the algebra of Steps 3–4: an error `e` for `D`
  and `e'` for `D̃` between a mesh pair and `(z,w)`, a gap `A`, and `D(z,w) ≤ M`, give
  `D̃(z,w) ≤ (C_* − A/(2M)) D(z,w)` once `C_* e + e' ≤ A/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `D̃_g ≤ C_*(g) D_g` at every pair of points (GM (1.21)) -/
theorem le_upperRatio_mul {D D' : DistC → ContMetric} {g : DistC} {K : ℝ}
    (hb : BiLip (D g) (D' g) K) (u v : ℂ) :
    (D' g).1 (u, v) ≤ upperRatio D D' g * (D g).1 (u, v) := by
  by_cases huv : u = v
  · subst huv; rw [(D' g).2.self_eq_zero, (D g).2.self_eq_zero, mul_zero]
  have hpos := dist_pos_of_ne (D g) huv
  have := le_ciSup (f := fun p : {p : ℂ × ℂ // p.1 ≠ p.2} => (D' g).1 p.1 / (D g).1 p.1)
    (bddAbove_ratio hb) ⟨(u, v), huv⟩
  exact (div_le_iff₀ hpos).1 this

/-- **GM (6.4)** (`eqn-away-sep`, l. 3617–3624), deterministic form -/
theorem away_sep {d d' : ContMetric} {a b : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 d a b η)
    {Cs c₂ : ℝ} (hup : ∀ u v, d'.1 (u, v) ≤ Cs * d.1 (u, v)) {s t : unitInterval}
    (hst : s ≤ t) (hc : d'.1 (η s, η t) ≤ c₂ * d.1 (η s, η t)) :
    d'.1 (a, b) ≤ Cs * d.1 (a, b) - (Cs - c₂) * d.1 (η s, η t) := by
  obtain ⟨h0, h1, hd⟩ := hη
  set L := d.1 (a, b)
  have e1 : d.1 (a, η s) = (s : ℝ) * L := by
    have := hd 0 s; rw [h0] at this; rw [this]; simp [abs_of_nonneg s.2.1]
  have e2 : d.1 (η s, η t) = ((t : ℝ) - s) * L := by
    rw [hd s t, abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ t from hst))]
  have e3 : d.1 (η t, b) = (1 - (t : ℝ)) * L := by
    have := hd t 1; rw [h1] at this; rw [this]
    simp [abs_of_nonneg (sub_nonneg.2 t.2.2)]
  have t1 := d'.2.triangle a (η s) b
  have t2 := d'.2.triangle (η s) (η t) b
  have u1 := hup a (η s)
  have u2 := hup (η t) b
  rw [e1] at u1; rw [e3] at u2; rw [e2] at hc ⊢
  nlinarith

/-- **GM (6.5)–(6.7)** (l. 3628–3643), the algebra of Steps 3–4 -/
theorem away_transfer {Cs A M e e' x x' y y' : ℝ} (hCs : 0 ≤ Cs) (hM : 0 < M)
    (hsep : y' ≤ Cs * y - A) (hy : |y - x| ≤ e) (hy' : |y' - x'| ≤ e')
    (herr : Cs * e + e' ≤ A / 2) (hxM : x ≤ M) :
    x' ≤ (Cs - A / (2 * M)) * x := by
  have a1 := (abs_le.1 hy).2
  have a2 := (abs_le.1 hy').1
  have a3 : Cs * y ≤ Cs * (x + e) := mul_le_mul_of_nonneg_left (by linarith) hCs
  have hA : 0 ≤ A := by
    have : 0 ≤ e := (abs_nonneg _).trans hy
    have : 0 ≤ e' := (abs_nonneg _).trans hy'
    nlinarith
  have a4 : A / (2 * M) * x ≤ A / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

/-- the grid `s ℤ²` -/
def gridPts (s : ℝ) : Set ℂ := {a | ∃ m : ℤ × ℤ, a = ((s : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)}

/-- **GM Prop 6.1, Step 1, first claim** (l. 3590–3599, display (6.1) `eqn-away-from-max-times`):
GM's stated consequence of Theorem 4.2 and Proposition 4.3 (with `ρ⁻¹𝕣`, `U = B_2(0)`,
`ℓ = ρβ̄`). Still open (see handoff/P2-M2O.md: as stated in Lean, `T4_2` does not give
`𝕫, 𝕨 ∉ B_{λ₄r}(z)`, which `P4_3` needs). -/
def P6_1Step1 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → cs < Cs →
  ∃ c'' c₂ bb ρ ν : ℝ, cs < c'' ∧ c₂ < Cs ∧ bb ∈ Ioo (0 : ℝ) 1 ∧ ρ ∈ Ioo (0 : ℝ) 1 ∧ 0 < ν ∧
  ∀ β ∈ Ioo (0 : ℝ) 1, ∀ βb ∈ Ioo (0 : ℝ) 1, ∀ q : ℝ, 0 < q → ∀ η : ℝ, 0 < η →
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : ℝ, 0 < R →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ENNReal.ofReal β ≤ P (h ⁻¹' GLow D D' R c'' β) →
    ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    P {ω | ∀ a b : ℂ, a ∈ gridPts (ε ^ q * ρ⁻¹ * R) → b ∈ gridPts (ε ^ q * ρ⁻¹ * R) →
      a ∈ Metric.ball (0 : ℂ) (2 * R) → b ∈ Metric.ball (0 : ℂ) (2 * R) → βb * R ≤ ‖a - b‖ →
      ∃ P' : C(unitInterval, ℂ), IsGeod01 (D (h ω)) a b P' ∧ ∃ s t : unitInterval, s < t ∧
        bb * ε ^ (1 + ν) * ρ⁻¹ * R ≤ ‖P' s - P' t‖ ∧
        (D' (h ω)).1 (P' s, P' t) ≤ c₂ * (D (h ω)).1 (P' s, P' t)}ᶜ ≤ ENNReal.ofReal η

end LQGMetric.GM
