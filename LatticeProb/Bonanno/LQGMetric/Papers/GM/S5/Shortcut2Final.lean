/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.ShortcutDist

/-!
# GM §5.5: the final step of the proof of Lemma 5.11 (l. 3513–3550)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

`gm_L5_11_final`: GM's proof of Lemma 5.11 from Lemma 5.15 (l. 3513–3550), verbatim, for two
metrics `d = D_{h−φ}`, `d' = D̃_{h−φ}` with `c_* d ≤ d' ≤ C_* d`: from (5.43)
(`d'(u, p; U), d'(v, q; U) ≤ η d'(u, v)`) and (5.45) (`d'(u, v) ≤ c_1' d(u, v)`) one gets (5.44)
`d(u,v) ≤ (1 − 2c_*⁻¹C_*η)⁻¹ d(p,q)` and then (5.46) `d'(p, q) ≤ c_2' d(p, q)`.

GM's choice (5.15) of `η` ("small", l. 2929) makes the denominator `1 − 2c_*⁻¹C_*η` of (5.15)
positive; `EtaChoice` (Defs.lean) does not record this, so it is the explicit hypothesis `hpos`
(reported to the orchestrator: `EtaChoice` should contain `2 * cs⁻¹ * Cs * η < 1`; without it,
`EtaChoice` holds for every large `η < 1`, e.g. `C_*/c_* = 10`, `η = 1/2`, and (5.46) fails).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- a bound on an internal distance bounds the distance -/
lemma le_of_internal_le_m2m2 (D : ContMetric) {U : Set ℂ} {a b : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : D.internal U a b ≤ ENNReal.ofReal B) : D.1 (a, b) ≤ B :=
  (ENNReal.ofReal_le_ofReal_iff hB).1 ((ofReal_le_internal_m2m D U a b).trans h)

/-- **GM l. 3513–3550** (end of the proof of Lemma 5.11): (5.43) and (5.45) give (5.46). -/
theorem gm_L5_11_final {d d' : ContMetric} {cs Cs c₁ c₂ η : ℝ} (hcs : 0 < cs) (hc₁ : cs < c₁)
    (hη : EtaChoice cs Cs c₁ c₂ η) (hpos : 2 * cs⁻¹ * Cs * η < 1)
    (hbl : ∀ x y : ℂ, cs * d.1 (x, y) ≤ d'.1 (x, y) ∧ d'.1 (x, y) ≤ Cs * d.1 (x, y))
    {U : Set ℂ} {p q u v : ℂ}
    (hpu : d'.internal U u p ≤ ENNReal.ofReal (η * d'.1 (u, v)))
    (hqv : d'.internal U v q ≤ ENNReal.ofReal (η * d'.1 (u, v)))
    (huv : d'.1 (u, v) ≤ c₁ * d.1 (u, v)) :
    d'.1 (p, q) ≤ c₂ * d.1 (p, q) := by
  obtain ⟨hη0, -, hfrac, -⟩ := hη
  have hd'uv := nonneg_m2m d' u v
  have hB0 : 0 ≤ η * d'.1 (u, v) := mul_nonneg hη0.le hd'uv
  have h1 := le_of_internal_le_m2m2 d' hB0 hpu
  have h2 := le_of_internal_le_m2m2 d' hB0 hqv
  set A := d.1 (u, v)
  set B := d.1 (p, q)
  set k := 2 * cs⁻¹ * Cs * η
  -- `d(u, p), d(v, q) ≤ c_*⁻¹ C_* η d(u, v)` ((5.43'))
  have hCA : d'.1 (u, v) ≤ Cs * A := (hbl u v).2
  have hk1 : ∀ a b : ℂ, d'.1 (a, b) ≤ η * d'.1 (u, v) → d.1 (a, b) ≤ k / 2 * A := by
    intro a b hab
    have h3 : cs * d.1 (a, b) ≤ cs * (k / 2 * A) := by
      have : cs * (k / 2 * A) = Cs * η * A := by simp only [k]; field_simp
      rw [this]
      calc cs * d.1 (a, b) ≤ d'.1 (a, b) := (hbl a b).1
        _ ≤ η * d'.1 (u, v) := hab
        _ ≤ η * (Cs * A) := mul_le_mul_of_nonneg_left hCA hη0.le
        _ = Cs * η * A := by ring
    exact le_of_mul_le_mul_left h3 hcs
  have hup := hk1 u p h1
  have hvq := hk1 v q h2
  -- (5.44)
  have hA : (1 - k) * A ≤ B := by
    have t1 := dist_triangle_m2m d u p v
    have t2 := dist_triangle_m2m d p q v
    have t3 := dist_comm_m2m d u p
    have t4 := dist_comm_m2m d q v
    have t5 := dist_comm_m2m d v q
    nlinarith
  -- (5.46)
  have hpq : d'.1 (p, q) ≤ (1 + 2 * η) * d'.1 (u, v) := by
    have t1 := dist_triangle_m2m d' p u q
    have t2 := dist_triangle_m2m d' u v q
    have t3 := dist_comm_m2m d' u p
    have t4 := dist_comm_m2m d' v q
    linarith
  have hden : 0 < 1 - k := by linarith
  have hc₁' : 0 ≤ c₁ * (1 + 2 * η) / (1 - k) :=
    div_nonneg (mul_nonneg (by linarith [hc₁]) (by linarith)) hden.le
  calc d'.1 (p, q) ≤ (1 + 2 * η) * d'.1 (u, v) := hpq
    _ ≤ (1 + 2 * η) * (c₁ * A) := mul_le_mul_of_nonneg_left huv (by linarith)
    _ = c₁ * (1 + 2 * η) / (1 - k) * ((1 - k) * A) := by field_simp
    _ ≤ c₁ * (1 + 2 * η) / (1 - k) * B := mul_le_mul_of_nonneg_left hA hc₁'
    _ ≤ c₂ * B := mul_le_mul_of_nonneg_right hfrac.le (nonneg_m2m d p q)

end LQGMetric.GM
