/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes58Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes58Indep

/-!
# GM Lemma 5.8: the deterministic linking geometry, as a statement (task P2-M2L3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, the deterministic parts of Steps 1–3 (l. 3068–3071, 3079–3092, 3110–3126).

`L58Geom` packages, for `ρ = δ/(500 n_*)` (GM l. 3068) and any `ε₁ ∈ (0, 1/100)`:
* the points `𝒵 ⊂ ∂B_r(0)` (GM l. 3069), pairwise at distance `≥ 8ρr` (the balls `B_{4ρr}(z)` are
  disjoint, l. 3071), and the "at most `4πδ⁻¹`" arcs (l. 3076–3077), each containing at least `n_*`
  points of `𝒵` (here as index sets `a ∈ A`, `#A · δ ≤ 100`);
* for every family of tubes `V_z` with the properties of GM Lemma 5.6 at radius `ρr` (`TubeProps`),
  the tubes `U_r^{x,y}` of (5.24) (l. 3087–3091) with their properties, and, for every `x, y` with
  `|x − y| ≥ δr`, an arc `a ∈ A` such that for every `z ∈ a`: `V_z ⊆ U_r^{x,y}`, `O_u` is the same
  in `U_r^{x,y}` and in `V_z` ((5.25), l. 3119), and condition 2 for `V_z` (with `z ∓ 2ρr`) implies
  condition 2 for `U_r^{x,y}` (with `x`, resp. `y`) (l. 3120–3123), each with GM's disconnection
  clause (decision D77: `z ± 2ρr` outside the component of `z ∓ 2ρr` in `V_z ∖ O_u` gives `y`,
  resp. `x`, outside the component of `x`, resp. `y`, in `U_r^{x,y} ∖ O_u`), for every `u ∈ V_z` with
  `|u − z| < 3ρr/2` (D69: condition (2) is read robustly, `SepNear`, so the transfer is needed
  on a neighbourhood of GM's `u ∈ cl B_{ρr}(z)`; GM's argument applies verbatim).
* (T5), decision D83 (c): `U_r^{x,y}` is attached locally at `x` and `y`.
* D69: the tubes are made of squares meeting `cl B_{2ρr}(z)`, resp. the closed annulus
  `cl 𝔸_{r/2,2r}(0)` (with GM's open sets `z − 2ρr ∉ V_z`, resp. `x ∉ U_r^{x,y}`, at grid corners).

This is the planar-geometry node of Lemma 5.8 (own statement following GM's argument), proved in
`l58Geom` (`Geom58T5`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the deterministic properties of the tube `V_R(z)` of GM Lemma 5.6 (side `ε₁R`) -/
def TubeProps (ε₁ R : ℝ) (z : ℂ) (V : Set ℂ) : Prop :=
  IsOpen V ∧ IsConnected V ∧ V ⊆ ball z ((2 + 2 * ε₁) * R) ∧
    IsSquareTube V (ε₁ * R) (closedBall z (2 * R)) ∧
    z - 2 * R ∈ V ∧ z + 2 * R ∈ V

/-- **the deterministic part of GM Lemma 5.8**; see the module docstring -/
def L58Geom : Prop := ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ, 0 < n → ∀ ε₁ ∈ Ioo (0 : ℝ) (1 / 100),
  ∀ r : ℝ, 0 < r → ∃ (Z : Finset ℂ) (A : Finset (Finset ℂ)), (A.card : ℝ) * δ ≤ 100 ∧
    (∀ a ∈ A, a ⊆ Z ∧ n ≤ a.card) ∧ (∀ z ∈ Z, ‖z‖ = r) ∧
    (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 8 * (δ / (500 * n) * r) ≤ ‖z - w‖) ∧
  ∀ V : ℂ → Set ℂ, (∀ z ∈ Z, TubeProps ε₁ (δ / (500 * n) * r) z (V z)) →
  ∃ U : ℂ → ℂ → Set ℂ,
    (∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
      IsOpen (U x y) ∧ IsConnected (U x y) ∧ U x y ⊆ ball 0 (3 * r) ∧
      IsSquareTube (U x y) (ε₁ * (δ / (500 * n)) * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} ∧
      x ∈ U x y ∧ y ∈ U x y ∧
      -- (T5), decision D83 (c)
      U x y ∩ ball x (4 * (ε₁ * (δ / (500 * n))) * r) ⊆
        connectedComponentIn (U x y ∩ ball x (5 * (ε₁ * (δ / (500 * n))) * r)) x ∧
      U x y ∩ ball y (4 * (ε₁ * (δ / (500 * n))) * r) ⊆
        connectedComponentIn (U x y ∩ ball y (5 * (ε₁ * (δ / (500 * n))) * r)) y) ∧
    (∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
      ∃ a ∈ A, ∀ z ∈ a, V z ⊆ U x y ∧ ∀ u ∈ V z ∩ ball z (3 / 2 * (δ / (500 * n) * r)),
        nearComp (U x y) (20 * (ε₁ * (δ / (500 * n))) * r) u =
          nearComp (V z) (20 * ε₁ * (δ / (500 * n) * r)) u ∧
        (SepFrom (V z) (nearComp (V z) (20 * ε₁ * (δ / (500 * n) * r)) u)
            (z - 2 * ((δ / (500 * n) * r : ℝ) : ℂ)) (ε₁ * (δ / (500 * n) * r)) ∧
            z + 2 * ((δ / (500 * n) * r : ℝ) : ℂ) ∉
              connectedComponentIn (V z \ nearComp (V z) (20 * ε₁ * (δ / (500 * n) * r)) u)
                (z - 2 * ((δ / (500 * n) * r : ℝ) : ℂ)) →
          SepFrom (U x y) (nearComp (U x y) (20 * (ε₁ * (δ / (500 * n))) * r) u) x
            (ε₁ * (δ / (500 * n)) * r) ∧
            y ∉ connectedComponentIn
              (U x y \ nearComp (U x y) (20 * (ε₁ * (δ / (500 * n))) * r) u) x) ∧
        (SepFrom (V z) (nearComp (V z) (20 * ε₁ * (δ / (500 * n) * r)) u)
            (z + 2 * ((δ / (500 * n) * r : ℝ) : ℂ)) (ε₁ * (δ / (500 * n) * r)) ∧
            z - 2 * ((δ / (500 * n) * r : ℝ) : ℂ) ∉
              connectedComponentIn (V z \ nearComp (V z) (20 * ε₁ * (δ / (500 * n) * r)) u)
                (z + 2 * ((δ / (500 * n) * r : ℝ) : ℂ)) →
          SepFrom (U x y) (nearComp (U x y) (20 * (ε₁ * (δ / (500 * n))) * r) u) y
            (ε₁ * (δ / (500 * n)) * r) ∧
            x ∉ connectedComponentIn
              (U x y \ nearComp (U x y) (20 * (ε₁ * (δ / (500 * n))) * r) u) y))

end LQGMetric.GM
