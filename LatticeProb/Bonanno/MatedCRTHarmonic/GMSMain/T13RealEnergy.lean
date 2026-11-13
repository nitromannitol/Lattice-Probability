/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13RealEnergy at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13Real

/-!
# [18] Theorem 1.3 (repaired) and Theorem 3.2 at every real mesh, from named inputs

Source: [18] Theorem 1.3 (with the boundary condition `area(B_r(∂D)) ≤ C r`) and Theorem 3.2
((i)): for `C ≥ 1` and `(D, f) ∈ 𝒞_C(ε^β)` (`D ⊂ B_ρ(0)` open, `area(B_r(∂D)) ≤ C r`,
`C`-bounded convexity, `∇f` `ε^{-β}`-Lipschitz, `‖f‖_∞, ‖∇f‖_∞ ≤ ε^{-β}`), with probability `1 − O_ε(ε^α)`,
`Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + ε^α`, the rate depending only on `C, ρ, γ`.

Both follow from the deterministic bound `t13_energy_le_on_event_R` on the event of Lemma 2.7 on `B_{ρ₁}(0)` and of
Proposition 2.10 for `(D, |∇f|²)`, `(D, 1)` and `(B_{ρ₁}(0), t13Layer D ε^{β'})`; the inputs are the real-mesh
bad events `EpsALemma27Bad`, `EpsAProp210Bad` (named hypotheses `h27`, `h210`).

* `T13RealEnergyGood ε b c D f A t` — an embedding of `MatedCRT.graph ε b` with the cells of `c` exists, and for EVERY
  such embedding and every `f_ε` with (1.6), harmonic on `V(D) \ V(∂D)`: `Energy(f_ε) ≤ A Energy(f; D) + t`;
* `t13r_err_le` — the elementary bound of the Theorem 3.2 error term by `K M² s`;
* **`t13r_theorem13_of_inputs`** — repaired Theorem 1.3 (`t = 0`), `A = 3C²A₂ + 1`, rate `C_f` depending on `f`;
* **`t13r_theorem32_of_inputs`** — Theorem 3.2, `A = 3C²A₂`, tolerance `ε^{α_t}`, rate uniform over `𝒞_C(ε^β)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3

/-- **The events (1.7) / (3.10) at mesh `ε`** for the mated-CRT map of a Brownian path `b` with the cells of a curve
`c`: an embedding with the curve cells exists, and for EVERY such embedding `H` and every `f_ε` with the boundary data
(1.6), discrete harmonic on `V(D) \ V(∂D)`: `Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + t`. -/
def T13RealEnergyGood (ε : ℝ) (b : MatedCRT.Path2) (c : C(ℝ, ℂ)) (Dom : Set ℂ) (f : ℂ → ℝ) (A t : ℝ) : Prop :=
  (∃ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
      ∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
    ∀ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
      ∀ fε : ℤ → ℝ, IsGMSDirichletSolution H Dom f fε →
        ENNReal.ofReal (energy (MatedCRT.graph ε b h) (vFin H Dom) fε) ≤
          ENNReal.ofReal A * eucEnergy f Dom + ENNReal.ofReal t

/-- The Proposition 2.10 failure event shrinks as the tolerance grows. -/
theorem t13r_prop210Bad_anti_tol {Ω : Type*} {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ε : ℝ}
    {V : Set ℂ} {f : ℂ → ℝ} {A t t' : ℝ} (htt' : t ≤ t') :
    EpsAProp210Bad bm η ε V f A t' ⊆ EpsAProp210Bad bm η ε V f A t := by
  intro ω hω hgood
  exact hω ⟨hgood.1, fun hlf H hcell => BundleSec4.bundle_prop210Bound_mono_tol H htt' (hgood.2 hlf H hcell)⟩

/-- The Theorem 3.2 error term (`G = Λ = M`) is at most `K M² s` when `η, δ, w ≤ s ≤ 1`, `M ≥ 1`, `C ≥ 1`. -/
theorem t13r_err_le {C A₂ M η δ w s : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A₂) (hM : 1 ≤ M) (hη0 : 0 ≤ η) (hηs : η ≤ s)
    (hδ0 : 0 ≤ δ) (hδs : δ ≤ s) (hw0 : 0 ≤ w) (hws : w ≤ s) (hs1 : s ≤ 1) :
    3 * C ^ 2 * (η + 2 * M * M * δ * (A₂ * 4 + η) + M ^ 2 * (A₂ * (C * (2 * w)) + η)) +
      24 * C ^ 2 * (M * (1 + C)) ^ 2 * δ ^ 2 * ((A₂ * 4 + η) + (A₂ * (C * (2 * w)) + η)) ≤
    (3 * C ^ 2 * (2 + 2 * (A₂ * 4 + 1) + 2 * A₂ * C) +
      24 * C ^ 2 * (1 + C) ^ 2 * (A₂ * 4 + 2 + 2 * A₂ * C)) * (M ^ 2 * s) := by
  have hs0 : 0 ≤ s := hη0.trans hηs
  have hM0 : 0 ≤ M := by linarith
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := by linarith
  have hη1 : η ≤ 1 := hηs.trans hs1
  have hw1 : w ≤ 1 := hws.trans hs1
  have hδ1 : δ ≤ 1 := hδs.trans hs1
  have hMs : 0 ≤ M ^ 2 * s := by positivity
  -- the four terms
  have t1 : η ≤ M ^ 2 * s := by nlinarith
  have t2 : 2 * M * M * δ * (A₂ * 4 + η) ≤ 2 * (A₂ * 4 + 1) * (M ^ 2 * s) := by
    have h1 : δ * (A₂ * 4 + η) ≤ s * (A₂ * 4 + 1) :=
      mul_le_mul hδs (by linarith) (by positivity) hs0
    have h2 : 0 ≤ 2 * M * M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have t3 : M ^ 2 * (A₂ * (C * (2 * w)) + η) ≤ (2 * A₂ * C + 1) * (M ^ 2 * s) := by
    have h1 : A₂ * (C * (2 * w)) + η ≤ (2 * A₂ * C + 1) * s := by
      have : A₂ * (C * (2 * w)) ≤ 2 * A₂ * C * s := by
        have := mul_le_mul_of_nonneg_left hws (by positivity : (0 : ℝ) ≤ 2 * A₂ * C)
        nlinarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ M ^ 2)]
  have t4 : (M * (1 + C)) ^ 2 * δ ^ 2 * ((A₂ * 4 + η) + (A₂ * (C * (2 * w)) + η)) ≤
      (1 + C) ^ 2 * (A₂ * 4 + 2 + 2 * A₂ * C) * (M ^ 2 * s) := by
    have hδ2 : δ ^ 2 ≤ s := by nlinarith
    have hbr : (A₂ * 4 + η) + (A₂ * (C * (2 * w)) + η) ≤ A₂ * 4 + 2 + 2 * A₂ * C := by
      have : A₂ * (C * (2 * w)) ≤ 2 * A₂ * C := by
        have := mul_le_mul_of_nonneg_left hw1 (by positivity : (0 : ℝ) ≤ 2 * A₂ * C)
        nlinarith
      linarith
    have hbr0 : 0 ≤ (A₂ * 4 + η) + (A₂ * (C * (2 * w)) + η) := by positivity
    calc (M * (1 + C)) ^ 2 * δ ^ 2 * ((A₂ * 4 + η) + (A₂ * (C * (2 * w)) + η))
        = (1 + C) ^ 2 * (M ^ 2 * δ ^ 2) * ((A₂ * 4 + η) + (A₂ * (C * (2 * w)) + η)) := by ring
      _ ≤ (1 + C) ^ 2 * (M ^ 2 * s) * (A₂ * 4 + 2 + 2 * A₂ * C) := by
          gcongr
      _ = (1 + C) ^ 2 * (A₂ * 4 + 2 + 2 * A₂ * C) * (M ^ 2 * s) := by ring
  have hC2 : 0 ≤ 3 * C ^ 2 := by positivity
  have h24 : 0 ≤ 24 * C ^ 2 := by positivity
  have hsum3 : η + 2 * M * M * δ * (A₂ * 4 + η) + M ^ 2 * (A₂ * (C * (2 * w)) + η) ≤
      (2 + 2 * (A₂ * 4 + 1) + 2 * A₂ * C) * (M ^ 2 * s) := by nlinarith
  have hA := mul_le_mul_of_nonneg_left hsum3 hC2
  have hB := mul_le_mul_of_nonneg_left t4 h24
  nlinarith [hA, hB]

end MatedCRTHarmonic.GMSMain
