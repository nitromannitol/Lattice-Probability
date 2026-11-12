/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_6Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Cross
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.SetDist

/-!
# LM Theorem 1.6 from LM Lemma 4.2 (task P2-LM16)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), §4, proof of Theorem 1.6 (`thm-bilip`), l. 828–882.

* `lmGoodE D D' C w r`: the event `E_r(w)` of LM (4.1) (l. 780–782).
* `LMLem4_2 p`: LM Lemma 4.2 (`lem-good-radius-all`, l. 820–826), for `U = ℂ`, as an open
  statement: with probability tending to 1 as `ε → 0`, every `z ∈ K` lies in some `B_{r/2}(w)`
  with `r ∈ [ε², ε] ∩ {2^{-k}ε}`, `w ∈ (¼ε²ℤ²) ∩ B_ε(K)` and `E_r(w)` occurring.
* `lmThm1_6_of`: `LMLem4_2 p` for some `p ∈ (0,1)` implies `Blueprint.LMThm1_6`, following
  LM l. 828–882: a near-`D`-geodesic path `P` (l. 838), the chaining step `lm_chain_det`
  (l. 844–880, file `T1_6Cross`), then `ε → 0`, `δ → 0` (l. 881–882), and continuity to pass
  from fixed `z₁, z₂` to all pairs (l. 832–834, via a countable dense set instead of `ℚ²`).

Departure: LM choose the path `P` "in a measurable manner" and a compact `K` with
`P[P ⊂ K] ≥ 1 − δ` (l. 838–840). We avoid the measurable selection: the bad event is covered by
countably many sets (indexed by `δ = 1/(n+1)`, a radius `R ∈ ℕ` with `P ⊂ cl B_R(0)`, and a
continuity modulus of `D̃` at `z₁, z₂`), each of outer measure 0.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- the event `E_r(w)` of LM (4.1) (l. 780–782) -/
def lmGoodE (D D' : ContMetric) (C : ℝ) (w : ℂ) (r : ℝ) : Prop :=
  internalDiam D' (sphere w r) (annulus w (r / 2) (2 * r)) ≤
    ENNReal.ofReal C * setDist D (sphere w (r / 2)) (sphere w r)

/-- the event `F^ε` of LM Lemma 4.2 (l. 822–823) -/
def lmCoverE (D D' : ContMetric) (C ε : ℝ) (K : Set ℂ) : Prop :=
  ∀ z ∈ K, ∃ k : ℕ, ∃ w : ℂ, ε ^ 2 ≤ (2 : ℝ) ^ (-(k : ℤ)) * ε ∧ (2 : ℝ) ^ (-(k : ℤ)) * ε ≤ ε ∧
    (∃ m n : ℤ, w = ((ε ^ 2 / 4 : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) ∧
    infDist w K < ε ∧ ‖z - w‖ < (2 : ℝ) ^ (-(k : ℤ)) * ε / 2 ∧
    lmGoodE D D' C w ((2 : ℝ) ^ (-(k : ℤ)) * ε)

/-- **LM Lemma 4.2** (`lem-good-radius-all`, l. 820–826), `U = ℂ`, with the universal constant
`p`: if (1.3) holds with this `p` (for every compact set, as in Theorem 1.6), then for every
compact `K`, `P[F^ε] → 1` as `ε → 0`. -/
def LMLem4_2 (p : ℝ) : Prop :=
  ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (D D' : Ω → ContMetric), IsNormalizedWPGFF h P → IsXiAdditive2 ξ P h D D' →
    ∀ C : ℝ, 0 < C →
    (∀ K : Set ℂ, IsCompact K → ∃ rK : ℝ, 0 < rK ∧ ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) rK,
      ENNReal.ofReal p ≤ P {ω | internalDiam (D' ω) (Metric.sphere z r) (annulus z (r / 2) (2 * r))
        ≤ ENNReal.ofReal C * setDist (D ω) (Metric.sphere z (r / 2)) (Metric.sphere z r)}) →
    ∀ K : Set ℂ, IsCompact K →
      Tendsto (fun ε => P {ω | ¬ lmCoverE (D ω) (D' ω) C ε K}) (𝓝[>] 0) (𝓝 0)

/-- LM (4.3), first inequality (l. 852–856): on `E_r(w)`, `D̃(u,v) ≤ C D(q₁,q₂)` for
`u, v ∈ ∂B_r(w)`, `q₁ ∈ ∂B_{r/2}(w)`, `q₂ ∈ ∂B_r(w)`. -/
theorem lmGoodE_bound {D D' : ContMetric} {C : ℝ} (hC : 0 ≤ C) {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hE : lmGoodE D D' C w r) {q₁ q₂ : ℂ} (hq₁ : q₁ ∈ sphere w (r / 2)) (hq₂ : q₂ ∈ sphere w r)
    {u v : ℂ} (hu : u ∈ sphere w r) (hv : v ∈ sphere w r) :
    D'.1 (u, v) ≤ C * D.1 (q₁, q₂) := by
  have h1 : ENNReal.ofReal (D'.1 (u, v)) ≤ D'.internal (annulus w (r / 2) (2 * r)) u v :=
    (edist_dist (D'.pt u) (D'.pt v)).symm.le.trans
      (MetricGeometry.edist_le_internalEDist (X := D'.Space) _ _ _)
  have h2 : D'.internal (annulus w (r / 2) (2 * r)) u v ≤
      internalDiam D' (sphere w r) (annulus w (r / 2) (2 * r)) :=
    le_iSup₂_of_le u hu (le_iSup₂_of_le v hv le_rfl)
  have h3 : setDist D (sphere w (r / 2)) (sphere w r) ≤ ENNReal.ofReal (D.1 (q₁, q₂)) :=
    (MetricGeometry.setEDist_le_edist (mem_image_of_mem D.pt hq₁)
      (mem_image_of_mem D.pt hq₂)).trans (edist_dist (D.pt q₁) (D.pt q₂)).le
  have h4 := (h1.trans h2).trans (hE.trans (mul_le_mul_of_nonneg_left h3 (zero_le)))
  rw [← ENNReal.ofReal_mul hC] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC
    (dist_nonneg : 0 ≤ dist (D.pt q₁) (D.pt q₂)))).1 h4

end LQGMetric.LM
