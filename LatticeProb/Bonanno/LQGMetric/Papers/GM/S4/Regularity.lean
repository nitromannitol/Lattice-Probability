/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Regularity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

/-!
# GM §4.3: the global regularity event `ℰ_𝕣` (WP-M2h)

Source: Gwynne–Miller, *Existence and uniqueness of the LQG metric for γ ∈ (0,2)*,
arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex` (GM), §4.3 "Global regularity
event", l. 1940–1990. Inventory: `blueprint/GM_B.md` rows GM.Def-ℰ, GM.S4.4 (Remark 4.10),
GM.L4.11, GM.S4.9; work package WP-M2h (`blueprint/M2.md` row 11).

* `regEvent` is `ℰ_𝕣 = ℰ_𝕣(a, ν, ℓ, U, V)` (GM l. 1950–1970): the intersection of the seven
  conditions `regC1 … regC7`. Conditions 1–6 are GM's conditions 1–6; condition 7 is the event
  `⋂_{𝕫 ∈ 𝕣U} ℰ^𝕫_{ℓ𝕣}(a)` (`confReg` at centre `𝕫`, radius `ℓ𝕣`), added by the proposed deviation
  **DV-B4**: GM's Remark 4.10 (l. 1975–1977) is not literally implied by conditions 2, 3, 6 (the
  normalizations `𝔠_𝕣e^{ξh_𝕣(0)}` vs `𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)}` and the radii `ρ_{𝕣,ε}` vs `ρ_{ℓ𝕣,ε}`
  differ by random / `ℓ`-dependent factors), and GM announce exactly this simultaneous statement at
  l. 1161.
* Readings (proposed DEVIATIONS entries in the WP-M2h report):
  - condition 3, upper bound: only for `z ≠ w` (for `z = w`, `B_{2|z−w|}(z) = ∅` and
    `D_h(z,z;∅) = ∞` with the internal-metric convention of `ContMetric.internal`; GM's bound is
    meant for distinct points);
  - condition 5: `ε ∈ (0,a] ∩ {2^{-n}}` (GM prints `(0,a𝕣] ∩ {2^{-n}𝕣}`, a typo: the radii
    `r^ε_k ∈ [ε^{1+ν}𝕣, ε𝕣]` of T4.2 (1) are indexed by the dimensionless `ε`);
  - condition 2: like conditions 4 and 7 (D60), `h_𝕣(z)`, `h_{ℓ𝕣}(z)` are read through the
    continuous circle-average process `H` (P2-M2H3, extension of DV-AUDM2-3);
  - condition 6: the grid `(ε𝕣/4)ℤ²` of GM Lemma 2.13 / CONF Lemma 3.5 (GM prints `(ε^{1+ν}𝕣/4)ℤ²`;
    condition 6 is used only through Remark 4.10, whose target `ℰ^𝕫_{ℓ𝕣}(a)` uses the grid
    `(ε·ℓ𝕣/4)ℤ²`, and Lemma 2.13 only controls `ρ_{𝕣,ε}` on `(ε𝕣/4)ℤ²`).
* `gm_S4_4` is GM Remark 4.10 (with DV-B4), `gm_regEvent_compl_le` the union bound of the proof
  of GM Lemma 4.11 (l. 1983–1990: each condition fails with probability at most `(1−p)/6`, here
  `(1−p)/7` with condition 7), and `gm_L4_11_of_conds` the assembly of GM Lemma 4.11 from the
  per-condition statements "the probability of condition `i` tends to `1` as `a → 0`, uniformly in
  `𝕣`" (`RegCondUnif`).
* D59 (DV-AUDM2-2): the radii `r^ε_k ∈ [ε^{1+ν}𝕣, ε𝕣]` of T4.2 (1) depend on `𝕣`, so
  `RegPar.rr 𝕣 ε k = r^ε_k` (GM U:1556: "Suppose `𝕣 > 0` and we are given … `ℛ`").
* D60 (DV-AUDM2-3): conditions 4 and 7 range over a continuum of centres, so they use a fixed
  jointly continuous version `H r z ω` of the circle-average process `h_r(z)` (GM U:223 footnote,
  citing Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, §3.1; in Lean
  `DFGPS.IsCircleAvgVersion`, `DFGPS.exists_isCircleAvgVersion`), passed to `regC4`, `regC7` and
  `regEvent`. Condition 7 uses `confRegH`, the event `confReg` with `𝔠_R e^{ξ H_R(𝕫)}` in place of
  `𝔠_R e^{ξ h_R(𝕫)}`; for each fixed `𝕫` it is a.s. equal to `confReg` (`confRegH_ae_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the fixed data of `ℰ_𝕣` (GM l. 1944–1970): `ξ`, the scaling constants `𝔠`, the CONF §3
parameters (for `ρ` and `ℰ^𝕫_𝕣(a)`), the Hölder exponents `χ < χ'`, `μ, ν` and `λ_1, …, λ_5`
(`lam 0, …, lam 4`) of Theorem 4.2, the events `E_r(z)` and chosen radii `r^ε_k = rr ε k` of
T4.2 (1) (`rr 𝕣 ε k = r^ε_k`, per scale `𝕣`, D59), `ℓ`, and the open sets `U ⊂ V` -/
structure RegPar where
  ξ : ℝ
  c : ℝ → ℝ
  p : CONFParams
  χ : ℝ
  χ' : ℝ
  μ : ℝ
  ν : ℝ
  lam : Fin 5 → ℝ
  E : ℝ → ℂ → Set DistC
  rr : ℝ → ℝ → ℕ → ℝ
  ℓ : ℝ
  U : Set ℂ
  V : Set ℂ

/-- `𝕣 A := {𝕣 x : x ∈ A}` (as in `Blueprint.T4_2`) -/
def rScale (𝕣 : ℝ) (A : Set ℂ) : Set ℂ := (fun x => (𝕣 : ℂ) * x) '' A

section Event
variable {Ω : Type} [MeasurableSpace Ω]

/-- `B_{4ℓ𝕣}(𝕣V)`, the region of conditions 2, 3, 5, 6 -/
def regRegion (R : RegPar) (𝕣 : ℝ) : Set ℂ := Metric.thickening (4 * (R.ℓ * 𝕣)) (rScale 𝕣 R.V)

/-- condition 1 (comparison of domains): `sup_{z,w ∈ 𝕣U} D_h(z,w) ≤ D_h(𝕣U, 𝕣∂V)` -/
def regC1 (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕣 : ℝ) : Set Ω :=
  {ω | (⨆ z ∈ rScale 𝕣 R.U, ⨆ w ∈ rScale 𝕣 R.U, ENNReal.ofReal ((D (h ω)).1 (z, w))) ≤
      setDist (D (h ω)) (rScale 𝕣 R.U) (rScale 𝕣 (frontier R.V))}

/-- condition 2 (comparison of `D_h`-balls and Euclidean balls), (4.32): for `z ∈ B_{4ℓ𝕣}(𝕣V)`,
`B_{a𝕣}(z) ⊂ 𝓑^•_{τ_{ℓ𝕣}(z)}(z)` and
`min{τ_{2ℓ𝕣} − τ_{ℓ𝕣}, τ_{3ℓ𝕣} − τ_{2ℓ𝕣}} ≥ a max{𝔠_𝕣e^{ξh_𝕣(z)}, 𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(z)}}`, with
`h_r(z) = H r z ω` the continuous circle-average process (the centres `z` range over a continuum;
D60 extended to condition 2, P2-M2H3) -/
def regC2 (D : DistC → ContMetric) (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ) (R : RegPar) (𝕣 a : ℝ) :
    Set Ω :=
  {ω | ∀ z ∈ regRegion R 𝕣,
    Metric.ball z (a * 𝕣) ⊆ filledBall (D (h ω)) z (tauR D h z (R.ℓ * 𝕣) ω) ∧
    a * max (R.c 𝕣 * Real.exp (R.ξ * H 𝕣 z ω))
        (R.c (R.ℓ * 𝕣) * Real.exp (R.ξ * H (R.ℓ * 𝕣) z ω)) ≤
      min (tauR D h z (2 * (R.ℓ * 𝕣)) ω - tauR D h z (R.ℓ * 𝕣) ω)
        (tauR D h z (3 * (R.ℓ * 𝕣)) ω - tauR D h z (2 * (R.ℓ * 𝕣)) ω)}

/-- condition 3 (Hölder continuity), (4.33): for `z, w ∈ B_{4ℓ𝕣}(𝕣V)` with `|z − w| ≤ a𝕣`,
`𝔠_𝕣⁻¹e^{−ξh_𝕣(0)} D_h(z,w) ≥ |(z−w)/𝕣|^{χ'}` and (for `z ≠ w`)
`𝔠_𝕣⁻¹e^{−ξh_𝕣(0)} D_h(z,w; B_{2|z−w|}(z)) ≤ |(z−w)/𝕣|^χ` (forms of DFGPS Prop 3.18 / Lemma 3.20) -/
def regC3 (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕣 a : ℝ) : Set Ω :=
  {ω | ∀ z ∈ regRegion R 𝕣, ∀ w ∈ regRegion R 𝕣, ‖z - w‖ ≤ a * 𝕣 →
    ‖(z - w) / 𝕣‖ ^ R.χ' ≤ (scaleFac R.ξ R.c (h ω) 𝕣 0)⁻¹ * (D (h ω)).1 (z, w) ∧
    (z ≠ w → ENNReal.ofReal ((scaleFac R.ξ R.c (h ω) 𝕣 0)⁻¹) *
        (D (h ω)).internal (Metric.ball z (2 * ‖z - w‖)) z w ≤
      ENNReal.ofReal (‖(z - w) / 𝕣‖ ^ R.χ))}

/-- condition 4 (comparison of circle averages): `sup_{z ∈ 𝕣V} |h_𝕣(z) − h_𝕣(0)| ≤ a⁻¹`, with
`h_𝕣(z) = H 𝕣 z ω` the continuous circle-average process (D60) -/
def regC4 (H : ℝ → ℂ → Ω → ℝ) (R : RegPar) (𝕣 a : ℝ) : Set Ω :=
  {ω | ∀ z ∈ rScale 𝕣 R.V, |H 𝕣 z ω - H 𝕣 0 ω| ≤ a⁻¹}

/-- condition 5 (existence of good annuli): for each dyadic `ε = 2^{-n} ∈ (0,a]` and each
`z ∈ (λ_1ε^{1+ν}𝕣/4)ℤ² ∩ B_{4ℓ𝕣}(𝕣V)` some `r^ε_k`, `k < ⌊μ log_8 ε⁻¹⌋`, has `E_{r^ε_k}(z)` -/
def regC5 (h : Ω → DistC) (R : RegPar) (𝕣 a : ℝ) : Set Ω :=
  {ω | ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n ≤ a →
    ∀ z ∈ gridPts (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4) ∩ regRegion R 𝕣,
      ∃ k < ⌊R.μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊, h ω ∈ R.E (R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k) z}

/-- condition 6 (bounds for the radii `ρ_{𝕣,ε}(z) = ρ^{⌊η log ε⁻¹⌋}_{ε𝕣}(z)`): for each dyadic
`ε = 2^{-n} ∈ (0,a]` and `z ∈ (ε𝕣/4)ℤ² ∩ B_{4ℓ𝕣}(𝕣V)`, `ρ_{𝕣,ε}(z) ≤ ε^{1/2}𝕣` -/
def regC6 (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (R : RegPar) (𝕣 a : ℝ) :
    Set Ω :=
  {ω | ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n ≤ a →
    ∀ z ∈ gridPts ((2 : ℝ)⁻¹ ^ n * 𝕣 / 4) ∩ regRegion R 𝕣,
      confRho R.ξ R.c D P h R.p ((2 : ℝ)⁻¹ ^ n * 𝕣) z (confN R.p ((2 : ℝ)⁻¹ ^ n)) ω ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ (1 / 2 : ℝ) * 𝕣)}

/-- the event `𝓔^𝕫_R(a)` of `Blueprint.confReg` (CONF l. 1484–1491, GM S2.7 l. 1153–1158) with
the normalization `𝔠_R e^{ξ h_R(𝕫)}` read through the continuous circle-average process `H` (D60) -/
def confRegH (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (H : ℝ → ℂ → Ω → ℝ) (p : CONFParams) (χ : ℝ) (z₀ : ℂ) (R a : ℝ) : Set Ω :=
  {ω | Metric.ball z₀ (a * R) ⊆ filledBall (D (h ω)) z₀ (tauR D h z₀ R ω) ∧
    a * (cc R * Real.exp (ξ * H R z₀ ω)) ≤ tauR D h z₀ (3 * R) ω - tauR D h z₀ (2 * R) ω ∧
    (∀ u ∈ Metric.ball z₀ (4 * R), ∀ v ∈ Metric.ball z₀ (4 * R), ‖u - v‖ / R ≤ a →
      (cc R * Real.exp (ξ * H R z₀ ω))⁻¹ * (D (h ω)).1 (u, v) ≤ (‖u - v‖ / R) ^ χ) ∧
    ∀ (j : ℕ), (2 : ℝ)⁻¹ ^ j ≤ a → ∀ z ∈ gridPts ((2 : ℝ)⁻¹ ^ j * R / 4) ∩ Metric.ball z₀ (4 * R),
      confRho ξ cc D P h p ((2 : ℝ)⁻¹ ^ j * R) z (confN p ((2 : ℝ)⁻¹ ^ j)) ω ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ (1 / 2 : ℝ) * R)}

/-- for a fixed centre, `confRegH` and `confReg` agree almost surely whenever `H R z₀ = h_R(z₀)`
a.s. (e.g. `DFGPS.IsCircleAvgVersion.ae_eq`) -/
theorem confRegH_ae_eq {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} {p : CONFParams} {χ : ℝ} {z₀ : ℂ} {R a : ℝ}
    (hH : ∀ᵐ ω ∂P, H R z₀ ω = circleAvg (h ω) R z₀) :
    confRegH ξ cc D P h H p χ z₀ R a =ᵐ[P] confReg ξ cc D P h p χ z₀ R a := by
  filter_upwards [hH] with ω hω
  simp only [confRegH, confReg, scaleFac, mem_ofPred_eq, hω]

/-- condition 7 (DV-B4): `ℰ^𝕫_{ℓ𝕣}(a)` (GM l. 1153–1158) for every `𝕫 ∈ 𝕣U`, through the
continuous circle-average process `H` (D60) -/
def regC7 (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ)
    (R : RegPar) (𝕣 a : ℝ) : Set Ω :=
  ⋂ 𝕫 ∈ rScale 𝕣 R.U, confRegH R.ξ R.c D P h H R.p R.χ 𝕫 (R.ℓ * 𝕣) a

/-- **the global regularity event** `ℰ_𝕣 = ℰ_𝕣(a, ν, ℓ, U, V)` (GM §4.3, l. 1950–1970, with
condition 7 of DV-B4) -/
def regEvent (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ)
    (R : RegPar) (𝕣 a : ℝ) : Set Ω :=
  regC1 D h R 𝕣 ∩ regC2 D h H R 𝕣 a ∩ regC3 D h R 𝕣 a ∩ regC4 H R 𝕣 a ∩ regC5 h R 𝕣 a ∩
    regC6 D P h R 𝕣 a ∩ regC7 D P h H R 𝕣 a

variable {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
  {R : RegPar} {𝕣 a : ℝ}

theorem gm_regEvent_mem {ω : Ω} :
    ω ∈ regEvent D P h H R 𝕣 a ↔ ω ∈ regC1 D h R 𝕣 ∧ ω ∈ regC2 D h H R 𝕣 a ∧ ω ∈ regC3 D h R 𝕣 a ∧
      ω ∈ regC4 H R 𝕣 a ∧ ω ∈ regC5 h R 𝕣 a ∧ ω ∈ regC6 D P h R 𝕣 a ∧
      ω ∈ regC7 D P h H R 𝕣 a := by
  simp only [regEvent, mem_inter_iff]
  tauto

/-- the union bound in the proof of **GM Lemma 4.11** (l. 1983–1990): `ℰ_𝕣ᶜ` is the union of the
complements of the seven conditions -/
theorem gm_regEvent_compl_le :
    P (regEvent D P h H R 𝕣 a)ᶜ ≤ P (regC1 D h R 𝕣)ᶜ + P (regC2 D h H R 𝕣 a)ᶜ +
      P (regC3 D h R 𝕣 a)ᶜ + P (regC4 H R 𝕣 a)ᶜ + P (regC5 h R 𝕣 a)ᶜ +
      P (regC6 D P h R 𝕣 a)ᶜ + P (regC7 D P h H R 𝕣 a)ᶜ := by
  simp only [regEvent, compl_inter]
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  exact measure_union_le _ _

/-- the uniform-in-`a` part of `RegCondUnif` at a fixed level `q` and threshold `a₀` (D75: in GM
Lemma 4.11 `a` depends only on `U, ν, ℓ, p` and the parameters, so the threshold is chosen before
the probability space) -/
def RegCondAt (P : Measure Ω) (C : ℝ → ℝ → Set Ω) (q a₀ : ℝ) : Prop :=
  ∀ a ∈ Ioc 0 a₀, ∀ 𝕣 : ℝ, 0 < 𝕣 → P (C 𝕣 a)ᶜ ≤ ENNReal.ofReal (1 - q)

/-- the parameter `a` of GM Lemma 4.11: the minimum of the thresholds of conditions 2–7 and `1/2` -/
def regAmin (a₂ a₃ a₄ a₅ a₆ a₇ : ℝ) : ℝ :=
  min (min (min a₂ a₃) (min a₄ a₅)) (min (min a₆ a₇) (1 / 2 : ℝ))

theorem gm_regAmin_pos {a₂ a₃ a₄ a₅ a₆ a₇ : ℝ} (h₂ : 0 < a₂) (h₃ : 0 < a₃) (h₄ : 0 < a₄)
    (h₅ : 0 < a₅) (h₆ : 0 < a₆) (h₇ : 0 < a₇) : regAmin a₂ a₃ a₄ a₅ a₆ a₇ ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨?_, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)⟩
  simp only [regAmin, lt_min_iff]; exact ⟨⟨⟨h₂, h₃⟩, ⟨h₄, h₅⟩⟩, ⟨⟨h₆, h₇⟩, by norm_num⟩⟩

end Event

end LQGMetric.GM
