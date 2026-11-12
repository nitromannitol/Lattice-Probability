/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Regularity at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
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

section Event
variable {Ω : Type} [MeasurableSpace Ω]

variable {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
  {R : RegPar} {𝕣 a : ℝ}

end Event

end LQGMetric.GM
