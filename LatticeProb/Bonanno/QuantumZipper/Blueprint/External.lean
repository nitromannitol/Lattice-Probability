/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Blueprint.External at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Analysis.Removability
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import LatticeProb.Bonanno.QuantumZipper.Loewner.Curves
import Mathlib.Probability.BrownianMotion.Basic

/-!
# External (literature) blueprint items

`Prop`-valued statements of results imported from the literature. Nothing is proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.Blueprint

/-- Jones–Smirnov, *Removability theorems for Sobolev functions and quasiconformal maps*,
Ark. Mat. 38 (2000), 263–279, Corollary 2 (p. 267): "Boundaries of Hölder domains are
quasiconformally removable." Formalized for a compact set `K ⊆ ℂ` whose complement in the Riemann
sphere is a Hölder domain (`IsHolderDomainSphere K`) and which has empty interior, so that `K` is
the boundary of that domain; the conclusion is conformal removability, the case the paper uses.

Deviation L-JS1 (approved by the user on 2026-09-27; see `DEVIATIONS.md`): the first version of
this item had no hypothesis `interior K = ∅` and claimed that the whole complement `K` of the
Hölder domain is removable. That version is false: the closed unit disk has the Hölder complement
`{z | 1 < ‖z‖}` but is not removable, since `z ↦ z * min 1 ‖z‖` is a homeomorphism of `ℂ` that is
holomorphic off the disk and not holomorphic inside it. Jones–Smirnov's result concerns the
boundary of the domain, which equals `K` exactly when `K` has empty interior. In Theorem 1.4 the
set is the closure of the SLE hull together with its complex conjugate, an arc, which has empty
interior (`interior_doubledHull_eq_empty`). -/
def JonesSmirnovRemovable : Prop :=
  ∀ K : Set ℂ, IsHolderDomainSphere K → interior K = ∅ → IsConformallyRemovable K

/-- Rohde–Schramm, *Basic properties of SLE*, Ann. of Math. 161 (2005), 883–924, Theorem 4.7
(the SLE_κ trace exists and generates the hulls) and Theorem 6.1 (for `κ ∈ [0,4]` it is a.s. a
simple curve in `ℍ ∪ {0}`, so the hull at time `t` is exactly the trace on `(0,t]`).
**Proved**: `RS.rohdeSchrammSimple` (`Proofs/RS/RohdeSchrammSimple.lean:31`, commit `f19b1bf`,
entry L-RS-P; standard axioms). -/
def RohdeSchrammSimple : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, IsSimpleChord (sleTrace κ B ω) ∧
      ∀ t : ℝ, 0 ≤ t → fwdHull (drive κ B ω) t = sleTrace κ B ω '' Set.Ioc 0 t

/-- Rohde–Schramm, Ann. of Math. 161 (2005), Theorem 5.2: for `κ < 4`, the complement of an
SLE_κ hull is a.s. a Hölder domain; we use it for the hull doubled by complex conjugation,
whose complement in `ℂ̂` is the relevant domain. Rohde–Schramm state it for the *forward*
hull; the reverse hull at a fixed time `T` has the same law (see `ForwardReverseRelation`:
the reverse flow at time `T` is the inverse forward flow driven by the time-reversed
increment, again a Brownian motion times `√κ` on `[0,T]`), which is how the paper uses it in
Theorem 1.4. -/
def RohdeSchrammHolder : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, IsHolderDomainSphere (closure (revHull (drive κ B ω) T) ∪
      (starRingEnd ℂ) '' closure (revHull (drive κ B ω) T))

/-- Riemann mapping theorem plus Carathéodory's boundary extension (e.g. Pommerenke,
*Boundary Behaviour of Conformal Maps*, Thm. 2.6): each complementary component of a simple
chord from `0` to `∞` in `ℍ` has a normalized conformal uniformizer onto `ℍ` fixing `0`
and `∞`.
**Proved**: `CA.Uniformizer.riemannMappingCaratheodory` (`Proofs/Complex/UniformizerRight.lean:142`,
entries L-CA-TOPO (U-nodes) and L-CA-M; standard axioms). -/
def RiemannMappingCaratheodory : Prop :=
  ∀ η : ℝ → ℂ, IsSimpleChord η →
    (∃ φ, IsNormalizedUniformizer (leftComponent η) φ) ∧
      (∃ φ, IsNormalizedUniformizer (rightComponent η) φ)

end QuantumZipper.Blueprint
