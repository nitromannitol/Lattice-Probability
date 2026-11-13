/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBFinal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp410

/-!
# [18] Lemmas 3.8 and 3.11 at every real mesh, for every frozen coupling (no premise)

The conditional theorems of `EpsBMain` / `EpsBLemma38` take [18] Proposition 4.10 at real meshes as their one named
hypothesis `Prop410Real P η ρ' 100`. Its body is verbatim that of `GMSMain.EpsAProp410At`
(`prop410Real_iff_epsA`, `Iff.rfl`), which holds for every frozen coupling, every `ρ' ∈ (0, 1)` and every
`C > 1` (`GMSMain.epsA_prop410At`). This file discharges that hypothesis using `GMSMain.epsA_prop410At`.

* **`lemma311Real_of_coupling`** — [18] Lemma 3.11 (3.35), graph disconnection, at every real `ε ∈ (0, 1)`, every
  `ρ ∈ (0, 1)`, every frozen coupling `D` on a standard Borel space, `γ ∈ (0, 2)`;
* `lemma311BadReal_of_coupling` — the same as `EpsBMain.Lemma311BadReal P bm η ρ` (consumer form);
* `lemma311Real_of_matingOfTrees` — the same in the bundle-variable form of `lemma311_of_matingOfTrees_all`;
* `lemma38Real_of_coupling` — [18] Lemma 3.8 (corrected form) at every real mesh, every `ρ ∈ (0, 1)`;
* `cellFamily_bandSeq_of_coupling` — the annulus-disconnection estimate along every band sequence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- [18] Proposition 4.10 at real meshes for every frozen coupling. -/
theorem prop410Real_of_coupling (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {ρ C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : 1 < C) :
    Prop410Real P η ρ C :=
  GMSMain.epsA_prop410At D hstd hγ hρ0 hρ1 hC

/-- **[18] Lemma 3.11 at every real mesh `ε ∈ (0, 1)`** for the embedded mated-CRT map of every frozen
mating-of-trees coupling, every `γ ∈ (0, 2)`, every `ρ ∈ (0, 1)`: there are `α, β, p > 0` and `C` such that for every
`ε ∈ (0, 1)`, outside an event of outer probability `≤ C ε^α`, the mesh-`ε` map `MatedCRT.graph ε (bm ω)` is locally
finite, its cells `η([ε(x−1), εx])` form a cellular embedding `H`, and (3.35) holds on `H`: for every `z` and
`r ∈ [ε^β, ρ]` with `B_{2r}(z) ⊂ B_ρ(0)` and every `x ∈ V(B_r(z))`, the walk graph-disconnects `V(∂B_{r/2}(z))`
from `V(∂B_{2r}(z))` before hitting `V(∂B_{2r}(z))` with quenched probability `≥ p`. -/
theorem lemma311Real_of_coupling (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) :=
  lemma311Real_of_prop410_all D hstd hγ
    (fun _ hρ0 hρ1 => prop410Real_of_coupling D hstd hγ hρ0 hρ1 (by norm_num)) hρ hρ1

end Coupling

end MatedCRTHarmonic.GMSMain.EpsB
