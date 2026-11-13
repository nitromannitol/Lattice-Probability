/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13Energy at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13Path

/-!
# The Dirichlet energy of the discrete harmonic extension of (1.6), deterministic form

Source: [18] (1.5)–(1.7) and Theorem 1.3, the proof of
Theorem 3.2 from Lemma 3.3 (`[18]`, Dirichlet's principle) using the energy estimate.

For a cellular embedding `H` of `G`, an open bounded `D` and `f` continuous on `D̄`:

* `IsGMSDirichletSolution H D f fε` — `fε` has the boundary values (1.6),
  `fε(x) = sup_{z ∈ H_x ∩ ∂D} f(z)` for `x ∈ V(∂D)`, and is discrete harmonic at the interior vertices
  `x ∈ V(D) \ V(∂D)` (the defining properties of [18]'s `f_ε`, `[18]`);
* `t13_exists_refPoint` — each cell meeting `D̄` has a point of `D̄` at which `f` attains the boundary value (1.6);
* **`t13_energy_le_of_lipschitz`** — if `f` is `L`-Lipschitz on `D̄`, then
  `Energy(fε; G(D)) ≤ 2 L² ∑_{x ∈ V(D)} deg(x) diam(H_x)²` (Dirichlet's principle with reference points in `D̄`,
  the edge estimate `|f(p x) − f(p y)| ≤ L (diam H_x + diam H_y)`);
* `t13_sum_le_lintegral_uDens` — `∑_{x ∈ S} diam(H_x)² deg(x) ≤ ∫_Ω u^ε` when the cells of `S` lie in `Ω`;
* **`t13_energy_le_on_event`** — on the event of [18] Lemma 2.7 on `B_{ρ₁}(0)` (diameters `≤ δ`) and of
  [18] Proposition 2.10 for the single test `(B_{ρ₁}(0), 1)`, with `D ⊂ B_ρ(0)`, `ρ + δ ≤ ρ₁ ≤ 1`:
  `Energy(fε; G(D)) ≤ 2 L² (4A + η)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal Classical

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3 LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **[18]'s discrete harmonic function `f_ε`**: the boundary values (1.6)
`fε(x) = sup_{z ∈ H_x ∩ ∂D} f(z)` on `V(∂D)` and discrete harmonicity on `V(D) \ V(∂D)`. -/
def IsGMSDirichletSolution (D : Set ℂ) (f : ℂ → ℝ) (fε : V → ℝ) : Prop :=
  (∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty → fε x = sSup (f '' (H.cell x ∩ frontier D))) ∧
    ∀ x ∈ vFin H D, ¬ (H.cell x ∩ frontier D).Nonempty → lap G fε x = 0

/-- A reference point of a cell meeting `D̄`: in `H_x ∩ D̄`, and a maximizer of `f` on `H_x ∩ ∂D` when this set is
nonempty. -/
theorem t13_exists_refPoint {D : Set ℂ} {f : ℂ → ℝ} (hfc : ContinuousOn f (closure D))
    (x : V) (hx : (H.cell x ∩ closure D).Nonempty) :
    ∃ z ∈ H.cell x ∩ closure D,
      ((H.cell x ∩ frontier D).Nonempty → f z = sSup (f '' (H.cell x ∩ frontier D))) := by
  by_cases hb : (H.cell x ∩ frontier D).Nonempty
  · have hK : IsCompact (H.cell x ∩ frontier D) := (H.isCompact_cell x).inter_right isClosed_frontier
    have hfK : ContinuousOn f (H.cell x ∩ frontier D) :=
      hfc.mono (inter_subset_right.trans frontier_subset_closure)
    obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hb hfK
    refine ⟨z, ⟨hz.1, frontier_subset_closure hz.2⟩, fun _ => ?_⟩
    refine (IsGreatest.csSup_eq ⟨mem_image_of_mem f hz, ?_⟩).symm
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  · obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz, fun h => absurd h hb⟩

end MatedCRTHarmonic.GMSMain
