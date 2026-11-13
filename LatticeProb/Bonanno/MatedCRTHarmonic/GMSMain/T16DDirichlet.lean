/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T16DDirichlet at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.FirstVisit
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma38

/-!
# The discrete Dirichlet problem on `G^ε(D)`

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]
(`[18]:N` is line N): the sub-graph `G^ε(D)` of (1.5) ([18], vertex
set `V(G^ε(D)) = {x : H_x ∩ D ≠ ∅}`) and "the function `f_ε`" of (1.6): `f_ε : V(G^ε(D)) → ℝ` equals
the boundary data on `V(G^ε(∂D))` and is discrete harmonic on `V(G^ε(D)) \ V(G^ε(∂D))`. This file proves that the
definite article is justified (existence and uniqueness), the random-walk representation
`f_ε(x) = E_x[f_ε(X_τ)]` (`τ` the hitting time of `V(G^ε(∂D))`) and the maximum principle; in particular,
("interior vertices have all their neighbours in `V(D)`").

## Abstract layer (a locally finite multigraph `G`, finite vertex sets `S`, `B`)

* `IsDirichletSolution G S B g f`: `lap G f = 0` on `S \ B` and `f = g` on `S ∩ B` (`GMS3.lap`: the unnormalized
  Laplacian over edge ends, so multiple edges count with multiplicity; `lap G f x = 0` iff `f(x)` is the average of
  `f` over the edge ends at `x`, i.e. `f` is harmonic for simple random walk at `x`).
* `lap_sub`, `lap_neg`, `lap_sum_mul`: linearity of the Laplacian.
* `exists_mem_boundary_eq_max` (**maximum principle**, strong form): if every vertex of `S \ B` has all of its dart
  heads in `S`, `G` is connected and some vertex lies outside `S`, a function harmonic on `S \ B` attains its maximum
  over `S` at a vertex of `S ∩ B`; `le_of_harmonic`, `ge_of_harmonic`: the weak maximum and minimum principles.
* `eqOn_of_isDirichletSolution` (**uniqueness** on `S`).
* `dirichletSol G B g x = ∑_{b ∈ B} g(b) P_x(X_{τ_B} = b)` and `isDirichletSolution_dirichletSol` (**existence**;
  no connectivity is needed for it).
* `walkLaw_hitTime_eq_one` (the walk from `S` hits `B` almost surely), `ae_hitVertex_mem` (almost surely it first
  hits `B` inside `S ∩ B`), `integral_hitVertex` (`E_x[F(X_τ)] = ∑_{b ∈ B} F(b) P_x(X_τ = b)`) and
  `eq_integral_of_isDirichletSolution` (**walk representation** `f(x) = E_x[f(X_τ)]`).

## Cell layer (a cellular embedding `H` of a connected `G`, a bounded open `D ⊂ ℂ`)

* `vBd H D = V(∂D)` (the finset `GMS3.vFin H (frontier D)`; `coe_vBd`: it is the frozen
  `verticesMeeting H.cell (frontier D)`); `V(D)` is `GMS3.vFin H D` (finite: `GMS3.finite_verticesMeeting`; equal to
  `verticesMeeting H.cell D`: `GMS3.coe_vFin`).
* `dtgt_mem_vFin_of_interior`, `mem_vFin_of_adj_of_interior`: interior vertices have all their neighbours in `V(D)`;
  `exists_notMem_vFin`: some vertex lies outside `V(D)` (cellular embeddings have infinitely many vertices).
* `IsCellDirichletSolution H D g f` (= `IsDirichletSolution G V(D) V(∂D) g f`), and the cell theorems
  `existsUnique_cellDirichlet`, `cellDirichlet_walkLaw_hitTime_eq_one`, `cellDirichlet_eq_integral`,
  `cellDirichlet_le`, `cellDirichlet_ge`.
* `bdryVal H D f x = sup_{z ∈ H_x ∩ ∂D} f(z)` ((1.6)), attained for `f` continuous on `∂D` (`exists_bdryVal_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open LFMultigraph Harmonic HarmonicInfinity Markov GMS3

variable {V E : Type*} (G : LFMultigraph V E)

/-! ### Linearity of the Laplacian -/

theorem lap_sum_mul {ι : Type*} (T : Finset ι) (c : ι → ℝ) (φ : ι → V → ℝ) (x : V) :
    lap G (fun y => ∑ i ∈ T, c i * φ i y) x = ∑ i ∈ T, c i * lap G (φ i) x := by
  unfold lap
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The Dirichlet problem on a finite vertex set -/

/-- **The discrete Dirichlet problem** on the finite vertex set `S` with boundary vertex set `B`: `f` is discrete
harmonic (`lap G f x = 0`) at every vertex of `S` outside `B` and equals `g` at every vertex of `S` in `B`. Only the
values of `f` on `S` and of `g` on `S ∩ B` matter. -/
def IsDirichletSolution (S B : Finset V) (g f : V → ℝ) : Prop :=
  (∀ x ∈ S, x ∉ B → lap G f x = 0) ∧ ∀ x ∈ S, x ∈ B → f x = g x

/-! ### Existence: the walk solution -/

/-- The walk solution `x ↦ E_x[g(X_{τ_B})] = ∑_{b ∈ B} g(b) P_x(X_{τ_B} = b)` (`τ_B` the hitting time of `B`). -/
def dirichletSol (B : Finset V) (g : V → ℝ) (x : V) : ℝ :=
  ∑ b ∈ B, g b * (hitDist G (B : Set V) x {b}).toReal

/-- The walk solution is discrete harmonic off `B`. -/
theorem lap_dirichletSol (B : Finset V) (g : V → ℝ) {x : V} (hx : x ∉ B) :
    lap G (dirichletSol G B g) x = 0 := by
  have h := lap_sum_mul G B g (fun b y => (hitDist G (B : Set V) y {b}).toReal) x
  have hfun : (fun y => ∑ b ∈ B, g b * (hitDist G (B : Set V) y {b}).toReal) = dirichletSol G B g := rfl
  rw [hfun] at h
  rw [h]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [lap_hitDist G (I := (B : Set V)) (by exact_mod_cast hx) {b}, mul_zero]

/-- The walk solution equals `g` on `B`. -/
theorem dirichletSol_of_mem (B : Finset V) (g : V → ℝ) {x : V} (hx : x ∈ B) :
    dirichletSol G B g x = g x := by
  unfold dirichletSol
  rw [Finset.sum_eq_single x]
  · rw [hitDist_of_mem G (I := (B : Set V)) (by exact_mod_cast hx),
      Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply, ENNReal.toReal_one, mul_one]
  · intro b _ hbx
    rw [hitDist_of_mem G (I := (B : Set V)) (by exact_mod_cast hx),
      Set.indicator_of_notMem (fun h => hbx (Set.mem_singleton_iff.mp h).symm), ENNReal.toReal_zero,
      mul_zero]
  · intro h
    exact absurd hx h

/-- **Existence**: the walk solution solves the Dirichlet problem (for any `S`; no connectivity is needed). -/
theorem isDirichletSolution_dirichletSol (S B : Finset V) (g : V → ℝ) :
    IsDirichletSolution G S B g (dirichletSol G B g) :=
  ⟨fun _ _ hxB => lap_dirichletSol G B g hxB, fun _ _ hxB => dirichletSol_of_mem G B g hxB⟩

/-! ### The walk representation -/

/-! ### The cell layer: `G^ε(D)` -/

section Cells

variable {G} {o : V} (H : CellularEmbedding G o)

/-- `V(G(∂D))`: the vertices whose cells meet `∂D = frontier D`, as a finset (`GMS3.vFin`). -/
abbrev vBd (D : Set ℂ) : Finset V := vFin H (frontier D)

theorem isBounded_frontier {D : Set ℂ} (hD : Bornology.IsBounded D) : Bornology.IsBounded (frontier D) :=
  hD.closure.subset frontier_subset_closure

theorem mem_vBd {D : Set ℂ} (hD : Bornology.IsBounded D) {x : V} :
    x ∈ vBd H D ↔ (H.cell x ∩ frontier D).Nonempty :=
  mem_vFin H (isBounded_frontier hD)

/-- **[18] (1.6), the discrete Dirichlet problem on `G(D)`**: `f` is discrete harmonic on
`V(G(D)) \ V(G(∂D))` and equals `g` on `V(G(D)) ∩ V(G(∂D))`. -/
def IsCellDirichletSolution (D : Set ℂ) (g f : V → ℝ) : Prop :=
  IsDirichletSolution G (vFin H D) (vBd H D) g f

/-- The walk solution solves the cell Dirichlet problem (for every `D`). -/
theorem isCellDirichletSolution_dirichletSol (D : Set ℂ) (g : V → ℝ) :
    IsCellDirichletSolution H D g (dirichletSol G (vBd H D) g) :=
  isDirichletSolution_dirichletSol G _ _ g

/-! ### The boundary values (1.6) -/

/-- **The boundary values of [18] (1.6)**: `sup_{z ∈ H_x ∩ ∂D} f(z)`. It is attained when `f` is
continuous on `∂D` and `H_x` meets `∂D` (`exists_bdryVal_eq`); its other values are never used. -/
def bdryVal (D : Set ℂ) (f : ℂ → ℝ) (x : V) : ℝ := sSup (f '' (H.cell x ∩ frontier D))

theorem isCompact_cell_inter_frontier (D : Set ℂ) (x : V) : IsCompact (H.cell x ∩ frontier D) :=
  (H.isCompact_cell x).inter_right isClosed_frontier

/-- For `f` continuous on `∂D` and `H_x ∩ ∂D ≠ ∅`, the supremum (1.6) is attained and bounds `f` on `H_x ∩ ∂D`. -/
theorem exists_bdryVal_eq {D : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {x : V}
    (hx : (H.cell x ∩ frontier D).Nonempty) :
    ∃ z ∈ H.cell x ∩ frontier D, bdryVal H D f x = f z ∧ ∀ w ∈ H.cell x ∩ frontier D, f w ≤ f z := by
  have hK := isCompact_cell_inter_frontier H D x
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hx (hf.mono Set.inter_subset_right)
  refine ⟨z, hz, ?_, fun w hw => hmax hw⟩
  have hgreat : IsGreatest (f '' (H.cell x ∩ frontier D)) (f z) :=
    ⟨Set.mem_image_of_mem f hz, by rintro _ ⟨w, hw, rfl⟩; exact hmax hw⟩
  exact hgreat.csSup_eq

end Cells

end MatedCRTHarmonic.GMSMain.T16D
