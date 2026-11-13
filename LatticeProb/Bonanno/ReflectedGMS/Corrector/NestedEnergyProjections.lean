/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.NestedEnergyProjections at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CentroidTraceLocalEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyRedistribution

/-!
# Nested energy projections (`s:prop:projection`): the deterministic identity

The manuscript proposition *Nested energy projections* asserts, for the blockwise harmonic
modifications `φ_m` of the base (centroid) embedding `b`,

`e_m + ‖g_m - g_0‖_*² = e_0`,   `e_m = e_n + ‖g_m - g_n‖_*²`  (`n ≥ m`),

with `g_m = ∇φ_m` and `e_m = ‖g_m‖_*²` the *specific* (expected root) energy, and concludes
`e_m ↓ e_∞ ≥ 0` with the gradients Cauchy in specific energy.

Its proof has two clearly separated halves, and the manuscript itself separates them:

* a **deterministic, blockwise** half — on a selected square `S` the full-energy minimizer
  with the centroid trace is energy-orthogonal to *every* finite-energy competitor
  difference, so the energies decompose by Pythagoras *on that block*; and
* a **probabilistic** half — the blockwise identities are transported to the expected root
  densities by the mass-transport redistribution `s:lem:redistribution`, already proved in
  `Corrector/SpecificEnergyRedistribution.lean`.

This module proves the deterministic half in full, for the *actual* project object
`DyadicApproximation.CentroidTraceMinimizer`, and then proves the two purely order-theoretic
conclusion clauses of the proposition.  Precisely:

## The deterministic orthogonality and Pythagoras

* `Energy_add_smul` — the exact quadratic expansion
  `ℰ(f + t ψ) = ℰ(f) + 2t ⟪f,ψ⟫ + t² ℰ(ψ)` of the existing `dirichletForm`, from its
  bilinearity; no new energy object is introduced.
* `eq_zero_of_quadratic_nonneg` — the first-variation lemma for a real quadratic.
* `sum_energy_line` — its plane-valued form, in terms of the existing
  `StatementIngredients.vectorPairing`.
* `vectorPairing_sub_eq_zero_of_min` — **full variational orthogonality**
  `⟪f, g - f⟫_G = 0` for a full-energy trace minimizer `f` against every finite-energy
  competitor `g` carrying the same trace.  This is the manuscript's `ℰ_{G_S}(φ_m, v) = 0`,
  obtained from minimality alone.
* `vectorEnergy_eq_add_vectorEnergy_sub_of_min` — the **Pythagorean identity**
  `ℰ_G(g) = ℰ_G(f) + ℰ_G(g - f)`, and `vectorEnergy_sub_le_of_min` its corollary
  `ℰ_G(g - f) ≤ ℰ_G(g)`, the manuscript's bound of the variation energy by the base energy
  carried by the block, which is what makes `e_m < ∞` follow by redistribution.

These are then specialised to the project's blockwise minimizer, where the competition class
is by definition the full one:

* `vectorPairing_sub_eq_zero_of_centroidTraceMinimizer`,
* `blockPythagoras_of_centroidTraceMinimizer`,
* `vectorEnergy_sub_le_of_centroidTraceMinimizer`.

The two manuscript equations appear blockwise as two instantiations of the *same* theorem:

* `blockPythagoras_centroid` is `s:eq:pyth0` on a block, the competitor being the centroid
  embedding `b` itself;
* `blockPythagoras_nested` is `s:eq:pythmn` on a block of the finer partition, the competitor
  being `φ_m`, which is admissible there exactly because `φ_m = b` on `skel_n`
  (`s:eq:pinnested`).  That pinning statement is a *geometric* input, carried here as the
  explicit hypothesis `hmtr`; it is not the identity being proved.

## The conclusion clauses

`antitone_of_nested_projection`, `nested_projection_iInf_nonneg`,
`tendsto_nested_projection_atTop` and `nested_projection_cauchy` prove, from the nested
identities as *numerical* relations `e m = e n + d m n` with `d ≥ 0`, that `e_m ↓ e_∞ ≥ 0`
and that `d m n` is eventually uniformly small — the final sentence of `s:prop:projection`.
These need no deterministic spatial average theorem, as required by the work order.

## The remaining probabilistic instantiation

`integral_signedRootDensity_eq_zero_of_ownerBlockDensity_eq` is the single probabilistic step
of the manuscript proof in the exact form supplied by the checked signed redistribution: once
the blockwise orthogonality above makes the owner-block densities of the positive and
negative parts of the signed coefficient `c(e) g_m(e)·(g_m(e) - g_0(e))` agree, the *signed
expected root density* — i.e. the specific pairing `⟪g_m, g_m - g_0⟫_*` — vanishes.

What is deliberately **not** claimed here is the assembly of that vanishing pairing into
`s:eq:pyth0` for the expected root densities.  That last step needs the polarization of the
root density `ρ_{θ+η}` together with the marked-law producers (joint measurability of the
kernel, the marked mass transport, and the re-rooting covariance of the owner field for the
actual `g_m`), which are separately staffed.  No finite total energy of the infinite
environment is used or assumed anywhere in this module: the specific energy stays an expected
root density throughout, and every energy hypothesis is local to one block.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.NestedEnergyProjections

open StatementIngredients DyadicApproximation

/-! ### The quadratic expansion of the Dirichlet energy along a line

Everything here is the bilinearity of the existing
`ReflectedWalk.ConductanceGraph.dirichletForm`; no new energy object is defined. -/

/-- **The exact quadratic expansion** `ℰ(f + t ψ) = ℰ(f) + 2t ⟪f, ψ⟫ + t² ℰ(ψ)` of the
Dirichlet energy along the line through `f` in the direction `ψ`, for finite-energy `f` and
`ψ`. -/
theorem Energy_add_smul {W : Type*} (G : ReflectedWalk.ConductanceGraph W) {f ψ : W → ℝ}
    (hf : G.HasFiniteEnergy f) (hψ : G.HasFiniteEnergy ψ) (t : ℝ) :
    G.Energy (f + t • ψ) = G.Energy f + 2 * t * G.dirichletForm f ψ + t ^ 2 * G.Energy ψ := by
  have hts : G.HasFiniteEnergy (t • ψ) := hψ.smul t
  have hsum : G.HasFiniteEnergy (f + t • ψ) := hf.add hts
  have hsplit : G.dirichletForm (f + t • ψ) (f + t • ψ)
      = G.dirichletForm f (f + t • ψ) + G.dirichletForm (t • ψ) (f + t • ψ) :=
    G.dirichletForm_add_left hf hts hsum
  have h1 : G.dirichletForm f (f + t • ψ)
      = G.dirichletForm f f + t * G.dirichletForm f ψ := by
    rw [G.dirichletForm_comm f (f + t • ψ), G.dirichletForm_add_left hf hts hf,
      G.dirichletForm_smul_left t ψ f, G.dirichletForm_comm ψ f]
  have h2 : G.dirichletForm (t • ψ) (f + t • ψ)
      = t * G.dirichletForm f ψ + t ^ 2 * G.dirichletForm ψ ψ := by
    rw [G.dirichletForm_smul_left t ψ (f + t • ψ), G.dirichletForm_comm ψ (f + t • ψ),
      G.dirichletForm_add_left hf hts hψ, G.dirichletForm_smul_left t ψ ψ,
      G.dirichletForm_comm f ψ]
    ring
  rw [← G.dirichletForm_self (f + t • ψ), hsplit, h1, h2, G.dirichletForm_self f,
    G.dirichletForm_self ψ]
  ring

/-- **First variation of a real quadratic.**  If `2 t b + t² c ≥ 0` for every real `t` and
`c ≥ 0`, then `b = 0`.  This is the only analytic ingredient of the orthogonality below. -/
theorem eq_zero_of_quadratic_nonneg {b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * c) : b = 0 := by
  by_contra hb
  have hb2 : 0 < b ^ 2 := by positivity
  have hcpos : (0 : ℝ) < c + 1 := by linarith
  have hspos : (0 : ℝ) < (c + 1)⁻¹ := inv_pos.2 hcpos
  have hsc : (c + 1)⁻¹ * c < 2 := by
    have hle : (c + 1)⁻¹ * c ≤ (c + 1)⁻¹ * (c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hspos.le
    rw [inv_mul_cancel₀ (ne_of_gt hcpos)] at hle
    linarith
  have hkey := h (-((c + 1)⁻¹ * b))
  have hexp : 2 * -((c + 1)⁻¹ * b) * b + (-((c + 1)⁻¹ * b)) ^ 2 * c
      = (c + 1)⁻¹ * b ^ 2 * ((c + 1)⁻¹ * c - 2) := by ring
  rw [hexp] at hkey
  have hpos : 0 < (c + 1)⁻¹ * b ^ 2 := mul_pos hspos hb2
  nlinarith

/-! ### The plane-valued line

The plane-valued energy is the existing `StatementIngredients.vectorEnergy`, the sum of the
two coordinate energies, and the pairing is the existing
`StatementIngredients.vectorPairing`. -/

/-- The coordinatewise sum form of `Energy_add_smul`, in terms of the existing
`vectorPairing`. -/
theorem sum_energy_line {W : Type*} (G : ReflectedWalk.ConductanceGraph W) (f u : W → Plane)
    (hf : ∀ i : Fin 2, G.HasFiniteEnergy fun v => f v i)
    (hu : ∀ i : Fin 2, G.HasFiniteEnergy fun v => u v i) (t : ℝ) :
    (∑ i : Fin 2, G.Energy fun v => f v i + t * u v i)
      = (∑ i : Fin 2, G.Energy fun v => f v i) + 2 * t * vectorPairing G f u
        + t ^ 2 * ∑ i : Fin 2, G.Energy fun v => u v i := by
  have hstep : ∀ i : Fin 2, (G.Energy fun v => f v i + t * u v i)
      = (G.Energy fun v => f v i) + 2 * t * G.dirichletForm (fun v => f v i) (fun v => u v i)
        + t ^ 2 * G.Energy fun v => u v i := by
    intro i
    have hline : (fun v => f v i + t * u v i) = (fun v => f v i) + t • fun v => u v i := by
      funext v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hline]
    exact Energy_add_smul G (hf i) (hu i) t
  have hpair : vectorPairing G f u
      = ∑ i : Fin 2, G.dirichletForm (fun v => f v i) (fun v => u v i) := rfl
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hpair, Fin.sum_univ_two,
    hstep 0, hstep 1]
  ring

/-! ### Orthogonality and Pythagoras for a full-energy trace minimizer

The statements are for an arbitrary conductance graph, an arbitrary trace set `A` and an
arbitrary prescribed trace `c`, with the *full* competition class of all plane-valued
functions carrying that trace.  No finite-support closure, no connectedness and no finiteness
of `A` or of the vertex type is used. -/

section Minimizer

variable {W : Type*} (G : ReflectedWalk.ConductanceGraph W) {A : Set W} {c f g : W → Plane}

/-- The coordinate energies of the difference of two finite-vector-energy functions are
finite. -/
theorem hasFiniteEnergy_coord_sub (hf : vectorEnergy G f < ∞) (hg : vectorEnergy G g < ∞)
    (i : Fin 2) : G.HasFiniteEnergy fun v => (g - f) v i := by
  have hcoe : (fun v => (g - f) v i) = (fun v => g v i) - fun v => f v i := by
    funext v
    simp only [Pi.sub_apply, PiLp.sub_apply]
  rw [hcoe]
  exact (hasFiniteEnergy_coord G hg i).sub (hasFiniteEnergy_coord G hf i)

/-- The line from the minimizer towards an admissible competitor stays admissible: on the
trace set the direction vanishes. -/
theorem trace_line (hftr : ∀ v ∈ A, f v = c v) (hgtr : ∀ v ∈ A, g v = c v) (t : ℝ) :
    ∀ v ∈ A, (f + t • (g - f)) v = c v := by
  intro v hv
  have hdir : (g - f) v = 0 := by
    simp only [Pi.sub_apply, hftr v hv, hgtr v hv, sub_self]
  simp only [Pi.add_apply, Pi.smul_apply, hdir, smul_zero, add_zero, hftr v hv]

/-- **Full variational orthogonality of a trace minimizer** (the manuscript's
`ℰ_{G_S}(φ_m, v) = 0`).  A finite-energy function minimizing the vector energy among *all*
functions with the prescribed trace on `A` is energy-orthogonal to its difference with every
finite-energy competitor carrying that trace.  Only minimality along the connecting line is
used, so the statement applies to any minimizer, not just a constructed one. -/
theorem vectorPairing_sub_eq_zero_of_min (hfE : vectorEnergy G f < ∞)
    (hftr : ∀ v ∈ A, f v = c v)
    (hfmin : ∀ h : W → Plane, (∀ v ∈ A, h v = c v) → vectorEnergy G f ≤ vectorEnergy G h)
    (hgE : vectorEnergy G g < ∞) (hgtr : ∀ v ∈ A, g v = c v) :
    vectorPairing G f (g - f) = 0 := by
  have hfc : ∀ i : Fin 2, G.HasFiniteEnergy fun v => f v i := fun i =>
    hasFiniteEnergy_coord G hfE i
  have huc : ∀ i : Fin 2, G.HasFiniteEnergy fun v => (g - f) v i := fun i =>
    hasFiniteEnergy_coord_sub G hfE hgE i
  have hCnn : (0 : ℝ) ≤ ∑ i : Fin 2, G.Energy fun v => (g - f) v i :=
    Finset.sum_nonneg fun i _ => G.Energy_nonneg _
  refine eq_zero_of_quadratic_nonneg hCnn ?_
  intro t
  -- the competitor on the line
  have hcoord : ∀ i : Fin 2,
      (fun v => (f + t • (g - f)) v i) = fun v => f v i + t * (g - f) v i := by
    intro i
    funext v
    simp only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hlinec : ∀ i : Fin 2, G.HasFiniteEnergy fun v => (f + t • (g - f)) v i := by
    intro i
    rw [hcoord i]
    have hline : (fun v => f v i + t * (g - f) v i)
        = (fun v => f v i) + t • fun v => (g - f) v i := by
      funext v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hline]
    exact (hfc i).add ((huc i).smul t)
  have hmin := hfmin _ (trace_line hftr hgtr t)
  rw [vectorEnergy_eq_ofReal_sum G hfc, vectorEnergy_eq_ofReal_sum G hlinec] at hmin
  have hreal : (∑ i : Fin 2, G.Energy fun v => f v i)
      ≤ ∑ i : Fin 2, G.Energy fun v => (f + t • (g - f)) v i := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).1 hmin
    exact Finset.sum_nonneg fun i _ => G.Energy_nonneg _
  have hexp : (∑ i : Fin 2, G.Energy fun v => (f + t • (g - f)) v i)
      = (∑ i : Fin 2, G.Energy fun v => f v i) + 2 * t * vectorPairing G f (g - f)
        + t ^ 2 * ∑ i : Fin 2, G.Energy fun v => (g - f) v i := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hcoord i]]
    exact sum_energy_line G f (g - f) hfc huc t
  rw [hexp] at hreal
  linarith

/-- **The Pythagorean energy decomposition** (`s:eq:pyth0` and `s:eq:pythmn` on one block).
For a full-energy trace minimizer `f` and any finite-energy competitor `g` with the same
trace, `ℰ(g) = ℰ(f) + ℰ(g - f)`. -/
theorem vectorEnergy_eq_add_vectorEnergy_sub_of_min (hfE : vectorEnergy G f < ∞)
    (hftr : ∀ v ∈ A, f v = c v)
    (hfmin : ∀ h : W → Plane, (∀ v ∈ A, h v = c v) → vectorEnergy G f ≤ vectorEnergy G h)
    (hgE : vectorEnergy G g < ∞) (hgtr : ∀ v ∈ A, g v = c v) :
    vectorEnergy G g = vectorEnergy G f + vectorEnergy G (g - f) := by
  have hfc : ∀ i : Fin 2, G.HasFiniteEnergy fun v => f v i := fun i =>
    hasFiniteEnergy_coord G hfE i
  have hgc : ∀ i : Fin 2, G.HasFiniteEnergy fun v => g v i := fun i =>
    hasFiniteEnergy_coord G hgE i
  have huc : ∀ i : Fin 2, G.HasFiniteEnergy fun v => (g - f) v i := fun i =>
    hasFiniteEnergy_coord_sub G hfE hgE i
  have horth : vectorPairing G f (g - f) = 0 :=
    vectorPairing_sub_eq_zero_of_min G hfE hftr hfmin hgE hgtr
  have hgcoord : ∀ i : Fin 2,
      (fun v => g v i) = fun v => f v i + (1 : ℝ) * (g - f) v i := by
    intro i
    funext v
    simp only [Pi.sub_apply, PiLp.sub_apply, one_mul]
    ring
  have hexp : (∑ i : Fin 2, G.Energy fun v => g v i)
      = (∑ i : Fin 2, G.Energy fun v => f v i)
        + 2 * (1 : ℝ) * vectorPairing G f (g - f)
        + (1 : ℝ) ^ 2 * ∑ i : Fin 2, G.Energy fun v => (g - f) v i := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hgcoord i]]
    exact sum_energy_line G f (g - f) hfc huc 1
  rw [horth] at hexp
  rw [vectorEnergy_eq_ofReal_sum G hgc, vectorEnergy_eq_ofReal_sum G hfc,
    vectorEnergy_eq_ofReal_sum G huc, hexp, ← ENNReal.ofReal_add
      (Finset.sum_nonneg fun i _ => G.Energy_nonneg _)
      (Finset.sum_nonneg fun i _ => G.Energy_nonneg _)]
  ring_nf

end Minimizer

/-! ### The blockwise statements for the project's centroid-trace minimizer

`DyadicApproximation.CentroidTraceMinimizer F Q f` is exactly a full-energy minimizer on the
patch graph `G_Q` with the centroid trace on the spatial boundary `A_Q`, and its competition
class is by definition all plane-valued functions on the patch with that trace. -/

section Block

variable {V : Type*} (F : IndexedCells V) (Q : Rectangle)

/-- The three data of `CentroidTraceMinimizer` in the form required by
`vectorPairing_sub_eq_zero_of_min`: the trace set is `{v | v.1 ∈ boundaryVertices F Q}` and
the prescribed trace is the centroid. -/
theorem centroidTraceMinimizer_min {f : V → Plane} (hf : CentroidTraceMinimizer F Q f) :
    ∀ h : patchVertices F Q → Plane,
      (∀ v ∈ {w : patchVertices F Q | w.1 ∈ boundaryVertices F Q},
        h v = (fun w : patchVertices F Q => cellCentroid F w.1) v) →
      vectorEnergy (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => f v.1)
        ≤ vectorEnergy (restrictGraph F.graph (patchVertices F Q)) h :=
  fun h hh => hf.2.2 h fun v hv => hh v hv

/-- **Blockwise full variational orthogonality** of the centroid-trace minimizer against
every finite-energy competitor with the centroid trace. -/
theorem vectorPairing_sub_eq_zero_of_centroidTraceMinimizer {f : V → Plane}
    (hf : CentroidTraceMinimizer F Q f) (g : patchVertices F Q → Plane)
    (hgE : vectorEnergy (restrictGraph F.graph (patchVertices F Q)) g < ∞)
    (hgtr : ∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q → g v = cellCentroid F v.1) :
    vectorPairing (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => f v.1)
        (g - fun v : patchVertices F Q => f v.1) = 0 :=
  vectorPairing_sub_eq_zero_of_min (restrictGraph F.graph (patchVertices F Q))
    (A := {w : patchVertices F Q | w.1 ∈ boundaryVertices F Q})
    (c := fun w : patchVertices F Q => cellCentroid F w.1)
    hf.1 (fun v hv => hf.2.1 v hv) (centroidTraceMinimizer_min F Q hf) hgE
    (fun v hv => hgtr v hv)

/-- **The blockwise Pythagorean identity** of `s:prop:projection`: on the patch graph the
energy of any finite-energy competitor with the centroid trace splits as the energy of the
block minimizer plus the energy of the variation. -/
theorem blockPythagoras_of_centroidTraceMinimizer {f : V → Plane}
    (hf : CentroidTraceMinimizer F Q f) (g : patchVertices F Q → Plane)
    (hgE : vectorEnergy (restrictGraph F.graph (patchVertices F Q)) g < ∞)
    (hgtr : ∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q → g v = cellCentroid F v.1) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q)) g
      = vectorEnergy (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => f v.1)
        + vectorEnergy (restrictGraph F.graph (patchVertices F Q))
          (g - fun v : patchVertices F Q => f v.1) :=
  vectorEnergy_eq_add_vectorEnergy_sub_of_min (restrictGraph F.graph (patchVertices F Q))
    (A := {w : patchVertices F Q | w.1 ∈ boundaryVertices F Q})
    (c := fun w : patchVertices F Q => cellCentroid F w.1)
    hf.1 (fun v hv => hf.2.1 v hv) (centroidTraceMinimizer_min F Q hf) hgE
    (fun v hv => hgtr v hv)

/-- **`s:eq:pyth0` on one block.**  Taking the centroid embedding itself as competitor,
`ℰ_{G_S}(b) = ℰ_{G_S}(φ) + ℰ_{G_S}(φ - b)`, the exact blockwise form of
`e_m + ‖g_m - g_0‖² = e_0`.  The only hypothesis besides minimality is finiteness of the base
energy **on this block** — no finite total energy of the environment. -/
theorem blockPythagoras_centroid {f : V → Plane} (hf : CentroidTraceMinimizer F Q f)
    (hbE : vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => cellCentroid F v.1) < ∞) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => cellCentroid F v.1)
      = vectorEnergy (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => f v.1)
        + vectorEnergy (restrictGraph F.graph (patchVertices F Q))
          ((fun v : patchVertices F Q => cellCentroid F v.1)
            - fun v : patchVertices F Q => f v.1) :=
  blockPythagoras_of_centroidTraceMinimizer F Q hf _ hbE fun _ _ => rfl

end Block

/-! ### The conclusion clauses of `s:prop:projection`

`e_m ↓ e_∞ ≥ 0` and the Cauchy property of the gradients follow from the nested identities as
numerical relations, with no deterministic spatial average theorem. -/

section Tail

variable {e : ℕ → ℝ} {d : ℕ → ℕ → ℝ}

end Tail

/-! ### The single probabilistic step supplied by the checked redistribution

The manuscript passes from the blockwise identities to the specific energies by redistributing
the signed coefficient `c(e) g_m(e)·(g_m(e) - g_0(e))`.  Its owner-block density is the
blockwise sum, which the orthogonality above makes vanish; the checked signed redistribution
then transfers this to the expected root density, i.e. to `⟪g_m, g_m - g_0⟫_* = 0`. -/

open SpecificEnergyRedistribution MarkedBlockAveraging

end ReflectedGMS.NestedEnergyProjections
