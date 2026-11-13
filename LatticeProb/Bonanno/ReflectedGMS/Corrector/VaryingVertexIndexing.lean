/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.VaryingVertexIndexing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly
import LatticeProb.Bonanno.ReflectedGMS.Forms.VectorTraceMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteDirichletEnergyLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyTraceBounds

/-!
# ℕ-indexing of the varying vertex type, and coordinatewise vectorization

Two foundations that every block-interpolant measurability packet needs.

## (1) The varying vertex type is a full subgraph of one fixed ℕ-indexed graph

The block problem lives on `Code.Vertex ω.1.val = {n : ℕ // (ω.1.val.1 n).isSome}`, a type
that **depends on the sample point**.  That dependence is what defeats every existing
measurability lemma in the project: `Corrector/MeasurableBlockMinimizer`,
`Corrector/MeasurableInfinitePatchMinimizer` and
`Corrector/MinimizerStrongGradientConvergence` are all stated for one *fixed* countable
vertex type.

The repair is that the dependence is only apparent.  `Vertex r` is a **subtype of `ℕ`**, and
`AdmissibleConductance.absent` says the raw conductance `r.2` already vanishes whenever
either endpoint is an absent slot.  So the raw conductance matrix `r.2 : ℕ → ℕ → ℝ` is itself
a `ConductanceGraph ℕ` — `natGraph` — in which `Vertex r` sits by `Subtype.val` as a *full*
subgraph carrying all of the conductance.  Energy therefore transfers **unconditionally and
in both directions**: `energyENN`, `Energy`, `HasFiniteEnergy`, `vectorEnergy` and
`restrictedEnergy` of a ℕ-indexed field equal those of its restriction to `Vertex r`, with no
summability, finiteness or support hypothesis anywhere (`energyENN_natGraph`,
`Energy_natGraph`, `hasFiniteEnergy_natGraph_iff`, `vectorEnergy_natGraph`,
`restrictedEnergy_natGraph`).  Conversely `natExtend` extends any `Vertex r`-indexed field to
`ℕ` by zero without changing any energy (`vectorEnergy_natExtend`), so nothing is lost by
working on the fixed index type.

Measurability of the indexing is then two facts about the code coordinates and nothing more:
the conductance at each fixed pair of labels is a measurable function of the environment
(`measurable_envNatGraph_c`), and the event that a label is an actual vertex is measurable
(`measurableSet_isVertexLabel`).  Both are immediate from `Code.measurable_inclusion`; the
point is that after the transfer there is nothing else left to make measurable.

## (2) The `Plane`-valued minimization decouples coordinatewise

`Energy` is scalar throughout the project and `s:eq:energy` for `ℝ²` is the dot-product form,
so `E(f) = E(f₁) + E(f₂)`.  `Forms/VectorTraceMinimizer.existsUnique_vector_trace_minimizer`
already exploits this *inside its own proof*; this module turns that into a reusable
statement.  `isVectorTraceMinimizer_iff_coord` is an **unconditional iff** — no anchoring, no
finite reference energy — saying that a plane-valued field solves the trace-minimization
problem exactly when each of its two coordinates solves the scalar one.  The forward
direction is the substantive half: it needs the cancellation
`energyENN_le_of_vectorEnergy_le_coordUpdate`, which replaces one coordinate by a scalar
competitor and cancels the untouched coordinate in `ℝ≥0∞` (legitimate because that coordinate
has finite energy).

`centroidTraceMinimizer_iff` records that `DyadicApproximation.CentroidTraceMinimizer` *is*
this predicate on the patch, and `centroidTraceMinimizer_iff_coord` decouples it.  That is the
established project convention by which rows n=7 and n=8 were justified, now a lemma rather
than a remark.

**This file proves no main theorem.**  It supplies steps (1) and (2) of the block-interpolant
measurability chain; steps (3) measurability of the `W`-bound event and of `Selected` at
arbitrary `s`, and (4) gluing the per-square minimizers, are not attempted here.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.VaryingVertexIndexing

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open FiniteDirichletEnergyLimit FullEnergyTraceBounds

variable {V W : Type*}

/-! ### Transfer of energy along a full embedding of conductance graphs -/

/-- **A full embedding of conductance graphs.**  `i` is injective, carries the conductance of
`G` to that of `H`, and `H` has *no* conductance touching the complement of the image.  The
last clause is what makes the transfer of energy an equality rather than an inequality: every
edge of `H` already lies inside the image. -/
structure IsFullEmbedding (G : ReflectedWalk.ConductanceGraph V)
    (H : ReflectedWalk.ConductanceGraph W) (i : V → W) : Prop where
  /-- The index map is injective. -/
  injective : Function.Injective i
  /-- Conductances agree on the image. -/
  conductance : ∀ v w : V, H.c (i v) (i w) = G.c v w
  /-- No edge of `H` leaves the image. -/
  vanishing : ∀ a b : W, a ∉ Set.range i → H.c a b = 0

namespace IsFullEmbedding

variable {G : ReflectedWalk.ConductanceGraph V} {H : ReflectedWalk.ConductanceGraph W}
  {i : V → W}

/-- The induced map on ordered pairs is injective. -/
theorem prodMap_injective (hi : IsFullEmbedding G H i) :
    Function.Injective fun p : V × V => (i p.1, i p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  simp only [Prod.mk.injEq] at hab ⊢
  exact ⟨hi.injective hab.1, hi.injective hab.2⟩

/-- Off the image the ambient gradient term vanishes, because the ambient conductance does. -/
theorem gradSq_eq_zero_of_notMem_range (hi : IsFullEmbedding G H i) (g : W → ℝ)
    {q : W × W} (hq : q ∉ Set.range fun p : V × V => (i p.1, i p.2)) :
    H.gradSq g q = 0 := by
  have hc : H.c q.1 q.2 = 0 := by
    by_cases h1 : q.1 ∈ Set.range i
    · obtain ⟨a, ha⟩ := h1
      by_cases h2 : q.2 ∈ Set.range i
      · obtain ⟨b, hb⟩ := h2
        exact absurd ⟨(a, b), by show (i a, i b) = q; rw [ha, hb]⟩ hq
      · rw [H.c_symm]
        exact hi.vanishing q.2 q.1 h2
    · exact hi.vanishing q.1 q.2 h1
  simp [ReflectedWalk.ConductanceGraph.gradSq, hc]

theorem support_gradSq_subset (hi : IsFullEmbedding G H i) (g : W → ℝ) :
    Function.support (H.gradSq g) ⊆ Set.range fun p : V × V => (i p.1, i p.2) :=
  Function.support_subset_iff'.2 fun _ hq => hi.gradSq_eq_zero_of_notMem_range g hq

theorem gradSq_apply (hi : IsFullEmbedding G H i) (g : W → ℝ) (p : V × V) :
    H.gradSq g (i p.1, i p.2) = G.gradSq (fun v => g (i v)) p := by
  simp only [ReflectedWalk.ConductanceGraph.gradSq, hi.conductance]

/-- The two gradient sums agree: the ambient sum has no terms outside the image. -/
theorem tsum_gradSq (hi : IsFullEmbedding G H i) (g : W → ℝ) :
    ∑' p : V × V, G.gradSq (fun v => g (i v)) p = ∑' q : W × W, H.gradSq g q := by
  rw [← hi.prodMap_injective.tsum_eq (hi.support_gradSq_subset g)]
  exact tsum_congr fun p => (hi.gradSq_apply g p).symm

/-- **Transfer of the real Dirichlet energy.**  No finiteness hypothesis. -/
theorem Energy_comp (hi : IsFullEmbedding G H i) (g : W → ℝ) :
    G.Energy (fun v => g (i v)) = H.Energy g := by
  unfold ReflectedWalk.ConductanceGraph.Energy
  rw [hi.tsum_gradSq g]

/-- **Transfer of finiteness of the energy.** -/
theorem hasFiniteEnergy_comp_iff (hi : IsFullEmbedding G H i) (g : W → ℝ) :
    G.HasFiniteEnergy (fun v => g (i v)) ↔ H.HasFiniteEnergy g := by
  have hiff := hi.prodMap_injective.summable_iff (f := H.gradSq g)
    fun q hq => hi.gradSq_eq_zero_of_notMem_range g hq
  have hfun : (H.gradSq g ∘ fun p : V × V => (i p.1, i p.2))
      = G.gradSq (fun v => g (i v)) := funext fun p => hi.gradSq_apply g p
  rw [hfun] at hiff
  exact hiff

/-- **Transfer of the extended-real energy.**  No finiteness hypothesis. -/
theorem energyENN_comp (hi : IsFullEmbedding G H i) (g : W → ℝ) :
    energyENN G (fun v => g (i v)) = energyENN H g := by
  have hsupp : Function.support (fun q : W × W => ENNReal.ofReal (H.gradSq g q))
      ⊆ Set.range fun p : V × V => (i p.1, i p.2) :=
    Function.support_subset_iff'.2 fun q hq => by
      rw [hi.gradSq_eq_zero_of_notMem_range g hq, ENNReal.ofReal_zero]
  unfold energyENN
  rw [← hi.prodMap_injective.tsum_eq hsupp]
  congr 1
  exact tsum_congr fun p => congrArg ENNReal.ofReal (hi.gradSq_apply g p).symm

/-- **Transfer of the plane-valued energy.** -/
theorem vectorEnergy_comp (hi : IsFullEmbedding G H i) (g : W → Plane) :
    vectorEnergy G (fun v => g (i v)) = vectorEnergy H g := by
  rw [vectorEnergy_eq_sum, vectorEnergy_eq_sum]
  exact Finset.sum_congr rfl fun j _ => hi.energyENN_comp fun w => (g w).ofLp j

end IsFullEmbedding

/-! ### The fixed ℕ-indexing of the varying vertex type -/

/-- **The conductance graph of a raw code, carried on the fixed index type `ℕ`.**  The
conductance matrix is the raw one; `AdmissibleConductance.absent` already makes it vanish at
absent slots, so no masking is needed. -/
def natGraph (r : RawCode) (h : AdmissibleConductance r) :
    ReflectedWalk.ConductanceGraph ℕ where
  c := r.2
  c_symm := h.symm
  c_nonneg := h.nonneg
  c_self := h.self
  summable_c n := summable_of_hasFiniteSupport (h.finiteRow n)

@[simp] theorem natGraph_c (r : RawCode) (h : AdmissibleConductance r) (n m : ℕ) :
    (natGraph r h).c n m = r.2 n m := rfl

@[simp] theorem decodeRaw_graph_c (r : RawCode) (h : AdmissibleConductance r)
    (v w : Vertex r) : (decodeRaw r h).graph.c v w = r.2 v.val w.val := rfl

/-- **The varying vertex type is a full subgraph of the fixed ℕ-indexed graph.**  This is the
statement that removes the sample-point dependence of the vertex type. -/
theorem isFullEmbedding_natGraph (r : RawCode) (h : AdmissibleConductance r) :
    IsFullEmbedding (decodeRaw r h).graph (natGraph r h) (Subtype.val : Vertex r → ℕ) where
  injective := Subtype.val_injective
  conductance := fun _ _ => rfl
  vanishing := by
    intro a b ha
    refine h.absent a b (Or.inl ?_)
    rw [← Option.not_isSome_iff_eq_none]
    intro hsome
    exact ha ⟨⟨a, hsome⟩, rfl⟩

/-! #### Back from the varying type to the fixed one -/

/-- Extend a field on the varying vertex type to the fixed index type by zero. -/
noncomputable def natExtend {r : RawCode} {α : Type*} [Zero α] (f : Vertex r → α) : ℕ → α :=
  Function.extend Subtype.val f fun _ => 0

theorem natExtend_apply {r : RawCode} {α : Type*} [Zero α] (f : Vertex r → α) (v : Vertex r) :
    natExtend f v.val = f v :=
  Subtype.val_injective.extend_apply f _ v

theorem natExtend_comp {r : RawCode} {α : Type*} [Zero α] (f : Vertex r → α) :
    (fun v : Vertex r => natExtend f v.val) = f :=
  funext (natExtend_apply f)

/-! #### Restricted (patch) versions -/

/-! ### The ℕ-indexing at a valid environment, and its measurability -/

/-- The ℕ-indexed conductance graph of a valid environment. -/
noncomputable def envNatGraph (e : Env) : ReflectedWalk.ConductanceGraph ℕ :=
  natGraph e.val e.property.choose

@[simp] theorem envNatGraph_c (e : Env) (n m : ℕ) : (envNatGraph e).c n m = e.val.2 n m := rfl

theorem isFullEmbedding_envNatGraph (e : Env) :
    IsFullEmbedding (decode e).graph (envNatGraph e) (Subtype.val : Vertex e.val → ℕ) :=
  isFullEmbedding_natGraph e.val e.property.choose

theorem Energy_envNatGraph (e : Env) (g : ℕ → ℝ) :
    (decode e).graph.Energy (fun v : Vertex e.val => g v.val) = (envNatGraph e).Energy g :=
  (isFullEmbedding_envNatGraph e).Energy_comp g

theorem hasFiniteEnergy_envNatGraph_iff (e : Env) (g : ℕ → ℝ) :
    (decode e).graph.HasFiniteEnergy (fun v : Vertex e.val => g v.val)
      ↔ (envNatGraph e).HasFiniteEnergy g :=
  (isFullEmbedding_envNatGraph e).hasFiniteEnergy_comp_iff g

/-- **The ℕ-indexing is measurable: at every fixed pair of labels the conductance is a
measurable function of the environment.** -/
theorem measurable_envNatGraph_c (n m : ℕ) :
    Measurable fun e : Env => (envNatGraph e).c n m := by
  have hEq : (fun e : Env => (envNatGraph e).c n m) = fun e : Env => e.val.2 n m := rfl
  rw [hEq]
  exact (measurable_pi_apply m).comp
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_inclusion))

theorem measurable_markedNatGraph_c (n m : ℕ) :
    Measurable fun ω : MarkedEnvironment => (envNatGraph ω.1).c n m :=
  (measurable_envNatGraph_c n m).comp measurable_fst

/-! ### Coordinatewise vectorization of the trace-minimization problem -/

/-! #### The patch problem of the block interpolation specification -/

end ReflectedGMS.VaryingVertexIndexing
