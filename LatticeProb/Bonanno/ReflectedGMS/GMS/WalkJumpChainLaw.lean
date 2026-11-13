/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.WalkJumpChainLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkStepPath

/-!
# The law of the jump chain of a reflected walk without explosion

Let `𝓧` be a continuous-time random walk reflected off infinity (`IsReflectedWalk`, Gwynne–Sung
Theorem 1.6) whose paths are almost surely step paths under `P_z` — i.e. almost surely the walk
never explodes.  Then its jump chain (`jumpChainOf 𝓧.X z`, the values at the successive exit times)
is the discrete-time simple random walk started at `z`: its cylinder probabilities are
`1{g 0 = z} · ∏_{j<n} c(g j, g (j+1)) / π(g j)` (`measure_jumpChainOf_cyl`), and it is an
a.e.-measurable random sequence (`aemeasurable_jumpChainOf`).

## Reuse

This is the uniqueness proof's Step 1 (`ReflectedWalk.Theorem16.measure_embeddedCyl`, the law of
the embedded chain of the recursion (3.31) at the level of a finite set `Gn`), applied with `Gn`
the finite set of the first `n + 1` prescribed states: while the walk stays in `Gn` the recursion
(3.31) is the pure exit-time recursion (`mem_embeddedCyl_iff_exitSeq`), and inside `Gn` the kernel
(3.2) of (3.31) is `c(x,y)/π(x)` (`ConductanceGraph.transProb_of_mem`).  No new strong-Markov
argument is made.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ReflectedGMS.GMS.WalkStepPath

open ReflectedWalk ReflectedWalk.Theorem16

universe u

section Law

variable {V : Type u}

open Classical in
/-- The finite set of the first `n + 1` prescribed states. -/
noncomputable def cylSupport (g : ℕ → V) (n : ℕ) : Finset V := (Finset.range (n + 1)).image g

theorem mem_cylSupport (g : ℕ → V) {n i : ℕ} (hi : i ≤ n) : g i ∈ cylSupport g n := by
  classical
  unfold cylSupport
  convert Finset.mem_image_of_mem g (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

theorem cylSupport_nonempty (g : ℕ → V) (n : ℕ) : (cylSupport g n).Nonempty :=
  ⟨g 0, mem_cylSupport g (Nat.zero_le n)⟩

variable {Ω : Type u} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V} {P : Measure Ω}

/-- **The cylinder events of the jump chain are, almost surely, the skeleton's cylinder events.** -/
theorem ae_jumpChainCyl_eq_embeddedCyl (v₀ : V)
    (hstep : ∀ᵐ ω ∂P, ∃ (J : ℕ → V) (s : ℕ → ℝ≥0), IsStepPath (fun t => X t ω) J s)
    (g : ℕ → V) (n : ℕ) :
    {ω | ∀ j ≤ n, jumpChainOf X v₀ ω j = g j} =ᵐ[P] embeddedCyl X (cylSupport g n) g n := by
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [hstep] with ω hω
  obtain ⟨J, s, hs⟩ := hω
  rw [mem_embeddedCyl_iff_exitSeq (fun i hi => mem_cylSupport g hi.le) ω]
  simp only [Set.mem_setOf_eq, jumpChainOf_of_isStepPath hs, mem_stopEvent_exitSeq_iff hs]

variable [Countable V] {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {𝓧 : ProcessFamily V}

/-- The skeleton's cylinder events are null-measurable. -/
theorem nullMeasurableSet_embeddedCyl (h : IsReflectedWalk G w hmin 𝓧) (z : V) (Gn : Finset V)
    (g : ℕ → V) (n : ℕ) : NullMeasurableSet (embeddedCyl 𝓧.X Gn g n) (𝓧.P z) := by
  induction n with
  | zero => exact nullMeasurableSet_stopEvent_stepTime h z (h z).2.2.2.1 Gn 0 (g 0)
  | succ n ih =>
    exact ih.inter (nullMeasurableSet_stopEvent_stepTime h z (h z).2.2.2.1 Gn (n + 1) (g (n + 1)))

open Classical in
/-- **The jump chain of a non-explosive reflected walk is the simple random walk**: cylinder
probabilities `1{g 0 = z} · ∏_{j<n} c(g j, g (j+1)) / π(g j)`. -/
theorem measure_jumpChainOf_cyl (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hstep : ∀ᵐ ω ∂𝓧.P z, ∃ (J : ℕ → V) (s : ℕ → ℝ≥0), IsStepPath (fun t => 𝓧.X t ω) J s)
    (g : ℕ → V) (n : ℕ) :
    𝓧.P z {ω | ∀ j ≤ n, jumpChainOf 𝓧.X z ω j = g j} =
      (if g 0 = z then 1 else 0) *
        ∏ j ∈ Finset.range n, ENNReal.ofReal (G.c (g j) (g (j + 1)) / G.pi (g j)) := by
  rw [measure_congr (ae_jumpChainCyl_eq_embeddedCyl z hstep g n),
    measure_embeddedCyl h hG z (fun x => (h x).2.2.2.1) (cylSupport_nonempty g n) g n]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [G.transProb_of_mem hG (mem_cylSupport g (Nat.le_of_lt (Finset.mem_range.1 hj)))]

/-- The jump chain's cylinder events are null-measurable. -/
theorem nullMeasurableSet_jumpChainOf_cyl (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hstep : ∀ᵐ ω ∂𝓧.P z, ∃ (J : ℕ → V) (s : ℕ → ℝ≥0), IsStepPath (fun t => 𝓧.X t ω) J s)
    (g : ℕ → V) (n : ℕ) :
    NullMeasurableSet {ω | ∀ j ≤ n, jumpChainOf 𝓧.X z ω j = g j} (𝓧.P z) :=
  (nullMeasurableSet_embeddedCyl h z _ g n).congr (ae_jumpChainCyl_eq_embeddedCyl z hstep g n).symm

/-- **The jump chain is an a.e.-measurable random sequence.** -/
theorem aemeasurable_jumpChainOf [MeasurableSpace V] [MeasurableSingletonClass V]
    (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hstep : ∀ᵐ ω ∂𝓧.P z, ∃ (J : ℕ → V) (s : ℕ → ℝ≥0), IsStepPath (fun t => 𝓧.X t ω) J s) :
    AEMeasurable (jumpChainOf 𝓧.X z) (𝓧.P z) := by
  refine AEMeasurable.of_eval fun i => NullMeasurable.aemeasurable ?_
  have hsing : ∀ x : V, NullMeasurableSet {ω | jumpChainOf 𝓧.X z ω i = x} (𝓧.P z) := by
    intro x
    have hset : {ω | jumpChainOf 𝓧.X z ω i = x} = ⋃ p : Fin i → V,
        {ω | ∀ j ≤ i, jumpChainOf 𝓧.X z ω j =
          (fun j => if hj : j < i then p ⟨j, hj⟩ else x) j} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hω
        refine ⟨fun j => jumpChainOf 𝓧.X z ω j, fun j hj => ?_⟩
        by_cases hji : j < i
        · simp [hji]
        · have hj' : j = i := le_antisymm hj (not_lt.1 hji)
          subst hj'
          simp [hω]
      · rintro ⟨p, hp⟩
        simpa using hp i le_rfl
    rw [hset]
    exact NullMeasurableSet.iUnion fun p => nullMeasurableSet_jumpChainOf_cyl h z hstep _ i
  intro S _
  have hpre : (fun ω => jumpChainOf 𝓧.X z ω i) ⁻¹' S =
      ⋃ x ∈ S, {ω | jumpChainOf 𝓧.X z ω i = x} := by
    ext ω
    simp
  rw [hpre]
  exact NullMeasurableSet.biUnion S.to_countable fun x _ => hsing x

end Law

end ReflectedGMS.GMS.WalkStepPath

open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry measure_jumpChainOf_cyl
open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry aemeasurable_jumpChainOf

#print axioms ReflectedGMS.GMS.WalkStepPath.ae_jumpChainCyl_eq_embeddedCyl
#print axioms ReflectedGMS.GMS.WalkStepPath.measure_jumpChainOf_cyl
#print axioms ReflectedGMS.GMS.WalkStepPath.nullMeasurableSet_jumpChainOf_cyl
#print axioms ReflectedGMS.GMS.WalkStepPath.aemeasurable_jumpChainOf
