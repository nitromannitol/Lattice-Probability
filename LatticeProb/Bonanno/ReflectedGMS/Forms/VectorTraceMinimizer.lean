/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VectorTraceMinimizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AnchoredTraceMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicApproximation

/-!
# The vector-valued trace minimizer from the scalar anchored minimizer

The vector energy is the existing `StatementIngredients.vectorEnergy`, the extended-real
sum of the two coordinate energies `energyENN`. Because that sum splits over the two
coordinates, the scalar full-energy minimizer of `AnchoredTraceMinimizer` can be applied in
each coordinate separately and reassembled into a plane-valued function.

The competition class is preserved exactly: every plane-valued function with the prescribed
trace competes, including those of infinite vector energy, for which the inequality is
trivial. No speed-`L²` restriction, finite boundary, finite patch or finite-support closure
is imposed anywhere.

The final specialization to the patch consumer
`DyadicApproximation.CentroidTraceMinimizer` is explicitly conditional on the two
geometric inputs that are *not* proved here: that the restricted patch graph is
`BoundaryAnchored` on its spatial boundary vertices, and that the centroid trace itself has
finite vector energy on the patch.
-/

set_option autoImplicit false

namespace ReflectedGMS

open scoped ENNReal
open StatementIngredients

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Coordinate splitting of the vector energy -/

/-- The defining coordinate sum of the existing vector energy. -/
theorem vectorEnergy_eq_sum (f : V → Plane) :
    vectorEnergy G f = ∑ i : Fin 2, energyENN G (fun v => f v i) := rfl

/-- The vector energy of a function assembled from two scalar coordinates. -/
theorem vectorEnergy_toLp (F : Fin 2 → V → ℝ) :
    vectorEnergy G (fun v => (WithLp.toLp 2 (fun i => F i v) : Plane)) =
      ∑ i : Fin 2, energyENN G (F i) := rfl

/-- Each coordinate of a finite-vector-energy function has finite scalar energy. -/
theorem hasFiniteEnergy_coord {f : V → Plane} (hf : vectorEnergy G f < ∞) (i : Fin 2) :
    G.HasFiniteEnergy (fun v => f v i) := by
  rw [vectorEnergy_eq_sum] at hf
  exact (energyENN_ne_top_iff G _).1 (ENNReal.sum_lt_top.1 hf i (Finset.mem_univ i)).ne

/-- Finite scalar energy in both coordinates gives finite vector energy. -/
theorem vectorEnergy_lt_top_of_coord {f : V → Plane}
    (hf : ∀ i : Fin 2, G.HasFiniteEnergy (fun v => f v i)) : vectorEnergy G f < ∞ := by
  rw [vectorEnergy_eq_sum]
  exact ENNReal.sum_lt_top.2 fun i _ => ((energyENN_ne_top_iff G _).2 (hf i)).lt_top

/-- On finite-energy coordinates the vector energy is the real coordinate sum. -/
theorem vectorEnergy_eq_ofReal_sum {f : V → Plane}
    (hf : ∀ i : Fin 2, G.HasFiniteEnergy (fun v => f v i)) :
    vectorEnergy G f = ENNReal.ofReal (∑ i : Fin 2, G.Energy (fun v => f v i)) := by
  rw [vectorEnergy_eq_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => G.Energy_nonneg _]
  exact Finset.sum_congr rfl fun i _ => energyENN_eq_ofReal_Energy G (hf i)

/-! ### The full vector minimizer with a supplied boundary trace -/

/-- **Existence and uniqueness of the vector trace minimizer.** For an arbitrary supplied
reference function of finite vector energy there is a unique plane-valued function with the
same trace on the whole boundary `A` minimizing the full vector energy against *every*
plane-valued competitor with that trace. Each coordinate is the scalar anchored minimizer,
and coordinatewise minimality gives minimality of the sum; conversely a minimizer of the
sum must be coordinatewise minimal, because the coordinate inequalities are simultaneous
and the totals agree. -/
theorem existsUnique_vector_trace_minimizer {A : Set V} (hA : BoundaryAnchored G A)
    {u : V → Plane} (hu : vectorEnergy G u < ∞) :
    ∃! f : V → Plane, vectorEnergy G f < ∞ ∧ (∀ a ∈ A, f a = u a) ∧
      ∀ g : V → Plane, (∀ a ∈ A, g a = u a) →
        vectorEnergy G f ≤ vectorEnergy G g := by
  choose F hFE hFtrace _hForth hFmin using fun i : Fin 2 =>
    exists_anchored_trace_minimizer G hA (hasFiniteEnergy_coord G hu i)
  have hfin : vectorEnergy G (fun v => (WithLp.toLp 2 (fun i => F i v) : Plane)) < ∞ := by
    rw [vectorEnergy_toLp]
    exact ENNReal.sum_lt_top.2 fun i _ => ((energyENN_ne_top_iff G _).2 (hFE i)).lt_top
  have htrace : ∀ a ∈ A, (WithLp.toLp 2 (fun i => F i a) : Plane) = u a := fun a ha =>
    PiLp.ext fun i => hFtrace i a ha
  have hmin : ∀ g : V → Plane, (∀ a ∈ A, g a = u a) →
      vectorEnergy G (fun v => (WithLp.toLp 2 (fun i => F i v) : Plane)) ≤ vectorEnergy G g := by
    intro g hg
    rcases eq_or_ne (vectorEnergy G g) ∞ with hginf | hgfin
    · rw [hginf]
      exact le_top
    · have hgc : ∀ i : Fin 2, G.HasFiniteEnergy (fun v => g v i) := fun i =>
        hasFiniteEnergy_coord G hgfin.lt_top i
      rw [vectorEnergy_toLp, vectorEnergy_eq_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [energyENN_eq_ofReal_Energy G (hFE i), energyENN_eq_ofReal_Energy G (hgc i)]
      exact ENNReal.ofReal_le_ofReal
        (hFmin i _ (hgc i) fun a ha => by rw [hg a ha])
  refine ⟨fun v => (WithLp.toLp 2 (fun i => F i v) : Plane), ⟨hfin, htrace, hmin⟩, ?_⟩
  rintro f' ⟨hf'fin, hf'trace, hf'min⟩
  have hf'c : ∀ i : Fin 2, G.HasFiniteEnergy (fun v => f' v i) := fun i =>
    hasFiniteEnergy_coord G hf'fin i
  have hEeq : vectorEnergy G f' =
      vectorEnergy G (fun v => (WithLp.toLp 2 (fun i => F i v) : Plane)) :=
    le_antisymm (hf'min _ htrace) (hmin f' hf'trace)
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      G.Energy (F i) ≤ G.Energy (fun v => f' v i) := fun i _ =>
    hFmin i _ (hf'c i) fun a ha => by rw [hf'trace a ha]
  have hofReal : ENNReal.ofReal (∑ i : Fin 2, G.Energy (F i)) =
      ENNReal.ofReal (∑ i : Fin 2, G.Energy (fun v => f' v i)) := by
    calc ENNReal.ofReal (∑ i : Fin 2, G.Energy (F i))
        = vectorEnergy G (fun v => (WithLp.toLp 2 (fun i => F i v) : Plane)) := by
          rw [vectorEnergy_toLp, ENNReal.ofReal_sum_of_nonneg fun i _ => G.Energy_nonneg _]
          exact Finset.sum_congr rfl fun i _ => (energyENN_eq_ofReal_Energy G (hFE i)).symm
      _ = vectorEnergy G f' := hEeq.symm
      _ = ENNReal.ofReal (∑ i : Fin 2, G.Energy (fun v => f' v i)) :=
          vectorEnergy_eq_ofReal_sum G hf'c
  have hsum : ∑ i : Fin 2, G.Energy (F i) = ∑ i : Fin 2, G.Energy (fun v => f' v i) :=
    (ENNReal.ofReal_eq_ofReal_iff
      (Finset.sum_nonneg fun i _ => G.Energy_nonneg _)
      (Finset.sum_nonneg fun i _ => G.Energy_nonneg _)).1 hofReal
  have hEcoord : ∀ i : Fin 2, G.Energy (F i) = G.Energy (fun v => f' v i) := fun i =>
    (Finset.sum_eq_sum_iff_of_le hle).1 hsum i (Finset.mem_univ i)
  have hcoordeq : ∀ i : Fin 2, (fun v => f' v i) = F i := by
    intro i
    refine (existsUnique_anchored_trace_minimizer G hA
      (hasFiniteEnergy_coord G hu i)).unique ⟨hf'c i, ?_, ?_⟩ ⟨hFE i, hFtrace i, hFmin i⟩
    · intro a ha
      rw [hf'trace a ha]
    · intro h hh htr
      rw [← hEcoord i]
      exact hFmin i h hh htr
  funext v
  exact PiLp.ext fun i => congrFun (hcoordeq i) v

/-- Existence form of the vector trace minimizer. -/
theorem exists_vector_trace_minimizer {A : Set V} (hA : BoundaryAnchored G A)
    {u : V → Plane} (hu : vectorEnergy G u < ∞) :
    ∃ f : V → Plane, vectorEnergy G f < ∞ ∧ (∀ a ∈ A, f a = u a) ∧
      ∀ g : V → Plane, (∀ a ∈ A, g a = u a) →
        vectorEnergy G f ≤ vectorEnergy G g :=
  (existsUnique_vector_trace_minimizer G hA hu).exists

/-! ### Specialization to the patch consumer -/

/-- Extend a function defined on a vertex subset to the whole vertex type. -/
noncomputable def subtypeExtend {S : Set V} (f : S → Plane) : V → Plane :=
  Function.extend Subtype.val f (fun _ => 0)

theorem subtypeExtend_apply {S : Set V} (f : S → Plane) (v : S) :
    subtypeExtend f v.1 = f v :=
  Subtype.val_injective.extend_apply f (fun _ => 0) v

theorem subtypeExtend_comp {S : Set V} (f : S → Plane) :
    (fun v : S => subtypeExtend f v.1) = f :=
  funext fun v => subtypeExtend_apply f v

end ReflectedGMS
