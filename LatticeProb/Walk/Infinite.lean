/-
The law of simple random walk and of the lazy walk on infinite paths.

`LatticeProb.Walk.Path` carries the law of the first `n` steps as a probability
mass function on the finite type of words.  Here the same walk is built on
infinite paths, as the product measure `Measure.infinitePi` of the one-step
laws, which is Mathlib's form of the Ionescu-Tulcea construction for an
independent family.  `pathLaw_map_take` identifies the two: the law of the first
`n` coordinates of the infinite path is the law of the first `n` steps.  Both
sides live on a finite discrete space, so the identification is a comparison of
singletons, and the singleton of the infinite path law is a cylinder whose
measure is the product of the one-step masses.

The lazy walk holds with probability `1/2` and otherwise steps to a uniform
neighbour, so its one-step law is carried by `Option (Dir d)`, the extra point
being the hold.  Its transition operator on functions is the `Q` of
`LatticeProb.Walk.Lazy`, and `LatticeProb.Q_eq_pushforward` is the statement
that averaging a function over the neighbours and pushing a measure forward by
one step are the same operator.
-/
import LatticeProb.Walk.Path

noncomputable section

namespace LatticeProb

open MeasureTheory

/-! ### One step -/

/-- The law of one step of simple random walk: a uniform direction. -/
noncomputable def stepLaw (d : ℕ) [NeZero d] : Measure (Dir d) :=
  (PMF.uniformOfFintype (Dir d)).toMeasure

instance stepLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (stepLaw d) := by
  unfold stepLaw; infer_instance

theorem stepLaw_singleton (d : ℕ) [NeZero d] (a : Dir d) :
    stepLaw d {a} = (((2 * d : ℕ) : ENNReal))⁻¹ := by
  rw [stepLaw, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton a),
    PMF.uniformOfFintype_apply]
  congr 2
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-! ### Infinite paths -/

/-- The law of the infinite path of simple random walk on `ℤ^d`: the steps are
independent uniform directions. -/
noncomputable def pathLaw (d : ℕ) [NeZero d] : Measure (ℕ → Dir d) :=
  Measure.infinitePi fun _ : ℕ => stepLaw d

instance pathLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (pathLaw d) := by
  unfold pathLaw; infer_instance

/-- The steps of the infinite path are independent. -/
theorem iIndepFun_pathLaw (d : ℕ) [NeZero d] :
    ProbabilityTheory.iIndepFun (fun (i : ℕ) (ω : ℕ → Dir d) => ω i) (pathLaw d) :=
  ProbabilityTheory.iIndepFun_infinitePi (X := fun _ a => a) fun _ => measurable_id

/-- Every step of the infinite path is a uniform direction. -/
theorem pathLaw_map_eval (d : ℕ) [NeZero d] (i : ℕ) :
    (pathLaw d).map (fun ω => ω i) = stepLaw d :=
  Measure.infinitePi_map_eval _ i

/-- The joint law of the steps indexed by a finite set is their product law. -/
theorem pathLaw_map_restrict (d : ℕ) [NeZero d] (I : Finset ℕ) :
    (pathLaw d).map I.restrict = Measure.pi fun _ : I => stepLaw d :=
  Measure.infinitePi_map_restrict _

/-- The first `n` steps of an infinite path. -/
def take (d n : ℕ) (ω : ℕ → Dir d) : Fin n → Dir d := fun i => ω i

theorem measurable_take (d n : ℕ) : Measurable (take d n) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

theorem preimage_take_singleton {d n : ℕ} (w : Fin n → Dir d) :
    take d n ⁻¹' {w}
      = Set.pi ↑(Finset.range n) fun i => if h : i < n then {w ⟨i, h⟩} else Set.univ := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe,
    Finset.mem_range]
  constructor
  · intro h i hi
    rw [dif_pos hi, Set.mem_singleton_iff, ← h]
    rfl
  · intro h
    funext i
    have hi := h (i : ℕ) i.isLt
    rw [dif_pos i.isLt, Set.mem_singleton_iff] at hi
    exact hi

/-- The law of the first `n` steps of the infinite path is the law of the first
`n` steps of `LatticeProb.Walk.Path`. -/
theorem pathLaw_map_take (d n : ℕ) [NeZero d] :
    (pathLaw d).map (take d n) = walkLaw d n := by
  refine Measure.ext_of_singleton fun w => ?_
  rw [Measure.map_apply (measurable_take d n) (MeasurableSet.singleton w),
    preimage_take_singleton w, pathLaw,
    Measure.infinitePi_pi _ (fun i _ => by
      by_cases h : i < n
      · rw [dif_pos h]; exact MeasurableSet.singleton _
      · rw [dif_neg h]; exact MeasurableSet.univ)]
  have hterm : ∀ i ∈ Finset.range n,
      stepLaw d (if h : i < n then {w ⟨i, h⟩} else Set.univ)
        = (((2 * d : ℕ) : ENNReal))⁻¹ := by
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi), stepLaw_singleton]
  rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]
  rw [walkLaw, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton w),
    walkPMF_apply]
  rw [← ENNReal.inv_pow]
  congr 1
  push_cast
  ring

/-- The law of the first `n` steps of simple random walk is the product of `n`
copies of the one-step law. -/
theorem walkLaw_eq_pi (d n : ℕ) [NeZero d] :
    walkLaw d n = Measure.pi fun _ : Fin n => stepLaw d := by
  refine Measure.ext_of_singleton fun w => ?_
  have hsing : ({w} : Set (Fin n → Dir d)) = Set.pi Set.univ fun i => {w i} := by
    rw [Set.univ_pi_singleton]
  rw [walkLaw, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton w),
    walkPMF_apply, hsing, Measure.pi_pi]
  simp only [stepLaw_singleton]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.inv_pow]
  congr 1
  push_cast
  ring

/-! ### The lazy walk -/

/-- One step of the lazy walk: `none` is a hold, `some a` a step in the direction
`a`. -/
abbrev LazyDir (d : ℕ) : Type := Option (Dir d)

instance instMeasurableSpaceLazyDir (d : ℕ) : MeasurableSpace (LazyDir d) := ⊤

instance instMeasurableSingletonClassLazyDir (d : ℕ) :
    MeasurableSingletonClass (LazyDir d) := ⟨fun _ => trivial⟩

/-- The displacement of one lazy step. -/
def lazyVec {d : ℕ} (a : LazyDir d) : Site d := a.elim 0 dirVec

@[simp] theorem lazyVec_none {d : ℕ} : lazyVec (none : LazyDir d) = 0 := rfl

@[simp] theorem lazyVec_some {d : ℕ} (a : Dir d) : lazyVec (some a) = dirVec a := rfl

/-- The law of one step of the lazy walk: a hold with probability `1/2`, and
otherwise a uniform direction, so each of the `2d` neighbours has probability
`1/(4d)`. -/
noncomputable def lazyStepLaw (d : ℕ) [NeZero d] : Measure (LazyDir d) :=
  (2 : ENNReal)⁻¹ • Measure.dirac none + (2 : ENNReal)⁻¹ • (stepLaw d).map some

instance lazyStepLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (lazyStepLaw d) := by
  constructor
  have hmap : (Measure.map (some : Dir d → LazyDir d) (stepLaw d)) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  rw [lazyStepLaw, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply,
    Measure.coe_smul, Pi.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, hmap]
  simp only [Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [ENNReal.inv_two_add_inv_two]

/-- The law of one step of the lazy walk on the whole space of lazy directions
determines the position of a lazy path. -/
def lazyPos {d n : ℕ} (w : Fin n → LazyDir d) (k : ℕ) : Site d :=
  ∑ i : Fin n, if (i : ℕ) < k then lazyVec (w i) else 0

/-- The law of the first `n` steps of the lazy walk, as a measure on the finite
type of lazy words. -/
noncomputable def lazyWalkLaw (d n : ℕ) [NeZero d] :
    Measure (Fin n → LazyDir d) :=
  Measure.pi fun _ : Fin n => lazyStepLaw d

instance lazyWalkLaw_isProbabilityMeasure (d n : ℕ) [NeZero d] :
    IsProbabilityMeasure (lazyWalkLaw d n) := by
  unfold lazyWalkLaw; infer_instance

/-- The law of the infinite path of the lazy walk. -/
noncomputable def lazyPathLaw (d : ℕ) [NeZero d] : Measure (ℕ → LazyDir d) :=
  Measure.infinitePi fun _ : ℕ => lazyStepLaw d

instance lazyPathLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (lazyPathLaw d) := by
  unfold lazyPathLaw; infer_instance

/-- The joint law of the lazy steps indexed by a finite set is their product
law. -/
theorem lazyPathLaw_map_restrict (d : ℕ) [NeZero d] (I : Finset ℕ) :
    (lazyPathLaw d).map I.restrict = Measure.pi fun _ : I => lazyStepLaw d :=
  Measure.infinitePi_map_restrict _

/-- Every step of the infinite lazy path has the one-step lazy law. -/
theorem lazyPathLaw_map_eval (d : ℕ) [NeZero d] (i : ℕ) :
    (lazyPathLaw d).map (fun ω => ω i) = lazyStepLaw d :=
  Measure.infinitePi_map_eval _ i

end LatticeProb

end
