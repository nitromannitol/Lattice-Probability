import LatticeProb.Bonanno.BouRabeeGwynne.JointExcursionPasting
import LatticeProb.Bonanno.BouRabeeGwynne.WalkCanonicalStopping
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteProbability

/-! # Observable distance between pasted excursion curves -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- Pairs whose pasted walk curve differs from the observed curve by more
than the indicated uniform distance. -/
def pastedDistanceBad {d n : ℕ} (P : TimePartition n) (e : ℝ) :
    Set ((ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)) :=
  {p | e < dist (pastedWalkCurve P p.1) p.2}

lemma measurableSet_pastedDistanceBad {d n : ℕ} (P : TimePartition n) (e : ℝ) :
    MeasurableSet (pastedDistanceBad (d := d) P e) :=
  measurableSet_lt measurable_const
    (((measurable_pastedWalkCurve P).comp measurable_fst).dist measurable_snd)

lemma pastedDistance_le_of_not_mem {d n : ℕ} (P : TimePartition n) {e : ℝ}
    {p : (ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)}
    (hp : p ∉ pastedDistanceBad P e) (t : unitInterval) :
    dist (pastedWalkCurve P p.1 t) (p.2 t) ≤ e :=
  (ContinuousMap.dist_apply_le_dist t).trans (le_of_not_gt hp)

/-- The observable distance failure has at most the probability of the
finite good-excursion failure in the full joint law. -/
theorem pastedDistanceBad_map_le_failure
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (hd : 1 ≤ d)
    (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) {n : ℕ} (P : TimePartition n)
    {a R S e : ℝ}
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a) (hpoint : R + a + S ≤ e)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        pos B initial select ω i).2 ∈ curveOscillationLe R)
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S) :
    ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
      initial v z).map (fun p => (p.1, pastedBrownianCurve P p.2)))
        (pastedDistanceBad P e) ≤
      N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
        {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} := by
  have hmap : Measurable (fun p : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) => (p.1, pastedBrownianCurve P p.2)) :=
    measurable_fst.prodMk ((measurable_pastedBrownianCurve P).comp measurable_snd)
  rw [Measure.map_apply hmap (measurableSet_pastedDistanceBad P e)]
  apply measure_mono_ae
  filter_upwards [N.walkBrownianJointLaw_ae_pasted_dist_le hd pos hinj B hB W hW hWb μ hμ
    select hs m E hE hdE hBA hA haccess initial v z P hdiam hnear hwrange hbrange] with p hp
  intro hbad
  by_contra hgood
  have hg : ∀ i ≤ n, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a := by
    intro i hi
    by_contra h
    exact hgood ⟨i, hi, h⟩
  have hc : dist (pastedWalkCurve P p.1) (pastedBrownianCurve P p.2) ≤ e :=
    ContinuousMap.dist_le_iff_of_nonempty.mpr (fun t => (hp hg t).trans hpoint)
  exact (not_lt_of_ge hc) hbad

end LatticeProb
end
