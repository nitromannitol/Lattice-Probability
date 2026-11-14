/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesClock8
import LatticeProb.Prob.KernelDeterminedFunctional

/-!
# A single functional determines the inverse crossing clock

Let `K : E → Prob C(ℝ≥0, E)` be a continuous family of path laws with the Markov property at
deterministic times, started at `z` (`K z`-a.s. `x 0 = z`).  Write `A_t(x)` for the inverse crossing
clock of `x` (`pathClockInv m x t`) and `B(x)` for `x` read in its crossing clock
(`t ↦ clockPath m x t`).  Suppose that under each `K z`:

* the crossing clock is almost surely good, and the shift identity at `A_t` holds for each `t, s`;
* for a fixed `s`, `A_s` is almost surely a measurable function of the rational-time restriction of
  `B(x)` (the function may depend on the start `z`).

Then there is a single measurable functional `F` on `ℝ≥0 → E` (independent of `z` and `t`) with
`A_s = F (B x)` almost surely under every `K z`, and
`A_{t+s} = A_t + F (B x (t + ·))` almost surely under every `K z`, for every `t`
(`exists_clockFunctional`).  The first part is the parametrised determination lemma
(`exists_measurable_of_kernel_ae_eq_fun`); the second is the strong Markov property at the optional
time `A_t` (`strongMarkov_pathClockInv`) applied to the first at the random start `x (A_t)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The restriction of a path to the rational times (through `ratTime`). -/
def ratPath (b : ℝ≥0 → E) : ℚ → E := fun r => b (ratTime r)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- The path read in its crossing clock starts at the starting point of the path. -/
theorem clockPath_zero (m : ℝ≥0∞) (x : C(ℝ≥0, E)) :
    clockPath m (fun u => x u) 0 = x 0 := by
  unfold clockPath
  rw [clockInv_zero]
  simp

omit [SecondCountableTopology E] in
/-- **One functional determines the inverse crossing clock under every start.** -/
theorem exists_clockFunctional [PolishSpace E]
    {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    (hM : ∀ z t, MarkovAt K z t) (m : ℝ≥0∞)
    (hstart : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), x 0 = z)
    (hgood : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), GoodClock (crossClock m fun u => x u))
    (hshift : ∀ z (t s : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ShiftIdentity m t s x)
    (s : ℝ≥0)
    (hdet : ∀ z, ∃ g : (ℚ → E) → ℝ, Measurable g ∧
      ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
        (pathClockInv m x s).toReal = g (ratPath fun t => clockPath m (fun u => x u) t)) :
    ∃ F : (ℝ≥0 → E) → ℝ, Measurable F ∧
      (∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
        (pathClockInv m x s).toReal = F fun t => clockPath m (fun u => x u) t) ∧
      ∀ z (t : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
        (pathClockInv m x (t + s)).toReal = (pathClockInv m x t).toReal +
          F fun q => clockPath m (fun u => x u) (t + q) := by
  -- the kernel and the determining functional
  let kE : Kernel E C(ℝ≥0, E) :=
    ⟨fun z => (K z : Measure C(ℝ≥0, E)), measurable_measure_comp_of_continuous hK measurable_id⟩
  have : IsMarkovKernel kE :=
    ⟨fun z => by
      show IsProbabilityMeasure (K z : Measure C(ℝ≥0, E))
      infer_instance⟩
  have hU : Measurable fun x : C(ℝ≥0, E) => ratPath fun t => clockPath m (fun u => x u) t :=
    measurable_pi_iff.2 fun r => measurable_clockPath m (ratTime r)
  have hV : Measurable fun x : C(ℝ≥0, E) => (pathClockInv m x s).toReal :=
    (measurable_pathClockInv m s).ennreal_toReal
  have hUV := hU.prodMk hV
  have : IsMarkovKernel (kE.map fun x : C(ℝ≥0, E) =>
      (ratPath fun t => clockPath m (fun u => x u) t, (pathClockInv m x s).toReal)) :=
    Kernel.IsMarkovKernel.map kE hUV
  obtain ⟨G, hGm, hG⟩ := exists_measurable_of_kernel_ae_eq_fun
    (kE.map fun x : C(ℝ≥0, E) =>
      (ratPath fun t => clockPath m (fun u => x u) t, (pathClockInv m x s).toReal))
    (fun z => by
      obtain ⟨g, hg, hgz⟩ := hdet z
      refine ⟨g, hg, ?_⟩
      rw [Kernel.map_apply kE hUV z]
      exact (ae_map_iff hUV.aemeasurable
        (measurableSet_eq_fun measurable_snd (hg.comp measurable_fst))).2 hgz)
  obtain ⟨F, hFdef⟩ : ∃ F : (ℝ≥0 → E) → ℝ, ∀ b, F b = G (b 0, ratPath b) := ⟨_, fun _ => rfl⟩
  have hFm : Measurable F := by
    have : F = fun b => G (b 0, ratPath b) := funext hFdef
    rw [this]
    exact hGm.comp ((measurable_pi_apply 0).prodMk
      (measurable_pi_iff.2 fun r => measurable_pi_apply (ratTime r)))
  have hFcongr : ∀ b b' : ℝ≥0 → E, b 0 = b' 0 → (∀ r : ℚ, b (ratTime r) = b' (ratTime r)) →
      F b = F b' := by
    intro b b' h0 hr
    rw [hFdef, hFdef, h0]
    congr 2
    funext r
    exact hr r
  -- the first claim, under every start
  have h1 : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      (pathClockInv m x s).toReal = F fun t => clockPath m (fun u => x u) t := by
    intro z
    have hz := hG z
    rw [Kernel.map_apply kE hUV z] at hz
    have hz' := ae_of_ae_map hUV.aemeasurable hz
    filter_upwards [hz', hstart z] with x hx hx0
    rw [hFdef, clockPath_zero, hx0]
    exact hx
  refine ⟨F, hFm, h1, fun z t => ?_⟩
  -- the second claim: strong Markov at `A_t`
  have hBf : Measurable fun x : C(ℝ≥0, E) => fun t => clockPath m (fun u => x u) t :=
    measurable_pi_iff.2 fun t => measurable_clockPath m t
  set Z : Set C(ℝ≥0, E) :=
    {y | (pathClockInv m y s).toReal ≠ F fun t => clockPath m (fun u => y u) t} with hZdef
  have hZ : MeasurableSet Z :=
    (measurableSet_eq_fun hV (hFm.comp hBf)).compl
  have hfin : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), pathClockInv m x t < ⊤ :=
    (hgood z).mono fun x hx => GoodClock.clockInv_lt_top hx t
  have hT : Measurable fun x : C(ℝ≥0, E) => (pathClockInv m x t).toNNReal :=
    (measurable_pathClockInv m t).ennreal_toNNReal
  have hsh : Measurable fun x : C(ℝ≥0, E) => pathShift x (pathClockInv m x t).toNNReal :=
    continuous_pathShift_uncurry.measurable.comp (measurable_id.prodMk hT)
  have hgm : Measurable fun p : C(ℝ≥0, E) × C(ℝ≥0, E) => Z.indicator (fun _ => (1 : ℝ)) p.2 :=
    (measurable_const.indicator hZ).comp measurable_snd
  have hSM := strongMarkov_pathClockInv hK (hM z) m t hfin hgm (C := 1) (fun p => by
    by_cases h : p.2 ∈ Z <;> simp [h])
  have hR : ∀ y : E, ∫ w, Z.indicator (fun _ => (1 : ℝ)) w ∂(K y : Measure C(ℝ≥0, E)) = 0 := by
    intro y
    refine integral_eq_zero_of_ae ((h1 y).mono fun w hw => ?_)
    have hw' : w ∉ Z := fun hmem => hmem hw
    simp [hw']
  have hint : Integrable (fun x : C(ℝ≥0, E) =>
      Z.indicator (fun _ => (1 : ℝ)) (pathShift x (pathClockInv m x t).toNNReal))
      (K z : Measure C(ℝ≥0, E)) :=
    Integrable.of_bound ((measurable_const.indicator hZ).comp hsh).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        by_cases h : pathShift x (pathClockInv m x t).toNNReal ∈ Z <;> simp [h])
  have hLzero : ∫ x, Z.indicator (fun _ => (1 : ℝ))
      (pathShift x (pathClockInv m x t).toNNReal) ∂(K z : Measure C(ℝ≥0, E)) = 0 := by
    dsimp only at hSM
    rw [hSM]
    simp [hR]
  have hae : (fun x : C(ℝ≥0, E) => Z.indicator (fun _ => (1 : ℝ))
      (pathShift x (pathClockInv m x t).toNNReal)) =ᵐ[(K z : Measure C(ℝ≥0, E))] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hint).1 hLzero
  have hnotZ : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      pathShift x (pathClockInv m x t).toNNReal ∉ Z := by
    filter_upwards [hae] with x hx hmem
    simp [Set.indicator_of_mem hmem] at hx
  have hrat : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ∀ r : ℚ, ShiftIdentity m t (ratTime r) x :=
    ae_all_iff.2 fun r => hshift z t (ratTime r)
  filter_upwards [hnotZ, hshift z t s, hrat, hshift z t 0, hgood z] with x hxZ hs hr h0 hgd
  obtain ⟨hAt, hAdd, -⟩ := hs
  have hfinal : pathClockInv m x (t + s) < ⊤ := GoodClock.clockInv_lt_top hgd (t + s)
  rw [hAdd] at hfinal ⊢
  have hAs : pathClockInv m (pathShift x (pathClockInv m x t).toNNReal) s < ⊤ :=
    (ENNReal.add_lt_top.1 hfinal).2
  rw [ENNReal.toReal_add hAt.ne hAs.ne]
  congr 1
  have hxZ' : (pathClockInv m (pathShift x (pathClockInv m x t).toNNReal) s).toReal =
      F fun t' => clockPath m (fun u => pathShift x (pathClockInv m x t).toNNReal u) t' := by
    by_contra hne
    exact hxZ hne
  rw [hxZ']
  refine hFcongr _ _ ?_ ?_
  · exact h0.2.2
  · exact fun r => (hr r).2.2

end LatticeProb
