/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2FlipLimit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Coupling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2TraceLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SubdivLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsP2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitMeasurable

 















set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {W : Type*} [Fintype W] [DecidableEq W] (G : WiredConductances W)

 
def circExcursions (Pc : Set (Finset W)) : Set (Excursion W) :=
  {γ | ∃ c ∈ Pc, ∀ x ∈ c, ∃ j, γ.2 j = x}

open Classical in
 

theorem soupCirc_lower (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) (Pc : Set (Finset W)) :
    1 - Real.exp (-(t * ∑' γ, (circExcursions Pc).indicator G.excursionWeight γ)) ≤
      ∑' s, G.soupMassAt t s * (if EdgeGraph.SoupCirc Pc s then 1 else 0) := by
  have hmass := G.hasSum_soupMassAt hK ht
  have havoid := hasSum_soupMass_avoid G.excursionWeight_nonneg (G.hasSum_excursionWeight hK) ht
    (circExcursions Pc)
  have hsub := hmass.sub havoid
  have hnn : ∀ s, 0 ≤ G.soupMassAt t s * (if EdgeGraph.SoupCirc Pc s then 1 else 0) := fun s =>
    mul_nonneg (G.soupMassAt_nonneg ht s) (by split_ifs <;> norm_num)
  have hle : ∀ s, G.soupMassAt t s * (if EdgeGraph.SoupCirc Pc s then 1 else 0) ≤
      G.soupMassAt t s := fun s => by
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact G.soupMassAt_nonneg ht s
  have hsum : Summable fun s => G.soupMassAt t s * (if EdgeGraph.SoupCirc Pc s then 1 else 0) :=
    Summable.of_nonneg_of_le hnn hle hmass.summable
  refine hasSum_le (fun s => ?_) hsub hsum.hasSum
  by_cases hs : ∀ i, s.2 i ∉ circExcursions Pc
  · rw [Set.indicator_of_mem (show s ∈ {s : Soup (Excursion W) | ∀ i, s.2 i ∉ circExcursions Pc}
      from hs), show soupMass G.excursionWeight (∑ i, G.boundary i) t s = G.soupMassAt t s from rfl,
      sub_self]
    exact hnn s
  · rw [Set.indicator_of_notMem (show s ∉ {s : Soup (Excursion W) | ∀ i, s.2 i ∉
      circExcursions Pc} from hs), sub_zero]
    push_neg at hs
    obtain ⟨i, c, hc, hci⟩ := hs
    have hS : EdgeGraph.SoupCirc Pc s :=
      ⟨c, hc, fun x hx => (EdgeGraph.soupVisitCount_ne_zero_iff s x).mpr
        (by obtain ⟨j, hj⟩ := hci x hx; exact ⟨i, j, hj⟩)⟩
    rw [if_pos hS, mul_one]

end WiredConductances

 

def boxAroundSets (n M : ℕ) : Set (Finset (EdgeGraph.SubV (DGFFSite n) (BoxHE n) M)) :=
  (fun p : List (DGFFSite n) => p.toFinset.image Sum.inl) '' {p | IsDGFFAroundPath n p}

 
def HasAroundPath (n : ℕ) (S : Finset (DGFFSite n)) : Prop :=
  ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ ∀ z ∈ p, z ∈ S

theorem not_hasAroundPath_empty (n : ℕ) : ¬ HasAroundPath n ∅ := by
  rintro ⟨p, hp, hpS⟩
  obtain ⟨z, w, hz, -, -⟩ := hp.2.2.2.1
  exact Finset.notMem_empty z (hpS z (List.mem_of_mem_head? hz))

 
def boxCircuitMass (n : ℕ) : ℝ :=
  ∑' γ : Excursion (DGFFSite n),
    {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ

 
theorem subdiv_circuitMass (n M : ℕ) (hM : 2 ≤ M) :
    ∑' γ, (WiredConductances.circExcursions (boxAroundSets n M)).indicator
        ((boxEdgeGraph n).subdiv M hM).toWired.excursionWeight γ = boxCircuitMass n := by
  classical
  have h1 : ∀ γ : Excursion (EdgeGraph.SubV (DGFFSite n) (BoxHE n) M),
      (WiredConductances.circExcursions (boxAroundSets n M)).indicator
        ((boxEdgeGraph n).subdiv M hM).toWired.excursionWeight γ =
      if HasAroundPath n (EdgeGraph.traceSet M γ) then
        ((boxEdgeGraph n).subdiv M hM).toWired.excursionWeight γ else 0 := by
    intro γ
    have hiff : γ ∈ WiredConductances.circExcursions (boxAroundSets n M) ↔
        HasAroundPath n (EdgeGraph.traceSet M γ) := by
      simp only [WiredConductances.circExcursions, boxAroundSets, Set.mem_setOf_eq,
        Set.mem_image, HasAroundPath, EdgeGraph.mem_traceSet]
      constructor
      · rintro ⟨c, ⟨p, hp, rfl⟩, hc⟩
        refine ⟨p, hp, fun z hz => ?_⟩
        obtain ⟨j, hj⟩ := hc (Sum.inl z) (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hz))
        exact ⟨j, hj⟩
      · rintro ⟨p, hp, hpS⟩
        refine ⟨_, ⟨p, hp, rfl⟩, fun x hx => ?_⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        exact hpS z (List.mem_toFinset.mp hz)
    by_cases h : HasAroundPath n (EdgeGraph.traceSet M γ)
    · rw [if_pos h, Set.indicator_of_mem (hiff.mpr h)]
    · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (hiff.mp h'))]
  rw [tsum_congr h1, EdgeGraph.tsum_trace_event (boxEdgeGraph n) M hM (boxEdgeGraph_posDef n)
    (HasAroundPath n) (not_hasAroundPath_empty n), boxEdgeGraph_toWired]
  unfold boxCircuitMass
  apply tsum_congr
  intro γ
  have hiff : HasAroundPath n γ.visitSet ↔ ExcursionEncircles n γ := by
    simp only [HasAroundPath, ExcursionEncircles, Excursion.Visits, Excursion.mem_visitSet]
  by_cases h : HasAroundPath n γ.visitSet
  · rw [if_pos h, Set.indicator_of_mem (show γ ∈ {γ | ExcursionEncircles n γ} from hiff.mp h)]
  · rw [if_neg h, Set.indicator_of_notMem
      (show γ ∉ {γ | ExcursionEncircles n γ} from fun h' => h (hiff.mpr h'))]

 
def boxCircuitEvent (n : ℕ) (u : ℝ) : Set (EuclideanSpace ℝ (DGFFSite n)) :=
  {h | ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ ∀ z ∈ p, -u ≤ h z}

theorem boxDGFF_eq_gff (n : ℕ) : boxDGFF n = (boxEdgeGraph n).toWired.gff := by
  unfold boxDGFF WiredConductances.gaussianOfPrecision WiredConductances.gff
  rw [boxEdgeGraph_toWired]

theorem preimage_boxCircuitEvent (n M : ℕ) (u : ℝ) :
    (EdgeGraph.restrictInl (V := DGFFSite n) (E := BoxHE n) M) ⁻¹' boxCircuitEvent n u =
      (· + WiredConductances.constVec u) ⁻¹' EdgeGraph.circEvent (boxAroundSets n M) := by
  ext φ
  simp only [boxCircuitEvent, EdgeGraph.circEvent, boxAroundSets, Set.mem_preimage,
    Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨p, hp, hpu⟩
    refine ⟨_, ⟨p, hp, rfl⟩, fun x hx => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have := hpu z (List.mem_toFinset.mp hz)
    have h1 : ((EdgeGraph.restrictInl (V := DGFFSite n) (E := BoxHE n) M) φ) z =
      φ (Sum.inl z) := rfl
    have h2 : (φ + (WiredConductances.constVec u :
        EuclideanSpace ℝ (EdgeGraph.SubV (DGFFSite n) (BoxHE n) M))) (Sum.inl z) =
      φ (Sum.inl z) + u := rfl
    rw [h2]; rw [h1] at this
    linarith
  · rintro ⟨c, ⟨p, hp, rfl⟩, hc⟩
    refine ⟨p, hp, fun z hz => ?_⟩
    have := hc (Sum.inl z) (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hz))
    have h1 : ((EdgeGraph.restrictInl (V := DGFFSite n) (E := BoxHE n) M) φ) z =
      φ (Sum.inl z) := rfl
    have h2 : (φ + (WiredConductances.constVec u :
        EuclideanSpace ℝ (EdgeGraph.SubV (DGFFSite n) (BoxHE n) M))) (Sum.inl z) =
      φ (Sum.inl z) + u := rfl
    rw [h2] at this; rw [h1]
    linarith

 

theorem boxCircuit_lower_M (n M : ℕ) (hM : 2 ≤ M) {u : ℝ} (hu : 0 < u) :
    1 - Real.exp (-(u ^ 2 / 2 * boxCircuitMass n)) - etaBox n M hM u ≤
      (boxDGFF n).real (boxCircuitEvent n u) := by
  set Γ := boxEdgeGraph n
  set ΓM := Γ.subdiv M hM
  have hK : Γ.toWired.precision.PosDef := boxEdgeGraph_posDef n
  have hKM : ΓM.toWired.precision.PosDef := Γ.subdiv_posDef M hM hK
  have hmeasE : MeasurableSet (boxCircuitEvent n u) := measurableSet_dgffCircuitEvent n u
  have hlaw : (boxDGFF n).real (boxCircuitEvent n u) =
      (ΓM.toWired.shiftLaw u).real (EdgeGraph.circEvent (boxAroundSets n M)) := by
    rw [boxDGFF_eq_gff, ← Γ.gff_subdiv_map_restrict M hM hK,
      map_measureReal_apply (EdgeGraph.restrictInl M).continuous.measurable hmeasE,
      preimage_boxCircuitEvent, WiredConductances.shiftLaw,
      map_measureReal_apply (measurable_add_const _) (EdgeGraph.measurableSet_circEvent _)]
  rw [hlaw]
  have hcoup := ΓM.shiftLaw_circEvent_lower hKM hu.le (boxAroundSets n M)
  have hflip := ΓM.tsum_disSum_le hKM hu.le
  have hsoup := ΓM.toWired.soupCirc_lower hKM (t := u ^ 2 / 2) (by positivity) (boxAroundSets n M)
  rw [subdiv_circuitMass n M hM] at hsoup
  have heta : (∑ e, (EdgeGraph.vertexAvg ΓM (ΓM.cond e) u (u ^ 2 / 2) (ΓM.tail e) +
      EdgeGraph.vertexAvg ΓM (ΓM.cond e) u (u ^ 2 / 2) (ΓM.head e))) = etaBox n M hM u := rfl
  rw [heta] at hflip
  linarith

 
theorem boxCircuit_lower (n : ℕ) {u : ℝ} (hu : 0 < u) :
    1 - Real.exp (-(u ^ 2 / 2 * boxCircuitMass n)) ≤
      (boxDGFF n).real (boxCircuitEvent n u) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨M, hM, hη⟩ := etaBox_small n hu hε
  have := boxCircuit_lower_M n M hM hu
  linarith

 

theorem dgffCircuitLower_of_circuitMass (hmass : InputsP2.CircuitMass) :
    Inputs.DGFFCircuitLower := by
  obtain ⟨m, hm, hmn⟩ := hmass
  refine ⟨m / 2, by positivity, fun n hn u hu => ?_⟩
  have hb := boxCircuit_lower n hu
  have hexp : Real.exp (-(u ^ 2 / 2 * boxCircuitMass n)) ≤ Real.exp (-(m / 2) * u ^ 2) := by
    rw [Real.exp_le_exp]
    have := hmn n hn
    have hu2 : 0 ≤ u ^ 2 / 2 := by positivity
    have : u ^ 2 / 2 * m ≤ u ^ 2 / 2 * boxCircuitMass n := mul_le_mul_of_nonneg_left this hu2
    nlinarith
  rw [← ofReal_measureReal (μ := boxDGFF n) (s := {h | ∃ p : List (DGFFSite n),
    IsDGFFAroundPath n p ∧ ∀ z ∈ p, -u ≤ h z}) (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (by
    have : (boxDGFF n).real (boxCircuitEvent n u) = (boxDGFF n).real {h | ∃ p : List (DGFFSite n),
      IsDGFFAroundPath n p ∧ ∀ z ∈ p, -u ≤ h z} := rfl
    linarith)

end SupercriticalLQGUniqueness.B2.QPos
