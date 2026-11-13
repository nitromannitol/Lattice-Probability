/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Events at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Radii
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFDistanceMeasurable

 














set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

 
def distEvent (m : ℕ) (ξ R : ℝ) : Set (EuclideanSpace ℝ (DGFFSite m)) :=
  {g | R ≤ dgffAnnulusDistance m ξ g}

 
def highCircuit (m : ℕ) (u : ℝ) : Set (EuclideanSpace ℝ (DGFFSite m)) :=
  {g | ∃ p : List (DGFFSite m), IsDGFFAroundPath m p ∧ ∀ c ∈ p, -u ≤ g c}

 
def lowCircuit (m : ℕ) (u : ℝ) : Set (EuclideanSpace ℝ (DGFFSite m)) :=
  {g | ∃ p : List (DGFFSite m), IsDGFFAroundPath m p ∧ ∀ c ∈ p, g c ≤ u}

theorem pathCost_congr {m : ℕ} (ξ : ℝ) {g g' : EuclideanSpace ℝ (DGFFSite m)}
    {p : List (DGFFSite m)} (h : ∀ c ∈ p, g c = g' c) :
    dgffPathCost m ξ g p = dgffPathCost m ξ g' p := by
  unfold dgffPathCost inclusivePathCost
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [h c hc]

theorem distEvent_annDet (m : ℕ) (ξ R : ℝ) : AnnDet (distEvent m ξ R) := by
  intro g g' hgg'
  have : dgffAnnulusDistance m ξ g = dgffAnnulusDistance m ξ g' := by
    unfold dgffAnnulusDistance
    congr 1
    funext p
    exact pathCost_congr ξ fun c hc => hgg' c (p.2.2.1 c hc)
  simp only [distEvent, Set.mem_setOf_eq, this]

theorem lowCircuit_annDet (m : ℕ) (u : ℝ) : AnnDet (lowCircuit m u) := by
  intro g g' hgg'
  simp only [lowCircuit, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, hpu⟩
    exact ⟨p, hp, fun c hc => by rw [← hgg' c (hp.2.2.1 c hc)]; exact hpu c hc⟩
  · rintro ⟨p, hp, hpu⟩
    exact ⟨p, hp, fun c hc => by rw [hgg' c (hp.2.2.1 c hc)]; exact hpu c hc⟩

theorem distEvent_measurable (m : ℕ) (ξ R : ℝ) : MeasurableSet (distEvent m ξ R) :=
  measurableSet_le measurable_const (measurable_dgffAnnulusDistance m ξ)

theorem highCircuit_measurable (m : ℕ) (u : ℝ) : MeasurableSet (highCircuit m u) :=
  measurableSet_dgffCircuitEvent m u

theorem lowCircuit_eq_neg (m : ℕ) (u : ℝ) :
    lowCircuit m u = (fun g => -g) ⁻¹' highCircuit m u := by
  ext g
  simp only [lowCircuit, highCircuit, Set.mem_setOf_eq, Set.mem_preimage, PiLp.neg_apply,
    neg_le_neg_iff]

theorem lowCircuit_measurable (m : ℕ) (u : ℝ) : MeasurableSet (lowCircuit m u) := by
  rw [lowCircuit_eq_neg]
  exact measurable_neg (highCircuit_measurable m u)

 

theorem lowCircuit_prob {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) (u : ℝ) :
    boxDGFF n (tresCLM hk ⁻¹' lowCircuit (n - k) u) = boxDGFF (n - k) (highCircuit (n - k) u) := by
  rw [← tres_prob_neg hk (highCircuit_measurable (n - k) u)]
  congr 1
  rw [lowCircuit_eq_neg]
  rfl

 

 
def axisPath (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) : List (DGFFSite n) :=
  List.ofFn fun i : Fin (dgffOuterRadius n - dgffInnerRadius n) =>
    ⟨(σ * ((dgffInnerRadius n : ℤ) + 1 + i), 0), by
      have hlt := dgffOuterRadius_lt_box n
      have hi := i.2
      rw [mem_interiorSites_iff]
      unfold interiorRadius
      have hpow : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by norm_cast
      have h1 : ((dgffInnerRadius n : ℤ) + 1 + i) ≤ (2 : ℤ) ^ n - 1 := by omega
      have h0 : (0 : ℤ) ≤ (dgffInnerRadius n : ℤ) + 1 + i := by positivity
      rcases hσ with rfl | rfl
      · simp only [one_mul, Prod.fst, Prod.snd]; omega
      · simp only [neg_one_mul, Prod.fst, Prod.snd]; omega⟩

theorem axisPath_crossing (n : ℕ) (hn : 4 ≤ n) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    IsDGFFAnnulusPath n (axisPath n σ hσ) := by
  have hgap := dgff_radius_gap n hn
  set L := dgffOuterRadius n - dgffInnerRadius n
  have hL : 0 < L := by omega
  have hrad : ∀ i : Fin L, latticeRadius ((axisPath n σ hσ)[i.1]'(by
      simp only [axisPath, List.length_ofFn]; exact i.2) ).1 = dgffInnerRadius n + 1 + i.1 := by
    intro i
    simp only [axisPath, List.getElem_ofFn, latticeRadius]
    rcases hσ with rfl | rfl
    · simp only [one_mul]
      have : (((dgffInnerRadius n : ℤ) + 1 + i)).natAbs = dgffInnerRadius n + 1 + i := by omega
      rw [this]; simp
    · simp only [neg_one_mul, Int.natAbs_neg]
      have : (((dgffInnerRadius n : ℤ) + 1 + i)).natAbs = dgffInnerRadius n + 1 + i := by omega
      rw [this]; simp
  have hne : axisPath n σ hσ ≠ [] := by simp [axisPath, List.ofFn_eq_nil_iff]; omega
  refine ⟨?_, ?_, (axisPath n σ hσ).head hne, (axisPath n σ hσ).getLast hne,
    List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne, ?_, ?_⟩
  · rw [axisPath, List.isChain_ofFn]
    intro i hi
    rcases hσ with rfl | rfl
    · left; simp; ring
    · right; left; simp; ring
  · intro c hc
    rw [axisPath, List.mem_ofFn] at hc
    obtain ⟨i, rfl⟩ := hc
    have := hrad i
    simp only [axisPath, List.getElem_ofFn] at this
    unfold inDGFFAnnulus
    rw [this]
    have := i.2
    omega
  · rw [List.head_eq_getElem]
    have := hrad ⟨0, hL⟩
    simpa using this
  · rw [List.getLast_eq_getElem]
    have hlen : (axisPath n σ hσ).length = L := by simp [axisPath, L]
    have := hrad ⟨L - 1, by omega⟩
    simp only [hlen] at this ⊢
    rw [this]
    omega

theorem mem_axisPath_fst {n : ℕ} {σ : ℤ} {hσ : σ = 1 ∨ σ = -1} {c : DGFFSite n}
    (hc : c ∈ axisPath n σ hσ) : (dgffInnerRadius n : ℤ) + 1 ≤ σ * c.1.1 := by
  rw [axisPath, List.mem_ofFn] at hc
  obtain ⟨i, rfl⟩ := hc
  simp only
  rcases hσ with rfl | rfl
  · simp
  · simp [neg_mul]

 

theorem around_far_vertex (n : ℕ) (hn : 4 ≤ n) {p : List (DGFFSite n)}
    (hp : IsDGFFAroundPath n p) (z : ℤ × ℤ) :
    ∃ c ∈ p, 2 ^ (n - 1) < latticeRadius (c.1 - z) := by
  obtain ⟨e, he, hepath⟩ := hp.2.2.2.2 _ (axisPath_crossing n hn 1 (Or.inl rfl))
  obtain ⟨w, hw, hwpath⟩ := hp.2.2.2.2 _ (axisPath_crossing n hn (-1) (Or.inr rfl))
  have h1 := mem_axisPath_fst hepath
  have h2 := mem_axisPath_fst hwpath
  simp only [one_mul, neg_one_mul] at h1 h2
  unfold dgffInnerRadius at h1 h2
  have he1 := fst_natAbs_le_latticeRadius (e.1 - z)
  have hw1 := fst_natAbs_le_latticeRadius (w.1 - z)
  simp only [Prod.fst_sub] at he1 hw1
  by_contra hc
  push_neg at hc
  have hce := hc e he
  have hcw := hc w hw
  have hpow : ((2 ^ (n - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n - 1) := by norm_cast
  omega

end SupercriticalLQGUniqueness.B2.QPos.P5
