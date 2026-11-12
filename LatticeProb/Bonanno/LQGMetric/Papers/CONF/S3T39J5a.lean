/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J5a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Almost sure trace of `σ(A, h|_A)` mod constants (DEC-120 §4–§5, packet J5)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), C:1543–1556 (the iteration
`s_{k+1} = σ^{ε_k}_{s_k,𝕣}`). In `T39JRestData` (S3T39J5) the recursion holds only almost surely
(D119 S5, D120 §5: the events `Cs k` of `T39IRestData` are dropped), so the exact trace lemma
`t39h_inter_localSigma0` (S3T39H3) is needed in an a.s. form: if `A = A'` a.s. on an event `C` of
`σ(A', h|_{A'})` mod constants, every event `E` of `σ(A, h|_A)` mod constants gives an a.s. event
`E ∩ C` of `σ(A', h|_{A'})` mod constants (**`t39j_inter_localSigma0_ae`**).

Copy-and-adapt (credited): `t39j_hullSigma0_succ_le` is `LocalEvent.hullSigma_succ_le`
(Meas/LocalEventRandom) for `hullSigma0` (with `conf36_fieldSigma0On_mono`, S3D114S4);
`t39j_aeEventIn_localSigma0` is `LocalEvent.aeEventIn_localSigma`; the hull-level step is
`t39h_hullSigma0_le_trace` with the exact trace σ-algebra replaced by the a.s. trace `t39jTrAE`
(the `C`-relative version of `t39hAESig`, S3T39H3).
-/

noncomputable section

open MeasureTheory MeasurableSpace Set Filter
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric
namespace CONF

section TraceAE
variable {Ω : Type}

/-- `n ↦ σ(A, h|_{int A^{(n)}})` mod constants is antitone (one step); copy of
`LocalEvent.hullSigma_succ_le` -/
theorem t39j_hullSigma0_succ_le (h : Ω → DistC) {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω))
    (n : ℕ) : hullSigma0 h A (n + 1) ≤ hullSigma0 h A n := by
  refine sup_le le_sup_left (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨S', F, hF, rfl⟩
  by_cases hne : ∃ ω₀, dyadicHull (n + 1) (A ω₀) = S'
  · obtain ⟨ω₀, hω₀⟩ := hne
    set S := dyadicHull n (A ω₀)
    have key : {ω | dyadicHull (n + 1) (A ω) = S'} ∩ F =
        ({ω | dyadicHull n (A ω) = S} ∩ F) ∩ {ω | dyadicHull (n + 1) (A ω) = S'} := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hull_eq_of_hull_succ_eq (h1.trans hω₀.symm), h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩
        exact ⟨h1, h2⟩
    rw [key]
    refine MeasurableSet.inter ?_ ?_
    · have hsub : interior S' ⊆ interior S :=
        interior_mono (hω₀ ▸ hull_succ_subset n (A ω₀))
      have hF' := conf36_fieldSigma0On_mono h hsub F hF
      exact (le_sup_right : _ ≤ hullSigma0 h A n) _
        (MeasurableSpace.measurableSet_generateFrom ⟨S, F, hF', rfl⟩)
    · exact (le_sup_left : _ ≤ hullSigma0 h A n) _ (measurableSet_hull_eq hA (n + 1) S')
  · convert (MeasurableSet.empty : MeasurableSet[hullSigma0 h A n] (∅ : Set Ω)) using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 => absurd ⟨ω, h1⟩ hne

theorem t39j_hullSigma0_anti (h : Ω → DistC) {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) :
    Antitone (hullSigma0 h A) :=
  antitone_nat_of_succ_le (t39j_hullSigma0_succ_le h hA)

/-- a.s.-determination by every `hullSigma0 h A n` gives a.s.-determination by
`localSigma0 h A`; copy of `LocalEvent.aeEventIn_localSigma` -/
theorem t39j_aeEventIn_localSigma0 [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) {E : Set Ω}
    (hE : ∀ n, AEEventIn P (hullSigma0 h A n) E) : AEEventIn P (localSigma0 h A) E := by
  choose F hFm hEF using hE
  refine ⟨⋃ N, ⋂ n, ⋂ (_ : N ≤ n), F n, ?_, ?_⟩
  · rw [localSigma0, MeasurableSpace.measurableSet_iInf]
    intro M
    have heq : (⋃ N, ⋂ n, ⋂ (_ : N ≤ n), F n) = ⋃ N, ⋂ n, ⋂ (_ : max N M ≤ n), F n := by
      ext ω
      simp only [mem_iUnion, mem_iInter]
      constructor
      · rintro ⟨N, hN⟩
        exact ⟨N, fun n hn => hN n ((le_max_left N M).trans hn)⟩
      · rintro ⟨N, hN⟩
        exact ⟨max N M, hN⟩
    rw [heq]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun hn =>
        t39j_hullSigma0_anti h hA ((le_max_right N M).trans hn) _ (hFm n)
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ E ↔ ω ∈ F n) := by
      rw [ae_all_iff]
      intro n
      filter_upwards [hEF n] with ω hω
      exact Iff.of_eq hω
    filter_upwards [hall] with ω hω
    apply propext
    simp only [mem_iUnion, mem_iInter]
    constructor
    · intro hE
      exact ⟨0, fun n _ => (hω n).1 hE⟩
    · rintro ⟨N, hN⟩
      exact (hω N).2 (hN N le_rfl)

variable [m0 : MeasurableSpace Ω]

/-- the **a.s. trace** of `m` on `C`: the sets `S` with `S ∩ C` a.s. equal to `B ∩ C`, `B ∈ m` -/
def t39jTrAE (P : Measure Ω) (m : MeasurableSpace Ω) (C : Set Ω) : MeasurableSpace Ω where
  MeasurableSet' S := ∃ B, MeasurableSet[m] B ∧ S ∩ C =ᵐ[P] B ∩ C
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, EventuallyEq.rfl⟩
  measurableSet_compl S := fun ⟨B, hB, hSB⟩ => ⟨Bᶜ, hB.compl, by
    filter_upwards [hSB] with ω hω
    have h1 : (ω ∈ S ∧ ω ∈ C) = (ω ∈ B ∧ ω ∈ C) := hω
    show (ω ∈ Sᶜ ∧ ω ∈ C) = (ω ∈ Bᶜ ∧ ω ∈ C)
    simp only [mem_compl_iff, eq_iff_iff] at h1 ⊢
    tauto⟩
  measurableSet_iUnion f hf := by
    choose B hB hfB using hf
    refine ⟨⋃ i, B i, MeasurableSet.iUnion hB, ?_⟩
    filter_upwards [ae_all_iff.2 hfB] with ω hω
    have h1 : ∀ i, (ω ∈ f i ∧ ω ∈ C) = (ω ∈ B i ∧ ω ∈ C) := hω
    show (ω ∈ ⋃ i, f i ∧ ω ∈ C) = (ω ∈ ⋃ i, B i ∧ ω ∈ C)
    simp only [mem_iUnion, eq_iff_iff] at h1 ⊢
    constructor
    · rintro ⟨⟨i, hi⟩, hC⟩; exact ⟨⟨i, ((h1 i).1 ⟨hi, hC⟩).1⟩, hC⟩
    · rintro ⟨⟨i, hi⟩, hC⟩; exact ⟨⟨i, ((h1 i).2 ⟨hi, hC⟩).1⟩, hC⟩

/-- one hull level, mod constants, a.s. trace (adapted from `t39h_hullSigma0_le_trace`) -/
theorem t39j_hullSigma0_le_trAE (P : Measure Ω) (h : Ω → DistC) {A A' : Ω → Set ℂ}
    {C : Set Ω} (n : ℕ) (hAA : ∀ᵐ ω ∂P, ω ∈ C → A ω = A' ω) :
    hullSigma0 h A n ≤ t39jTrAE P (hullSigma0 h A' n) C := by
  refine sup_le (generateFrom_le ?_) (generateFrom_le ?_)
  · rintro _ ⟨U, hU, rfl⟩
    refine ⟨{ω | (A' ω ∩ U).Nonempty}, (le_sup_left : setSigma A' ≤ hullSigma0 h A' n) _
      (measurableSet_generateFrom ⟨U, hU, rfl⟩), ?_⟩
    filter_upwards [hAA] with ω hω
    show (ω ∈ {ω | (A ω ∩ U).Nonempty} ∧ ω ∈ C) = (ω ∈ {ω | (A' ω ∩ U).Nonempty} ∧ ω ∈ C)
    apply propext
    simp only [mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hω h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hω h2).symm ▸ h1, h2⟩⟩
  · rintro _ ⟨S, F, hF, rfl⟩
    refine ⟨{ω | dyadicHull n (A' ω) = S} ∩ F, (le_sup_right : _ ≤ hullSigma0 h A' n) _
      (measurableSet_generateFrom ⟨S, F, hF, rfl⟩), ?_⟩
    filter_upwards [hAA] with ω hω
    show (ω ∈ {ω | dyadicHull n (A ω) = S} ∩ F ∧ ω ∈ C) =
      (ω ∈ {ω | dyadicHull n (A' ω) = S} ∩ F ∧ ω ∈ C)
    apply propext
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨hω h3 ▸ h1, h2⟩, h3⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨(hω h3).symm ▸ h1, h2⟩, h3⟩⟩

/-- **a.s. trace of `σ(A, h|_A)` mod constants on an event where `A = A'` a.s.** -/
theorem t39j_inter_localSigma0_ae (P : Measure Ω) (h : Ω → DistC) {A A' : Ω → Set ℂ}
    (hA' : ∀ ω, IsClosed (A' ω)) {C : Set Ω} (hC : MeasurableSet[localSigma0 h A'] C)
    (hAA : ∀ᵐ ω ∂P, ω ∈ C → A ω = A' ω) {E : Set Ω} (hE : MeasurableSet[localSigma0 h A] E) :
    AEEventIn P (localSigma0 h A') (E ∩ C) := by
  refine t39j_aeEventIn_localSigma0 h hA' fun n => ?_
  obtain ⟨B, hB, hEB⟩ := t39j_hullSigma0_le_trAE P h n hAA E
    (MeasurableSpace.measurableSet_iInf.1 hE n)
  exact ⟨B ∩ C, hB.inter (MeasurableSpace.measurableSet_iInf.1 hC n), hEB⟩

end TraceAE

end CONF
end LQGMetric
