import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWLemma
import LatticeProb.Probability.Percolation.VerticalJoinedExposure

/-!
# First contact with a crossing barrier

An open crossing of a lattice rectangle has an initial segment that first meets
any crossing joining the other two sides.
-/

namespace Percolation.Literature

open SimpleGraph

/-- A left-to-right walk has a prefix whose first contact is with a bottom-to-top
walk in the same rectangle. -/
theorem exists_first_contact_of_crossings {L R B T : ℤ}
    {a b c d : LatticeModels.Site 2}
    (P : (LatticeModels.zdGraph 2).Walk a b)
    (Q : (LatticeModels.zdGraph 2).Walk c d)
    (hP : ∀ z ∈ P.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hQ : ∀ z ∈ Q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 0 = L) (hb : b 0 = R) (hc : c 1 = B) (hd : d 1 = T) :
    ∃ v ∈ Q.support, ∃ p : (LatticeModels.zdGraph 2).Walk a v,
      (∀ z ∈ p.support, z ∈ P.support) ∧
      (∀ e ∈ p.edges, e ∈ P.edges) ∧
      ∀ dart ∈ p.darts, dart.fst ∉ Q.support := by
  obtain ⟨z, hzP, hzQ⟩ := exists_mem_support_of_crossing P Q hP hQ ha hb hc hd
  exact exists_prefix_first_mem P ⟨z, hzP, hzQ⟩

/-- A horizontal crossing first meets a vertical walk or its reflection across
its starting height. -/
theorem exists_first_contact_of_reflected_crossing {n : ℕ}
    {a b c d : LatticeModels.Site 2}
    (P : (LatticeModels.zdGraph 2).Walk a b)
    (Q : (LatticeModels.zdGraph 2).Walk c d)
    (hP : ∀ z ∈ P.support, -(n : ℤ) ≤ z 0 ∧ z 0 ≤ n ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n)
    (hQ : ∀ z ∈ Q.support, 0 ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n)
    (ha : a 0 = -(n : ℤ)) (hb : b 0 = n) (hc : c 1 = 0) (hd : d 1 = n) :
    ∃ v, (v ∈ Q.support ∨ reflY 0 v ∈ Q.support) ∧
      ∃ p : (LatticeModels.zdGraph 2).Walk a v,
        (∀ z ∈ p.support, z ∈ P.support) ∧
        (∀ e ∈ p.edges, e ∈ P.edges) ∧
        ∀ dart ∈ p.darts, dart.fst ∉ Q.support ∧ reflY 0 dart.fst ∉ Q.support := by
  have hfix : reflY 0 c = c := by
    rw [LatticeModels.Site.eq_iff_two]
    simp [hc]
  let Qr := ((Q.map (reflY 0).toEmbedding.toHom).reverse).copy rfl hfix
  let barrier := Qr.append Q
  have hsupport : ∀ z, z ∈ barrier.support ↔ z ∈ Q.support ∨ reflY 0 z ∈ Q.support := by
    intro z
    simp only [barrier, Walk.mem_support_append_iff, Qr, Walk.support_copy,
      Walk.support_reverse, List.mem_reverse, Walk.support_map, List.mem_map]
    constructor
    · rintro (⟨w, hw, hwz⟩ | hz)
      · right
        have : reflY 0 w = z := hwz
        simpa [← this] using hw
      · exact Or.inl hz
    · rintro (hz | hz)
      · exact Or.inr hz
      · exact Or.inl ⟨reflY 0 z, hz, by simp⟩
  have hbarrier : ∀ z ∈ barrier.support, -(n : ℤ) ≤ z 0 ∧ z 0 ≤ n ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    rcases (hsupport z).1 hz with hz | hz
    · have h := hQ z hz
      omega
    · have h := hQ (reflY 0 z) hz
      simp only [reflY_apply_zero, reflY_apply_one] at h
      omega
  have hbottom : reflY 0 d 1 = -(n : ℤ) := by simp [hd]
  obtain ⟨v, hv, p, hp, he, havoid⟩ :=
    exists_first_contact_of_crossings P barrier hP hbarrier ha hb hbottom hd
  refine ⟨v, (hsupport v).1 hv, p, hp, he, ?_⟩
  intro dart hdart
  have h := havoid dart hdart
  simpa only [hsupport, not_or] using h

/-- A walk whose darts start outside a barrier uses no edge of the barrier,
including at its terminal vertex. -/
theorem edges_disjoint_of_darts_avoid {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d)
    (h : ∀ dart ∈ p.darts, dart.fst ∉ q.support) :
    ∀ e ∈ p.edges, e ∉ q.edges := by
  intro e he heq
  rw [Walk.edges, List.mem_map] at he
  obtain ⟨dart, hdart, rfl⟩ := he
  exact h dart hdart (q.mem_support_of_mem_edges heq (Sym2.mem_mk_left _ _))

end Percolation.Literature

namespace EdgeCrossing

open MeasureTheory ProbabilityTheory Percolation.Literature SimpleGraph
open scoped ProbabilityTheory

noncomputable section

private theorem determinedBy_avoidingPath (R : Finset (LatticeModels.Site 2))
    (O A T : Set (LatticeModels.Site 2)) :
    DeterminedBy (avoidingPath R O A T) (R.sym2 : Set _) := by
  classical
  rw [determinedBy_iff]
  suffices key : ∀ ω ω' : BondConfig (LatticeModels.Site 2),
      ω ∩ (R.sym2 : Set _) = ω' ∩ (R.sym2 : Set _) →
      ω ∈ avoidingPath R O A T → ω' ∈ avoidingPath R O A T by
    intro ω ω' h
    exact ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω ω' h ⟨t, ht, v, hv, q, hq, ho, he⟩
  refine ⟨t, ht, v, hv, q, hq, ho, ?_⟩
  intro e heq
  have heR : e ∈ R.sym2 := by
    rw [Walk.edges, List.mem_map] at heq
    obtain ⟨d, hd, rfl⟩ := heq
    exact Finset.mk_mem_sym2_iff.2 ⟨hq _ (q.dart_fst_mem_support_of_mem_darts hd),
      hq _ (q.dart_snd_mem_support_of_mem_darts hd)⟩
  exact ((Set.ext_iff.1 h e).1 ⟨he e heq, heR⟩).1

private theorem avoidingPath_probability (p : unitInterval)
    (R : Finset (LatticeModels.Site 2)) (O A T : Set (LatticeModels.Site 2)) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
        (extend (LatticeModels.zdGraph 2) ⁻¹' avoidingPath R O A T) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (avoidingPath R O A T) := by
  have hm : MeasurableSet (extend (LatticeModels.zdGraph 2) ⁻¹' avoidingPath R O A T) :=
    ((determinedBy_avoidingPath R O A T).measurableSet_of_finset).preimage
      (measurable_extend _)
  rw [← edge_product_law (LatticeModels.zdGraph 2) p, measureReal_def,
    Measure.map_apply (measurable_restrict _) hm, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
  apply propext
  change (extend (LatticeModels.zdGraph 2) (restrict (LatticeModels.zdGraph 2) ω) ∈
    avoidingPath R O A T) ↔ ω ∈ avoidingPath R O A T
  rw [extend_restrict, hω]


/-- The first contact with a vertical walk, avoiding it and its reflection until
that contact. -/
def firstContact (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool) :
    Set ((LatticeModels.zdGraph 2).edgeSet → Prop) :=
  extend (LatticeModels.zdGraph 2) ⁻¹'
    avoidingPath (centeredSquare n)
      {z | z ∈ Q.support ∨ reflY 0 z ∈ Q.support}
      (if reflected then {z | reflY 0 z ∈ Q.support} else {z | z ∈ Q.support})
      (outerLeft n)

/-- Every open horizontal crossing of the centered square has first contact with
one of the two reflected halves of a fixed vertical crossing. -/
theorem crossingIn_subset_firstContact_union (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (hc : c 1 = 0) (hd : d 1 = n) :
    crossingIn (centeredSquare n) (outerLeft n)
      {z | z 0 = (n : ℤ) ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n} ⊆
      firstContact n Q (Bool.not true) ∪ firstContact n Q true := by
  intro η hη
  obtain ⟨a, ha, b, hb, P, hP, hopen⟩ := (mem_crossingIn_iff _ _ _ _).1 hη
  have hP' : ∀ z ∈ P.support, -(n : ℤ) ≤ z 0 ∧ z 0 ≤ n ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    exact (mem_centered_square n z).1 (hP z hz)
  have hQ' : ∀ z ∈ Q.support, 0 ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    exact mem_rectangle_iff.1 (hQ z hz)
  obtain ⟨v, hv, p, hp, he, havoid⟩ :=
    exists_first_contact_of_reflected_crossing P Q hP' hQ' ha.1 hb.1 hc hd
  have hpR : ∀ z ∈ p.support, z ∈ (centeredSquare n : Set _) := fun z hz => hP z (hp z hz)
  have hpO : ∀ dart ∈ p.darts,
      dart.fst ∉ {z | z ∈ Q.support ∨ reflY 0 z ∈ Q.support} := by
    intro dart h
    simpa only [Set.mem_ofPred_eq, not_or] using havoid dart h
  have hpOpen : ∀ e ∈ p.edges, e ∈ extend (LatticeModels.zdGraph 2) η := by
    intro e he'
    exact ⟨p.edges_subset_edgeSet he', hopen e (he e he')⟩
  rcases hv with hv | hv
  · left
    exact ⟨a, ha, v, hv, p, hpR, hpO, hpOpen⟩
  · right
    exact ⟨a, ha, v, hv, p, hpR, hpO, hpOpen⟩

/-- Reflection across the horizontal axis exchanges the two first-contact events. -/
theorem firstContact_probability_reflection (p : unitInterval) (n : ℕ)
    {c d : LatticeModels.Site 2} (Q : (LatticeModels.zdGraph 2).Walk c d) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (firstContact n Q true) =
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (firstContact n Q (Bool.not true)) := by
  set ρ := reflY 0 with hρ
  set O : Set (LatticeModels.Site 2) := {z | z ∈ Q.support ∨ ρ z ∈ Q.support} with hO
  set A : Set (LatticeModels.Site 2) := {z | z ∈ Q.support} with hA
  set A' : Set (LatticeModels.Site 2) := {z | ρ z ∈ Q.support} with hA'
  have hR : ρ '' (centeredSquare n : Set _) = centeredSquare n := by
    ext z
    rw [hρ, mem_image_reflY_iff]
    simp only [Finset.mem_coe, centeredSquare, mem_centered_square, reflY_apply_zero,
      reflY_apply_one]
    omega
  have hT : ρ '' outerLeft n = outerLeft n := by
    ext z
    rw [hρ, mem_image_reflY_iff]
    simp only [outerLeft, Set.mem_ofPred_eq, reflY_apply_zero, reflY_apply_one]
    omega
  have hobs : ρ '' O = O := by
    ext z
    rw [hρ, mem_image_reflY_iff]
    simp only [hO, hρ, Set.mem_ofPred_eq, reflY_reflY, or_comm]
  have htarget : ρ '' A = A' := by
    ext z
    rw [hρ, mem_image_reflY_iff]
    rfl
  have htarget' : ρ '' A' = A := by
    ext z
    rw [hρ, mem_image_reflY_iff]
    simp only [hA, hA', hρ, Set.mem_ofPred_eq, reflY_reflY]
  have hrho : ∀ z, ρ.symm z = ρ z := by
    intro z
    apply ρ.injective
    simp [hρ]
  have hs : ∀ U : Set (LatticeModels.Site 2), ρ.symm '' U = ρ '' U := by
    intro U
    congr 1
    funext z
    exact hrho z
  have hpre : BondConfig.relabel (sym2Equiv ρ.toEquiv) ⁻¹'
      avoidingPath (centeredSquare n) O A' (outerLeft n) =
        avoidingPath (centeredSquare n) O A (outerLeft n) := by
    ext ω
    constructor
    · intro hω
      have h := relabel_mem_avoidingPath ρ.symm hω
      rw [show ρ.symm.toEquiv = ρ.toEquiv.symm from rfl, relabel_symm_relabel] at h
      simp only [hs] at h
      rwa [hR, hobs, htarget', hT] at h
    · intro hω
      have h := relabel_mem_avoidingPath ρ hω
      rwa [hR, hobs, htarget, hT] at h
  change (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
    bernoulliMeasure True False p)).real
      (extend (LatticeModels.zdGraph 2) ⁻¹'
        avoidingPath (centeredSquare n) O A' (outerLeft n)) =
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
      (extend (LatticeModels.zdGraph 2) ⁻¹'
        avoidingPath (centeredSquare n) O A (outerLeft n))
  rw [avoidingPath_probability, avoidingPath_probability,
    ← bondPercolation_real_preimage_relabel_iso ρ p, hpre]

/-- A fixed vertical crossing is first reached with probability at least one quarter. -/
theorem quarter_le_firstContact (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (hc : c 1 = 0) (hd : d 1 = n) :
    (1 / 4 : ℝ) ≤ (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False half)).real (firstContact n Q (Bool.not true)) := by
  let μ : Measure ((LatticeModels.zdGraph 2).edgeSet → Prop) :=
    Measure.infinitePi (fun _ => bernoulliMeasure True False half)
  let H := crossingIn (centeredSquare n) (outerLeft n)
    {z | z 0 = (n : ℤ) ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n}
  have hH : (1 / 2 : ℝ) ≤ μ.real H := by
    refine le_trans (half_le_centered_square_horizontal n) ?_
    apply measureReal_mono _ (measure_ne_top _ _)
    intro η hη
    obtain ⟨a, ha, b, hb, P, hP, hOpen⟩ := (mem_crossingIn_iff _ _ _ _).1 hη
    apply (mem_crossingIn_iff _ _ _ _).2
    refine ⟨a, ?_, b, ?_, P, hP, hOpen⟩
    · change a 0 = -(n : ℤ) ∧ -(n : ℤ) ≤ a 1 ∧ a 1 ≤ n
      exact ⟨ha.2, ha.1.2.2.1, ha.1.2.2.2⟩
    · exact ⟨hb.2, hb.1.2.2.1, hb.1.2.2.2⟩
  have hcover : μ.real H ≤ μ.real (firstContact n Q (Bool.not true)) +
      μ.real (firstContact n Q true) := by
    exact le_trans (measureReal_mono (crossingIn_subset_firstContact_union n Q hQ hc hd)
      (measure_ne_top _ _)) (measureReal_union_le _ _)
  have hsymm : μ.real (firstContact n Q true) = μ.real (firstContact n Q (Bool.not true)) :=
    firstContact_probability_reflection half n Q
  change (1 / 4 : ℝ) ≤ μ.real (firstContact n Q (Bool.not true))
  linarith

end

end EdgeCrossing
