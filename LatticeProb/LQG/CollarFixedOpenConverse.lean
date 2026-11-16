import LatticeProb.LQG.ReciprocalCollarAnchors
import LatticeProb.LQG.LocalCountablePathGluing
import LatticeProb.LQG.CollarEventCountablePath
import LatticeProb.Topology.AnchoredCompactOpenCofinal

/-! # Collar observations from countable fixed-open paths -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric
open SmallGammaGeodesics.CC SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- Countable fixed-open observations, gated by inclusion in the collar. -/
def collarFixedOpenCode {Ω : Type} (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (ψ : TestC) (hψ1 : ∫ z, ψ z = 1) {p : ℝ} (hp : 0 < p) (k : ℕ)
    (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ : ℂ → ℝ) ⊆ V n) (ω : Ω) :
    NonemptyCompacts ℂ × (ℕ → ℝ × (ℕ → ℝ) × ℝ) :=
  (K ω, fun n =>
    let E : Set Ω := {ω | (V n : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    (E.indicator (fun _ => (1 : ℝ)) ω,
      (fun j => E.indicator (fun x => localCountablePath (V n) ψ (hψV n) hψ1 (h x) j) ω),
      E.indicator (fun x => toIcoMod hp 0 (h x ψ)) ω))

/-- Fixed-open paths recover the dense collar code when the anchor is supported
in every sampled collar and the open family is cofinal for compact enclosures. -/
theorem measurable_collarFieldCode_of_fixedOpenCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (hψ1 : ∫ z, ψ k z = 1)
    (hψK : ∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n)
    (hV : ∀ C : Set ℂ, IsCompact C → ∀ U : Set ℂ, IsOpen U →
      tsupport (ψ k : ℂ → ℝ) ⊆ U → C ⊆ U → ∃ n, C ⊆ V n ∧ (V n : Set ℂ) ⊆ U) :
    Measurable[MeasurableSpace.comap (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV)
      inferInstance] (collarFieldCode h K localDenseTest ψ hp k) := by
  classical
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) inferInstance
  let E : ℕ → Set Ω := fun n => {ω | (V n : Set ℂ) ⊆
    thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
  have hobs : Measurable (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) :=
    comap_measurable _
  have hK : Measurable K := hobs.fst
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_sigmaCompact_subset_thickening hK (isSigmaCompact_of_isOpen (V n).isOpen) _
  have hpath : ∀ n j, Measurable ((E n).indicator
      (fun ω => localCountablePath (V n) (ψ k) (hψV n) hψ1 (h ω) j)) := by
    intro n j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply n).comp hobs.snd).snd.fst
  have hphasegate : ∀ n, Measurable ((E n).indicator (fun ω => toIcoMod hp 0 (h ω (ψ k)))) := by
    intro n
    exact ((measurable_pi_apply n).comp hobs.snd).snd.snd
  have hcover : (⋃ n, E n) = univ := by
    apply eq_univ_iff_forall.mpr
    intro ω
    obtain ⟨n, _, hn⟩ := hV ∅ isCompact_empty _ isOpen_thickening (hψK ω) (empty_subset _)
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hphase : Measurable (fun ω => toIcoMod hp 0 (h ω (ψ k))) := by
    intro B hB
    have heq : (fun ω => toIcoMod hp 0 (h ω (ψ k))) ⁻¹' B =
        ⋃ n, E n ∩ ((E n).indicator (fun ω => toIcoMod hp 0 (h ω (ψ k)))) ⁻¹' B := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      constructor
      · intro hw
        have : ω ∈ ⋃ n, E n := by rw [hcover]; trivial
        obtain ⟨n, hn⟩ := mem_iUnion.mp this
        exact ⟨n, hn, by simpa only [indicator_of_mem hn] using hw⟩
      · rintro ⟨n, hn, hw⟩
        simpa only [indicator_of_mem hn] using hw
    rw [heq]
    exact MeasurableSet.iUnion fun n => (hE n).inter (hphasegate n hB)
  have hcoords : Measurable (fun ω i =>
      let G : Set Ω := {ω | tsupport (localDenseTest i : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
      (G.indicator (fun _ => (1 : ℝ)) ω,
       G.indicator (fun ω => h ω (localDenseTest i) -
         (∫ z, localDenseTest i z) * h ω (ψ k)) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    let φ := localDenseTest i
    let G : Set Ω := {ω | tsupport (φ : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    let F : ℕ → Set Ω := fun n => if tsupport (φ : ℂ → ℝ) ⊆ V n then E n else ∅
    have hF : ∀ n, MeasurableSet (F n) := by
      intro n
      dsimp [F]
      split_ifs <;> simp_all
    have hFG : (⋃ n, F n) = G := by
      ext ω
      simp only [mem_iUnion, G, mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩
        by_cases hs : tsupport (φ : ℂ → ℝ) ⊆ V n
        · exact hs.trans (by simpa [F, hs, E] using hn)
        · simp [F, hs] at hn
      · intro hg
        obtain ⟨n, hn, hnU⟩ := hV _ φ.hasCompactSupport.isCompact _
          isOpen_thickening (hψK ω) hg
        exact ⟨n, by simpa only [F, ite_eq_left hn, E, mem_ofPred_eq] using hnU⟩
    have hFpath : ∀ n j, Measurable ((F n).indicator
        (fun ω => localCountablePath (V n) (ψ k) (hψV n) hψ1 (h ω) j)) := by
      intro n j
      by_cases hs : tsupport (φ : ℂ → ℝ) ⊆ V n
      · simpa [F, hs] using hpath n j
      · simp [F, hs]
    let θ : TestC := φ - (∫ z, φ z) • ψ k
    have hθsupp : tsupport (θ : ℂ → ℝ) ⊆
        tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ k : ℂ → ℝ) := by
      have he : (θ : ℂ → ℝ) = (φ : ℂ → ℝ) - (∫ z, φ z) • (ψ k : ℂ → ℝ) := by
        ext x
        simp [θ]
      rw [he]
      exact tsupport_sub_smul_subset _ _ _
    have hm := measurable_indicator_pairing_of_localCountablePaths h V (fun _ => ψ k)
      hψV (fun _ => hψ1) F hF hFpath θ (by
        intro n hn
        have hs : tsupport (φ : ℂ → ℝ) ⊆ V n := by
          by_contra hs
          exact hn (by simp [F, hs])
        exact hθsupp.trans (union_subset hs (hψV n)))
      (LQGMetric.GFFLaw.integral_sub_smul hψ1 φ)
    rw [hFG] at hm
    have hG : MeasurableSet G := measurableSet_compact_subset_thickening hK
      φ.hasCompactSupport.isCompact _
    apply (measurable_const.indicator hG).prodMk
    change Measurable (G.indicator (fun ω => h ω φ - (∫ z, φ z) * h ω (ψ k)))
    convert hm using 1
    funext ω
    by_cases hw : ω ∈ G
    · simp only [indicator_of_mem hw, θ, map_sub, map_smul, smul_eq_mul]
    · simp only [indicator_of_notMem hw]
  exact hK.prodMk (hcoords.prodMk hphase)

/-- The dense collar code determines the fixed-open observations. -/
theorem measurable_fixedOpenCode_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (hψ1 : ∫ z, ψ k z = 1)
    (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hK : Measurable K := (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  apply hK.prodMk
  apply measurable_pi_iff.mpr
  intro n
  have hE := measurableSet_open_subset_collar_of_collarFieldCode h K ψ hp k (V n)
  have hm := measurable_event_localCountablePath_phase_of_collarFieldCode
    h K ψ hp k (V n) (ψ k) (hψV n) hψ1
  exact (measurable_const.indicator hE).prodMk hm

/-- The fixed-open and dense-test codes generate the same fixed-scale
σ-algebra for any cofinal anchored open family. -/
theorem collarFieldCode_comap_eq_fixedOpenCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (hψ1 : ∫ z, ψ k z = 1)
    (hψK : ∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n)
    (hV : ∀ C : Set ℂ, IsCompact C → ∀ U : Set ℂ, IsOpen U →
      tsupport (ψ k : ℂ → ℝ) ⊆ U → C ⊆ U → ∃ n, C ⊆ V n ∧ (V n : Set ℂ) ⊆ U) :
    MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance =
      MeasurableSpace.comap (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) inferInstance :=
  le_antisymm
    (measurable_collarFieldCode_of_fixedOpenCode h K ψ hp k hψ1 hψK V hψV hV).comap_le
    (measurable_fixedOpenCode_of_collarFieldCode h K ψ hp k hψ1 V hψV).comap_le

/-- There is a countable fixed-open code generating the fixed-scale collar
σ-algebra when the anchor is supported in every sampled collar. -/
theorem exists_collarFieldCode_comap_eq_fixedOpenCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (hψ1 : ∫ z, ψ k z = 1)
    (hψK : ∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    ∃ (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n),
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance =
        MeasurableSpace.comap (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) inferInstance := by
  obtain ⟨W, hWo, hWA, hW⟩ :=
    LatticeProb.Topology.exists_sequence_open_compact_enclosures_containing ℂ
      (tsupport (ψ k : ℂ → ℝ)) (ψ k).hasCompactSupport.isCompact
  let V : ℕ → Opens ℂ := fun n => ⟨W n, hWo n⟩
  have hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n := hWA
  refine ⟨V, hψV, collarFieldCode_comap_eq_fixedOpenCode h K ψ hp k hψ1 hψK V hψV ?_⟩
  exact hW

/-- A common point of the compact sets supplies an actual anchor family and
countable fixed-open codes for all reciprocal collar scales. -/
theorem exists_anchored_collarFixedOpenCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (z : ℂ)
    (hz : ∀ ω, z ∈ (K ω : Set ℂ)) {p : ℝ} (hp : 0 < p) :
    ∃ ψ : ℕ → TestC, ∀ k, ∃ (hψ1 : ∫ x, ψ k x = 1)
      (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n),
      (∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) ∧
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance =
        MeasurableSpace.comap (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) inferInstance := by
  obtain ⟨ψ, hψ⟩ := exists_reciprocal_collar_anchors z
  refine ⟨ψ, fun k => ?_⟩
  have hsupp : ∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) := fun ω => (hψ k).2 _ (hz ω)
  obtain ⟨V, hψV, heq⟩ := exists_collarFieldCode_comap_eq_fixedOpenCode
    h K ψ hp k (hψ k).1 hsupp
  exact ⟨(hψ k).1, V, hψV, hsupp, heq⟩

end LatticeProb.LQG
