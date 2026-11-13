/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cM.FailSet at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.Cert
import LatticeProb.Bonanno.LQGMetric.Meas.UM

/-!
# The localized failure set is sandwiched between universally measurable sets

Source: [18], Lemma 4.3: "`DA^ε(z) 1(B̄^ε_z ⊂ V)`
is a.s. determined by `h|_V` (and the space-filling SLE)". the `failSet γ V ε D f A tol R r` is the set of
local data `p = (h|_V, c)` for which some field with this restriction has a vague limit `ν` on `V` with
`¬ LocalGood ν c …`.

**Witnesses.** `L43MRel γ V p (h, ψ)`: `h|_V = p.1`, the countable certificate `L43MCert` holds for `h` and
`ν_ψ := ((p.2 ∘ ψ)_* Leb)|_V`, and `L43MCond p.2 ψ` (so the `BridgeHyp` holds for `(p.2 ∘ ψ)_* Leb`).
The relation is **Borel** (`measurableSet_l43mRel`) on the standard Borel space
`(DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))`.

**Sandwich** (guarded parameters: `0 < ε`, `0 ≤ r`, `D ⊆ R`, `B̄_{4r}(z) ⊆ V` on `R`, `D`, `R` Borel, `f`
a.e.-measurable on `D` — the event of [18] Lemma 4.3):
* `l43mBad ⊆ failSet` and `failSet ⊆ l43mBad ∪ l43mNoWitness`, where `l43mBad` (a witness whose area-time
  curve fails the geometric good event) and `l43mNoWitness` (no witness) are **universally measurable**
  by Lusin's theorem (`LQGMetric.UMeasurableSet.setOf_exists`);
* `nullMeasurableSet_failSet`: `failSet` is null-measurable for every finite law under which
  `l43mNoWitness` is null. The null set does not depend on the parameters `ε, D, f, A, tol, R, r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cM

open MatedCRTHarmonic LQGMetric QuantumZipper GMS4FO

variable (γ : ℝ) (V : Opens ℂ)

/-- **The witness relation**: a field extension `h` of the local field, certified to have the local
push-forward area of `p.2 ∘ ψ` as its local GMC, and a time change `ψ` making `p.2 ∘ ψ` area-parametrized. -/
def L43MRel (p : DistOn V × C(ℝ, ℂ)) (w : DistC × C(ℝ, ℝ)) : Prop :=
  restrictTo V w.1 = p.1 ∧ L43MCert γ V w.1 ((volume.map (p.2.comp w.2)).restrict V) ∧
    L43MCond p.2 w.2

/-- **The witness relation is Borel.** -/
theorem measurableSet_l43mRel :
    MeasurableSet {q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) | L43MRel γ V q.1 q.2} := by
  have h1 : MeasurableSet {q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) |
      restrictTo V q.2.1 = q.1.1} :=
    measurableSet_eq_fun ((measurable_restrictTo V).comp (measurable_fst.comp measurable_snd))
      (measurable_fst.comp measurable_fst)
  have hpair : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) =>
      ((q.1.2, q.2.2) : C(ℝ, ℂ) × C(ℝ, ℝ)) :=
    (measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hcomp : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) => q.1.2.comp q.2.2 := by
    have e := measurable_comp_pair.comp hpair
    exact e
  have h2 : MeasurableSet {q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) |
      L43MCert γ V q.2.1 ((volume.map (q.1.2.comp q.2.2)).restrict V)} := by
    have hm : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) =>
        ((q.2.1, q.1.2.comp q.2.2) : DistC × C(ℝ, ℂ)) :=
      (measurable_fst.comp measurable_snd).prodMk hcomp
    have h0 := measurableSet_l43mCert γ V.isOpen.measurableSet
    have h0' := h0.preimage hm
    exact h0'
  have h3 : MeasurableSet {q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) | L43MCond q.1.2 q.2.2} := by
    have h0 := measurableSet_l43mCond.preimage hpair
    exact h0
  have h4 := h1.inter (h2.inter h3)
  exact h4

/-! ### The universally measurable sets -/

/-- Local data with no witness. -/
def l43mNoWitness : Set (DistOn V × C(ℝ, ℂ)) := {p | ¬ ∃ w, L43MRel γ V p w}

/-- A witness whose area-time curve has a large window at a point of `R`. -/
def l43mWinBad (ε : ℝ) (R : Set ℂ) (r : ℝ) : Set (DistOn V × C(ℝ, ℂ)) :=
  {p | ∃ w : (DistC × C(ℝ, ℝ)) × ℂ, L43MRel γ V p w.1 ∧ w.2 ∈ R ∧
    r < GMS4b.windowDiam ε (p.2.comp w.1.2) w.2}

/-- A witness whose area-time curve violates the integral bound (with a Borel test `f'`). -/
def l43mIntBad (ε : ℝ) (Dm : Set ℂ) (f' : ℂ → ℝ) (A tol : ℝ) (I : ℝ≥0∞) :
    Set (DistOn V × C(ℝ, ℂ)) :=
  {p | ∃ w : DistC × C(ℝ, ℝ), L43MRel γ V p w ∧
    ENNReal.ofReal A * I + ENNReal.ofReal tol <
      ∫⁻ z in Dm, ENNReal.ofReal (f' z) * GMS4b.uStar ε (p.2.comp w.2) z}

theorem um_l43mNoWitness : UMeasurableSet (l43mNoWitness γ V) :=
  (UMeasurableSet.setOf_exists (measurableSet_l43mRel γ V)).compl

theorem um_l43mWinBad (ε : ℝ) {R : Set ℂ} (hR : MeasurableSet R) (r : ℝ) :
    UMeasurableSet (l43mWinBad γ V ε R r) := by
  have hrel : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × ((DistC × C(ℝ, ℝ)) × ℂ) =>
      ((q.1, q.2.1) : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hpt : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × ((DistC × C(ℝ, ℝ)) × ℂ) =>
      ((q.1.2.comp q.2.1.2, q.2.2) : C(ℝ, ℂ) × ℂ) := by
    have hc : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × ((DistC × C(ℝ, ℝ)) × ℂ) =>
        ((q.1.2, q.2.1.2) : C(ℝ, ℂ) × C(ℝ, ℝ)) :=
      (measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_snd))
    exact (measurable_comp_pair.comp hc).prodMk (measurable_snd.comp measurable_snd)
  have hS1 := (measurableSet_l43mRel γ V).preimage hrel
  have hsnd : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × ((DistC × C(ℝ, ℝ)) × ℂ) => q.2.2 :=
    measurable_snd.comp measurable_snd
  have hS2 := hR.preimage hsnd
  have hwd := (GMS4b.measurable_windowDiam ε).comp hpt
  have hS3 := measurableSet_lt (measurable_const (a := r)) hwd
  have hS : MeasurableSet {q : (DistOn V × C(ℝ, ℂ)) × ((DistC × C(ℝ, ℝ)) × ℂ) |
      L43MRel γ V q.1 q.2.1 ∧ q.2.2 ∈ R ∧ r < GMS4b.windowDiam ε (q.1.2.comp q.2.1.2) q.2.2} := by
    have h := hS1.inter (hS2.inter hS3)
    exact h
  have h := UMeasurableSet.setOf_exists hS
  exact h

theorem um_l43mIntBad {ε : ℝ} (hε : 0 ≤ ε) (Dm : Set ℂ) {f' : ℂ → ℝ} (hf' : Measurable f')
    (A tol : ℝ) (I : ℝ≥0∞) : UMeasurableSet (l43mIntBad γ V ε Dm f' A tol I) := by
  have hcomp : Measurable fun q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) => q.1.2.comp q.2.2 :=
    measurable_comp_pair.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  have hm : Measurable fun x : ((DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))) × ℂ =>
      ((x.1.1.2.comp x.1.2.2, x.2) : C(ℝ, ℂ) × ℂ) :=
    (hcomp.comp measurable_fst).prodMk measurable_snd
  have hU : Measurable fun x : ((DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))) × ℂ =>
      GMS4b.uStar ε (x.1.1.2.comp x.1.2.2) x.2 := by
    have e := (GMS4b.measurable_uStar hε).comp hm
    exact e
  have hO : Measurable fun x : ((DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))) × ℂ =>
      ENNReal.ofReal (f' x.2) := by
    have hs : Measurable fun x : ((DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))) × ℂ => x.2 :=
      measurable_snd
    have e := ENNReal.measurable_ofReal.comp (hf'.comp hs)
    exact e
  have hF : Measurable fun x : ((DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ))) × ℂ =>
      ENNReal.ofReal (f' x.2) * GMS4b.uStar ε (x.1.1.2.comp x.1.2.2) x.2 := hO.mul hU
  have hI := hF.lintegral_prod_right' (ν := volume.restrict Dm)
  have hS2 := measurableSet_lt (measurable_const (a := ENNReal.ofReal A * I + ENNReal.ofReal tol)) hI
  have hS : MeasurableSet {q : (DistOn V × C(ℝ, ℂ)) × (DistC × C(ℝ, ℝ)) |
      L43MRel γ V q.1 q.2 ∧ ENNReal.ofReal A * I + ENNReal.ofReal tol <
        ∫⁻ z in Dm, ENNReal.ofReal (f' z) * GMS4b.uStar ε (q.1.2.comp q.2.2) z} := by
    have h := (measurableSet_l43mRel γ V).inter hS2
    exact h
  have h := UMeasurableSet.setOf_exists hS
  exact h

/-! ### The sandwich -/

variable {γ V}

/-- A witness gives the local vague limit and the bridge. -/
theorem L43MRel.isVagueLimitOn (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {p : DistOn V × C(ℝ, ℂ)} {w : DistC × C(ℝ, ℝ)} (hw : L43MRel γ V p w) :
    IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ w.1)
      ((volume.map (p.2.comp w.2)).restrict V) := by
  refine isVagueLimitOn_of_cert V.isOpen hV1 ?_ hw.2.1
  rw [Measure.restrict_apply V.isOpen.measurableSet.compl, compl_inter_self, measure_empty]

/-- With a witness, the local good event is the geometric good event of `p.2 ∘ ψ`. -/
theorem L43MRel.localGood_iff (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {p : DistOn V × C(ℝ, ℂ)} {w : DistC × C(ℝ, ℝ)} (hw : L43MRel γ V p w) {ε : ℝ} (hε : 0 < ε)
    {Dm R : Set ℂ} {f : ℂ → ℝ} {A tol r : ℝ} (hr : 0 ≤ r) (hDR : Dm ⊆ R)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V) (hD : MeasurableSet Dm) :
    LocalGood ((volume.map (p.2.comp w.2)).restrict V) p.2 ε Dm f A tol R r ↔
      GlobalGood (p.2.comp w.2) ε Dm f A tol R r := by
  have H := hw.2.2.bridgeHyp V.isOpen (isBounded_ball.subset hV1)
  exact H.localGood_iff_globalGood hε hr hDR hRV hD

/-- Failure of the geometric good event, with the test replaced by an a.e.-equal one. -/
theorem not_globalGood_iff {η : ℝ → ℂ} {ε : ℝ} {Dm R : Set ℂ} {f f' : ℂ → ℝ} {A tol r : ℝ}
    (hff' : f' =ᵐ[volume.restrict Dm] f) :
    ¬ GlobalGood η ε Dm f A tol R r ↔
      (∃ z ∈ R, r < GMS4b.windowDiam ε η z) ∨
        ENNReal.ofReal A * (∫⁻ z in Dm, ENNReal.ofReal (f z)) + ENNReal.ofReal tol <
          ∫⁻ z in Dm, ENNReal.ofReal (f' z) * GMS4b.uStar ε η z := by
  have hint : (∫⁻ z in Dm, ENNReal.ofReal (f' z) * GMS4b.uStar ε η z) =
      ∫⁻ z in Dm, ENNReal.ofReal (f z) * GMS4b.uStar ε η z := by
    refine lintegral_congr_ae ?_
    filter_upwards [hff'] with z hz
    rw [hz]
  rw [hint, GlobalGood, not_and_or]
  simp only [not_forall, not_le, exists_prop]

/-- The bad set of the sandwich. -/
def l43mBad (ε : ℝ) (Dm : Set ℂ) (f f' : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ) :
    Set (DistOn V × C(ℝ, ℂ)) :=
  l43mWinBad γ V ε R r ∪ l43mIntBad γ V ε Dm f' A tol (∫⁻ z in Dm, ENNReal.ofReal (f z))

theorem l43mBad_subset_failSet (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) {ε : ℝ} (hε : 0 < ε)
    {Dm R : Set ℂ} {f f' : ℂ → ℝ} {A tol r : ℝ} (hr : 0 ≤ r) (hDR : Dm ⊆ R)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V) (hD : MeasurableSet Dm)
    (hff' : f' =ᵐ[volume.restrict Dm] f) :
    l43mBad (γ := γ) (V := V) ε Dm f f' A tol R r ⊆ failSet γ V ε Dm f A tol R r := by
  intro p hp
  have hex : ∃ w : DistC × C(ℝ, ℝ), L43MRel γ V p w ∧ ¬ GlobalGood (p.2.comp w.2) ε Dm f A tol R r := by
    rcases hp with ⟨w, hw, hz, hlt⟩ | ⟨w, hw, hlt⟩
    · exact ⟨w.1, hw, (not_globalGood_iff hff').2 (Or.inl ⟨w.2, hz, hlt⟩)⟩
    · exact ⟨w, hw, (not_globalGood_iff hff').2 (Or.inr hlt)⟩
  obtain ⟨w, hw, hfail⟩ := hex
  refine ⟨w.1, hw.1, (volume.map (p.2.comp w.2)).restrict V, hw.isVagueLimitOn hV1, ?_⟩
  rwa [hw.localGood_iff hV1 hε hr hDR hRV hD]

theorem failSet_subset_l43mBad_union (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) {ε : ℝ} (hε : 0 < ε)
    {Dm R : Set ℂ} {f f' : ℂ → ℝ} {A tol r : ℝ} (hr : 0 ≤ r) (hDR : Dm ⊆ R)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V) (hD : MeasurableSet Dm)
    (hff' : f' =ᵐ[volume.restrict Dm] f) :
    failSet γ V ε Dm f A tol R r ⊆
      l43mBad (γ := γ) (V := V) ε Dm f f' A tol R r ∪ l43mNoWitness γ V := by
  rintro p ⟨h₀, hres₀, ν₀, hν₀, hfail⟩
  by_cases hex : ∃ w, L43MRel γ V p w
  · left
    obtain ⟨w, hw⟩ := hex
    have hvl := hw.isVagueLimitOn hV1
    have hvl₀ : IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ h₀)
        ((volume.map (p.2.comp w.2)).restrict V) :=
      isVagueLimitOn_of_restrictTo_eq (hw.1.trans hres₀.symm) hvl
    have hνeq := QuantumZipper.isVagueLimitOn_unique V.isOpen hν₀ hvl₀
    rw [hνeq, hw.localGood_iff hV1 hε hr hDR hRV hD] at hfail
    rcases (not_globalGood_iff hff').1 hfail with ⟨z, hz, hlt⟩ | hlt
    · exact Or.inl ⟨(w, z), hw, hz, hlt⟩
    · exact Or.inr ⟨w, hw, hlt⟩
  · exact Or.inr hex

/-- **The localized failure set is null-measurable** for every finite law of the local data under which
`l43mNoWitness` is null, for all guarded parameters. -/
theorem nullMeasurableSet_failSet {Q : Measure (DistOn V × C(ℝ, ℂ))} [IsFiniteMeasure Q]
    (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) (hN : Q (l43mNoWitness γ V) = 0) {ε : ℝ} (hε : 0 < ε)
    {Dm R : Set ℂ} {f : ℂ → ℝ} {A tol r : ℝ} (hr : 0 ≤ r) (hDR : Dm ⊆ R)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V) (hD : MeasurableSet Dm) (hR : MeasurableSet R)
    (hf : AEMeasurable f (volume.restrict Dm)) :
    NullMeasurableSet (failSet γ V ε Dm f A tol R r) Q := by
  have hff' : hf.mk f =ᵐ[volume.restrict Dm] f := hf.ae_eq_mk.symm
  set T := l43mBad (γ := γ) (V := V) ε Dm f (hf.mk f) A tol R r with hT
  have hTum : UMeasurableSet T :=
    (um_l43mWinBad γ V ε hR r).union (um_l43mIntBad γ V hε.le Dm hf.measurable_mk A tol _)
  have hsub1 := l43mBad_subset_failSet (γ := γ) hV1 hε hr hDR hRV hD hff' (A := A) (tol := tol)
  have hsub2 := failSet_subset_l43mBad_union (γ := γ) hV1 hε hr hDR hRV hD hff' (A := A) (tol := tol)
  have hae : T =ᵐ[Q] failSet γ V ε Dm f A tol R r := by
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [sdiff_eq_empty.2 hsub1, measure_empty]
    · refine measure_mono_null (fun p hp => ?_) hN
      rcases hsub2 hp.1 with h | h
      · exact absurd h hp.2
      · exact h
  exact (hTum Q inferInstance).congr hae

end MatedCRTHarmonic.GMS4cM
