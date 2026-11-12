/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114U1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5a
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114T1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3Norm

/-!
# CONF Lemma 3.6 Step 1 (i): local events are a.s. events of `σ(𝓑^•_{σ^ε}, h|) mod constants`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 1, C:1362–1368 ("Since `z` and
`Ũ^r` … are each determined by `(𝓑^•_τ, h|_{𝓑^•_τ})`, … each `E^{Ũ^r}(z)` is determined by
`(𝓑^•_τ, h|_{𝓑^•_τ})` and `h|_{𝔸_{2r,5r}(z)}`. … we have `B_{5ρ̃ⁿ}(z) ⊆ 𝓑^•_{σ}`. By combining
these statements … and the locality of the metric, `G^ε_x ∈ σ(𝓑^•_σ, h|_{𝓑^•_σ})`"). DEC-114 §4 C3.

Generic tools, for a random closed set `A'` which is a.s. bounded or `ℂ` (the filled ball
`𝓑^•_{σ}` at a radius `σ ∈ [0,∞]`):

* `conf36_aeEventIn_hullSigma0_of_pieces`: gluing over the hull partition for `hullSigma0`;
  copy of `LocalEvent.aeEventIn_hullSigma_of_pieces` (Meas/LocalEventRandom) for a countable
  family of hull shapes (finite unions of squares and `ℂ`);
* `conf36_setSigma_subset_open`: `{V ⊆ A'}` (`V` open) is an event of `σ(A')`;
* **`conf36_trace_mono_ae`**: for a local set `A ⊆ A'` (mod constants, a.s. bounded) every event
  of `σ(A, h|_A) mod const` is a.s. an event of `σ(A', h|_{A'}) mod const` (the half
  "determined by `(𝓑^•_τ, h|_{𝓑^•_τ})`" of C:1362–1368), from `conf36_trace_local0` (S3D114S4);
* **`conf36_local_ae`**: an a.s. event `Y` of `σ(h|_V) mod const` gives the a.s. event
  `Y ∩ {V ⊆ A'}` of `σ(A', h|_{A'}) mod const`;
* **`conf36_aeEventIn_fieldSigma0On_of_norm`**: an event of `σ((h − h_r(z))|_A)` is a.s. an event
  of `σ(h|_W) mod const` for `A ⊆ W ⊇ ∂B_r(z)` (normalize at a bump `ψ₀ ⊆ W`:
  `gm_fieldSigma_circleAvg_le`, `gm_fieldSigma_eq_fieldSigma0On`, `ae_circleAvg_addConst`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric TopologicalSpace
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.CONF

/-- the possible level-`n` hulls of a set which is bounded or `ℂ` -/
def conf36HullShapes (n : ℕ) : Set (Set ℂ) := insert univ (range (hullFin n))

theorem conf36HullShapes_countable (n : ℕ) : (conf36HullShapes n).Countable :=
  (countable_range _).insert _

theorem conf36_dyadicHull_univ (n : ℕ) : dyadicHull n (univ : Set ℂ) = univ := by
  refine eq_univ_of_forall fun y => ?_
  obtain ⟨k, hk⟩ := exists_sq_mem n y
  simp only [dyadicHull, mem_iUnion]
  exact ⟨k, ⟨y, hk, mem_univ _⟩, hk⟩

theorem conf36_hull_mem_shapes {A : Set ℂ} (hA : Bornology.IsBounded A ∨ A = univ) (n : ℕ) :
    dyadicHull n A ∈ conf36HullShapes n := by
  rcases hA with hb | rfl
  · obtain ⟨s, hs⟩ := exists_hullFin_of_bounded hb n
    exact Or.inr ⟨s, hs.symm⟩
  · exact Or.inl (conf36_dyadicHull_univ n)

section Glue
variable {Ω : Type} [MeasurableSpace Ω]

/-- **gluing over the hull partition** for `hullSigma0` and a countable family of hull shapes
(copy of `LocalEvent.aeEventIn_hullSigma_of_pieces`) -/
theorem conf36_aeEventIn_hullSigma0_of_pieces {P : Measure Ω} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) {𝒮 : Set (Set ℂ)} (h𝒮 : 𝒮.Countable) (hA : ∀ᵐ ω ∂P, dyadicHull n (A ω) ∈ 𝒮)
    {E : Set Ω}
    (hE : ∀ S ∈ 𝒮, ∃ F, MeasurableSet[fieldSigma0On h (interior S)] F ∧
      ∀ᵐ ω ∂P, dyadicHull n (A ω) = S → (ω ∈ E ↔ ω ∈ F)) :
    AEEventIn P (hullSigma0 h A n) E := by
  choose! F hFm hEF using hE
  refine ⟨⋃ S ∈ 𝒮, {ω | dyadicHull n (A ω) = S} ∩ F S, ?_, ?_⟩
  · exact MeasurableSet.biUnion h𝒮 fun S hS => (le_sup_right : _ ≤ hullSigma0 h A n) _
      (measurableSet_generateFrom ⟨S, F S, hFm S hS, rfl⟩)
  · have hall : ∀ᵐ ω ∂P, ∀ S ∈ 𝒮, dyadicHull n (A ω) = S → (ω ∈ E ↔ ω ∈ F S) :=
      (ae_ball_iff h𝒮).2 hEF
    filter_upwards [hA, hall] with ω hω hω'
    apply propext
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop]
    constructor
    · exact fun hE => ⟨_, hω, rfl, (hω' _ hω rfl).1 hE⟩
    · rintro ⟨S, hS, hS', hF⟩
      exact (hω' S hS hS').2 hF

omit [MeasurableSpace Ω] in
/-- `{V ⊆ A}` is an event of `σ(A)` for `A` closed and `V` open -/
theorem conf36_setSigma_subset_open {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) {V : Set ℂ}
    (hV : IsOpen V) : MeasurableSet[setSigma A] {ω | V ⊆ A ω} := by
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have e : {ω | V ⊆ A ω} = ⋂ q ∈ Q ∩ V, {ω | (A ω ∩ {q}).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, inter_singleton_nonempty]
    constructor
    · intro hV q hq
      exact hV hq.2
    · intro hq v hv
      by_contra hvA
      obtain ⟨q, hqQ, hq'⟩ := hQd.exists_mem_open ((hA ω).isOpen_compl.inter hV) ⟨v, hvA, hv⟩
      exact hq'.1 (hq q ⟨hqQ, hq'.2⟩)
  rw [e]
  exact MeasurableSet.biInter (hQc.mono inter_subset_left) fun q _ =>
    GM.gm_setSigma_hit_closed hA isClosed_singleton

/-- **trace of a smaller local set**: for a local set `A ⊆ A'` (a.s. bounded), every event of
`σ(A, h|_A) mod const` is a.s. an event of `σ(A', h|_{A'}) mod const` -/
theorem conf36_trace_mono_ae {P : Measure Ω} (h : Ω → DistC) {A A' : Ω → Set ℂ}
    (hAc : ∀ ω, IsClosed (A ω)) (hAb : ∀ᵐ ω ∂P, Bornology.IsBounded (A ω))
    (hloc : IsLocalSetDet0 P h A) (hA'c : ∀ ω, IsClosed (A' ω))
    (hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (A' ω) ∨ A' ω = univ)
    (hAA : ∀ᵐ ω ∂P, A ω ⊆ A' ω) {E : Set Ω} (hE : MeasurableSet[localSigma0 h A] E) :
    AEEventIn P (localSigma0 h A') E := by
  refine t39j_aeEventIn_localSigma0 h hA'c fun n => ?_
  refine conf36_aeEventIn_hullSigma0_of_pieces h A' n (conf36HullShapes_countable n)
    (hA'.mono fun ω hω => conf36_hull_mem_shapes hω n) fun S _ => ?_
  obtain ⟨F, hF, hEF⟩ := conf36_trace_local0 h hAc hAb hloc (isOpen_interior (s := S)) hE
  refine ⟨F, hF, ?_⟩
  filter_upwards [hEF, hAA] with ω hω hωA hS
  have hsub : A ω ⊆ interior S := by
    rw [← hS]; exact hωA.trans (subset_interior_dyadicHull n _)
  have e : (ω ∈ {ω | A ω ⊆ interior S} ∩ E) = (ω ∈ F) := hω
  rw [← e]
  exact ⟨fun h => ⟨hsub, h⟩, fun h => h.2⟩

/-- **local events**: an a.s. event `Y` of `σ(h|_V) mod const` (`V` open) gives the a.s. event
`Y ∩ {V ⊆ A'}` of `σ(A', h|_{A'}) mod const` -/
theorem conf36_local_ae {P : Measure Ω} (h : Ω → DistC) {A' : Ω → Set ℂ}
    (hA'c : ∀ ω, IsClosed (A' ω)) (hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (A' ω) ∨ A' ω = univ)
    {V : Set ℂ} (hV : IsOpen V) {Y : Set Ω} (hY : AEEventIn P (fieldSigma0On h V) Y) :
    AEEventIn P (localSigma0 h A') (Y ∩ {ω | V ⊆ A' ω}) := by
  obtain ⟨F, hF, hYF⟩ := hY
  refine t39j_aeEventIn_localSigma0 h hA'c fun n => ?_
  have h1 : AEEventIn P (hullSigma0 h A' n)
      (Y ∩ {ω | V ⊆ interior (dyadicHull n (A' ω))}) := by
    refine conf36_aeEventIn_hullSigma0_of_pieces h A' n (conf36HullShapes_countable n)
      (hA'.mono fun ω hω => conf36_hull_mem_shapes hω n) fun S _ => ?_
    by_cases hVS : V ⊆ interior S
    · refine ⟨F, conf36_fieldSigma0On_mono h hVS _ hF, ?_⟩
      filter_upwards [hYF] with ω hω hS
      have e : (ω ∈ Y) = (ω ∈ F) := hω
      rw [← e]
      simp only [mem_inter_iff, mem_ofPred_eq, hS]
      exact ⟨fun h => h.1, fun h => ⟨h, hVS⟩⟩
    · refine ⟨∅, @MeasurableSet.empty _ (fieldSigma0On h (interior S)),
        Eventually.of_forall fun ω hS => ?_⟩
      simp only [mem_inter_iff, mem_ofPred_eq, hS, mem_empty_iff_false, iff_false, not_and]
      exact fun _ h => hVS h
  obtain ⟨F', hF', hF'e⟩ := h1
  have hHb : MeasurableSet[hullSigma0 h A' n] {ω | V ⊆ A' ω} :=
    (le_sup_left : setSigma A' ≤ hullSigma0 h A' n) _ (conf36_setSigma_subset_open hA'c hV)
  refine ⟨F' ∩ {ω | V ⊆ A' ω}, @MeasurableSet.inter _ (hullSigma0 h A' n) _ _ hF' hHb, ?_⟩
  have e : Y ∩ {ω | V ⊆ A' ω} =
      (Y ∩ {ω | V ⊆ interior (dyadicHull n (A' ω))}) ∩ {ω | V ⊆ A' ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2.trans (subset_interior_dyadicHull n _)⟩, h2⟩,
      fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
  rw [e]
  exact hF'e.inter EventuallyEq.rfl

/-- **normalization at a circle, mod constants**: an event of `σ((h − h_r(z))|_A)` is a.s. an
event of `σ(h|_W) mod const` for `A ⊆ W ⊇ ∂B_r(z)` -/
theorem conf36_aeEventIn_fieldSigma0On_of_norm {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) {z : ℂ} {A W : Opens ℂ} (hAW : A ≤ W)
    (hsph : sphere z r ⊆ W) {E : Set Ω}
    (hE : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) A) E) :
    AEEventIn P (fieldSigma0On h W) E := by
  -- a bump `ψ₀` with `∫ ψ₀ = 1`, `supp ψ₀ ⊆ W`
  have hw : z + (r : ℂ) ∈ (W : Set ℂ) := hsph (by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr])
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 W.isOpen _ hw
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  set ψ₀ : TestC := bumpTest m (z + (r : ℂ))
  have hψ1 : ∫ x, ψ₀ x = 1 := CircleAvg.integral_bumpTest' m _
  have hψs : tsupport (ψ₀ : ℂ → ℝ) ⊆ W := by
    rw [GM.tsupport_bumpTest]
    exact (closedBall_subset_ball hm).trans hδW
  set g : Ω → DistC := fun ω => addConst (h ω) (-(h ω ψ₀))
  have hg0 : ∀ ω, g ω ψ₀ = 0 := fun ω => by
    simp only [g, GFFInv.addConst_apply, hψ1, one_mul, add_neg_cancel]
  -- `h − h_r(z) = g − g_r(z)` a.s.
  have hae : ∀ᵐ ω ∂P, addConst (h ω) (-circleAvg (h ω) r z) =
      addConst (g ω) (-circleAvg (g ω) r z) := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh z hr] with ω hω
    simp only [g, hω, GFFLaw.addConst_addConst]
    congr 1
    ring
  obtain ⟨F, hF, hEF⟩ := hE
  obtain ⟨S, hS, rfl⟩ := hF
  refine ⟨(fun ω => restrictTo A (addConst (g ω) (-circleAvg (g ω) r z))) ⁻¹' S, ?_, ?_⟩
  · have h1 : fieldSigma (fun ω => addConst (g ω) (-circleAvg (g ω) r z)) A ≤ fieldSigma g W :=
      GM.gm_fieldSigma_circleAvg_le g hAW (by rwa [abs_of_pos hr])
    have h2 : fieldSigma g W = fieldSigma0On g W :=
      GM.gm_fieldSigma_eq_fieldSigma0On hψ1 hg0 hψs
    have h3 : fieldSigma0On g W = fieldSigma0On h W :=
      fieldSigma0On_addConst h (fun ω => -(h ω ψ₀)) W
    rw [← h3, ← h2]
    exact h1 _ ⟨S, hS, rfl⟩
  · refine hEF.trans ?_
    filter_upwards [hae] with ω hω
    simp only [mem_preimage, hω]

end Glue

end LQGMetric.CONF
