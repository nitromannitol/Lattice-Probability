/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CorrectorInterpolationTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoercivitySmallJumps
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialEnds

/-!
# Corrector and interpolation transfer

This file proves the manuscript's transfer step at `tex:1648-1652`, the paragraph
of the proof of Theorem `p:thm:areaclt` which reads

> By compact containment, with probability arbitrarily close to one the spatial
> path through time `T/ε²` lies in `B̄(R/ε)`.  On that event `(p:eq:corrector)`
> gives `sup_{t≤T} ε|Z_{t/ε²} - M_{t/ε²}| → 0`.  The assertion extends from vertex
> times to all times by their right-continuous extensions. … Its interpolation
> error is bounded by the largest ordinary spatial jump whose preceding holding
> interval meets the time interval. … The estimate `|z_H - z_{H'}| ≤ d_H + d_{H'}`,
> together with `(p:eq:mesh)`, makes that error `o(1)` after scaling.

Everything here is **deterministic and pathwise**, exactly as in the manuscript:
the probabilistic half of the paragraph ("with probability arbitrarily close to
one") is compact containment, which is the separate Lemma `p:lem:lindeberg`, and
enters below only as the hypothesis `‖Z t‖ ≤ R/ε` — the manuscript's "on that
event".  Nothing here asserts compact containment, and nothing here constructs a
corrector.

## Inputs

* `z` are cell representatives (`StatementIngredients.CellRepresentatives`);
* `hsub : UniformlySublinearError F Φ z` is the manuscript's `(p:eq:corrector)`;
* `hdiam : SubmacroscopicDiameters F` is the manuscript's `D_R = o(R)` from
  `(p:eq:mesh)`, already proved by `Spatial.maxDiamHittingBall_sublinear` and
  bridged by `CoercivitySmallJumps.submacroscopicDiameters_of_finite_scaledNear`.

These are the same two inputs used by the immediately preceding manuscript lemma
`p:lem:coercive`, formalized in `ReflectedGMS.Limit.CoercivitySmallJumps`, whose
geometry helpers are reused throughout.

## Results

* `exists_pos_forall_scaled_correctorError_le` — the scaled corrector error
  `ε‖z_H - Φ(H)‖` is uniformly below `δ` over all cells with `‖z_H‖ ≤ R/ε`, once
  `ε` is small.  This is the display at `tex:1650` at vertex level.
* `norm_representative_sub_le_diam_add_diam` — the manuscript's displayed
  estimate `|z_H - z_{H'}| ≤ d_H + d_{H'}` across an ordinary edge.
* `exists_pos_forall_scaled_neighborRepresentativeGap_le` — its scaled,
  submacroscopic-diameter consequence: `ε‖z_{H'} - z_H‖ ≤ δ`.  It is obtained by
  *reusing* `CoercivitySmallJumps.exists_pos_forall_neighbor_smallJump` with the
  corrector taken to be `z` itself, via `uniformlySublinearError_self`.
* `exists_pos_forall_scaled_spatialExtension_sub_le` — the display at `tex:1650`
  for the actual pathwise spatial extensions: `Z` the extension of the path
  through the representatives `z`, and `M` the extension through the harmonic
  coordinate `Φ`.  These are exactly the two objects appearing in
  `InvarianceMainStatement.RegularSpatialExtension`, whose conjunction over one
  common lift is what `FixedStartConclusions` and
  `RepresentativePathConclusions` carry.
* `exists_pos_forall_scaled_interpolation_sub_le` — the interpolation clause of
  `tex:1652`: the *continuous* interpolation `Ztilde` of the representative path
  (`SpatialEnds.IsContinuousInterpolation`, the object whose law is compared to
  the Brownian target in `RepresentativePathConclusions`) stays within `δ/ε` of
  the harmonic martingale path `M` at every vertex-valued time of the contained
  region.  This combines the two previous bounds.
* `le_of_forall_vertexTime_le` and
  `exists_pos_forall_scaled_interpolation_sub_le_allTimes` — the first sentence
  of `tex:1652`, "the assertion extends from vertex times to all times by their
  right-continuous extensions".

**Conditionality.**  `le_of_forall_vertexTime_le` and
`exists_pos_forall_scaled_interpolation_sub_le_allTimes` carry the additional
explicit hypothesis `RightDenseVertexTimes F X`: the vertex-valued times of the
path are right-dense.  This is exactly what "by their right-continuous
extensions" presupposes, and it is *not* implied by the predicates
`IsSpatialExtension` / `IsContinuousInterpolation` alone — a path that is
end-valued on a whole time interval satisfies those predicates with an arbitrary
continuous value there.  It is a genuinely open input about the reflected walk,
not proved here.  Every other theorem in this file is unconditional given the two
manuscript inputs above.

None of this certifies the existence of a harmonic coordinate: `Φ` and its
sublinearity are hypotheses.
-/

set_option autoImplicit false

open Filter Set Topology

open scoped NNReal

namespace ReflectedGMS.CorrectorInterpolationTransfer

open StatementIngredients DirectionalNondegeneracy CoercivitySmallJumps SpatialEnds

variable {V : Type*}

/-! ## The scaled corrector error on a contained region -/

/-- **Manuscript `tex:1648-1651`, vertex level.**  For each fixed `R ≥ 0` and each
`δ > 0` there is `ε₀ > 0` such that for every `0 < ε ≤ ε₀`, every cell whose
representative lies in `B̄(0, R/ε)` satisfies `ε‖z_H - Φ(H)‖ ≤ δ`.

This is the whole content of "on that event `(p:eq:corrector)` gives
`sup_{t≤T} ε|Z_{t/ε²} - M_{t/ε²}| → 0`": the sublinear error is `o(R/ε)` at the
radius `R/ε` reached by the contained path, and `ε · o(R/ε) → 0`.  Only the
corrector sublinearity is used; no geometry and no diameter bound. -/
theorem exists_pos_forall_scaled_correctorError_le (F : IndexedCells V) (Φ z : V → Plane)
    (hz : CellRepresentatives F z) (hsub : UniformlySublinearError F Φ z)
    {R : ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ v : V,
      ‖z v‖ ≤ R / ε → ε * ‖z v - Φ v‖ ≤ δ := by
  obtain ⟨R', hR'pos, hRR'le⟩ : ∃ R' : ℝ, 0 < R' ∧ R ≤ R' :=
    ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  obtain ⟨R₁, hR₁pos, hR₁⟩ := hsub (δ / R') (div_pos hδ hR'pos)
  refine ⟨R' / R₁, div_pos hR'pos hR₁pos, ?_⟩
  intro ε hε hεle v hzv
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hεR₁ : ε * R₁ ≤ R' := (le_div_iff₀ hR₁pos).mp hεle
  have hL : R₁ ≤ R' / ε := by
    rw [le_div_iff₀ hε]
    linarith [mul_comm ε R₁]
  have hRR' : R / ε ≤ R' / ε := by
    have hinv : (0 : ℝ) ≤ ε⁻¹ := (inv_pos.mpr hε).le
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hRR'le hinv
  have hhit : Hits F (Metric.closedBall (0 : Plane) (R' / ε)) v :=
    hits_closedBall_of_mem F (hz v) (le_trans hzv hRR')
  have hb := hR₁ (R' / ε) hL v hhit
  have hcollapse : δ / R' * (R' / ε) = δ / ε := by
    field_simp
  rw [hcollapse] at hb
  have hrev : ‖z v - Φ v‖ = ‖Φ v - z v‖ := norm_sub_rev _ _
  rw [hrev]
  have hmul : ε * ‖Φ v - z v‖ ≤ ε * (δ / ε) := mul_le_mul_of_nonneg_left hb hε.le
  have hcancel : ε * (δ / ε) = δ := by field_simp
  rwa [hcancel] at hmul

/-! ## The scaled representative gap across an ordinary edge -/

/-- A field is trivially uniformly sublinear against itself.  This lets the
representative-gap bound be obtained by *reusing*
`CoercivitySmallJumps.exists_pos_forall_neighbor_smallJump` with `Φ := z`, rather
than by repeating its geometric argument. -/
theorem uniformlySublinearError_self (F : IndexedCells V) (z : V → Plane) :
    UniformlySublinearError F z z := by
  intro η hη
  refine ⟨1, one_pos, fun R hR v _ => ?_⟩
  simp only [sub_self, norm_zero]
  exact mul_nonneg hη.le (le_trans zero_le_one hR)

/-- **Manuscript `tex:1652`, scaled form.**  For each fixed `R ≥ 0` and each
`δ > 0` there is `ε₀ > 0` such that for `0 < ε ≤ ε₀`, every ordinary edge issued
from a cell with `‖z_H‖ ≤ R/ε` has `ε‖z_{H'} - z_H‖ ≤ δ`.  This is
`|z_H - z_{H'}| ≤ d_H + d_{H'}` combined with `(p:eq:mesh)`, and it is the bound
on "the largest ordinary spatial jump" that controls the interpolation error. -/
theorem exists_pos_forall_scaled_neighborRepresentativeGap_le [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane) (hz : CellRepresentatives F z)
    (hdiam : SubmacroscopicDiameters F) {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ v w : V,
      F.graph.toSimpleGraph.Adj v w → ‖z v‖ ≤ R / ε → ε * ‖z w - z v‖ ≤ δ := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_pos_forall_neighbor_smallJump F hF z z hz
    (uniformlySublinearError_self F z) hdiam hR hδ
  exact ⟨ε₀, hε₀, fun ε hε hεle v w hadj hzv =>
    h ε hε hεle v w (F.graph.toSimpleGraph_adj.mp hadj) hzv⟩

/-! ## Transfer to the pathwise spatial extensions -/

/-! ## Transfer to the continuous interpolation -/

/-- **Manuscript `tex:1652`, interpolation clause.**  `Ztilde` is the continuous
interpolation of the representative path over its complete holding intervals
(`SpatialEnds.IsContinuousInterpolation`; this is the object whose law is
compared with the Brownian target in
`InvarianceMainStatement.RepresentativePathConclusions`), and `M` is the harmonic
spatial extension of the same path.  At every vertex-valued time of the contained
region the scaled difference is at most `δ`, once `ε` is small: the corrector
error contributes at most `δ/2`, and the interpolation error — bounded by the
ordinary spatial jump `|z_H - z_{H'}| ≤ d_H + d_{H'}` of its own holding
interval — contributes at most `δ/2`. -/
theorem exists_pos_forall_scaled_interpolation_sub_le [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Φ z : V → Plane)
    (hz : CellRepresentatives F z) (hsub : UniformlySublinearError F Φ z)
    (hdiam : SubmacroscopicDiameters F) {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (X : ℝ≥0 → State F) (Z Ztilde M : ℝ≥0 → Plane),
        IsContinuousInterpolation F z X Z Ztilde →
        IsSpatialExtension F Φ X M →
        ∀ (r : ℝ≥0) (v : V), X r = Sum.inl v → ‖z v‖ ≤ R / ε →
          ε * ‖Ztilde r - M r‖ ≤ δ := by
  obtain ⟨ε₁, hε₁pos, h₁⟩ :=
    exists_pos_forall_scaled_correctorError_le F Φ z hz hsub (half_pos hδ)
  obtain ⟨ε₂, hε₂pos, h₂⟩ :=
    exists_pos_forall_scaled_neighborRepresentativeGap_le F hF z hz hdiam hR (half_pos hδ)
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
  intro ε hε hεle X Z Ztilde M hI hM r v hXr hzv
  have hε1 : ε ≤ ε₁ := le_trans hεle (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := le_trans hεle (min_le_right _ _)
  obtain ⟨s, t, w, hHI, hrmem⟩ := hI.2.1 r v hXr
  have hadj : F.graph.toSimpleGraph.Adj v w := hHI.2.2.2.1
  have hst : s < t := hHI.1
  have hsr : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrmem.1
  have hrt : (r : ℝ) < (t : ℝ) := by exact_mod_cast hrmem.2
  have hstR : (s : ℝ) < (t : ℝ) := by exact_mod_cast hst
  set θ : ℝ := ((r : ℝ) - s) / ((t : ℝ) - s) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by linarith)]
    linarith
  have hZt : Ztilde r = AffineMap.lineMap (z v) (z w) θ :=
    hI.2.2.1 v w s t hHI r ⟨hrmem.1, hrmem.2.le⟩
  have hMr : M r = Φ v := hM.2.1 r v hXr
  have hsplit : Ztilde r - M r = θ • (z w - z v) + (z v - Φ v) := by
    rw [hZt, hMr, AffineMap.lineMap_apply_module']
    abel
  have hnorm : ‖Ztilde r - M r‖ ≤ ‖z w - z v‖ + ‖z v - Φ v‖ := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ le_rfl)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ1
  have hmul : ε * ‖Ztilde r - M r‖ ≤ ε * (‖z w - z v‖ + ‖z v - Φ v‖) :=
    mul_le_mul_of_nonneg_left hnorm hε.le
  have hgap : ε * ‖z w - z v‖ ≤ δ / 2 := h₂ ε hε hε2 v w hadj hzv
  have hcorr : ε * ‖z v - Φ v‖ ≤ δ / 2 := h₁ ε hε hε1 v hzv
  nlinarith [hmul, hgap, hcorr]

/-! ## From vertex times to all times -/

/-- Vertex-valued times are right-dense: every time is approached from the right
by times at which the path sits at an actual vertex.  This is what the
manuscript's "extends from vertex times to all times by their right-continuous
extensions" presupposes; it is a property of the reflected walk and is **not**
implied by `IsSpatialExtension` or `IsContinuousInterpolation`. -/
def RightDenseVertexTimes (F : IndexedCells V) (X : ℝ≥0 → State F) : Prop :=
  ∀ t : ℝ≥0, ∃ᶠ s in 𝓝[>] t, ∃ v : V, X s = Sum.inl v

/-- **Manuscript `tex:1652`, first sentence.**  A bound holding at every
vertex-valued time strictly before `T` extends to every time strictly before `T`,
for any function that is right-continuous everywhere, provided vertex times are
right-dense. -/
theorem le_of_forall_vertexTime_le (F : IndexedCells V)
    {X : ℝ≥0 → State F} {g : ℝ≥0 → ℝ}
    (hg : ∀ u : ℝ≥0, ContinuousWithinAt g (Set.Ioi u) u)
    (hdense : RightDenseVertexTimes F X) {c : ℝ} {T : ℝ≥0}
    (hvertex : ∀ (s : ℝ≥0) (v : V), s < T → X s = Sum.inl v → g s ≤ c)
    {r : ℝ≥0} (hr : r < T) : g r ≤ c := by
  have hnhds : ∀ᶠ s : ℝ≥0 in 𝓝 r, s < T := gt_mem_nhds hr
  have hlt : ∀ᶠ s : ℝ≥0 in 𝓝[>] r, s < T := hnhds.filter_mono nhdsWithin_le_nhds
  have hfreq : ∃ᶠ s in 𝓝[>] r, g s ∈ Set.Iic c := by
    refine ((hdense r).and_eventually hlt).mono ?_
    rintro s ⟨⟨v, hv⟩, hsT⟩
    exact hvertex s v hsT hv
  exact isClosed_Iic.mem_of_frequently_of_tendsto hfreq (hg r)

/-- **Manuscript `tex:1648-1652`, all times.**  Combining the interpolation
transfer with the right-continuous extension: on the compact containment event,
and for every time strictly before the horizon `T`, the continuous interpolation
of the representative path stays within `δ/ε` of the harmonic spatial extension.

This statement is **conditional** on `RightDenseVertexTimes F X`, an open input
about the reflected walk; see the module docstring. -/
theorem exists_pos_forall_scaled_interpolation_sub_le_allTimes [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Φ z : V → Plane)
    (hz : CellRepresentatives F z) (hsub : UniformlySublinearError F Φ z)
    (hdiam : SubmacroscopicDiameters F) {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (X : ℝ≥0 → State F) (Z Ztilde M : ℝ≥0 → Plane),
        IsContinuousInterpolation F z X Z Ztilde →
        IsSpatialExtension F Φ X M →
        RightDenseVertexTimes F X →
        ∀ T : ℝ≥0, (∀ (s : ℝ≥0) (v : V), s < T → X s = Sum.inl v → ‖z v‖ ≤ R / ε) →
          ∀ r : ℝ≥0, r < T → ε * ‖Ztilde r - M r‖ ≤ δ := by
  obtain ⟨ε₀, hε₀, h⟩ :=
    exists_pos_forall_scaled_interpolation_sub_le F hF Φ z hz hsub hdiam hR hδ
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle X Z Ztilde M hI hM hdense T hcont r hr
  refine le_of_forall_vertexTime_le F (g := fun u => ε * ‖Ztilde u - M u‖) ?_ hdense
    (c := δ) (T := T) (fun s v hsT hXs => h ε hε hεle X Z Ztilde M hI hM s v hXs
      (hcont s v hsT hXs)) hr
  intro u
  have hZc : ContinuousWithinAt Ztilde (Set.Ioi u) u := hI.1.continuousWithinAt
  have hMc : ContinuousWithinAt M (Set.Ioi u) u := hM.1.isRightContinuous u
  exact continuousWithinAt_const.mul (hZc.sub hMc).norm

end ReflectedGMS.CorrectorInterpolationTransfer
