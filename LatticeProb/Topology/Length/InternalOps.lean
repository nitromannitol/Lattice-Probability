/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/InternalOps.lean.
-/
import LatticeProb.Topology.Length.Internal
import LatticeProb.Topology.Length.SetDist

/-!
# Internal metrics: scaling, first hitting times and boundary distance

For a pseudo-emetric space `X` and `Y : Set X`, this file records four facts about the internal
metric `internalEDist Y` and about path lengths.

* Scaling: a map multiplying all distances by a constant `c ∈ (0, ∞)` multiplies the lengths of
  curves and paths by `c`, and multiplies internal distances on images by `c`
  (`curveLength_comp_of_edist_eq`, `pathLength_map_of_edist_eq`, `internalEDist_image_of_edist_eq`).
* First hitting times: a continuous curve on `[a, b]` that meets a closed set has a first time of
  meeting it (`exists_first_hit`).
* Path crossings: a path from a point of an open set `V` to a point outside `V` meets the frontier
  of `V` (`exists_mem_frontier_of_path`).
* Boundary distance: in a length space, for `u` in an open set `V`, the distance from `u` to the
  complement of `V` equals the distance from `u` to the frontier of `V`
  (`infEDist_compl_eq_infEDist_frontier`). A geodesic from `u` to `v` with
  `d(u, v) ≤ d(u, ∂V)` stays in `V` (`IsGeodesicCurve.mapsTo_of_edist_le_infEDist`), and in a
  proper length space this gives `d(u, v; V) = d(u, v)` (`internalEDist_eq_edist_of_le_infEDist`).
-/

open Set Filter Topology unitInterval
open scoped ENNReal

namespace LatticeProb.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Scaling -/

section Scaling

variable {Z : Type*} [PseudoEMetricSpace Z]

/-- A map multiplying all distances by `c` multiplies the length of every curve by `c`. -/
theorem curveLength_comp_of_edist_eq {f : X → Z} {c : ℝ≥0∞}
    (hf : ∀ a b, edist (f a) (f b) = c * edist a b) (P : ℝ → X) (a b : ℝ) :
    curveLength (f ∘ P) a b = c * curveLength P a b := by
  unfold curveLength eVariationOn
  rw [ENNReal.mul_iSup]
  congr 1
  funext p
  rw [Finset.mul_sum]
  simp only [Function.comp, hf]

/-- A map multiplying all distances by `c` multiplies the length of every path by `c`. -/
theorem pathLength_map_of_edist_eq {f : X → Z} {c : ℝ≥0∞}
    (hf : ∀ a b, edist (f a) (f b) = c * edist a b) (hfc : Continuous f) {x y : X}
    (γ : Path x y) : pathLength (γ.map hfc) = c * pathLength γ := by
  unfold pathLength
  rw [← curveLength_comp_of_edist_eq hf]
  rfl

/-- If `e : X ≃ Z` multiplies distances by `c ∈ (0, ∞)`, then
`d_Z(e x, e y; e '' Y) = c · d_X(x, y; Y)`. -/
theorem internalEDist_image_of_edist_eq (e : X ≃ Z) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (he : ∀ a b, edist (e a) (e b) = c * edist a b) (Y : Set X) (x y : X) :
    internalEDist (e '' Y) (e x) (e y) = c * internalEDist Y x y := by
  have hlip : LipschitzWith c.toNNReal e := fun a b => by rw [he, ENNReal.coe_toNNReal hct]
  have hsymm : ∀ a b, edist (e.symm a) (e.symm b) = c⁻¹ * edist a b := fun a b => by
    have h := he (e.symm a) (e.symm b)
    rw [e.apply_symm_apply, e.apply_symm_apply] at h
    rw [h, ENNReal.inv_mul_cancel_left hc0 hct]
  have hlip' : LipschitzWith c⁻¹.toNNReal e.symm := fun a b => by
    rw [hsymm, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 hc0)]
  refine le_antisymm ?_ ?_
  · rw [show c * internalEDist Y x y = ⨅ γ : {γ : Path x y // ∀ t, γ t ∈ Y}, c * pathLength γ.1
      from ENNReal.mul_iInf_of_ne hc0 hct]
    exact le_iInf fun γ => (internalEDist_le_pathLength (Y := e '' Y) (γ.1.map hlip.continuous)
      fun t => ⟨_, γ.2 t, rfl⟩).trans_eq (pathLength_map_of_edist_eq he hlip.continuous γ.1)
  · refine le_iInf fun γ => ?_
    let δ : Path x y := (γ.1.map hlip'.continuous).cast (e.symm_apply_apply x).symm
      (e.symm_apply_apply y).symm
    have hδ : ∀ t, δ t ∈ Y := fun t => by
      obtain ⟨z, hz, hzeq⟩ := γ.2 t
      show e.symm (γ.1 t) ∈ Y
      rw [← hzeq, e.symm_apply_apply]
      exact hz
    have hlen : pathLength δ = c⁻¹ * pathLength γ.1 :=
      pathLength_map_of_edist_eq hsymm hlip'.continuous γ.1
    calc c * internalEDist Y x y ≤ c * pathLength δ :=
          by gcongr; exact internalEDist_le_pathLength δ hδ
      _ = pathLength γ.1 := by rw [hlen, ENNReal.mul_inv_cancel_left hc0 hct]

end Scaling

/-! ### First hitting times -/

/-- The first hitting time of a closed set `A` by a curve `P` on `[a, b]`: if `P` meets `A` on
`[a, b]`, there is `s₀ ∈ [a, b]` with `P s₀ ∈ A` and `P t ∉ A` for all `t ∈ [a, s₀)`. -/
theorem exists_first_hit {X' : Type*} [TopologicalSpace X'] {P : ℝ → X'} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) {A : Set X'} (hA : IsClosed A)
    (hne : ∃ t ∈ Icc a b, P t ∈ A) :
    ∃ s₀ ∈ Icc a b, P s₀ ∈ A ∧ ∀ t ∈ Ico a s₀, P t ∉ A := by
  set S := Icc a b ∩ P ⁻¹' A
  have hS : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hA
  have hSne : S.Nonempty := let ⟨t, ht, htA⟩ := hne; ⟨t, ht, htA⟩
  have hbdd : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  have hmem := hS.csInf_mem hSne hbdd
  refine ⟨sInf S, hmem.1, hmem.2, fun t ht htA => ?_⟩
  have : sInf S ≤ t := csInf_le hbdd ⟨⟨ht.1, ht.2.le.trans hmem.1.2⟩, htA⟩
  exact absurd ht.2 (not_lt.2 this)

/-! ### Boundary distance and paths near a point -/

/-- The distance from the starting point of a path to any of its points is at most the length of
the path. -/
theorem edist_le_pathLength_apply {x y : X} (γ : Path x y) (t : I) :
    edist x (γ t) ≤ pathLength γ := by
  have h1 := edist_le_curveLength γ.extend t.2.1
  rw [Path.extend_zero, Path.extend_extends'] at h1
  exact h1.trans (curveLength_mono γ.extend le_rfl t.2.2)

/-- A path from a point of the open set `V` to a point outside `V` meets the frontier of `V`. -/
theorem exists_mem_frontier_of_path {X' : Type*} [TopologicalSpace X'] {V : Set X'}
    (hV : IsOpen V) {u w : X'} (γ : Path u w) (hu : u ∈ V) (hw : w ∉ V) :
    ∃ t, γ t ∈ frontier V := by
  by_contra h
  simp only [not_exists] at h
  have hsub : range γ ⊆ V := by
    refine (isPreconnected_range γ.continuous).subset_left_of_subset_union hV
      isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.2 subset_closure) ?_
      ⟨u, ⟨0, γ.source⟩, hu⟩
    rintro _ ⟨t, rfl⟩
    by_cases ht : γ t ∈ V
    · exact Or.inl ht
    · exact Or.inr fun hcl => h t ⟨hcl, by rwa [hV.interior_eq]⟩
  exact hw (hsub ⟨1, γ.target⟩)

/-- In a length space, for `u` in the open set `V`, the distance from `u` to the complement of `V`
equals the distance from `u` to the frontier of `V`. -/
theorem infEDist_compl_eq_infEDist_frontier (hX : IsLengthSpace X) {V : Set X} (hV : IsOpen V)
    {u : X} (hu : u ∈ V) : Metric.infEDist u Vᶜ = Metric.infEDist u (frontier V) := by
  refine le_antisymm (Metric.infEDist_anti fun x hx hxV => hx.2 (by rwa [hV.interior_eq]))
    (Metric.le_infEDist.2 fun w hw => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  obtain ⟨γ, hγ⟩ := hX u w ε (by exact_mod_cast hε)
  rw [ENNReal.ofReal_coe_nnreal] at hγ
  obtain ⟨t, ht⟩ := exists_mem_frontier_of_path hV γ hu hw
  exact (Metric.infEDist_le_edist_of_mem ht).trans ((edist_le_pathLength_apply γ t).trans hγ)

/-- In a length space, if `u, v` lie in the open set `V` and `d(u, v) ≤ d(u, ∂V)`, then every
geodesic curve from `u` to `v` stays in `V`. -/
theorem IsGeodesicCurve.mapsTo_of_edist_le_infEDist (hX : IsLengthSpace X) {P : ℝ → X}
    {a b : ℝ} (hP : IsGeodesicCurve P a b) (hfin : edist (P a) (P b) ≠ ∞) {V : Set X}
    (hV : IsOpen V) (ha : P a ∈ V) (hb : P b ∈ V)
    (hle : edist (P a) (P b) ≤ Metric.infEDist (P a) (frontier V)) : MapsTo P (Icc a b) V := by
  rw [← infEDist_compl_eq_infEDist_frontier hX hV ha] at hle
  intro t ht
  by_contra hPt
  have hadd := hP.edist_add hfin le_rfl ht.1 ht.2 le_rfl
  have h1 : edist (P a) (P b) ≤ edist (P a) (P t) :=
    hle.trans (Metric.infEDist_le_edist_of_mem hPt)
  have hA : edist (P a) (P t) ≠ ∞ := ne_top_of_le_ne_top hfin (hadd ▸ le_self_add)
  have h0 : edist (P t) (P b) = 0 := by
    refine (ENNReal.add_right_inj hA).1 ?_
    rw [add_zero]
    exact le_antisymm (hadd.le.trans h1) le_self_add
  obtain ⟨r, hr, hball⟩ := EMetric.isOpen_iff.1 hV (P b) hb
  exact hPt (hball (by rw [Metric.mem_eball, h0]; exact hr))

/-- In a proper length metric space, if `u, v` lie in the open set `V` and `d(u, v) ≤ d(u, ∂V)`,
then the internal distance `d(u, v; V)` equals `d(u, v)`. -/
theorem internalEDist_eq_edist_of_le_infEDist {X : Type*} [MetricSpace X] [ProperSpace X]
    (hX : IsLengthSpace X) {V : Set X} (hV : IsOpen V) {u v : X} (hu : u ∈ V) (hv : v ∈ V)
    (hle : edist u v ≤ Metric.infEDist u (frontier V)) : internalEDist V u v = edist u v := by
  obtain ⟨γ, hγ⟩ := exists_shortest_path hX u v
  have hgeo : IsGeodesicPath γ := (isGeodesicPath_iff_forall_le hX γ).2 hγ
  have hcurve := (isGeodesicPath_iff_isGeodesicCurve γ).1 hgeo
  have hmaps := hcurve.mapsTo_of_edist_le_infEDist hX (by simp [edist_ne_top]) hV
    (by simpa using hu) (by simpa using hv) (by simpa using hle)
  refine le_antisymm ((internalEDist_le_pathLength γ fun t => ?_).trans_eq hgeo)
    (edist_le_internalEDist V u v)
  have := hmaps t.2
  rwa [Path.extend_extends'] at this

/-! ### Nonvacuity examples on `ℝ` -/

namespace InternalOpsExample

/-- The segment from `x` to `y` in `ℝ`, parametrised by `[0, 1]`. -/
def segment (x y : ℝ) : Path x y where
  toFun t := x + (t : ℝ) • (y - x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- `ℝ` is a length space: the segment from `x` to `y` has length `d(x, y)`. -/
theorem isLengthSpace_real : IsLengthSpace ℝ := by
  intro x y ε hε
  have hlip : LipschitzWith ‖y - x‖₊ (fun s : ℝ => x + s • (y - x)) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    show dist (x + s • (y - x)) (x + t • (y - x)) ≤ (‖y - x‖₊ : ℝ) * dist s t
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq,
      coe_nnnorm]
    exact le_of_eq (mul_comm _ _)
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, (segment x y).extend t = x + t • (y - x) := fun t ht =>
    (Path.extend_apply (segment x y) ht).trans rfl
  refine ⟨segment x y, ?_⟩
  calc pathLength (segment x y) = curveLength (fun s : ℝ => x + s • (y - x)) 0 1 := by
        unfold pathLength
        exact curveLength_congr fun t ht => hγ t ht
    _ ≤ ‖y - x‖₊ * eVariationOn (id : ℝ → ℝ) (Icc 0 1) := by
        unfold curveLength
        exact hlip.lipschitzOnWith.comp_eVariationOn_le (g := id) (mapsTo_univ _ _)
    _ = edist x y := by
        rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one, edist_comm,
          edist_eq_enorm_sub, enorm_eq_nnnorm]
    _ ≤ edist x y + ENNReal.ofReal ε := le_self_add

/-- The identity `t ↦ t` is a geodesic curve on `[0, 1]` in `ℝ`. -/
theorem isGeodesicCurve_id : IsGeodesicCurve (fun t : ℝ => t) 0 1 := by
  unfold IsGeodesicCurve
  refine ⟨zero_le_one, continuous_id.continuousOn, ?_⟩
  change eVariationOn id (Icc (0 : ℝ) 1) = edist (0 : ℝ) 1
  rw [eVariationOn_id_Icc, edist_dist, Real.dist_eq]
  norm_num

/-- Scaling by `1` satisfies the hypothesis of `curveLength_comp_of_edist_eq`. -/
example : curveLength (id ∘ fun t : ℝ => t) 0 1 = 1 * curveLength (fun t : ℝ => t) 0 1 :=
  curveLength_comp_of_edist_eq (f := (id : ℝ → ℝ)) (c := 1) (fun a b => by simp)
    (fun t : ℝ => t) 0 1

/-- Scaling by `1` satisfies the hypothesis of `pathLength_map_of_edist_eq`. -/
example : pathLength ((segment 0 1).map (continuous_id : Continuous (id : ℝ → ℝ))) =
    1 * pathLength (segment 0 1) :=
  pathLength_map_of_edist_eq (f := (id : ℝ → ℝ)) (c := 1) (fun a b => by simp) continuous_id
    (segment 0 1)

/-- The identity map of `ℝ` satisfies the hypotheses of `internalEDist_image_of_edist_eq`, so
`d(1/3, 1/2; (0, 1)) = d(1/3, 1/2; (0, 1))` after scaling by `1`. -/
example : internalEDist ((Equiv.refl ℝ) '' Ioo (0 : ℝ) 1) ((Equiv.refl ℝ) (1 / 3))
      ((Equiv.refl ℝ) (1 / 2)) = 1 * internalEDist (Ioo (0 : ℝ) 1) (1 / 3) (1 / 2) :=
  internalEDist_image_of_edist_eq (Equiv.refl ℝ) one_ne_zero ENNReal.one_ne_top
    (fun a b => by simp) (Ioo (0 : ℝ) 1) (1 / 3) (1 / 2)

/-- The identity curve `t ↦ t` on `[0, 1]` meets the closed set `{1}`, so `exists_first_hit`
applies. -/
example : ∃ s₀ ∈ Icc (0 : ℝ) 1, (fun t : ℝ => t) s₀ ∈ ({1} : Set ℝ) ∧
    ∀ t ∈ Ico (0 : ℝ) s₀, (fun t : ℝ => t) t ∉ ({1} : Set ℝ) :=
  exists_first_hit continuous_id.continuousOn isClosed_singleton
    ⟨1, ⟨zero_le_one, le_rfl⟩, Set.mem_singleton _⟩

/-- The distance from the start of a segment to any of its points is at most its length. -/
example (t : I) : edist (0 : ℝ) (segment 0 1 t) ≤ pathLength (segment 0 1) :=
  edist_le_pathLength_apply _ t

/-- The segment from `1/2` to `2` leaves `(0, 1)`, so it meets the frontier of `(0, 1)`. -/
example : ∃ t : I, segment (1 / 2) 2 t ∈ frontier (Ioo (0 : ℝ) 1) :=
  exists_mem_frontier_of_path isOpen_Ioo (segment (1 / 2) 2) ⟨by norm_num, by norm_num⟩
    (by norm_num)

/-- In `ℝ`, for `u = 1/3` in `(0, 1)`, the distance from `u` to the complement of `(0, 1)` equals
the distance to the frontier `{0, 1}`. -/
example : Metric.infEDist (1 / 3 : ℝ) (Ioo (0 : ℝ) 1)ᶜ =
    Metric.infEDist (1 / 3 : ℝ) (frontier (Ioo (0 : ℝ) 1)) :=
  infEDist_compl_eq_infEDist_frontier isLengthSpace_real isOpen_Ioo ⟨by norm_num, by norm_num⟩

/-- In `ℝ`, the geodesic `t ↦ t` on `[0, 1]` stays in `(-1, 2)`, since `d(0, 1) = 1` does not
exceed `d(0, {-1, 2}) = 1`. -/
example : MapsTo (fun t : ℝ => t) (Icc (0 : ℝ) 1) (Ioo (-1 : ℝ) 2) := by
  refine isGeodesicCurve_id.mapsTo_of_edist_le_infEDist isLengthSpace_real
    (edist_ne_top _ _) isOpen_Ioo (V := Ioo (-1 : ℝ) 2) ?_ ?_ ?_
  · norm_num
  · norm_num
  · rw [frontier_Ioo (show (-1 : ℝ) < 2 by norm_num)]
    refine Metric.le_infEDist.2 ?_
    rintro w (rfl | rfl)
    · rw [edist_dist, edist_dist]
      apply ENNReal.ofReal_le_ofReal
      norm_num [Real.dist_eq]
    · rw [edist_dist, edist_dist]
      apply ENNReal.ofReal_le_ofReal
      norm_num [Real.dist_eq]

/-- In `ℝ`, two points `1/4` and `1/2` of the open interval `(0, 1)` satisfy the hypothesis of
`internalEDist_eq_edist_of_le_infEDist`, so their internal distance in `(0, 1)` is their
distance. -/
example : internalEDist (Ioo (0 : ℝ) 1) (1 / 4) (1 / 2) = edist (1 / 4 : ℝ) (1 / 2) := by
  refine internalEDist_eq_edist_of_le_infEDist isLengthSpace_real isOpen_Ioo
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ?_
  rw [frontier_Ioo (show (0 : ℝ) < 1 by norm_num)]
  refine Metric.le_infEDist.2 ?_
  rintro w (rfl | rfl)
  · rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    norm_num [Real.dist_eq]
  · rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    norm_num [Real.dist_eq]

end InternalOpsExample

end LatticeProb.MetricGeometry
