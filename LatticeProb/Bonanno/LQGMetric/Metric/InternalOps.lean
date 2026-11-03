/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.InternalOps at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Metric.SetDist

/-!
# Internal metrics: disjoint unions, scaling, boundary distance, geodesics (LM S-int (c), (d);
GM S3.1; GM S4.2)

* `internalEDist_iUnion_eq` (**LM S-int (c)**, LM tex:556): for pairwise disjoint open `W i` and
  `x ∈ W i`, `d(x, ·; ⋃ W) = d(x, ·; W i)`; in particular (`internalEDist_iUnion_eq_top`) it is
  `∞` between different pieces. A path is connected, so it cannot leave `W i`.
* `curveLength_comp_of_edist_eq`, `internalEDist_image_of_edist_eq` (**LM S-int (d)**, LM tex:813):
  a bijection multiplying distances by `c ∈ (0, ∞)` multiplies lengths and internal metrics by
  `c` (for `ℂ` carrying `D` and `cD`, take the identity).
* `infEDist_compl_eq_infEDist_frontier`: in a length space, for `u ∈ V` open,
  `d(u, Vᶜ) = d(u, ∂V)` (a near-minimal path from `u` to a point outside `V` crosses `∂V`).
* `IsGeodesicCurve.mapsTo_of_edist_le_infEDist`, `internalEDist_eq_edist_of_le_infEDist`
  (**GM S3.1 (b)**, GM tex:1197, 1351–1357): if `d(u, v) ≤ d(u, ∂V)`, `v ∈ V`, then every
  geodesic from `u` to `v` lies in `V`, and (in a proper length space) `d(u, v; V) = d(u, v)`.
  GM S3.1 (c) (lengths of paths in `V` agree for `d` and `d(·,·;V)`) is
  `InternalSpace.curveLength_internalSpace` (BBI Prop. 2.3.12(1)).
* `exists_first_hit`, `IsGeodesicCurve.firstHit_outside` (**GM S4.2**, GM tex:1697): a geodesic
  from a point outside the open set `O` which enters `O`, stopped at its first hitting time `σ`
  of `closure O`, is a path in `Oᶜ` that meets `∂O` only at its endpoint `P σ`, has minimal length
  among all curves between its endpoints, and its length is `d(P a, P σ; Oᶜ)`.

Sources: GM = Gwynne–Miller, arXiv:1905.00383 (`uniqueness-final.tex`); LM = Gwynne–Miller,
arXiv:1905.00379 (`local-metrics-final.tex`); BBI = Burago–Burago–Ivanov, *A course in metric
geometry*, §2.3. These facts are used without proof in GM/LM; the arguments here are the
elementary ones indicated there (connectedness of paths; truncation at a first hitting time).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology unitInterval
open scoped ENNReal

namespace LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Disjoint unions (LM S-int (c)) -/

/-! ### Scaling (LM S-int (d)) -/

section Scaling

variable {Z : Type*} [PseudoEMetricSpace Z]

/-- A map multiplying distances by `c` multiplies lengths by `c`. -/
theorem curveLength_comp_of_edist_eq {f : X → Z} {c : ℝ≥0∞}
    (hf : ∀ a b, edist (f a) (f b) = c * edist a b) (P : ℝ → X) (a b : ℝ) :
    curveLength (f ∘ P) a b = c * curveLength P a b := by
  unfold curveLength eVariationOn
  rw [ENNReal.mul_iSup]
  congr 1
  funext p
  rw [Finset.mul_sum]
  simp only [Function.comp, hf]

theorem pathLength_map_of_edist_eq {f : X → Z} {c : ℝ≥0∞}
    (hf : ∀ a b, edist (f a) (f b) = c * edist a b) (hfc : Continuous f) {x y : X}
    (γ : Path x y) : pathLength (γ.map hfc) = c * pathLength γ := by
  unfold pathLength
  rw [← curveLength_comp_of_edist_eq hf]
  rfl

/-- **LM S-int (d).** If `e : X ≃ Z` multiplies distances by `c ∈ (0, ∞)`, then
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

/-- The first hitting time of a closed set by a curve on `[a, b]`. -/
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

/-! ### Boundary distance and geodesics near a point (GM S3.1) -/

theorem edist_le_pathLength_apply {x y : X} (γ : Path x y) (t : I) :
    edist x (γ t) ≤ pathLength γ := by
  have h1 := edist_le_curveLength γ.extend t.2.1
  rw [Path.extend_zero, Path.extend_extends'] at h1
  exact h1.trans (curveLength_mono γ.extend le_rfl t.2.2)

/-- A path from a point of the open set `V` to a point outside `V` meets `∂V`. -/
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

/-- In a length space, for `u` in the open set `V`, `d(u, Vᶜ) = d(u, ∂V)`. -/
theorem infEDist_compl_eq_infEDist_frontier (hX : IsLengthSpace X) {V : Set X} (hV : IsOpen V)
    {u : X} (hu : u ∈ V) : Metric.infEDist u Vᶜ = Metric.infEDist u (frontier V) := by
  refine le_antisymm (Metric.infEDist_anti fun x hx hxV => hx.2 (by rwa [hV.interior_eq]))
    (Metric.le_infEDist.2 fun w hw => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  obtain ⟨γ, hγ⟩ := hX u w ε (by exact_mod_cast hε)
  rw [ENNReal.ofReal_coe_nnreal] at hγ
  obtain ⟨t, ht⟩ := exists_mem_frontier_of_path hV γ hu hw
  exact (Metric.infEDist_le_edist_of_mem ht).trans ((edist_le_pathLength_apply γ t).trans hγ)

/-- **GM S3.1 (b)** (GM tex:1197, 1351–1357). In a length space, if `u, v ∈ V` (open) and
`d(u, v) ≤ d(u, ∂V) `, then every geodesic from `u` to `v` stays in `V`. -/
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

/-- **GM S3.1 (b)**, internal-metric form: in a proper length metric space, if `u, v ∈ V` (open)
and `d(u, v) ≤ d(u, ∂V)`, then `d(u, v; V) = d(u, v)`. -/
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

/-! ### First hitting of a ball by a geodesic (GM S4.2) -/

end LQGMetric.MetricGeometry
