/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusMeas3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas2

/-!
# GM Lemma 3.7: geodesics inside `𝔸_{r/2,2r}(z)` through the internal metric (task P2-M2E2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, proof
of Lemma 3.7, l. 1354–1358: "If `P` is a path from `u` to `v` which stays in `cl 𝔸_{αr,r}(z)`,
then `P` is a `D_h`-geodesic iff `len(P; D_h) = D_h(u,v)`. Hence if condition 2 holds, then `P`
cannot be a `D_h`-geodesic unless `D_h(u,v) ≤ D_h(u, ∂𝔸_{r/2,2r}(z))` …, in which case we can tell
whether `P` is a `D_h`-geodesic from the restriction of `h` to the `D_h`-metric ball of radius
`D_h(u, ∂𝔸_{r/2,2r}(z))` centred at `u`."

* `lenFun_pj_le`: a path `η` with `f(η s, η t) = |t − s| c` has `f`-length `≤ c` (telescoping).
* `internal_eq_of_le`: `D(x,y;V) = D(x,y)` when `D(x,y) ≤ D(x,∂V)` (GM S3.1 (b)).
* `IsGeodI`, `isGeod01_iff_isGeodI`: when `D(u,v) ≤ D(u,∂V)`, the `D`-geodesics from `u` to `v` are
  exactly the paths in `V` which are geodesics for the internal metric `D(·,·;V)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- telescoping: a path `η` with `f(η s, η t) = |t − s| c` has `f`-length at most `c` -/
lemma lenFun_pj_le {f : ℂ → ℂ → ℝ≥0∞} {η : C(unitInterval, ℂ)} {c : ℝ≥0∞}
    (h : ∀ s t : unitInterval, f (η s) (η t) = ENNReal.ofReal |(t : ℝ) - s| * c) :
    lenFun f (fun t => η (pj t)) 0 1 ≤ c := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  have e : ∀ i, f (η (pj (u (i + 1)))) (η (pj (u i))) =
      ENNReal.ofReal (u (i + 1) - u i) * c := fun i => by
    rw [h, pj_coe_of_mem (hus i), pj_coe_of_mem (hus (i + 1)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (hu (Nat.le_succ i)))]
  calc ∑ i ∈ Finset.range n, f (η (pj (u (i + 1)))) (η (pj (u i)))
      = (∑ i ∈ Finset.range n, ENNReal.ofReal (u (i + 1) - u i)) * c := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => e i
    _ = ENNReal.ofReal (u n - u 0) * c := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.2 (hu (Nat.le_succ i))),
          Finset.sum_range_sub (fun i => u i)]
    _ ≤ 1 * c := by
        gcongr
        exact ENNReal.ofReal_le_one.2 (by linarith [(hus n).2, (hus 0).1])
    _ = c := one_mul c

/-- `D`-length as `lenFun` of the distance -/
lemma len_eq_lenFun (D : ContMetric) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b = lenFun (fun x y => ENNReal.ofReal (D.1 (x, y))) P a b := by
  unfold ContMetric.len curveLength eVariationOn lenFun
  simp only [Function.comp_apply, ContMetric.edist_pt]

lemma setDist_singleton_eq (D : ContMetric) (x : ℂ) (S : Set ℂ) :
    setDist D {x} S = Metric.infEDist (D.pt x) (D.pt '' S) := by
  rw [setDist, image_singleton, setEDist, iInf_singleton]

/-- **GM S3.1 (b)**: `D(x,y;V) = D(x,y)` if `x, y ∈ V` (open) and `D(x,y) ≤ D(x,∂V)` -/
lemma internal_eq_of_le (D : ContMetric) (hD : D.IsLength) [ProperSpace D.Space] {V : Set ℂ}
    (hV : IsOpen V) {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V)
    (hle : ENNReal.ofReal (D.1 (x, y)) ≤ setDist D {x} (frontier V)) :
    D.internal V x y = ENNReal.ofReal (D.1 (x, y)) := by
  have hfr : D.pt '' frontier V = frontier (D.pt '' V) := D.ptHomeomorph.image_frontier V
  rw [setDist_singleton_eq, hfr, ← ContMetric.edist_pt] at hle
  rw [← ContMetric.edist_pt]
  exact internalEDist_eq_edist_of_le_infEDist hD (D.isOpen_image_pt hV) ⟨x, hx, rfl⟩
    ⟨y, hy, rfl⟩ hle

lemma setDist_le_add (D : ContMetric) (x y : ℂ) (S : Set ℂ) :
    setDist D {x} S ≤ setDist D {y} S + ENNReal.ofReal (D.1 (x, y)) := by
  rw [setDist_singleton_eq, setDist_singleton_eq, ← ContMetric.edist_pt]
  exact Metric.infEDist_le_infEDist_add_edist

/-- a geodesic for the internal metric `J` of `V`, from `u` to `v`, inside `V` -/
def IsGeodI (J : ℂ → ℂ → ℝ≥0∞) (V : Set ℂ) (u v : ℂ) (η : C(unitInterval, ℂ)) : Prop :=
  η 0 = u ∧ η 1 = v ∧ (∀ t, η t ∈ V) ∧
    ∀ s t : unitInterval, J (η s) (η t) = ENNReal.ofReal |(t : ℝ) - s| * J u v

lemma dist_geod_left {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)} (h : D.IsGeod01 u v η)
    (t : unitInterval) : D.1 (u, η t) = t * D.1 (u, v) := by
  obtain ⟨h0, -, hd⟩ := h
  have := hd 0 t
  rwa [h0, Set.Icc.coe_zero, sub_zero, abs_of_nonneg t.2.1] at this

/-- **GM l. 1354–1358**: if `D(u,v) ≤ D(u,∂V)`, the `D`-geodesics from `u` to `v` are exactly the
`D(·,·;V)`-geodesics inside `V` (own elementary argument from GM S3.1 (b)). -/
theorem isGeod01_iff_isGeodI (D : ContMetric) (hD : D.IsLength) [ProperSpace D.Space]
    {V : Set ℂ} (hV : IsOpen V) {u v : ℂ} (hu : u ∈ V) (hv : v ∈ V)
    (hle : ENNReal.ofReal (D.1 (u, v)) ≤ setDist D {u} (frontier V))
    (η : C(unitInterval, ℂ)) : D.IsGeod01 u v η ↔ IsGeodI (D.internal V) V u v η := by
  set L := D.1 (u, v) with hL
  have hL0 : 0 ≤ L := D.nonneg u v
  have hJuv : D.internal V u v = ENNReal.ofReal L := internal_eq_of_le D hD hV hu hv hle
  constructor
  · intro hg
    obtain ⟨h0, h1, hd⟩ := hg
    have hmem : ∀ t : unitInterval, η t ∈ V := fun t => by
      by_cases ht1 : (t : ℝ) = 1
      · rw [show t = 1 from Subtype.ext ht1, h1]; exact hv
      rcases hL0.eq_or_lt with hL0' | hLpos
      · have hz : D.1 (u, v) = 0 := hL0'.symm
        have : D.1 (u, η t) = 0 := by
          rw [dist_geod_left ⟨h0, h1, hd⟩ t, hz, mul_zero]
        have := (dist_eq_zero (x := D.pt u) (y := D.pt (η t))).1 this
        rw [← show u = η t from this]; exact hu
      · have hlt : ENNReal.ofReal (D.1 (u, η t)) < setDist D {u} (frontier V) := by
          rw [dist_geod_left ⟨h0, h1, hd⟩ t]
          refine lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff hLpos |>.2 ?_) hle
          have : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
          nlinarith
        rw [setDist_singleton_eq, ← ContMetric.edist_pt] at hlt
        exact (ContMetric.internal_eq_of_lt_infEDist_frontier hD hV hu hlt).1
    have key : ∀ s t : unitInterval, (s : ℝ) ≤ t →
        D.internal V (η s) (η t) = ENNReal.ofReal |(t : ℝ) - s| * D.internal V u v := by
      intro s t hst
      have hdst : D.1 (η s, η t) = ((t : ℝ) - s) * L := by
        rw [hd s t, abs_of_nonneg (sub_nonneg.2 hst)]
      have hus : D.1 (u, η s) = s * L := dist_geod_left ⟨h0, h1, hd⟩ s
      have hle' : ENNReal.ofReal (D.1 (η s, η t)) ≤ setDist D {η s} (frontier V) := by
        have h2 := hle.trans (setDist_le_add D u (η s) (frontier V))
        rw [hus] at h2
        have h3 : ENNReal.ofReal (L - s * L) ≤ setDist D {η s} (frontier V) := by
          rw [ENNReal.ofReal_sub _ (by have := s.2.1; positivity)]
          exact tsub_le_iff_right.2 h2
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) h3
        rw [hdst]; nlinarith [t.2.2]
      rw [internal_eq_of_le D hD hV (hmem s) (hmem t) hle', hdst, hJuv,
        abs_of_nonneg (sub_nonneg.2 hst), ENNReal.ofReal_mul (sub_nonneg.2 hst)]
    refine ⟨h0, h1, hmem, fun s t => ?_⟩
    rcases le_total (s : ℝ) t with hst | hts
    · exact key s t hst
    · rw [ContMetric.internal, internalEDist_comm, ← ContMetric.internal, key t s hts,
        abs_sub_comm]
  · rintro ⟨h0, h1, hmem, hJ⟩
    have hle1 : ∀ s t : unitInterval, D.1 (η s, η t) ≤ |(t : ℝ) - s| * L := fun s t => by
      have h := (show ENNReal.ofReal (D.1 (η s, η t)) ≤ D.internal V (η s) (η t) by
        rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _)
      rw [hJ, hJuv, ← ENNReal.ofReal_mul (abs_nonneg _)] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    have key : ∀ s t : unitInterval, (s : ℝ) ≤ t → D.1 (η s, η t) = ((t : ℝ) - s) * L := by
      intro s t hst
      have a1 := hle1 0 s
      have a2 := hle1 s t
      have a3 := hle1 t 1
      rw [h0, Set.Icc.coe_zero, sub_zero, abs_of_nonneg s.2.1] at a1
      rw [abs_of_nonneg (sub_nonneg.2 hst)] at a2
      rw [h1, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.2 t.2.2)] at a3
      have tri1 := D.2.triangle u (η s) v
      have tri2 := D.2.triangle (η s) (η t) v
      have : L ≤ s * L + ((t : ℝ) - s) * L + (1 - t) * L := by linarith
      nlinarith
    refine ⟨h0, h1, fun s t => ?_⟩
    rcases le_total (s : ℝ) t with hst | hts
    · rw [key s t hst, abs_of_nonneg (sub_nonneg.2 hst)]
    · rw [D.2.symm, key t s hts, abs_of_nonpos (sub_nonpos.2 hts)]
      ring

/-! ## Midpoint sets and condition 1 through the internal metrics -/

/-- `x ∈ M_t` for the internal metric `J` of `V` -/
def midPtI (J : ℂ → ℂ → ℝ≥0∞) (V : Set ℂ) (u v : ℂ) (t : ℝ) (x : ℂ) : Prop :=
  x ∈ V ∧ J u x = ENNReal.ofReal t * J u v ∧ J x v = ENNReal.ofReal (1 - t) * J u v

/-- `MidUnique` for the internal metric `J` of `V` -/
def MidUniqueI (J : ℂ → ℂ → ℝ≥0∞) (V : Set ℂ) (u v : ℂ) : Prop :=
  ∀ q : ℚ, ∀ x y : ℂ, midPtI J V u v (pj q) x → midPtI J V u v (pj q) y → x = y

lemma midPt_iff_midPtI (D : ContMetric) (hD : D.IsLength) [ProperSpace D.Space]
    {V : Set ℂ} (hV : IsOpen V) {u v : ℂ} (hu : u ∈ V) (hv : v ∈ V)
    (hle : ENNReal.ofReal (D.1 (u, v)) ≤ setDist D {u} (frontier V)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : ℂ) : midPt D u v t x ↔ midPtI (D.internal V) V u v t x := by
  set L := D.1 (u, v) with hL
  have hL0 : 0 ≤ L := D.nonneg u v
  have hJuv : D.internal V u v = ENNReal.ofReal L := internal_eq_of_le D hD hV hu hv hle
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x ∈ V := by
      by_cases ht1 : t = 1
      · have : D.1 (x, v) = 0 := by rw [h2, ht1, sub_self, zero_mul]
        rw [show x = v from (dist_eq_zero (x := D.pt x) (y := D.pt v)).1 this]; exact hv
      rcases hL0.eq_or_lt with hL0' | hLpos
      · have hz : D.1 (u, v) = 0 := hL0'.symm
        have : D.1 (u, x) = 0 := by rw [h1, hz, mul_zero]
        rw [← show u = x from (dist_eq_zero (x := D.pt u) (y := D.pt x)).1 this]; exact hu
      · have hlt : ENNReal.ofReal (D.1 (u, x)) < setDist D {u} (frontier V) := by
          rw [h1]
          refine lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff hLpos |>.2 ?_) hle
          have : t < 1 := lt_of_le_of_ne ht.2 ht1
          nlinarith
        rw [setDist_singleton_eq, ← ContMetric.edist_pt] at hlt
        exact (ContMetric.internal_eq_of_lt_infEDist_frontier hD hV hu hlt).1
    have hux : ENNReal.ofReal (D.1 (u, x)) ≤ setDist D {u} (frontier V) :=
      le_trans (ENNReal.ofReal_le_ofReal (by rw [h1]; nlinarith [ht.2])) hle
    have hxv : ENNReal.ofReal (D.1 (x, v)) ≤ setDist D {x} (frontier V) := by
      have h3 := hle.trans (setDist_le_add D u x (frontier V))
      rw [h1] at h3
      have h4 : ENNReal.ofReal (L - t * L) ≤ setDist D {x} (frontier V) := by
        rw [ENNReal.ofReal_sub _ (by nlinarith [ht.1])]
        exact tsub_le_iff_right.2 h3
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) h4
      rw [h2]; linarith
    refine ⟨hx, ?_, ?_⟩
    · rw [internal_eq_of_le D hD hV hu hx hux, h1, hJuv, ENNReal.ofReal_mul ht.1]
    · rw [internal_eq_of_le D hD hV hx hv hxv, h2, hJuv,
        ENNReal.ofReal_mul (by linarith [ht.2])]
  · rintro ⟨hx, h1, h2⟩
    rw [hJuv, ← ENNReal.ofReal_mul ht.1] at h1
    rw [hJuv, ← ENNReal.ofReal_mul (by linarith [ht.2])] at h2
    have a1 : D.1 (u, x) ≤ t * L := by
      refine (ENNReal.ofReal_le_ofReal_iff (by nlinarith [ht.1])).1 ?_
      rw [← h1, ← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
    have a2 : D.1 (x, v) ≤ (1 - t) * L := by
      refine (ENNReal.ofReal_le_ofReal_iff (by nlinarith [ht.2])).1 ?_
      rw [← h2, ← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
    have tri := D.2.triangle u x v
    exact ⟨by linarith, by linarith⟩

lemma midUnique_iff_midUniqueI (D : ContMetric) (hD : D.IsLength) [ProperSpace D.Space]
    {V : Set ℂ} (hV : IsOpen V) {u v : ℂ} (hu : u ∈ V) (hv : v ∈ V)
    (hle : ENNReal.ofReal (D.1 (u, v)) ≤ setDist D {u} (frontier V)) :
    MidUnique D u v ↔ MidUniqueI (D.internal V) V u v := by
  refine forall_congr' fun q => forall₂_congr fun x y => ?_
  have ht : ((pj q : unitInterval) : ℝ) ∈ Icc (0 : ℝ) 1 := (pj q).2
  rw [midPt_iff_midPtI D hD hV hu hv hle ht, midPt_iff_midPtI D hD hV hu hv hle ht]

/-- condition 1 of `𝖤_r(z)` (Borel form `gaCompareB`) through the internal metrics `J`, `J'` of
`U = 𝔸_{r/2,2r}(z)` -/
def gaCompareBI (J J' : ℂ → ℂ → ℝ≥0∞) (α C' r : ℝ) (z : ℂ) : Prop :=
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, ∀ η : C(unitInterval, ℂ),
    MidUniqueI J (annulus z (r / 2) (2 * r)) u v →
    IsGeodI J (annulus z (r / 2) (2 * r)) u v η →
    (∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) → (J' u v).toReal ≤ C' * (J u v).toReal

/-- **GM l. 1354–1358**: on condition 2, condition 1 (Borel form) is determined by the internal
metrics of `𝔸_{r/2,2r}(z)`, for proper length metrics `D_h`, `D̃_h`. -/
theorem mem_gaCompareB_iff_internal {D D' : DistC → ContMetric} {α C' r : ℝ} {z : ℂ}
    {g : DistC} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) (hL : (D g).IsLength)
    (hL' : (D' g).IsLength) [ProperSpace (D g).Space] [ProperSpace (D' g).Space]
    (hlong : g ∈ gaLong D D' α r z) :
    g ∈ gaCompareB D D' α C' r z ↔ gaCompareBI ((D g).internal (annulus z (r / 2) (2 * r)))
      ((D' g).internal (annulus z (r / 2) (2 * r))) α C' r z := by
  set U : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ) with hUdef
  have hUo : IsOpen U := (annulus z (r / 2) (2 * r)).isOpen
  simp only [gaCompareB, gaCompareBI, mem_ofPred_eq]
  refine forall₂_congr fun u hu => forall₂_congr fun v hv => forall_congr' fun η => ?_
  have huU : u ∈ U := closedAnnulus_subset hα hr (mem_sphere_iff_norm.1 hu).ge
    ((mem_sphere_iff_norm.1 hu).le.trans (by nlinarith))
  have hvU : v ∈ U := closedAnnulus_subset hα hr
    ((mem_sphere_iff_norm.1 hv).ge.trans' (by nlinarith)) (mem_sphere_iff_norm.1 hv).le
  -- a geodesic (for `D` or for `J`) in `cl 𝔸_{αr,r}(z)` forces the hypothesis of condition 2 to fail
  have hyp2 : ((D g).IsGeod01 u v η ∨ IsGeodI ((D g).internal U) U u v η) →
      (∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) →
      ENNReal.ofReal ((D g).1 (u, v)) ≤ setDist (D g) {u} (frontier U) ∧
        ENNReal.ofReal ((D' g).1 (u, v)) ≤ setDist (D' g) {u} (frontier U) := by
    intro hgeo hK
    by_contra hc
    rw [not_and_or, not_le, not_le] at hc
    have hP : ContinuousOn (fun t => η (pj t)) (Icc 0 1) :=
      (η.continuous.comp continuous_projIcc).continuousOn
    have h0 : η (pj 0) = u := by
      rcases hgeo with hg | hg <;>
      · rw [show pj 0 = 0 from Set.projIcc_left zero_le_one]; exact hg.1
    have h1 : η (pj 1) = v := by
      rcases hgeo with hg | hg <;>
      · rw [show pj 1 = 1 from Set.projIcc_right zero_le_one]; exact hg.2.1
    have hlt := hlong u hu v hv hc 0 1 (fun t => η (pj t)) zero_le_one hP h0 h1
      (by rintro _ ⟨t, -, rfl⟩; exact hK _)
    have hmaps : MapsTo (fun t => η (pj t)) (Icc 0 1) U := fun t _ =>
      closure_annulus_subset hα hr (hK _)
    rcases hgeo with hg | hg
    · have hlen : (D g).len (fun t => η (pj t)) 0 1 ≤ ENNReal.ofReal ((D g).1 (u, v)) := by
        rw [len_eq_lenFun]
        refine lenFun_pj_le fun s t => ?_
        rw [hg.2.2 s t, ENNReal.ofReal_mul (abs_nonneg _)]
      have : ENNReal.ofReal ((D g).1 (u, v)) ≤ (D g).internal U u v := by
        rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
      exact absurd (hlt.trans_le hlen) (not_lt.2 this)
    · have hlen : (D g).len (fun t => η (pj t)) 0 1 ≤ (D g).internal U u v := by
        rw [← lenFun_internal (D g) hP hmaps]
        exact lenFun_pj_le hg.2.2.2
      exact absurd (hlt.trans_le hlen) (lt_irrefl _)
  constructor
  · intro H hm hgI hK
    obtain ⟨h2, h2'⟩ := hyp2 (Or.inr hgI) hK
    have := H ((midUnique_iff_midUniqueI (D g) hL hUo huU hvU h2).2 hm)
      ((isGeod01_iff_isGeodI (D g) hL hUo huU hvU h2 η).2 hgI) hK
    rwa [internal_eq_of_le (D g) hL hUo huU hvU h2, internal_eq_of_le (D' g) hL' hUo huU hvU h2',
      ENNReal.toReal_ofReal ((D g).nonneg u v), ENNReal.toReal_ofReal ((D' g).nonneg u v)]
  · intro H hm hg hK
    obtain ⟨h2, h2'⟩ := hyp2 (Or.inl hg) hK
    have := H ((midUnique_iff_midUniqueI (D g) hL hUo huU hvU h2).1 hm)
      ((isGeod01_iff_isGeodI (D g) hL hUo huU hvU h2 η).1 hg) hK
    rwa [internal_eq_of_le (D g) hL hUo huU hvU h2, internal_eq_of_le (D' g) hL' hUo huU hvU h2',
      ENNReal.toReal_ofReal ((D g).nonneg u v), ENNReal.toReal_ofReal ((D' g).nonneg u v)] at this

/-! ## `𝖤_r(z)` through the internal metrics, and the remaining measurability node -/

/-- `𝖤_r(z)` through the internal metrics `J`, `J'` of `𝔸_{r/2,2r}(z)` -/
def goodAnnulusI (J J' : ℂ → ℂ → ℝ≥0∞) (α A C' r : ℝ) (z : ℂ) : Prop :=
  gaCompareBI J J' α C' r z ∧ gaLongI J J' α r z ∧ gaAroundI J α A r z

/-- **GM l. 1348–1359** (deterministic part of Lemma 3.7): for proper length metrics `D_h`, `D̃_h`
with `D_h`-geodesics between all pairs of points, `𝖤_r(z)` is determined by the internal metrics
of `𝔸_{r/2,2r}(z)`. -/
theorem mem_goodAnnulus_iff_internal {D D' : DistC → ContMetric} {α A C' r : ℝ} {z : ℂ}
    {g : DistC} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) (hL : (D g).IsLength)
    (hL' : (D' g).IsLength) [ProperSpace (D g).Space] [ProperSpace (D' g).Space]
    (hex : ∀ a b : ℂ, ∃ η, (D g).IsGeod01 a b η) :
    g ∈ goodAnnulus D D' α A C' r z ↔ goodAnnulusI ((D g).internal (annulus z (r / 2) (2 * r)))
      ((D' g).internal (annulus z (r / 2) (2 * r))) α A C' r z := by
  have eL := mem_gaLong_iff_internal (D := D) (D' := D') (z := z) (g := g) hα hα1 hr hL hL'
  have eA := mem_gaAround_iff_internal (D := D) (A := A) (z := z) (g := g) hα hα1 hr hL
  simp only [goodAnnulus, mem_inter_iff, goodAnnulusI, mem_gaCompare_iff hex]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(mem_gaCompareB_iff_internal hα hα1 hr hL hL' h2).1 h1, eL.1 h2, eA.1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h2' := eL.2 h2
    exact ⟨⟨(mem_gaCompareB_iff_internal hα hα1 hr hL hL' h2').2 h1, h2'⟩, eA.2 h3⟩

/-- the measurability part of GM Lemma 3.7 (l. 1348–1360, "determined by `h|_{𝔸_{r/2,2r}(z)}`"):
the event `goodAnnulusI` of the internal metrics of `𝔸_{r/2,2r}(z)` is a.s. an event of
`σ(h|_{𝔸_{r/2,2r}(z)})` (open; see `handoff/P2-M2E2.md`). -/
def L3_7meas : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∀ {α : ℝ}, 1 / 2 < α → α < 1 → ∀ A C' : ℝ, ∀ (z : ℂ) (r : ℝ), 0 < r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma h (annulus z (r / 2) (2 * r)))
      {ω | goodAnnulusI ((D (h ω)).internal (annulus z (r / 2) (2 * r)))
        ((D' (h ω)).internal (annulus z (r / 2) (2 * r))) α A C' r z}

/-- GM's reduced Lemma 3.7 from its measurability part and GM.S1.1 (`DFGPSLem3_8`: boundedly
compact, hence proper, with geodesics). -/
theorem gm_L3_7loc_of_meas (h38 : DFGPSLem3_8) (H : L3_7meas) : L3_7loc := by
  intro γ D D' c hPS α hα hα1 A C' z r hr Ω _ P _ h hh
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  obtain ⟨F, hF, hFae⟩ := H hPS hα hα1 A C' z r hr P h hh
  refine ⟨F, hF, EventuallyEq.trans ?_ hFae⟩
  filter_upwards [gm_S1_1_bcpt h38 hγ0 hγ2 hD P h hh, gm_S1_1_bcpt h38 hγ0 hγ2 hD' P h hh,
    hD.length P h (Tight.isGFFPlusCont_of_wp hh),
    hD'.length P h (Tight.isGFFPlusCont_of_wp hh)] with ω hb hb' hl hl'
  have := properSpace_of_bcpt _ hb
  have := properSpace_of_bcpt _ hb'
  exact propext (mem_goodAnnulus_iff_internal hα hα1 hr hl hl'
    (fun a b => exists_isGeod01_of_bcpt _ hl hb a b))

/-- **GM Lemma 3.7** from its measurability part `L3_7meas` and `DFGPSLem3_8`. -/
theorem gm_L3_7_of_meas (h38 : DFGPSLem3_8) (H : L3_7meas) : L3_7 :=
  gm_L3_7_of_loc (gm_L3_7loc_of_meas h38 H)

end LQGMetric.GM
