/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.LGDScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic

/-!
# The Liouville graph distance: monotonicity in `μ`, scaling, free centres, similarity
invariance (task P2-GMC, WP-24)

Deterministic facts about DZZ's `lgdDZZ μ δ u v` (Statement/Dimension.lean; DZZ arXiv:1807.00422
`LBM_LGDarXiv.tex` l. 121–124) used implicitly in DZZ §§2–3 and DG Lemma 2.2 (DG applies DZZ in a
rotated, rescaled square; decision D24 / OD-14):

* `lgdDZZ_mono_measure` : `μ ≤ ν ⇒ D_δ(μ) ≤ D_δ(ν)` (comparison of fields, DZZ L3.8–3.10,
  DG L3.2);
* `lgdDZZ_smul` : `D_δ(c μ) = D_{δ/√c}(μ)` (a constant shift `h + a` multiplies the measure by
  `e^{γa}`, QZ `FinArea.ae_qAreaMeasure_add_ofFun`);
* `lgdDZZ_eq_lgdFree` : rational centres are no restriction — `lgdDZZ = lgdFree`, the same
  infimum over balls with arbitrary centres (compactness of the path: a uniform margin `η`, then
  shrink each ball by `η/2` and move its centre to a rational point);
* `lgdDZZ_map_similarity` : for `φ z = a z + b`, `a ≠ 0`,
  `D_δ(φ_* μ)(φ u, φ v) = D_δ(μ)(u, v)` (balls go to balls).

With DS Prop 2.1 (`φ_* μ_h = μ_{h∘φ⁻¹ + Q log|(φ⁻¹)'|}`, still open here) this gives the
LGD of the field on a rotated/rescaled square. All proofs are own elementary arguments (the
papers use these facts without comment).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

/-- more mass, more balls -/
theorem lgdDZZ_mono_measure {μ ν : Measure ℂ} (h : μ ≤ ν) (δ : ℝ) (u v : ℂ) :
    lgdDZZ μ δ u v ≤ lgdDZZ ν δ u v := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  exact iInf₂_le N ⟨c, ρ, P, fun i => ⟨(h1 i).1, (Measure.le_iff'.mp h _).trans (h1 i).2⟩, h2⟩

lemma smul_mass_le_iff {c δ : ℝ} (hc : 0 < c) (m : ℝ≥0∞) :
    ENNReal.ofReal c * m ≤ ENNReal.ofReal (δ ^ 2) ↔
      m ≤ ENNReal.ofReal ((δ / Real.sqrt c) ^ 2) := by
  rw [div_pow, Real.sq_sqrt hc.le, ENNReal.ofReal_div_of_pos hc,
    ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hc).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]

/-- the Liouville graph distance with arbitrary (not necessarily rational) centres -/
def lgdFree (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ∃ (x : Fin N → ℂ) (ρ : Fin N → ℝ) (P : Path u v),
      (∀ i, 0 < ρ i ∧ μ (Metric.ball (x i) (ρ i)) ≤ ENNReal.ofReal (δ ^ 2)) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)), (N : ℕ∞)

lemma lgdFree_le_lgdDZZ (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) : lgdFree μ δ u v ≤ lgdDZZ μ δ u v := by
  unfold lgdDZZ lgdFree
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  exact iInf₂_le N ⟨fun i => ratPt (c i), ρ, P, h1, h2⟩

/-- a finite cover of a path by open balls has a uniform margin `η` -/
lemma exists_margin {u v : ℂ} {N : ℕ} (x : Fin N → ℂ) (ρ : Fin N → ℝ) (P : Path u v)
    (h : ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)) :
    ∃ η : ℝ, 0 < η ∧ ∀ t, ∃ i, dist (P t) (x i) < ρ i - η := by
  set V : ℕ → Set unitInterval := fun n => ⋃ i, {t | dist (P t) (x i) < ρ i - 1 / (n + 1)}
  have hVo : ∀ n, IsOpen (V n) := fun n => isOpen_iUnion fun i =>
    isOpen_lt ((P.continuous.dist continuous_const)) continuous_const
  have hmono : Monotone V := by
    intro m n hmn t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    refine mem_iUnion.mpr ⟨i, ?_⟩
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
    simp only [mem_ofPred_eq] at hi ⊢; linarith
  have hcov : (univ : Set unitInterval) ⊆ ⋃ n, V n := by
    intro t _
    obtain ⟨i, hi⟩ := h t
    rw [Metric.mem_ball] at hi
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (ρ i - dist (P t) (x i)))
    have hpos : 0 < ρ i - dist (P t) (x i) := by linarith
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨i, ?_⟩⟩
    simp only [mem_ofPred_eq]
    have : 1 / ((n : ℝ) + 1) < ρ i - dist (P t) (x i) := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hn; nlinarith
    linarith
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover V hVo hcov hmono.directed_le
  refine ⟨1 / (n + 1), by positivity, fun t => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hn (mem_univ t))
  exact ⟨i, hi⟩

/-- **rational centres are no restriction** -/
theorem lgdDZZ_eq_lgdFree (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) : lgdDZZ μ δ u v = lgdFree μ δ u v := by
  refine le_antisymm ?_ (lgdFree_le_lgdDZZ μ δ u v)
  unfold lgdDZZ lgdFree
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  obtain ⟨η, hη, hmar⟩ := exists_margin x ρ P h2
  set θ : Fin N → ℝ := fun i => min (η / 2) (ρ i / 2) with hθ
  have hθpos : ∀ i, 0 < θ i := fun i => lt_min (by positivity) (by linarith [(h1 i).1])
  choose c hc using fun i => exists_ratPt_dist_lt (x i) (hθpos i)
  refine iInf₂_le N ⟨c, fun i => ρ i - θ i, P, fun i => ⟨?_, ?_⟩, fun t => ?_⟩
  · linarith [min_le_right (η / 2) (ρ i / 2), (h1 i).1]
  · refine (measure_mono fun z hz => ?_).trans (h1 i).2
    rw [Metric.mem_ball] at hz ⊢
    linarith [dist_triangle z (ratPt (c i)) (x i), hc i]
  · obtain ⟨i, hi⟩ := hmar t
    refine ⟨i, ?_⟩
    rw [Metric.mem_ball]
    have := dist_triangle (P t) (x i) (ratPt (c i))
    rw [dist_comm (x i)] at this
    linarith [hc i, min_le_left (η / 2) (ρ i / 2)]

/-- the similarity `z ↦ a z + b` -/
def simMap (a b : ℂ) (z : ℂ) : ℂ := a * z + b

lemma continuous_simMap (a b : ℂ) : Continuous (simMap a b) := by unfold simMap; fun_prop

lemma simMap_preimage_ball {a : ℂ} (ha : a ≠ 0) (b x : ℂ) (ρ : ℝ) :
    simMap a b ⁻¹' Metric.ball (simMap a b x) (‖a‖ * ρ) = Metric.ball x ρ := by
  ext z
  simp only [mem_preimage, Metric.mem_ball, Complex.dist_eq, simMap, add_sub_add_right_eq_sub,
    ← mul_sub, norm_mul]
  exact mul_lt_mul_iff_right₀ (norm_pos_iff.mpr ha)

lemma lgdFree_map_le {a : ℂ} (ha : a ≠ 0) (b : ℂ) (μ : Measure ℂ) (δ : ℝ) {u v u' v' : ℂ}
    (hu : simMap a b u = u') (hv : simMap a b v = v') :
    lgdFree (μ.map (simMap a b)) δ u' v' ≤ lgdFree μ δ u v := by
  subst hu hv
  unfold lgdFree
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine iInf₂_le N ⟨fun i => simMap a b (x i), fun i => ‖a‖ * ρ i,
    P.map (continuous_simMap a b), fun i => ⟨mul_pos hna (h1 i).1, ?_⟩, fun t => ?_⟩
  · rw [Measure.map_apply (continuous_simMap a b).measurable measurableSet_ball,
      simMap_preimage_ball ha]
    exact (h1 i).2
  · obtain ⟨i, hi⟩ := h2 t
    refine ⟨i, ?_⟩
    rw [Path.map_coe, Function.comp_apply, ← mem_preimage, simMap_preimage_ball ha]
    exact hi

/-- **similarity invariance of the Liouville graph distance** -/
theorem lgdDZZ_map_similarity {a : ℂ} (ha : a ≠ 0) (b : ℂ) (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) :
    lgdDZZ (μ.map (simMap a b)) δ (simMap a b u) (simMap a b v) = lgdDZZ μ δ u v := by
  rw [lgdDZZ_eq_lgdFree, lgdDZZ_eq_lgdFree]
  refine le_antisymm (lgdFree_map_le ha b μ δ rfl rfl) ?_
  have hinv : ∀ z, simMap a⁻¹ (-(a⁻¹ * b)) (simMap a b z) = z := fun z => by
    simp only [simMap]; field_simp; ring
  have hcomp : (μ.map (simMap a b)).map (simMap a⁻¹ (-(a⁻¹ * b))) = μ := by
    rw [Measure.map_map (continuous_simMap _ _).measurable (continuous_simMap _ _).measurable]
    conv_rhs => rw [← Measure.map_id (μ := μ)]
    congr 1; funext z; exact hinv z
  have := lgdFree_map_le (inv_ne_zero ha) (-(a⁻¹ * b)) (μ.map (simMap a b)) δ (hinv u) (hinv v)
  rwa [hcomp] at this

end LQGMetric
