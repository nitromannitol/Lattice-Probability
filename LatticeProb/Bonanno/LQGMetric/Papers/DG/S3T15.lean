/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3T15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Poly
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperScale
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Theorem 1.5 and the second half of (1.5b) from DG Propositions 3.15 and 3.18

Source: Ding–Gwynne arXiv:1807.01072, `literature/src/1807.01072/metric-comparison-final.tex`
(`DG:`). Proof of Theorem 1.5, DG:1782–1785: "The lower bound for the point-to-point distance in
(1.5a) follows from Proposition 3.15 applied with `K = {z}` and `U` an open set containing `z` but
not `w`. The upper bound follows from Proposition 3.18 applied with `K` chosen so that
`z, w ∈ K`. The bounds for other LFPP distances in (1.5b) are immediate from Propositions 3.15
and 3.18 together with (1.5a)."

* `DGProp3_15` — DG Proposition 3.15 (`prop-lfpp-lower`, DG:1411–1416), whole-plane GFF,
  stated for the circle-average process `hc` as `DG.DGThm1_5` / `Blueprint.DGProp3_21` are
  (P3.18 in the final tex is `Blueprint.DGProp3_21`, see blueprint/DG3-STATUS.md).
* `dgThm1_5_of : DGProp3_15 → Blueprint.DGProp3_21 → DGThm1_5`,
  `dgThm1_5KU_of : DGProp3_15 → Blueprint.DGProp3_21 → Blueprint.DGThm1_5KU`.

Readings: for (1.5a) lower we take `U = B(z, |w − z|)`, so `w ∈ ∂U` and `D(z,w) ≥ D({z}, ∂U)`
directly (DG: any `U ∋ z` with `w ∉ U`; the special case avoids cutting the path). The lower
half of (1.5b) uses (1.5a) at two distinct points of `K` and a polygonal path in the connected
open set `U` (own elementary argument: DG's "immediate"). The upper half of `DGThm1_5KU`
(`D(K, ∂U) ≤ D(z, w)` for `z ∈ K`, `w ∈ ∂U`) uses (1.5a) upper.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

/-- **DG Proposition 3.15** (`prop-lfpp-lower`, DG:1411–1416): "Let `h` be a whole-plane GFF
normalized so that `h_1(0) = 0`. Also let `U ⊂ ℂ` be a bounded open set and let `K ⊂ U` be a
compact set. For each `ζ ∈ (0,1)`, it holds with polynomially high probability as `δ → 0` that
the LFPP distance with exponent `ξ = γ/d_γ` satisfies `D^δ_{h,LFPP}(K, ∂U) ≥ δ^{λ + ζ}`."
(field model and "polynomially high probability" as in `Blueprint.DGProp3_21`; the constants may
depend on the probability space.) -/
def DGProp3_15 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage hc P →
      ∀ U K : Set ℂ, IsOpen U → Bornology.IsBounded U → IsCompact K → K ⊆ U →
        ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
          P {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
            dgSetDist (xiGamma γ) (fun x => hc δ x ω) K U} ≤ ENNReal.ofReal (C * δ ^ p)

/-! ## Deterministic facts on `dgLFPP` -/

lemma t15_dgLFPP_nonneg (ξ : ℝ) (φ : ℂ → ℝ) (S : Set ℂ) (z w : ℂ) : 0 ≤ dgLFPP ξ φ S z w :=
  Real.iInf_nonneg fun p => lfppLength_nonneg ξ φ p.1

/-- paths in a larger set give a smaller distance (if `S` has a path at all) -/
lemma t15_dgLFPP_mono {ξ : ℝ} {φ : ℂ → ℝ} {S S' : Set ℂ} (hSS : S ⊆ S') {z w : ℂ}
    (hne : ∃ q, IsDGPath S z w q) : dgLFPP ξ φ S' z w ≤ dgLFPP ξ φ S z w := by
  obtain ⟨q, hq⟩ := hne
  have : Nonempty {p : ℝ → ℂ // IsDGPath S z w p} := ⟨⟨q, hq⟩⟩
  exact le_ciInf fun p => ciInf_le (bddBelow_dg ξ φ S' z w)
    ⟨p.1, ⟨p.2.source, p.2.target, p.2.mapsTo.mono_right hSS, p.2.continuousOn,
      p.2.piecewise_contDiff⟩⟩

/-- `z, w` joined by a polygon whose edges lie in `U` -/
def T15PolyJoin (U : Set ℂ) (z y : ℂ) : Prop :=
  ∃ (m : ℕ) (V : ℕ → ℂ), 0 < m ∧ V 0 = z ∧ V m = y ∧ ∀ i < m, segment ℝ (V i) (V (i + 1)) ⊆ U

lemma t15_polyJoin_mem {U : Set ℂ} {z y : ℂ} (h : T15PolyJoin U z y) : y ∈ U := by
  obtain ⟨m, V, hm, -, hy, hs⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact hy ▸ hs k (by omega) (right_mem_segment ℝ _ _)

lemma t15_polyJoin_refl {U : Set ℂ} {z : ℂ} (hz : z ∈ U) : T15PolyJoin U z z :=
  ⟨1, fun _ => z, one_pos, rfl, rfl, fun i _ => by simpa using hz⟩

lemma t15_polyJoin_snoc {U : Set ℂ} {z y y' : ℂ} (h : T15PolyJoin U z y)
    (hs : segment ℝ y y' ⊆ U) : T15PolyJoin U z y' := by
  obtain ⟨m, V, hm, h0, hy, hV⟩ := h
  refine ⟨m + 1, fun i => if i ≤ m then V i else y', by omega, by simp [h0], by simp, ?_⟩
  intro i hi
  rcases Nat.lt_or_ge i m with h | h
  · simp only [show i ≤ m by omega, show i + 1 ≤ m by omega, ite_true]
    exact hV i h
  · have : i = m := by omega
    subst this
    simpa [hy] using hs

/-- a polygon in `U` is a DG path in `U` -/
lemma t15_isDGPath_of_polyJoin {U : Set ℂ} {z y : ℂ} (h : T15PolyJoin U z y) :
    ∃ q, IsDGPath U z y q := by
  obtain ⟨m, V, hm, h0, hy, hV⟩ := h
  have hP := DFGPS.L36.isDGPath_polyPath V m hm
  rw [h0, hy] at hP
  refine ⟨_, ⟨hP.source, hP.target, fun t ht => ?_, hP.continuousOn, hP.piecewise_contDiff⟩⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set i := ⌊t * (m : ℝ)⌋₊ with hi
  have htm0 : 0 ≤ t * m := mul_nonneg ht.1 hm'.le
  have h1 : (i : ℝ) ≤ t * m := Nat.floor_le htm0
  have h2 : t * m < i + 1 := Nat.lt_floor_add_one _
  have h3 : t * m ≤ m := by nlinarith [ht.2]
  show LQGDimension.PolygonRiemannAux.edgeAff V m i t ∈ U
  unfold LQGDimension.PolygonRiemannAux.edgeAff
  rcases Nat.lt_or_ge i m with hlt | hge
  · refine hV i hlt ?_
    rw [segment_eq_image']
    exact ⟨t * m - i, ⟨by linarith, by linarith⟩, rfl⟩
  · have him : (i : ℝ) = m := le_antisymm (h1.trans h3) (by exact_mod_cast hge)
    have : t * (m : ℝ) - i = 0 := by linarith
    have hie : i = m := by exact_mod_cast him
    rw [this, zero_smul, add_zero, hie, hy]
    exact t15_polyJoin_mem ⟨m, V, hm, h0, hy, hV⟩

/-- **polygonal paths in a connected open set** (own elementary argument) -/
lemma t15_exists_isDGPath {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {z w : ℂ}
    (hz : z ∈ U) (hw : w ∈ U) : ∃ q, IsDGPath U z w q := by
  refine t15_isDGPath_of_polyJoin ?_
  have hA : IsOpen {y | T15PolyJoin U z y} := by
    refine isOpen_iff.2 fun y hy => ?_
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU y (t15_polyJoin_mem hy)
    exact ⟨r, hr, fun y' hy' => t15_polyJoin_snoc hy
      (((convex_ball y r).segment_subset (mem_ball_self hr) hy').trans hrU)⟩
  have hB : IsOpen {y | y ∈ U ∧ ¬ T15PolyJoin U z y} := by
    refine isOpen_iff.2 fun y hy => ?_
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU y hy.1
    refine ⟨r, hr, fun y' hy' => ⟨hrU hy', fun h => hy.2 (t15_polyJoin_snoc h
      (((convex_ball y r).segment_subset hy' (mem_ball_self hr)).trans hrU))⟩⟩
  have hsub : U ⊆ {y | T15PolyJoin U z y} :=
    hUc.isPreconnected.subset_left_of_subset_union hA hB
      (Set.disjoint_left.2 fun y h1 h2 => h2.2 h1)
      (fun y hy => by by_cases h : T15PolyJoin U z y; exacts [Or.inl h, Or.inr ⟨hy, h⟩])
      ⟨z, hz, t15_polyJoin_refl hz⟩
  exact hsub hw

/-! ## Probability glue -/

variable {Ω : Type} [MeasurableSpace Ω]

lemma t15_tendsto_of_poly {P : Measure Ω} {E : ℝ → Set Ω} {p C δ₀ : ℝ} (hp : 0 < p)
    (hδ₀ : 0 < δ₀) (h : ∀ δ ∈ Ioo (0 : ℝ) δ₀, P (E δ) ≤ ENNReal.ofReal (C * δ ^ p)) :
    Tendsto (fun δ => P (E δ)) (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun δ : ℝ => ENNReal.ofReal (C * δ ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ ^ p) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => δ ^ p) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ p)) :=
        (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds
      rwa [Real.zero_rpow hp.ne'] at this
    have h2 := ENNReal.tendsto_ofReal (h1.const_mul C)
    rwa [mul_zero, ENNReal.ofReal_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ using h δ hδ

lemma t15_tendsto_mono {P : Measure Ω} {E F : ℝ → Set Ω} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hEF : ∀ δ ∈ Ioo (0 : ℝ) δ₀, E δ ⊆ F δ) (hF : Tendsto (fun δ => P (F δ)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ => P (E δ)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ using measure_mono (hEF δ hδ)

lemma t15_tendsto_union {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : Tendsto (fun δ => P (E δ)) (𝓝[>] 0) (𝓝 0))
    (hF : Tendsto (fun δ => P (F δ)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ => P (E δ ∪ F δ)) (𝓝[>] 0) (𝓝 0) := by
  have h := hE.add hF
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun _ => measure_union_le _ _)

lemma t15_rpow_mono {δ a b : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) : δ ^ b ≤ δ ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le hab

/-! ## Point-to-point bounds -/

/-- (1.5a), upper half, from DG Prop 3.18 (`Blueprint.DGProp3_21`) with `K = {z, w}` -/
theorem t15_tendsto_upper (h321 : Blueprint.DGProp3_21) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ} (hG : LQGDimension.IsGFFCircleAverage hc P)
    (z w : ℂ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun δ : ℝ => P {ω | ¬ dgLFPP (xiGamma γ) (fun x => hc δ x ω) univ z w ≤
      δ ^ (dgLambda γ - η)}) (𝓝[>] 0) (𝓝 0) := by
  set R := ‖z - w‖ + 1
  have hR : 0 < R := by positivity
  have hzU : z ∈ ball w R := by rw [mem_ball, dist_eq_norm]; linarith
  have hK : ({z, w} : Set ℂ) ⊆ ball w R := by
    rintro x (rfl | rfl)
    · exact hzU
    · exact mem_ball_self hR
  set ζ := min η (1 / 2)
  have hζ : ζ ∈ Ioo (0 : ℝ) 1 := ⟨lt_min hη (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨p, C, δ₀, hp, hδ₀, hb⟩ := h321 γ hγ hγ2 (ball w R) {z, w} isOpen_ball
    ((convex_ball w R).isConnected (nonempty_ball.2 hR))
    (Set.toFinite ({z, w} : Set ℂ)).isCompact hK ζ hζ
  have hpath : ∃ q, IsDGPath (closure (ball w R)) z w q := by
    rw [closure_ball w hR.ne']
    exact ⟨_, DFGPS.L36.isDGPath_segment_ball (by linarith : ‖z - w‖ ≤ R)⟩
  refine t15_tendsto_mono (lt_min hδ₀ one_pos) (fun δ hδ ω hω => ?_)
    (t15_tendsto_of_poly hp hδ₀ (hb P hc hG))
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  intro hgood
  apply hω
  have h1 : ENNReal.ofReal (dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure (ball w R)) z w) ≤
      ENNReal.ofReal (δ ^ (dgLambda γ - ζ)) :=
    (le_iSup₂_of_le (f := fun a (_ : a ∈ ({z, w} : Set ℂ)) => ⨆ b ∈ ({z, w} : Set ℂ),
      ENNReal.ofReal (dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure (ball w R)) a b)) z
      (Or.inl rfl) (le_iSup₂_of_le (f := fun b (_ : b ∈ ({z, w} : Set ℂ)) =>
        ENNReal.ofReal (dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure (ball w R)) z b)) w
        (Or.inr rfl) le_rfl)).trans hgood
  rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hδ.1.le _)] at h1
  exact ((t15_dgLFPP_mono (subset_univ _) hpath).trans h1).trans
    (t15_rpow_mono hδ1 (by linarith [min_le_left η (1 / 2)]))

/-- (1.5a), lower half, from DG Prop 3.15 with `K = {z}`, `U = B(z, |w − z|)` -/
theorem t15_tendsto_lower (h315 : DGProp3_15) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ} (hG : LQGDimension.IsGFFCircleAverage hc P)
    {z w : ℂ} (hzw : z ≠ w) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun δ : ℝ => P {ω | ¬ δ ^ (dgLambda γ + η) ≤
      dgLFPP (xiGamma γ) (fun x => hc δ x ω) univ z w}) (𝓝[>] 0) (𝓝 0) := by
  set r := ‖w - z‖
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzw.symm)
  set ζ := min η (1 / 2)
  have hζ : ζ ∈ Ioo (0 : ℝ) 1 := ⟨lt_min hη (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨p, C, δ₀, hp, hδ₀, hb⟩ := h315 γ hγ hγ2 P hc hG (ball z r) {z} isOpen_ball
    (isBounded_ball (x := z) (r := r)) isCompact_singleton
    (singleton_subset_iff.2 (mem_ball_self hr)) ζ hζ
  have hwf : w ∈ frontier (ball z r) := by
    rw [frontier_ball z hr.ne', mem_sphere, dist_eq_norm]
  refine t15_tendsto_mono (lt_min hδ₀ one_pos) (fun δ hδ ω hω => ?_)
    (t15_tendsto_of_poly hp hδ₀ (hb · ·))
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  intro hgood
  apply hω
  have h1 : ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
      ENNReal.ofReal (dgLFPP (xiGamma γ) (fun x => hc δ x ω) univ z w) :=
    hgood.trans (iInf₂_le_of_le z rfl (iInf₂_le w hwf))
  rw [ENNReal.ofReal_le_ofReal_iff (t15_dgLFPP_nonneg _ _ _ _ _)] at h1
  exact (t15_rpow_mono hδ1 (by linarith [min_le_left η (1 / 2)])).trans h1

/-! ## The three statements -/

/-- **DG Theorem 1.5** (DG:336–356) from DG Propositions 3.15 and 3.18 (proof DG:1782–1785). -/
theorem dgThm1_5_of (h315 : DGProp3_15) (h321 : Blueprint.DGProp3_21) : DGThm1_5 := by
  intro γ hγ hγ2 Ω _ P hc hG
  refine ⟨fun z w hzw η hη => ?_, fun U K hU hUc hUb hK hKU hzw η hη => ?_⟩
  · refine t15_tendsto_mono one_pos (fun δ _ ω hω => ?_)
      (t15_tendsto_union (t15_tendsto_lower h315 hγ hγ2 hG hzw hη)
        (t15_tendsto_upper h321 hγ hγ2 hG z w hη))
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
    exact hω ⟨hn.1, hn.2⟩
  · obtain ⟨z, hz, w, hw, hzw⟩ := hzw
    set ζ := min η (1 / 2)
    have hζ : ζ ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_min hη (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
    obtain ⟨p, C, δ₀, hp, hδ₀, hb⟩ := h321 γ hγ hγ2 U K hU hUc hK hKU ζ hζ
    obtain ⟨q, hq⟩ := t15_exists_isDGPath hU hUc (hKU hz) (hKU hw)
    have hpath : ∃ q, IsDGPath (closure U) z w q :=
      ⟨q, ⟨hq.source, hq.target, hq.mapsTo.mono_right subset_closure, hq.continuousOn,
        hq.piecewise_contDiff⟩⟩
    refine t15_tendsto_mono (lt_min hδ₀ one_pos) (fun δ hδ ω hω => ?_)
      (t15_tendsto_union (t15_tendsto_lower h315 hγ hγ2 hG hzw hη)
        (t15_tendsto_of_poly hp hδ₀ (hb P hc hG)))
    have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
    apply hω
    refine ⟨?_, hn.2.trans (ENNReal.ofReal_le_ofReal
      (t15_rpow_mono hδ1 (by linarith [min_le_left η (1 / 2)])))⟩
    refine (ENNReal.ofReal_le_ofReal (hn.1.trans (t15_dgLFPP_mono (subset_univ _) hpath))).trans ?_
    exact le_iSup₂_of_le z hz (le_iSup₂_of_le w hw le_rfl)

/-- **DG Theorem 1.5, second half of (1.5b)** (`Blueprint.DGThm1_5KU`, DG:343–346) from DG
Propositions 3.15 and 3.18 (DG:1784–1785). -/
theorem dgThm1_5KU_of (h315 : DGProp3_15) (h321 : Blueprint.DGProp3_21) : DGThm1_5KU := by
  intro γ hγ hγ2 Ω _ P hc hG U K hU hUb hK hKne hKU η hη
  obtain ⟨z, hz⟩ := hKne
  have hUne : U ≠ univ := by
    obtain ⟨R, hR⟩ := hUb.exists_norm_le
    intro h
    have := hR ((|R| + 1 : ℝ) : ℂ) (h ▸ mem_univ _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  obtain ⟨w, hw⟩ := nonempty_frontier_iff.2 ⟨⟨z, hKU hz⟩, hUne⟩
  set ζ := min η (1 / 2)
  have hζ : ζ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min hη (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨p, C, δ₀, hp, hδ₀, hb⟩ := h315 γ hγ hγ2 P hc hG U K hU hUb hK hKU ζ hζ
  refine t15_tendsto_mono (lt_min hδ₀ one_pos) (fun δ hδ ω hω => ?_)
    (t15_tendsto_union (t15_tendsto_of_poly hp hδ₀ (hb · ·))
      (t15_tendsto_upper h321 hγ hγ2 hG z w hη))
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
  apply hω
  refine ⟨(ENNReal.ofReal_le_ofReal (t15_rpow_mono hδ1
    (by linarith [min_le_left η (1 / 2)]))).trans hn.1, ?_⟩
  exact (iInf₂_le_of_le z hz (iInf₂_le w hw)).trans (ENNReal.ofReal_le_ofReal hn.2)

end LQGMetric.DG
