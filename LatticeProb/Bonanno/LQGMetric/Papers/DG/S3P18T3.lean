/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18T3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Prop 3.18 on squares: reduction to one reference process (DG:1774–1777)

DG's statement "the same is true with a whole-plane GFF" (DG:1776) is a statement about the law of
the field. `DGProp3_18Sq` quantifies over every process `hc` with `IsGFFCircleAverage hc P`. Here:

* `t18DistR_eq` — on `S' = t18Sq c R` the LFPP distance between rational points is the countable
  infimum of chain costs in the coordinates (`LFPP.lfppDOn_eq_iInf_chain`);
* `t18_event_iff` — the event `max_{z,w∈S} D^δ(z,w;S(1/2)) ≤ t` is `g ∈ t18B`, a measurable set of
  coordinates `g = (φ(c + r q))_{q ∈ ℚ²}`;
* `t18_bad_eq` — its probability is the same for all such processes (`t18T_measure_eq`);
* **`dgProp3_18Sq_of_ref : DGProp3_18SqRef → DGProp3_18Sq`**: it suffices to prove the bound for
  one process with `IsGFFCircleAverage` (chosen per `γ, S, ζ`), e.g. the circle averages of a
  normalized whole-plane GFF on which L2.2 (`L22T.dg_lemma22_tr`) is available.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open LFPP

/-- the rational points `c + r q` lying in `t18Sq c R` -/
def t18Ch (c : ℂ) (r R : ℝ) : Set ℂ := t18Pt c r '' {q | t18Pt c r q ∈ t18Sq c R}

lemma t18Ch_countable (c : ℂ) (r R : ℝ) : (t18Ch c r R).Countable :=
  (Set.to_countable _).image _

/-- a rational label of a point of `t18Ch` -/
def t18tch {c : ℂ} {r R : ℝ} (x : t18Ch c r R) : ℚ × ℚ := x.2.choose

lemma t18Pt_tch {c : ℂ} {r R : ℝ} (x : t18Ch c r R) : t18Pt c r (t18tch x) = x :=
  x.2.choose_spec.2

/-- the labels of the vertices `chainV` of a chain -/
def t18VT {c : ℂ} {r R : ℝ} (a b : ℚ × ℚ) (N : ℕ) (q : Fin N → t18Ch c r R) (i : ℕ) : ℚ × ℚ :=
  if h0 : i = 0 then a else if h : i ≤ N then t18tch (q ⟨i - 1, by omega⟩) else b

lemma t18Pt_VT {c : ℂ} {r R : ℝ} (a b : ℚ × ℚ) (N : ℕ) (q : Fin N → t18Ch c r R) (i : ℕ) :
    t18Pt c r (t18VT a b N q i) = chainV (t18Pt c r a) (t18Pt c r b) N q i := by
  unfold t18VT chainV
  split_ifs <;> simp [t18Pt_tch]

/-- the LFPP distance in `t18Sq c R` between rational points, in the coordinates `g` -/
def t18DistR (ξ : ℝ) (c : ℂ) (r R : ℝ) (g : ℚ × ℚ → ℝ) (a b : ℚ × ℚ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (q : Fin N → t18Ch c r R), ∑ i ∈ Finset.range (N + 1),
    t18Seg ξ c r g (t18VT a b N q i) (t18VT a b N q (i + 1))

lemma measurable_t18DistR (ξ : ℝ) (c : ℂ) (r R : ℝ) (a b : ℚ × ℚ) :
    Measurable fun g => t18DistR ξ c r R g a b := by
  have := (t18Ch_countable c r R).to_subtype
  exact Measurable.iInf fun N => Measurable.iInf fun q =>
    Finset.measurable_sum _ fun i _ => measurable_t18Seg ξ c r _ _

lemma t18DistR_eq {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {c : ℂ} {r R : ℝ} (hr : 0 < r)
    (hR : 0 < R) {a b : ℚ × ℚ} (ha : t18Pt c r a ∈ t18Sq c R) (hb : t18Pt c r b ∈ t18Sq c R) :
    t18DistR ξ c r R (fun q => φ (t18Pt c r q)) a b =
      lfppDOn ξ φ (t18Sq c R) (t18Pt c r a) (t18Pt c r b) := by
  have hCS : t18Ch c r R ⊆ t18Sq c R := by rintro _ ⟨q, hq, rfl⟩; exact hq
  have hC : ∀ x ∈ t18Sq c R, ∀ ρ > 0, ∃ q ∈ t18Ch c r R, ‖q - x‖ < ρ := fun x hx ρ hρ => by
    obtain ⟨q, hq, hn⟩ := t18Pt_dense hr hR hx hρ
    exact ⟨_, ⟨q, hq, rfl⟩, hn⟩
  rw [lfppDOn_eq_iInf_chain hφ (t18Sq_convex c R) hCS hC ha hb]
  simp only [t18DistR, chainCost, t18Seg_eq hφ, t18Pt_VT]

/-- `D^δ` as a real infimum and as `lfppDOn` -/
lemma t18_ofReal_dgLFPP {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ} {z w : ℂ}
    (hne : ∃ p, IsDGPath S z w p) :
    ENNReal.ofReal (dgLFPP ξ φ S z w) = lfppDOn ξ φ S z w := by
  have : Nonempty {p : ℝ → ℂ // IsDGPath S z w p} := ⟨⟨_, hne.choose_spec⟩⟩
  rw [dgLFPP, ENNReal.ofReal_iInf]
  apply le_antisymm
  · refine le_iInf fun P => ?_
    have hP : IsDGPath S z w P.1 := ⟨P.2.1.source, P.2.1.target, fun t ht => P.2.2 t ht,
      P.2.1.continuousOn, P.2.1.piecewise⟩
    exact iInf_le_of_le ⟨P.1, hP⟩ (t18_ofReal_lfppLength hφ hP).le
  · refine le_iInf fun p => ?_
    refine iInf_le_of_le ⟨p.1, ⟨p.2.source, p.2.target, p.2.continuousOn,
      p.2.piecewise_contDiff⟩, fun t ht => p.2.mapsTo ht⟩ ?_
    exact (t18_ofReal_lfppLength hφ p.2).ge

lemma t18Sq_mono {c : ℂ} {r R : ℝ} (h : r ≤ R) : t18Sq c r ⊆ t18Sq c R := fun _ hx =>
  ⟨hx.1.trans h, hx.2.trans h⟩

/-- the coordinate event `∀ rational a, b ∈ S, D(a,b; S(1/2)) ≤ t` -/
def t18B (ξ : ℝ) (c : ℂ) (r t : ℝ) : Set (ℚ × ℚ → ℝ) :=
  {g | ∀ a : ℚ × ℚ, t18Pt c r a ∈ t18Sq c r → ∀ b : ℚ × ℚ, t18Pt c r b ∈ t18Sq c r →
    t18DistR ξ c r (2 * r) g a b ≤ ENNReal.ofReal t}

lemma measurableSet_t18B (ξ : ℝ) (c : ℂ) (r t : ℝ) : MeasurableSet (t18B ξ c r t) := by
  simp only [t18B, Set.ofPred_forall]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_t18DistR ξ c r _ a b)
      measurable_const

/-- **the event of `DGProp3_18Sq` in the rational coordinates** -/
theorem t18_event_iff {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {c : ℂ} {r t : ℝ} (hr : 0 < r)
    (ht : 0 ≤ t) :
    (∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r, dgLFPP ξ φ (t18Sq c (2 * r)) z w ≤ t) ↔
      (fun q => φ (t18Pt c r q)) ∈ t18B ξ c r t := by
  have hsub : t18Sq c r ⊆ t18Sq c (2 * r) := t18Sq_mono (by linarith)
  have hcv := t18Sq_convex c (2 * r)
  have hconv : ∀ {z w}, z ∈ t18Sq c r → w ∈ t18Sq c r →
      ENNReal.ofReal (dgLFPP ξ φ (t18Sq c (2 * r)) z w) = lfppDOn ξ φ (t18Sq c (2 * r)) z w :=
    fun hz hw => t18_ofReal_dgLFPP hφ ⟨_, t18_isDGPath_segment hcv (hsub hz) (hsub hw)⟩
  constructor
  · intro h a ha b hb
    rw [t18DistR_eq hφ hr (by linarith) (hsub ha) (hsub hb), ← hconv ha hb]
    exact ENNReal.ofReal_le_ofReal (h _ ha _ hb)
  · intro h z hz w hw
    rw [← ENNReal.ofReal_le_ofReal_iff ht, hconv hz hw]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set E : ℂ → ℝ := fun x => Real.exp (ξ * φ x)
    have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
    obtain ⟨M, hM⟩ := (isCompact_closedBall c (4 * r)).exists_bound_of_continuousOn
      hE.continuousOn
    set ρ := min r ((ε : ℝ) / (2 * (|M| + 1)))
    have hρ : 0 < ρ := lt_min hr (by have : (0 : ℝ) < ε := hε; positivity)
    have hseg : ∀ x y : ℂ, x ∈ t18Sq c r → ‖y - x‖ < ρ →
        segCost ξ φ x y ≤ ENNReal.ofReal ((ε : ℝ) / 2) := by
      intro x y hx hxy
      refine (segCost_le (B := |M|) fun u hu => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
      · have hu' : u ∈ closedBall c (4 * r) := by
          have h1 := t18Sq_subset_ball c r hx
          rw [mem_closedBall, dist_eq_norm] at hu h1 ⊢
          have h2 := norm_sub_le_norm_sub_add_norm_sub u x c
          linarith [min_le_left r ((ε : ℝ) / (2 * (|M| + 1)))]
        exact (Real.le_norm_self _).trans ((hM u hu').trans (le_abs_self M))
      · have h1 : ρ ≤ (ε : ℝ) / (2 * (|M| + 1)) := min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at h1
        nlinarith [abs_nonneg M, norm_nonneg (y - x)]
    obtain ⟨a, ha, haz⟩ := t18Pt_dense hr hr hz hρ
    obtain ⟨b, hb, hbw⟩ := t18Pt_dense hr hr hw hρ
    have hab := h a ha b hb
    rw [t18DistR_eq hφ hr (by linarith) (hsub ha) (hsub hb)] at hab
    have e1 := (lfppDOn_le_segCost (ξ := ξ) (φ := φ) hcv (hsub hz) (hsub ha)).trans
      (hseg z _ hz haz)
    have e2 := (lfppDOn_le_segCost (ξ := ξ) (φ := φ) hcv (hsub hb) (hsub hw)).trans
      (hseg _ w hb (by rw [norm_sub_rev]; exact hbw))
    calc lfppDOn ξ φ (t18Sq c (2 * r)) z w
        ≤ lfppDOn ξ φ (t18Sq c (2 * r)) z (t18Pt c r a) +
          (lfppDOn ξ φ (t18Sq c (2 * r)) (t18Pt c r a) (t18Pt c r b) +
            lfppDOn ξ φ (t18Sq c (2 * r)) (t18Pt c r b) w) :=
          (lfppDOn_triangle _ (t18Pt c r a) _).trans (add_le_add le_rfl
            (lfppDOn_triangle _ (t18Pt c r b) _))
      _ ≤ ENNReal.ofReal ((ε : ℝ) / 2) + (ENNReal.ofReal t + ENNReal.ofReal ((ε : ℝ) / 2)) :=
          add_le_add e1 (add_le_add hab e2)
      _ = ENNReal.ofReal t + ε := by
          rw [add_comm, add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity),
            add_halves, ENNReal.ofReal_coe_nnreal]

lemma t18_bad_set {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) {c : ℂ} {r t : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) :
    {ω | ¬ ∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r,
        dgLFPP ξ (fun x => hc δ x ω) (t18Sq c (2 * r)) z w ≤ t} =
      {ω | t18Coord hc δ (t18Pt c r) ω ∈ (t18B ξ c r t)ᶜ} := by
  ext ω
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, mem_compl_iff,
    t18_event_iff (hG.continuous δ hδ ω) hr ht]
  rfl

/-- **law transfer of the event of `DGProp3_18Sq`** -/
theorem t18_bad_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {hc : ℝ → ℂ → Ω → ℝ} {hc' : ℝ → ℂ → Ω' → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) (hG' : LQGDimension.IsGFFCircleAverage hc' P')
    {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) {c : ℂ} {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    P {ω | ¬ ∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r,
        dgLFPP ξ (fun x => hc δ x ω) (t18Sq c (2 * r)) z w ≤ t} =
      P' {ω | ¬ ∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r,
        dgLFPP ξ (fun x => hc' δ x ω) (t18Sq c (2 * r)) z w ≤ t} := by
  rw [t18_bad_set hG hδ ξ hr ht, t18_bad_set hG' hδ ξ hr ht]
  exact t18T_measure_eq hG hG' hδ _ (measurableSet_t18B ξ c r t).compl

/-- `DGProp3_18Sq` for one process with `IsGFFCircleAverage` (per `γ`, square, `ζ`) -/
def DGProp3_18SqRef : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ ζ ∈ Ioo (0 : ℝ) 1,
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage hc P ∧ ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧
        ∀ δ ∈ Ioo (0 : ℝ) δ₀,
          P {ω | ¬ ∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r,
            dgLFPP (xiGamma γ) (fun x => hc δ x ω) (t18Sq c (2 * r)) z w ≤
              δ ^ (dgLambda γ - ζ)} ≤ ENNReal.ofReal (C * δ ^ p)

/-- **`DGProp3_18Sq` from one reference process** (the law step of DG:1776) -/
theorem dgProp3_18Sq_of_ref (h : DGProp3_18SqRef) : DGProp3_18Sq := by
  intro γ hγ hγ2 c r hr ζ hζ
  obtain ⟨Ω₀, _, P₀, H, hH, p, C, δ₀, hp, hδ₀, hb⟩ := h γ hγ hγ2 c r hr ζ hζ
  refine ⟨p, C, δ₀, hp, hδ₀, ?_⟩
  intro Ω _ P hc hG δ hδ
  rw [t18_bad_eq hG hH hδ.1 _ hr (Real.rpow_nonneg hδ.1.le _)]
  exact hb δ hδ

end LQGMetric.DG
