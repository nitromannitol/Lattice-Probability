/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8Len at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Final
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eConcat

/-!
# The set of length metrics is universally measurable; `CopyAeLength` (task P2-ANALYTIC)

`{d : ContMetric | d.IsLength}` is the projection of a Borel subset of
`ContMetric × (ℕ × ℕ × ℕ → C([0,1], ℂ))` (`c18LenS`): with `q` the dense sequence of `ℂ`, the
witness is a family of paths `Γ (i, j, m)` from `q i` to `q j` of `d`-length at most
`d(q i, q j) + 1/(m+1)` (`c18_isLength_iff`). Hence it is universally measurable
(`c18_uMeasurableSet_isLength`) by Lusin's theorem (Kechris, *Classical Descriptive Set Theory*,
Thm 21.10, in the project as `UMeasurableSet.setOf_exists`, via QuantumZipper
`analyticSet_nullMeasurableSet`), which gives `CopyAeLength` (`copyAeLength_of_nullMeasurable`),
P2-LM17b's `T17KernelLength`, and LM Corollary 1.8 from LM Theorem 1.7 alone.

The converse direction of `c18_isLength_iff` (paths between dense points give paths between all
points) is an own elementary argument: a point `x` is joined to a dense point by the infinite
concatenation (`GM.p412e_concat`) of near-geodesics between dense points converging to `x`.
LM take the measurability for granted (LM l. 323–332, "conditionally i.i.d. samples").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint MetricGeometry GM

/-- the dense sequence of `ℂ` -/
abbrev c18q : ℕ → ℂ := TopologicalSpace.denseSeq ℂ

/-- the Borel witness relation: `Γ (i, j, m)` is a path from `q i` to `q j` of `d`-length at
most `d(q i, q j) + 1/(m+1)` -/
def c18LenS : Set (ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ))) :=
  {p | ∀ k : ℕ × ℕ × ℕ, p.2 k 0 = c18q k.1 ∧ p.2 k 1 = c18q k.2.1 ∧
    p.1.len (fun t => p.2 k (pj t)) 0 1 ≤
      edist (p.1.pt (c18q k.1)) (p.1.pt (c18q k.2.1)) + ENNReal.ofReal (1 / ((k.2.2 : ℝ) + 1))}

theorem c18_measurableSet_lenS : MeasurableSet c18LenS := by
  have key : ∀ k : ℕ × ℕ × ℕ, MeasurableSet {p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) |
      p.2 k 0 = c18q k.1 ∧ p.2 k 1 = c18q k.2.1 ∧
      p.1.len (fun t => p.2 k (pj t)) 0 1 ≤
        edist (p.1.pt (c18q k.1)) (p.1.pt (c18q k.2.1)) +
          ENNReal.ofReal (1 / ((k.2.2 : ℝ) + 1))} := by
    intro k
    have ev : Measurable fun p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) => p.2 k :=
      (measurable_pi_apply k).comp measurable_snd
    have ev' : ∀ a : unitInterval, Measurable
        fun p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) => p.2 k a :=
      fun a => (continuous_eval_const a).measurable.comp ev
    have hlen : Measurable fun p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) =>
        p.1.len (fun t => p.2 k (pj t)) 0 1 := by
      have hm0 : Measurable fun p : ContMetric × C(unitInterval, ℂ) =>
          p.1.len (fun t => p.2 (pj t)) 0 1 := lowerSemicontinuous_lenPath.measurable
      exact hm0.comp (f := fun p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) => (p.1, p.2 k))
        (measurable_fst.prodMk ev)
    have hed : Measurable fun p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) =>
        edist (p.1.pt (c18q k.1)) (p.1.pt (c18q k.2.1)) :=
      ContMetric.measurable_edist_pt.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_const))
    exact (measurableSet_eq_fun (ev' 0) measurable_const).inter
      ((measurableSet_eq_fun (ev' 1) measurable_const).inter
        (measurableSet_le hlen (hed.add measurable_const)))
  have e : c18LenS = ⋂ k : ℕ × ℕ × ℕ, {p : ContMetric × (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) |
      p.2 k 0 = c18q k.1 ∧ p.2 k 1 = c18q k.2.1 ∧
      p.1.len (fun t => p.2 k (pj t)) 0 1 ≤
        edist (p.1.pt (c18q k.1)) (p.1.pt (c18q k.2.1)) +
          ENNReal.ofReal (1 / ((k.2.2 : ℝ) + 1))} := by
    ext p; simp only [c18LenS, mem_ofPred_eq, mem_iInter]
  rw [e]
  exact MeasurableSet.iInter key

/-- a path in `d.Space` as an element of `C([0,1], ℂ)` -/
def c18toC (d : ContMetric) {x y : d.Space} (γ : Path x y) : C(unitInterval, ℂ) :=
  ⟨fun t => (ContMetric.ptHomeomorph d).symm (γ t),
    (ContMetric.ptHomeomorph d).symm.continuous.comp γ.continuous⟩

theorem c18_len_toC (d : ContMetric) {x y : d.Space} (γ : Path x y) :
    d.len (fun t => c18toC d γ (pj t)) 0 1 = pathLength γ := rfl

/-- the dense points are dense in `d.Space` -/
theorem c18_denseRange (d : ContMetric) : DenseRange fun n => d.pt (c18q n) :=
  (Function.Surjective.denseRange (f := d.pt) Function.surjective_id).comp
    (TopologicalSpace.denseRange_denseSeq ℂ) (ContMetric.continuous_pt d)

/-- from the witness: every point is joined to some dense point at distance `< δ` by a path of
length `≤ δ` (infinite concatenation, `GM.p412e_concat`) -/
theorem c18_short_path (d : ContMetric) {Γ : ℕ × ℕ × ℕ → C(unitInterval, ℂ)}
    (hΓ : (d, Γ) ∈ c18LenS) (x : d.Space) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, dist (d.pt (c18q a)) x < δ ∧
      ∃ γ : Path (d.pt (c18q a)) x, pathLength γ ≤ ENNReal.ofReal δ := by
  set e : ℕ → ℝ := fun k => δ / 8 * (1 / 2) ^ k with he
  have he0 : ∀ k, 0 < e k := fun k => by positivity
  have hemono : ∀ k, e (k + 1) ≤ e k := fun k => by
    have h2 : e (k + 1) = e k / 2 := by simp only [he, pow_succ]; ring
    have := he0 k
    linarith
  have hd := Metric.denseRange_iff.1 (c18_denseRange d)
  choose a ha using fun k => hd x (e k) (he0 k)
  choose m hm using fun k => exists_nat_one_div_lt (he0 k)
  let η : ℕ → C(unitInterval, ℂ) := fun k => Γ (a k, a (k + 1), m k)
  let γ : ℕ → ℝ → d.Space := fun k t => d.pt (η k (pj t))
  have hcont : ∀ k, ContinuousOn (γ k) (Icc 0 1) := fun k =>
    ((ContMetric.continuous_pt d).comp ((η k).continuous.comp continuous_projIcc)).continuousOn
  have h0 : ∀ k, γ k 0 = d.pt (c18q (a k)) := fun k => by
    show d.pt (η k (pj 0)) = _
    rw [show pj 0 = 0 from Subtype.ext (pj_coe_of_mem ⟨le_rfl, zero_le_one⟩)]
    exact congrArg d.pt (hΓ (a k, a (k + 1), m k)).1
  have h1 : ∀ k, γ k 1 = d.pt (c18q (a (k + 1))) := fun k => by
    show d.pt (η k (pj 1)) = _
    rw [show pj 1 = 1 from Subtype.ext (pj_coe_of_mem ⟨zero_le_one, le_rfl⟩)]
    exact congrArg d.pt (hΓ (a k, a (k + 1), m k)).2.1
  have hj : ∀ k, γ k 1 = γ (k + 1) 0 := fun k => by rw [h1, h0]
  have hlen : ∀ k, curveLength (γ k) 0 1 ≤ ENNReal.ofReal (3 * e k) := fun k => by
    have := (hΓ (a k, a (k + 1), m k)).2.2
    refine this.trans ?_
    rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have t1 := dist_triangle_right (d.pt (c18q (a k))) (d.pt (c18q (a (k + 1)))) x
    have := ha k; have := ha (k + 1); have := hm k; have := hemono k
    rw [dist_comm] at *
    simp only at *
    linarith
  have hsum : HasSum (fun k => 3 * e k) (3 * (δ / 8) * 2) := by
    simp only [he, ← mul_assoc]
    exact (hasSum_geometric_two).mul_left _
  have htsum : ∑' k, curveLength (γ k) 0 1 ≤ ENNReal.ofReal (3 * (δ / 8) * 2) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => (mul_pos three_pos (he0 k)).le)
      hsum.summable]
    exact ENNReal.tsum_le_tsum hlen
  have hp : Tendsto (fun k => γ k 0) atTop (𝓝 x) := by
    simp only [h0]
    have he_t : Tendsto e atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (δ / 8)
      simpa [he] using this
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => (ha k).le.trans_eq' (dist_comm _ _)) he_t)
  obtain ⟨hc, hc0, hc1, hcl, -⟩ := p412e_concat hcont hj hp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htsum)
  obtain ⟨π, hπ, -⟩ := exists_path_of_curve zero_le_one hc
  refine ⟨a 0, (dist_comm _ _).trans_lt ((ha 0).trans_le (by simp [he]; linarith)),
    π.cast (by rw [hc0, h0]) hc1.symm, ?_⟩
  show pathLength π ≤ _
  rw [hπ]
  exact hcl.trans (htsum.trans (ENNReal.ofReal_le_ofReal (by linarith)))

/-- **`d` is a length metric iff it has a Borel witness** -/
theorem c18_isLength_iff (d : ContMetric) : d.IsLength ↔ ∃ Γ, (d, Γ) ∈ c18LenS := by
  constructor
  · intro hL
    have := fun k : ℕ × ℕ × ℕ => hL (d.pt (c18q k.1)) (d.pt (c18q k.2.1))
      (1 / ((k.2.2 : ℝ) + 1)) (by positivity)
    choose γ hγ using this
    refine ⟨fun k => c18toC d (γ k), fun k => ⟨congrArg d.unpt (γ k).source, congrArg d.unpt (γ k).target, ?_⟩⟩
    exact (c18_len_toC d (γ k)).trans_le (hγ k)
  · rintro ⟨Γ, hΓ⟩ x y ε hε
    set δ := ε / 6 with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨a, hax, γa, hγa⟩ := c18_short_path d hΓ x hδ0
    obtain ⟨b, hby, γb, hγb⟩ := c18_short_path d hΓ y hδ0
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ0
    have hab := (hΓ (a, b, m))
    let η : Path (d.pt (c18q a)) (d.pt (c18q b)) :=
      { toFun := fun t => d.pt (Γ (a, b, m) t)
        continuous_toFun := (ContMetric.continuous_pt d).comp (Γ (a, b, m)).continuous
        source' := congrArg d.pt hab.1
        target' := congrArg d.pt hab.2.1 }
    have hη : pathLength η ≤ ENNReal.ofReal (dist (d.pt (c18q a)) (d.pt (c18q b)) + δ) := by
      refine (show pathLength η = d.len (fun t => Γ (a, b, m) (pj t)) 0 1 from rfl) ▸
        hab.2.2.trans ?_
      rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by simp only at hm ⊢; linarith)
    refine ⟨(γa.symm.trans η).trans γb, ?_⟩
    rw [pathLength_trans, pathLength_trans, pathLength_symm, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg hε.le]
    have t1 := dist_triangle4 (d.pt (c18q a)) x y (d.pt (c18q b))
    have hsum : ENNReal.ofReal δ + ENNReal.ofReal (dist (d.pt (c18q a)) (d.pt (c18q b)) + δ) +
        ENNReal.ofReal δ ≤ ENNReal.ofReal (dist x y + ε) := by
      rw [← ENNReal.ofReal_add hδ0.le (by positivity), ← ENNReal.ofReal_add (by positivity)
        hδ0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [dist_comm] at hby
      linarith
    exact (add_le_add (add_le_add hγa hη) hγb).trans hsum

instance c18_sbW : StandardBorelSpace (ℕ × ℕ × ℕ → C(unitInterval, ℂ)) := inferInstance

/-- **the set of length metrics is universally measurable** (analytic + Lusin) -/
theorem c18_uMeasurableSet_isLength : UMeasurableSet {d : ContMetric | d.IsLength} := by
  have := UMeasurableSet.setOf_exists c18_measurableSet_lenS
  convert this using 1
  ext d
  exact c18_isLength_iff d

/-- **`CopyAeLength` holds** -/
theorem copyAeLength : CopyAeLength :=
  copyAeLength_of_nullMeasurable fun μ _ => c18_uMeasurableSet_isLength μ inferInstance

/-- P2-LM17b's blocker (handoff/P2-LM17b.md): for a.e. field `g`, the conditional law of `D`
given `h = g` is concentrated on length metrics -/
def T17KernelLength : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D : Ω → ContMetric), Measurable h → Measurable D → (∀ᵐ ω ∂P, (D ω).IsLength) →
    ∀ᵐ g ∂P.map h, ∀ᵐ d ∂condDistrib D h P g, d.IsLength

theorem t17KernelLength : T17KernelLength := by
  intro Ω _ P _ h D hm hD hlD
  have : IsProbabilityMeasure (P.map D) :=
    (Measure.isProbabilityMeasure_map_iff hD.aemeasurable).2 inferInstance
  obtain ⟨M, hMS, hM, hMae⟩ :=
    (c18_uMeasurableSet_isLength (P.map D) inferInstance).exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null
    (show (P.map D) ({d : ContMetric | d.IsLength} \ M) = 0 from ae_le_set.1 hMae.symm.le)
  have hDM : ∀ᵐ ω ∂P, D ω ∈ M := by
    have hN' : ∀ᵐ ω ∂P, D ω ∉ N := by
      rw [Measure.map_apply hD hN] at hN0
      exact measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hlD, hN'] with ω h1 h2
    by_contra h3
    exact h2 (hSN ⟨h1, h3⟩)
  have h2 : ∀ᵐ p ∂(P.map h ⊗ₘ condDistrib D h P), p.2 ∈ M := by
    rw [compProd_map_condDistrib hm.aemeasurable hD.aemeasurable]
    exact (ae_map_iff (hm.prodMk hD).aemeasurable (measurable_snd hM)).2 hDM
  exact ((Measure.ae_compProd_iff (measurable_snd hM)).1 h2).mono fun g hg =>
    hg.mono fun d hd => hMS hd

/-- **LM Corollary 1.8** (`cor-bilip-msrble`, l. 317–332) from LM Theorem 1.7 alone -/
theorem lmCor1_8_of_thm1_7' (h17 : LMThm1_7) : Blueprint.LMCor1_8 :=
  lmCor1_8_of_thm1_7 h17 copyAeLength

end LQGMetric.LM
