/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.Subseq at commit 31e7483; only the module paths of local imports are changed.
   Changed: docstring wording of the module docstring entry for gm_tip_congr and gm_tip_smul_of_aemeasurable. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Defs
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Analysis.Multiplicative

/-!
# GM §1.4: elementary steps (blueprint M1, §3 rows 4–8)

Source: Gwynne–Miller, arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex`.

* `gm_s1_9_unique` (GM.S1.9, l. 507–509): the constant `𝔨_b` with `D^{(b)}_h = 𝔨_b D_h` is
  unique (evaluate at `(0, 1)`, where `D_h(0,1) > 0`, on a normalized GFF).
* `gm_s1_9_comp` (GM.S1.9, l. 509): `(D^{(b₁)})^{(b₂)} = D^{(b₁ b₂)}`, pathwise.
* `gm_s1_11_cauchy` (GM.S1.11, l. 519): a positive multiplicative `𝔨`, continuous at `1`, is a
  power `b ↦ b^β`. Reuses `LQGMetric.Analysis.exists_rpow_of_mul_of_continuous_logExp`
  (task P2-ELEM); continuity at `1` gives continuity of the additive map `t ↦ log 𝔨(eᵗ)` at `0`,
  hence everywhere (mathlib `continuous_of_continuousAt_zero`).
* `gm_s1_20` (GM.S1.20, l. 591–593, "every sequence has a subsequence along which …"): the
  sub-subsequence principle for convergence in probability along `ε → 0⁺`, via mathlib
  `Filter.tendsto_of_subseq_tendsto`.
* `gm_tip_congr`, `gm_tip_smul_of_aemeasurable`: convergence in probability is unchanged by
  a.s. modification of the limit, and is preserved by deterministic scalars `a_i → a₀`.
  (Own elementary proofs.) The scalar version assumes each `ω ↦ Y ω p` is a.e.-measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM

/-- a whole-plane GFF is a whole-plane GFF plus the continuous function `0` -/
theorem isGFFPlusCont_of_isWholePlaneGFF {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsGFFPlusCont h P := by
  refine ⟨hh.measurable, fun _ => ContinuousMap.const ℂ 0, measurable_const, ?_⟩
  have h0 : ofCont (ContinuousMap.const ℂ 0) = 0 := by
    have := GFFLaw.addConst_zero' (0 : DistC)
    simpa [addConst, addFun] using this
  have e : (fun ω => h ω - ofCont (ContinuousMap.const ℂ 0)) = h := by
    funext ω; rw [h0, sub_zero]
  rw [e]; exact hh

/-- **GM.S1.9** (uniqueness of `𝔨_b`). -/
theorem gm_s1_9_unique {D D' : DistC → ContMetric} {k k' : ℝ} (hex : ExistsNormalizedGFF)
    (hk : EqSmulAS D' D k) (hk' : EqSmulAS D' D k') : k = k' := by
  obtain ⟨Ω, _, P, _, h, hh⟩ := hex
  have hc := isGFFPlusCont_of_isWholePlaneGFF hh.1
  obtain ⟨ω, h1, h2⟩ := ((hk P h hc).and (hk' P h hc)).exists
  have hne : (D (h ω)).1 (0, 1) ≠ 0 := fun h0 => zero_ne_one ((D (h ω)).2.eq_of_eq_zero 0 1 h0)
  exact mul_right_cancel₀ hne ((h1 0 1).symm.trans (h2 0 1))

/-- `h(·/b₂)(·/b₁) = h(·/(b₁ b₂))` -/
theorem affineComp_inv_comp {b₁ b₂ : ℝ} (h₁ : 0 < b₁) (h₂ : 0 < b₂) (h : DistC) :
    affineComp b₁⁻¹ 0 (affineComp b₂⁻¹ 0 h) = affineComp (b₁ * b₂)⁻¹ 0 h := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull b₂⁻¹ 0 (testAffinePull b₁⁻¹ 0 φ) = testAffinePull (b₁ * b₂)⁻¹ 0 φ :=
    TestFunction.ext fun x => by
      rw [testAffinePull_apply _ _ (inv_ne_zero h₂.ne'), testAffinePull_apply _ _
        (inv_ne_zero h₁.ne'), testAffinePull_apply _ _ (inv_ne_zero (mul_pos h₁ h₂).ne')]
      congr 1
      push_cast
      field_simp
      ring
  rw [GFFInv.affineComp_apply, GFFInv.affineComp_apply, GFFInv.affineComp_apply, e]
  rw [inv_pow, inv_pow, inv_pow, inv_inv, inv_inv, inv_inv, mul_pow]
  ring

/-- **GM.S1.9** (composition `(D^{(b₁)})^{(b₂)} = D^{(b₁ b₂)}`, GM l. 509). -/
theorem gm_s1_9_comp (D : DistC → ContMetric) {b₁ b₂ : ℝ} (h₁ : 0 < b₁) (h₂ : 0 < b₂) :
    dilateMetric b₂ h₂ (dilateMetric b₁ h₁ D) = dilateMetric (b₁ * b₂) (mul_pos h₁ h₂) D := by
  funext h
  refine Subtype.ext (ContinuousMap.ext fun p => ?_)
  show (D (affineComp b₁⁻¹ 0 (affineComp b₂⁻¹ 0 h))).1 ((b₁ : ℂ) * ((b₂ : ℂ) * p.1),
      (b₁ : ℂ) * ((b₂ : ℂ) * p.2)) =
    (D (affineComp (b₁ * b₂)⁻¹ 0 h)).1 (((b₁ * b₂ : ℝ) : ℂ) * p.1, ((b₁ * b₂ : ℝ) : ℂ) * p.2)
  rw [affineComp_inv_comp h₁ h₂]
  push_cast
  simp only [mul_assoc]

/-- **GM.S1.11** (Cauchy equation, GM l. 519): a positive multiplicative `k` on `(0,∞)` that is
continuous at `1` is `b ↦ b^β`. -/
theorem gm_s1_11_cauchy (k : ℝ → ℝ) (hpos : ∀ b, 0 < b → 0 < k b)
    (hmul : ∀ b₁ b₂, 0 < b₁ → 0 < b₂ → k (b₁ * b₂) = k b₁ * k b₂) (hcont : ContinuousAt k 1) :
    ∃ β : ℝ, ∀ b, 0 < b → k b = b ^ β := by
  refine Analysis.exists_rpow_of_mul_of_continuous_logExp k hpos hmul ?_
  let F : ℝ →+ ℝ := AddMonoidHom.mk' (fun t => Real.log (k (Real.exp t))) (by
    intro s t
    rw [Real.exp_add, hmul _ _ (Real.exp_pos s) (Real.exp_pos t),
      Real.log_mul (hpos _ (Real.exp_pos s)).ne' (hpos _ (Real.exp_pos t)).ne'])
  have h0 : ContinuousAt F 0 := by
    have he : ContinuousAt (fun t => k (Real.exp t)) 0 := by
      refine ContinuousAt.comp (g := k) ?_ Real.continuous_exp.continuousAt
      rwa [Real.exp_zero]
    have hk1 : k (Real.exp 0) ≠ 0 := (hpos _ (Real.exp_pos 0)).ne'
    exact he.log hk1
  exact continuous_of_continuousAt_zero F h0

/-- **GM.S1.20** (sub-subsequence principle, GM l. 591–593). -/
theorem gm_s1_20 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℂ × ℂ → ℝ) (Y : Ω → ℂ × ℂ → ℝ)
    (H : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoInProbLU P (fun n => X (ε (φ n))) atTop Y) :
    TendstoInProbLU P X (𝓝[>] 0) Y := by
  intro R hR δ hδ
  refine tendsto_of_subseq_tendsto fun x hx => ?_
  obtain ⟨hx0, hxpos⟩ := tendsto_nhdsWithin_iff.1 hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 hxpos
  obtain ⟨φ, -, hT⟩ := H (fun n => x (n + N)) (fun n => hN _ (Nat.le_add_left N n))
    ((tendsto_add_atTop_iff_nat N).2 hx0)
  exact ⟨fun n => φ n + N, hT R hR δ hδ⟩

/-- `TendstoInProbLU` under a.e. equality of the limits -/
theorem gm_tip_congr {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → ℂ × ℂ → ℝ) (l : Filter ι) (Y Y' : Ω → ℂ × ℂ → ℝ)
    (hX : TendstoInProbLU P X l Y) (hY : ∀ᵐ ω ∂P, Y ω = Y' ω) : TendstoInProbLU P X l Y' := by
  intro R hR δ hδ
  refine (hX R hR δ hδ).congr fun i => measure_congr ?_
  filter_upwards [hY] with ω hω
  simp only [hω]

/-- pointwise: `|a x − a₀ y| ≤ |a| |x − y| + |a − a₀| |y|` -/
lemma edist_mul_mul_le (a a₀ x y : ℝ) :
    edist (a * x) (a₀ * y) ≤
      ENNReal.ofReal |a| * edist x y + ENNReal.ofReal |a - a₀| * ENNReal.ofReal |y| := by
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← abs_mul, ← abs_mul]
  calc |a * x - a₀ * y| = |a * (x - y) + (a - a₀) * y| := by ring_nf
    _ ≤ _ := abs_add_le _ _

/-- the sup of `|Y ω|` over a compact set is a.e.-measurable when `Y ω` is continuous and each
evaluation is a.e.-measurable (reduce to a countable dense subset) -/
lemma aemeasurable_iSup_abs {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℂ × ℂ → ℝ} (hYc : ∀ ω, Continuous (Y ω)) (hYm : ∀ p, AEMeasurable (fun ω => Y ω p) P)
    (B : Set (ℂ × ℂ)) :
    AEMeasurable (fun ω => ⨆ p ∈ B, ENNReal.ofReal |Y ω p|) P := by
  obtain ⟨T, hTc, hTB, hBT⟩ := TopologicalSpace.exists_countable_dense_subset B
  have e : (fun ω => ⨆ p ∈ B, ENNReal.ofReal |Y ω p|) =
      fun ω => ⨆ q : T, ENNReal.ofReal |Y ω q| := by
    funext ω
    refine le_antisymm (iSup₂_le fun p hp => ?_) (iSup_le fun q => le_iSup₂_of_le (q : ℂ × ℂ)
      (hTB q.2) le_rfl)
    have hcl : IsClosed {p : ℂ × ℂ | ENNReal.ofReal |Y ω p| ≤ ⨆ q : T, ENNReal.ofReal |Y ω q|} :=
      isClosed_le (ENNReal.continuous_ofReal.comp (hYc ω).abs) continuous_const
    exact hcl.closure_subset_iff.2 (fun q hq => by
      simp only [mem_setOf_eq]
      exact le_iSup (fun q' : T => ENNReal.ofReal |Y ω q'|) ⟨q, hq⟩) (hBT hp)
  rw [e]
  have := hTc.to_subtype
  exact AEMeasurable.iSup fun q => ENNReal.measurable_ofReal.comp_aemeasurable
    (continuous_abs.measurable.comp_aemeasurable (hYm q))

/-- `TendstoInProbLU` under deterministic scalars `a_i → a₀` (row 8, `TIP_smul` with the
measurability hypothesis `hYm`, which `blueprint/M1.md` §5 omits). Own elementary proof. -/
theorem gm_tip_smul_of_aemeasurable {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (X : ι → Ω → ℂ × ℂ → ℝ) (l : Filter ι) (Y : Ω → ℂ × ℂ → ℝ)
    (a : ι → ℝ) (a₀ : ℝ) (hYc : ∀ ω, Continuous (Y ω))
    (hYm : ∀ p, AEMeasurable (fun ω => Y ω p) P) (hX : TendstoInProbLU P X l Y)
    (ha : Tendsto a l (𝓝 a₀)) :
    TendstoInProbLU P (fun i ω => a i • X i ω) l (fun ω => a₀ • Y ω) := by
  intro R hR δ hδ
  set B := Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R with hBdef
  have hB : IsCompact B := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  set M : Ω → ℝ≥0∞ := fun ω => ⨆ p ∈ B, ENNReal.ofReal |Y ω p| with hMdef
  have hMm : AEMeasurable M P := aemeasurable_iSup_abs hYc hYm B
  have hMfin : ∀ ω, M ω < ⊤ := fun ω => by
    obtain ⟨C, hC⟩ := hB.exists_bound_of_continuousOn (hYc ω).continuousOn
    have hle : M ω ≤ ENNReal.ofReal C := iSup₂_le fun p hp =>
      ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC p hp)
    exact hle.trans_lt ENNReal.ofReal_lt_top
  -- the tail of `M`
  set S : ℕ → Set Ω := fun n => {ω | (n : ℝ≥0∞) ≤ M ω} with hSdef
  have hS : Tendsto (fun n => P (S n)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := P) (s := S)
      (fun n => nullMeasurableSet_le aemeasurable_const hMm)
      (fun m n hmn ω (hω : (n : ℝ≥0∞) ≤ M ω) => le_trans (by exact_mod_cast hmn) hω)
      ⟨0, measure_ne_top _ _⟩
    have h2 : (⋂ n, S n) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hMfin ω).ne
      exact absurd (mem_iInter.1 hω n) (not_le.2 hn)
    rw [h2, measure_empty] at h1
    exact h1
  -- the two pieces
  set A : ℝ := |a₀| + 1 with hAdef
  have hA : 0 < A := by positivity
  have hfirst := hX R hR (δ / 2 / A) (by positivity)
  have hsecond : Tendsto (fun i => P {ω | ENNReal.ofReal (δ / 2) ≤
      ENNReal.ofReal |a i - a₀| * M ω}) l (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hS η hη)
    have hρ : 0 < δ / 2 / ((N : ℝ) + 1) := by positivity
    filter_upwards [Metric.tendsto_nhds.1 ha _ hρ] with i hi
    refine le_trans (measure_mono fun ω hω => ?_) (hN (N + 1) (Nat.le_succ N))
    simp only [mem_setOf_eq, hSdef] at hω ⊢
    by_contra hlt
    push Not at hlt
    rw [Real.dist_eq] at hi
    have h3 : ENNReal.ofReal |a i - a₀| * M ω <
        ENNReal.ofReal (δ / 2 / ((N : ℝ) + 1)) * ((N + 1 : ℕ) : ℝ≥0∞) :=
      ENNReal.mul_lt_mul (ENNReal.ofReal_lt_ofReal_iff hρ |>.2 hi) hlt
    have h4 : ENNReal.ofReal (δ / 2 / ((N : ℝ) + 1)) * ((N + 1 : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (δ / 2) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hρ.le]
      congr 1
      push_cast
      field_simp
    exact absurd hω (not_le.2 (h4 ▸ h3))
  have hsum := hfirst.add hsecond
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  have hbdd : ∀ᶠ i in l, |a i| ≤ A := by
    filter_upwards [Metric.tendsto_nhds.1 ha 1 one_pos] with i hi
    rw [Real.dist_eq] at hi
    have := abs_sub_abs_le_abs_sub (a i) a₀
    rw [hAdef]; linarith
  filter_upwards [hbdd] with i hi
  refine le_trans (measure_mono fun ω hω => ?_) (measure_union_le _ _)
  simp only [mem_setOf_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hcon
  refine absurd hω (not_le.2 ?_)
  set E := ⨆ p ∈ B, edist (X i ω p) (Y ω p) with hEdef
  calc (⨆ p ∈ B, edist ((a i • X i ω) p) ((a₀ • Y ω) p))
      ≤ ENNReal.ofReal |a i| * E + ENNReal.ofReal |a i - a₀| * M ω := by
        refine iSup₂_le fun p hp => ?_
        refine le_trans (edist_mul_mul_le (a i) a₀ (X i ω p) (Y ω p)) ?_
        gcongr
        · exact le_iSup₂_of_le p hp le_rfl
        · exact le_iSup₂_of_le p hp le_rfl
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
        refine ENNReal.add_lt_add ?_ c2
        calc ENNReal.ofReal |a i| * E ≤ ENNReal.ofReal A * E := by gcongr
            _ < ENNReal.ofReal A * ENNReal.ofReal (δ / 2 / A) :=
              ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.2 hA).ne' ENNReal.ofReal_ne_top c1
            _ = ENNReal.ofReal (δ / 2) := by
              rw [← ENNReal.ofReal_mul hA.le]; congr 1; field_simp
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end GM
end LQGMetric
