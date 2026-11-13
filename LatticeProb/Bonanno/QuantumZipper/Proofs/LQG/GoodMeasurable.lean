/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.GoodMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague

/-!
# M4-R5(a): the good set is measurable

Given regularity (`GoodMeasurableReg`), the existence of the boundary limit (uniformly in the
offset `a ∈ [1,2]`) is equivalent to a countable Cauchy condition (`BdryCert`) for the countable
test family `testFam N m`, `bump N` of `BoundaryVague`, with rational offsets; similarly on `ℍ`
with a countable dense test family (`AreaCert`). The limit measure is produced from the `a = 1`
subsequence by Riesz–Markov (`BoundaryVague`, `AreaExistenceVague`) and the convergence is then
upgraded to the filter `goodFilter` by a `3ε` argument.

Main results: `measurableSet_isLQGGood`, and the global measurability corollaries
`measurable_qBoundaryMeasure_global`, `measurable_qAreaMeasure_global`,
`measurable_scaleParam_global`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace GoodMeas

open BdryVague (testFam bump continuous_testFam hasCompactSupport_testFam continuous_bump
  hasCompactSupport_bump bump_nonneg exists_testFam_approx)
open VagueH (IsTestH IsDenseTestFamily)

/-! ## Generic helpers -/

theorem mprop_imp {X : Type*} [MeasurableSpace X] {P : Prop} {q : X → Prop}
    (h : P → Measurable q) : Measurable fun x => P → q x := by
  by_cases hP : P
  · exact measurable_const.imp (h hP)
  · have e : (fun x => P → q x) = fun _ => True :=
      funext fun x => propext ⟨fun _ => trivial, fun _ hp => absurd hp hP⟩
    rw [e]; exact measurable_const

/-- A bound at rational points of `[1,2]` extends to `[1,2]` by continuity. -/
theorem le_of_rat_Icc {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 1 2)) {c : ℝ}
    (h : ∀ q : ℚ, (1 : ℝ) ≤ q → (q : ℝ) ≤ 2 → φ q ≤ c) {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    φ a ≤ c := by
  set T : Set ℝ := Ioo 1 2 ∩ range ((↑) : ℚ → ℝ) with hTdef
  have hT : T ⊆ Icc 1 2 := fun t ht => Ioo_subset_Icc_self ht.1
  have hcl : a ∈ closure T := by
    have h1 : Ioo (1 : ℝ) 2 ⊆ closure T := Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
    have h2 := closure_mono h1
    rw [closure_Ioo (by norm_num), closure_closure] at h2
    exact h2 ha
  have hmem := ((hφ a ha).mono hT).mem_closure_image hcl
  refine closure_minimal ?_ isClosed_Iic hmem
  rintro _ ⟨t, ⟨⟨ht1, ht2⟩, q, rfl⟩, rfl⟩
  exact h q ht1.le ht2.le

/-- Joint continuity of `(r, v) ↦ evalReg x (fc(v, r))` for a regular sample. -/
theorem continuousOn_evalReg_fc_param {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) :
    ContinuousOn (fun p : ℝ × ℂ => evalReg x (foldedCircle p.2 p.1)) (Ioi 0 ×ˢ univ) := by
  refine ContinuousOn.congr (f := fun p : ℝ × ℂ => F (foldH p.2, p.1)) ?_
    (fun p hp => h.evalReg_fc p.2 hp.1)
  exact h.1.comp ((CircleFubini.continuous_foldH'.comp continuous_snd).prodMk
    continuous_fst).continuousOn (fun p hp => ⟨CircleFubini.foldH_mem_Hbar' _, hp.1⟩)

/-! ## Integrals against `bdryR`, `areaR`: measurability and continuity in the radius -/

theorem gm_measurable_integral_bdryR (γ : ℝ) {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : Measurable f) : Measurable fun x : FieldSample => ∫ t, f t ∂bdryR γ x r := by
  let D : FieldSample × ℝ → ℝ := fun p => bdryDens γ p.1 r p.2
  have hDm : Measurable D :=
    (Real.measurable_exp.comp (((measurable_evalReg_fc_joint r).comp (measurable_fst.prodMk
      (Complex.continuous_ofReal.measurable.comp measurable_snd))).const_mul (γ / 2))).const_mul _
  have hD0 : ∀ p, 0 ≤ D p := fun p => GoodSample.bdryDens_nonneg γ p.1 hr p.2
  have heq : ∀ x : FieldSample, ∫ t, f t ∂bdryR γ x r = ∫ t, D (x, t) * f t := fun x =>
    GoodSample.integral_withDensity_ofReal (hDm.comp (measurable_const.prodMk measurable_id))
      (fun t => hD0 _) f
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (f := fun p : FieldSample × ℝ => D p * f p.2)
    (hDm.mul (hf.comp measurable_snd)).stronglyMeasurable).measurable

theorem gm_measurable_integral_areaR (γ : ℝ) {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hf : Measurable f) : Measurable fun x : FieldSample => ∫ z, f z ∂areaR γ x r := by
  let D : FieldSample × ℂ → ℝ := fun p => areaDens γ p.1 r p.2
  have hDm : Measurable D :=
    (Real.measurable_exp.comp ((measurable_evalReg_fc_joint r).const_mul γ)).const_mul _
  have hD0 : ∀ p, 0 ≤ D p := fun p => GoodSample.areaDens_nonneg γ p.1 hr p.2
  have heq : ∀ x : FieldSample,
      ∫ z, f z ∂areaR γ x r = ∫ z, D (x, z) * f z ∂(volume.restrict H) := fun x =>
    GoodSample.integral_withDensity_ofReal (μ := volume.restrict H)
      (hDm.comp (measurable_const.prodMk measurable_id)) (fun z => hD0 _) f
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (ν := volume.restrict H)
    (f := fun p : FieldSample × ℂ => D p * f p.2)
    (hDm.mul (hf.comp measurable_snd)).stronglyMeasurable).measurable

theorem continuousOn_integral_bdryR {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    ContinuousOn (fun r => ∫ t, g t ∂bdryR γ x r) (Ioi 0) := by
  have hE := continuousOn_evalReg_fc_param h
  have hD : ContinuousOn (fun p : ℝ × ℝ => bdryDens γ x p.1 p.2 * g p.2) (Ioi 0 ×ˢ univ) := by
    have h1 := hE.comp (t := Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) (s := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))
      (f := fun p : ℝ × ℝ => (p.1, (p.2 : ℂ)))
      (continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd)).continuousOn
      (fun p hp => mk_mem_prod hp.1 (mem_univ _))
    simp only [Function.comp_def] at h1
    have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ (γ ^ 2 / 4)) (Ioi 0 ×ˢ univ) :=
      continuousOn_fst.rpow_const (fun p hp => Or.inl (ne_of_gt hp.1))
    exact (h2.mul (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul h1))).mul
      (hg.comp continuous_snd).continuousOn
  have heq : EqOn (fun r => ∫ t, g t ∂bdryR γ x r) (fun r => ∫ t, bdryDens γ x r t * g t)
      (Ioi 0) := fun r hr =>
    GoodSample.integral_withDensity_ofReal (GoodSample.continuous_bdryDens γ h hr).measurable
      (fun t => GoodSample.bdryDens_nonneg γ x hr t) g
  refine ContinuousOn.congr ?_ heq
  exact continuousOn_integral_of_compact_support (k := tsupport g) hgc hD
    (fun p t _ ht => by simp [image_eq_zero_of_notMem_tsupport ht])

theorem continuousOn_integral_areaR {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) {g : ℂ → ℝ} (hg : IsTestH g) :
    ContinuousOn (fun r => ∫ z, g z ∂areaR γ x r) (Ioi 0) := by
  have hE := continuousOn_evalReg_fc_param h
  have hD : ContinuousOn (fun p : ℝ × ℂ => areaDens γ x p.1 p.2 * g p.2) (Ioi 0 ×ˢ univ) := by
    have h2 : ContinuousOn (fun p : ℝ × ℂ => p.1 ^ (γ ^ 2 / 2)) (Ioi 0 ×ˢ univ) :=
      continuousOn_fst.rpow_const (fun p hp => Or.inl (ne_of_gt hp.1))
    exact (h2.mul (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hE))).mul
      (hg.1.comp continuous_snd).continuousOn
  have heq : EqOn (fun r => ∫ z, g z ∂areaR γ x r)
      (fun r => ∫ z, areaDens γ x r z * g z ∂(volume.restrict H)) (Ioi 0) := fun r hr =>
    GoodSample.integral_withDensity_ofReal (μ := volume.restrict H)
      (GoodSample.continuous_areaDens γ h hr).measurable
      (fun z => GoodSample.areaDens_nonneg γ x hr z) g
  refine ContinuousOn.congr ?_ heq
  exact continuousOn_integral_of_compact_support (μ := volume.restrict H) (k := tsupport g)
    hg.2.1 hD (fun p z _ hz => by simp [image_eq_zero_of_notMem_tsupport hz])

/-! ## Upgrading convergence on a countable family, along an arbitrary filter -/

theorem abs_integral_sub_testFam_le {μ : Measure ℝ} [IsFiniteMeasureOnCompacts μ] {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) {N m : ℕ} {η : ℝ}
    (hm : ∀ x, |f x - testFam N m x| ≤ η * bump N x) :
    |∫ t, f t ∂μ - ∫ t, testFam N m t ∂μ| ≤ η * ∫ t, bump N t ∂μ := by
  have hi1 : Integrable f μ := hf.integrable_of_hasCompactSupport hcs
  have hi2 : Integrable (testFam N m) μ :=
    (continuous_testFam N m).integrable_of_hasCompactSupport (hasCompactSupport_testFam N m)
  have hi3 : Integrable (bump N) μ :=
    (continuous_bump N).integrable_of_hasCompactSupport (hasCompactSupport_bump N)
  rw [← integral_sub hi1 hi2, ← integral_const_mul]
  have := norm_integral_le_of_norm_le (f := fun x => f x - testFam N m x) (hi3.const_mul η)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hm x)
  rwa [Real.norm_eq_abs] at this

theorem tendsto_of_testFam_filter {ι : Type*} {L : Filter ι} {νs : ι → Measure ℝ}
    {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    (hfin : ∀ᶠ i in L, IsFiniteMeasureOnCompacts (νs i))
    (hconv : ∀ N m, Tendsto (fun i => ∫ t, testFam N m t ∂νs i) L (𝓝 (∫ t, testFam N m t ∂ν)))
    (hbump : ∀ N, Tendsto (fun i => ∫ t, bump N t ∂νs i) L (𝓝 (∫ t, bump N t ∂ν)))
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Tendsto (fun i => ∫ t, f t ∂νs i) L (𝓝 (∫ t, f t ∂ν)) := by
  obtain ⟨N, hN⟩ := exists_testFam_approx hf hcs
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B := ∫ t, bump N t ∂ν + 1 with hBdef
  have hbν : 0 ≤ ∫ t, bump N t ∂ν := integral_nonneg (bump_nonneg N)
  have hB0 : 0 < B := by linarith
  obtain ⟨m, hm⟩ := hN (ε / (3 * B)) (by positivity)
  have hν := abs_integral_sub_testFam_le (μ := ν) hf hcs hm
  have hbB : ∀ᶠ i in L, ∫ t, bump N t ∂νs i < B := (hbump N).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hfin, hbB, Metric.tendsto_nhds.1 (hconv N m) (ε / 3) (by positivity)]
    with i hi hiB hic
  have := hi
  have hνi := abs_integral_sub_testFam_le (μ := νs i) hf hcs hm
  have hb0 : 0 ≤ ∫ t, bump N t ∂νs i := integral_nonneg (bump_nonneg N)
  have e1 : ε / (3 * B) * ∫ t, bump N t ∂νs i ≤ ε / 3 :=
    calc ε / (3 * B) * ∫ t, bump N t ∂νs i ≤ ε / (3 * B) * B :=
          mul_le_mul_of_nonneg_left hiB.le (by positivity)
      _ = ε / 3 := by field_simp
  have e2 : ε / (3 * B) * ∫ t, bump N t ∂ν ≤ ε / 3 :=
    calc ε / (3 * B) * ∫ t, bump N t ∂ν ≤ ε / (3 * B) * B :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  rw [Real.dist_eq] at hic ⊢
  rw [abs_le] at hνi hν
  rw [abs_lt] at hic ⊢
  constructor <;> linarith

theorem abs_integral_sub_le_H {ν : Measure ℂ} {f g φ : ℂ → ℝ} {K : Set ℂ} (hf : IsTestH f)
    (hg : IsTestH g) (hφ : IsTestH φ) (hfK : tsupport f ⊆ K) (hgK : tsupport g ⊆ K)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z ∈ K, 1 ≤ φ z) {η : ℝ} (hη : 0 ≤ η)
    (hfg : ∀ z, |f z - g z| ≤ η) (hK : ν K < ⊤) (hφν : ν (tsupport φ) < ⊤) :
    |∫ z, f z ∂ν - ∫ z, g z ∂ν| ≤ η * ∫ z, φ z ∂ν := by
  have hif : Integrable f ν := hf.integrable ((measure_mono hfK).trans_lt hK)
  have hig : Integrable g ν := hg.integrable ((measure_mono hgK).trans_lt hK)
  have hiφ : Integrable φ ν := hφ.integrable hφν
  have hpt : ∀ z, |f z - g z| ≤ η * φ z := by
    intro z
    by_cases hz : z ∈ K
    · calc |f z - g z| ≤ η := hfg z
        _ = η * 1 := (mul_one η).symm
        _ ≤ η * φ z := mul_le_mul_of_nonneg_left (hφ1 z hz) hη
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
      exact mul_nonneg hη (hφ0 z)
  calc |∫ z, f z ∂ν - ∫ z, g z ∂ν| = |∫ z, (f z - g z) ∂ν| := by rw [integral_sub hif hig]
    _ ≤ ∫ z, |f z - g z| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ z, η * φ z ∂ν := integral_mono (hif.sub hig).abs (hiφ.const_mul η) hpt
    _ = η * ∫ z, φ z ∂ν := integral_const_mul _ _

theorem tendsto_of_denseFamily_filter {ι : Type*} {L : Filter ι} {μs : ι → Measure ℂ}
    {μ : Measure ℂ} (hμ : ∀ K, IsCompact K → K ⊆ H → μ K < ⊤)
    (hfin : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ i in L, μs i K < ⊤) {F : Set (ℂ → ℝ)}
    (hF : IsDenseTestFamily F)
    (hconv : ∀ g ∈ F, Tendsto (fun i => ∫ z, g z ∂μs i) L (𝓝 (∫ z, g z ∂μ)))
    (f : ℂ → ℝ) (hf : IsTestH f) : Tendsto (fun i => ∫ z, f z ∂μs i) L (𝓝 (∫ z, f z ∂μ)) := by
  obtain ⟨K, hK, hKH, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ := hF.2 f hf
  have hφ := hF.1 φ hφF
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B := ∫ z, φ z ∂μ + 1 with hBdef
  have hb0' : 0 ≤ ∫ z, φ z ∂μ := integral_nonneg hφ0
  have hB0 : 0 < B := by linarith
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox (ε / (3 * B)) (by positivity)
  have hg := hF.1 g hgF
  have hμb := abs_integral_sub_le_H hf hg hφ hfK hgK hφ0 hφ1 (by positivity) hfg (hμ K hK hKH)
    (hμ _ hφ.2.1 hφ.2.2)
  have hbB : ∀ᶠ i in L, ∫ z, φ z ∂μs i < B :=
    (hconv φ hφF).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hfin K hK hKH, hfin _ hφ.2.1 hφ.2.2, hbB,
    Metric.tendsto_nhds.1 (hconv g hgF) (ε / 3) (by positivity)] with i hiK hiφ hiB hic
  have hib := abs_integral_sub_le_H hf hg hφ hfK hgK hφ0 hφ1 (by positivity) hfg hiK hiφ
  have hb0 : 0 ≤ ∫ z, φ z ∂μs i := integral_nonneg hφ0
  have e1 : ε / (3 * B) * ∫ z, φ z ∂μs i ≤ ε / 3 :=
    calc ε / (3 * B) * ∫ z, φ z ∂μs i ≤ ε / (3 * B) * B :=
          mul_le_mul_of_nonneg_left hiB.le (by positivity)
      _ = ε / 3 := by field_simp
  have e2 : ε / (3 * B) * ∫ z, φ z ∂μ ≤ ε / 3 :=
    calc ε / (3 * B) * ∫ z, φ z ∂μ ≤ ε / (3 * B) * B :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  rw [Real.dist_eq] at hic ⊢
  rw [abs_le] at hib hμb
  rw [abs_lt] at hic ⊢
  constructor <;> linarith

/-! ## The boundary certificate -/

/-- `∫ g dν_{a 2^{-k}}(x)`. -/
def bI (γ : ℝ) (g : ℝ → ℝ) (x : FieldSample) (k : ℕ) (a : ℝ) : ℝ :=
  ∫ t, g t ∂bdryR γ x (a * radius k)

/-- Uniform Cauchy condition along `goodFilter`, tested at rational offsets. -/
def CauchyB (γ : ℝ) (g : ℝ → ℝ) (x : FieldSample) : Prop :=
  ∀ e : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ k' : ℕ, K ≤ k' → ∀ q : ℚ, (1 : ℝ) ≤ q → (q : ℝ) ≤ 2 →
    |bI γ g x k q - bI γ g x k' 1| ≤ 1 / ((e : ℝ) + 1)

/-- The countable boundary certificate. -/
def BdryCert (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ N m : ℕ, CauchyB γ (testFam N m) x) ∧ ∀ N : ℕ, CauchyB γ (bump N) x

theorem measurable_CauchyB (γ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) : Measurable (CauchyB γ g) := by
  unfold CauchyB
  refine Measurable.forall fun e => Measurable.exists fun K => Measurable.forall fun k =>
    measurable_const.imp (Measurable.forall fun k' => measurable_const.imp
      (Measurable.forall fun q => mprop_imp fun hq1 => measurable_const.imp ?_))
  exact mprop_abs_le (gm_measurable_integral_bdryR γ (mul_pos (by linarith) (radius_pos k)) hg)
    (gm_measurable_integral_bdryR γ (mul_pos one_pos (radius_pos k')) hg) _

theorem measurable_BdryCert (γ : ℝ) : Measurable (BdryCert γ) :=
  (Measurable.forall fun N => Measurable.forall fun m =>
    measurable_CauchyB γ (continuous_testFam N m).measurable).and
    (Measurable.forall fun N => measurable_CauchyB γ (continuous_bump N).measurable)

theorem cauchyB_of_tendsto {γ : ℝ} {x : FieldSample} {g : ℝ → ℝ} {l : ℝ}
    (ht : Tendsto (fun i => ∫ t, g t ∂bdryR γ x (goodRad i)) goodFilter (𝓝 l)) :
    CauchyB γ g x := by
  intro e
  have hev := (Metric.tendsto_nhds.1 ht) (1 / ((e : ℝ) + 1) / 2) (by positivity)
  rw [goodFilter, eventually_prod_principal_iff] at hev
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun k hk k' hk' q hq1 hq2 => ?_⟩
  have h1 := hK k hk q ⟨hq1, hq2⟩
  have h2 := hK k' hk' 1 ⟨le_rfl, one_le_two⟩
  simp only [goodRad] at h1 h2
  simp only [bI]
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [abs_le]
  constructor <;> linarith

theorem bdryCert_of_hasBdryLimit {γ : ℝ} {x : FieldSample} {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) : BdryCert γ x :=
  ⟨fun N m => cauchyB_of_tendsto (hν.2 _ (continuous_testFam N m) (hasCompactSupport_testFam N m)),
    fun N => cauchyB_of_tendsto (hν.2 _ (continuous_bump N) (hasCompactSupport_bump N))⟩

theorem tendsto_goodFilter_of_cauchyB {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hC : CauchyB γ g x) :
    ∃ l, Tendsto (fun i => ∫ t, g t ∂bdryR γ x (goodRad i)) goodFilter (𝓝 l) := by
  have hcont : ∀ k : ℕ, ContinuousOn (fun a => bI γ g x k a) (Icc 1 2) := fun k =>
    (continuousOn_integral_bdryR h hg hgc).comp (continuous_id.mul continuous_const).continuousOn
      (fun a ha => mul_pos (by linarith [ha.1]) (radius_pos k))
  have hR : ∀ e : ℕ, ∃ K : ℕ, ∀ k ≥ K, ∀ k' ≥ K, ∀ a ∈ Icc (1 : ℝ) 2,
      |bI γ g x k a - bI γ g x k' 1| ≤ 1 / ((e : ℝ) + 1) := by
    intro e
    obtain ⟨K, hK⟩ := hC e
    exact ⟨K, fun k hk k' hk' a ha => le_of_rat_Icc
      (φ := fun a => |bI γ g x k a - bI γ g x k' 1|)
      (continuous_abs.comp_continuousOn ((hcont k).sub continuousOn_const))
      (fun q hq1 hq2 => hK k hk k' hk' q hq1 hq2) ha⟩
  obtain ⟨l, hl⟩ : ∃ l, Tendsto (fun k => bI γ g x k 1) atTop (𝓝 l) := by
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨K, hK⟩ := hR e
    exact ⟨K, fun k hk k' hk' => by
      rw [Real.dist_eq]; exact (hK k hk k' hk' 1 ⟨le_rfl, one_le_two⟩).trans_lt he⟩
  refine ⟨l, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := hR e
  rw [goodFilter, eventually_prod_principal_iff]
  refine eventually_atTop.2 ⟨K, fun k hk a ha => ?_⟩
  have hle : |bI γ g x k a - l| ≤ 1 / ((e : ℝ) + 1) :=
    le_of_tendsto ((tendsto_const_nhds.sub hl).abs :
      Tendsto (fun k' => |bI γ g x k a - bI γ g x k' 1|) atTop _)
      (eventually_atTop.2 ⟨K, fun k' hk' => hK k hk k' hk' a ha⟩)
  rw [Real.dist_eq]
  exact hle.trans_lt he

theorem hasBdryLimit_of_cert {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    (hc : BdryCert γ x) : ∃ ν, HasBdryLimit γ x ν := by
  have hpos : ∀ k : ℕ, 0 < goodRad (k, 1) := fun k => mul_pos one_pos (radius_pos k)
  have hfin : ∀ k : ℕ, IsFiniteMeasureOnCompacts (bdryR γ x (goodRad (k, 1))) := fun k =>
    ⟨fun K hK => GoodSample.bdryR_lt_top γ h (hpos k) hK⟩
  choose lT hlT using fun N m => tendsto_goodFilter_of_cauchyB h (continuous_testFam N m)
    (hasCompactSupport_testFam N m) (hc.1 N m)
  choose lB hlB using fun N => tendsto_goodFilter_of_cauchyB h (continuous_bump N)
    (hasCompactSupport_bump N) (hc.2 N)
  obtain ⟨ν, hν⟩ := BdryVague.exists_isVagueLimitR_of_testFam
    (νs := fun k => bdryR γ x (goodRad (k, 1))) hfin
    (fun N m => ⟨_, (hlT N m).comp GoodSample.tendsto_one_goodFilter⟩)
    (fun N => ⟨_, (hlB N).comp GoodSample.tendsto_one_goodFilter⟩)
  have hT : ∀ N m, lT N m = ∫ t, testFam N m t ∂ν := fun N m =>
    tendsto_nhds_unique ((hlT N m).comp GoodSample.tendsto_one_goodFilter)
      (hν.2 _ (continuous_testFam N m) (hasCompactSupport_testFam N m))
  have hB : ∀ N, lB N = ∫ t, bump N t ∂ν := fun N =>
    tendsto_nhds_unique ((hlB N).comp GoodSample.tendsto_one_goodFilter)
      (hν.2 _ (continuous_bump N) (hasCompactSupport_bump N))
  have := hν.1
  refine ⟨ν, hν.1, fun f hf hfc => ?_⟩
  refine tendsto_of_testFam_filter (GoodSample.eventually_goodRad_pos.mono fun i hi =>
    ⟨fun K hK => GoodSample.bdryR_lt_top γ h hi hK⟩) (fun N m => ?_) (fun N => ?_) hf hfc
  · rw [← hT N m]; exact hlT N m
  · rw [← hB N]; exact hlB N

theorem exists_hasBdryLimit_iff {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) : (∃ ν, HasBdryLimit γ x ν) ↔ BdryCert γ x :=
  ⟨fun ⟨_, hν⟩ => bdryCert_of_hasBdryLimit hν, hasBdryLimit_of_cert h⟩

/-! ## The area certificate -/

/-- A fixed countable dense test family on `ℍ`. -/
def denseFam : Set (ℂ → ℝ) := Classical.choose VagueH.exists_denseTestFamily

theorem denseFam_countable : denseFam.Countable :=
  (Classical.choose_spec VagueH.exists_denseTestFamily).1

theorem denseFam_dense : IsDenseTestFamily denseFam :=
  (Classical.choose_spec VagueH.exists_denseTestFamily).2

/-- `∫ g dμ_{a 2^{-k}}(x)`. -/
def aI (γ : ℝ) (g : ℂ → ℝ) (x : FieldSample) (k : ℕ) (a : ℝ) : ℝ :=
  ∫ z, g z ∂areaR γ x (a * radius k)

def CauchyA (γ : ℝ) (g : ℂ → ℝ) (x : FieldSample) : Prop :=
  ∀ e : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ k' : ℕ, K ≤ k' → ∀ q : ℚ, (1 : ℝ) ≤ q → (q : ℝ) ≤ 2 →
    |aI γ g x k q - aI γ g x k' 1| ≤ 1 / ((e : ℝ) + 1)

/-- The countable area certificate. -/
def AreaCert (γ : ℝ) (x : FieldSample) : Prop := ∀ g : denseFam, CauchyA γ g.1 x

theorem measurable_CauchyA (γ : ℝ) {g : ℂ → ℝ} (hg : Measurable g) : Measurable (CauchyA γ g) := by
  unfold CauchyA
  refine Measurable.forall fun e => Measurable.exists fun K => Measurable.forall fun k =>
    measurable_const.imp (Measurable.forall fun k' => measurable_const.imp
      (Measurable.forall fun q => mprop_imp fun hq1 => measurable_const.imp ?_))
  exact mprop_abs_le (gm_measurable_integral_areaR γ (mul_pos (by linarith) (radius_pos k)) hg)
    (gm_measurable_integral_areaR γ (mul_pos one_pos (radius_pos k')) hg) _

theorem measurable_AreaCert (γ : ℝ) : Measurable (AreaCert γ) := by
  have : Countable denseFam := denseFam_countable.to_subtype
  unfold AreaCert
  exact Measurable.forall fun g => measurable_CauchyA γ (denseFam_dense.1 g.1 g.2).1.measurable

theorem cauchyA_of_tendsto {γ : ℝ} {x : FieldSample} {g : ℂ → ℝ} {l : ℝ}
    (ht : Tendsto (fun i => ∫ z, g z ∂areaR γ x (goodRad i)) goodFilter (𝓝 l)) :
    CauchyA γ g x := by
  intro e
  have hev := (Metric.tendsto_nhds.1 ht) (1 / ((e : ℝ) + 1) / 2) (by positivity)
  rw [goodFilter, eventually_prod_principal_iff] at hev
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun k hk k' hk' q hq1 hq2 => ?_⟩
  have h1 := hK k hk q ⟨hq1, hq2⟩
  have h2 := hK k' hk' 1 ⟨le_rfl, one_le_two⟩
  simp only [goodRad] at h1 h2
  simp only [aI]
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [abs_le]
  constructor <;> linarith

theorem areaCert_of_hasAreaLimit {γ : ℝ} {x : FieldSample} {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) : AreaCert γ x := fun g =>
  have hg := denseFam_dense.1 g.1 g.2
  cauchyA_of_tendsto (hμ.2.2 _ hg.1 hg.2.1 hg.2.2)

theorem tendsto_goodFilter_of_cauchyA {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) {g : ℂ → ℝ} (hg : IsTestH g) (hC : CauchyA γ g x) :
    ∃ l, Tendsto (fun i => ∫ z, g z ∂areaR γ x (goodRad i)) goodFilter (𝓝 l) := by
  have hcont : ∀ k : ℕ, ContinuousOn (fun a => aI γ g x k a) (Icc 1 2) := fun k =>
    (continuousOn_integral_areaR h hg).comp (continuous_id.mul continuous_const).continuousOn
      (fun a ha => mul_pos (by linarith [ha.1]) (radius_pos k))
  have hR : ∀ e : ℕ, ∃ K : ℕ, ∀ k ≥ K, ∀ k' ≥ K, ∀ a ∈ Icc (1 : ℝ) 2,
      |aI γ g x k a - aI γ g x k' 1| ≤ 1 / ((e : ℝ) + 1) := by
    intro e
    obtain ⟨K, hK⟩ := hC e
    exact ⟨K, fun k hk k' hk' a ha => le_of_rat_Icc
      (φ := fun a => |aI γ g x k a - aI γ g x k' 1|)
      (continuous_abs.comp_continuousOn ((hcont k).sub continuousOn_const))
      (fun q hq1 hq2 => hK k hk k' hk' q hq1 hq2) ha⟩
  obtain ⟨l, hl⟩ : ∃ l, Tendsto (fun k => aI γ g x k 1) atTop (𝓝 l) := by
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨K, hK⟩ := hR e
    exact ⟨K, fun k hk k' hk' => by
      rw [Real.dist_eq]; exact (hK k hk k' hk' 1 ⟨le_rfl, one_le_two⟩).trans_lt he⟩
  refine ⟨l, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := hR e
  rw [goodFilter, eventually_prod_principal_iff]
  refine eventually_atTop.2 ⟨K, fun k hk a ha => ?_⟩
  have hle : |aI γ g x k a - l| ≤ 1 / ((e : ℝ) + 1) :=
    le_of_tendsto ((tendsto_const_nhds.sub hl).abs :
      Tendsto (fun k' => |aI γ g x k a - aI γ g x k' 1|) atTop _)
      (eventually_atTop.2 ⟨K, fun k' hk' => hK k hk k' hk' a ha⟩)
  rw [Real.dist_eq]
  exact hle.trans_lt he

theorem hasAreaLimit_of_cert {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    (hc : AreaCert γ x) : ∃ μ, HasAreaLimit γ x μ := by
  have hpos : ∀ k : ℕ, 0 < goodRad (k, 1) := fun k => mul_pos one_pos (radius_pos k)
  have hfinK : ∀ K, IsCompact K → K ⊆ H →
      ∀ᶠ k in atTop, areaR γ x (goodRad (k, 1)) K < ⊤ := fun K hK _ =>
    Eventually.of_forall fun k => GoodSample.areaR_lt_top γ h (hpos k) hK
  have hl : ∀ g ∈ denseFam, ∃ l,
      Tendsto (fun i => ∫ z, g z ∂areaR γ x (goodRad i)) goodFilter (𝓝 l) := fun g hg =>
    tendsto_goodFilter_of_cauchyA h (denseFam_dense.1 g hg) (hc ⟨g, hg⟩)
  choose! lA hlA using hl
  obtain ⟨μ, hμ⟩ := VagueH.exists_isVagueLimitOn_of_family
    (μs := fun k => areaR γ x (goodRad (k, 1))) hfinK denseFam_dense
    (fun g hg => ⟨_, (hlA g hg).comp GoodSample.tendsto_one_goodFilter⟩)
  have hA : ∀ g ∈ denseFam, lA g = ∫ z, g z ∂μ := fun g hg =>
    have hgt := denseFam_dense.1 g hg
    tendsto_nhds_unique ((hlA g hg).comp GoodSample.tendsto_one_goodFilter)
      (hμ.2.2 g hgt.1 hgt.2.1 hgt.2.2)
  refine ⟨μ, hμ.1, hμ.2.1, fun f hf hfc hfH => ?_⟩
  refine tendsto_of_denseFamily_filter hμ.2.1 (fun K hK _ =>
    GoodSample.eventually_goodRad_pos.mono fun i hi => GoodSample.areaR_lt_top γ h hi hK)
    denseFam_dense (fun g hg => ?_) f ⟨hf, hfc, hfH⟩
  rw [← hA g hg]
  exact hlA g hg

theorem exists_hasAreaLimit_iff {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) : (∃ μ, HasAreaLimit γ x μ) ↔ AreaCert γ x :=
  ⟨fun ⟨_, hμ⟩ => areaCert_of_hasAreaLimit hμ, hasAreaLimit_of_cert h⟩

/-! ## Main theorem and global measurability -/

theorem isLQGGood_iff_cert (γ : ℝ) (x : FieldSample) :
    IsLQGGood γ x ↔ IsRegularSample x ∧ BdryCert γ x ∧ AreaCert γ x := by
  constructor
  · rintro ⟨⟨F, hF⟩, hb, ha⟩
    exact ⟨⟨F, hF⟩, (exists_hasBdryLimit_iff hF).1 hb, (exists_hasAreaLimit_iff hF).1 ha⟩
  · rintro ⟨⟨F, hF⟩, hb, ha⟩
    exact ⟨⟨F, hF⟩, (exists_hasBdryLimit_iff hF).2 hb, (exists_hasAreaLimit_iff hF).2 ha⟩

/-- **M4-R5(a).** The set of good samples is measurable. -/
theorem measurableSet_isLQGGood (γ : ℝ) : MeasurableSet {x : FieldSample | IsLQGGood γ x} := by
  have e : {x : FieldSample | IsLQGGood γ x} =
      {x | IsRegularSample x} ∩ ({x | BdryCert γ x} ∩ {x | AreaCert γ x}) := by
    ext x; exact isLQGGood_iff_cert γ x
  rw [e]
  exact measurableSet_isRegularSample.inter ((measurableSet_setOfPred.2 (measurable_BdryCert γ)).inter
    (measurableSet_setOfPred.2 (measurable_AreaCert γ)))

open Classical in
theorem measurable_qBoundaryMeasure_global (γ : ℝ) :
    Measurable fun x => if IsLQGGood γ x then qBoundaryMeasure γ x else 0 :=
  LQGMeas.measurable_qBoundaryMeasure_of_measurableSet γ (measurableSet_isLQGGood γ)

open Classical in
theorem measurable_qAreaMeasure_global (γ : ℝ) :
    Measurable fun x => if IsLQGGood γ x then qAreaMeasure γ x else 0 :=
  LQGMeas.measurable_qAreaMeasure_of_measurableSet γ (measurableSet_isLQGGood γ)

open Classical in
theorem measurable_scaleParam_global (γ : ℝ) :
    Measurable fun x => if IsLQGGood γ x then scaleParam γ x else 0 :=
  LQGMeas.measurable_scaleParam_of_measurableSet γ (measurableSet_isLQGGood γ)

end GoodMeas

end QuantumZipper
