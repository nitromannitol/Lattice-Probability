/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112M4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L3
import LatticeProb.Bonanno.LQGMetric.Field.HarmExistB
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `σ((h − h_ρ(w))|_K) = σ(h|_K mod constants)` up to null sets (for `CONFHarmPartLink`)

The mod-constant version of `GM.measurable_circleAvg_fieldSigmaClosed` (handoff/P2-CONF33G.md
item 2): for `∂B_ρ(w) ⊆ K`, every set of `recSigma h ρ w K = σ((h − h_ρ(w))|_K)` agrees, off the
`P`-null set `N` where the mollified circle averages `h(circBump n w ρ)` do not converge, with a
set of `fieldSigmaClosed0 h K = σ(h|_K mod constants)` (`inter_compl_mem_fieldSigmaClosed0`).
Hence every `recSigma`-measurable real function is `fieldSigmaClosed0`-a.e. strongly measurable
(`aestronglyMeasurable_fieldSigmaClosed0_of_recSigma`).

Proof (own elementary argument, as `GM.measurable_circleAvg_fieldSigma`): on `Nᶜ`,
`h_ρ(w) = h(β) + lim_n h(circBump (n + N_ε) w ρ − β)` with `β = circBump N_ε w ρ` supported in
the `ε`-thickening of `∂B_ρ(w)`; the right side is a limit of mean-zero pairings, and
`(h − h_ρ(w))(ψ) = h(ψ − (∫ψ)β) − (∫ψ)·lim_n …`. The a.s. convergence is
`CircleAvg.ae_tendsto_mollAvg_of_logCov_le`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal Topology

namespace LQGMetric.CONF

open Blueprint CircleAvg

lemma circBump_eq_zero_of {n : ℕ} {w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) {y : ℂ}
    (hy : y ∉ cthickening ((2 : ℝ)⁻¹ ^ n) (sphere w ρ)) : circBump n w ρ y = 0 := by
  rw [circBump_apply]
  have : ∀ θ, bumpTest n (circleMap w ρ θ) y = 0 := by
    intro θ
    rw [bumpTest_apply, ContDiffBump.normed_def, (bumpAt n _).zero_of_le_dist, zero_div]
    show (2 : ℝ)⁻¹ ^ n ≤ dist y (circleMap w ρ θ)
    by_contra hlt
    exact hy (mem_cthickening_of_dist_le y (circleMap w ρ θ) _ _
      (circleMap_mem_sphere w hρ θ) (not_le.1 hlt).le)
  simp [Real.circleAverage_def, this]

lemma tsupport_circBump_subset' (n : ℕ) (w : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    tsupport (circBump n w ρ : ℂ → ℝ) ⊆ cthickening ((2 : ℝ)⁻¹ ^ n) (sphere w ρ) :=
  closure_minimal (fun _ hy => by_contra fun h' => hy (circBump_eq_zero_of hρ h'))
    isClosed_cthickening

/-- a mean-zero pairing supported in `V` is `σ(h|_V mod constants)`-measurable -/
lemma measurable_pair_fieldSigma0On {Ω : Type} (h : Ω → DistC) {V : Set ℂ} (θ : TestC)
    (hθ : ∫ x, θ x = 0) (hθV : tsupport (θ : ℂ → ℝ) ⊆ V) :
    Measurable[fieldSigma0On h V] fun ω => h ω θ := by
  let F : Ω → ({ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V} → ℝ) := fun ω ψ => h ω ψ.1.1
  have hF : Measurable[MeasurableSpace.comap F MeasurableSpace.pi] F := comap_measurable F
  exact (measurable_pi_apply (⟨⟨θ, hθ⟩, hθV⟩ :
    {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V})).comp hF

lemma tsupport_sub_smul_subset {V : Set ℂ} {φ β : TestC} (c : ℝ)
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ V) (hβ : tsupport (β : ℂ → ℝ) ⊆ V) :
    tsupport ((φ - c • β : TestC) : ℂ → ℝ) ⊆ V := by
  have e : ((φ - c • β : TestC) : ℂ → ℝ) = fun x => φ x - (fun _ => c) x * β x := by
    ext x; simp
  rw [e]
  exact (tsupport_sub _ _).trans (union_subset hφ ((tsupport_mul_subset_right).trans hβ))

lemma integral_sub_smul_unit {φ β : TestC} (hβ : ∫ x, β x = 1) :
    ∫ x, (φ - (∫ x, φ x) • β : TestC) x = 0 := by
  have e : ((φ - (∫ x, φ x) • β : TestC) : ℂ → ℝ) = fun x => φ x - (∫ x, φ x) * β x := by
    ext x; simp
  rw [e, integral_sub (GM.gm_integrable_testC φ) ((GM.gm_integrable_testC β).const_mul _),
    integral_const_mul, hβ, mul_one, sub_self]

variable {Ω : Type} [MeasurableSpace Ω]

/-- the non-convergence set of the mollified circle averages `h(circBump n w ρ)` -/
def circNC (h : Ω → DistC) (ρ : ℝ) (w : ℂ) : Set Ω :=
  {ω | ¬ ∃ a, Tendsto (fun n => mollAvg (h ω) n w ρ) atTop (𝓝 a)}

lemma measure_circNC {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ρ : ℝ}
    (hρ : 0 < ρ) (w : ℂ) : P (circNC h ρ w) = 0 :=
  ae_iff.1 (ae_tendsto_mollAvg_of_logCov_le hh w ρ (C := 4 / ρ) (q := 2⁻¹) (by norm_num)
    (by norm_num) (logCov_circDiff_succ_le hρ w))

/-- the index from which `circBump n w ρ` is supported in the `ε`-thickening of `K ⊇ ∂B_ρ(w)` -/
lemma exists_circBump_supp {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) {K : Set ℂ} (hK : sphere w ρ ⊆ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → tsupport (circBump n w ρ : ℂ → ℝ) ⊆ thickening ε K := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun n hn => (tsupport_circBump_subset' n w hρ.le).trans ?_⟩
  refine (cthickening_subset_thickening' hε ?_ _).trans (thickening_subset_of_subset ε hK)
  calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ < ε := hN

/-- the key step at one thickening -/
lemma inter_compl_mem_fieldSigma0On {h : Ω → DistC} {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) {K : Set ℂ}
    (hK : sphere w ρ ⊆ K) {ε : ℝ} (hε : 0 < ε) {S : Set Ω}
    (hS : MeasurableSet[fieldSigma (CONF.recField h ρ w) (nbhdO ε K)] S) :
    MeasurableSet[fieldSigma0On h (thickening ε K)] (S ∩ (circNC h ρ w)ᶜ) ∧
      MeasurableSet[fieldSigma0On h (thickening ε K)] (circNC h ρ w) := by
  set m0 := fieldSigma0On h (thickening ε K)
  obtain ⟨N, hN⟩ := exists_circBump_supp hρ w hK hε
  set β : TestC := circBump N w ρ
  have hβ1 : ∫ x, β x = 1 := integral_circBump N w ρ
  have hβV : tsupport (β : ℂ → ℝ) ⊆ thickening ε K := hN N le_rfl
  -- the shifted mean-zero sequence
  set Y : ℕ → Ω → ℝ := fun n ω => h ω (circBump (n + N) w ρ - β)
  have hY : ∀ n, Measurable[m0] (Y n) := fun n => by
    refine measurable_pair_fieldSigma0On h _ ?_ ?_
    · have e : ((circBump (n + N) w ρ - β : TestC) : ℂ → ℝ) =
          fun x => circBump (n + N) w ρ x - β x := by ext x; simp
      rw [e, integral_sub (GM.gm_integrable_testC _) (GM.gm_integrable_testC _),
        integral_circBump, hβ1, sub_self]
    · have := tsupport_sub_smul_subset (V := thickening ε K) 1
        (hN (n + N) (Nat.le_add_left N n)) hβV
      simpa using this
  have hYm : ∀ ω, ∀ n, Y n ω = mollAvg (h ω) (n + N) w ρ - h ω β := fun ω n => by
    simp only [Y, map_sub, mollAvg_eq]
  set M : Ω → ℝ := fun ω => limUnder atTop fun n => Y n ω
  have hM : Measurable[m0] M :=
    (StronglyMeasurable.limUnder (l := atTop) fun n => (hY n).stronglyMeasurable).measurable
  -- the non-convergence set
  have hNC : circNC h ρ w = {ω | ∃ a, Tendsto (fun n => Y n ω) atTop (𝓝 a)}ᶜ := by
    ext ω
    simp only [circNC, mem_ofPred_eq, mem_compl_iff, hYm]
    refine not_congr ⟨fun ⟨a, ha⟩ => ⟨a - h ω β, ?_⟩, fun ⟨a, ha⟩ => ⟨a + h ω β, ?_⟩⟩
    · exact ((tendsto_add_atTop_iff_nat N).2 ha).sub_const _
    · have := ha.add_const (h ω β)
      simp only [sub_add_cancel] at this
      exact (tendsto_add_atTop_iff_nat N).1 this
  have hNCm : MeasurableSet[m0] (circNC h ρ w) := by
    rw [hNC]
    exact (measurableSet_exists_tendsto fun n => hY n).compl
  refine ⟨?_, hNCm⟩
  -- the modified restriction map
  obtain ⟨B, hB, rfl⟩ := hS
  set Φ' : Ω → DistOn (nbhdO ε K) := fun ω =>
    restrictTo (nbhdO ε K) (addConst (h ω) (-(h ω β + M ω)))
  have hΦ' : Measurable[m0] Φ' := by
    refine measurable_distOn_iff.2 fun ψ => ?_
    set ψc : TestC := MarkovGerm.extC (nbhdO ε K) ψ
    have hψc : tsupport (ψc : ℂ → ℝ) ⊆ thickening ε K := by
      rw [MarkovGerm.coe_extC]; exact ψ.tsupport_subset
    have e : (fun ω => Φ' ω ψ) = fun ω =>
        h ω (ψc - (∫ x, ψc x) • β) - (∫ x, ψc x) * M ω := by
      funext ω
      show addConst (h ω) (-(h ω β + M ω)) ψc = _
      rw [GFFInv.addConst_apply, map_sub, map_smul, smul_eq_mul]
      ring
    rw [e]
    exact (measurable_pair_fieldSigma0On h _ (integral_sub_smul_unit hβ1)
      (tsupport_sub_smul_subset _ hψc hβV)).sub (hM.const_mul _)
  have hEq : ∀ ω ∉ circNC h ρ w,
      restrictTo (nbhdO ε K) (CONF.recField h ρ w ω) = Φ' ω := by
    intro ω hω
    simp only [circNC, mem_ofPred_eq, not_not] at hω
    obtain ⟨a, ha⟩ := hω
    have hc : circleAvg (h ω) ρ w = a := circleAvg_eq_of_tendsto ha
    have hYt : Tendsto (fun n => Y n ω) atTop (𝓝 (a - h ω β)) := by
      simp only [hYm]
      exact ((tendsto_add_atTop_iff_nat N).2 ha).sub_const _
    have hMω : M ω = a - h ω β := hYt.limUnder_eq
    show restrictTo _ (addConst (h ω) (-circleAvg (h ω) ρ w)) = _
    simp only [Φ', hMω, hc, add_sub_cancel]
  have e : (fun ω => restrictTo (nbhdO ε K) (CONF.recField h ρ w ω)) ⁻¹' B ∩
      (circNC h ρ w)ᶜ = Φ' ⁻¹' B ∩ (circNC h ρ w)ᶜ := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hEq ω h2 ▸ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hEq ω h2).symm ▸ h1, h2⟩
  rw [e]
  exact (hΦ' hB).inter hNCm.compl

/-- **`σ((h − h_ρ(w))|_K) ⊆ σ(h|_K mod constants)` off the null set `circNC`** -/
theorem inter_compl_mem_fieldSigmaClosed0 {h : Ω → DistC} {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ)
    {K : Set ℂ} (hK : sphere w ρ ⊆ K) {S : Set Ω}
    (hS : MeasurableSet[recSigma h ρ w K] S) :
    MeasurableSet[fieldSigmaClosed0 h K] (S ∩ (circNC h ρ w)ᶜ) ∧
      MeasurableSet[fieldSigmaClosed0 h K] (circNC h ρ w) := by
  unfold fieldSigmaClosed0
  simp only [MeasurableSpace.measurableSet_iInf]
  have hS' : ∀ ε, 0 < ε → MeasurableSet[fieldSigma (CONF.recField h ρ w) (nbhdO ε K)] S :=
    fun ε hε => by
      have := hS
      unfold recSigma fieldSigmaClosed at this
      simp only [MeasurableSpace.measurableSet_iInf] at this
      exact this ε hε
  exact ⟨fun ε hε => (inter_compl_mem_fieldSigma0On hρ w hK hε (hS' ε hε)).1,
    fun ε hε => (inter_compl_mem_fieldSigma0On hρ w hK hε (hS' ε hε)).2⟩

/-- every `σ((h − h_ρ(w))|_K)`-measurable real function is a.e. equal to a
`σ(h|_K mod constants)`-measurable one -/
theorem aestronglyMeasurable_fieldSigmaClosed0_of_recSigma {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) {K : Set ℂ}
    (hK : sphere w ρ ⊆ K) {f : Ω → ℝ} (hf : Measurable[recSigma h ρ w K] f) :
    AEStronglyMeasurable[fieldSigmaClosed0 h K] f P := by
  set N := circNC h ρ w
  have hN0 := (inter_compl_mem_fieldSigmaClosed0 (S := univ) hρ w hK
    (@MeasurableSet.univ Ω (recSigma h ρ w K))).2
  have hm : Measurable[fieldSigmaClosed0 h K] (Nᶜ.indicator f) := by
    intro B hB
    have h1 := (inter_compl_mem_fieldSigmaClosed0 hρ w hK (hf hB)).1
    by_cases h0 : (0 : ℝ) ∈ B
    · have e : Nᶜ.indicator f ⁻¹' B = (f ⁻¹' B ∩ Nᶜ) ∪ N := by
        ext ω
        by_cases hω : ω ∈ N <;> simp [Set.indicator, hω, h0]
      rw [e]; exact h1.union hN0
    · have e : Nᶜ.indicator f ⁻¹' B = f ⁻¹' B ∩ Nᶜ := by
        ext ω
        by_cases hω : ω ∈ N <;> simp [Set.indicator, hω, h0]
      rw [e]; exact h1
  refine ⟨Nᶜ.indicator f, hm.stronglyMeasurable, ?_⟩
  have hNP : P N = 0 := measure_circNC hh hρ w
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNP] with ω hω
  rw [indicator_of_mem (show ω ∈ Nᶜ from hω)]

end LQGMetric.CONF
