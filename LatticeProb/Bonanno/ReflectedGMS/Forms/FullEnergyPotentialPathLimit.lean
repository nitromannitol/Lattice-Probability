/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyPotentialPathLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CorePotentialUniformBound
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPotentialVariance
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingaleLinearity
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyStationaryIsometry

/-! Raw centered full-energy potential paths. This does not assert vanishing
of the remainder for locally finite-energy harmonic coordinates. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm
variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem compactResolventCorePotential_sub
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q r : CountableResolventCoreIndex V) :
    compactResolventCorePotential G m hm PF default (q - r) =
      compactResolventCorePotential G m hm PF default q -
        compactResolventCorePotential G m hm PF default r := by
  classical
  unfold compactResolventCorePotential
  apply Finsupp.sum_sub_index
  intro y a b
  rw [Rat.cast_sub, sub_smul]

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m)

include h hG hmsum

/-- Actual successive core differences have normalized square envelopes with
geometrically summable stationary integrals. -/
theorem fullEnergyPotential_successive_envelopes (T : ℝ≥0) :
    ∃ D : ℕ → PF.Ω → ℝ, (∀ n, Measurable (D n)) ∧
      (∀ n, Integrable (D n) (reflectedSpeedLaw PF m)) ∧
      (∀ᵐ ω ∂reflectedSpeedLaw PF m, ∀ n, 0 ≤ D n ω ∧ ∀ t ≤ T,
        (compactResolventCorePotential G m hm PF default
            (fullEnergyCoreIndex G m hm U (2 * (n + 1))) t ω -
          compactResolventCorePotential G m hm PF default
            (fullEnergyCoreIndex G m hm U (2 * (n + 1))) 0 ω -
          (compactResolventCorePotential G m hm PF default
            (fullEnergyCoreIndex G m hm U (2 * n)) t ω -
          compactResolventCorePotential G m hm PF default
            (fullEnergyCoreIndex G m hm U (2 * n)) 0 ω)) ^ 2 ≤
          D n ω * (1 / 4 : ℝ) ^ n) ∧
      (∀ n, (∫ ω, D n ω ∂reflectedSpeedLaw PF m) ≤
        4096 * (T : ℝ) * (1 / 4 : ℝ) ^ n) := by
  let q := fullEnergyCoreIndex G m hm U
  let r := fun n ↦ q (2 * (n + 1)) - q (2 * n)
  choose E hEm hEi hEb hEint using fun n ↦
    exists_integrable_sq_envelope_compactResolventCorePotential
      h hG hm hmsum default (r n) T
  refine ⟨fun n ω ↦ E n ω / (1 / 4 : ℝ) ^ n,
    fun n ↦ (hEm n).div_const _, fun n ↦ (hEi n).div_const _, ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 hEb] with ω hω
    intro n
    have hpos : 0 < (1 / 4 : ℝ) ^ n := by positivity
    have hnonneg : 0 ≤ E n ω := by simpa using hω n 0 (zero_le : 0 ≤ T)
    refine ⟨div_nonneg hnonneg hpos.le, ?_⟩
    intro t ht
    rw [div_mul_cancel₀ _ hpos.ne']
    have hb := hω n t ht
    dsimp only [r] at hb
    rw [compactResolventCorePotential_sub] at hb
    simp only [Pi.sub_apply] at hb
    convert hb using 1 <;> ring
  · intro n
    rw [integral_div]
    have hpair : G.Energy (countableResolventCoreFeature G m (r n)) ≤
        ((1 / 2 : ℝ) ^ (2 * (n + 1)) + (1 / 2 : ℝ) ^ (2 * n)) ^ 2 := by
      dsimp only [r]
      rw [countableResolventCoreFeature_sub]
      exact countableResolventCore_pair_energy_le_of_geometric_bound G m U q
        (fullEnergyCoreIndex_bound G m hm U) _ _
    have hpowers :
        ((1 / 2 : ℝ) ^ (2 * (n + 1)) + (1 / 2 : ℝ) ^ (2 * n)) ^ 2 ≤
          2 * ((1 / 4 : ℝ) ^ n) ^ 2 := by
      calc
        _ = ((1 / 4 : ℝ) ^ n / 4 + (1 / 4 : ℝ) ^ n) ^ 2 := by
          rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add, pow_mul]
          norm_num
          ring
        _ ≤ _ := by nlinarith [sq_nonneg ((1 / 4 : ℝ) ^ n)]
    apply (div_le_iff₀ (by positivity : 0 < (1 / 4 : ℝ) ^ n)).2
    calc
      _ ≤ 2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m (r n)) := hEint n
      _ ≤ 2048 * (T : ℝ) * (2 * ((1 / 4 : ℝ) ^ n) ^ 2) :=
        mul_le_mul_of_nonneg_left (hpair.trans hpowers) (by positivity)
      _ = _ := by ring

noncomputable def fullEnergyPotentialApprox
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m)
    (n : ℕ) (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  compactResolventCorePotential G m hm PF default (fullEnergyCoreIndex G m hm U (2 * n)) t ω -
    compactResolventCorePotential G m hm PF default (fullEnergyCoreIndex G m hm U (2 * n)) 0 ω

noncomputable def fullEnergyPotentialPathLimit
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m)
    (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  limUnder atTop (fun n ↦ fullEnergyPotentialApprox G m hm PF default U n t ω)

/-- Borel-Cantelli applied to the actual raw-potential envelopes. -/
theorem fullEnergyPotentialApprox_successive_uniform (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ≤ (T : ℝ≥0),
      |fullEnergyPotentialApprox G m hm PF default U (n + 1) t ω -
        fullEnergyPotentialApprox G m hm PF default U n t ω| ≤ (1 / 2 : ℝ) ^ n := by
  apply (ae_reflectedSpeedLaw_iff PF m hm _).1 ?_ z
  rw [ae_all_iff]
  intro T
  obtain ⟨D, hDm, hDi, hDb, hDint⟩ :=
    fullEnergyPotential_successive_envelopes h hG hm hmsum default U (T : ℝ≥0)
  let P := reflectedSpeedLaw PF m
  let bad : ℕ → Set PF.Ω := fun n ↦ {ω | 1 ≤ D n ω}
  have hbad (n : ℕ) : P (bad n) ≤
      ENNReal.ofReal (4096 * (T : ℝ)) * (2 : ℝ≥0∞)⁻¹ ^ n := by
    have hpos : 0 ≤ᵐ[P] D n := hDb.mono fun ω hω ↦ (hω n).1
    calc
      P (bad n) ≤ ENNReal.ofReal (∫ ω, D n ω ∂P) :=
        (hDi n).measure_le_integral hpos (fun _ hω ↦ hω)
      _ ≤ ENNReal.ofReal (4096 * (T : ℝ) * (1 / 4 : ℝ) ^ n) :=
        ENNReal.ofReal_le_ofReal (hDint n)
      _ ≤ ENNReal.ofReal (4096 * (T : ℝ) * (1 / 2 : ℝ) ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
          (by positivity)
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hsum : (∑' n, P (bad n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.summable.tsum_le_tsum hbad ENNReal.summable)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  filter_upwards [ae_eventually_notMem hsum, hDb] with ω hω hbound
  filter_upwards [hω] with n hn
  intro t ht
  have hlt : D n ω < 1 := lt_of_not_ge hn
  have hsq := (hbound n).2 t ht
  change (fullEnergyPotentialApprox G m hm PF default U (n + 1) t ω -
    fullEnergyPotentialApprox G m hm PF default U n t ω) ^ 2 ≤ _ at hsq
  apply abs_le_of_sq_le_sq _ (by positivity)
  calc
    _ ≤ D n ω * (1 / 4 : ℝ) ^ n := hsq
    _ ≤ (1 / 4 : ℝ) ^ n := mul_le_of_le_one_left (by positivity) hlt.le
    _ = ((1 / 2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num

/-- The existing compact lift makes each finite core potential càdlàg. -/
theorem compactResolventCorePotential_ae_isCadlag (q : CountableResolventCoreIndex V)
    (z : V) : ∀ᵐ ω ∂PF.P z,
      IsCadlag (fun t ↦ compactResolventCorePotential G m hm PF default q t ω) := by
  classical
  filter_upwards [reflectedCompactProcess_ae_cadlag_and_projection
    h hG hm hmsum default z] with ω hc
  unfold compactResolventCorePotential Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  have hpath (y : V) : IsCadlag (fun t ↦
      (q y : ℝ) • ResolventCompactSpace.potentialCoordinate G m hm y
        (reflectedCompactProcess G m hm PF default t ω)) := by
    have hy := (hc.1.continuous_comp
      (ResolventCompactSpace.potentialCoordinate G m hm y).continuous).const_smul (q y : ℝ)
    convert hy using 1 <;> funext s <;> rfl
  induction q.support using Finset.induction_on with
  | empty => simpa using (IsCadlag.const (c := (0 : ℝ)))
  | @insert y s hy ih =>
      have hadd := (hpath y).add ih
      convert hadd using 1
      funext t
      rw [Finset.sum_insert hy]
      rfl

/-- Under every fixed starting law, the actual raw centered core potentials
converge locally uniformly to a càdlàg full-energy path. -/
theorem fullEnergyPotentialPathLimit_ae_cadlag_and_uniform (z : V) :
    ∀ᵐ ω ∂PF.P z,
      IsCadlag (fun t ↦ fullEnergyPotentialPathLimit G m hm PF default U t ω) ∧
        ∀ T : ℕ, TendstoUniformlyOn
          (fun n t ↦ fullEnergyPotentialApprox G m hm PF default U n t ω)
          (fun t ↦ fullEnergyPotentialPathLimit G m hm PF default U t ω)
          atTop (Icc 0 (T : ℝ≥0)) := by
  have hgeom := fullEnergyPotentialApprox_successive_uniform h hG hm hmsum default U z
  have hcad : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ,
      IsCadlag (fun t ↦ fullEnergyPotentialApprox G m hm PF default U n t ω) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [compactResolventCorePotential_ae_isCadlag h hG hm hmsum default
      (fullEnergyCoreIndex G m hm U (2 * n)) z] with ω hω
    exact hω.sub IsCadlag.const
  filter_upwards [hgeom, hcad] with ω hω hωcad
  let fseq := fun n t ↦ fullEnergyPotentialApprox G m hm PF default U n t ω
  have hdiff : ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ≥0) (T : ℝ≥0),
      ‖fseq (n + 1) t - fseq n t‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro T
    filter_upwards [hω T] with n hn
    intro t ht
    simpa only [fseq, Real.norm_eq_abs] using hn t ht.2
  obtain ⟨f, hfcad, hf⟩ :=
    exists_cadlag_tendstoUniformlyOn_Icc_nat_of_geometric fseq hωcad hdiff
  have heq : (fun t ↦ fullEnergyPotentialPathLimit G m hm PF default U t ω) = f := by
    funext t
    obtain ⟨T, ht⟩ := exists_nat_ge t
    exact ((hf T).tendsto_at ⟨zero_le, ht⟩).limUnder_eq
  rw [heq]
  exact ⟨hfcad, hf⟩

/-- The path limit recovers the actual full-domain representative
simultaneously at all times at which the original path is a vertex. -/
theorem fullEnergyPotentialPathLimit_ae_eq_at_vertex_times (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t x, PF.X t ω = some x →
      fullEnergyPotentialPathLimit G m hm PF default U t ω =
        unweight m (valueInclusion G m U) x - unweight m (valueInclusion G m U) z := by
  classical
  have heven : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn ↦ by omega⟩
  have hconv (x : V) :=
    (countableResolventCoreFeature_tendsto_of_geometric_bound G m hm U
      (fullEnergyCoreIndex G m hm U) (fullEnergyCoreIndex_bound G m hm U) x).comp heven
  filter_upwards [reflectedCompactProcess_ae_cadlag_and_projection
    h hG hm hmsum default z, (h z).1] with ω hc h0
  have hval (q : CountableResolventCoreIndex V) (t : ℝ≥0) (x : V)
      (hx : PF.X t ω = some x) :
      compactResolventCorePotential G m hm PF default q t ω =
        countableResolventCoreFeature G m q x := by
    have hp := (ResolventCompactSpace.toOption_eq_some_iff G m hm _ x).1
      ((hc.2 t).trans hx)
    unfold compactResolventCorePotential Finsupp.sum
    simp only [Finset.sum_apply, Pi.smul_apply, hp,
      ResolventCompactSpace.potentialCoordinate_vertex, smul_eq_mul]
    exact (countableResolventCoreFeature_eq_sum G m q x).symm
  intro t x hx
  have hlim : Tendsto
      (fun n ↦ fullEnergyPotentialApprox G m hm PF default U n t ω) atTop
      (𝓝 (unweight m (valueInclusion G m U) x -
        unweight m (valueInclusion G m U) z)) := by
    convert (hconv x).sub (hconv z) using 1
    funext n
    simp only [fullEnergyPotentialApprox, Function.comp_apply, hval _ t x hx, hval _ 0 z h0]
  exact hlim.limUnder_eq

/-- At every deterministic time the `none`-as-zero convention is retained. -/
theorem fullEnergyPotentialPathLimit_ae_eq (z : V) (t : ℝ≥0) :
    fullEnergyPotentialPathLimit G m hm PF default U t =ᵐ[PF.P z]
      fun ω ↦ (PF.X t ω).elim 0 (unweight m (valueInclusion G m U)) -
        unweight m (valueInclusion G m U) z := by
  filter_upwards [fullEnergyPotentialPathLimit_ae_eq_at_vertex_times
    h hG hm hmsum default U z, (h z).2.1 t] with ω heq ht
  obtain ⟨x, hx⟩ := ht.1
  simpa only [hx, Option.elim_some] using heq t x hx

end ReflectedGMS
