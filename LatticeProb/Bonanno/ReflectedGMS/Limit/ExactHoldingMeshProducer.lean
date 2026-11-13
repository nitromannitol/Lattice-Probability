/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ExactHoldingMeshProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ClockCrossClosenessWeld
import LatticeProb.Bonanno.ReflectedGMS.Spatial.HoldingLengthDecay

/-!
# The exact holding mesh (P3) at the actual walk, every start; main theorem 2 at `hlln` alone

`ClockMeshInputSample.ExactHoldingMesh` (the exact-clock case of `p:lem:holdingsmall`) says that
after diffusive scaling the exact-clock path visits no cell with macroscopic exact holding
length `ε² a_v/π(v) > θ` before the horizon `ε⁻² H`, in probability.  It was the one open
input of `hcross` beyond `hlln` (`ClockCrossClosenessWeld`).  This file proves it.

## The argument (spatial, not the manuscript's temporal one)

The manuscript proves `p:lem:holdingsmall` with the time mass transport `p:eq:timeMTP` under the
stationary two-sided annealed law, which is not built for the actual walk.  The route here needs
no temporal stationarity:

1. **Environment** (`HoldingLengthDecay.ae_exists_areaHoldingLength_bound`, from MTP and (FE)):
   almost surely `h_v ≤ C_δ + δ ‖z_v‖²` for every `δ > 0`.
2. **Exact → exponential** (`expFamily_clock_ge_le`, Markov conditionally on the chain): the
   exponential-clock time `φ(u) = ∑_a E_a c_a(u)` of exact time `u` has conditional mean
   `∑_a c_a(u) = u`, so `P(φ(T) ≥ K T) ≤ 1/K`.  Off that event, a visit of the exact path to `v`
   before `T` is a visit of the exponential path to `v` before `K T`
   (`HoldingTimeChange.X_eq_X_timeChange`).
3. **Exponential containment**: the exponential path stays in `‖z_v‖ ≤ R/ε` up to
   `ε⁻² K H` with probability `≥ 1 − η` (`CompactContainmentProducer.compactContainment_of_arrays`,
   from the martingale arrays, i.e. from `CanonicalBracket` and **`hlln`**).
4. In that ball `ε² h_v ≤ ε² C_δ + δ R² < θ` once `δ R² < θ/2` and `ε` is small.

Hence `limsup P(mesh event) ≤ 1/K + η` for every `K`, `η`.

## Results

* `exactHoldingMesh_of_expContainment` — (P3) for the constructed walk on any cell family, from
  (3.16) for both holding families, containment of the exponential path in a representative
  field and the subquadratic holding bound;
* `exactHoldingMesh_walk` — the same at the actual walk from the pathwise clauses;
* `aeExactHoldingMesh`, `uniformExactHoldingMesh` — (P3) at every start, a.e. environment, from
  `MassTransport ν`, (FE), the harmonic coordinate and `hlln`;
* `uniformClockCrossCloseness` — `hcross` from `hmt`, (FE), `hlln`;
* `reflectedInvarianceConclusions_of_lln` and `…_validLaw_of_lln` — **main theorem 2 at ONE named
  input `hlln`**.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ExactHoldingMeshProducer

open ReflectedWalk ReflectedWalk.IndexSet
open AreaClocks StatementIngredients SpatialEnds
open ReflectedGMS.HoldingTimeChange ReflectedGMS.ClockMeshInput ReflectedGMS.ClockMeshInputSample

universe u

/-! ## Markov for the exact-to-exponential clock, conditionally on the chain -/

section Markov

variable {V : Type u} {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ}

theorem measurable_clock_expFamily (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (u : ℝ≥0∞) :
    Measurable fun E : (ℕ →₀ ℕ) → ℝ => clock Gs Y w E (fun _ => 1) u := by
  have hEq : (fun E : (ℕ →₀ ℕ) → ℝ => clock Gs Y w E (fun _ => 1) u)
      = fun E => ∑' a, ENNReal.ofReal (E a) * exactWeight Gs Y w u a :=
    funext fun E => clock_eq_tsum_exactWeight E u
  rw [hEq]
  exact Measurable.ennreal_tsum fun a => (measurable_pi_apply a).ennreal_ofReal.mul_const _

/-- **`𝔼 φ_E(u) = u` conditionally on the chain.** -/
theorem lintegral_clock_expFamily (hcd : ChainData Gs Y w) (hd : ClockData Gs Y w (fun _ => 1))
    {u : ℝ≥0∞} (hu : u ≠ ⊤) :
    ∫⁻ E, clock Gs Y w E (fun _ => 1) u ∂ReflectedWalk.expFamily = u := by
  calc ∫⁻ E, clock Gs Y w E (fun _ => 1) u ∂ReflectedWalk.expFamily
      = ∫⁻ E, ∑' a, ENNReal.ofReal (E a) * exactWeight Gs Y w u a ∂ReflectedWalk.expFamily :=
        lintegral_congr fun E => clock_eq_tsum_exactWeight E u
    _ = ∑' a, ∫⁻ E, ENNReal.ofReal (E a) * exactWeight Gs Y w u a ∂ReflectedWalk.expFamily :=
        lintegral_tsum fun a => ((measurable_pi_apply a).ennreal_ofReal.mul_const _).aemeasurable
    _ = ∑' a, exactWeight Gs Y w u a := by
        refine tsum_congr fun a => ?_
        rw [lintegral_mul_const _ (measurable_pi_apply a).ennreal_ofReal,
          lintegral_ofReal_eval_expFamily, one_mul]
    _ = u := tsum_exactWeight hcd hd hu

/-- **Markov for the clock**: `P(φ_E(u) ≥ c u) ≤ c⁻¹`, conditionally on the chain. -/
theorem expFamily_clock_ge_le (hcd : ChainData Gs Y w) (hd : ClockData Gs Y w (fun _ => 1))
    {u : ℝ≥0∞} (hu : u ≠ ⊤) (hu0 : u ≠ 0) {c : ℝ≥0∞} :
    ReflectedWalk.expFamily {E | c * u ≤ clock Gs Y w E (fun _ => 1) u} ≤ c⁻¹ := by
  have hM := mul_meas_ge_le_lintegral₀ (μ := ReflectedWalk.expFamily)
    (measurable_clock_expFamily Gs Y w u).aemeasurable (c * u)
  rw [lintegral_clock_expFamily hcd hd hu] at hM
  rw [ENNReal.le_inv_iff_mul_le]
  have h2 : (ReflectedWalk.expFamily {E | c * u ≤ clock Gs Y w E (fun _ => 1) u} * c) * u
      ≤ 1 * u := by
    rw [one_mul]
    calc (ReflectedWalk.expFamily {E | c * u ≤ clock Gs Y w E (fun _ => 1) u} * c) * u
        = c * u * ReflectedWalk.expFamily {E | c * u ≤ clock Gs Y w E (fun _ => 1) u} := by
          ring
      _ ≤ u := hM
  exact (ENNReal.mul_le_mul_iff_left hu0 hu).1 h2

end Markov

/-! ## (P3) from exponential containment and the subquadratic holding bound -/

section Mesh

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V]

theorem measurable_clock_sample (Gs : ℕ → Set V) (w : V → ℝ) (x : ℝ≥0∞) :
    Measurable fun ω : Existence.Sample V => clock Gs ω.1 w ω.2 (fun _ => 1) x := by
  simp only [clock_eq_tsum_exactWeight]
  exact Measurable.ennreal_tsum fun a =>
    (ENNReal.measurable_ofReal.comp ((measurable_pi_apply a).comp measurable_snd)).mul
      (measurable_exactWeight Gs w x a)

/-- **(P3) for the constructed walk**, from (3.16) for both holding families, containment of
the exponential-clock path in a field `zf`, and `h_v ≤ C_δ + δ ‖zf v‖²` for every `δ > 0`. -/
theorem exactHoldingMesh_of_expContainment (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (hrate : ∀ v, 0 < areaRate F v) (z0 : V)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw F D hG z0),
      HoldingTimesSummable (D.levelSets (D.nz z0)) ω.1 (areaRate F) ω.2)
    (hone : ∀ᵐ ω ∂(areaSampleLaw F D hG z0),
      HoldingTimesSummable (D.levelSets (D.nz z0)) ω.1 (areaRate F) (fun _ => 1))
    (zf : V → Plane)
    (hcont : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (η : ℝ≥0∞), 0 < η → ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
        areaSampleLaw F D hG z0 {ω | ∃ s : ℝ≥0, s < (ε n)⁻¹ ^ 2 * H ∧ ∃ v : V,
          exponentialAreaPath F D s ω = some v ∧ R / (ε n : ℝ) < ‖zf v‖} ≤ η)
    (hhold : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ v : V,
      areaHoldingLength F v ≤ C + δ * ‖zf v‖ ^ 2) :
    ExactHoldingMesh F D hG z0 := by
  classical
  intro ε hεpos hεlim H θ hθ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
  -- the Markov level `K`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ((K : ℝ≥0∞))⁻¹ < η / 2 := ENNReal.exists_inv_nat_lt hη2.ne'
  -- the horizon, made positive
  set H' : ℝ≥0 := H + 1 with hH'
  have hH'pos : 0 < H' := by rw [hH']; exact add_pos_of_nonneg_of_pos zero_le one_pos
  -- containment of the exponential path at the horizon `K H'`
  obtain ⟨R, hR0, hRev⟩ := hcont ε hεpos hεlim ((K : ℝ≥0) * H') (η / 2) hη2
  -- the environment bound at `δ = θ / (2 (R² + 1))`
  set δ : ℝ := θ / (2 * (R ^ 2 + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδR : δ * R ^ 2 < θ / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨C, hC⟩ := hhold δ hδ
  have hsmallT : Tendsto (fun n => (ε n : ℝ) ^ 2 * C) atTop (𝓝 0) := by
    have h := ((NNReal.tendsto_coe.2 hεlim).pow 2).mul_const C
    simpa using h
  have hsmall : ∀ᶠ n in atTop, (ε n : ℝ) ^ 2 * C < θ / 2 :=
    hsmallT.eventually_lt_const (by linarith)
  filter_upwards [hRev, hsmall] with n hn hsm
  -- the scale
  have he : 0 < ε n := hεpos n
  have heR : (0 : ℝ) < (ε n : ℝ) := NNReal.coe_pos.2 he
  set Gs := D.levelSets (D.nz z0) with hGs
  set T : ℝ≥0 := (ε n)⁻¹ ^ 2 * H' with hTdef
  have hTpos : 0 < T := mul_pos (pow_pos (inv_pos.2 he) 2) hH'pos
  -- the events
  let Good : Set (Existence.Sample V) :=
    {ω | ω.1 0 0 = z0} ∩ {ω | Consistent Gs ω.1} ∩
      {ω | HoldingTimesSummable Gs ω.1 (areaRate F) (fun _ => 1)} ∩
      {ω | HoldingTimesSummable Gs ω.1 (areaRate F) ω.2} ∩
      {ω | ∀ a, 0 < ω.2 a}
  let Good₀ : Set (Existence.Sample V) :=
    {ω | Consistent Gs ω.1} ∩ {ω | HoldingTimesSummable Gs ω.1 (areaRate F) (fun _ => 1)}
  let Big : Set (Existence.Sample V) :=
    {ω | (K : ℝ≥0∞) * (T : ℝ≥0∞) ≤ clock Gs ω.1 (areaRate F) ω.2 (fun _ => 1) (T : ℝ≥0∞)}
  let Cont : Set (Existence.Sample V) :=
    {ω | ∃ s : ℝ≥0, s < (ε n)⁻¹ ^ 2 * ((K : ℝ≥0) * H') ∧ ∃ v : V,
      exponentialAreaPath F D s ω = some v ∧ R / (ε n : ℝ) < ‖zf v‖}
  let Mesh : Set (Existence.Sample V) :=
    {ω | ∃ t : ℝ≥0, t < (ε n)⁻¹ ^ 2 * H ∧ ∃ v : V,
      exactAreaPath F D t ω = some v ∧ θ < (ε n : ℝ) ^ 2 * areaHoldingLength F v}
  -- the null part
  have hGoodc : areaSampleLaw F D hG z0 Goodᶜ = 0 := by
    have hae : ∀ᵐ ω ∂(areaSampleLaw F D hG z0), ω ∈ Good := by
      filter_upwards [Existence.sampleLaw_ae_start D hG z0,
        Existence.sampleLaw_ae_consistent D hG z0, hone, hexp,
        Existence.sampleLaw_ae_pos D hG z0] with ω h0 hc h1 h2 hp
      exact ⟨⟨⟨⟨h0 0, hc⟩, h1⟩, h2⟩, hp⟩
    exact ae_iff.1 hae
  -- measurability of the Markov event
  have hGood₀m : MeasurableSet Good₀ :=
    (PathProperties.measurableSet_consistent (Ω := Existence.Sample V) Gs
        (Y := Prod.fst) measurable_fst).inter
      (PathProperties.measurableSet_holdingTimesSummable (Ω := Existence.Sample V)
        Gs (areaRate F) (Y := Prod.fst) (E := fun _ _ => (1 : ℝ)) measurable_fst
        measurable_const)
  have hBigm : MeasurableSet Big :=
    measurableSet_le measurable_const (measurable_clock_sample Gs (areaRate F) (T : ℝ≥0∞))
  -- the inclusion
  have hsub : Mesh ⊆ (Goodᶜ ∪ (Big ∩ Good₀)) ∪ Cont := by
    rintro ω ⟨t, ht, v, hv, hθv⟩
    by_cases hgood : ω ∈ Good
    swap
    · exact Or.inl (Or.inl hgood)
    obtain ⟨⟨⟨⟨h00, hcons⟩, hs1⟩, hs2⟩, hpos⟩ := hgood
    by_cases hB : ω ∈ Big
    · exact Or.inl (Or.inr ⟨hB, hcons, hs1⟩)
    right
    have hcd : ChainData Gs ω.1 (areaRate F) :=
      ⟨hcons, D.levelSets_mono _, D.exists_mem_levelSets _, hrate⟩
    have hd₁ : ClockData Gs ω.1 (areaRate F) ω.2 := ⟨hpos, hs2⟩
    have hd₂ : ClockData Gs ω.1 (areaRate F) (fun _ => 1) := ⟨fun _ => one_pos, hs1⟩
    have hBlt : clock Gs ω.1 (areaRate F) ω.2 (fun _ => 1) (T : ℝ≥0∞)
        < (K : ℝ≥0∞) * (T : ℝ≥0∞) := not_le.1 hB
    refine ⟨timeChange Gs ω.1 (areaRate F) ω.2 (fun _ => 1) t, ?_, v, ?_, ?_⟩
    · -- the exponential time is before `K T`
      have htT : t ≤ T := by
        rw [hTdef]
        refine ht.le.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
        rw [hH']
        exact le_add_of_nonneg_right zero_le
      have h1 : ((timeChange Gs ω.1 (areaRate F) ω.2 (fun _ => 1) t : ℝ≥0) : ℝ≥0∞)
          < (((ε n)⁻¹ ^ 2 * ((K : ℝ≥0) * H') : ℝ≥0) : ℝ≥0∞) := by
        rw [coe_timeChange hcd hd₁ hd₂]
        calc clock Gs ω.1 (areaRate F) ω.2 (fun _ => 1) (t : ℝ≥0∞)
            ≤ clock Gs ω.1 (areaRate F) ω.2 (fun _ => 1) (T : ℝ≥0∞) :=
              clock_mono (ENNReal.coe_le_coe.2 htT)
          _ < (K : ℝ≥0∞) * (T : ℝ≥0∞) := hBlt
          _ = (((ε n)⁻¹ ^ 2 * ((K : ℝ≥0) * H') : ℝ≥0) : ℝ≥0∞) := by
              rw [hTdef]
              push_cast
              ring
      exact ENNReal.coe_lt_coe.1 h1
    · -- the exponential path sits at `v` at the time-changed time
      have hexact : exactAreaPath F D t ω = X Gs ω.1 (areaRate F) (fun _ => 1) t := by
        show Existence.process D (areaRate F) t (exactHoldingSample ω) = _
        rw [Existence.process_eq D (areaRate F) (z := z0) (ω := exactHoldingSample ω) h00 hcons]
        rfl
      have hexpo : exponentialAreaPath F D (timeChange Gs ω.1 (areaRate F) ω.2 (fun _ => 1) t) ω
          = X Gs ω.1 (areaRate F) ω.2 (timeChange Gs ω.1 (areaRate F) ω.2 (fun _ => 1) t) := by
        show Existence.process D (areaRate F) _ ω = _
        rw [Existence.process_eq D (areaRate F) (z := z0) (ω := ω) h00 hcons]
      rw [hexpo, ← X_eq_X_timeChange hcd hd₁ hd₂ t, ← hexact]
      exact hv
    · -- the visited cell is outside the ball
      by_contra hle
      have hle' : ‖zf v‖ ≤ R / (ε n : ℝ) := not_lt.1 hle
      have h1 : (ε n : ℝ) * ‖zf v‖ ≤ R := by
        rw [le_div_iff₀ heR] at hle'
        linarith
      have h2 : ((ε n : ℝ) * ‖zf v‖) ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      have h3 : (ε n : ℝ) ^ 2 * areaHoldingLength F v
          ≤ (ε n : ℝ) ^ 2 * C + δ * ((ε n : ℝ) * ‖zf v‖) ^ 2 := by
        have := mul_le_mul_of_nonneg_left (hC v) (sq_nonneg (ε n : ℝ))
        nlinarith
      have h4 : δ * ((ε n : ℝ) * ‖zf v‖) ^ 2 ≤ δ * R ^ 2 :=
        mul_le_mul_of_nonneg_left h2 hδ.le
      linarith
  -- the Markov part, by Tonelli over `coupling ⊗ expFamily`
  have hmarkov : areaSampleLaw F D hG z0 (Big ∩ Good₀) ≤ ((K : ℝ≥0∞))⁻¹ := by
    have hP : areaSampleLaw F D hG z0
        = (D.coupling hG (D.nz z0) z0).prod ReflectedWalk.expFamily := rfl
    rw [hP, Measure.prod_apply (hBigm.inter hGood₀m)]
    have hconst : ∫⁻ _y, ((K : ℝ≥0∞))⁻¹ ∂(D.coupling hG (D.nz z0) z0) = ((K : ℝ≥0∞))⁻¹ := by
      rw [lintegral_const, measure_univ, mul_one]
    refine (lintegral_mono fun y => ?_).trans hconst.le
    by_cases hy : Consistent Gs y ∧ HoldingTimesSummable Gs y (areaRate F) (fun _ => 1)
    · obtain ⟨hcons, hs1⟩ := hy
      have hcd : ChainData Gs y (areaRate F) :=
        ⟨hcons, D.levelSets_mono _, D.exists_mem_levelSets _, hrate⟩
      have hd₂ : ClockData Gs y (areaRate F) (fun _ => 1) := ⟨fun _ => one_pos, hs1⟩
      have hslice : Prod.mk y ⁻¹' (Big ∩ Good₀) ⊆
          {E | (K : ℝ≥0∞) * (T : ℝ≥0∞) ≤ clock Gs y (areaRate F) E (fun _ => 1) (T : ℝ≥0∞)} :=
        fun E hE => hE.1
      refine (measure_mono hslice).trans ?_
      exact expFamily_clock_ge_le hcd hd₂ ENNReal.coe_ne_top
        (by exact_mod_cast hTpos.ne')
    · have hempty : Prod.mk y ⁻¹' (Big ∩ Good₀) ⊆ ∅ := by
        rintro E ⟨-, hc, h1⟩
        exact hy ⟨hc, h1⟩
      exact (measure_mono hempty).trans (by rw [measure_empty]; exact zero_le)
  calc areaSampleLaw F D hG z0 Mesh
      ≤ areaSampleLaw F D hG z0 ((Goodᶜ ∪ (Big ∩ Good₀)) ∪ Cont) := measure_mono hsub
    _ ≤ areaSampleLaw F D hG z0 Goodᶜ + areaSampleLaw F D hG z0 (Big ∩ Good₀)
        + areaSampleLaw F D hG z0 Cont :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + η / 2 + η / 2 := by
        rw [hGoodc]
        exact add_le_add (add_le_add le_rfl (hmarkov.trans hK.le)) hn
    _ = η := by rw [zero_add, ENNReal.add_halves]

end Mesh

/-! ## At the actual walk -/

section Walk

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.AnalyticPacketAssembly
open ReflectedGMS.GaussianLimitIdentification

/-- **(P3) at the actual walk** from the pathwise clock clauses, compact containment of the
exponential lift in a representative field, and the subquadratic holding bound. -/
theorem exactHoldingMesh_walk (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hcc : ActualWindowModulus.CompactContainment e D hG z start Xexp)
    (hhold : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ v : Vertex e.val,
      areaHoldingLength (decode e) v
        ≤ C + δ * Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) ^ 2) :
    ExactHoldingMesh (decode e) D hG start := by
  have h3 := AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
    e D hG hdat
  have h4 :=
    ExactAreaClockCollapse.exactAreaClockReachesLevelZeroIndices_of_environmentWalkData e D hG
      hdat
  have hexp := EnvironmentWalkDataProducer.areaClock_holdingTimesSummable e D hG h3 start
  have hone := ExactExponentialTimeChange.ae_holdingTimesSummable_one D hG
    (areaRate (decode e)) (EnvironmentWalkDataProducer.areaRate_pos e) start (h4 start)
  refine exactHoldingMesh_of_expContainment (decode e) D hG
    (EnvironmentWalkDataProducer.areaRate_pos e) start hexp hone (z.at e) ?_ ?_
  · intro ε hεpos hεlim H η hη
    obtain ⟨R, hR0, hev⟩ := hcc ε hεpos hεlim H η hη
    refine ⟨R, hR0, hev.mono fun n hn => le_trans (measure_mono_ae ?_) hn⟩
    filter_upwards [hclock] with ω hω hmem
    obtain ⟨s, hs, v, hv, hlt⟩ := hmem
    intro hall
    have hc : collapse (Xexp s ω) = some v := by rw [hω.1 s]; exact hv
    have hx : Xexp s ω = Sum.inl v := by
      rcases hX : Xexp s ω with u | u
      · rw [hX] at hc
        have hu : u = v := Option.some.inj hc
        rw [hu]
      · rw [hX] at hc
        exact absurd hc (by simp [collapse])
    exact absurd (hall s v hs hx) (not_le.2 hlt)
  · intro δ hδ
    obtain ⟨C, hC⟩ := hhold δ hδ
    refine ⟨C, fun v => (hC v).trans ?_⟩
    have hinf : Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) ≤ ‖z.at e v‖ := by
      have h := Metric.infDist_le_dist_of_mem (x := (0 : Plane)) (hz e v)
      rwa [dist_zero_left] at h
    have h0 : 0 ≤ Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) :=
      Metric.infDist_nonneg
    have hsq : Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) ^ 2 ≤ ‖z.at e v‖ ^ 2 :=
      pow_le_pow_left₀ h0 hinf 2
    have := mul_le_mul_of_nonneg_left hsq hδ.le
    linarith

/-- **(P3) at every start, almost every environment**, from `MassTransport ν`, (FE), the
harmonic coordinate and the directional bracket LLN (which supplies the martingale arrays behind
compact containment). -/
theorem aeExactHoldingMesh (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) (hlln : AeDirectionalBracketLLN ν Φ) :
    ClockCrossClosenessWeld.AeExactHoldingMesh ν Φ := by
  filter_upwards [ae_all_iff.2
      (CoordinateLocallySquareIntegrableWeld.hbracket_of_ae_diagonalCompensatedSquares ν hmt
        hFE Φ hΦ (InvarianceMainTheoremTwoAtoms.uniformDiagonalCompensatedSquares ν hmt hFE Φ hΦ)),
    hlln, Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hmt hFE.ne, hΦ.2.2.2.2.1,
    HoldingLengthDecay.ae_exists_areaHoldingLength_bound ν hmt hFE.ne]
    with e hbre hllne hdec hcorr hhold
  intro hnt D hG hdat start Xexp Xexact M hclock
  have : Nontrivial (Vertex e.val) := hnt
  have hz : IsCellRepresentative lexMinField := isCellRepresentative_lexMinField
  have hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M :=
    hbre start.1 start.2 hnt D hG hdat Xexp Xexact M hclock
  have hsub : UniformlySublinearError (decode e) (Φ.at e) (lexMinField.at e) :=
    HarmonicCoordinateAssembly.uniformlySublinearError_of_representatives (decode e)
      (decode_geometry e) hdec.2.1 hcorr.2.2.2.2.1 (fun v => hz e v)
  have harray := ActualThresholdArray.harray_of_canonicalBracket e D hG Φ start Xexp Xexact M
    hclock hbr
    (fun k => bilinForm (meanCovariance ν Φ) (EuclideanSpace.single k 1)
      (EuclideanSpace.single k 1))
    (fun k => by
      have h := hllne hnt D hG hdat start M hbr (EuclideanSpace.single k 1)
      rwa [ActualThresholdArray.dirBracket_single] at h)
  have hcc := CompactContainmentProducer.compactContainment_of_arrays e D hG lexMinField Φ start
    Xexp M hz hsub (Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1) harray
  exact exactHoldingMesh_walk e D hG hdat lexMinField Φ start Xexp Xexact M hclock hz hcc hhold

/-- **(P3), uniformly in the harmonic coordinate**, from `hmt`, (FE) and `hlln`. -/
theorem uniformExactHoldingMesh (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hlln : UniformDirectionalBracketLLN ν) :
    ClockCrossClosenessWeld.UniformExactHoldingMesh ν :=
  fun Φ hΦ => aeExactHoldingMesh ν hmt hFE Φ hΦ (hlln Φ hΦ)

/-- **Main theorem 2 at its own law, at ONE named input `hlln`.** -/
theorem reflectedInvarianceConclusions_validLaw_of_lln
    (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P)
    (hmt : AmbientMassTransport P hP) (hFE : FiniteEnergyMoment (validLaw P hP))
    (hlln : UniformDirectionalBracketLLN (validLaw P hP)) :
    ReflectedInvarianceConclusions (validLaw P hP) :=
  ClockCrossClosenessWeld.reflectedInvarianceConclusions_validLaw_of_lln_and_mesh P hP hmt hFE
    hlln (uniformExactHoldingMesh (validLaw P hP) hmt hFE hlln)

end Walk

end ReflectedGMS.ExactHoldingMeshProducer
