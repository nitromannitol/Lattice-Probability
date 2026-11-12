/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Conv
import LatticeProb.Bonanno.LQGMetric.Prob.CondCopies
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.20 (`lem-lfpp-msrble`): the subsequential limit is determined by the field

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 2.20 T:1297–1302, proof
T:1320–1336, with Theorem 2.21 = LM Corollary 1.8 (`Blueprint.LMCor1_8`, T:1304–1317).

Proof of the paper: `D_h` is a ξ-additive local metric (Lemma 2.17); Lemma 2.13 and translation
invariance give a deterministic `C` with (T:1325–1330)
`P[D_h(∂B_{r/2}(z), ∂B_r(z)) ≥ C^{-1/2} 𝔠_r e^{ξ h_r(z)}] ≥ 1 − (1−p)/2` and
`P[sup_{u,v ∈ ∂B_r(z)} D_h(u,v; B_{2r}(z) ∖ cl B_{r/2}(z)) ≤ C^{1/2} 𝔠_r e^{ξ h_r(z)}] ≥ 1 − (1−p)/2`
(the paper prints `≥ (1−p)/2`; the union bound it then uses needs `1 − (1−p)/2`); since the
conditionally independent copy `D̃` has the same joint law with `h` as `D_h`, a union bound gives
(eqn-bilip) with probability `≥ p`, and LM Cor 1.8 applies. The last sentence is Lemma 1.3
(`L220.tendstoInProbLU_of_det`, `L2_20Conv.lean`).

Here:
* `L220.condCopy_inter_ge` — the union bound on the conditional-copy space (T:1331).
* `Lem2_20Bilip` — the two displays T:1325–1330, with the scale `𝔠_r e^{ξ h_r(z)}` abstracted to a
  measurable function `S` of the field and the constants `C^{∓1/2}` folded into `C⁻¹`, `1`
  (the internal-diameter event is given as a measurable event `E` of `(h, D_h)`, since
  measurability of the internal diameter is not in the library). Open node.
* `lem2_20_of_bilip : LMCor1_8 → Lem2_17 → Lem2_20Bilip → Lem2_20`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint

namespace L220

/-- **Union bound for a conditionally independent copy** (T:1331): if two measurable events of
`(X, Y)` each have probability `≥ 1 − q`, then on the conditional-copy space the event that the
first holds for `(X, Y)` and the second for `(X, Ỹ)` has probability `≥ 1 − 2q`. -/
theorem condCopy_inter_ge {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y)
    {E₁ E₂ : Set (α × β)} (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂) {q : ℝ}
    (h1 : ENNReal.ofReal (1 - q) ≤ μ {ω | (X ω, Y ω) ∈ E₁})
    (h2 : ENNReal.ofReal (1 - q) ≤ μ {ω | (X ω, Y ω) ∈ E₂}) :
    ENNReal.ofReal (1 - 2 * q) ≤
      condCopyMeasure Y X μ hX {p | (X p.1, Y p.1) ∈ E₁ ∧ (X p.1, p.2) ∈ E₂} := by
  set ν := condCopyMeasure Y X μ hX
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hf1 : Measurable fun p : Ω × β => (X p.1, Y p.1) := hXY.comp measurable_fst
  have hf2 : Measurable fun p : Ω × β => (X p.1, p.2) := (hX.comp measurable_fst).prodMk
    measurable_snd
  set A₁ := {p : Ω × β | (X p.1, Y p.1) ∈ E₁}
  set A₂ := {p : Ω × β | (X p.1, p.2) ∈ E₂}
  have hA₁ : MeasurableSet A₁ := hf1 hE₁
  have hA₂ : MeasurableSet A₂ := hf2 hE₂
  have e1 : ν A₁ = μ {ω | (X ω, Y ω) ∈ E₁} := by
    have hm := condCopyMeasure_fst (Y := Y) (μ := μ) hX
    have : ν A₁ = (ν.map Prod.fst) {ω | (X ω, Y ω) ∈ E₁} := by
      rw [Measure.map_apply measurable_fst (show MeasurableSet {ω | (X ω, Y ω) ∈ E₁} from hXY hE₁)]
      rfl
    rw [this, hm]
  have e2 : ν A₂ = μ {ω | (X ω, Y ω) ∈ E₂} := by
    have hm := condCopyMeasure_map_snd (μ := μ) hX hY
    have : ν A₂ = (ν.map fun p => (X p.1, p.2)) E₂ := by
      rw [Measure.map_apply hf2 hE₂]; rfl
    rw [this, hm, Measure.map_apply hXY hE₂]; rfl
  have r1 : 1 - q ≤ ν.real A₁ := by
    rw [measureReal_def, e1]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  have r2 : 1 - q ≤ ν.real A₂ := by
    rw [measureReal_def, e2]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h2
  have hu := measureReal_union_add_inter (μ := ν) (s := A₁) hA₂
  have hle : ν.real (A₁ ∪ A₂) ≤ 1 := measureReal_le_one
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (by
    show 1 - 2 * q ≤ ν.real (A₁ ∩ A₂)
    linarith)

open L217 in
/-- the law of a subsequential limit `D_h` is carried by length metrics (Lemma 2.5 A; the law-level
form of `L217.ae_isLength_of_conv`, needed to transfer the length property to the conditional
copy `D̃`) -/
theorem ae_isLength_law (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    {Dh : Ω → ContMetric} {εn : ℕ → ℝ}
    (hh : IsNormalizedWPGFF h P) (hDm : Measurable Dh) (hεp : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0))
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) :
    ∀ᵐ d ∂(P.map Dh), ContMetric.IsLength d := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hε0.eventually (gt_mem_nhds one_pos))
  set ε' : ℕ → ℝ := fun n => εn (n + N)
  have hgff : IsGFFPlusBddCont h P := isGFFPlusBddCont_of_normalizedWP hh
  have hDc : Measurable fun ω => (Dh ω).1 := measurable_subtype_coe.comp hDm
  have hFm : ∀ n, AEMeasurable (fun ω => lfppC (xiGamma γ) (ε' n) (h ω)) P := fun n =>
    aemeasurable_lfppC hgff (hεp _).ne'
  let ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ) := fun n =>
    ⟨P.map fun ω => lfppC (xiGamma γ) (ε' n) (h ω), inferInstance⟩
  let μ : ProbabilityMeasure C(ℂ × ℂ, ℝ) :=
    ⟨P.map fun ω => (Dh ω).1, inferInstance⟩
  have hlim : Tendsto ν atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have H := hconv (fun x => f x.2) (f.continuous.comp continuous_snd)
      ⟨‖f‖, fun x => (Real.norm_eq_abs _).symm.le.trans (f.norm_coe_le_norm x.2)⟩
    have e1 : ∀ n, ∫ x, f x ∂(ν n : Measure C(ℂ × ℂ, ℝ)) =
        ∫ ω, f (lfppC (xiGamma γ) (ε' n) (h ω)) ∂P := fun n =>
      integral_map (hFm n) f.continuous.aestronglyMeasurable
    have e2 : ∫ x, f x ∂(μ : Measure C(ℂ × ℂ, ℝ)) = ∫ ω, f (Dh ω).1 ∂P :=
      integral_map hDc.aemeasurable f.continuous.aestronglyMeasurable
    simp only [e1, e2]
    exact H.comp (tendsto_add_atTop_nat N)
  have hA := ((lem2_5 h28).1 γ hγ hγ2 P h hgff).2 ε' ν μ
    (fun n => ⟨⟨hεp _, hN _ (by omega)⟩, rfl⟩) (hε0.comp (tendsto_add_atTop_nat N)) hlim
  have hval : Measurable fun d : ContMetric => d.1 := measurable_subtype_coe
  have hmap : (P.map Dh).map (fun d : ContMetric => d.1) = P.map (fun ω => (Dh ω).1) :=
    Measure.map_map hval hDm
  have hA' : ∀ᵐ d ∂((P.map Dh).map (fun d : ContMetric => d.1)), IsContLengthMetric d := by
    rw [hmap]; exact hA
  filter_upwards [ae_of_ae_map hval.aemeasurable hA'] with d ⟨_, hl⟩
  exact hl

end L220

/-- **The two displays in the proof of DFGPS Lemma 2.20** (T:1325–1330), for a subsequential limit
coupling `(h, D_h)` as in `Lem2_20`: for every `q > 0` there is a deterministic `C > 0` such that
for all `z` and `r > 0`, with a scale `S(h)` measurable in `h` (in the paper
`S(h) = C^{1/2} 𝔠_r e^{ξ h_r(z)}`), `D_h(∂B_{r/2}(z), ∂B_r(z)) ≥ C⁻¹ S(h)` with probability
`≥ 1 − q`, and `sup_{u,v ∈ ∂B_r(z)} D_h(u,v; 𝔸_{r/2,2r}(z)) ≤ S(h)` whenever `D_h` is a length
metric, on a measurable event `E` of `(h, D_h)` of probability `≥ 1 − q`. The paper derives this from Lemma 2.13 and the translation
invariance of the law of `h` modulo additive constant. -/
def Lem2_20Bilip : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ),
    IsNormalizedWPGFF h P → Measurable Dh → (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    (∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) →
    ∀ q : ℝ, 0 < q → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      ∃ S : DistC → ℝ, Measurable S ∧
        ENNReal.ofReal (1 - q) ≤ P {ω | ENNReal.ofReal (C⁻¹ * S (h ω)) ≤
          setDist (Dh ω) (Metric.sphere z (r / 2)) (Metric.sphere z r)} ∧
        ∃ E : Set (DistC × ContMetric), MeasurableSet E ∧
          (∀ x ∈ E, x.2.IsLength →
            internalDiam x.2 (Metric.sphere z r) (annulus z (r / 2) (2 * r)) ≤
              ENNReal.ofReal (S x.1)) ∧
          ENNReal.ofReal (1 - q) ≤ P {ω | (h ω, Dh ω) ∈ E}

/-- **DFGPS Lemma 2.20** (T:1297–1302, proof T:1320–1336) from LM Corollary 1.8, Lemma 2.17 and
the bi-Lipschitz-type bounds `Lem2_20Bilip`. -/
theorem lem2_20_of_bilip (hLM : LMCor1_8) (h28 : Lem2_8) (h217 : Lem2_17) (hbil : Lem2_20Bilip) :
    Lem2_20 := by
  intro γ hγ hγ2 Ω _ P _ h Dh εn hh hDm hεp hεt hconv
  have hadd : IsXiAdditive1 (xiGamma γ) P h Dh := h217 γ hγ hγ2 P h Dh εn hh hDm hεp hεt hconv
  obtain ⟨p, hp0, hp1, hcor⟩ := hLM
  set q : ℝ := (1 - p) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  obtain ⟨C, hC, hb⟩ := hbil γ hγ hγ2 P h Dh εn hh hDm hεp hεt hconv q hq0
  have hdet : AEDeterminedBy Dh h P := by
    refine hcor (xiGamma γ) P h Dh hh hadd C hC fun K _ => ⟨1, one_pos, fun z _ r hr => ?_⟩
    obtain ⟨S, hS, h1, E, hE, hEsub, h2⟩ := hb z r hr.1
    set E₁ : Set (DistC × ContMetric) := {x | ENNReal.ofReal (C⁻¹ * S x.1) ≤
      setDist x.2 (Metric.sphere z (r / 2)) (Metric.sphere z r)}
    have hE₁ : MeasurableSet E₁ :=
      measurableSet_le (ENNReal.measurable_ofReal.comp (measurable_const.mul
        (hS.comp measurable_fst))) ((GM.measurable_setDist _ _).comp measurable_snd)
    have key := L220.condCopy_inter_ge hh.1.measurable hDm hE₁ hE h1 h2
    have hp : 1 - 2 * q = p := by rw [hq]; ring
    rw [hp] at key
    -- the copy `D̃` is a.s. a length metric (its law is that of `D_h`)
    have hlenL := L220.ae_isLength_law h28 hγ hγ2 hh hDm hεp hεt hconv
    have hsnd : (condCopyMeasure Dh h P hh.1.measurable).map Prod.snd = P.map Dh := by
      have hm := condCopyMeasure_map_snd (μ := P) hh.1.measurable hDm
      have hf : Measurable fun p : Ω × ContMetric => (h p.1, p.2) :=
        (hh.1.measurable.comp measurable_fst).prodMk measurable_snd
      calc (condCopyMeasure Dh h P hh.1.measurable).map Prod.snd
          = ((condCopyMeasure Dh h P hh.1.measurable).map fun p => (h p.1, p.2)).map
              Prod.snd := by rw [Measure.map_map measurable_snd hf]; rfl
        _ = (P.map fun ω => (h ω, Dh ω)).map Prod.snd := by rw [hm]
        _ = P.map Dh := by rw [Measure.map_map measurable_snd (hh.1.measurable.prodMk hDm)]; rfl
    have hlen2 : ∀ᵐ x ∂(condCopyMeasure Dh h P hh.1.measurable), x.2.IsLength := by
      rw [← hsnd] at hlenL
      exact ae_of_ae_map measurable_snd.aemeasurable hlenL
    refine key.trans (measure_mono_ae ?_)
    filter_upwards [hlen2] with x hxl hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : ENNReal.ofReal (C⁻¹ * S (h x.1)) ≤
        setDist (Dh x.1) (Metric.sphere z (r / 2)) (Metric.sphere z r) := hx1
    have hS' : ENNReal.ofReal (S (h x.1)) = ENNReal.ofReal C * ENNReal.ofReal (C⁻¹ * S (h x.1)) := by
      rw [← ENNReal.ofReal_mul hC.le, ← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
    show internalDiam x.2 (Metric.sphere z r) (annulus z (r / 2) (2 * r)) ≤
      ENNReal.ofReal C * setDist (Dh x.1) (Metric.sphere z (r / 2)) (Metric.sphere z r)
    calc _ ≤ ENNReal.ofReal (S (h x.1)) := hEsub _ hx2 hxl
      _ = _ := hS'
      _ ≤ _ := by gcongr
  exact ⟨hdet, L220.tendstoInProbLU_of_det P h Dh εn hh hDm hεp hconv hdet⟩

end LQGMetric.DFGPS
