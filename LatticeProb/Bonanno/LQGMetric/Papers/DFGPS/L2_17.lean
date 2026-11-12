/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5Final
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Proof
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.StrongWeak

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17 (`lem-lfpp-local`), from its case `B_r(z) ⊂ V`

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Def 2.15/2.16
(T:1136–1146), Lemma 2.17 (T:1150–1155), Lemma 2.19 (T:1182–1206), proof of Lemma 2.17
(T:1218–1282).

* `Lem2_17Core` — the statement the proof of Lemma 2.17 actually establishes after its Step 1
  reduction by Lemma 2.19 (T:1220–1221: "By Lemma 2.19, we can also assume without loss of
  generality that `B_r(z) ⊂ V`"): for every `z`, `r > 0` and open `V ⊇ B_r(z)`, the pair
  `(h − h_r(z), e^{−ξh_r(z)} D_h)` satisfies Def 2.15 at `V` (`LocalAt`).
* `lem2_17_of_core` — **DFGPS Lemma 2.17** (`DFGPS.Lem2_17`) from `Lem2_17Core`, Lemma 2.19
  (`lem2_19`), LM Lemma 2.3 (`Blueprint.LMLem2_3`, which DFGPS cite at T:1140 for the equivalence of
  Def 2.15 with LM Def 1.2) and Lemma 2.8 (through Lemma 2.5 A: the subsequential limit is a.s. a
  continuous length metric).
* `ae_isLength_of_conv` — the limit `D_h` of Lemma 2.17 is a.s. a length metric (DFGPS
  Lemma 2.5 A, T:822).

The ξ-additive local metric of Def 2.16 (`Blueprint.IsXiAdditive1`) has the normalization of `h`
(`h_1(0) = 0`) as its base case; the passage from `h − h_1(0)` to `h` is an a.s. identity
(`L217.condIndepEv_congr_cond`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Bilip

/-- **The case `B_r(z) ⊂ V` of DFGPS Lemma 2.17** (T:1150–1155 with T:1220–1221): for the
subsequential limit `D_h` of `𝔞_ε⁻¹ D^ε_h`, every `z`, `r > 0` and open `V ⊇ B_r(z)`, the internal
metric `e^{−ξh_r(z)} D_h(·,·;V)` is conditionally independent from
`(h − h_r(z), e^{−ξh_r(z)} D_h(·,·;ℂ∖cl V))` given `(h − h_r(z))|_{cl V}`. -/
def Lem2_17Core : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ),
    IsNormalizedWPGFF h P → Measurable Dh → (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    (∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) →
    ∀ (z : ℂ) (r : ℝ) (V : TopologicalSpace.Opens ℂ), 0 < r → Metric.ball z r ⊆ V →
      LocalAt P (normField h z r) (normFam (xiGamma γ) h Dh z r) V

namespace L217

section CI

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- conditional independence only depends on the conditioning σ-algebra up to null events -/
theorem condIndepEv_congr_cond [IsProbabilityMeasure μ] {G G' A B : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hG' : G' ≤ mΩ) (h1 : G ≤ aeClosure μ G') (h2 : G' ≤ aeClosure μ G)
    (hA : A ≤ aeClosure μ mΩ) (hB : B ≤ aeClosure μ mΩ) (h : CondIndepEv G A B μ) :
    CondIndepEv G' A B μ := by
  have key : ∀ s, MeasurableSet[mΩ] s → μ⟦s | G'⟧ =ᵐ[μ] μ⟦s | G⟧ := fun s hs => by
    have hi := integrable_indOne (μ := μ) hs
    exact (L219.condExp_sandwich le_sup_right (sup_le hG hG') hG' (sup_le h1 (le_aeClosure _))
      hi EventuallyEq.rfl).symm.trans (L219.condExp_sandwich le_sup_left (sup_le hG hG') hG
        (sup_le (le_aeClosure _) h2) hi EventuallyEq.rfl)
  intro a b ha hb
  obtain ⟨a₀, ha₀, haa⟩ := hA a ha
  obtain ⟨b₀, hb₀, hbb⟩ := hB b hb
  have c1 : ∀ m : MeasurableSpace Ω, μ⟦a ∩ b | m⟧ =ᵐ[μ] μ⟦a₀ ∩ b₀ | m⟧ := fun m =>
    condExp_congr_ae (indOne_ae_eq_of_ae_eq (haa.inter hbb))
  have c2 : ∀ m : MeasurableSpace Ω, μ⟦a | m⟧ =ᵐ[μ] μ⟦a₀ | m⟧ := fun m =>
    condExp_congr_ae (indOne_ae_eq_of_ae_eq haa)
  have c3 : ∀ m : MeasurableSpace Ω, μ⟦b | m⟧ =ᵐ[μ] μ⟦b₀ | m⟧ := fun m =>
    condExp_congr_ae (indOne_ae_eq_of_ae_eq hbb)
  filter_upwards [h a b ha hb, c1 G', c1 G, c2 G', c2 G, c3 G', c3 G, key _ (ha₀.inter hb₀),
    key _ ha₀, key _ hb₀] with x h0 e1 e1' e2 e2' e3 e3' k1 k2 k3
  simp only [Pi.mul_apply] at h0 ⊢
  rw [e1, k1, ← e1', h0, e2', e3', ← k2, ← k3, e2, e3]

end CI

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma fieldSigmaClosed_le_aeClosure_of_ae_eq {g g' : Ω → DistC} (hgg : ∀ᵐ ω ∂P, g ω = g' ω)
    (K : Set ℂ) : fieldSigmaClosed g K ≤ aeClosure P (fieldSigmaClosed g' K) := by
  intro s hs
  refine GM.gm_aeEventIn_fieldSigmaClosed g' K fun n => ?_
  have hs' : MeasurableSet[fieldSigma g (nbhdO (1 / ((n : ℝ) + 1)) K)] s := by
    have := hs
    unfold fieldSigmaClosed at this
    rw [MeasurableSpace.measurableSet_iInf] at this
    have := this (1 / ((n : ℝ) + 1))
    rw [MeasurableSpace.measurableSet_iInf] at this
    exact this (by positivity)
  obtain ⟨S, hS, rfl⟩ := hs'
  refine ⟨_, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [hgg] with ω hω
  change (restrictTo _ (g ω) ∈ S) = (restrictTo _ (g' ω) ∈ S)
  rw [hω]

/-- the subsequential limit of Lemma 2.17 is a.s. a length metric (DFGPS Lemma 2.5 A, T:822) -/
theorem ae_isLength_of_conv (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    [IsProbabilityMeasure P] {h : Ω → DistC} {Dh : Ω → ContMetric} {εn : ℕ → ℝ}
    (hh : IsNormalizedWPGFF h P) (hDm : Measurable Dh) (hεp : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0))
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) :
    ∀ᵐ ω ∂P, (Dh ω).IsLength := by
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
  have hA' := ae_of_ae_map hDc.aemeasurable hA
  filter_upwards [hA'] with ω ⟨_, hl⟩
  exact hl

lemma measurable_smulPos_rand {D : Ω → ContMetric} (hD : Measurable D) {x : Ω → ℝ}
    (hx : Measurable x) :
    Measurable fun ω => (D ω).smulPos (Real.exp (x ω)) (Real.exp_pos _) := by
  have hc : Continuous fun p : ℝ × C(ℂ × ℂ, ℝ) => p.1 • p.2 := continuous_smul
  exact (hc.measurable.comp (hx.exp.prodMk (measurable_subtype_coe.comp hD))).subtype_mk

end L217

open L217

end LQGMetric.DFGPS
