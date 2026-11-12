/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4E at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm

/-!
# Whole-plane LQG area, part 5: a continuous version of the radial part

`ae_radial_version`: for a whole-plane GFF `X`, a.s. there is `R : ℝ → ℝ`, continuous on `(0,∞)`
and measurable, with `X_{|z|}(0) = R(|z|)` for a.e. `z ∈ ℂ` (the first three conjuncts of statement (R2)).

Source: the jointly continuous version of the circle-average process (Duplantier–Sheffield
arXiv:0808.1560 Prop. 3.1 / Hu–Miller–Peres; LM `CircleAvg.exists_continuous_version_circleAvg`)
at the centre `0`. The version is only known to agree with the circle averages radius by radius;
to pass to "for a.e. `z`" (Fubini) we replace it, on the full-measure event where it agrees with
the circle averages at all dyadic radii, by the jointly measurable limit of the circle averages
at the dyadic upper approximations `⌈r 2^n⌉/2^n` (own elementary measure-theoretic glue).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric

/-- the dyadic upper approximation `(⌊r 2^n⌋ + 1)/2^n` -/
def dyUp (n : ℕ) (r : ℝ) : ℝ := ((⌊r * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n

lemma measurable_dyUp (n : ℕ) : Measurable (dyUp n) :=
  (((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
    (Nat.measurable_floor.comp (measurable_id.mul_const _))).add_const _).div_const _

lemma dyUp_pos (n : ℕ) (r : ℝ) : 0 < dyUp n r := by
  unfold dyUp; positivity

lemma tendsto_dyUp {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun n => dyUp n r) atTop (𝓝 r) := by
  have h2 : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => pow_pos two_pos n
  have hlo : ∀ n, r ≤ dyUp n r := fun n => by
    rw [dyUp, le_div_iff₀ (h2 n)]
    have := Nat.lt_floor_add_one (r * 2 ^ n)
    linarith
  have hhi : ∀ n, dyUp n r ≤ r + (1 / 2) ^ n := fun n => by
    rw [dyUp, div_le_iff₀ (h2 n), add_mul, one_div, inv_pow, inv_mul_cancel₀ (h2 n).ne']
    have := Nat.floor_le (mul_nonneg hr (h2 n).le)
    linarith
  have hu : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ) ^ n) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu hlo hhi

/-- `X_r(0) − X_1(0)` -/
def radG {Ω : Type*} (X : Ω → Field) (r : ℝ) (ω : Ω) : ℝ :=
  circleAvg (X ω) r 0 - circleAvg (X ω) 1 0

/-- the jointly measurable dyadic limit of `radG` -/
def radFt {Ω : Type*} (X : Ω → Field) (p : ℝ × Ω) : ℝ :=
  limUnder atTop fun n => radG X (dyUp n p.1) p.2

lemma measurable_radG {Ω : Type*} [MeasurableSpace Ω] {X : Ω → Field} (hX : Measurable X) :
    Measurable fun p : ℝ × Ω => radG X p.1 p.2 := by
  have h1 : Measurable fun p : ℝ × Ω => circleAvg (X p.2) p.1 0 :=
    measurable_circleAvg.comp (f := fun p : ℝ × Ω => (X p.2, p.1, (0 : ℂ)))
      ((hX.comp measurable_snd).prodMk (measurable_fst.prodMk measurable_const))
  exact h1.sub ((measurable_circleAvg_left 1 0).comp (hX.comp measurable_snd))

lemma measurable_radFt {Ω : Type*} [MeasurableSpace Ω] {X : Ω → Field} (hX : Measurable X) :
    Measurable (radFt X) := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun p : ℝ × Ω => radG X (dyUp n p.1) p.2 := fun n =>
    ((measurable_radG hX).comp (f := fun p : ℝ × Ω => (dyUp n p.1, p.2))
      (((measurable_dyUp n).comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hn).measurable

/-- **(R2), version part**: a.s. the radial part `z ↦ X_{|z|}(0)` agrees a.e. with `R(|z|)`
for some `R` continuous on `(0,∞)` -/
theorem ae_radial_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ∃ R : ℝ → ℝ, ContinuousOn R (Ioi 0) ∧ Measurable R ∧
      radialFun (X ω) =ᵐ[volume] fun z => R ‖z‖ := by
  obtain ⟨H, hHc, hHae⟩ := CircleAvg.exists_continuous_version_circleAvg hX
  have hg := measurable_radG hX.measurable
  have hFt := measurable_radFt hX.measurable
  -- the version agrees with the circle averages at all dyadic radii
  have hG : ∀ᵐ ω ∂P, ∀ n j : ℕ, H (((j : ℝ) + 1) / 2 ^ n) 0 ω = radG X (((j : ℝ) + 1) / 2 ^ n) ω := by
    simp only [ae_all_iff]
    intro n j
    exact hHae _ (by positivity) 0
  have hkey : ∀ ω, (∀ n j : ℕ, H (((j : ℝ) + 1) / 2 ^ n) 0 ω = radG X (((j : ℝ) + 1) / 2 ^ n) ω) →
      ∀ r : ℝ, 0 < r → radFt X (r, ω) = H r 0 ω := by
    intro ω hω r hr
    have hlim : Tendsto (fun n => H (dyUp n r) 0 ω) atTop (𝓝 (H r 0 ω)) := by
      have hc := ((hHc ω) (r, 0) ⟨hr, mem_univ _⟩).tendsto
      have ht : Tendsto (fun n : ℕ => ((dyUp n r, (0 : ℂ)) : ℝ × ℂ)) atTop
          (𝓝[Ioi 0 ×ˢ univ] (r, 0)) :=
        tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyUp hr.le).prodMk_nhds tendsto_const_nhds,
          Eventually.of_forall fun n =>
            (show ((dyUp n r, (0 : ℂ)) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) from
              ⟨dyUp_pos n r, mem_univ _⟩)⟩
      exact hc.comp ht
    have e : (fun n => radG X (dyUp n r) ω) = fun n => H (dyUp n r) 0 ω :=
      funext fun n => (hω n _).symm
    show limUnder atTop (fun n => radG X (dyUp n r) ω) = _
    rw [e]
    exact hlim.limUnder_eq
  have hS : MeasurableSet {p : Ω × ℂ | radFt X (‖p.2‖, p.1) = radG X ‖p.2‖ p.1} :=
    measurableSet_eq_fun
      (hFt.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
        ((measurable_norm.comp measurable_snd).prodMk measurable_fst))
      (hg.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
        ((measurable_norm.comp measurable_snd).prodMk measurable_fst))
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hF : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), radFt X (‖z‖, ω) = radG X ‖z‖ ω := by
    rw [Measure.ae_ae_comm hS]
    filter_upwards [hne] with z hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    filter_upwards [hG, hHae ‖z‖ hz' 0] with ω hω h1
    rw [hkey ω hω _ hz', h1]; rfl
  filter_upwards [hG, hF] with ω hω hFω
  refine ⟨(Ioi (0 : ℝ)).piecewise (fun r => H r 0 ω + circleAvg (X ω) 1 0) 0, ?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun r => H r 0 ω + circleAvg (X ω) 1 0) (Ioi 0) :=
      ((hHc ω).comp (continuous_id.prodMk continuous_const).continuousOn
        fun r hr => ⟨hr, mem_univ _⟩).add continuousOn_const
    exact hc.congr fun r hr => piecewise_eq_of_mem _ _ _ hr
  · exact ContinuousOn.measurable_piecewise
      (((hHc ω).comp (continuous_id.prodMk continuous_const).continuousOn
        fun r hr => ⟨hr, mem_univ _⟩).add continuousOn_const)
      continuousOn_const measurableSet_Ioi
  · filter_upwards [hFω, hne] with z h1 h2
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 h2
    rw [piecewise_eq_of_mem _ _ _ (show ‖z‖ ∈ Ioi (0 : ℝ) from hz'), ← hkey ω hω _ hz', h1]
    simp only [radialFun, radG]
    ring

end ConeArea4
end MatedCRTHarmonic.MoTPort
