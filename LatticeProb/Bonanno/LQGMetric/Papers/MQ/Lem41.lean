/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.Lem41 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.RNMoment
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Cutoff
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.ZBCM
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepZB
import LatticeProb.Bonanno.LQGMetric.Blueprint.MQGeodesic

/-!
# MQ Lemma 4.1 with general radii (`Blueprint.MQLem4_1Gen`) (task P2-MQ)

Source: J. Miller, W. Qian, *The geodesics in Liouville quantum gravity are not
Schramm–Loewner evolutions*, arXiv:1812.03913, `literature/src/1812.03913/lqg_geodesics.tex`,
Lemma 4.1 (`lem:good_scale_rn`, l. 549–563) and its proof (l. 566–589). MQ's proof, step by step,
with general radii `ρ₁ r < ρ₂ r < r` and centring constant `a` (decision D41):

1. cut-off (l. 566–572): `F = (g − a) χ ∈ C_c^∞(B(z, r))`, `F = g − a` on `B(z, ρ₁ r)`
   (`exists_cutoff_harm`), so on `B(z, ρ₁ r)` the field `h̃ + G` agrees with `h̃ + F`;
2. Cameron–Martin (l. 576–580): the law of `h̃ + F` is the `exp((h̃, F)_∇ − (F, F)_∇/2)`-tilt of
   the law of `h̃` (`map_tiltMeasure_cmSigma`);
3. energy bound (l. 580–583, MQ (4.1)): `(F, F)_∇ ≤ K₀(ρ₁, ρ₂, M)` (`exists_cutoff_harm`);
4. Jensen for the restriction (l. 585–589): the moments of the RN derivatives of the restricted
   laws are bounded by those of the Cameron–Martin density (`rnDeriv_map_moments_le`), which
   are `exp(q(q − 1)(F, F)_∇ / 2)` (`lintegral_rnDeriv_tilt_rpow`).

* `mqLem4_1Gen` : `Blueprint.MQLem4_1Gen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open scoped ENNReal

namespace LQGMetric.MQ

open QuantumZipper QuantumZipper.CameronMartin MarkovZB Blueprint

/-- two measures on `𝒟'(V)` (cylinder σ-algebra) agree if their laws of pairings agree -/
lemma measure_distOn_ext {V : Opens ℂ} {μ ν : Measure (DistOn V)}
    (h : μ.map (fun T (φ : TestOn V) => T φ) = ν.map (fun T (φ : TestOn V) => T φ)) : μ = ν := by
  have hev : Measurable (fun (T : DistOn V) (φ : TestOn V) => T φ) :=
    measurable_iff_comap_le.2 le_rfl
  ext s hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  rw [← Measure.map_apply hev ht, ← Measure.map_apply hev ht, h]

/-- **MQ Lemma 4.1, general radii and centring** (`Blueprint.MQLem4_1Gen`). -/
theorem mqLem4_1Gen : MQLem4_1Gen := by
  intro ρ₁ ρ₂ h0 h12 h2 M hM p
  obtain ⟨K₀, hK₀⟩ := exists_cutoff_harm h0 h12 h2 hM
  set K₁ := max K₀ 0
  set e := Real.exp (|p * (p - 1)| * K₁ / 2)
  refine ⟨max 2 e, lt_of_lt_of_le two_pos (le_max_left _ _), ?_⟩
  intro z r hr Ω _ P _ ht hht hzb g hg a hb G hG
  dsimp only
  set U := ballO z r
  set B := ballO z (ρ₁ * r)
  have hBU : B ≤ U := fun x hx => by
    change x ∈ ball z (ρ₁ * r) at hx
    exact ball_subset_ball (by nlinarith) hx
  have hadm : ZBAdmissible U := zbAdmissible_of_isBounded isBounded_ball
  have hne : (U : Set ℂ).Nonempty := ⟨z, mem_ball_self hr⟩
  set X : TestOn U → Ω → ℝ := fun φ ω => restrictTo U (ht ω) φ
  have hX : IsZBGFFProcess U X P := hzb.process
  obtain ⟨F, hF, hFeq, hE⟩ := hK₀ z r hr g hg a hb
  set f : zsSub (U : Set ℂ) := ⟨F, hF⟩
  set Q := tiltMeasure X P (cmSigma f)
  have hQ : IsProbabilityMeasure Q :=
    isProbabilityMeasure_tiltMeasure hX.gaussian hX.measurable hX.centered _
  set R : Ω → DistOn B := fun ω => restrictTo B (ht ω)
  have hRm : Measurable R := (measurable_restrictTo B).comp hht
  have hpath : Measurable fun ω (j : TestOn U) => X j ω := measurable_pi_iff.mpr hX.measurable
  set π' : (TestOn U → ℝ) → (TestOn B → ℝ) := fun x φ => x (GM.testIncl B U φ)
  have hπ : Measurable π' := measurable_pi_iff.2 fun φ => measurable_pi_apply _
  have hev : Measurable (fun (T : DistOn B) (φ : TestOn B) => T φ) :=
    measurable_iff_comap_le.2 le_rfl
  -- `G = F` on `B`
  have hGF : ∀ φ : TestOn B, restrictTo B G φ = ∫ x, F x * φ x := by
    intro φ
    rw [GM.restrictTo_apply_testIncl hBU, hG, GM.coe_testIncl hBU]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ (B : Set ℂ)
    · simp only; rw [hFeq x hx]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
      simp [this]
  -- step 2: `μg` is the push-forward of the tilt
  have hμg : P.map (fun ω => restrictTo B (ht ω + G)) = Q.map R := by
    refine measure_distOn_ext ?_
    have hR' : Measurable fun ω => restrictTo B (ht ω + G) :=
      measurable_distOn_iff.2 fun φ =>
        ((measurable_distOn_apply φ).comp hRm).add_const (restrictTo B G φ)
    rw [Measure.map_map hev hR', Measure.map_map hev hRm]
    have e1 : (fun T (φ : TestOn B) => T φ) ∘ R = π' ∘ fun ω j => X j ω := by
      funext ω φ
      exact GM.restrictTo_apply_testIncl hBU (ht ω) φ
    rw [e1, ← Measure.map_map hπ hpath, map_tiltMeasure_cmSigma hadm hne hX f,
      Measure.map_map hπ (measurable_pi_iff.mpr fun j => (hX.measurable j).add_const _)]
    congr 1
    funext ω φ
    simp only [Function.comp_apply, π']
    rw [GM.coe_testIncl hBU]
    have e2 : restrictTo B (ht ω + G) φ = restrictTo B (ht ω) φ + restrictTo B G φ := rfl
    rw [e2, hGF, GM.restrictTo_apply_testIncl hBU]
  -- absolute continuity
  have hDm : Measurable fun ω => ((tiltDensity X P (cmSigma f) ω).toNNReal : ℝ≥0∞) :=
    (measurable_tiltDensity hX.gaussian hX.measurable _).real_toNNReal.coe_nnreal_ennreal
  have h1 : Q ≪ P := withDensity_absolutelyContinuous _ _
  have h2 : P ≪ Q := withDensity_absolutelyContinuous' hDm.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
      exact Real.exp_pos _)
  -- the energy
  have hK : covNorm X P (cmSigma f) ≤ K₁ :=
    (covNorm_cmSigma hadm hX f).le.trans (hE.trans (le_max_left _ _))
  have hK0 : 0 ≤ covNorm X P (cmSigma f) := by
    rw [covNorm_cmSigma hadm hX f]; exact K3.energy_nonneg _ _
  have hC : ∀ q : ℝ, (q = p ∨ q = 1 - p) →
      ∫⁻ x, (Q.rnDeriv P x) ^ q ∂P ≤ ENNReal.ofReal e := by
    intro q hq
    rw [lintegral_rnDeriv_tilt_rpow hX.gaussian hX.measurable hX.centered]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hqq : q * (q - 1) = p * (p - 1) := by rcases hq with rfl | rfl <;> ring
    rw [hqq]
    have := mul_le_mul (le_abs_self (p * (p - 1))) hK hK0 (abs_nonneg _)
    linarith
  obtain ⟨m1, m2⟩ := rnDeriv_map_moments_le h1 h2 hRm p hC
  have hc : max 2 (ENNReal.ofReal e) = ENNReal.ofReal (max 2 e) := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hμg]; exact h1.map hRm
  · rw [hμg]; exact h2.map hRm
  · rw [hμg, ← hc]; exact m1
  · rw [hμg, ← hc]; exact m2

end LQGMetric.MQ
