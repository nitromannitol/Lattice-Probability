/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcL1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcI1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcK
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12

/-!
# D124 packet I3, part 1: DZZ's sandwich on the mixed samples (P2-DZZI3)

Decision D124 (`decisions/DEC-124.md` §1, §5 I3). Source: DZZ (arXiv:1807.00422,
`LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1584–1587: for coarse configurations `𝐱_δ`, `𝐱'_δ`
with `‖𝐱_δ − 𝐱'_δ‖_∞ ≤ ℓ`, Lemma 3.8 (`lem-LGD-compare`, l. 1218–1233; here with `a = 1`,
`b₁ = 0` since both chaos limits are normalised by `tildeVar`, and `b₂ = ℓ`) gives, for almost
every fine configuration `𝐲_δ`,
`D_{γ, δ' e^{γℓ/2}, 𝐱_δ} ≤ D_{γ, δ', 𝐱'_δ} ≤ D_{γ, δ' e^{−γℓ/2}, 𝐱_δ}`.

On `Ω × Ω` with the mixing white noise `W̃ = wnMix W κ δ` (S3D124, S3ConcI1), the configuration
`(𝐱_δ, 𝐲_δ)` is the pair `(ω₁, ω₂)`. The field difference between `(ω₁, ω₂)` and `(ω₁', ω₂)` is
exactly the difference of the coarse fields at `ω₁`, `ω₁'` (`tildeHInf_wnMix_sub`: the fine terms
cancel); it is read at the rational points of `𝕍` (coarse indices) and extended to `𝕍` by the
continuity of the versions `coarseVer` (`kcGrid`, S3ConcK). The null sets (versions at the
countably many `(n, v)`, the chaos limit) are sliced by `measure_ae_null_of_prod_null` (Fubini,
no measurability needed).

* `wall_ball_le`: a ball comparison `μ(B) ≤ e^c ν(B)`, `c ≥ 0`, passes to `dzzWall K`;
* `lgdMinSet_sandwich`: the two-sided comparison of Lemma 3.8 from ball comparisons
  (`lgdDZZ_le_of_ball_le`, S3L8);
* **`ae_sandwich_wnMix`**: DZZ l. 1584–1587 on the mixed samples, for every wall `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {κ δ : ℝ}

/-- A ball comparison with constant `e^c ≥ 1` passes to the walled measures. -/
lemma wall_ball_le {μ ν : Measure ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (x : ℚ × ℚ) (r : ℝ),
      μ (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * ν (Metric.ball (ratPt x) r))
    (K : Set ℂ) (x : ℚ × ℚ) (r : ℝ) :
    dzzWall K μ (Metric.ball (ratPt x) r) ≤
      ENNReal.ofReal (Real.exp c) * dzzWall K ν (Metric.ball (ratPt x) r) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp c) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hc)
  simp only [dzzWall, Measure.add_apply, mul_add]
  exact add_le_add (h x r) (le_mul_of_one_le_left' h1)

/-- Lemma 3.8's two-sided comparison (`min` over `A × B`) from two ball comparisons. -/
lemma lgdMinSet_sandwich {μ ν : Measure ℂ} {c : ℝ}
    (h12 : ∀ (x : ℚ × ℚ) (r : ℝ),
      μ (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * ν (Metric.ball (ratPt x) r))
    (h21 : ∀ (x : ℚ × ℚ) (r : ℝ),
      ν (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * μ (Metric.ball (ratPt x) r))
    (δ' : ℝ) (A B : Set ℂ) :
    lgdMinSet μ (δ' * Real.exp (c / 2)) A B ≤ lgdMinSet ν δ' A B ∧
      lgdMinSet ν δ' A B ≤ lgdMinSet μ (δ' * Real.exp (-(c / 2))) A B := by
  constructor
  · refine iInf₂_mono fun u _ => iInf₂_mono fun v _ => ?_
    have := lgdDZZ_le_of_ball_le h12 (δ' * Real.exp (c / 2)) u v
    rwa [mul_assoc, ← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero, mul_one] at this
  · refine iInf₂_mono fun u _ => iInf₂_mono fun v _ => ?_
    have := lgdDZZ_le_of_ball_le h21 δ' u v
    rwa [neg_div] at this

/-- The rational grid points `kcGrid m z` of `𝕍` converge to `z`. -/
lemma tendsto_kcGrid (z : ℂ) : Tendsto (fun m : ℕ => kcGrid m z) atTop (𝓝 z) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) (?_ : Tendsto
    (fun m : ℕ => 2 * (2 : ℝ)⁻¹ ^ m) atTop (𝓝 0))
  · rw [dist_comm]; exact kcGrid_dist m z
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul (2 : ℝ)

/-- A continuous function bounded by `ℓ` at the rational points of `𝕍` is bounded on `𝕍`. -/
lemma abs_le_of_ratPt {f : ℂ → ℝ} (hf : Continuous f) {ℓ : ℝ}
    (h : ∀ z ∈ dzzV, IsRatPt z → |f z| ≤ ℓ) {z : ℂ} (hz : z ∈ dzzV) : |f z| ≤ ℓ :=
  le_of_tendsto ((continuous_abs.comp hf).continuousAt.tendsto.comp (tendsto_kcGrid z))
    (Eventually.of_forall fun m => h _ (kcGrid_mem m hz) (kcGrid_rat m z))

lemma isCoarseScale_max (κ δ : ℝ) (n : ℕ) :
    IsCoarseScale κ δ (max ((2 : ℝ)⁻¹ ^ n) (δ ^ κ)) := by
  rcases le_total (δ ^ κ) ((2 : ℝ)⁻¹ ^ n) with h | h
  · exact Or.inr ⟨n, max_eq_left h, (max_eq_left h).symm ▸ h⟩
  · exact Or.inl (max_eq_right h)

/-- The good property of a mixed sample: the versions agree with the field at the rational points
and the dyadic scales, and the chaos limit holds. -/
def SandGood (hW : IsWhiteNoise (P.prod P) (wnMix W κ δ)) (γ : ℝ) (p : Ω × Ω) : Prop :=
  (∀ (n : ℕ) (a b : ℚ), coarseVer hW n ⟨a, b⟩ p =
      tildeHInf (wnMix W κ δ) ((2 : ℝ)⁻¹ ^ n) ⟨a, b⟩ p) ∧
    IsChaosLimit γ (fun s z => wickZeta hW s z p) tildeVar (fun n => (1 / 2 : ℝ) ^ n)
      (wickQArea γ (wnMix W κ δ) p)

lemma ae_sandGood (hW' : IsWhiteNoise (P.prod P) (wnMix W κ δ)) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : ∀ᵐ p ∂(P.prod P), SandGood hW' γ p := by
  have h1 : ∀ᵐ p ∂(P.prod P), ∀ (n : ℕ) (a b : ℚ), coarseVer hW' n ⟨a, b⟩ p =
      tildeHInf (wnMix W κ δ) ((2 : ℝ)⁻¹ ^ n) ⟨a, b⟩ p := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
    exact (coarseVer_spec hW' n).2.2 ⟨a, b⟩
  filter_upwards [h1, isChaosLimit_wickQArea_of_tight hW' hγ hγ2 (ae_stripTight hW' γ)]
    with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- The deterministic step: on two good mixed samples sharing the fine part, a coarse bound `ℓ`
gives the ball comparison of the chaos measures with constant `e^{γℓ}`. -/
lemma ball_le_of_sandGood (hW' : IsWhiteNoise (P.prod P) (wnMix W κ δ)) {γ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 0 < δ) {ω₁ ω₁' ω₂ : Ω} (h₁ : SandGood hW' γ (ω₁, ω₂)) (h₂ : SandGood hW' γ (ω₁', ω₂))
    {ℓ : ℝ}
    (hℓ : ∀ q : CoarsePt κ δ,
      |coarseField W κ δ (Sum.inr q) ω₁ - coarseField W κ δ (Sum.inr q) ω₁'| ≤ ℓ)
    (x : ℚ × ℚ) (r : ℝ) :
    wickQArea γ (wnMix W κ δ) (ω₁, ω₂) (Metric.ball (ratPt x) r) ≤
      ENNReal.ofReal (Real.exp (γ * ℓ)) *
        wickQArea γ (wnMix W κ δ) (ω₁', ω₂) (Metric.ball (ratPt x) r) ∧
    wickQArea γ (wnMix W κ δ) (ω₁', ω₂) (Metric.ball (ratPt x) r) ≤
      ENNReal.ofReal (Real.exp (γ * ℓ)) *
        wickQArea γ (wnMix W κ δ) (ω₁, ω₂) (Metric.ball (ratPt x) r) := by
  -- the coupling bound (eq-coupling-two-fields) with `b₂ = ℓ` on `𝕍`
  have hcoup : ∀ n : ℕ, ∀ z ∈ dzzV, |wickZeta hW' ((1 / 2 : ℝ) ^ n) z (ω₁, ω₂) -
      wickZeta hW' ((1 / 2 : ℝ) ^ n) z (ω₁', ω₂)| ≤ ℓ := by
    intro n z hz
    simp only [wickZeta_pow]
    refine abs_le_of_ratPt (f := fun z => coarseVer hW' n z (ω₁, ω₂) - coarseVer hW' n z (ω₁', ω₂))
      (((coarseVer_spec hW' n).1 _).sub ((coarseVer_spec hW' n).1 _)) ?_ hz
    rintro z hz ⟨a, b, rfl⟩
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [h₁.1 n a b, h₂.1 n a b, tildeHInf_wnMix_sub W hδ hε]
    exact hℓ ⟨(⟨a, b⟩, max ((2 : ℝ)⁻¹ ^ n) (δ ^ κ)), hz, ⟨a, b, rfl⟩, isCoarseScale_max κ δ n⟩
  constructor
  · exact chaos_ratBall_le h₁.2 h₂.2 (fun n z hz => by
      have := (abs_le.mp (hcoup n z hz)).2
      nlinarith [mul_le_mul_of_nonneg_left this hγ]) x r
  · exact chaos_ratBall_le h₂.2 h₁.2 (fun n z hz => by
      have := (abs_le.mp (hcoup n z hz)).1
      nlinarith [mul_le_mul_of_nonneg_left this hγ]) x r

/-- **DZZ's sandwich on the mixed samples** (DZZ l. 1584–1587; Lemma 3.8 with `a = 1`, `b₁ = 0`,
`b₂ = ℓ`): there is a full-measure set `G₁` of coarse samples such that for `ω₁, ω₁' ∈ G₁` whose
coarse fields differ by at most `ℓ` at the coarse points, for almost every fine sample `ω₂` and
every wall `K`, `D_{δ'e^{γℓ/2}}(ω₁, ω₂) ≤ D_{δ'}(ω₁', ω₂) ≤ D_{δ'e^{−γℓ/2}}(ω₁, ω₂)`. -/
theorem ae_sandwich_wnMix (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hδ : 0 < δ) :
    ∃ G₁ : Set Ω, P G₁ᶜ = 0 ∧ ∀ ω₁ ∈ G₁, ∀ ω₁' ∈ G₁, ∀ ℓ : ℝ, 0 ≤ ℓ →
      (∀ q : CoarsePt κ δ,
        |coarseField W κ δ (Sum.inr q) ω₁ - coarseField W κ δ (Sum.inr q) ω₁'| ≤ ℓ) →
      ∀ᵐ ω₂ ∂P, ∀ (K : Set ℂ) (δ' : ℝ) (A B : Set ℂ),
        lgdMinSet (dzzWall K (dzzMuIn γ (wnMix W κ δ) (ω₁, ω₂))) (δ' * Real.exp (γ * ℓ / 2))
            A B ≤ lgdMinSet (dzzWall K (dzzMuIn γ (wnMix W κ δ) (ω₁', ω₂))) δ' A B ∧
          lgdMinSet (dzzWall K (dzzMuIn γ (wnMix W κ δ) (ω₁', ω₂))) δ' A B ≤
            lgdMinSet (dzzWall K (dzzMuIn γ (wnMix W κ δ) (ω₁, ω₂)))
              (δ' * Real.exp (-(γ * ℓ / 2))) A B := by
  have hP := hW.isProbabilityMeasure
  have hW' := isWhiteNoise_wnMix hW κ δ
  have hnull : (P.prod P) {p | ¬ SandGood hW' γ p} = 0 := ae_iff.1 (ae_sandGood hW' hγ hγ2)
  have hsl := Measure.measure_ae_null_of_prod_null hnull
  refine ⟨{ω₁ | P (Prod.mk ω₁ ⁻¹' {p | ¬ SandGood hW' γ p}) = 0}, ?_, ?_⟩
  · have := ae_iff.1 hsl
    simpa only [Pi.zero_apply, compl_ofPred] using this
  intro ω₁ hω₁ ω₁' hω₁' ℓ hℓ0 hℓ
  have g₁ : ∀ᵐ ω₂ ∂P, SandGood hW' γ (ω₁, ω₂) := by
    rw [ae_iff]; exact hω₁
  have g₂ : ∀ᵐ ω₂ ∂P, SandGood hW' γ (ω₁', ω₂) := by
    rw [ae_iff]; exact hω₁'
  filter_upwards [g₁, g₂] with ω₂ h₁ h₂ K δ' A B
  have hb := ball_le_of_sandGood hW' hγ.le hδ h₁ h₂ hℓ
  have hc : 0 ≤ γ * ℓ := mul_nonneg hγ.le hℓ0
  have w12 := wall_ball_le hc (fun x r => (wall_ball_le hc (fun x r => (hb x r).1) dzzV x r)) K
  have w21 := wall_ball_le hc (fun x r => (wall_ball_le hc (fun x r => (hb x r).2) dzzV x r)) K
  exact lgdMinSet_sandwich w12 w21 δ' A B

end DZZ
end LQGMetric
