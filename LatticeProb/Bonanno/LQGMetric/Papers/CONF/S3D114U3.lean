/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114U3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H5

/-!
# CONF Lemma 3.6 Step 1 (i), corrected form, and CONF Lemma 3.6 from Lemma 3.3

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 1, C:1341–1368; DEC-114 §4 C3.

**Statement correction.** `Conf36MeasNodeAEi` (S3D114T3) has no hypothesis on the position of `x`.
CONF chooses the grid point `z ∈ B_{ε𝕣}(𝓑^•_τ)` (C:1341, from `x ∈ ∂𝓑^•_τ`, C:1312), and the
inclusion `B_{5ρ̃ⁿ}(z) ⊆ 𝓑^•_{σ^ε}` of C:1366 rests on it (`ρ̃ⁿ ≤ ρⁿ(z) ≤ R^ε/6` needs `z` in the
index set of `R^ε_𝕣`, (3.16)). For `x` far from `𝓑^•_τ` (e.g. a constant point) the events
`E^{Ũ}_r(z)` at the radii `r ≤ ρ̃ⁿ` live near `z`, outside `𝓑^•_{σ^ε}`, and `G^ε_x` is not
determined by `(𝓑^•_{σ^ε}, h|)`. `Conf36MeasNodeAEiX` adds the hypothesis
`∀ᵐ ω, x ω ∈ ∂𝓑^•_τ` of `CONFLem3_6AtAE0` (where it is available, so the consumer is unchanged).

* `conf36_enbhd_subset_sigBall`: `B_{R^ε}(𝓑^•_τ) ⊆ 𝓑^•_{σ^ε}` (C:1300, via
  `t39g_enbhd_subset_interior`, given geodesics and bounded balls);
* `conf36_geo_omega`: the geometric input of `conf36_G_aeEventIn_of_geo` (C:1366, `(3.21)`);
* **`conf36MeasNodeAEiX_of`**: `Conf36MeasNodeAEiX γ D c p` from DFGPS Lemma 3.8 (`DFGPSLem3_8`,
  via `t39h_good_ae`: a.s. geodesics and bounded `D_h`-balls) for `γ ∈ (0,2)`, `0 < δ < 1/8`;
* `conf36_lem3_6AtAE0_of_iX`, **`conf36_lem3_6AtAE0_of_h38`**: `CONFLem3_6AtAE0 γ D c p` from
  `L33Gen γ D c p (fatG p)` (copy of `conf36_lem3_6AtAE0_of_D114`, S3D114W).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- **`B_{R^ε_𝕣(𝓑^•_τ)}(𝓑^•_τ) ⊆ 𝓑^•_{σ^ε}`** (CONF (3.17), C:1295–1300), given geodesics from
`z₀` and bounded `D_h`-balls -/
theorem conf36_enbhd_subset_sigBall {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ}
    {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {z₀ : ℂ}
    {R ε τ : ℝ} {ω : Ω} (hgeo : ∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w)
    (hbd : ∀ s : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s))
    (hne : (filledBall (D (h ω)) z₀ τ).Nonempty) :
    enbhd (confRK ξ cc D P h p R ε (filledBall (D (h ω)) z₀ τ) ω) (filledBall (D (h ω)) z₀ τ) ⊆
      filledBallE (D (h ω)) z₀ (confSigma ξ cc D P h p z₀ R ε τ ω) := by
  by_cases hσ : confSigma ξ cc D P h p z₀ R ε τ ω = ⊤
  · simp [filledBallE, hσ]
  have hτ0 : 0 < τ := by
    by_contra hτ
    rw [GM.gm_filledBall_nonpos _ _ (not_lt.1 hτ)] at hne
    exact not_nonempty_empty hne
  have hσ' : confSigma ξ cc D P h p z₀ R ε τ ω =
      ENNReal.ofReal (confSigma ξ cc D P h p z₀ R ε τ ω).toReal :=
    (ENNReal.ofReal_toReal hσ).symm
  have hτσ : τ ≤ (confSigma ξ cc D P h p z₀ R ε τ ω).toReal := by
    have h1 := t39g_le_confSigma ξ cc D P h p z₀ R ε τ ω
    rw [hσ'] at h1
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h1
  have := t39g_enbhd_subset_interior hσ' (hτ0.trans_le hτσ) hgeo (hbd _)
  refine this.trans (interior_subset.trans ?_)
  simp only [filledBallE, hσ, ↓reduceIte]
  exact subset_rfl

variable {Ω : Type} [MeasurableSpace Ω]

/-- **the geometric input** (CONF C:1366): for `x ∈ ∂𝓑^•_τ` and `1 ≤ n ≤ ⌊η log ε⁻¹⌋`,
`B_{5ρ̃ⁿ}(z) ⊆ 𝓑^•_{σ^ε}`, and `𝓑^•_{σ^ε} = ℂ` if `ρ̃ⁿ = ∞` -/
theorem conf36_geo_omega {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {p : CONFParams} {z₀ : ℂ} {R : ℝ} (hR : 0 < R) {τ : Ω → ℝ} {x : Ω → ℂ}
    {ε : Ω → ℝ} (hε : ∀ ω, ε ω ∈ Ioo 0 1) {ω : Ω}
    (hgeo : ∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w)
    (hbd : ∀ s : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s))
    (hx : x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) (n : ℕ) (hnN : n ≤ confN p (ε ω)) :
    (∀ k : ℤ, conf36Rho ξ cc D P h p (fun ω => ε ω * R)
        (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω =
        ENNReal.ofReal ((2 : ℝ) ^ k * (ε ω * R)) →
      ball (conf36Grid (ε ω * R / 4) (x ω)) (5 * ((2 : ℝ) ^ k * (ε ω * R))) ⊆
        filledBallE (D (h ω)) z₀ (confSigma ξ cc D P h p z₀ R (ε ω) (τ ω) ω)) ∧
    (conf36Rho ξ cc D P h p (fun ω => ε ω * R)
        (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω =
        ⊤ → ∀ ρ : ℝ, ball (conf36Grid (ε ω * R / 4) (x ω)) ρ ⊆
          filledBallE (D (h ω)) z₀ (confSigma ξ cc D P h p z₀ R (ε ω) (τ ω) ω)) := by
  set B := filledBall (D (h ω)) z₀ (τ ω) with hBdef
  set e := ε ω * R with hedef
  have he : 0 < e := mul_pos (hε ω).1 hR
  have hxB : x ω ∈ B := (GM.gm_filledBall_isClosed _ _ _).frontier_subset hx
  have hsub := conf36_enbhd_subset_sigBall (ξ := ξ) (cc := cc) (P := P) (p := p) (R := R)
    (ε := ε ω) hgeo hbd ⟨x ω, hxB⟩
  set z := conf36Grid (e / 4) (x ω) with hzdef
  have hzT : z ∈ gridPts (ε ω * R / 4) ∩ Metric.thickening (ε ω * R) B :=
    ⟨conf36Grid_mem _ _, Metric.mem_thickening_iff.2 ⟨x ω, hxB, by
      have := conf36Grid_norm_lt (m := e / 4) (by positivity) (x ω)
      rw [dist_comm, dist_eq_norm]; linarith⟩⟩
  have hxz : ‖x ω - z‖ < e / 2 := by
    have := conf36Grid_norm_lt (m := e / 4) (by positivity) (x ω)
    linarith
  have hle : ∀ r : ℝ, ENNReal.ofReal r ≤ conf36Rho ξ cc D P h p (fun ω => ε ω * R)
      (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω →
      6 * ENNReal.ofReal r ≤ confRK ξ cc D P h p R (ε ω) B ω := by
    intro r hr
    have h1 : ENNReal.ofReal r ≤ confRho ξ cc D P h p (ε ω * R) z (confN p (ε ω)) ω :=
      hr.trans ((conf36Rho_mono ω hnN).trans (conf36Rho_le_confRho ω _))
    have h2 := h1.trans (le_iSup₂_of_le (f := fun z' (_ : z' ∈ gridPts (ε ω * R / 4) ∩
      Metric.thickening (ε ω * R) B) =>
        confRho ξ cc D P h p (ε ω * R) z' (confN p (ε ω)) ω) z hzT le_rfl)
    unfold confRK
    exact le_add_right (by gcongr)
  have hRe : ENNReal.ofReal e ≤ confRK ξ cc D P h p R (ε ω) B ω := by
    unfold confRK; exact le_add_left le_rfl
  constructor
  · intro k hρ u hu
    have hr : 0 < (2 : ℝ) ^ k * e := mul_pos (zpow_pos (by norm_num) k) he
    have h6 := hle _ hρ.ge
    apply hsub
    show Metric.infEDist u B < confRK ξ cc D P h p R (ε ω) B ω
    have hux : dist u (x ω) < 5 * ((2 : ℝ) ^ k * e) + e / 2 := by
      have h1 : dist u z < 5 * ((2 : ℝ) ^ k * e) := hu
      have h2 : dist z (x ω) < e / 2 := by rw [dist_comm, dist_eq_norm]; exact hxz
      linarith [dist_triangle u z (x ω)]
    calc Metric.infEDist u B ≤ edist u (x ω) := Metric.infEDist_le_edist_of_mem hxB
      _ = ENNReal.ofReal (dist u (x ω)) := edist_dist _ _
      _ < ENNReal.ofReal (6 * ((2 : ℝ) ^ k * e) + e) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]; linarith
      _ = 6 * ENNReal.ofReal ((2 : ℝ) ^ k * e) + ENNReal.ofReal e := by
          rw [ENNReal.ofReal_add (by positivity) he.le, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
      _ ≤ confRK ξ cc D P h p R (ε ω) B ω := by
          unfold confRK at h6 ⊢
          gcongr
          exact (le_iSup₂_of_le (f := fun z' (_ : z' ∈ gridPts (ε ω * R / 4) ∩
            Metric.thickening (ε ω * R) B) =>
              confRho ξ cc D P h p (ε ω * R) z' (confN p (ε ω)) ω) z hzT
            ((hρ.ge).trans ((conf36Rho_mono ω hnN).trans (conf36Rho_le_confRho ω _))))
  · intro htop ρ u _
    apply hsub
    have hRK : confRK ξ cc D P h p R (ε ω) B ω = ⊤ := by
      have h1 : conf36Rho ξ cc D P h p (fun ω => ε ω * R)
          (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω ≤
          confRho ξ cc D P h p (ε ω * R) z (confN p (ε ω)) ω :=
        (conf36Rho_mono ω hnN).trans (conf36Rho_le_confRho ω _)
      rw [htop, top_le_iff] at h1
      have h2 := le_iSup₂_of_le (f := fun z' (_ : z' ∈ gridPts (ε ω * R / 4) ∩
        Metric.thickening (ε ω * R) B) =>
          confRho ξ cc D P h p (ε ω * R) z' (confN p (ε ω)) ω) z hzT h1.ge
      rw [top_le_iff] at h2
      unfold confRK
      rw [h2, ENNReal.mul_top (by norm_num), top_add]
    show Metric.infEDist u B < confRK ξ cc D P h p R (ε ω) B ω
    rw [hRK]
    exact lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hxB) (edist_lt_top _ _)

/-- **Step 1, part (i), corrected** (CONF C:1341–1368): `Conf36MeasNodeAEi` with the hypothesis
`x ∈ ∂𝓑^•_τ` a.s. (CONF C:1312; present in `CONFLem3_6AtAE0`) -/
def Conf36MeasNodeAEiX (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  IsWeakLQGMetric γ D c →
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTimeAE P D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ mΩ →
      ∀ (x : Ω → ℂ) (ε : Ω → ℝ),
      @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x →
      @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε →
      (∀ᵐ ω ∂P, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) →
      (∀ ω, ε ω ∈ Ioo 0 1) → (Set.range ε).Countable →
      AEEventIn P (filledBallSigmaAt0 D h z₀
          (fun ω => confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω))
        (conf36G (fatG p) (xiGamma γ) c D P h p ε (fun ω => ε ω * R)
          (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)))

/-- **`Conf36MeasNodeAEiX` holds** for `γ ∈ (0,2)`, `0 < δ < 1/8`, given DFGPS Lemma 3.8 -/
theorem conf36MeasNodeAEiX_of (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) :
    Conf36MeasNodeAEiX γ D c p := by
  intro hD Ω mΩ P _ h hh z₀ R hR τ _ hloc _ x ε hx hε hxf hε1 hεc
  have hgood := t39h_good_ae h38 hγ hγ2 hD P h hh z₀
  have hBc : ∀ ω, IsClosed (filledBall (D (h ω)) z₀ (τ ω)) := fun ω =>
    conf36_isClosed_filledBall _ _ _
  have hB'c : ∀ ω, IsClosed (filledBallE (D (h ω)) z₀
      (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω)) := fun ω =>
    GM.p412i_filledBallE_isClosed _ _ _
  have hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (filledBallE (D (h ω)) z₀
      (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω)) ∨
      filledBallE (D (h ω)) z₀ (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω) = univ := by
    filter_upwards [hgood] with ω hω
    by_cases hσ : confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω = ⊤
    · right; simp [filledBallE, hσ]
    · left; simp only [filledBallE, hσ, ↓reduceIte]; exact (GM.jb_isCompact_filledBall (hω.2 _)).isBounded
  have hBb : ∀ᵐ ω ∂P, Bornology.IsBounded (filledBall (D (h ω)) z₀ (τ ω)) := by
    filter_upwards [hgood] with ω hω
    exact (GM.jb_isCompact_filledBall (hω.2 _)).isBounded
  have hBB : ∀ᵐ ω ∂P, filledBall (D (h ω)) z₀ (τ ω) ⊆ filledBallE (D (h ω)) z₀
      (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω) := by
    refine Eventually.of_forall fun ω => ?_
    by_cases hσ : confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω = ⊤
    · simp [filledBallE, hσ]
    simp only [filledBallE, hσ, ↓reduceIte]
    by_cases hτ : τ ω ≤ 0
    · rw [GM.gm_filledBall_nonpos _ _ hτ]; exact empty_subset _
    refine GM.gm_filledBall_mono _ _ ?_
    have h1 := ENNReal.toReal_mono hσ (t39g_le_confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω)
    rwa [ENNReal.toReal_ofReal (not_le.1 hτ).le] at h1
  exact conf36_G_aeEventIn_of_geo hδ hδ8 hD hh hBc hB'c hA'
    (fun hY => conf36_trace_mono_ae h hBc hBb hloc hB'c hA' hBB hY) hR x ε hx hε hε1 hεc
    (by
      filter_upwards [hgood, hxf] with ω hω hxω
      intro n _ hnN
      exact conf36_geo_omega hR hε1 hω.1 hω.2 hxω n hnN)

/-- **CONF Lemma 3.6** (`CONFLem3_6AtAE0`) from Lemma 3.3 for `fatG` and the corrected Step 1
part (i) (copy of `conf36_lem3_6AtAE0_of_D114`, S3D114W, with `Conf36MeasNodeAEiX`) -/
theorem conf36_lem3_6AtAE0_of_iX {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    {p : CONFParams} (hp : p.Valid) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    (h33 : L33Gen γ D c p (fatG p)) (H : Conf36MeasNodeAEiX γ D c p) :
    CONFLem3_6AtAE0 γ D c p := by
  have hS := conf36StepNodeAE_fatG (γ := γ) (D := D) (c := c) hp.2.2.1 hδ8
  have hcc : ∀ r, 0 < r → 0 < c r := hD.tightness.1
  have hIn : L36Step2Input p (fatG p) := l36Step2Input_fatG' hp.1 hp.2.2.1 hδ8
  obtain ⟨𝔭, h𝔭, H33⟩ := h33
  set 𝔭' := min 𝔭 (1 / 2) with h𝔭'
  have h𝔭'0 : 0 < 𝔭' := lt_min h𝔭 (by norm_num)
  have h𝔭'1 : 𝔭' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have H33' : L33GenAt γ D c p (fatG p) 𝔭' :=
    l33GenAt_mono (min_le_left _ _) (fun P _ h => H33 P h)
  obtain ⟨α, C₀, hα, hC₀, hrate⟩ := conf36_rate h𝔭'0 h𝔭'1 hp.2.2.2.2.2
  refine ⟨α, C₀, hα, hC₀, fun {Ω} _ P _ h hh z₀ R hR τ hτ hloc hle x ε hx hε hxf hε1 hεc => ?_⟩
  have hGm := H hD P h hh z₀ R hR τ hτ hloc hle x ε hx hε hxf hε1 hεc
  have hFm := fun n => conf36_Gt_aeEventIn hp.2.2.1 hδ8 hD hh z₀ hR τ hle x ε hx hε hε1 hεc n
  refine ⟨_, hGm, conf36_propA hIn hcc hp.2.2.1 hR hε1, ?_⟩
  have hN : @Measurable Ω ℕ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _
      (fun ω => confN p (ε ω)) := by
    have hg : Measurable (fun t : ℝ => ⌊p.η * Real.log t⁻¹⌋₊) :=
      (measurable_const.mul (Real.measurable_log.comp measurable_inv)).nat_floor
    exact hg.comp hε
  have hB := conf36_propB_of_steps_ae hle hFm hN h𝔭'0 h𝔭'1
    (hS 𝔭' h𝔭'0 h𝔭'1 H33' hD P h hh z₀ R hR τ hτ hloc hle x ε hx hε hxf hε1 hεc)
  filter_upwards [hB] with ω hω
  refine le_trans ?_ hω
  have := hrate (ε ω) (hε1 ω)
  unfold confN
  linarith

/-- **CONF Lemma 3.6** (`CONFLem3_6AtAE0`) from CONF Lemma 3.3 for `fatG` (`L33Gen`) and DFGPS
Lemma 3.8, for `γ ∈ (0,2)`, valid `p` with `δ < 1/8` -/
theorem conf36_lem3_6AtAE0_of_h38 (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} (hp : p.Valid) (hδ8 : p.δ < 1 / 8)
    (hD : IsWeakLQGMetric γ D c) (h33 : L33Gen γ D c p (fatG p)) : CONFLem3_6AtAE0 γ D c p :=
  conf36_lem3_6AtAE0_of_iX hp hδ8 hD h33 (conf36MeasNodeAEiX_of h38 hγ hγ2 hp.2.2.1 hδ8)

end LQGMetric.CONF
