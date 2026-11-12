/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L34 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm2

/-!
# CONF Lemma 3.4 from CONF Lemmas 3.2 and 2.12

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), `literature/src/1905.00381/confluence-final.tex`, proof of Lemma 3.4
(C:1269–1271): "Since each `E_r(z)` is determined by `(h − h_r(z))|_{𝔸_{2r,5r}(z)}`, this follows by
combining Lemma 2.12 (applied with `r_k = 8^k𝕣`, `S₁ = 2`, `S₂ = 5`, …) and Lemma 3.2."

* `CONFLem3_2` : **CONF Lemma 3.2** (`lem-clsce-event-pos`, C:1163–1165), verbatim (open).
* `CONFEMeas` : CONF C:1270 (and C:1150–1154): `E_r(z)` is (a.s.) an event of
  `σ((h − h_r(z))|_{𝔸_{2r,5r}(z)})` (open).
* `CONFLem2_12aP` : **CONF Lemma 2.12 (1)** (`lem-annulus-iterate-inverse`, C:785–795) **as
  printed**: `E_{r_k} ∈ σ((h − h_{r_k}(0))|_{𝔸_{S₁r_k,S₂r_k}(0)})` (open). The project's
  `CONF.CONFLem2_12a` (decision D47) asks for measurability for **every** normalization radius
  `ρ`, i.e. events determined modulo additive constants; `E_r(z)` is *not* of that kind
  (condition 1 compares `D_h(∂B_{2r},∂B_{3r})` with `e^{ξh_r(z)}`, and `h_r(z) − h_{3r}(z)` is not
  a function of `h|_{𝔸_{2r,5r}(z)}` modulo constants), so D47's form does not apply to L3.4.
* `confRho_le_of_count` : the good-radius chain (deterministic, implicit at C:1270): if at least
  `n` of the radii `8^k𝕣`, `k ∈ [1,K]`, are good then `ρ^n_𝕣(z) ≤ 8^K𝕣`.
* `confLem3_4_of` : **CONF Lemma 3.4** from the three statements above.

Constants (C:1270 writes "`a = log q`, `b = 1/2`, `K = ⌊log₆ C⌋`"): we take `b = 1/2`,
`K = ⌊log₈ C⌋`, `a = q log 8` (so that `e^{−aK} ≤ 8^q C^{−q}`), `η = 1/(4 log 8)` and `C ≥ 64`
(so that `⌊η log C⌋ ≤ K/2`). Proposed deviation DV-CONF-34.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Lemma 3.2** (`lem-clsce-event-pos`, C:1163–1165): "For each `p ∈ (0,1)`, we can find
parameters `c, δ ∈ (0,1)` and `A > 0` such that … `P[E_r(z)] ≥ p` for each `z ∈ ℂ` and `r > 0`."
(`η` plays no role in `E_r(z)`; any `η > 0` is allowed by `Valid`.) -/
def CONFLem3_2 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) : Prop :=
  ∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 → ∃ p : CONFParams, p.Valid ∧ p.δ < 1 / 8 ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
        ENNReal.ofReal p₀ ≤ P (confE (xiGamma γ) c D P h p r z)

/-- CONF C:1270 (C:1150–1154): "each `E_r(z)` is determined by `(h − h_r(z))|_{𝔸_{2r,5r}(z)}`",
in the almost sure form, with the annulus `𝔸_{3r/2,5r}(z)` (∂B_{2r}(z), used by condition 1, is not
inside the open annulus `𝔸_{2r,5r}(z)`; proposed DV-CONF-EMeas). Reduced to `CONFHarmLocN` in
`S3EMeas.lean`. -/
def CONFEMeas (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) : Prop :=
  ∀ p : CONFParams, p.Valid →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∃ F : Set Ω,
      MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
        (annulus z (3 / 2 * r) (5 * r))] F ∧ F =ᵐ[P] confE (xiGamma γ) c D P h p r z

/-- **CONF Lemma 2.12 (1)** (C:785–795) as printed: events
`E_{r_k} ∈ σ((h − h_{r_k}(0))|_{𝔸_{S₁r_k,S₂r_k}(0)})`. -/
def CONFLem2_12aP : Prop :=
  ∀ S₁ S₂ : ℝ, 1 < S₁ → S₁ < S₂ → ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → b < 1 →
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
        (∀ k, 0 < r k) → (∀ k, S₂ ≤ r (k + 1) / r k) →
        (∀ k, MeasurableSet[fieldSigma
          (fun ω => addConst (h ω) (-circleAvg (h ω) (r k) 0)) (annulus 0 (S₁ * r k) (S₂ * r k))]
            (E k)) →
        (∀ k, ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K))

/-! ## The good-radius chain -/

open Classical in
theorem countOcc_succ {Ω : Type} (E : ℕ → Set Ω) (K : ℕ) (ω : Ω) :
    countOcc E (K + 1) ω = countOcc E K ω + if ω ∈ E (K + 1) then 1 else 0 := by
  unfold countOcc
  have hI : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- the radii `8^k 𝕣 = 2^{3k} 𝕣` -/
def rad8 (R : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ ((3 * k : ℕ) : ℤ) * R

/-- **the good-radius chain** (implicit at C:1270): if at least `n` of the radii `8^k𝕣`,
`k ∈ [1,K]`, are good (`E_{8^k𝕣}(z)` occurs), then `ρ^n_𝕣(z) ≤ 8^K𝕣`. -/
theorem confRho_le_of_count {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (p : CONFParams) {R : ℝ}
    (hR : 0 < R) (z : ℂ) (ω : Ω) :
    ∀ K n : ℕ, n ≤ countOcc (fun k => confE ξ cc D P h p (rad8 R k) z) K ω →
      confRho ξ cc D P h p R z n ω ≤ ENNReal.ofReal (rad8 R K) := by
  intro K
  induction K with
  | zero =>
    intro n hn
    have : n = 0 := by simpa [countOcc] using hn
    subst this
    simp [confRho, rad8]
  | succ K ih =>
    intro n hn
    have hmono : ENNReal.ofReal (rad8 R K) ≤ ENNReal.ofReal (rad8 R (K + 1)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [rad8, zpow_natCast]
      gcongr
      · norm_num
      · omega
    rw [countOcc_succ] at hn
    split_ifs at hn with hE
    · rcases n with _ | m
      · exact (ih 0 (Nat.zero_le _)).trans hmono
      · have hm := ih m (by omega)
        refine iInf_le_of_le ((3 * (K + 1) : ℕ) : ℤ) (iInf_le_of_le ?_ (iInf_le_of_le hE le_rfl))
        refine (show 6 * confRho ξ cc D P h p R z m ω ≤ 6 * ENNReal.ofReal (rad8 R K) by gcongr).trans ?_
        rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [rad8, zpow_natCast]
        rw [show 3 * (K + 1) = 3 * K + 3 by ring, pow_add]
        nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (3 * K)]
    · exact (ih n (by omega)).trans hmono

theorem rad8_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < rad8 R k := by
  unfold rad8; positivity

theorem rad8_succ (R : ℝ) (k : ℕ) : rad8 R (k + 1) = 8 * rad8 R k := by
  simp only [rad8, zpow_natCast]
  rw [show 3 * (k + 1) = 3 * k + 3 by ring, pow_add]; ring

theorem rad8_eq (R : ℝ) (K : ℕ) : rad8 R K = (8 : ℝ) ^ K * R := by
  simp only [rad8, zpow_natCast, pow_mul]; norm_num

theorem countOcc_congr' {Ω : Type} {E E' : ℕ → Set Ω} {ω : Ω} (hω : ∀ k, (ω ∈ E k ↔ ω ∈ E' k))
    (K : ℕ) : countOcc E K ω = countOcc E' K ω := by
  classical
  unfold countOcc
  congr 1
  exact Finset.filter_congr fun k _ => hω k

/-! ## Translation to the centre `0` -/

/-- `h(· + z) − h(· + z)_1(0)` -/
def transN {Ω : Type} (h : Ω → DistC) (z : ℂ) : Ω → DistC :=
  fun ω => addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0)

/-- `E_r(z)` as an event of the translated normalized field on `𝔸_{2r,5r}(0)`, normalized at
radius `r` (the form of `CONFLem2_12aP`); template `DFGPS.annEvent_translate`. -/
theorem confE_translate {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (HE : CONFEMeas γ D c)
    {p : CONFParams} (hp : p.Valid) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ∃ F : Set Ω, MeasurableSet[fieldSigma (fun ω => addConst (transN h z ω)
        (-circleAvg (transN h z ω) r 0)) (annulus 0 (3 / 2 * r) (5 * r))] F ∧
      F =ᵐ[P] confE (xiGamma γ) c D P h p r z := by
  obtain ⟨F, hF, hFae⟩ := HE p hp P h hh z r hr
  have hUV : ∀ y : ℂ, y ∈ annulus 0 (3 / 2 * r) (5 * r) ↔
      (1 : ℝ) • y + z ∈ annulus z (3 / 2 * r) (5 * r) :=
    fun y => by
      show 3 / 2 * r < ‖y - 0‖ ∧ ‖y - 0‖ < 5 * r ↔
        3 / 2 * r < ‖(1 : ℝ) • y + z - z‖ ∧ ‖(1 : ℝ) • y + z - z‖ < 5 * r
      simp only [sub_zero, one_smul, add_sub_cancel_right]
  have hF2 := GM.fieldSigma_le_affineComp one_pos hUV
    (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) F hF
  obtain ⟨B, hB, hBF⟩ := hF2
  refine ⟨_, ⟨B, hB, rfl⟩, ?_⟩
  refine EventuallyEq.trans ?_ hFae
  rw [← hBF]
  have hz := hh.affineComp one_pos z
  filter_upwards [CircleAvg.ae_circleAvg_addConst hz 0 hr] with ω hω
  have e : addConst (transN h z ω) (-circleAvg (transN h z ω) r 0) =
      affineComp 1 z (addConst (h ω) (-circleAvg (h ω) r z)) := by
    simp only [transN]
    rw [hω, GM.Tight.circleAvg_affineComp_one, GM.Tight.circleAvg_affineComp_one,
      GFFLaw.addConst_addConst,
      GM.affineComp_addConst one_pos]
    congr 1; ring
  simp only [mem_preimage]
  rw [e]

/-! ## CONF Lemma 3.4 -/

/-- **CONF Lemma 3.4** (C:1262–1268) from **CONF Lemma 3.2**, the determination of `E_r(z)` by
`(h − h_r(z))|_{𝔸_{2r,5r}(z)}` (C:1270) and **CONF Lemma 2.12 (1)** as printed; proof C:1269–1271
with `r_k = 8^k𝕣`, `S₁ = 3/2` (CONF: 2; see `CONFEMeas`), `S₂ = 5`, `b = 1/2`, `a = q log 8`, `K = ⌊log₈ C⌋`. -/
theorem confLem3_4_of {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (H32 : CONFLem3_2 γ D c)
    (HE : CONFEMeas γ D c) (H212 : CONFLem2_12aP) : CONFLem3_4 γ D c := by
  intro q hq
  set L := Real.log 8 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  obtain ⟨p₀, c₀, hp₀, hp₀1, hc₀, H⟩ := H212 (3 / 2) 5 (by norm_num) (by norm_num) (q * L)
    (by positivity) (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨p, hpv, hδ8, hP2⟩ := H32 p₀ hp₀ hp₀1
  have ⟨h1, h2, h3, h4, h5, _⟩ := hpv
  let p' : CONFParams := ⟨p.c, p.δ, p.A, 1 / (4 * L)⟩
  have hp'v : p'.Valid := ⟨h1, h2, h3, h4, h5, by simp only [p']; positivity⟩
  refine ⟨p', hp'v, hδ8, 64, c₀ * Real.exp (q * L), by norm_num, by positivity, ?_⟩
  intro Ω _ P _ h hh z R hR C hC
  have hC0 : 0 < C := by linarith
  have hn : IsNormalizedWPGFF (transN h z) P := GM.isNormalized_shift hh z
  choose F hFm hFae using fun k : ℕ => confE_translate HE hpv P h hh z (rad8_pos hR k)
  -- numerics
  set x := Real.log C / L with hx
  set K := ⌊x⌋₊ with hK
  have hlogC : 2 * L ≤ Real.log C := by
    have e64 : Real.log 64 = 2 * L := by
      rw [hLdef, show (64 : ℝ) = 8 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← e64]; exact Real.log_le_log (by norm_num) hC
  have hx2 : 2 ≤ x := by rw [hx, le_div_iff₀ hL]; linarith
  have hKx : (K : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxK : x < K + 1 := Nat.lt_floor_add_one x
  set n := ⌊p'.η * Real.log C⌋₊ with hn'
  have hnK : (n : ℝ) ≤ 1 / 2 * K := by
    have : (n : ℝ) ≤ p'.η * Real.log C := Nat.floor_le (by simp only [p']; exact mul_nonneg (by positivity) (by linarith))
    have e : p'.η * Real.log C = x / 4 := by
      simp only [p', hx]; field_simp
    rw [e] at this
    linarith
  have h8K : rad8 R K ≤ C * R := by
    rw [rad8_eq]
    refine mul_le_mul_of_nonneg_right ?_ hR.le
    have e8 : (8 : ℝ) ^ K = Real.exp (L * K) := by
      rw [hLdef, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    rw [e8, ← Real.exp_log hC0]
    refine Real.exp_le_exp.mpr ?_
    calc L * K ≤ L * x := mul_le_mul_of_nonneg_left hKx hL.le
      _ = Real.log C := by rw [hx]; field_simp
  have hcnt : ∀ᵐ ω ∂P, ∀ k, (ω ∈ F k ↔ ω ∈ confE (xiGamma γ) c D P h p (rad8 R k) z) := by
    filter_upwards [ae_all_iff.2 hFae] with ω hω k
    exact Iff.of_eq (hω k)
  refine (measure_mono_ae ?_).trans ((H P (transN h z) hn (rad8 R) F (rad8_pos hR) ?_ hFm ?_ K).trans ?_)
  · filter_upwards [hcnt] with ω hω hbad
    have hbad' : ENNReal.ofReal (C * R) < confRho (xiGamma γ) c D P h p' R z n ω := hbad
    show (countOcc F K ω : ℝ) < 1 / 2 * K
    rw [countOcc_congr' hω]
    by_contra hge
    push Not at hge
    have hnc : n ≤ countOcc (fun k => confE (xiGamma γ) c D P h p' (rad8 R k) z) K ω := by
      have : (n : ℝ) ≤ countOcc (fun k => confE (xiGamma γ) c D P h p (rad8 R k) z) K ω :=
        hnK.trans hge
      exact_mod_cast this
    have hle := confRho_le_of_count (xiGamma γ) c D P h p' hR z ω K n hnc
    exact absurd (hle.trans (ENNReal.ofReal_le_ofReal h8K)) (not_le.2 hbad')
  · intro k
    rw [rad8_succ, le_div_iff₀ (rad8_pos hR k)]
    nlinarith [rad8_pos hR k]
  · intro k; rw [measure_congr (hFae k)]; exact hP2 P h hh z _ (rad8_pos hR k)
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_def_of_pos hC0, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc₀.le
    have : Real.log C = L * x := by rw [hx]; field_simp
    rw [this]
    nlinarith [mul_nonneg (mul_pos hq hL).le (by linarith : (0 : ℝ) ≤ K + 1 - x)]

end LQGMetric.CONF
