/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Regularity
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE2Core
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults

/-!
# GM Lemma 4.11, condition 5 (existence of good annuli): the per-point bound

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11, l. 1987: "By Lemma 2.6
[= LM Lemma 3.1], conditions (2) and (3) of Theorem 4.2, and a union bound over all
`z ∈ (λ_1ε^{1+ν}𝕣/4)ℤ² ∩ V`, if `𝕡` is chosen sufficiently close to 1 … the probability of
condition 5 … tends to 1 as `a → 0`, uniformly over the choice of `𝕣`."

This file proves the per-point step: LM Lemma 3.1 (1) (`Blueprint.LMLem3_1a`, stated at the centre
`0` for a normalized field) applied at a centre `z` to the translated normalized field
`h(· + z) − h_1(z)`, exactly as in the proof of GM Lemma 3.8 (`GM.gm_L3_8`,
`Papers/GM/S3/GoodAnnulusL38.lean`): if the events `F_j` are (a.s.) determined by
`(h − h_{ρ_j}(z))|_{A_{s₁ρ_j, s₂ρ_j}(z)}` with `ρ_{j+1} ≤ s₁ρ_j` and have probability `≥ p`, then
the probability that none of `F_1, …, F_N` occurs is `≤ c e^{−aN}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- transport of an event determined by `(h − h_ρ(z))|_{A_{s₁ρ,s₂ρ}(z)}` to an event of the
translated normalized field `h(· + z) − h_1(z)`, determined on `A_{s₁ρ,s₂ρ}(0)` modulo
`h_ρ(0)` (as `aeEventIn_goodAnnulus_translate`) -/
theorem gm_c5_translate {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z : ℂ) {ρ s₁ s₂ : ℝ} (hρ : 0 < ρ) {F : Set Ω}
    (hF : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ z))
      (annulus z (s₁ * ρ) (s₂ * ρ))) F) :
    ∃ E : Set Ω, MeasurableSet[fieldSigma (fun ω =>
        addConst (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
          (-circleAvg (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
            ρ 0)) (annulus 0 (s₁ * ρ) (s₂ * ρ))] E ∧ E =ᵐ[P] F := by
  obtain ⟨F', hF', hFae⟩ := hF
  have hUV : ∀ y : ℂ, y ∈ annulus 0 (s₁ * ρ) (s₂ * ρ) ↔
      (1 : ℝ) • y + z ∈ annulus z (s₁ * ρ) (s₂ * ρ) := fun y => by
    show s₁ * ρ < ‖y - 0‖ ∧ ‖y - 0‖ < s₂ * ρ ↔
      s₁ * ρ < ‖(1 : ℝ) • y + z - z‖ ∧ ‖(1 : ℝ) • y + z - z‖ < s₂ * ρ
    simp only [sub_zero, one_smul, add_sub_cancel_right]
  have hF2 := fieldSigma_le_affineComp one_pos hUV _ F' hF'
  obtain ⟨B, hB, hBF⟩ := hF2
  refine ⟨_, ⟨B, hB, rfl⟩, ?_⟩
  have hz := hh.affineComp one_pos z
  refine EventuallyEq.trans ?_ hFae.symm
  rw [← hBF]
  filter_upwards [CircleAvg.ae_circleAvg_addConst hz 0 hρ] with ω hω
  simp only [mem_preimage]
  rw [affineComp_addConst one_pos, hω, Tight.circleAvg_affineComp_one,
    Tight.circleAvg_affineComp_one, GFFLaw.addConst_addConst]
  congr! 3
  ring

/-- **per-point step of condition 5** (GM l. 1987, via LM Lemma 3.1 (1) at the centre `z`, as in
the proof of GM Lemma 3.8): if `F_j` is a.s. determined by `(h − h_{ρ_j}(z))|_{A_{s₁ρ_j,s₂ρ_j}(z)}`,
`ρ` is decreasing with `ρ_{j+1} ≤ s₁ρ_j`, and `P[F_j] ≥ p`, then
`P[none of F_1, …, F_N] ≤ c e^{−aN}` (`N ≥ 1`), with `p, c` from LM Lemma 3.1 (1). -/
theorem gm_c5_point {s₁ s₂ pt cc a : ℝ}
    (HLM : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
      AnnulusIterHyp h s₁ s₂ r E → (∀ k, ENNReal.ofReal pt ≤ P (E k)) →
      ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < 1 / 2 * K} ≤ ENNReal.ofReal (cc * Real.exp (-a * K)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z : ℂ) (ρ : ℕ → ℝ) (hρpos : ∀ j, 0 < ρ j) (hρanti : Antitone ρ)
    (hρrat : ∀ j, ρ (j + 1) / ρ j ≤ s₁) (F : ℕ → Set Ω)
    (hFm : ∀ j, AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (ρ j) z))
      (annulus z (s₁ * ρ j) (s₂ * ρ j))) (F j))
    (hFp : ∀ j, ENNReal.ofReal pt ≤ P (F j)) (N : ℕ) (hN : 1 ≤ N) :
    P {ω | ∀ j, 1 ≤ j → j ≤ N → ω ∉ F j} ≤ ENNReal.ofReal (cc * Real.exp (-a * N)) := by
  have hz := hh.affineComp one_pos z
  have hm1 := measurable_circleAvg_left 1 0
  set hn : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0) with hn_def
  have hnN : IsNormalizedWPGFF hn P := by
    refine ⟨hz.addConst (hm1.comp hz.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
    simp only [hn_def]
    rw [hω]; ring
  choose E hEm hEae using fun j => gm_c5_translate hh z (hρpos j) (hFm j)
  have hAI : AnnulusIterHyp hn s₁ s₂ ρ E := ⟨hρpos, hρanti, hρrat, hEm⟩
  have hEp : ∀ k, ENNReal.ofReal pt ≤ P (E k) := fun k => by
    rw [measure_congr (hEae k)]; exact hFp k
  have HB := HLM P hn hnN ρ E hAI hEp N
  have hall := ae_all_iff.2 hEae
  refine (measure_mono_ae ?_).trans HB
  filter_upwards [hall] with ω hω hno
  by_contra hcount
  simp only [mem_ofPred_eq, not_lt] at hcount
  have hpos : (0 : ℝ) < countOcc E N ω := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨k, hk1, hkK, hkE⟩ :=
    Tight.exists_good_of_count E (Nat.zero_le _) ω (by rw [Nat.cast_zero]; exact hpos)
  have : ω ∈ F k := by
    have := hω k
    rw [← this]; exact hkE
  exact hno k hk1 (by omega) this

/-- `r_{k+i} ≤ q^i r_k` along a sequence with `r_{j+1} ≤ q r_j` for `j + 1 < K` -/
theorem gm_c5_chain {K : ℕ} {r : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hr : ∀ j, j + 1 < K → r (j + 1) ≤ q * r j) (k : ℕ) :
    ∀ i, k + i < K → r (k + i) ≤ q ^ i * r k := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := hr (k + i) (by omega)
    have h2 := ih (by omega)
    rw [← add_assoc, pow_succ]
    calc r (k + i + 1) ≤ q * r (k + i) := h1
      _ ≤ q * (q ^ i * r k) := mul_le_mul_of_nonneg_left h2 hq
      _ = q ^ i * q * r k := by ring

/-- **per-point step of condition 5 with the radii of T4.2 (1)**: for radii `r_0, …, r_{K−1}` with
`r_k/r_{k+1} ≥ λ_4/λ_1` and events `G_k` a.s. determined by
`(h − h_{λ_5 r_k}(z))|_{A_{λ_1 r_k, λ_4 r_k}(z)}` with `P[G_k] ≥ p`, the probability that no `G_k`
occurs is `≤ c e^{−a⌊(K−1)/m⌋}`, where `m` is such that `(λ_1/λ_4)^m ≤ λ_1/λ_5` (LM Lemma 3.1 (1)
is applied to every `m`-th radius `λ_5 r_{mj}`, `s₁ = λ_1/λ_5`, `s₂ = λ_4/λ_5`). -/
theorem gm_c5_point_rr {l0 l3 l4 pt cc a : ℝ} (hl0 : 0 < l0) (hl03 : l0 < l3) (hl34 : l3 < l4)
    (HLM : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
      AnnulusIterHyp h (l0 / l4) (l3 / l4) r E → (∀ k, ENNReal.ofReal pt ≤ P (E k)) →
      ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < 1 / 2 * K} ≤ ENNReal.ofReal (cc * Real.exp (-a * K)))
    (hpt1 : pt ≤ 1) {m : ℕ} (hm : (l0 / l3) ^ m ≤ l0 / l4)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z : ℂ) (K : ℕ) (hK : m + 1 ≤ K) (r : ℕ → ℝ)
    (hr : ∀ k < K, 0 < r k) (hrat : ∀ k, k + 1 < K → l3 / l0 ≤ r k / r (k + 1))
    (G : ℕ → Set Ω)
    (hGm : ∀ k < K, AEEventIn P (fieldSigma (fun ω => addConst (h ω)
      (-circleAvg (h ω) (l4 * r k) z)) (annulus z (l0 * r k) (l3 * r k))) (G k))
    (hGp : ∀ k < K, ENNReal.ofReal pt ≤ P (G k)) :
    P {ω | ∀ k < K, ω ∉ G k} ≤ ENNReal.ofReal (cc * Real.exp (-a * ((K - 1) / m : ℕ))) := by
  classical
  have hl4 : 0 < l4 := by linarith
  have hl4' : l4 ≠ 0 := hl4.ne'
  have hm0 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero, le_div_iff₀ (by linarith)] at hm
    linarith
  set N : ℕ := (K - 1) / m with hN
  have hN1 : 1 ≤ N := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hmN : ∀ j ≤ N, m * j < K := fun j hj => by
    have : m * N ≤ K - 1 := by rw [hN]; exact Nat.mul_div_le (K - 1) m
    have : m * j ≤ m * N := Nat.mul_le_mul_left m hj
    omega
  set s₁ : ℝ := l0 / l4 with hs₁
  have hs₁0 : 0 < s₁ := div_pos hl0 (by linarith)
  have hs₁1 : s₁ < 1 := by rw [hs₁, div_lt_one (by linarith)]; linarith
  set q : ℝ := l0 / l3 with hq
  have hq0 : 0 ≤ q := div_nonneg hl0.le (by linarith)
  have hrq : ∀ j, j + 1 < K → r (j + 1) ≤ q * r j := fun j hj => by
    have h1 := hrat j hj
    have hp1 := hr (j + 1) hj
    have hp0 := hr j (by omega)
    rw [div_le_div_iff₀ hl0 hp1] at h1
    rw [hq, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  -- the radii `ρ_j = λ_5 r_{mj}` (`j ≤ N`), continued geometrically
  set ρ : ℕ → ℝ := fun j => if j ≤ N then l4 * r (m * j) else l4 * r (m * N) * s₁ ^ (j - N)
    with hρ
  have hρpos : ∀ j, 0 < ρ j := fun j => by
    simp only [hρ]
    split_ifs
    · exact mul_pos (by linarith) (hr _ (hmN j (by assumption)))
    · exact mul_pos (mul_pos (by linarith) (hr _ (hmN N le_rfl))) (pow_pos hs₁0 _)
  have hρrat : ∀ j, ρ (j + 1) ≤ s₁ * ρ j := fun j => by
    simp only [hρ]
    split_ifs with h1 h2 h2
    · have hlt : m * j + m < K := by have := hmN (j + 1) h1; rw [mul_add, mul_one] at this; exact this
      have hc := gm_c5_chain hq0 hrq (m * j) m hlt
      have e : m * j + m = m * (j + 1) := by ring
      rw [e] at hc
      have hpos := hr _ (hmN j h2)
      calc l4 * r (m * (j + 1)) ≤ l4 * (q ^ m * r (m * j)) :=
            mul_le_mul_of_nonneg_left hc (by linarith)
        _ ≤ l4 * (s₁ * r (m * j)) := by gcongr
        _ = s₁ * (l4 * r (m * j)) := by ring
    · omega
    · have : j = N := by omega
      subst this
      rw [show N + 1 - N = 1 by omega, pow_one, mul_comm]
    · rw [show j + 1 - N = (j - N) + 1 by omega, pow_succ]
      have := hρpos j
      nlinarith [pow_pos hs₁0 (j - N), hr _ (hmN N le_rfl)]
  have hρanti : Antitone ρ := antitone_nat_of_succ_le fun j => by
    have := hρrat j; have := hρpos j; nlinarith
  set F : ℕ → Set Ω := fun j => if 1 ≤ j ∧ j ≤ N then G (m * j) else univ with hF
  have hFm : ∀ j, AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (ρ j) z))
      (annulus z (s₁ * ρ j) (l3 / l4 * ρ j))) (F j) := fun j => by
    simp only [hF]
    split_ifs with hj
    · have hρj : ρ j = l4 * r (m * j) := by simp only [hρ, hj.2, ↓reduceIte]
      have e1 : s₁ * ρ j = l0 * r (m * j) := by
        rw [hρj, hs₁]; field_simp
      have e2 : l3 / l4 * ρ j = l3 * r (m * j) := by
        rw [hρj]; field_simp
      rw [e1, e2, hρj]
      exact hGm _ (hmN j hj.2)
    · exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
  have hFp : ∀ j, ENNReal.ofReal pt ≤ P (F j) := fun j => by
    simp only [hF]
    split_ifs with hj
    · exact hGp _ (hmN j hj.2)
    · rw [measure_univ]; exact ENNReal.ofReal_le_one.2 hpt1
  have key := gm_c5_point (s₁ := s₁) (s₂ := l3 / l4) HLM P h hh z ρ hρpos hρanti
    (fun j => by rw [div_le_iff₀ (hρpos j)]; linarith [hρrat j]) F hFm hFp N hN1
  refine (measure_mono ?_).trans key
  intro ω hω j hj1 hjN hFj
  simp only [hF, hj1, hjN, and_self, ↓reduceIte] at hFj
  exact hω (m * j) (hmN j hjN) hFj

end LQGMetric.GM
