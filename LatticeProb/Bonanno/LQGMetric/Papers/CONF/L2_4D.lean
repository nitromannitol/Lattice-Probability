/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_4D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4C

/-!
# CONF Lemma 2.4 from the uniqueness of one-sided limits

Source: CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, Lemma 2.4
(`lem-leftmost-geodesic`, l. 533–537) and its proof (l. 548–558).

* `side_approx` (l. 552–556): if the one-sided limit `IsSideGeod left` at `y` is unique on
  `[0, s]`, it is the uniform limit of the geodesics `P_{q_n}` to rational points
  `q_n ∈ ℚ² ∖ 𝓑^•_s` (CONF's construction, `exists_rat_near`, then Arzelà–Ascoli).
* `CONFSideUniq`: the remaining step, CONF l. 557–558, "By Lemma 2.3, no `D_h`-geodesic from 0
  to `y` can cross any of the `P_{q_n^-}`'s. It follows that each such geodesic lies to the
  right of `P_y^-`", in the form the Blueprint reading needs: two one-sided limits at `y` from
  the same side agree on `[0, s]`. Deterministic, given the a.s. inputs (length metric, bounded
  compactness, existence of geodesics, CONF Lemma 2.2 at the centre).
* `confLem2_4_of`: **CONF Lemma 2.4** (`Blueprint.CONFLem2_4`) from `DFGPSLem3_8` and
  `CONFSideUniq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- **CONF Lemma 2.4, uniqueness of the one-sided limit** (proof l. 557–558; open): for a
boundedly compact length metric with geodesics, in which the geodesics from `z₀` to rational
points are unique (CONF Lemma 2.2), two one-sided limits (`IsSideGeod`) from the same side at
`y ∈ ∂𝓑^•_s(z₀)` agree on `[0, s]`. -/
def CONFSideUniq : Prop :=
  ∀ (D : ContMetric) (z₀ : ℂ), D.IsLength →
    (∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A) →
    (∀ a b : ℂ, ∃ η, IsGeod01 D a b η) → (∀ q : ℚ × ℚ, UniqueGeod D z₀ (ratPt q)) →
    ∀ s : ℝ, 0 < s → ∀ y ∈ frontier (filledBall D z₀ s), ∀ (left : Bool) (Q Q' : ℝ → ℂ),
      IsSideGeod left D z₀ s y Q → IsSideGeod left D z₀ s y Q' → EqOn Q Q' (Icc 0 s)

section Det
variable {D : ContMetric} {z : ℂ} {s : ℝ}

theorem supDistOn_congr {P Q Q' : ℝ → ℂ} (h : EqOn Q Q' (Icc 0 s)) :
    supDistOn P Q s = supDistOn P Q' s := by
  simp only [supDistOn]
  exact iSup_congr fun t => iSup_congr fun ht => by rw [h ht]

/-- **CONF Lemma 2.4, approximation clause** (l. 552–556), given uniqueness -/
theorem side_approx
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hs : 0 < s) {y : ℂ} {left : Bool}
    (huniq : ∀ Q Q', IsSideGeod left D z s y Q → IsSideGeod left D z s y Q' →
      EqOn Q Q' (Icc 0 s))
    {Q : ℝ → ℂ} (hQ : IsSideGeod left D z s y Q) :
    ∃ (q : ℕ → ℚ × ℚ) (Qn : ℕ → ℝ → ℂ),
      (∀ n, ratPt (q n) ∉ filledBall D z s) ∧
      (∀ n, IsGeodesicL D (Qn n) (D.1 (z, ratPt (q n))) z (ratPt (q n))) ∧
      Tendsto (fun n => supDistOn (Qn n) Q s) atTop (𝓝 0) := by
  obtain ⟨hy, -, φ, hφ, t₀, ht₀, -⟩ := id hQ
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) / 2 with he
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have heT : Tendsto e atTop (𝓝 0) := by
    simpa [he] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  choose q G r hqK hG hsL hr hrt using fun n =>
    exists_rat_near hbc hgeo hs hφ (sideSeq left t₀ n) (he0 n)
  have hGs : ∀ n, IsGeodesicL D (G n) s z (φ (r n)) := fun n =>
    (hr n) ▸ geodL_restr (hG n) ⟨hs.le, (hsL n).le⟩
  have hrT : Tendsto r atTop (𝓝 t₀) := by
    have h1 : Tendsto (fun n => r n - sideSeq left t₀ n) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (hrt n).le) heT
    simpa using h1.add (tendsto_sideSeq left t₀)
  have hside : ∀ n, if left then t₀ < r n else r n < t₀ := by
    intro n
    have h1 := hrt n
    have h2 : e n < 1 / ((n : ℝ) + 1) := by
      simp only [he]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
    rw [abs_lt] at h1
    cases left <;> simp only [sideSeq, Bool.false_eq_true, if_true, if_false] at h1 ⊢ <;> linarith
  obtain ⟨ψ, Q'', hψ, hconv⟩ := exists_subseq_supDist hbc hs.le hGs
  have hrψ : Tendsto (fun n => r (ψ n)) atTop (𝓝 t₀) := hrT.comp hψ.tendsto_atTop
  have hyψ : Tendsto (fun n => φ (r (ψ n))) atTop (𝓝 y) := ht₀ ▸ (hφ.1.tendsto t₀).comp hrψ
  have hQ'' : IsSideGeod left D z s y Q'' :=
    ⟨hy, geod_of_tendsto (fun n => hGs (ψ n)) hs.le hyψ
      (fun t ht => tendsto_of_supDistOn hconv ht), φ, hφ, t₀, ht₀, fun n => r (ψ n),
      fun n => G (ψ n), hrψ, fun n => hside (ψ n), fun n => hGs (ψ n), hconv⟩
  have heq := huniq Q'' Q hQ'' hQ
  refine ⟨fun n => q (ψ n), fun n => G (ψ n), fun n => hqK (ψ n), fun n => hG (ψ n), ?_⟩
  simpa only [supDistOn_congr heq] using hconv

end Det

/-- **CONF Lemma 2.4** (`lem-leftmost-geodesic`, l. 533–537) in the Blueprint reading, from
DFGPS Lemma 3.8 (via GM.S1.1, MQ Theorem 1.2 = CONF Lemma 2.2) and `CONFSideUniq`. -/
theorem confLem2_4_of (h38 : DFGPSLem3_8) (hU : CONFSideUniq) : CONFLem2_4 := by
  intro γ hγ hγ2 D c hD Ω _ P _ h hh z₀
  filter_upwards [GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh, GM.gm_S1_1 h38 hγ hγ2 hD P h hh,
    hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh), confLem2_2 h38 γ hγ hγ2 D c hD P h hh z₀]
    with ω hc hg hL hq s hs y hy left
  have huniq := hU (D (h ω)) z₀ hL hc hg hq s hs y hy left
  exact ⟨exists_sideGeod' hL hc hg hs hy left, huniq, fun Q hQ => side_approx hc hg hs huniq hQ⟩

end LQGMetric.CONF
