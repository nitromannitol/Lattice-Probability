/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW1

/-!
# Walled (Eq.boundDprime), UW2: `L32UpperCrossOn` at a dyadic wall from the walled inputs
(P2-DZZUPW, packet P-317K-UP, decision D123)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.2, (Eq.boundDprime) l. 1088–1101 (following the
proof of Lemma 3.5, l. 1054–1083), for `D^{B̄w}` (Remark 5.2, l. 2281–2284) and `D'_S`,
`S = cellsInside Bw`.

* `encPhiAllWOn`, `L32EncPhiHPWOn`: (eq-B-percolation-Psi) + union bound relative to the wall
  (the enclosures of the pulled-back cells by boxes with `Φ^W ≤ λ` for the pulled-back measure;
  the walled form of `L32EncPhiHPW`, S3P32XW);
* `startPhiCOn`, `L32StartPhiHPCOn`, `startPhiEvCOn`: (eq-B-good-Psi) relative to the wall (the
  walled form of `L32StartPhiHPC`, S3P32UClip);
* `mem_dzzVIn_of_kXi`: a point of `B̄w^ξ` pulls back into `𝕍_{−ρ/s}` for `ρ ≤ ξ`;
* **`l32UpperCrossOn_of`**: `L32UpperCrossOn P γ W B̄w (cellsInside Bw) μ ξ ξd` from the two walled
  inputs. Copy of `l32UpperCross_ofW` (S3P32XW, D102) with the deterministic step
  `l32BallCrossingOn` (S3P32UW1) instead of `L32BallCrossingW`, and two extra smallness
  conditions on `δ` (`δ^{C_Mc} < s_{Bw}`, giving `WSplit` by `wsplit_of_side`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- All `δ`-cells inside `B̄w` have an enclosure relative to the wall: the pulled-back cell has an
enclosure in `𝕍` by boxes with `Φ^W_{·,δ,r} ≤ λ` for the pulled-back measure (`r` in the
coordinates of `𝕍`). -/
def encPhiAllWOn (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (Bw : DyBox) (r δ : ℝ) :
    Set Ω :=
  {ω | ∀ b, IsCell (approxLQG γ W ω) δ (wEmb Bw b) →
    HasEnclosure b (kL37 γ δ) fun c => PhiLeW (wPullMeas Bw (μ ω)) δ r c (lamP32 δ)}

/-- **Walled (eq-B-percolation-Psi) + union bound** (DZZ l. 1104–1147 with Remark 5.2; open),
clipping depth `r δ` in the wall, i.e. `r δ / s_{Bw}` in the coordinates of `𝕍`. -/
def L32EncPhiHPWOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (Bw : DyBox) (r : ℝ → ℝ) : Prop :=
  HighProb P fun δ => encPhiAllWOn γ W μ Bw (r δ / Bw.side) δ

/-- The walled start event at the pulled-back point `x ∈ 𝕍`. -/
def startPhiCOn (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (Bw : DyBox) (r δ ι : ℝ)
    (x : ℂ) : Set Ω :=
  {ω | ∀ b, IsCell (approxLQG γ W ω) δ (wEmb Bw b) → x ∈ b.largeBox →
    BallPathLeC (wPullMeas Bw (μ ω)) δ r x (frontier b.largeBox) (δ ^ (-ι) * lamP32 δ)}

/-- **Walled (eq-B-good-Psi) + union bound** (DZZ l. 1094–1096, 1062 with Remark 5.2; open),
uniformly in the pulled-back points of `𝕍_{−r δ / s}`. -/
def L32StartPhiHPCOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (Bw : DyBox) (r : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ x ∈ dzzVIn (r δ / Bw.side),
    P (startPhiCOn γ W μ Bw (r δ / Bw.side) δ (dzzCMc γ / 2) x)ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- The walled start event of a pulled-back end `A` (trivial unless `A` is a point). -/
def startPhiEvCOn (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (Bw : DyBox) (r δ ι : ℝ)
    (A : Set ℂ) : Set Ω :=
  {ω | ∀ u, A = {u} → ω ∈ startPhiCOn γ W μ Bw r δ ι u}

lemma startPhiEvCOn_bound {P : Measure Ω} {γ r δ ι : ℝ} {W : WNSpace → Ω → ℝ}
    {μ : Ω → Measure ℂ} {Bw : DyBox} {A : Set ℂ} {q : ℝ≥0∞}
    (h : ∀ u ∈ dzzVIn r, P (startPhiCOn γ W μ Bw r δ ι u)ᶜ ≤ q) (hA : A ⊆ dzzVIn r) :
    P (startPhiEvCOn γ W μ Bw r δ ι A)ᶜ ≤ q := by
  by_cases hs : ∃ u, A = {u}
  · obtain ⟨u, rfl⟩ := hs
    have e : startPhiEvCOn γ W μ Bw r δ ι {u} = startPhiCOn γ W μ Bw r δ ι u := by
      ext ω
      refine ⟨fun h => h u rfl, fun h u' hu' => ?_⟩
      obtain rfl := Set.singleton_eq_singleton_iff.1 hu'
      exact h
    rw [e]; exact h u (hA rfl)
  · have e : startPhiEvCOn γ W μ Bw r δ ι A = univ := by
      ext ω
      simp only [startPhiEvCOn, mem_ofPred_eq, mem_univ, iff_true]
      intro u hu; exact absurd ⟨u, hu⟩ hs
    rw [e, compl_univ, measure_empty]; exact bot_le

/-- The `ξ`-ball about a point of `K^ξ` lies in `K` (copy of `cmw_ball_sub_of_kXi`, S3CMW2). -/
lemma ball_sub_of_kXi' {K : Set ℂ} {ξ : ℝ} {u : ℂ} (hu : u ∈ kXi K ξ) :
    Metric.ball u ξ ⊆ K := by
  intro w hw
  by_contra h
  have := Metric.infDist_le_dist_of_mem (x := u) (show w ∈ Kᶜ from h)
  rw [Metric.mem_ball, dist_comm] at hw
  exact absurd (hu.trans this) (not_le.2 hw)

/-- A point of `B̄w^ξ` pulls back into `𝕍_{−ρ/s}` for `ρ ≤ ξ`. -/
lemma mem_dzzVIn_of_kXi {Bw : DyBox} {ξ ρ : ℝ} (hξ : 0 < ξ) (hρ : ρ ≤ ξ) {x : ℂ}
    (hx : x ∈ kXi Bw.closedBox ξ) : (wHom Bw).symm x ∈ dzzVIn (ρ / Bw.side) := by
  have hs := wside_pos Bw
  have hb := ball_sub_of_kXi' hx
  have key : ∀ w : ℂ, ‖w‖ < ξ → x + w ∈ Bw.closedBox := fun w hw =>
    hb (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hw)
  have hx0 := key 0 (by simpa using hξ)
  rw [add_zero] at hx0
  obtain ⟨a1, a2, a3, a4⟩ := hx0
  set z := (wHom Bw).symm x with hz
  have hxz : x = wHom Bw z := by simp [hz]
  have hre : x.re = Bw.j * Bw.side + Bw.side * z.re := by rw [hxz, wHom_re]
  have him : x.im = Bw.k * Bw.side + Bw.side * z.im := by rw [hxz, wHom_im]
  have tre : ∀ t : ℝ, |t| < ξ → Bw.j * Bw.side ≤ x.re + t ∧ x.re + t ≤ (Bw.j + 1) * Bw.side :=
    fun t ht => by
      have := key (t : ℂ) (by rwa [Complex.norm_real, Real.norm_eq_abs])
      exact ⟨by simpa using this.1, by simpa using this.2.1⟩
  have tim : ∀ t : ℝ, |t| < ξ → Bw.k * Bw.side ≤ x.im + t ∧ x.im + t ≤ (Bw.k + 1) * Bw.side :=
    fun t ht => by
      have := key ((t : ℂ) * Complex.I) (by
        rwa [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs])
      exact ⟨by simpa using this.2.2.1, by simpa using this.2.2.2⟩
  have c1 : Bw.j * Bw.side + ρ ≤ x.re := by
    by_contra h; push Not at h
    have := (tre (-((x.re - Bw.j * Bw.side + ξ) / 2)) (by
      rw [abs_lt]; constructor <;> linarith)).1
    linarith
  have c2 : x.re ≤ (Bw.j + 1) * Bw.side - ρ := by
    by_contra h; push Not at h
    have := (tre (((Bw.j + 1) * Bw.side - x.re + ξ) / 2) (by
      rw [abs_lt]; constructor <;> linarith)).2
    linarith
  have c3 : Bw.k * Bw.side + ρ ≤ x.im := by
    by_contra h; push Not at h
    have := (tim (-((x.im - Bw.k * Bw.side + ξ) / 2)) (by
      rw [abs_lt]; constructor <;> linarith)).1
    linarith
  have c4 : x.im ≤ (Bw.k + 1) * Bw.side - ρ := by
    by_contra h; push Not at h
    have := (tim (((Bw.k + 1) * Bw.side - x.im + ξ) / 2) (by
      rw [abs_lt]; constructor <;> linarith)).2
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs]; nlinarith
  · rw [show 1 - ρ / Bw.side = (Bw.side - ρ) / Bw.side by field_simp, le_div_iff₀ hs]; nlinarith
  · rw [div_le_iff₀ hs]; nlinarith
  · rw [show 1 - ρ / Bw.side = (Bw.side - ρ) / Bw.side by field_simp, le_div_iff₀ hs]; nlinarith

end DZZ
end LQGMetric
