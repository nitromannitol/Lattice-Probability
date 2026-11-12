/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Adapt at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L12
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L20B

/-!
# Adapters: DZZ Proposition 3.17 + Lemma 5.3 / 6.1 at `ν = μIn` in DG's form (P2-DZZ56)

Ding–Gwynne arXiv:1807.01072 use DZZ (arXiv:1807.00422) only as "Proposition 3.17 and Lemma 5.3"
(DG:1206, Lemma 3.12) and "Proposition 3.17 and Lemma 6.1" (DG:1627, Lemma 3.20), "with probability
tending to 1" (decision D105 N9). The DG consumers (P2-DG105h) take the hypotheses
`DG.DZZL53Whp P ν χ` (Papers/DG/S3L12) and `DG.DZZL61Whp P ν α χ u` (Papers/DG/S3L20B); this file
derives them at `ν = dzzMuIn γ W` (D97) from `dzz_lem53_upper_whp` / `dzz_lem61_lower_whp`.

* `dzzL53Whp_dzzMuIn`: from `DZZLem53Exp` (DZZ Lemma 5.3) and DZZ Proposition 3.17 for the tilde
  distances (DZZ Remark 5.2, `ξ`-admissible pairs, `0 < ξ < ξ₀`), plus the a.s. regularity of the
  GMC measure on `𝕍°` (locally finite, no atoms), which gives `D̃_δ(u,v) < ∞`
  (`lgdDZZ_lt_top_of_convex` on the ball `B((u+v)/2, |u−v|) ⊆ 𝕍̃_{u,v} ∩ 𝕍°`).
* `dzzL61Whp_of`: from `DZZLem61Exp` (DZZ Lemma 6.1) and DZZ Proposition 3.17, for any measure;
  the `ξ`-admissible pair is `(∂𝕍̄_{u,α}, ∂𝕍̄_u)` once `δ^ξ ≤ α/20` (two points before).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

lemma mem_dzzVXi_of_mem_sqBox {u z : ℂ} {l ξ : ℝ} (hu : u ∈ dzzVbar) (hz : z ∈ sqBox u l)
    (hl : l ≤ 1 / 20) (hξ : 0 ≤ ξ) (hξ9 : ξ ≤ 9 / 20) : z ∈ dzzVXi ξ := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  obtain ⟨h3, h4⟩ := hz
  rw [abs_le] at h1 h2 h3 h4
  exact mem_dzzVXi_of_near (a := 1 / 20) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith) hξ

lemma edge_of_mem_frontier_sqBox {u b : ℂ} {l : ℝ} (hl : 0 < l) (hb : b ∈ frontier (sqBox u l)) :
    |b.re - u.re| = l / 2 ∨ |b.im - u.im| = l / 2 := by
  rw [frontier_sqBox hl] at hb
  rcases hb with ((⟨_, hb⟩ | ⟨hb, _⟩) | ⟨_, hb⟩) | ⟨hb, _⟩
  · right; rw [mem_singleton_iff.mp hb, show u.im - l / 2 - u.im = -(l / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
  · left; rw [mem_singleton_iff.mp hb, show u.re - l / 2 - u.re = -(l / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
  · right; rw [mem_singleton_iff.mp hb, show u.im + l / 2 - u.im = l / 2 by ring,
      abs_of_pos (by positivity)]
  · left; rw [mem_singleton_iff.mp hb, show u.re + l / 2 - u.re = l / 2 by ring,
      abs_of_pos (by positivity)]

lemma dist_ge_of_edge {u a b : ℂ} {α : ℝ} (ha : a ∈ sqBox u (α / 20))
    (hb : |b.re - u.re| = 1 / 40 ∨ |b.im - u.im| = 1 / 40) : (1 - α) / 40 ≤ dist a b := by
  obtain ⟨h1, h2⟩ := ha
  rw [dist_eq_norm]
  rcases hb with hb | hb
  · have h := Complex.abs_re_le_norm (a - b)
    rw [Complex.sub_re] at h
    have := abs_sub_le b.re a.re u.re
    rw [abs_sub_comm b.re a.re] at this
    linarith
  · have h := Complex.abs_im_le_norm (a - b)
    rw [Complex.sub_im] at h
    have := abs_sub_le b.im a.im u.im
    rw [abs_sub_comm b.im a.im] at this
    linarith

/-- The half of **DZZ Lemma 5.3** used by DG (DG:1206): `limsup E log D̃_δ(u,v)/log δ⁻¹ ≤ χ`. -/
def DZZLem53Upper (P : Measure Ω) (μ : Ω → Measure ℂ) (χ : ℝ) : Prop :=
  ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
    (∫ ω, logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ {u} {v} ∂P) / Real.log δ⁻¹ < χ + ε

/-- The half of **DZZ Lemma 6.1** used by DG (DG:1627) and proved by DZZ (l. 2597: "it suffices
to prove a lower bound"): `liminf E log min_{∂𝕍̄_{u,α} × ∂𝕍̄_u} D_δ / log δ⁻¹ ≥ χ`. -/
def DZZLem61Lower (P : Measure Ω) (μ : Ω → Measure ℂ) (α χ : ℝ) : Prop :=
  ∀ u ∈ dzzVbar, ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
    χ - ε < (∫ ω, logMinLGD (μ ω) δ (frontier (sqBox u (α / 20)))
      (frontier (sqBox u (1 / 20))) ∂P) / Real.log δ⁻¹

lemma DZZLem53Exp.upper {P : Measure Ω} {μ : Ω → Measure ℂ} {χ : ℝ} (h : DZZLem53Exp P μ χ) :
    DZZLem53Upper P μ χ := fun u hu v hv huv ε hε =>
  h u hu v hv huv (Iio_mem_nhds (by linarith))

/-- **DG Lemma 3.20's DZZ input at any measure** (DZZ Proposition 3.17 + the lower half of
Lemma 6.1). -/
theorem dzzL61Whp_of_lower {P : Measure Ω} {μ : Ω → Measure ℂ} {α χ ξ₀ : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hξ₀ : 0 < ξ₀) {u : ℂ} (hu : u ∈ dzzVbar) (hL : DZZLem61Lower P μ α χ)
    (h317 : ∀ ξ, 0 < ξ → ξ < ξ₀ → DZZProp317 P μ ξ) :
    DG.DZZL61Whp P μ α χ u := by
  intro ι hι
  set ξ := min (ξ₀ / 2) ((1 - α) / 40) with hξdef
  have hξ : 0 < ξ := lt_min (by linarith) (by linarith)
  have hξ₀' : ξ < ξ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hξα : ξ ≤ (1 - α) / 40 := min_le_right _ _
  have hξ9 : ξ ≤ 9 / 20 := by linarith
  set a₀ : ℂ := u + ((α / 40 : ℝ) : ℂ)
  set b₀ : ℂ := u + ((1 / 40 : ℝ) : ℂ)
  have ha₀ : a₀ ∈ sqBox u (α / 20) := by
    constructor
    · show |(u + ((α / 40 : ℝ) : ℂ)).re - u.re| ≤ α / 20 / 2
      rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith
    · show |(u + ((α / 40 : ℝ) : ℂ)).im - u.im| ≤ α / 20 / 2
      rw [Complex.add_im, Complex.ofReal_im, add_zero, sub_self, abs_zero]; positivity
  have hb₀ : b₀ ∈ sqBox u (1 / 20) := by
    constructor
    · show |(u + ((1 / 40 : ℝ) : ℂ)).re - u.re| ≤ 1 / 20 / 2
      rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith
    · show |(u + ((1 / 40 : ℝ) : ℂ)).im - u.im| ≤ 1 / 20 / 2
      rw [Complex.add_im, Complex.ofReal_im, add_zero, sub_self, abs_zero]; positivity
  have hb₀e : |b₀.re - u.re| = 1 / 40 ∨ |b₀.im - u.im| = 1 / 40 := by
    left; show |(u + ((1 / 40 : ℝ) : ℂ)).re - u.re| = 1 / 40
    rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
  let A : ℝ → Set ℂ := fun δ =>
    if δ ^ ξ ≤ α / 20 then frontier (sqBox u (α / 20)) else {a₀}
  let B : ℝ → Set ℂ := fun δ =>
    if δ ^ ξ ≤ α / 20 then frontier (sqBox u (1 / 20)) else {b₀}
  have hAsub : ∀ δ, A δ ⊆ sqBox u (α / 20) := fun δ => by
    simp only [A]; split_ifs
    · exact (isClosed_sqBox _ _).frontier_subset
    · exact singleton_subset_iff.mpr ha₀
  have hBsub : ∀ δ, B δ ⊆ sqBox u (1 / 20) := fun δ => by
    simp only [B]; split_ifs
    · exact (isClosed_sqBox _ _).frontier_subset
    · exact singleton_subset_iff.mpr hb₀
  have hBe : ∀ δ, ∀ b ∈ B δ, |b.re - u.re| = 1 / 40 ∨ |b.im - u.im| = 1 / 40 := fun δ b hb => by
    simp only [B] at hb; split_ifs at hb
    · have := edge_of_mem_frontier_sqBox (by norm_num : (0 : ℝ) < 1 / 20) hb
      norm_num at this ⊢; exact this
    · rw [mem_singleton_iff.mp hb]; exact hb₀e
  have hAB : IsXiAdmissible ξ A B :=
    { subset_left := fun δ _ z hz =>
        mem_dzzVXi_of_mem_sqBox hu (hAsub δ hz) (by linarith) hξ.le hξ9
      subset_right := fun δ _ z hz => mem_dzzVXi_of_mem_sqBox hu (hBsub δ hz) le_rfl hξ.le hξ9
      adm_left := fun δ _ => by
        simp only [A]; split_ifs with h
        · exact Or.inr ⟨isConnected_frontier_sqBox u (by positivity),
            h.trans (side_le_diam_frontier_sqBox u (by positivity))⟩
        · exact Or.inl ⟨a₀, rfl⟩
      adm_right := fun δ _ => by
        simp only [B]; split_ifs with h
        · exact Or.inr ⟨isConnected_frontier_sqBox u (by positivity),
            (h.trans (by linarith)).trans (side_le_diam_frontier_sqBox u (by positivity))⟩
        · exact Or.inl ⟨b₀, rfl⟩
      dist_ge := fun δ _ a ha b hb => hξα.trans (dist_ge_of_edge (hAsub δ ha) (hBe δ b hb)) }
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ ξ ≤ α / 20 := by
    have h : Tendsto (fun δ : ℝ => δ ^ ξ) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hξ.ne'] using
        (Real.continuousAt_rpow_const 0 ξ (Or.inr hξ.le)).tendsto
    exact (tendsto_nhdsWithin_of_tendsto_nhds h).eventually (Iic_mem_nhds (by positivity))
  have hA : ∀ᶠ δ in 𝓝[>] (0 : ℝ), A δ = frontier (sqBox u (α / 20)) ∧
      B δ = frontier (sqBox u (1 / 20)) := by
    filter_upwards [hsmall] with δ hδ
    simp only [A, B, if_pos hδ]; exact ⟨trivial, trivial⟩
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      χ - ε < (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹ := fun ε hε => by
    filter_upwards [hL u hu ε hε, hA] with δ h1 h2
    rw [h2.1, h2.2]; exact h1
  refine (dzz_lgd_lower_whp' (h317 ξ hξ hξ₀') hAB hlow hι).congr' ?_
  filter_upwards [hA] with δ hδ
  rw [hδ.1, hδ.2]
  rfl

/-- **DG Lemma 3.12's DZZ input at `μIn`** (DZZ Proposition 3.17 for `D̃` + the upper half of
Lemma 5.3). -/
theorem dzzL53Whp_dzzMuIn_of_upper {P : Measure Ω} {γ : ℝ} {W : WNSpace → Ω → ℝ} {χ ξ₀ : ℝ}
    (hξ₀ : 0 < ξ₀) (hL : DZZLem53Upper P (dzzMuIn γ W) χ)
    (h317 : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ ξ, 0 < ξ → ξ < ξ₀ →
      DZZProp317In P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) (tildeBox u v) ξ)
    (hreg : ∀ᵐ ω ∂P, (∀ K, IsCompact K → K ⊆ openSquare → wickQArea γ W ω K < ⊤) ∧
      ∀ x ∈ openSquare, wickQArea γ W ω {x} = 0) :
    DG.DZZL53Whp P (dzzMuIn γ W) χ := by
  intro u hu v hv huv ι hι
  have hu' : u ∈ dzzVbar := hu
  have hv' : v ∈ dzzVbar := hv
  have hd0 : 0 < dist u v := dist_pos.mpr huv
  set ξ := min (ξ₀ / 2) (min (dist u v / 2) (9 / 20)) with hξdef
  have hξ : 0 < ξ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hξ₀' : ξ < ξ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hξd2 : 2 * ξ ≤ dist u v := by
    have : ξ ≤ dist u v / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hξd : ξ ≤ dist u v := by linarith
  have hξ9 : ξ ≤ 9 / 20 := (min_le_right _ _).trans (min_le_right _ _)
  have hVXi : ∀ w ∈ dzzVbar, w ∈ dzzVXi ξ := fun w hw =>
    mem_dzzVXi_of_near (near_of_mem_dzzVbar hw).1 (near_of_mem_dzzVbar hw).2 (by linarith) hξ.le
  have hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v < ⊤ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [hreg] with ω hω
    obtain ⟨hK, hat⟩ := hω
    have hBT := ball_mid_subset_tildeBox u v
    have hBS := ball_mid_subset_openSquare hu' hv'
    have hBV : Metric.ball ((u + v) / 2) ‖v - u‖ ⊆ dzzV := hBS.trans fun z hz =>
      ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
    have hw : ∀ K ⊆ Metric.ball ((u + v) / 2) ‖v - u‖,
        dzzWall (tildeBox u v) (dzzMuIn γ W ω) K = wickQArea γ W ω K := fun K hKB => by
      rw [dzzWall_apply_of_subset (isClosed_tildeBox u v).measurableSet (hKB.trans hBT),
        dzzMuIn, dzzWall_apply_of_subset isClosed_dzzV.measurableSet (hKB.trans hBV)]
    have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
    have hum : u ∈ Metric.ball ((u + v) / 2) ‖v - u‖ := by
      rw [Metric.mem_ball, dist_eq_norm, show u - (u + v) / 2 = -((v - u) / 2) by ring, norm_neg,
        norm_div]
      simp only [Complex.norm_ofNat]; linarith
    have hvm : v ∈ Metric.ball ((u + v) / 2) ‖v - u‖ := by
      rw [Metric.mem_ball, dist_eq_norm, show v - (u + v) / 2 = (v - u) / 2 by ring, norm_div]
      simp only [Complex.norm_ofNat]; linarith
    exact lgdDZZ_lt_top_of_convex Metric.isOpen_ball (convex_ball _ _)
      (fun K hKc hKB => by rw [hw K hKB]; exact hK K hKc (hKB.trans hBS))
      (fun x hx => by rw [hw {x} (singleton_subset_iff.mpr hx)]; exact hat x (hBS hx))
      hδ hum hvm
  have := dzz_lgd_upper_whpIn' (h317 u hu' v hv' huv ξ hξ hξ₀')
    (isXiAdmissible_const_singleton (hVXi u hu') (hVXi v hv') hξd)
    (fun _ _ => ⟨singleton_subset_iff.mpr (mem_kXi_tildeBox_left huv hξd2),
      singleton_subset_iff.mpr (mem_kXi_tildeBox_right huv hξd2)⟩) (hL u hu' v hv' huv)
    (by simpa only [lgdMinSet_singleton] using hfin) hι
  simp only [lgdMinSet_singleton] at this
  exact this

end DZZ
end LQGMetric
