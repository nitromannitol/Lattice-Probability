/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W1
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Fin
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4LGD
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind

/-!
# D97, packet P-2: balls of small mass meeting a compact set stay in a larger set

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2563, l. 2342–2346): "with high probability, the balls
intersecting both `∂𝕍_{u,λ}` and `∂𝕍_{u,2λ}` have LQG measure larger than `2δ²`". Their reason:
such a ball is large, so it contains one of finitely many fixed balls inside `𝕍`, each of
positive mass. Here:

* **`exists_heavy_of_pos`** (deterministic): if `C` is compact, every point of `C` is at distance
  `≥ 4r` from `Kᶜ`, the `4r`-thickening of `C` lies in `(0,1)²`, and `μ` charges every rational
  ball in `(0,1)²`, then there is `δ₀ > 0` such that for `δ < δ₀` every rational ball of
  `μ`-mass `≤ δ²` meeting `C` lies in `K` (the hypothesis `hheavy` of `lgd_sandwich_dzzWall`,
  with `C = closure U`);
* **`ae_qArea_ball_pos`**: for the zero-boundary GFF `X` on `𝕍`, a.s. `M_γ` charges every rational
  ball in `(0,1)²` (negative moments, `lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg`);
* **`ae_exists_heavy`**: the a.s. combination.

Own elementary geometry (the finite family of fixed balls is a finite rational net of the
`2r`-thickening of `C`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open QuantumZipper

/-- A ball `B(c, ρ)` with `ρ > 2r` containing `p` contains `B(q, 2r)` for some `q` with
`|q − p| ≤ 2r`. -/
lemma exists_ball_sub_ball_near {c p : ℂ} {ρ r : ℝ} (hr : 0 < r) (hρ : 2 * r < ρ)
    (hp : p ∈ ball c ρ) : ∃ q : ℂ, dist q p ≤ 2 * r ∧ ball q (2 * r) ⊆ ball c ρ := by
  by_cases h : dist c p ≤ 2 * r
  · exact ⟨c, h, ball_subset_ball hρ.le⟩
  · rw [not_le] at h
    have hd : 0 < dist c p := lt_trans (by positivity) h
    set t : ℝ := 2 * r / dist c p with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := (div_le_one hd).2 h.le
    refine ⟨p + (t : ℂ) * (c - p), ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0,
        ← dist_eq_norm, ht, div_mul_cancel₀ _ hd.ne']
    · intro x hx
      rw [mem_ball] at hx ⊢
      have e : c - (p + (t : ℂ) * (c - p)) = ((1 - t : ℝ) : ℂ) * (c - p) := by
        push_cast; ring
      have h1 : dist (p + (t : ℂ) * (c - p)) c = (1 - t) * dist c p := by
        rw [dist_comm, dist_eq_norm, e, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by linarith), ← dist_eq_norm]
      have h2 : (1 - t) * dist c p = dist c p - 2 * r := by
        rw [sub_mul, one_mul, ht, div_mul_cancel₀ _ hd.ne']
      have hcp : dist c p < ρ := by rw [dist_comm]; exact hp
      calc dist x c ≤ dist x (p + (t : ℂ) * (c - p)) + dist (p + (t : ℂ) * (c - p)) c :=
            dist_triangle _ _ _
        _ < 2 * r + (dist c p - 2 * r) := by rw [h1, h2]; exact add_lt_add_of_lt_of_le hx le_rfl
        _ < ρ := by linarith

/-- A finite rational `r`-net of a compact set. -/
lemma exists_finite_ratNet {S : Set ℂ} (hS : IsCompact S) {r : ℝ} (hr : 0 < r) :
    ∃ G : Finset (ℚ × ℚ), ∀ z ∈ S, ∃ g ∈ G, dist z (ratPt g) < r := by
  obtain ⟨G, hG⟩ := hS.elim_finite_subcover (fun g : ℚ × ℚ => ball (ratPt g) r)
    (fun _ => isOpen_ball) fun z _ => by
      obtain ⟨g, hg⟩ := exists_ratPt_dist_lt z hr
      exact mem_iUnion.2 ⟨g, by rw [mem_ball, dist_comm]; exact hg⟩
  refine ⟨G, fun z hz => ?_⟩
  obtain ⟨g, hg, hz'⟩ := mem_iUnion₂.1 (hG hz)
  exact ⟨g, hg, hz'⟩

/-- **The heavy-ball property** (deterministic form of DZZ l. 2563): balls of small mass meeting
`C` stay in `K`. -/
theorem exists_heavy_of_pos {μ : Measure ℂ} {C K : Set ℂ} (hC : IsCompact C) {r : ℝ}
    (hr : 0 < r) (hCK : ∀ p ∈ C, ∀ z ∉ K, 4 * r ≤ dist p z)
    (hCV : thickening (4 * r) C ⊆ openSquare)
    (hpos : ∀ (g : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt g) q ⊆ openSquare →
      0 < μ (ball (ratPt g) q)) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (c : ℚ × ℚ) (ρ : ℝ),
      (ball (ratPt c) ρ ∩ C).Nonempty → μ (ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
        ball (ratPt c) ρ ⊆ K := by
  classical
  obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn hr
  have hq0' : (0 : ℝ) < q := hq0
  have hq0'' : (0 : ℚ) < q := by exact_mod_cast hq0
  obtain ⟨G, hG⟩ := exists_finite_ratNet (hC.cthickening (r := 2 * r)) hr
  -- the fixed balls `B(g, q)`, `g ∈ G` near `C`
  set G' : Finset (ℚ × ℚ) := G.filter fun g => ball (ratPt g) q ⊆ thickening (4 * r) C
  set m : ℝ≥0∞ := min (G'.inf fun g => μ (ball (ratPt g) q)) 1 with hm
  have hm0 : 0 < m := by
    refine lt_min ((Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun g hg => ?_) one_pos
    exact hpos g q hq0'' ((Finset.mem_filter.1 hg).2.trans hCV)
  have hm1 : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hm1
  refine ⟨Real.sqrt m.toReal, Real.sqrt_pos.2 hmr, fun δ hδ hδ₀ c ρ hne hμ => ?_⟩
  by_contra hsub
  obtain ⟨z, hzB, hzK⟩ := not_subset.1 hsub
  obtain ⟨p, hpB, hpC⟩ := hne
  -- the ball is large
  have hρ : 2 * r < ρ := by
    have h1 := hCK p hpC z hzK
    have h2 : dist p z < 2 * ρ := by
      have := dist_triangle p (ratPt c) z
      rw [mem_ball] at hpB hzB
      rw [dist_comm (ratPt c) z] at this
      linarith
    linarith
  obtain ⟨y, hyp, hyB⟩ := exists_ball_sub_ball_near hr hρ hpB
  have hyC : y ∈ cthickening (2 * r) C :=
    mem_cthickening_of_dist_le y p _ _ hpC hyp
  obtain ⟨g, hgG, hgy⟩ := hG y hyC
  have hsub1 : ball (ratPt g) q ⊆ ball (ratPt c) ρ := by
    refine (ball_subset_ball' ?_).trans hyB
    rw [dist_comm]; linarith
  have hsub2 : ball (ratPt g) q ⊆ thickening (4 * r) C := by
    intro x hx
    rw [mem_ball] at hx
    refine mem_thickening_iff.2 ⟨p, hpC, ?_⟩
    have := dist_triangle4 x (ratPt g) y p
    rw [dist_comm (ratPt g) y] at this
    linarith
  have hgG' : g ∈ G' := by rw [Finset.mem_filter]; exact ⟨hgG, hsub2⟩
  have h1 : m ≤ μ (ball (ratPt g) q) := (min_le_left _ _).trans (Finset.inf_le hgG')
  have h2 : ENNReal.ofReal (δ ^ 2) < m := by
    rw [← ENNReal.ofReal_toReal hm1]
    refine (ENNReal.ofReal_lt_ofReal_iff hmr).2 ?_
    have := Real.sq_sqrt hmr.le
    nlinarith [Real.sqrt_nonneg m.toReal]
  exact absurd (h1.trans ((measure_mono hsub1).trans hμ)) (not_le.2 h2)

/-- For the zero-boundary GFF on `𝕍`, a.s. `M_γ` charges every rational ball inside `(0,1)²`
(DZZ Lemma 2.10, negative moments). -/
theorem ae_qArea_ball_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Measure ℂ → ℝ} (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ (g : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt g) q ⊆ openSquare →
      0 < qAreaMeasureOn γ (X ω) openSquare (ball (ratPt g) q) := by
  have := hX.gaussian.isProbabilityMeasure
  rw [ae_all_iff]; intro g; rw [ae_all_iff]; intro q
  by_cases hq : (0 : ℚ) < q
  swap
  · exact Eventually.of_forall fun _ h => absurd h hq
  by_cases hB : ball (ratPt g) q ⊆ openSquare
  swap
  · exact Eventually.of_forall fun _ _ h => absurd h hB
  have h := lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg hX hγ hγ2 (x := ratPt g)
    (by exact_mod_cast hq) hB (p := -1) (by norm_num)
  have hm := (aemeasurable_qAreaMeasureOn_ball' hX hγ hγ2 (ratPt g) q).pow_const (-1 : ℝ)
  filter_upwards [ae_lt_top' hm h.ne] with ω hω _ _
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, ENNReal.zero_rpow_of_neg (by norm_num)] at hω
  exact lt_irrefl _ hω

/-- The same for the white-noise field (transport of the law of the ball masses,
`GMCIdent4.map_qArea_ball_eq_wn`). -/
theorem ae_qArea_wn_ball_pos {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W : WhiteNoise.WNSpace → Ω' → ℝ} (hW : WhiteNoise.IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', ∀ (g : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt g) q ⊆ openSquare →
      0 < qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare (ball (ratPt g) q) := by
  obtain ⟨Ω, _, P, X, hP, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have hX0 := ae_qArea_ball_pos hX hγ hγ2
  rw [ae_all_iff]; intro g; rw [ae_all_iff]; intro q
  set f : Ω' → ℝ≥0∞ := fun ω =>
    qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare (ball (ratPt g) q) with hf
  set fX : Ω → ℝ≥0∞ := fun ω => qAreaMeasureOn γ (X ω) openSquare (ball (ratPt g) q) with hfX
  have hmap : P.map fX = P'.map f := GMCIdent4.map_qArea_ball_eq_wn hX hW hγ hγ2 _ _
  have hXm : AEMeasurable fX P := aemeasurable_qAreaMeasureOn_ball' hX hγ hγ2 _ _
  have hfm : AEMeasurable f P' := by
    have hF := GMCIdent4.aemeasurable_qAreaMeasureOn_ball_circ hX hγ hγ2 (ratPt g) (q : ℝ)
    rw [GMCIdent3.circLaw, GMCIdent3.map_circVec_eq hX hW] at hF
    exact hF.comp_aemeasurable (GMCIdent3.measurable_wnCircVec hW).aemeasurable
  by_cases hq : (0 : ℚ) < q
  swap
  · exact Eventually.of_forall fun _ h => absurd h hq
  by_cases hB : ball (ratPt g) q ⊆ openSquare
  swap
  · exact Eventually.of_forall fun _ _ h => absurd h hB
  have h3 : ∀ᵐ x ∂(P.map fX), 0 < x := by
    rw [ae_map_iff hXm (measurableSet_lt measurable_const measurable_id : MeasurableSet {x : ℝ≥0∞ | 0 < x})]
    filter_upwards [hX0] with ω hω using hω g q hq hB
  rw [hmap] at h3
  filter_upwards [ae_of_ae_map hfm h3] with ω hω _ _ using hω

/-- **P-2** (DZZ l. 2563): a.s. there is `δ₀ > 0` such that for `δ < δ₀` every rational ball of
`M_γ`-mass `≤ δ²` meeting `C` lies in `K`. -/
theorem ae_exists_heavy_wn {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W : WhiteNoise.WNSpace → Ω' → ℝ} (hW : WhiteNoise.IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {C K : Set ℂ} (hC : IsCompact C) {r : ℝ} (hr : 0 < r)
    (hCK : ∀ p ∈ C, ∀ z ∉ K, 4 * r ≤ dist p z) (hCV : thickening (4 * r) C ⊆ openSquare) :
    ∀ᵐ ω ∂P', ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (c : ℚ × ℚ) (ρ : ℝ),
      (ball (ratPt c) ρ ∩ C).Nonempty →
      qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare (ball (ratPt c) ρ) ≤
        ENNReal.ofReal (δ ^ 2) → ball (ratPt c) ρ ⊆ K := by
  filter_upwards [ae_qArea_wn_ball_pos hW hγ hγ2] with ω hω
  exact exists_heavy_of_pos hC hr hCK hCV hω

end DZZ
end LQGMetric
