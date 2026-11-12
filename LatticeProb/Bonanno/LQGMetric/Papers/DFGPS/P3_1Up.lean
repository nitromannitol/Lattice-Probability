/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_1Up at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.1: Step 2, the upper bound (task P2-DFA3)

DFGPS (arXiv:1905.00380, "T"), proof of Proposition 3.1, Step 2 ((3.12), T:1547–1556): the path
of Lemma 3.5 from `𝕣K₁` to `𝕣K₂` lies in the union of the good circles `∂B_r(w)`,
`w ∈ B_{ε𝕣}(𝕣U) ∩ (ε²𝕣/4)ℤ²`, `r ∈ [ε²𝕣, ε𝕣] ∩ {2^{-k}𝕣}`; there are at most
`B ε^{-6}` of them (`B = 2(8R+1)² + 1`; the paper counts `ε^{-4-o(1)}`, any polynomial bound
works), each of `D_h(·,·; 𝕣U)`-diameter `≤ C 𝔠_r e^{ξh_r(w)} ≤ C Λ ε^{-(2Λ+ξq)} 𝔠_𝕣 e^{ξh_𝕣(0)}`;
"by the triangle inequality" is `P31.chain_bound`.
-/

noncomputable section

open Set Metric
open scoped ENNReal
open LQGDimension.LFPPRecords

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

namespace P31

/-- the number of dyadic scales: `ε² ≤ 2^{-k}` forces `k ≤ ⌊ε^{-2}⌋` -/
lemma le_floor_of_dyadic {ε : ℝ} (hε0 : 0 < ε) {k : ℕ} (hk : ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹) :
    k ≤ ⌊(ε ^ 2)⁻¹⌋₊ := by
  refine Nat.le_floor ?_
  have h1 : ((k : ℕ) : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ k ≤ (ε ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) (by positivity)]; exact hk
  linarith

/-- the count of the circles -/
lemma card_circles_le {ε 𝕣 R : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h𝕣 : 0 < 𝕣) (hR : 0 ≤ R) :
    ((gridBox (ε ^ 2 * 𝕣 / 4) 0 (R * 𝕣) ×ˢ Finset.range (⌊(ε ^ 2)⁻¹⌋₊ + 1)).card : ℝ) + 1 ≤
      (2 * (8 * R + 1) ^ 2 + 1) / ε ^ 6 := by
  have hm : 0 < ε ^ 2 * 𝕣 / 4 := by positivity
  have hg := card_gridBox_le hm (by positivity : 0 ≤ R * 𝕣) 0
  have h8 : 2 * (R * 𝕣) / (ε ^ 2 * 𝕣 / 4) + 1 ≤ (8 * R + 1) / ε ^ 2 := by
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have e : 2 * (R * 𝕣) + ε ^ 2 * 𝕣 / 4 = 𝕣 * (2 * R + ε ^ 2 / 4) := by ring
    rw [e]
    have : 2 * R + ε ^ 2 / 4 ≤ 8 * R + 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 𝕣 * ε ^ 2 / 4)]
  have hk : ((⌊(ε ^ 2)⁻¹⌋₊ + 1 : ℕ) : ℝ) ≤ 2 / ε ^ 2 := by
    push_cast
    have := Nat.floor_le (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ ε ^ 2))
    have h1 : (1 : ℝ) ≤ (ε ^ 2)⁻¹ := by rw [one_le_inv₀ (by positivity)]; nlinarith
    rw [show (2 : ℝ) / ε ^ 2 = (ε ^ 2)⁻¹ + (ε ^ 2)⁻¹ by rw [div_eq_mul_inv]; ring]
    linarith
  rw [Finset.card_product, Finset.card_range, Nat.cast_mul]
  have hgb : ((gridBox (ε ^ 2 * 𝕣 / 4) 0 (R * 𝕣)).card : ℝ) ≤ ((8 * R + 1) / ε ^ 2) ^ 2 :=
    hg.trans (pow_le_pow_left₀ (by positivity) h8 2)
  have h6 : (1 : ℝ) ≤ 1 / ε ^ 6 := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_one₀ hε0.le hε1.le
  calc ((gridBox (ε ^ 2 * 𝕣 / 4) 0 (R * 𝕣)).card : ℝ) * ((⌊(ε ^ 2)⁻¹⌋₊ + 1 : ℕ) : ℝ) + 1
      ≤ ((8 * R + 1) / ε ^ 2) ^ 2 * (2 / ε ^ 2) + 1 / ε ^ 6 := by
        gcongr
    _ = (2 * (8 * R + 1) ^ 2 + 1) / ε ^ 6 := by field_simp

/-- **Step 2** of the proof of Proposition 3.1 ((3.12), T:1547–1556), on the conclusion of
Lemma 3.5 for `good w r := g ∈ E_r(w; C)`. -/
theorem upper_det {D : DistC → ContMetric} {c : ℝ → ℝ} {g : DistC} {ξ Λ q ε 𝕣 C R₀ : ℝ}
    (hξ : 0 < ξ) (hΛ : 1 < Λ)
    (hc : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    (hcpos : ∀ r, 0 < r → 0 < c r) (hε0 : 0 < ε) (hε1 : ε < 1) (h𝕣 : 0 < 𝕣) (hC : 1 < C)
    (hR₀ : 0 < R₀) {U₀ K₁ K₂ : Set ℂ} (hU₀ : U₀ ⊆ ball 0 R₀)
    (h35 : ∃ x ∈ scaleSet 𝕣 0 K₁, ∃ y ∈ scaleSet 𝕣 0 K₂, ∃ γ : Path x y, ∀ t,
        γ t ∈ scaleSet 𝕣 0 U₀ ∧ ∃ w : ℂ, ∃ r : ℝ, w ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 U₀) ∧
          w ∈ gridPts (ε ^ 2 * 𝕣 / 4) ∧ (∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣) ∧
          ε ^ 2 * 𝕣 ≤ r ∧ r ≤ ε * 𝕣 ∧ g ∈ annEvent ξ D c C r w ∧ γ t ∈ sphere w r ∧
          closedBall w (2 * r) ⊆ scaleSet 𝕣 0 U₀)
    (htail : TailOK g q ε 𝕣 (R₀ + 1)) :
    setDistIn (D g) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U₀) ≤
      ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6 *
        (C * (Λ * ε ^ (-(2 * Λ + ξ * q)) * scaleFac ξ c g 𝕣 0))) := by
  classical
  obtain ⟨x, hx, y, hy, γ, hγ⟩ := h35
  set m := ε ^ 2 * 𝕣 / 4 with hm_def
  have hm : 0 < m := by positivity
  set R := R₀ + 1
  set V := scaleSet 𝕣 0 U₀
  set L := C * (Λ * ε ^ (-(2 * Λ + ξ * q)) * scaleFac ξ c g 𝕣 0)
  set I0 := gridBox m 0 (R * 𝕣) ×ˢ Finset.range (⌊(ε ^ 2)⁻¹⌋₊ + 1)
  set Cs : (ℤ × ℤ) × ℕ → Set ℂ := fun i => sphere (gridPt m i.1) (((2 : ℝ) ^ i.2)⁻¹ * 𝕣)
  set Q : (ℤ × ℤ) × ℕ → Prop := fun i =>
    g ∈ annEvent ξ D c C (((2 : ℝ) ^ i.2)⁻¹ * 𝕣) (gridPt m i.1) ∧
      closedBall (gridPt m i.1) (2 * (((2 : ℝ) ^ i.2)⁻¹ * 𝕣)) ⊆ V ∧
      ε ^ 2 ≤ ((2 : ℝ) ^ i.2)⁻¹ ∧ ((2 : ℝ) ^ i.2)⁻¹ ≤ ε ∧ ‖gridPt m i.1‖ < R * 𝕣
  set I := I0.filter Q
  have hS : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hxS : x ∈ range γ := ⟨0, γ.source⟩
  have hyS : y ∈ range γ := ⟨1, γ.target⟩
  have hxV : x ∈ V := by simpa using (hγ 0).1
  have hcov : ∀ p ∈ range γ, ∃ i ∈ I, p ∈ Cs i := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨_, w, r, hwth, ⟨a, b, rfl⟩, ⟨k, rfl⟩, hr1, hr2, hgood, hsph, hball⟩ := hγ t
    have hpt : gridPt m (a, b) = ⟨a * m, b * m⟩ := rfl
    have hwn : ‖(⟨a * m, b * m⟩ : ℂ)‖ < R * 𝕣 := by
      obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hwth
      have hzn := norm_of_mem_scaleSet h𝕣 hU₀ hz
      have : ‖(⟨a * m, b * m⟩ : ℂ)‖ ≤ ‖z‖ + dist (⟨a * m, b * m⟩ : ℂ) z := by
        rw [dist_eq_norm]
        calc _ = ‖z + ((⟨a * m, b * m⟩ : ℂ) - z)‖ := by rw [add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      have : ε * 𝕣 ≤ 𝕣 := by nlinarith
      simp only [R]; nlinarith
    have hδ1 : ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ := le_of_mul_le_mul_right hr1 h𝕣
    have hδ2 : ((2 : ℝ) ^ k)⁻¹ ≤ ε := le_of_mul_le_mul_right hr2 h𝕣
    refine ⟨((a, b), k), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_gridBox hm ?_,
      Finset.mem_range.2 (Nat.lt_succ_of_le (le_floor_of_dyadic hε0 hδ1))⟩, ?_⟩, ?_⟩
    · rw [sub_zero, hpt]; exact hwn.le
    · exact ⟨by rw [hpt]; exact hgood, by rw [hpt]; exact hball, hδ1, hδ2, by rw [hpt]; exact hwn⟩
    · show γ t ∈ sphere (gridPt m (a, b)) _
      rw [hpt]; exact hsph
  have hdiam : ∀ i ∈ I, ∀ p ∈ Cs i ∩ range γ, ∀ p' ∈ Cs i ∩ range γ,
      (D g).internal V p p' ≤ ENNReal.ofReal L := by
    intro i hi p hp p' hp'
    obtain ⟨-, hgood, hball, hδ1, hδ2, hwn⟩ := Finset.mem_filter.1 hi
    set w := gridPt m i.1
    set r := ((2 : ℝ) ^ i.2)⁻¹ * 𝕣
    have hwg : w ∈ gridPts (ε ^ 2 * 𝕣 / 4) := ⟨i.1.1, i.1.2, rfl⟩
    obtain ⟨-, hb2⟩ := scaleFac_bounds hξ hΛ hc hcpos hε0 hε1 h𝕣 hδ1 hδ2
      (htail w hwn hwg i.2 hδ1 hδ2)
    have hann : ((annulus w (r / 2) (2 * r) : Set ℂ)) ⊆ V := fun z hz =>
      hball (mem_closedBall.2 (by rw [dist_eq_norm]; exact hz.2.le))
    calc (D g).internal V p p' ≤ (D g).internal (annulus w (r / 2) (2 * r)) p p' :=
          internalEDist_anti (Set.image_mono hann) _ _
      _ ≤ internalDiam (D g) (sphere w r) (annulus w (r / 2) (2 * r)) :=
          le_iSup₂_of_le p hp.1 (le_iSup₂_of_le p' hp'.1 le_rfl)
      _ ≤ ENNReal.ofReal (C * scaleFac ξ c g r w) := hgood.1
      _ ≤ ENNReal.ofReal L :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb2 (by linarith))
  have hchain := chain_bound I hS Cs (fun _ => isClosed_sphere) ((D g).internal V)
    (fun a b c => internal_triangle (D g) V a b c) (ENNReal.ofReal L) hcov hdiam hxS hyS
    (internalEDist_self (mem_image_of_mem _ hxV))
  have hcard : ((I.card : ℝ≥0∞) + 1) ≤
      ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6) := by
    have h1 : (I.card : ℝ) + 1 ≤ (I0.card : ℝ) + 1 := by
      have := Finset.card_filter_le I0 Q
      exact_mod_cast Nat.add_le_add_right this 1
    have h2 := card_circles_le hε0 hε1 h𝕣 (by positivity : (0 : ℝ) ≤ R)
    rw [show ((I.card : ℝ≥0∞) + 1) = ENNReal.ofReal ((I.card : ℝ) + 1) by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]]
    exact ENNReal.ofReal_le_ofReal (h1.trans h2)
  have hL : 0 ≤ (2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6 := by positivity
  calc setDistIn (D g) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) V ≤ (D g).internal V x y :=
        iInf₂_le_of_le x hx (iInf₂_le_of_le y hy le_rfl)
    _ ≤ ((I.card : ℝ≥0∞) + 1) * ENNReal.ofReal L := hchain
    _ ≤ ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6) * ENNReal.ofReal L := by
        gcongr
    _ = _ := (ENNReal.ofReal_mul hL).symm

end P31

end LQGMetric.DFGPS
