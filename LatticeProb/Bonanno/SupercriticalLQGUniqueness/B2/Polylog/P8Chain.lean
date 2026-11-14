/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P8Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Net
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Scale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.WeakStrong.Homothety
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.BLb

 


















set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open Uniqueness.Objects.CorrectedEvent (acr)
open WeakStrong (dilateM)

lemma dilateM_eq_comp (M : LSCMetric) {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    dilateM M r hr.ne' (x, y) = 1 * M (dilateHomeo hr x, dilateHomeo hr y) := by
  rw [one_mul, WeakStrong.dilateM_apply]; rfl

 
lemma aroundDist_dilateM (M : LSCMetric) {r : ℝ} (hr : 0 < r) (c : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    aroundDist (dilateM M r hr.ne') (annAt c a b ha hab) =
      aroundDist M (annAt (r • c) (r * a) (r * b) (mul_pos hr ha)
        (mul_lt_mul_of_pos_left hab hr)) := by
  obtain ⟨h1, h2, h3⟩ := image_dilate_annAt hr c a b ha hab
  rw [aroundDist_comp_mul one_ne_zero ENNReal.one_ne_top (dilateHomeo hr) (dilateM_eq_comp M hr)
    _ _ h1 h2 h3, one_mul]

 
lemma acrossDist_dilateM (M : LSCMetric) {r : ℝ} (hr : 0 < r) (c : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    acrossDist (dilateM M r hr.ne') (annAt c a b ha hab) =
      acrossDist M (annAt (r • c) (r * a) (r * b) (mul_pos hr ha)
        (mul_lt_mul_of_pos_left hab hr)) := by
  obtain ⟨-, h2, h3⟩ := image_dilate_annAt hr c a b ha hab
  rw [acrossDist_comp_mul one_ne_zero ENNReal.one_ne_top (dilateHomeo hr) (dilateM_eq_comp M hr)
    _ _ h2 h3, one_mul]

 

lemma le_internalSetDist_of_dilateM (M : LSCMetric) {r : ℝ} (hr : 0 < r) (V : Set ℂ)
    (z w : ℂ) (ρ : ℝ) {L : ℝ≥0∞}
    (h : L ≤ (dilateM M r hr.ne').internalSetDist {x | r • x ∈ V}
      {x | (x : ℂ) ∈ ball (r⁻¹ • z) (ρ / r)} {x | (x : ℂ) ∈ ball (r⁻¹ • w) (ρ / r)}) :
    L ≤ M.internalSetDist V {x | (x : ℂ) ∈ ball z ρ} {x | (x : ℂ) ∈ ball w ρ} := by
  have hr0 : r ≠ 0 := hr.ne'
  have hball : ∀ (u v : ℂ), u ∈ ball v ρ → r⁻¹ • u ∈ ball (r⁻¹ • v) (ρ / r) := by
    intro u v hu
    rw [mem_ball, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    exact div_lt_div_of_pos_right (mem_ball.1 hu) hr
  unfold LSCMetric.internalSetDist
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have hxV : r • (r⁻¹ • (x : ℂ)) ∈ V := by rw [smul_inv_smul₀ hr0]; exact x.2
  have hyV : r • (r⁻¹ • (y : ℂ)) ∈ V := by rw [smul_inv_smul₀ hr0]; exact y.2
  let x' : {u : ℂ | r • u ∈ V} := ⟨r⁻¹ • (x : ℂ), hxV⟩
  let y' : {u : ℂ | r • u ∈ V} := ⟨r⁻¹ • (y : ℂ), hyV⟩
  have hx' : x' ∈ {u : {u : ℂ | r • u ∈ V} | (u : ℂ) ∈ ball (r⁻¹ • z) (ρ / r)} := hball _ _ hx
  have hy' : y' ∈ {u : {u : ℂ | r • u ∈ V} | (u : ℂ) ∈ ball (r⁻¹ • w) (ρ / r)} := hball _ _ hy
  have hint := WeakStrong.internal_dilateM M r hr0 {u : ℂ | r • u ∈ V} V (fun _ => Iff.rfl)
    (x', y')
  have ex : (⟨r • (x' : ℂ), hxV⟩ : V) = x := Subtype.ext (smul_inv_smul₀ hr0 _)
  have ey : (⟨r • (y' : ℂ), hyV⟩ : V) = y := Subtype.ext (smul_inv_smul₀ hr0 _)
  calc L ≤ (dilateM M r hr0).internalSetDist {x | r • x ∈ V}
        {x | (x : ℂ) ∈ ball (r⁻¹ • z) (ρ / r)} {x | (x : ℂ) ∈ ball (r⁻¹ • w) (ρ / r)} := h
    _ ≤ (dilateM M r hr0).internal {u : ℂ | r • u ∈ V} (x', y') :=
        iInf₂_le_of_le x' hx' (iInf₂_le_of_le y' hy' le_rfl)
    _ = M.internal V (x, y) := by rw [hint, ex, ey]

 




theorem chain_scale (M₁ M₂ : LSCMetric) {r ρ R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ r / 16) {Y L K : ℝ≥0∞}
    (hA : aroundDist M₁ (annAt 0 (r * 1) (r * 2) (mul_pos hr one_pos)
      (mul_lt_mul_of_pos_left one_lt_two hr)) < Y)
    (hnet : ∀ b : Bool, ∀ i : ℕ, i < 9 →
      L ≤ acrossDist M₂ (annAt (r • netPt b i) (r * (1 / 8)) (r * (1 / 4))
        (mul_pos hr (by norm_num)) (mul_lt_mul_of_pos_left (by norm_num) hr)))
    (hcmp : ∀ (z w : ℂ) (hz : z ∈ ball (0 : ℂ) (3 * R)) (hw : w ∈ ball (0 : ℂ) (3 * R)),
      M₂.internalSetDist (thickening ρ (ball (0 : ℂ) (3 * R))) {x | (x : ℂ) ∈ ball z ρ}
        {x | (x : ℂ) ∈ ball w ρ} ≤ K * M₁.internal (ball (0 : ℂ) (3 * R)) (⟨z, hz⟩, ⟨w, hw⟩)) :
    L ≤ K * Y := by
  have hr0 : r ≠ 0 := hr.ne'
  
  have hA' : aroundDist (dilateM M₁ r hr0) (annAt 0 1 2 one_pos one_lt_two) < Y := by
    rw [aroundDist_dilateM M₁ hr 0 one_pos one_lt_two, smul_zero]; exact hA
  have hU3 : (annAt 0 1 2 one_pos one_lt_two).toSet ⊆ ball (0 : ℂ) 3 := by
    intro x hx
    rw [annAt_toSet] at hx
    rw [mem_ball, dist_zero_right]
    have := hx.2; rw [sub_zero] at this; linarith
  obtain ⟨z, w, hz, hw, hcfg, hint⟩ := exists_loop_points_of_aroundDist_lt (dilateM M₁ r hr0) hU3 hA'
  
  have hY3 : ∀ u : ℂ, r • u ∈ ball (0 : ℂ) (3 * r) ↔ u ∈ ball (0 : ℂ) 3 := by
    intro u
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hint' := WeakStrong.internal_dilateM M₁ r hr0 (ball (0 : ℂ) 3) (ball (0 : ℂ) (3 * r)) hY3
    (⟨z, hz⟩, ⟨w, hw⟩)
  rw [hint'] at hint
  have hsub : ball (0 : ℂ) (3 * r) ⊆ ball (0 : ℂ) (3 * R) := ball_subset_ball (by linarith)
  have hzR : r • z ∈ ball (0 : ℂ) (3 * R) := hsub ((hY3 z).2 hz)
  have hwR : r • w ∈ ball (0 : ℂ) (3 * R) := hsub ((hY3 w).2 hw)
  have hanti := Uniqueness.Objects.Producer.internal_anti M₁ hsub ((hY3 z).2 hz) ((hY3 w).2 hw)
  have hupper : M₂.internalSetDist (thickening ρ (ball (0 : ℂ) (3 * R)))
      {x | (x : ℂ) ∈ ball (r • z) ρ} {x | (x : ℂ) ∈ ball (r • w) ρ} ≤ K * Y :=
    (hcmp (r • z) (r • w) hzR hwR).trans (mul_le_mul_right (hanti.trans hint.le) K)
  
  refine le_trans ?_ hupper
  apply le_internalSetDist_of_dilateM M₂ hr
  rw [inv_smul_smul₀ hr0, inv_smul_smul₀ hr0]
  have hVb : Bornology.IsBounded {x : ℂ | r • x ∈ thickening ρ (ball (0 : ℂ) (3 * R))} := by
    refine (isBounded_ball (x := (0 : ℂ)) (r := (ρ + 3 * R) / r)).subset fun x hx => ?_
    have hx' := thickening_ball hρ0 (by linarith : 0 < 3 * R) (0 : ℂ) ▸ hx
    rw [mem_ofPred_eq, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr] at hx'
    rw [mem_ball, dist_zero_right, lt_div_iff₀ hr]
    linarith
  have hρr : ρ / r ≤ 1 / 16 := by
    rw [div_le_iff₀ hr]; linarith
  refine le_internalSetDist_of_net (dilateM M₂ r hr0) hVb hρr hcfg ?_
  intro b i hi
  calc L ≤ acrossDist M₂ (annAt (r • netPt b i) (r * (1 / 8)) (r * (1 / 4))
        (mul_pos hr (by norm_num)) (mul_lt_mul_of_pos_left (by norm_num) hr)) := hnet b i hi
    _ = acrossDist (dilateM M₂ r hr0) (annAt (netPt b i) (1 / 8) (1 / 4) (by norm_num)
          (by norm_num)) := (acrossDist_dilateM M₂ hr _ _ _).symm
    _ ≤ acrossIn (dilateM M₂ r hr0) (netPt b i) (1 / 8) (1 / 4) := acrossDist_le_acrossIn _ _ _ _
    _ = acr (dilateM M₂ r hr0) (netPt b i) (1 / 8) (1 / 4) := acrossIn_eq_acr _ _ _ _

end SupercriticalLQGUniqueness.B2.Polylog
