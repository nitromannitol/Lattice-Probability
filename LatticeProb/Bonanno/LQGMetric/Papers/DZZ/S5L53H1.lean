/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53H1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Mono
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F1

/-!
# DZZ Lemma 5.3, the `d_i` comparison, part 1: tools (P2-DZZ53H)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2380–2391 ((Eq.calD1)):
`d_i ≤ e^{(log δ⁻¹)^{0.92}} D̃^{(i)} ≤ e^{(log δ⁻¹)^{0.94}} exp{E log D̃_δ(u,v)}`
"by Proposition 3.2, Lemmas 2.9, 3.8, 3.10, Corollary 3.9 and (eq-coupling-comparison)".

This file:
* `approxLGDIn_mono`: (eq-280318b) (DZZ l. 919–923) for the walled `D'^K` (cells meeting `K`):
  `D'^K_δ ≤ D'^K_{δ'}` for `δ' ≤ δ` (copy of `approxDist_mono`, S3L5Mono, for `cellGraphOn`;
  the `δ`-cell containing a cell meeting `K` meets `K`);
* `l53hA`, `l53hB`: the similarity `θ_{x,y} = simMap (8(y−x)) (x − 8(y−x)p₁)` with
  `θ(p₁) = x`, `θ(p₂) = y`, `θ(B̄₀) = 𝕍̃_{x,y}` (`B̄₀ = wsimB₀`, `p₁ = (5/16,3/8)`,
  `p₂ = (7/16,3/8)`, `wsimB₀_eq_tildeBox`, S5WallSim4);
* `l53W_mem_dzzVbar`, `l53W_ne`: the points `w_i` lie in `𝕍̄` and are distinct;
* `l53h_tail`: the tail comparison through one similarity coupling (DZZ lem-scaling-coupling,
  l. 611–624; `dzzSimCoupleU_of_norm_le`) with the law transfer `wsim_prob_lgdMinSet_wall_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-! ### (eq-280318b) for the walled `D'^K` -/

section Mono

variable {m : DyBox → ℝ} {δ : ℝ}

/-- A walk of `δ'`-cells of `S` maps to a walk of their `δ`-cells, inside `S` when `S` is closed
under passing to larger boxes (copy of `exists_walk_cellAnc`, S3L5Mono). -/
lemma l53h_exists_walk_cellAnc {S : Set DyBox}
    (hS : ∀ b c : DyBox, b ∈ S → b.closedBox ⊆ c.closedBox → c ∈ S) {δ' : ℝ}
    (hδ : δ' ^ 2 ≤ δ ^ 2) {x y : DyBox} (p : (cellGraphOn S m δ').Walk x y) :
    ∃ q : (cellGraphOn S m δ).Walk (cellAnc m δ x) (cellAnc m δ y), q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨.nil, le_rfl⟩
  | @cons x z y hadj p ih =>
    obtain ⟨q, hq⟩ := ih
    have hx := hadj.1.1; have hz := hadj.1.2.1; have hn := hadj.1.2.2
    have mx : m x < δ ^ 2 := lt_of_lt_of_le hx.1 hδ
    have mz : m z < δ ^ 2 := lt_of_lt_of_le hz.1 hδ
    obtain ⟨-, -, -, cx⟩ := cellAnc_spec (m := m) (δ := δ) mx
    obtain ⟨-, -, -, cz⟩ := cellAnc_spec (m := m) (δ := δ) mz
    have sx := hS _ _ hadj.2.1 (closedBox_sub_cellAnc mx)
    have sz := hS _ _ hadj.2.2 (closedBox_sub_cellAnc mz)
    rcases eq_or_neighbour_of_sub hn (closedBox_sub_cellAnc mx) (closedBox_sub_cellAnc mz) with
      he | hN
    · refine ⟨q.copy he.symm rfl, ?_⟩
      rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons]; omega
    · refine ⟨.cons (show (cellGraphOn S m δ).Adj _ _ from ⟨⟨cx, cz, hN⟩, sx, sz⟩) q, ?_⟩
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]; omega

/-- (eq-280318b) for `D'` through the cells of an upward closed family `S`. -/
theorem l53h_approxDistOn_mono {S : Set DyBox}
    (hS : ∀ b c : DyBox, b ∈ S → b.closedBox ⊆ c.closedBox → c ∈ S) {δ' : ℝ}
    (hδ : δ' ^ 2 ≤ δ ^ 2) (u v : ℂ) :
    approxDistOn S m δ u v ≤ approxDistOn S m δ' u v := by
  unfold approxDistOn
  refine le_iInf fun b => le_iInf fun b' => le_iInf fun hb => le_iInf fun hb' => ?_
  have mb : m b < δ ^ 2 := lt_of_lt_of_le hb.1.1 hδ
  have mb' : m b' < δ ^ 2 := lt_of_lt_of_le hb'.1.1 hδ
  obtain ⟨i, hi, he, hc⟩ := cellAnc_spec (m := m) (δ := δ) mb
  obtain ⟨i', hi', he', hc'⟩ := cellAnc_spec (m := m) (δ := δ) mb'
  have hu : (cellAnc m δ b).Mem u := by rw [he]; exact mem_anc hb.2.1 hi
  have hv : (cellAnc m δ b').Mem v := by rw [he']; exact mem_anc hb'.2.1 hi'
  have sb := hS _ _ hb.2.2 (closedBox_sub_cellAnc mb)
  have sb' := hS _ _ hb'.2.2 (closedBox_sub_cellAnc mb')
  refine (iInf_le_of_le (cellAnc m δ b) (iInf_le_of_le (cellAnc m δ b')
    (iInf_le_of_le (show IsCell m δ (cellAnc m δ b) ∧ (cellAnc m δ b).Mem u ∧
      cellAnc m δ b ∈ S from ⟨hc, hu, sb⟩)
      (iInf_le_of_le (show IsCell m δ (cellAnc m δ b') ∧ (cellAnc m δ b').Mem v ∧
        cellAnc m δ b' ∈ S from ⟨hc', hv, sb'⟩) le_rfl)))).trans ?_
  gcongr
  by_cases ht : (cellGraphOn S m δ').edist b b' = ⊤
  · rw [ht]; exact le_top
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top ht
    obtain ⟨q, hq⟩ := l53h_exists_walk_cellAnc hS hδ p
    rw [← hp]
    exact (SimpleGraph.edist_le q).trans (by exact_mod_cast hq)

end Mono

lemma cellsMeeting_upClosed (K : Set ℂ) :
    ∀ b c : DyBox, b ∈ cellsMeeting K → b.closedBox ⊆ c.closedBox → c ∈ cellsMeeting K :=
  fun _ _ ⟨z, hz1, hz2⟩ h => ⟨z, h hz1, hz2⟩

/-- **(eq-280318b) for the walled `D'^K`**: `D'^K_δ(u,v) ≤ D'^K_{δ'}(u,v)` for `0 ≤ δ' ≤ δ`. -/
theorem approxLGDIn_mono {Ω : Type*} [MeasurableSpace Ω] (K : Set ℂ) (γ : ℝ)
    (W : WNSpace → Ω → ℝ) {δ δ' : ℝ} (hδ' : 0 ≤ δ') (h : δ' ≤ δ) (u v : ℂ) (ω : Ω) :
    approxLGDIn K γ W δ u v ω ≤ approxLGDIn K γ W δ' u v ω :=
  l53h_approxDistOn_mono (cellsMeeting_upClosed K) (pow_le_pow_left₀ hδ' h 2) u v

/-! ### The similarity `B̄₀ → 𝕍̃_{x,y}` -/

/-- `a = 8(y − x)`. -/
def l53hA (x y : ℂ) : ℂ := 8 * (y - x)

/-- `b = x − a p₁`. -/
def l53hB (x y : ℂ) : ℂ := x - l53hA x y * ⟨5 / 16, 3 / 8⟩

lemma l53h_sim_p₁ (x y : ℂ) : simMap (l53hA x y) (l53hB x y) ⟨5 / 16, 3 / 8⟩ = x := by
  simp only [simMap, l53hB]; ring

lemma l53h_sim_p₂ (x y : ℂ) : simMap (l53hA x y) (l53hB x y) ⟨7 / 16, 3 / 8⟩ = y := by
  have e : (⟨7 / 16, 3 / 8⟩ : ℂ) = ⟨5 / 16, 3 / 8⟩ + ((1 / 8 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> norm_num
  simp only [simMap, l53hB, l53hA, e]; push_cast; ring

lemma l53hA_ne {x y : ℂ} (h : x ≠ y) : l53hA x y ≠ 0 :=
  mul_ne_zero (by norm_num) (sub_ne_zero.2 h.symm)

lemma l53h_sim_image {x y : ℂ} (h : x ≠ y) :
    simMap (l53hA x y) (l53hB x y) '' wsimB₀.closedBox = tildeBox x y := by
  rw [wsimB₀_eq_tildeBox, simMap_image_tildeBox (l53hA_ne h), l53h_sim_p₁, l53h_sim_p₂]

lemma l53hA_norm_le {x y : ℂ} (hx : x ∈ dzzVbar) (hy : y ∈ dzzVbar) : ‖l53hA x y‖ ≤ 1 := by
  obtain ⟨hu1, hu2⟩ := near_of_mem_dzzVbar hx
  obtain ⟨hv1, hv2⟩ := near_of_mem_dzzVbar hy
  have h := Complex.norm_le_abs_re_add_abs_im (y - x)
  have e1 : |(y - x).re| ≤ 1 / 20 := by
    rw [Complex.sub_re, abs_le]; rw [abs_le] at hu1 hv1; constructor <;> linarith
  have e2 : |(y - x).im| ≤ 1 / 20 := by
    rw [Complex.sub_im, abs_le]; rw [abs_le] at hu2 hv2; constructor <;> linarith
  simp only [l53hA, norm_mul]
  norm_num
  linarith

lemma l53hA_w (u v : ℂ) (i : ℕ) :
    l53hA (l53W u v i) (l53W u v (i + 1)) = ((1 / 9 : ℝ) : ℂ) * l53hA u v := by
  simp only [l53hA, l53W]; push_cast; ring

lemma l53hA_w_norm (u v : ℂ) (i : ℕ) :
    ‖l53hA (l53W u v i) (l53W u v (i + 1))‖ = ‖l53hA u v‖ / 9 := by
  rw [l53hA_w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]; ring

/-! ### The points `w_i` -/

lemma l53W_mem_dzzVbar {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) {i : ℕ} (hi : i ≤ 9) :
    l53W u v i ∈ dzzVbar := by
  have ht0 : (0 : ℝ) ≤ (i : ℝ) / 9 := by positivity
  have ht1 : (i : ℝ) / 9 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact_mod_cast hi
  have hre : (l53W u v i).re = u.re + (i : ℝ) / 9 * (v.re - u.re) := by
    simp [l53W, Complex.add_re, Complex.mul_re]
  have him : (l53W u v i).im = u.im + (i : ℝ) / 9 * (v.im - u.im) := by
    simp [l53W, Complex.add_im, Complex.mul_im]
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  simp only at hu1 hu2 hv1 hv2
  refine ⟨?_, ?_⟩
  · simp only
    rw [hre, abs_le]
    rw [abs_le] at hu1 hv1
    constructor <;> nlinarith
  · simp only
    rw [him, abs_le]
    rw [abs_le] at hu2 hv2
    constructor <;> nlinarith

lemma l53W_succ_sub (u v : ℂ) (i : ℕ) : l53W u v (i + 1) - l53W u v i = (v - u) / 9 := by
  simp only [l53W]; push_cast; ring

lemma l53W_ne {u v : ℂ} (huv : u ≠ v) (i : ℕ) : l53W u v i ≠ l53W u v (i + 1) := by
  intro h
  have := l53W_succ_sub u v i
  rw [h, sub_self] at this
  exact huv (by linear_combination (9 : ℂ) * this)

/-! ### The tail comparison through one coupling -/

lemma l53h_tail_aux {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsFiniteMeasure P']
    {E A B : Set Ω'} {c : ℝ} (hE : P'.real E ≤ c) (h : ∀ ω, ω ∉ E → ω ∈ A → ω ∈ B) :
    P' A ≤ ENNReal.ofReal c + P' B := by
  have hsub : A ⊆ E ∪ B := fun ω hω => by
    by_cases he : ω ∈ E
    · exact Or.inl he
    · exact Or.inr (h ω he hω)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ le_rfl))
  rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal hE

/-- **Tails through one similarity coupling** (DZZ lem-scaling-coupling, l. 611–624, for the
walls `B̄₀` and `θB̄₀`): for every white noise, the law of `D^{θB̄₀}_{‖a‖δe^{±λ}}(θx, θy)` is
compared with that of `D^{B̄₀}_δ(x, y)` up to `C e^{−λ²/C}`. -/
theorem l53h_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a b : ℂ} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (hKV : simMap a b '' wsimB₀.closedBox ⊆ dzzVXi (1 / 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 ≤ lam → ∀ x ∈ wsimB₀.closedBox, ∀ y ∈ wsimB₀.closedBox,
      ∀ δ : ℝ, 0 < δ → ∀ R : ℝ≥0∞,
      P {ω | R < ((lgdDZZ (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω))
          (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * Real.exp (-lam ^ 2 / C)) +
          P {ω | R < ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δ x y : ℕ∞) : ℝ≥0∞)} ∧
      P {ω | R < ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δ x y : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * Real.exp (-lam ^ 2 / C)) +
          P {ω | R < ((lgdDZZ (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω))
            (‖a‖ * δ * Real.exp (-lam)) (simMap a b x) (simMap a b y) : ℕ∞) : ℝ≥0∞)} := by
  obtain ⟨C, hC, hcpl⟩ := dzzSimCoupleU_of_norm_le hγ hγ2 (ξ := 1 / 4) (by norm_num)
    (by norm_num) (isClosed_closedBox wsimB₀) (wsimB₀_subset_dzzVXi (by norm_num) le_rfl) ha ha1
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hcp⟩ := hcpl b hKV
  have := hW₂.isProbabilityMeasure
  refine ⟨C, hC, fun lam hlam x hx y hy δ hδ R => ?_⟩
  have tr := fun (W' : WNSpace → Ω' → ℝ) (hW' : IsWhiteNoise P' W') (K : Set ℂ) (δ' : ℝ)
      (p q : ℂ) => by
    have e := wsim_prob_lgdMinSet_wall_eq hW hW' hγ hγ2 K δ' {p} {q}
      {n : ℕ∞ | R < (n : ℝ≥0∞)}
    simp only [lgdMinSet_singleton, mem_ofPred_eq] at e
    exact e
  constructor
  · rw [tr W₂ hW₂, tr W₁ hW₁]
    refine l53h_tail_aux (hcp lam hlam) fun ω hω hA => ?_
    simp only [mem_ofPred_eq, not_not] at hω hA ⊢
    exact hA.trans_le (ENat.toENNReal_le.2 (hω x hx y hy δ hδ).1)
  · rw [tr W₁ hW₁, tr W₂ hW₂]
    refine l53h_tail_aux (hcp lam hlam) fun ω hω hA => ?_
    simp only [mem_ofPred_eq, not_not] at hω hA ⊢
    exact hA.trans_le (ENat.toENNReal_le.2 (hω x hx y hy δ hδ).2)

end DZZ
end LQGMetric
