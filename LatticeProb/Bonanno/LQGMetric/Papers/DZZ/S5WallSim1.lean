/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61P1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW6

/-!
# P-317K-SIM, part 1: the probabilistic tools of the similarity transfer (DEC-123 §3)

DZZ (arXiv:1807.00422) uses Proposition 3.17 for walls that are not dyadic (squares of side
`1/10`, the rotated boxes `𝕍̃_{u,v}`; Remark 5.2 and l. 611–624). We obtain it from the dyadic walled
P3.17 at a fixed box `B̄₀` by the similarity coupling. This file holds the general tools:

* `wsim_abs_sub_integral_le`: a nonnegative `X ∈ L²` with `a ≤ X ≤ b` outside an event of
  probability `≤ p ≤ 1/4` satisfies `|X − E X| ≤ (b − a) + 4 M √p` on `{a ≤ X ≤ b}`, where
  `E X² ≤ M²` (own elementary proof: `integral_ge_of_ae_le_off`, S6L61P1, and Chebyshev);
* `wsim_log_le_of_le`, `wsim_log_le_add_log`: `log ∘ toNat` on finite walled distances
  (`D ≥ 1`, `one_le_lgdDZZ`);
* `cor39_boundOn`: **walled DZZ Corollary 3.9** (l. 1235–1244) from the walled P3.2 and L3.5, a
  copy of `cor39_bound` (S3L9) with `prop32EventOn`, `lem35EventOn`;
* `ae_lgdMinSet_wall_lt_top`: a.s. finiteness of `min D^{K}_δ(A, B)` for a convex wall
  `K ⊆ (0,1)²` and points of `int K` (pattern of `ae_lgd_tilde_lt_top`, S5L53Side).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Window of the mean from a sandwich** (own elementary proof). -/
theorem wsim_abs_sub_integral_le {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX0 : ∀ ω, 0 ≤ X ω) (hX : MemLp X 2 P) {M a b p : ℝ} (hM : 0 < M)
    (hXM : ∫ ω, X ω ^ 2 ∂P ≤ M ^ 2) (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (hG : P {ω | ¬ (a ≤ X ω ∧ X ω ≤ b)} ≤ ENNReal.ofReal p) {ω : Ω} (ha : a ≤ X ω)
    (hb : X ω ≤ b) : |X ω - ∫ ω', X ω' ∂P| ≤ (b - a) + 4 * M * Real.sqrt p := by
  set Bd := {ω | ¬ (a ≤ X ω ∧ X ω ≤ b)} with hBd
  have hBr : P.real Bd ≤ p := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hp.le hG
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have hXi : Integrable X P := hX.integrable one_le_two
  have hb0 : 0 ≤ b := (hX0 ω).trans hb
  -- upper bound
  have hup : ∫ ω', X ω' ∂P ≤ b + 2 * M * Real.sqrt p := by
    have h := integral_ge_of_ae_le_off (P := P) (X := fun _ => b) (Y := X) (Bd := Bd)
      (fun _ => hb0) (integrable_const b) hX
      (Eventually.of_forall fun ω' hω' => by
        by_contra hc; exact hω' fun h => hc h.2) (t := M / Real.sqrt p) (by positivity)
    rw [integral_const, smul_eq_mul, probReal_univ, one_mul] at h
    have e1 : M / Real.sqrt p * P.real Bd ≤ M * Real.sqrt p := by
      calc M / Real.sqrt p * P.real Bd ≤ M / Real.sqrt p * p := by gcongr
        _ = M * Real.sqrt p := by rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
    have e2 : (∫ ω', X ω' ^ 2 ∂P) / (M / Real.sqrt p) ≤ M * Real.sqrt p := by
      rw [div_le_iff₀ (by positivity)]
      calc ∫ ω', X ω' ^ 2 ∂P ≤ M ^ 2 := hXM
        _ = M * Real.sqrt p * (M / Real.sqrt p) := by field_simp
    linarith
  -- lower bound
  have hlo : a - 4 * M * Real.sqrt p ≤ ∫ ω', X ω' ∂P := by
    rcases le_or_gt a 0 with ha0 | ha0
    · have : 0 ≤ ∫ ω', X ω' ∂P := integral_nonneg hX0
      nlinarith [hsp, hM]
    · -- Chebyshev: `a ≤ 2 M`
      have hX2i : Integrable (fun ω' => X ω' ^ 2) P := hX.integrable_sq
      have hch := mul_meas_ge_le_integral_of_nonneg (μ := P)
        (Eventually.of_forall fun ω' => sq_nonneg (X ω')) hX2i (a ^ 2)
      have hsub : Bdᶜ ⊆ {ω' | a ^ 2 ≤ X ω' ^ 2} := fun ω' hω' => by
        simp only [hBd, mem_compl_iff, mem_ofPred_eq, not_not] at hω'
        exact pow_le_pow_left₀ ha0.le hω'.1 2
      have hmeas : 3 / 4 ≤ P.real {ω' | a ^ 2 ≤ X ω' ^ 2} := by
        have h1 := measureReal_mono (μ := P) hsub
        have h2 := measureReal_union_le (μ := P) Bd Bdᶜ
        rw [union_compl_self, probReal_univ] at h2
        linarith
      have ha2 : a ≤ 2 * M := by nlinarith
      have h := integral_ge_of_ae_le_off (P := P) (X := X) (Y := fun _ => a) (Bd := Bd)
        hX0 hXi (memLp_const a)
        (Eventually.of_forall fun ω' hω' => by
          by_contra hc; exact hω' fun h => hc h.1) (t := a / Real.sqrt p) (by positivity)
      rw [integral_const, smul_eq_mul, probReal_univ, one_mul, integral_const, smul_eq_mul,
        probReal_univ, one_mul] at h
      have e1 : a / Real.sqrt p * P.real Bd ≤ a * Real.sqrt p := by
        calc a / Real.sqrt p * P.real Bd ≤ a / Real.sqrt p * p := by gcongr
          _ = a * Real.sqrt p := by rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
      have e2 : a ^ 2 / (a / Real.sqrt p) = a * Real.sqrt p := by field_simp
      nlinarith
  have hMp : 0 ≤ M * Real.sqrt p := by positivity
  rw [abs_le]; constructor <;> linarith

/-- `log ∘ toNat` is monotone on walled distances below a finite one. -/
lemma wsim_log_le_of_le {n m : ℕ∞} (hn : 1 ≤ n) (hm : m ≠ ⊤) (h : n ≤ m) :
    Real.log (n.toNat : ℝ) ≤ Real.log (m.toNat : ℝ) := by
  have hn' : n ≠ ⊤ := ne_top_of_le_ne_top hm h
  have h1 : 1 ≤ n.toNat := by
    have := ENat.toNat_le_toNat hn hn'; simpa using this
  have h2 := ENat.toNat_le_toNat h hm
  exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- `log n ≤ log m + log F` from `n ≤ m F` (`n ≥ 1`, `m` finite, `F ≥ 1`). -/
lemma wsim_log_le_add_log {n m : ℕ∞} {F : ℝ} (hn : 1 ≤ n) (hm : m ≠ ⊤) (hF : 1 ≤ F)
    (h : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) * ENNReal.ofReal F) :
    Real.log (n.toNat : ℝ) ≤ Real.log (m.toNat : ℝ) + Real.log F := by
  induction m using ENat.recTopCoe with
  | top => exact absurd rfl hm
  | coe k =>
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      have hlt : ((k : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal F < ⊤ :=
        ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
      rw [ENat.toENNReal_top] at h
      exact hlt.ne (top_le_iff.mp h)
    | coe j =>
      simp only [ENat.toNat_natCast, ENat.toENNReal_coe] at h ⊢
      rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg k),
        ← ENNReal.ofReal_natCast j,
        ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg k) (by linarith))] at h
      have hj : (1 : ℝ) ≤ j := by exact_mod_cast hn
      have hk : (0 : ℝ) < k := by
        by_contra hk; push Not at hk
        have : (k : ℝ) = 0 := le_antisymm hk (Nat.cast_nonneg k)
        rw [this, zero_mul] at h; linarith
      have := Real.log_le_log (by linarith) h
      rwa [Real.log_mul hk.ne' (by linarith)] at this

variable {P : Measure Ω}

/-- **Walled DZZ Corollary 3.9, uniform core** (l. 1235–1244; copy of `cor39_bound`, S3L9, with
the walled events). -/
theorem cor39_boundOn {γ ξ ξd : ℝ} (hξd : 0 ≤ ξd) {K : Set ℂ} {S : Set DyBox}
    {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ}
    (h32 : DZZProp32UOn P γ W K S μ ξ ξd) (h35 : DZZLemma35UOn P γ W K S ξ ξd) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioo (0 : ℝ) δ,
      ∀ A B : Set ℂ, IsXiAdmissibleAtIn K ξ ξd δ A B →
        P (cor39Event μ δ δ' A B)ᶜ ≤ ENNReal.ofReal (3 * δ ^ c) := by
  obtain ⟨c₁, hc₁, δ₁, hδ₁, h₁⟩ := h32
  obtain ⟨c₃, hc₃, δ₃, hδ₃, h₃⟩ := h35
  refine ⟨min c₁ c₃, lt_min hc₁ hc₃, min (min δ₁ δ₃) 1, by positivity, min_le_right _ _,
    fun δ hδ δ' hδ' A B hAB => ?_⟩
  have hδa : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₃ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le (min_le_right _ _)
  have hsub : prop32EventOn S γ W μ δ A B ∩ prop32EventOn S γ W μ δ' A B ∩
      lem35EventOn S γ W δ δ' A B ⊆ cor39Event μ δ δ' A B := by
    rintro ω ⟨⟨⟨E1, -⟩, ⟨-, E2⟩⟩, E3⟩
    exact cor39_chain (pow_nonneg (div_nonneg hδ.1.le hδ'.1.le) 3) E1 E2 E3
  refine (measure_mono (compl_subset_compl.mpr hsub)).trans ?_
  rw [compl_inter, compl_inter]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
  have e1 := h₁ δ ⟨hδ.1, hδa⟩ A B hAB
  have e2 := h₁ δ' ⟨hδ'.1, hδ'.2.trans hδa⟩ A B
    ⟨hAB.1.mono hξd hδ'.1.le hδ'.2.le, hAB.2⟩
  have e3 := h₃ δ ⟨hδ.1, hδb⟩ δ' hδ' A B hAB
  refine (add_le_add (add_le_add e1 e2) e3).trans ?_
  have p1 := Real.rpow_nonneg hδ.1.le c₁
  have p2 := Real.rpow_nonneg hδ'.1.le c₁
  have p3 := Real.rpow_nonneg hδ.1.le c₃
  rw [← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3]
  refine ENNReal.ofReal_le_ofReal ?_
  have m1 : δ ^ c₁ ≤ δ ^ min c₁ c₃ :=
    Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ1.le (min_le_left _ _)
  have m2 : δ' ^ c₁ ≤ δ ^ c₁ := Real.rpow_le_rpow hδ'.1.le hδ'.2.le hc₁.le
  have m3 : δ ^ c₃ ≤ δ ^ min c₁ c₃ :=
    Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ1.le (min_le_right _ _)
  linarith

/-- **a.s. finiteness of a walled `min D_δ(A, B)`** for a convex wall `K ⊆ (0,1)²` and
`A ∋ x`, `B ∋ y` with `x, y ∈ int K` (pattern of `ae_lgd_tilde_lt_top`, S5L53Side). -/
theorem ae_lgdMinSet_wall_lt_top {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ} (hKc : Convex ℝ K) (hKm : MeasurableSet K)
    (hKo : K ⊆ openSquare) {δ : ℝ} (hδ : 0 < δ) {A B : Set ℂ} {x y : ℂ} (hx : x ∈ A)
    (hy : y ∈ B) (hxi : x ∈ interior K) (hyi : y ∈ interior K) :
    ∀ᵐ ω ∂P, lgdMinSet (dzzWall K (dzzMuIn γ W ω)) δ A B < ⊤ := by
  filter_upwards [ae_wickQArea_reg hW hγ hγ2] with ω hω
  obtain ⟨hK, hat⟩ := hω
  have hOV : openSquare ⊆ dzzV := fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hw : ∀ L ⊆ interior K, dzzWall K (dzzMuIn γ W ω) L = wickQArea γ W ω L := fun L hL => by
    rw [dzzWall_apply_of_subset hKm (hL.trans interior_subset), dzzMuIn,
      dzzWall_apply_of_subset measurableSet_dzzV
        (hL.trans (interior_subset.trans (hKo.trans hOV)))]
  have hlt : lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ x y < ⊤ :=
    lgdDZZ_lt_top_of_convex isOpen_interior hKc.interior
      (fun L hLc hLK => by rw [hw L hLK]; exact hK L hLc (hLK.trans (interior_subset.trans hKo)))
      (fun z hz => by
        rw [hw {z} (singleton_subset_iff.mpr hz)]; exact hat z (hKo (interior_subset hz)))
      hδ hxi hyi
  exact ((iInf₂_le x hx).trans (iInf₂_le y hy)).trans_lt hlt

end DZZ
end LQGMetric
