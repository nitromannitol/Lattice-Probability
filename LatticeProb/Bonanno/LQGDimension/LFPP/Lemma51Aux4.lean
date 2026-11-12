/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51Aux4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux3

/-!
# Lemma 5.1, auxiliary file 4: the Gram-level lower bound (5.4)

For a finitely supported probability `μ = Σ_{z ∈ S} w_z δ_z` on the tube and Gram vectors `u`
realising `bandCov a b` on the block points, put `V_h = Σ_i Σ_z (w_z/M) u(T^h_i z)` (so that
`⟨X, ν^h_μ⟩ = ⟪V_h, x⟫`).  Then

* `norm_vecV_sub_sq`: `‖V_f - V_g‖² = B(m₁, m₁)` for the point combination
  `m₁ = ν^f_μ - ν^g_μ` and the band form `B = bandForm a b`;
* `cross_total`: `B(m₁, μ_{δ,f} - μ_{δ,g}) / δ ≥ (1 - κ) d(f,g)² - E₁ - o(1)`, with
  `κ = 2K/(√π R)` (scales above `b = δR`), `E₁ = (4π√(2E₀) + 4πK + 16√π R)/M` (scale cutoff
  `a = 4δR/M`, quadrature, and the offset `ζ`) and an explicit `o(1)`;
* `gram_lower`: **(5.4)** — for all small `δ`, uniformly over `S, w, u`,
  `‖V_f - V_g‖²/δ ≥ (1 - 2κ - θ₀) d(f,g)² - 2E₁`, using Cauchy–Schwarz
  `B(m₁,m₁) ≥ 2B(m₁,m₂) - B(m₂,m₂)`, `B(m₂,m₂) ≤ logCov(m₂,m₂)` and the graph covariance limit.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

open Blueprint.Draft HeatKernel

/-! ## Block points and Gram vectors -/

/-- The index set `range M × S` of block points. -/
def bIdx (n : ℕ) (S : Finset ℂ) : Finset (ℕ × ℂ) := Finset.range (16 ^ n) ×ˢ S

/-- The weights `w_z / M`. -/
def bW (n : ℕ) (w : ℂ → ℝ) (k : ℕ × ℂ) : ℝ := w k.2 / (16 : ℝ) ^ n

/-- The block points `T^h_i z`. -/
def bP (n : ℕ) (δ : ℝ) (h : ℝ → ℝ) (k : ℕ × ℂ) : ℂ := edgeSim (16 ^ n) δ h k.1 k.2

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Σ_i Σ_z (w_z/M) u(T^h_i z)`. -/
def vecV (n : ℕ) (δ : ℝ) (S : Finset ℂ) (w : ℂ → ℝ) (u : ℂ → E) (h : ℝ → ℝ) : E :=
  ∑ i ∈ Finset.range (16 ^ n), ∑ z ∈ S, (w z / (16 : ℝ) ^ n) • u (edgeSim (16 ^ n) δ h i z)

lemma vecV_eq (n : ℕ) (δ : ℝ) (S : Finset ℂ) (w : ℂ → ℝ) (u : ℂ → E) (h : ℝ → ℝ) :
    vecV n δ S w u h = ∑ k ∈ bIdx n S, bW n w k • u (bP n δ h k) := by
  unfold vecV bIdx bW bP
  rw [Finset.sum_product]

end Gram

/-- The point combination `ν^f_μ - ν^g_μ`. -/
def mOne (n : ℕ) (δ : ℝ) (S : Finset ℂ) (w : ℂ → ℝ) (f g : ℝ → ℝ) : SegComb :=
  (ptComb (bIdx n S) (bW n w) (bP n δ f)).sub (ptComb (bIdx n S) (bW n w) (bP n δ g))

lemma sum4 {ι : Type*} (I : Finset ι) (X Y Z W : ι → ι → ℝ) :
    (∑ k ∈ I, ∑ l ∈ I, X k l) - (∑ k ∈ I, ∑ l ∈ I, Y k l) -
      ((∑ k ∈ I, ∑ l ∈ I, Z k l) - ∑ k ∈ I, ∑ l ∈ I, W k l) =
      ∑ k ∈ I, ∑ l ∈ I, (X k l - Y k l - Z k l + W k l) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

lemma norm_vecV_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (δ : ℝ) (S : Finset ℂ) (w : ℂ → ℝ) (u : ℂ → E)
    (f g : ℝ → ℝ)
    (hG : ∀ h h' : ℝ → ℝ, (h = f ∨ h = g) → (h' = f ∨ h' = g) → ∀ k ∈ bIdx n S,
      ∀ l ∈ bIdx n S, ⟪u (bP n δ h k), u (bP n δ h' l)⟫ = bandCov a b (bP n δ h k) (bP n δ h' l)) :
    ‖vecV n δ S w u f - vecV n δ S w u g‖ ^ 2 =
      bandForm a b (mOne n δ S w f g) (mOne n δ S w f g) := by
  have hv : vecV n δ S w u f - vecV n δ S w u g =
      ∑ k ∈ bIdx n S, bW n w k • (u (bP n δ f k) - u (bP n δ g k)) := by
    rw [vecV_eq, vecV_eq, ← Finset.sum_sub_distrib]
    simp_rw [smul_sub]
  rw [hv, ← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  rw [mOne, bandForm_sub_left ha hab, bandForm_sub_right ha hab, bandForm_sub_right ha hab,
    bandForm_ptComb_ptComb ha hab, bandForm_ptComb_ptComb ha hab, bandForm_ptComb_ptComb ha hab,
    bandForm_ptComb_ptComb ha hab, sum4]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
  rw [hG f f (Or.inl rfl) (Or.inl rfl) k hk l hl, hG f g (Or.inl rfl) (Or.inr rfl) k hk l hl,
    hG g f (Or.inr rfl) (Or.inl rfl) k hk l hl, hG g g (Or.inr rfl) (Or.inr rfl) k hk l hl]
  ring

lemma bandForm_mOne_left {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (δ : ℝ) (S : Finset ℂ)
    (w : ℂ → ℝ) (f g : ℝ → ℝ) (m : SegComb) :
    bandForm a b (mOne n δ S w f g) m = ∑ k ∈ bIdx n S,
      bW n w k * bandForm a b ((pt (bP n δ f k)).sub (pt (bP n δ g k))) m := by
  rw [mOne, bandForm_sub_left ha hab, bandForm_ptComb_left ha hab, bandForm_ptComb_left ha hab,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bandForm_sub_left ha hab]; ring

lemma sum_bW (n : ℕ) (S : Finset ℂ) (w : ℂ → ℝ) (hw1 : ∑ z ∈ S, w z = 1) :
    ∑ k ∈ bIdx n S, bW n w k = 1 := by
  unfold bIdx bW
  rw [Finset.sum_product]
  simp only [← Finset.sum_div, hw1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

lemma sub_mem_V {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) : f - g ∈ V n := by
  refine ⟨by simp [hf.1, hg.1], by simp [hf.2.1, hg.2.1],
    fun x hx => by simp [hf.2.2.1 x hx, hg.2.2.1 x hx], fun k hk => ?_⟩
  obtain ⟨α, β, h⟩ := hf.2.2.2 k hk
  obtain ⟨α', β', h'⟩ := hg.2.2.2 k hk
  exact ⟨α - α', β - β', fun x hx => by simp only [Pi.sub_apply, h x hx, h' x hx]; ring⟩

/-! ## The cross term, summed over the block points -/

/-- The constant of the point perturbation: `pertB (12 δ² K²) a b = δ cP`. -/
def cP (n : ℕ) (K R : ℝ) : ℝ := 3 * K ^ 2 * (16 : ℝ) ^ n / R * √(Real.log ((16 : ℝ) ^ n / 4) / 2)

lemma cP_nonneg (n : ℕ) {K R : ℝ} (hR : 0 < R) : 0 ≤ cP n K R := by
  unfold cP; positivity

lemma pertB_eq {n : ℕ} {K R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    pertB (12 * δ ^ 2 * K ^ 2) (4 * (δ * R) / (16 : ℝ) ^ n) (δ * R) = δ * cP n K R := by
  have hM : (0 : ℝ) < (16 : ℝ) ^ n := by positivity
  have hba : δ * R / (4 * (δ * R) / (16 : ℝ) ^ n) = (16 : ℝ) ^ n / 4 := by
    field_simp
  unfold pertB cP
  rw [hba]
  have e : (12 * δ ^ 2 * K ^ 2) ^ 2 / (2 * (4 * (δ * R) / (16 : ℝ) ^ n) ^ 2) *
      Real.log ((16 : ℝ) ^ n / 4) =
      (δ * (3 * K ^ 2 * (16 : ℝ) ^ n / R)) ^ 2 * (Real.log ((16 : ℝ) ^ n / 4) / 2) := by
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

/-- **The cross term (5.6), summed over the block points**, for fixed `δ`. -/
theorem cross_total {n : ℕ} (hn : 1 ≤ n) {K R E₀ : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hκ : 2 / √π * K / R ≤ 1) {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n)
    (hfK : ∀ x, |f x| ≤ K) (hgK : ∀ x, |g x| ≤ K) (hEf : energy f ≤ E₀) (hEg : energy g ≤ E₀)
    {δ : ℝ} (hδ : 0 < δ) {S : Finset ℂ} {w : ℂ → ℝ} (hS : ↑S ⊆ tube δ K)
    (hw : ∀ z ∈ S, 0 ≤ w z) (hw1 : ∑ z ∈ S, w z = 1) :
    (1 - 2 / √π * K / R) * (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|) -
        (4 * π * √(2 * E₀) + 4 * π * K + 16 * √π * R) / (16 : ℝ) ^ n - 16 * π * δ * K ^ 2 -
        2 * (∫ u, min (2 * K * (16 : ℝ) ^ n * δ) (GraphCov.lk (2 * K + K) u)) -
        2 * cP n K R * √(bandForm (4 * (δ * R) / (16 : ℝ) ^ n) (δ * R)
          (gdiff (16 ^ n) δ f g) (gdiff (16 ^ n) δ f g)) ≤
      bandForm (4 * (δ * R) / (16 : ℝ) ^ n) (δ * R) (mOne n δ S w f g)
        (gdiff (16 ^ n) δ f g) / δ := by
  set Mr : ℝ := (16 : ℝ) ^ n with hMr
  have hM16 : (16 : ℝ) ≤ Mr := by
    rw [hMr]; calc (16 : ℝ) = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hM : 0 < Mr := by linarith
  set a := 4 * (δ * R) / Mr with ha_def
  set b := δ * R with hb_def
  have hb : 0 < b := mul_pos hδ hR
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by
    rw [ha_def, div_le_iff₀ hM]; nlinarith
  set m := gdiff (16 ^ n) δ f g with hm
  set B2 := bandForm a b m m with hB2
  set η := ∫ u, min (2 * K * (16 : ℝ) ^ n * δ) (GraphCov.lk (2 * K + K) u) with hη
  set κ := 2 / √π * K / R with hκ_def
  set c := cP n K R with hc
  have hc0 : 0 ≤ c := cP_nonneg n hR
  have hsB2 : 0 ≤ √B2 := Real.sqrt_nonneg _
  have hpert : pertB (12 * δ ^ 2 * K ^ 2) a b = δ * c := pertB_eq hR hδ
  have hsqπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hππ : π = √π * √π := (Real.mul_self_sqrt Real.pi_pos.le).symm
  -- the per-point bound
  have hk : ∀ k ∈ bIdx n S, δ * (2 * π * (1 - κ) *
      |f (((k.1 : ℝ) + k.2.re) / Mr) - g (((k.1 : ℝ) + k.2.re) / Mr)| - 4 * π * K / Mr -
      2 * η - 16 * √π * R / Mr - 2 * c * √B2) ≤
      bandForm a b ((pt (bP n δ f k)).sub (pt (bP n δ g k))) m := by
    intro k hkI
    obtain ⟨hi, hzS⟩ := Finset.mem_product.1 hkI
    have hi' : k.1 < 16 ^ n := Finset.mem_range.1 hi
    have hz : k.2 ∈ tube δ K := hS hzS
    set x := ((k.1 : ℝ) + k.2.re) / Mr with hx
    set ζ := k.2.im / (δ * Mr) with hζ
    have hζK : |ζ| ≤ 2 * K / Mr := by
      rw [hζ, abs_div, abs_of_pos (mul_pos hδ hM), div_le_div_iff₀ (mul_pos hδ hM) hM]
      have := mul_le_mul_of_nonneg_right (tube_bounds hz).1 hM.le
      linarith
    have hζK' : |ζ| ≤ K := hζK.trans (by rw [div_le_iff₀ hM]; nlinarith)
    have c1 := cross_hpt hf hg hfK hgK hδ ha hab x ζ hζK'
    have p1 := edgeSim_sub_hpt_le hf hfK hδ hi' hz
    have p2 := edgeSim_sub_hpt_le hg hgK hδ hi' hz
    have c2 := cross_pert ha hab p1 p2 m
    rw [hpert] at c2
    have e1 : 4 * √π * a = δ * (16 * √π * R / Mr) := by rw [ha_def]; field_simp; ring
    have hπs : π / √π = √π := by rw [div_eq_iff hsqπ.ne']; exact hππ
    have hκπ : 2 * π * κ = 4 * √π * K / R := by
      calc 2 * π * κ = 4 * (π / √π) * K / R := by rw [hκ_def]; ring
        _ = 4 * √π * K / R := by rw [hπs]
    have e2 : 4 * √π * δ ^ 2 * K * |f x - g x| / b = δ * (2 * π * κ * |f x - g x|) := by
      rw [hκπ, hb_def]; field_simp
    have e3 : 2 * π * |ζ| ≤ 4 * π * K / Mr := by
      have := mul_le_mul_of_nonneg_left hζK (by positivity : (0:ℝ) ≤ 2 * π)
      calc 2 * π * |ζ| ≤ 2 * π * (2 * K / Mr) := this
        _ = 4 * π * K / Mr := by ring
    have e4 : bP n δ f k = edgeSim (16 ^ n) δ f k.1 k.2 := rfl
    have e5 : bP n δ g k = edgeSim (16 ^ n) δ g k.1 k.2 := rfl
    rw [e4, e5]
    rw [e1, e2] at c1
    have hδe3 := mul_le_mul_of_nonneg_left e3 hδ.le
    linarith
  -- summing
  have hsum := bandForm_mOne_left ha hab n δ S w f g m
  have hW := sum_bW n S w hw1
  have hbW : ∀ k ∈ bIdx n S, 0 ≤ bW n w k := fun k hk =>
    div_nonneg (hw k.2 (Finset.mem_product.1 hk).2) hM.le
  have hlow : ∑ k ∈ bIdx n S, bW n w k * (δ * (2 * π * (1 - κ) *
      |f (((k.1 : ℝ) + k.2.re) / Mr) - g (((k.1 : ℝ) + k.2.re) / Mr)| - 4 * π * K / Mr -
      2 * η - 16 * √π * R / Mr - 2 * c * √B2)) ≤ bandForm a b (mOne n δ S w f g) m := by
    rw [hsum]
    exact Finset.sum_le_sum fun k hkI => mul_le_mul_of_nonneg_left (hk k hkI) (hbW k hkI)
  -- the Riemann sum
  set wfg : ℝ → ℝ := f - g with hwfg
  have hwV : wfg ∈ V n := sub_mem_V hf hg
  have hwK : ∀ x, |wfg x| ≤ 2 * K := fun x => by
    simp only [hwfg, Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith [hfK x, hgK x])
  have hTV : ∑ i ∈ Finset.range (16 ^ n), |wfg (((i : ℝ) + 1) / 16 ^ n) - wfg ((i : ℝ) / 16 ^ n)|
      ≤ 2 * √(2 * E₀) := by
    have h1 := sum_abs_incr_le hf
    have h2 := sum_abs_incr_le hg
    have h3 : √(2 * energy f) ≤ √(2 * E₀) := Real.sqrt_le_sqrt (by linarith)
    have h4 : √(2 * energy g) ≤ √(2 * E₀) := Real.sqrt_le_sqrt (by linarith)
    calc ∑ i ∈ Finset.range (16 ^ n), |wfg (((i : ℝ) + 1) / 16 ^ n) - wfg ((i : ℝ) / 16 ^ n)|
        ≤ ∑ i ∈ Finset.range (16 ^ n), (|f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)| +
            |g (((i : ℝ) + 1) / 16 ^ n) - g ((i : ℝ) / 16 ^ n)|) := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [hwfg, Pi.sub_apply]
          rw [show f ((↑i + 1) / 16 ^ n) - g ((↑i + 1) / 16 ^ n) - (f (↑i / 16 ^ n) - g (↑i / 16 ^ n))
            = (f ((↑i + 1) / 16 ^ n) - f (↑i / 16 ^ n)) - (g ((↑i + 1) / 16 ^ n) - g (↑i / 16 ^ n))
            by ring]
          exact abs_sub _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ 2 * √(2 * E₀) := by linarith
  have hriem : ∀ z ∈ S, (∫ x in (0:ℝ)..1, |f x - g x|) - 2 * √(2 * E₀) / Mr - 8 * δ * K ^ 2 ≤
      (1 / Mr) * ∑ i ∈ Finset.range (16 ^ n), |f (((i : ℝ) + z.re) / Mr) - g (((i : ℝ) + z.re) / Mr)| := by
    intro z hzS
    obtain ⟨-, s, hs, hus⟩ := tube_bounds (hS hzS)
    have hr := riemann_lower hwV hwK hs hus
    simp only [hwfg, Pi.sub_apply] at hr hTV
    have hTV' : (1 / Mr) * ∑ i ∈ Finset.range (16 ^ n),
        |f (((i : ℝ) + 1) / 16 ^ n) - g (((i : ℝ) + 1) / 16 ^ n) -
          (f ((i : ℝ) / 16 ^ n) - g ((i : ℝ) / 16 ^ n))| ≤ 2 * √(2 * E₀) / Mr := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hTV hM.le
    rw [← hMr] at hr
    linarith
  have hRsum : (∫ x in (0:ℝ)..1, |f x - g x|) - 2 * √(2 * E₀) / Mr - 8 * δ * K ^ 2 ≤
      ∑ k ∈ bIdx n S, bW n w k *
        |f (((k.1 : ℝ) + k.2.re) / Mr) - g (((k.1 : ℝ) + k.2.re) / Mr)| := by
    have e : ∑ k ∈ bIdx n S, bW n w k *
        |f (((k.1 : ℝ) + k.2.re) / Mr) - g (((k.1 : ℝ) + k.2.re) / Mr)| =
        ∑ z ∈ S, w z * ((1 / Mr) * ∑ i ∈ Finset.range (16 ^ n),
          |f (((i : ℝ) + z.re) / Mr) - g (((i : ℝ) + z.re) / Mr)|) := by
      unfold bIdx bW
      rw [Finset.sum_product, Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hMr]; ring
    rw [e]
    calc (∫ x in (0:ℝ)..1, |f x - g x|) - 2 * √(2 * E₀) / Mr - 8 * δ * K ^ 2
        = ∑ z ∈ S, w z * ((∫ x in (0:ℝ)..1, |f x - g x|) - 2 * √(2 * E₀) / Mr - 8 * δ * K ^ 2) := by
          rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hriem z hz) (hw z hz)
  -- assembling
  have hexp : ∑ k ∈ bIdx n S, bW n w k * (δ * (2 * π * (1 - κ) *
      |f (((k.1 : ℝ) + k.2.re) / Mr) - g (((k.1 : ℝ) + k.2.re) / Mr)| - 4 * π * K / Mr -
      2 * η - 16 * √π * R / Mr - 2 * c * √B2)) =
      δ * (2 * π * (1 - κ) * ∑ k ∈ bIdx n S, bW n w k *
        |f (((k.1 : ℝ) + k.2.re) / Mr) - g (((k.1 : ℝ) + k.2.re) / Mr)| -
        (4 * π * K / Mr + 2 * η + 16 * √π * R / Mr + 2 * c * √B2) *
          ∑ k ∈ bIdx n S, bW n w k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, hW, mul_one] at hlow
  rw [le_div_iff₀ hδ]
  have hκ0 : 0 ≤ 1 - κ := by linarith
  have hint0 : 0 ≤ ∫ x in (0:ℝ)..1, |f x - g x| :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hRsum
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le) hκ0)
  have hE0 : 0 ≤ √(2 * E₀) := Real.sqrt_nonneg _
  have hκle : 1 - κ ≤ 1 := by
    have : 0 ≤ κ := by rw [hκ_def]; positivity
    linarith
  have hX : 0 ≤ 2 * √(2 * E₀) / Mr + 8 * δ * K ^ 2 := by positivity
  have hmul2 : 2 * π * (1 - κ) * (2 * √(2 * E₀) / Mr + 8 * δ * K ^ 2) ≤
      2 * π * (2 * √(2 * E₀) / Mr + 8 * δ * K ^ 2) :=
    mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hX
  have e6 : (4 * π * √(2 * E₀) + 4 * π * K + 16 * √π * R) / Mr =
      2 * π * (2 * √(2 * E₀) / Mr) + 4 * π * K / Mr + 16 * √π * R / Mr := by ring
  rw [e6]
  have hmulδ := mul_le_mul_of_nonneg_left hmul hδ.le
  have hmul2δ := mul_le_mul_of_nonneg_left hmul2 hδ.le
  linarith

/-! ## (5.4) -/

/-- **(5.4)**: for all small `δ`, uniformly over the refinement measure `μ = Σ w_z δ_z` on the
tube and over the Gram realisations `u` of the band covariance on the block points,
`‖V_f - V_g‖² / δ ≥ (1 - 2κ - θ₀) d(f,g)² - 2E₁`. -/
theorem gram_lower {n : ℕ} (hn : 1 ≤ n) {K R E₀ θ₀ : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hθ₀ : 0 < θ₀) (hκ : 2 / √π * K / R ≤ 1) {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n)
    (hfK : ∀ x, |f x| ≤ K) (hgK : ∀ x, |g x| ≤ K) (hEf : energy f ≤ E₀) (hEg : energy g ≤ E₀)
    (hL : Tendsto (fun δ => δ⁻¹ * (gdiff (16 ^ n) δ f g).logCov (gdiff (16 ^ n) δ f g))
      (𝓝[>] 0) (𝓝 (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|))) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ (S : Finset ℂ) (w : ℂ → ℝ), ↑S ⊆ tube δ K → (∀ z ∈ S, 0 ≤ w z) →
      ∑ z ∈ S, w z = 1 → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (u : ℂ → E),
      (∀ h h' : ℝ → ℝ, (h = f ∨ h = g) → (h' = f ∨ h' = g) → ∀ k ∈ bIdx n S,
        ∀ l ∈ bIdx n S, ⟪u (bP n δ h k), u (bP n δ h' l)⟫ =
          bandCov (4 * (δ * R) / (16 : ℝ) ^ n) (δ * R) (bP n δ h k) (bP n δ h' l)) →
      (1 - 2 * (2 / √π * K / R) - θ₀) * (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|) -
          2 * ((4 * π * √(2 * E₀) + 4 * π * K + 16 * √π * R) / (16 : ℝ) ^ n) ≤
        ‖vecV n δ S w u f - vecV n δ S w u g‖ ^ 2 / δ := by
  set r := 2 * π * ∫ x in (0:ℝ)..1, |f x - g x| with hr
  set E₁ := (4 * π * √(2 * E₀) + 4 * π * K + 16 * √π * R) / (16 : ℝ) ^ n with hE₁
  set κ := 2 / √π * K / R with hκ_def
  have hint0 : 0 ≤ ∫ x in (0:ℝ)..1, |f x - g x| :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; positivity
  set L2 : ℝ → ℝ := fun δ => (gdiff (16 ^ n) δ f g).logCov (gdiff (16 ^ n) δ f g) with hL2
  set η : ℝ → ℝ := fun δ => ∫ u, min (2 * K * (16 : ℝ) ^ n * δ) (GraphCov.lk (2 * K + K) u)
    with hη
  set c := cP n K R with hc
  have hc0 : 0 ≤ c := cP_nonneg n hR
  rcases eq_or_lt_of_le hr0 with hr0' | hrpos
  · -- `d(f,g) = 0`: nothing to prove
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro S w _ _ _ E _ _ u _
    rw [← hr0', mul_zero, zero_sub]
    have : 0 ≤ ‖vecV n δ S w u f - vecV n δ S w u g‖ ^ 2 / δ :=
      div_nonneg (sq_nonneg _) (le_of_lt hδ)
    linarith
  -- the error term tends to zero
  set ε : ℝ → ℝ := fun δ => 32 * π * δ * K ^ 2 + 4 * η δ + 4 * c * √((r + 1) * δ) +
    |δ⁻¹ * L2 δ - r| with hε_def
  have hε : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have T1 : Tendsto (fun δ : ℝ => 32 * π * δ * K ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => 32 * π * δ * K ^ 2) (𝓝 0) (𝓝 (32 * π * 0 * K ^ 2)) :=
        ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
      rw [mul_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have T2 : Tendsto η (𝓝[>] 0) (𝓝 0) :=
      tendsto_eta (L := 2 * K * (16 : ℝ) ^ n) (by positivity) (2 * K + K)
    have T3 : Tendsto (fun δ : ℝ => √((r + 1) * δ)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => √((r + 1) * δ)) (𝓝 0) (𝓝 (√((r + 1) * 0))) :=
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).tendsto 0
      rw [mul_zero, Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have T4 : Tendsto (fun δ => |δ⁻¹ * L2 δ - r|) (𝓝[>] 0) (𝓝 0) := by
      have := (hL.sub (tendsto_const_nhds (x := r))).abs
      rwa [sub_self, abs_zero] at this
    have := ((T1.add (T2.const_mul 4)).add (T3.const_mul (4 * c))).add T4
    simp only [mul_zero, add_zero] at this
    exact this
  have h1 : ∀ᶠ δ in 𝓝[>] 0, ε δ < θ₀ * r := hε.eventually (gt_mem_nhds (mul_pos hθ₀ hrpos))
  have h2 : ∀ᶠ δ in 𝓝[>] 0, δ⁻¹ * L2 δ < r + 1 := hL.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2, self_mem_nhdsWithin] with δ hε1 hL2' hδ
  intro S w hS hw hw1 E _ _ u hG
  have hδ0 : (0:ℝ) < δ := hδ
  have hM16 : (16 : ℝ) ≤ (16 : ℝ) ^ n := by
    calc (16 : ℝ) = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hn
  set a := 4 * (δ * R) / (16 : ℝ) ^ n with ha_def
  set b := δ * R with hb_def
  have hb : 0 < b := mul_pos hδ0 hR
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by
    rw [ha_def, div_le_iff₀ (by positivity)]; nlinarith
  set m := gdiff (16 ^ n) δ f g with hm
  have hnorm := norm_vecV_sub_sq ha hab n δ S w u f g hG
  have hct := cross_total hn hK hR hκ hf hg hfK hgK hEf hEg hδ0 hS hw hw1
  have hcs := bandForm_two_mul_le ha hab (mOne n δ S w f g) m
  have hB2L : bandForm a b m m ≤ L2 δ :=
    bandForm_le_logCov ha hab m (gdiff_mass n δ f g) (gdiff_nondeg n δ f g)
  have hL2δ : L2 δ ≤ (r + 1) * δ := by
    have := mul_le_mul_of_nonneg_left hL2'.le hδ0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hδ0.ne', one_mul, mul_comm] at this
  have hsq : √(bandForm a b m m) ≤ √((r + 1) * δ) := Real.sqrt_le_sqrt (hB2L.trans hL2δ)
  have hsqc := mul_le_mul_of_nonneg_left hsq hc0
  rw [hnorm]
  -- divide the Cauchy–Schwarz inequality by `δ`
  have hcsδ : 2 * (bandForm a b (mOne n δ S w f g) m / δ) - bandForm a b m m / δ ≤
      bandForm a b (mOne n δ S w f g) (mOne n δ S w f g) / δ := by
    rw [mul_div_assoc', ← sub_div]
    exact div_le_div_of_nonneg_right hcs hδ0.le
  have hB2δ : bandForm a b m m / δ ≤ δ⁻¹ * L2 δ := by
    rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hB2L (inv_nonneg.2 hδ0.le)
  have habs := le_abs_self (δ⁻¹ * L2 δ - r)
  simp only [hε_def] at hε1
  have hθr : 0 ≤ θ₀ * r := by positivity
  nlinarith

end LQGDimension.L51
