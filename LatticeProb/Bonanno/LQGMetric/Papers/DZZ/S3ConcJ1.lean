/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcJ1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcI2L
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Low
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S2

/-!
# D124 packet I2, part A: the deterministic chain behind DZZ's event `𝓔*` (P2-DZZI2)

Decision D124 (`decisions/DEC-124.md` §4). Source: DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`),
proof of Prop 3.17, l. 1577–1579 (part 1) and l. 1637–1639 (part 2): "`𝓔*` holds with
probability `1 − δ^{cι}` by Proposition 3.2 and Lemmas 3.1 and 3.5". DEC-124 §4 makes this
precise: Prop 3.2 at `δ₋ = δe^{−r}` and `δ₊ = δe^{r}`, Lemma 3.5 at `(δ, δ₋)` and `(δ₊, δ)`, the
antitonicity of `δ' ↦ D_{δ'}` and Lemma 3.1 (finiteness of `D'_δ`).

* `approxLGDSetOn_univ`: `D'_{univ} = D'`; `one_le_approxDistSetOn`: `D' ≥ 1` always;
  `lgdMinSet_anti`: `δ' ↦ min D_{δ'}` is antitone (from `lgdDZZ_antitone`);
* `approxDist_ne_top_of` (the finiteness part of `exists_geodesic_chain`, S3L12S2, copied) and
  `approxLGDSet_ne_top_of_cellSize`: on DZZ Lemma 3.1's event `D'_δ(A, B) < ∞`;
* `eStar_mem_of`: two-sided bounds `D_{δ'} ≤ D'_δ e^τ`, `D'_δ ≤ D_{δ'} e^τ` on `[δe^{−r}, δe^{r}]`
  give `𝓔*` (generic in the cell family `S`; via `abs_log_toNat_sub_le`, S3L10Exp);
* **`eStar_of_events`**: on the four events of Prop 3.2 (at `δ₋`, `δ₊`) and Lemma 3.5 (at `(δ, δ₋)`,
  `(δ₊, δ)`), with `D'_δ < ∞` and `3r + (log δ₋⁻¹)^{0.9} + (log δ⁻¹)^{0.8} ≤ τ`,
  `3r + (log δ₊⁻¹)^{0.9} + (log δ₊⁻¹)^{0.8} ≤ τ`, the event `𝓔*` holds (chains by
  `cor39_chain`, S3L9, the deterministic chain of DZZ Cor 3.9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-! ### Elementary properties of `D'` and `D` -/

lemma cellGraphOn_univ (m : DyBox → ℝ) (δ : ℝ) : cellGraphOn univ m δ = cellGraph m δ := by
  ext b b'; simp [cellGraphOn]

lemma approxDistOn_univ (m : DyBox → ℝ) (δ : ℝ) (u v : ℂ) :
    approxDistOn univ m δ u v = approxDist m δ u v := by
  simp [approxDistOn, approxDist, cellGraphOn_univ]

lemma approxLGDSetOn_univ {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (W : WNSpace → Ω → ℝ)
    (δ : ℝ) (A B : Set ℂ) (ω : Ω) :
    approxLGDSetOn univ γ W δ A B ω = approxLGDSet γ W δ A B ω := by
  simp only [approxLGDSetOn, approxLGDSet, approxDistSetOn, approxDistSet, approxDistOn_univ]

/-- `D'_S ≥ 1` (a cell path has at least one cell; `⊤` if there is none). -/
lemma one_le_approxDistSetOn (S : Set DyBox) (m : DyBox → ℝ) (δ : ℝ) (A B : Set ℂ) :
    1 ≤ approxDistSetOn S m δ A B := by
  unfold approxDistSetOn approxDistOn
  exact le_iInf₂ fun _ _ => le_iInf₂ fun _ _ => le_iInf fun _ => le_iInf fun _ =>
    le_iInf fun _ => le_iInf fun _ => le_add_self

/-- `δ' ↦ min_{A × B} D_{δ'}` is antitone (`lgdDZZ_antitone`). -/
lemma lgdMinSet_anti (μ : Measure ℂ) {δ δ' : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ δ') (A B : Set ℂ) :
    lgdMinSet μ δ' A B ≤ lgdMinSet μ δ A B :=
  iInf₂_mono fun x _ => iInf₂_mono fun y _ => lgdDZZ_antitone μ hδ h x y

/-- The cell graph is connected, so `D'(u, v) < ∞` (the finiteness step of
`exists_geodesic_chain`, S3L12S2). -/
lemma approxDist_ne_top_of {m : DyBox → ℝ} {δ : ℝ} {M : ℕ}
    (hcov : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) (hlev : ∀ c, IsCell m δ c → c.n ≤ M)
    {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) : approxDist m δ u v ≠ ⊤ := by
  obtain ⟨cu, hcu⟩ := hcov u hu
  obtain ⟨cv, hcv⟩ := hcov v hv
  have hr := cellGraph_reachable hcov hlev hcu hcv
  refine ne_top_of_le_ne_top ?_ (iInf_le_of_le cu (iInf_le_of_le cv
    (iInf_le_of_le hcu (iInf_le_of_le hcv le_rfl))))
  have h1 := SimpleGraph.edist_ne_top_iff_reachable.2 hr
  generalize (cellGraph m δ).edist cu cv = e at h1 ⊢
  induction e using ENat.recTopCoe with
  | top => exact absurd rfl h1
  | coe n => exact_mod_cast ENat.natCast_ne_top (n + 1)

lemma IsXiAdmissibleSet.nonempty_dzzC {ξ δ : ℝ} {A : Set ℂ} (h : IsXiAdmissibleSet ξ δ A) :
    A.Nonempty := by
  rcases h with ⟨a, rfl⟩ | ⟨hc, -⟩
  · exact ⟨a, rfl⟩
  · exact hc.nonempty

/-- **On DZZ Lemma 3.1's event, `D'_δ(A, B) < ∞`** for `A`, `B` meeting `𝕍`. -/
lemma approxLGDSet_ne_top_of_cellSize {Ω : Type*} [MeasurableSpace Ω] {γ δ : ℝ}
    {W : WNSpace → Ω → ℝ} {ω : Ω} (hδ : 0 < δ) (hω : ω ∈ cellSizeEvent γ W δ) {A B : Set ℂ}
    {a b : ℂ} (ha : a ∈ A) (hb : b ∈ B) (haV : a ∈ dzzV) (hbV : b ∈ dzzV) :
    approxLGDSet γ W δ A B ω ≠ ⊤ := by
  obtain ⟨M, hM⟩ := exists_level_bound (Real.rpow_pos_of_pos hδ (dzzCmc γ))
    (fun c hc => (hω.2 c hc).1)
  have h := approxDist_ne_top_of hω.1 hM haV hbV
  exact ne_top_of_le_ne_top h ((iInf₂_le a ha).trans (iInf₂_le b hb))

/-! ### From two-sided bounds to `𝓔*` -/

lemma ofReal_exp_mul_cancel_dzzC (x : ℝ≥0∞) (t : ℝ) :
    x * ENNReal.ofReal (Real.exp t) * ENNReal.ofReal (Real.exp (-t)) = x := by
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- **Two-sided bounds give `𝓔*`** (generic in the cell family `S`). -/
lemma eStar_mem_of {Ω' : Type*} [MeasurableSpace Ω'] {S : Set DyBox} {γ : ℝ}
    {W' : WNSpace → Ω' → ℝ} {μ' : Ω' → Measure ℂ} {δ r τ : ℝ} {A B : Set ℂ} {ω : Ω'}
    (hfin : approxLGDSetOn S γ W' δ A B ω ≠ ⊤) (hτ : 0 ≤ τ)
    (hup : ∀ δ' ∈ Icc (δ * Real.exp (-r)) (δ * Real.exp r),
      ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp τ))
    (hlo : ∀ δ' ∈ Icc (δ * Real.exp (-r)) (δ * Real.exp r),
      ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) ≤
        ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp τ)) :
    ω ∈ eStarEvent S γ W' μ' δ r τ A B := by
  refine ⟨hfin, one_le_approxDistSetOn _ _ _ _ _, fun δ' hδ' => ⟨?_, ?_⟩⟩
  · intro htop
    have h := hup δ' hδ'
    rw [htop, ENat.toENNReal_top, top_le_iff, ENNReal.mul_eq_top] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact ENNReal.ofReal_ne_top h
    · exact hfin (ENat.toENNReal_eq_top.1 h)
  · have h1 : ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-τ)) ≤
        ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) := by
      calc _ ≤ ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp τ) *
            ENNReal.ofReal (Real.exp (-τ)) := by gcongr; exact hlo δ' hδ'
        _ = _ := ofReal_exp_mul_cancel_dzzC _ _
    exact abs_log_toNat_sub_le hτ h1 (hup δ' hδ')

lemma log_inv_mul_exp_dzzC {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Real.log (δ * Real.exp s)⁻¹ = Real.log δ⁻¹ - s := by
  rw [Real.log_inv, Real.log_inv, Real.log_mul hδ.ne' (Real.exp_pos s).ne', Real.log_exp]
  ring

lemma div_mul_exp_neg_dzzC {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    (δ / (δ * Real.exp (-r))) ^ 3 = Real.exp (3 * r) := by
  rw [div_mul_cancel_left₀ hδ.ne', Real.exp_neg, inv_inv, ← Real.exp_nat_mul]
  norm_num

lemma mul_exp_div_dzzC {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    (δ * Real.exp r / δ) ^ 3 = Real.exp (3 * r) := by
  rw [mul_div_cancel_left₀ _ hδ.ne', ← Real.exp_nat_mul]
  norm_num

/-- **The chain of DZZ l. 1577–1579** (DEC-124 §4.1–4.4): on the events of Prop 3.2 at
`δ₋ = δe^{−r}`, `δ₊ = δe^{r}` and of Lemma 3.5 at `(δ, δ₋)`, `(δ₊, δ)`, with `D'_δ < ∞`,
`𝓔*` holds as soon as `τ` dominates the accumulated sub-exponential factors. -/
lemma eStar_of_events {Ω' : Type*} [MeasurableSpace Ω'] {γ : ℝ} {W' : WNSpace → Ω' → ℝ}
    {μ' : Ω' → Measure ℂ} {δ r τ : ℝ} {A B : Set ℂ} {ω : Ω'} (hδ : 0 < δ) (hτ0 : 0 ≤ τ)
    (hτm : 3 * r + Real.log (δ * Real.exp (-r))⁻¹ ^ (0.9 : ℝ) + Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ τ)
    (hτp : 3 * r + Real.log (δ * Real.exp r)⁻¹ ^ (0.9 : ℝ) +
      Real.log (δ * Real.exp r)⁻¹ ^ (0.8 : ℝ) ≤ τ)
    (hfin : approxLGDSet γ W' δ A B ω ≠ ⊤)
    (E1 : ω ∈ prop32Event γ W' μ' (δ * Real.exp (-r)) A B)
    (E2 : ω ∈ prop32Event γ W' μ' (δ * Real.exp r) A B)
    (E3 : ω ∈ lem35Event γ W' δ (δ * Real.exp (-r)) A B)
    (E4 : ω ∈ lem35Event γ W' (δ * Real.exp r) δ A B) :
    ω ∈ eStarEvent univ γ W' μ' δ r τ A B := by
  have hm0 : 0 ≤ δ * Real.exp (-r) := by positivity
  refine eStar_mem_of (by rw [approxLGDSetOn_univ]; exact hfin) hτ0 (fun δ' hδ' => ?_)
    (fun δ' hδ' => ?_) <;> rw [approxLGDSetOn_univ]
  · -- upper chain: `D_{δ'} ≤ D_{δ₋} ≤ D'_{δ₋} e^{…} ≤ D'_δ e^{3r + …}`
    have hmono : ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) ≤
        ((lgdMinSet (μ' ω) (δ * Real.exp (-r)) A B : ℕ∞) : ℝ≥0∞) :=
      ENat.toENNReal_le.2 (lgdMinSet_anti _ hm0 hδ'.1 A B)
    have E0 : ((approxLGDSet γ W' δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-0)) ≤
        ((approxLGDSet γ W' δ A B ω : ℕ∞) : ℝ≥0∞) := by simp
    have h := cor39_chain (pow_nonneg (div_nonneg hδ.le hm0) 3) E0 E1.2 E3
    refine (hmono.trans h).trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    rw [div_mul_exp_neg_dzzC hδ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · -- lower chain: `D'_δ ≤ D'_{δ₊} e^{3r + …} ≤ D_{δ₊} e^{…} ≤ D_{δ'} e^{…}`
    have hmono : ((lgdMinSet (μ' ω) (δ * Real.exp r) A B : ℕ∞) : ℝ≥0∞) ≤
        ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) :=
      ENat.toENNReal_le.2 (lgdMinSet_anti _ (hm0.trans hδ'.1) hδ'.2 A B)
    have E0 : ((approxLGDSet γ W' δ A B ω : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSet γ W' δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp 0) := by simp
    have h := cor39_chain (pow_nonneg (div_nonneg (by positivity) hδ.le) 3) E2.1 E0 E4
    refine h.trans (mul_le_mul' hmono (ENNReal.ofReal_le_ofReal ?_))
    rw [mul_exp_div_dzzC hδ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)

end DZZ
end LQGMetric
