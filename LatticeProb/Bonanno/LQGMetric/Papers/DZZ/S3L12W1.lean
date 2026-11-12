/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12U1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12V3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Main

/-!
# DZZ Lemma 3.12 from the ring node `L312CoreR`: the wiring (D93/D99, packet P-7 wiring)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1428–1499.
Decision D93/D99: the enclosure consumed by the path surgery is the ring `CellRing` (S3L12U1),
obtained from the coarse crossing form `HasCrossRing` of Lemma 3.16 (`dzz_lemma316_cross`,
S3L12V3). This file re-runs the (proved) reduction chain
`L312Core → L312Replace → L312Step → L312SurgeryC → L312Surgery → DZZLemma312`
(S3L12T5, S3L12T2, S3L12S3, S3L12Enc, S3L12Main, S3L16Main) with `CellRing` in place of
`CellEnclosure` and `HasCrossRing` in place of `HasEnclosure`; the proofs are those of the
originals verbatim (the enclosure hypothesis is only passed through).

* `L312ReplaceR`, `L312StepR`, `L312SurgeryCR`, `L312SurgeryX`: the ring/crossing versions.
* `CellRingOfCross`: the statement of DEC-93 packet P-6 (`cellRing_of_hasCrossRing`, D99).
* `dzz_lemma316X`: (eq-B-percolation) in crossing form + (eq-B-good) (`dzz_lemma316_cross`,
  `dzz_lemma316_good`).
* **`dzz_lemma312_of_coreR`**: `L312CoreR γ → CellRingOfCross → DZZLemma312 P γ W`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- `L312Replace` (S3L12T2) with the ring enclosures `CellRing` as hypothesis. -/
def L312ReplaceR (γ : ℝ) : Prop :=
  ∀ αs : ℝ, 0 < αs → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C) →
    ∀ u ∈ dzzV, ∀ v ∈ dzzV, IsGoodPoint m δ (epsStar αs δ) u →
      IsGoodPoint m δ (epsStar αs δ) v →
      ∀ l : List DyBox, JoinsCells m δ u v l → l.IsChain Neighbour → l.Nodup →
      ∀ C ∈ l312Bad (epsStar αs δ) l, (∀ c ∈ l312Bad (epsStar αs δ) l, c.side ≤ C.side) →
        ∃ (A M B R : List DyBox) (x y : DyBox), l = A ++ x :: (M ++ y :: B) ∧ C ∈ M ∧
          (x :: R ++ [y]).IsChain Neighbour ∧ (∀ c ∈ R, IsCell m δ c) ∧
          R.length ≤ 32 * 4 ^ epsStarN αs δ ∧
          C ∉ l312Bad (epsStar αs δ) (x :: R ++ [y]) ∧
          (l312Bad (epsStar αs δ) (x :: R ++ [y]) \ l312Bad (epsStar αs δ) l).card ≤ 1 ∧
          ∀ c ∈ l312Bad (epsStar αs δ) (x :: R ++ [y]) \ l312Bad (epsStar αs δ) l,
            2 * C.side ≤ c.side

/-- `L312Step` (S3L12S3) with the ring enclosures `CellRing` as hypothesis. -/
def L312StepR (γ : ℝ) : Prop :=
  ∀ αs : ℝ, 0 < αs → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C) →
    ∀ u ∈ dzzV, ∀ v ∈ dzzV, IsGoodPoint m δ (epsStar αs δ) u →
      IsGoodPoint m δ (epsStar αs δ) v →
      ∀ l : List DyBox, JoinsCells m δ u v l → l.IsChain Neighbour → l.Nodup →
        (l312Bad (epsStar αs δ) l).Nonempty →
        ∃ l' : List DyBox, JoinsCells m δ u v l' ∧ l'.IsChain Neighbour ∧ l'.Nodup ∧
          l'.length ≤ l.length + 32 * 4 ^ epsStarN αs δ ∧ L312Progress (epsStar αs δ) l l'

/-- `L312SurgeryC` (S3L12Enc) with the ring enclosures `CellRing` as hypothesis. -/
def L312SurgeryCR (γ : ℝ) : Prop :=
  ∀ αs : ℝ, 0 < αs → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C) →
    ∀ u ∈ dzzV, ∀ v ∈ dzzV, IsGoodPoint m δ (epsStar αs δ) u →
      IsGoodPoint m δ (epsStar αs δ) v →
      ∃ l : List DyBox, JoinsCells m δ u v l ∧ IsGoodSeq (epsStar αs δ) l ∧
        ((l.length : ℕ∞) : ENNReal) ≤ ((approxDist m δ u v : ℕ∞) : ENNReal) *
          ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)))

/-- `L312Surgery` (S3L12Main) with the crossing form `HasCrossRing` of `𝓔_{δ,𝖢}` (D99) as
hypothesis. -/
def L312SurgeryX (γ : ℝ) : Prop :=
  ∀ αs : ℝ, 0 < αs → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → HasCrossRing C (epsStarN αs δ) fun b' => m b' < δ ^ 2) →
    ∀ u ∈ dzzV, ∀ v ∈ dzzV, IsGoodPoint m δ (epsStar αs δ) u →
      IsGoodPoint m δ (epsStar αs δ) v →
      ∃ l : List DyBox, JoinsCells m δ u v l ∧ IsGoodSeq (epsStar αs δ) l ∧
        ((l.length : ℕ∞) : ℝ≥0∞) ≤ ((approxDist m δ u v : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)))

/-- **DEC-93 packet P-6** (D99): the crossing form of `𝓔_{δ,𝖢}` gives the ring enclosure (for a
cell `𝖢` with `n_𝖢 ≥ 1`, as in DZZ, which only use boxes with `m ≥ 1`; D99's
`cellRing_of_hasCrossRing` with these two extra hypotheses). -/
def CellRingOfCross : Prop :=
  ∀ (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (K : ℕ), IsCell m δ C → 1 ≤ C.n →
    HasCrossRing C K (fun b' => m b' < δ ^ 2) → CellRing m δ ((2 : ℝ)⁻¹ ^ K) C

variable {m : DyBox → ℝ} {δ : ℝ}

/-- `l312Replace_of_core` (S3L12T5) for the ring versions. -/
theorem l312ReplaceR_of_coreR {γ : ℝ} (h : L312CoreR γ) : L312ReplaceR γ := by
  intro αs hαs
  obtain ⟨δ₀, hδ₀, h⟩ := h αs hαs
  refine ⟨δ₀, hδ₀, fun δ hδ m hcov hsize henc u hu v hv hgu hgv l hj hch hnd C hC hmax => ?_⟩
  obtain ⟨A, M, B, R, x, y, hl, hCM, hW, hRnd, hR, hx, hy, hcard⟩ :=
    h δ hδ m hcov hsize henc u hu v hv hgu hgv l hj hch hnd C hC hmax
  set ε := epsStar αs δ
  have hε : 0 < ε := by simp only [ε, epsStar]; positivity
  have hWs : ∀ c ∈ x :: R ++ [y], ε * C.side ≤ c.side := by
    intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · exact hx
    · exact (hR c hc).2.1
    · exact hy
  refine ⟨A, M, B, R, x, y, hl, hCM, hW, fun c hc => (hR c hc).1, ?_, ?_, ?_, ?_⟩
  · exact length_le_of_near hRnd (fun c hc => (hR c hc).1) (fun c hc => (hR c hc).2.1)
      (fun c hc => (hR c hc).2.2)
  · intro hCW
    have := side_gt_of_mem_l312Bad hε hWs hCW
    linarith
  · exact (Finset.card_le_card Finset.sdiff_subset).trans hcard
  · intro c hc
    exact two_mul_side_le_of_lt (side_gt_of_mem_l312Bad hε hWs (Finset.mem_sdiff.1 hc).1)

/-- `l312Step_of_replace` (S3L12T2) for the ring versions (choice of `𝖢` of maximal side, l. 1442). -/
theorem l312StepR_of_replaceR {γ : ℝ} (h : L312ReplaceR γ) : L312StepR γ := by
  intro αs hαs
  obtain ⟨δ₀, hδ₀, h⟩ := h αs hαs
  refine ⟨δ₀, hδ₀, fun δ hδ m hcov hsize henc u hu v hv hgu hgv l hj hch hnd hne => ?_⟩
  obtain ⟨C, hC, hmax⟩ := exists_max_side hne
  obtain ⟨A, M, B, R, x, y, hl, hCM, hW, hR, hRlen, hCW, hD1, hD2⟩ :=
    h δ hδ m hcov hsize henc u hu v hv hgu hgv l hj hch hnd C hC hmax
  obtain ⟨l', hj', hch', hnd', hlen', hprog⟩ :=
    l312_splice hj hch hnd hC hmax hl hCM hW hR hCW hD1 hD2
  exact ⟨l', hj', hch', hnd', by omega, hprog⟩


/-- `l312SurgeryC_of_step` (S3L12S3) for the ring versions (l. 1436–1458). -/
theorem l312SurgeryCR_of_stepR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hS : L312StepR γ) :
    L312SurgeryCR γ := by
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  intro αs hαs
  obtain ⟨δ₁, hδ₁, hS'⟩ := hS αs hαs
  obtain ⟨δ₂, hδ₂, hδ₂1, hA⟩ := l312_count_asym hC hαs
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ m hcov hsize henc u hu v hv hgu hgv => ?_⟩
  have hδ0 := hδ.1
  set ε := epsStar αs δ
  set M := ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊
  set K := 32 * 4 ^ epsStarN αs δ
  have hlev : ∀ c, IsCell m δ c → c.n ≤ M := fun c hc =>
    Nat.le_floor (n_le_of_rpow_le_side hδ0 (hsize c hc).1)
  obtain ⟨l0, hj0, hch0, hnd0, hlen0⟩ := exists_geodesic_chain hcov hlev hu hv
  obtain ⟨l1, ⟨hj1, hch1, -⟩, hbad, hlen1⟩ := l312_iterate
    (Q := fun l => JoinsCells m δ u v l ∧ l.IsChain Neighbour ∧ l.Nodup) ε M K
    (fun l hl c hc => hlev c (hl.1.2.1 c hc))
    (fun l hl hne => by
      obtain ⟨l', a, b, b', c, d⟩ := hS' δ ⟨hδ0, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩ m hcov
        hsize henc u hu v hv hgu hgv l hl.1 hl.2.1 hl.2.2 hne
      exact ⟨l', ⟨a, b, b'⟩, c, d⟩) l0 ⟨hj0, hch0, hnd0⟩
  have hε : 0 < ε := by unfold ε epsStar; positivity
  refine ⟨l1, hj1, isGoodSeq_of_bad_empty hε hch1 hbad, ?_⟩
  have hpot := l312Pot_le (ε := ε) (fun c hc => hlev c (hj0.2.1 c hc))
  have hpos : 1 ≤ l0.length := by
    obtain ⟨hne, -⟩ := hj0; exact List.length_pos_iff.2 hne
  have hnat : l1.length ≤ l0.length * (1 + K * (2 * M + 1)) := by
    have h1 := Nat.mul_le_mul_left K hpot
    have h2 : K * M ≤ K * M * l0.length := Nat.le_mul_of_pos_right _ hpos
    have e : l0.length * (1 + K * (2 * M + 1)) =
        l0.length + K * (l0.length * (M + 1)) + K * M * l0.length := by ring
    rw [e]; nlinarith
  have hA' := hA δ ⟨hδ0, lt_of_lt_of_le hδ.2 (min_le_right _ _)⟩
  rw [ENat.toENNReal_coe]
  calc (l1.length : ℝ≥0∞) ≤ (l0.length : ℝ≥0∞) * ((1 + K * (2 * M + 1) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hnat
    _ ≤ ((approxDist m δ u v : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ))) := by
      refine mul_le_mul' ?_ ?_
      · rw [← ENat.toENNReal_coe]; exact ENat.toENNReal_le.2 hlen0
      · rw [← ENNReal.ofReal_natCast]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [K, M]
        push_cast
        push_cast at hA'
        exact hA'


/-- `L312SurgeryC.toSurgery` (S3L12Enc) for the ring/crossing versions, through P-6. -/
theorem L312SurgeryCR.toSurgeryX {γ : ℝ} (h : L312SurgeryCR γ) (hR : CellRingOfCross) :
    L312SurgeryX γ := by
  intro αs hαs
  obtain ⟨δ₀, hδ₀, hS⟩ := h αs hαs
  refine ⟨min δ₀ (1 / 2), by positivity, fun δ hδ m hcov hsize henc =>
    hS δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩ m hcov hsize fun C hC => ?_⟩
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (by norm_num))
  have := hR m δ C _ hC (one_le_n_of_side_le hδ.1 hδ1 (dzzCMc_pos γ) (hsize C hC).2) (henc C hC)
  simpa [epsStar] using this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.16** in crossing form: `DZZLemma316` (S3L12Defs) with `encEventCross`. -/
def DZZLemma316X (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) : Prop :=
  ∃ α₁ : ℝ, ∀ α ≥ α₁, ∃ αs > α, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ b : DyBox,
    1 ≤ b.n → (b.n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ →
      P ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩ (encEventCross γ W αs δ b)ᶜ) ≤
          ENNReal.ofReal (δ ^ (10 * dzzCmc γ + 10)) ∧
        P ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
          {ω | ∃ b' ∈ boxColl b (epsStarN αs δ), δ ^ 2 ≤ approxLQG γ W ω b'}) ≤
          ENNReal.ofReal (Real.exp (-Real.sqrt (Real.log δ⁻¹)))

/-- `dzz_lemma316_of_perc` (S3L16Main) in crossing form. -/
theorem dzz_lemma316X_of_cross (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hperc : DZZLemma316Cross P γ W) : DZZLemma316X P γ W := by
  obtain ⟨α₁, h⟩ := hperc
  refine ⟨max α₁ 1, fun α hα => ?_⟩
  have hα0 : 0 < α := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hα)
  obtain ⟨A, hA⟩ := h α ((le_max_left _ _).trans hα)
  set αs := max (max A ((l316lam γ * γ * α + 1) / l31q γ)) (α + 1)
  obtain ⟨δ₁, hδ₁, h1⟩ := hA αs ((le_max_left _ _).trans (le_max_left _ _))
  obtain ⟨δ₂, hδ₂, h2⟩ := dzz_lemma316_good (P := P) (W := W) hW hγ hγ2 hα0
    ((le_max_right _ _).trans (le_max_left _ _) : (l316lam γ * γ * α + 1) / l31q γ ≤ αs)
  refine ⟨αs, lt_of_lt_of_le (lt_add_one α) (le_max_right _ _), min δ₁ δ₂, lt_min hδ₁ hδ₂,
    fun δ hδ b hb1 hbn => ⟨h1 δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩ b hb1 hbn,
      h2 δ ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩ b hbn⟩⟩

/-- **DZZ Lemma 3.16, crossing form** (both parts). -/
theorem dzz_lemma316X (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    DZZLemma316X P γ W :=
  dzz_lemma316X_of_cross hW hγ hγ2 (dzz_lemma316_cross hW hγ hγ2)

/-- **DZZ Lemma 3.12 from Lemma 3.16 and the path surgery** (proof of Lemma 3.12, l. 1428–1446). -/
theorem dzz_lemma312_of_X (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h316 : DZZLemma316X P γ W) (hS : L312SurgeryX γ) : DZZLemma312 P γ W := by
  have := hW.isProbabilityMeasure
  obtain ⟨α₁, h316⟩ := h316
  obtain ⟨αs, hαs, δ₁, hδ₁, hb⟩ := h316 (max α₁ 1) (le_max_left _ _)
  have hα : 0 < max α₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hαs0 : 0 < αs := hα.trans hαs
  have hE1 := dzz_lemma34_of_pos hW hγ hγ2 hαs0
  refine ⟨αs, hαs0, hE1, ?_⟩
  obtain ⟨c₁, hc₁, δ₂, hδ₂, h₁⟩ := hE1
  obtain ⟨c₂, hc₂, δ₃, hδ₃, h₂⟩ := dzz_lemma34_fine hW hγ hγ2 hα
  obtain ⟨δ₄, hδ₄, hsurg⟩ := hS αs hαs0
  have hCmc : 0 ≤ dzzCmc γ := dzzCmc_nonneg hγ hγ2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ dzzCmc γ / Real.log 2 := div_nonneg hCmc hl2.le
  obtain ⟨L₀, hL₀⟩ := (l312_asym hc₁ hc₂ hA).exists_forall_of_atTop
  refine ⟨min (min δ₁ δ₂) (min (min δ₃ δ₄) (Real.exp (-(max L₀ 2)))), by positivity,
    fun δ hδ u hu v hv => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ_1 : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ_2 : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ_3 : δ < δ₃ := hδ.2.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ_4 : δ < δ₄ := hδ.2.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδ_e : δ < Real.exp (-(max L₀ 2)) := hδ.2.trans_le ((min_le_right _ _).trans
    (min_le_right _ _))
  set L := Real.log δ⁻¹ with hLdef
  have hLlog : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hLmax : max L₀ 2 < L := by
    have := Real.log_lt_log hδ0 hδ_e
    rw [Real.log_exp, hLlog] at this
    linarith
  have hL2 : 2 < L := lt_of_le_of_lt (le_max_right _ _) hLmax
  have hδ1 : δ < 1 := by
    have : Real.log δ < 0 := by rw [hLlog]; linarith
    exact (Real.log_neg_iff hδ0).mp this
  have hrpow : ∀ c : ℝ, δ ^ c = Real.exp (-(c * L)) := by
    intro c; rw [Real.rpow_def_of_pos hδ0, hLlog]; ring_nf
  -- notation
  set m := fun ω => approxLQG γ W ω
  set k := epsStarN αs δ
  have hk : 1 ≤ k := one_le_epsStarN hαs0 (by linarith)
  set y := dzzCmc γ * Real.logb 2 δ⁻¹ with hy
  have hlogb : Real.logb 2 δ⁻¹ = L / Real.log 2 := rfl
  have hy0 : 0 ≤ y := by rw [hy, hlogb]; positivity
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0
  have hyAL : y = dzzCmc γ / Real.log 2 * L := by rw [hy, hlogb]; ring
  have hnN : ∀ b : DyBox, b.n ≤ N → (b.n : ℝ) ≤ y := fun b hb =>
    ((Nat.le_floor_iff hy0).mp hb)
  set E2 := eventEFine γ W (max α₁ 1) δ
  set S1 : DyBox → Set Ω := fun b => {_ω | 1 ≤ b.n} ∩
    ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ E2 ∩ (encEventCross γ W αs δ b)ᶜ)
  set S2 : DyBox → Set Ω := fun b => {_ω | 1 ≤ b.n} ∩
    ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ E2 ∩
      {ω | ∃ b' ∈ boxColl b (epsStarN αs δ), δ ^ 2 ≤ approxLQG γ W ω b'})
  set U1 := {ω | ∃ b : DyBox, b.n ≤ N ∧ ω ∈ S1 b}
  set Uu := {ω | ∃ b : DyBox, b.n ≤ N ∧ u ∈ b.largeBox ∧ ω ∈ S2 b}
  set Uv := {ω | ∃ b : DyBox, b.n ≤ N ∧ v ∈ b.largeBox ∧ ω ∈ S2 b}
  -- the inclusion
  have hsub : (eventRegular γ W αs δ u v)ᶜ ⊆
      (eventEDeltaAlpha γ W αs δ)ᶜ ∪ E2ᶜ ∪ U1 ∪ Uu ∪ Uv := by
    intro ω hω
    by_contra hne
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hne
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
    apply hω
    have hcs := h2.1
    have hlev : ∀ C, IsCell (m ω) δ C → 1 ≤ C.n ∧ C.n ≤ N := fun C hC =>
      ⟨one_le_n_of_side_le hδ0 hδ1 (dzzCMc_pos γ) (hcs.2 C hC).2,
        (Nat.le_floor_iff hy0).mpr (n_le_of_rpow_le_side hδ0 (hcs.2 C hC).1)⟩
    have henc : ∀ C, IsCell (m ω) δ C → HasCrossRing C (epsStarN αs δ)
        fun b' => m ω b' < δ ^ 2 := by
      intro C hC
      by_contra hnot
      exact h3 ⟨C, (hlev C hC).2, (hlev C hC).1, ⟨hC.1.le, h2⟩, hnot⟩
    have hgood : ∀ x ∈ dzzV, (¬ ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S2 b) →
        IsGoodPoint (m ω) δ (epsStar αs δ) x := by
      intro x _ hx
      refine isGoodPoint_of_boxColl hk fun C hC hxC b' hb' => ?_
      by_contra hlt
      exact hx ⟨C, (hlev C hC).2, hxC, (hlev C hC).1, ⟨hC.1.le, h2⟩, b', hb', not_lt.mp hlt⟩
    have gu := hgood u hu h4
    have gv := hgood v hv h5
    obtain ⟨l, hl1, hl2, hl3⟩ := hsurg δ ⟨hδ0, hδ_4⟩ (m ω) hcs.1 hcs.2 henc u hu v hv gu gv
    exact ⟨h1, gu, gv, l, hl1, hl2, hl3⟩
  -- the bounds
  have hreal : ∀ (s : Set Ω) (x : ℝ), 0 ≤ x → P s ≤ ENNReal.ofReal x → P.real s ≤ x :=
    fun s x hx h => ENNReal.toReal_le_of_le_ofReal hx h
  have b1 : P.real (eventEDeltaAlpha γ W αs δ)ᶜ ≤ Real.exp (-(c₁ * L)) := by
    rw [← hrpow]; exact hreal _ _ (by positivity) (h₁ δ ⟨hδ0, hδ_2⟩)
  have b2 : P.real E2ᶜ ≤ Real.exp (-(c₂ * L)) := by
    rw [← hrpow]; exact hreal _ _ (by positivity) (h₂ δ ⟨hδ0, hδ_3⟩)
  have b3 : P.real U1 ≤ (N + 1) * ((2 : ℝ) ^ N) ^ 2 * δ ^ (10 * dzzCmc γ + 10) := by
    refine measureReal_levels_le N S1 (by positivity) fun b hbN => ?_
    by_cases h1 : 1 ≤ b.n
    · exact (measureReal_mono inter_subset_right).trans
        (hreal _ _ (by positivity) (hb δ ⟨hδ0, hδ_1⟩ b h1 (hnN b hbN)).1)
    · have : S1 b = ∅ := by
        ext ω; simp only [S1, mem_inter_iff, mem_ofPred_eq, h1, false_and, mem_empty_iff_false]
      rw [this, measureReal_empty]; positivity
  have bw : ∀ x ∈ dzzV, P.real {ω | ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S2 b} ≤
      9 * (N + 1) * Real.exp (-Real.sqrt L) := by
    intro x hx
    refine measureReal_window_levels_le N hx S2 (by positivity) fun b hbN _ => ?_
    by_cases h1 : 1 ≤ b.n
    · exact (measureReal_mono inter_subset_right).trans
        (hreal _ _ (by positivity) (hb δ ⟨hδ0, hδ_1⟩ b h1 (hnN b hbN)).2)
    · have : S2 b = ∅ := by
        ext ω; simp only [S2, mem_inter_iff, mem_ofPred_eq, h1, false_and, mem_empty_iff_false]
      rw [this, measureReal_empty]; positivity
  have b4 := bw u hu
  have b5 := bw v hv
  -- `(N + 1) (2^N)² δ^{10 C_mc + 10} ≤ (A L + 1) e^{-10 L}`
  have hN1 : (N : ℝ) + 1 ≤ dzzCmc γ / Real.log 2 * L + 1 := by linarith
  have hpow : ((2 : ℝ) ^ N) ^ 2 * δ ^ (10 * dzzCmc γ + 10) ≤ Real.exp (-(10 * L)) := by
    rw [two_pow_sq_eq, hrpow, ← Real.exp_add, Real.exp_le_exp]
    have : (N : ℝ) * Real.log 2 ≤ dzzCmc γ * L := by
      have := mul_le_mul_of_nonneg_right (hNy.trans_eq hyAL) hl2.le
      rwa [show dzzCmc γ / Real.log 2 * L * Real.log 2 = dzzCmc γ * L by field_simp] at this
    nlinarith
  have b3' : P.real U1 ≤ (dzzCmc γ / Real.log 2 * L + 1) * Real.exp (-(10 * L)) := by
    refine b3.trans ?_
    rw [mul_assoc]
    exact mul_le_mul hN1 hpow (by positivity) (by positivity)
  have b45 : ∀ x ∈ dzzV, P.real {ω | ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S2 b} ≤
      9 * ((dzzCmc γ / Real.log 2 * L + 1) * Real.exp (-Real.sqrt L)) := by
    intro x hx
    refine (bw x hx).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN1 (by positivity)) (by norm_num)
  have htot : P.real (eventRegular γ W αs δ u v)ᶜ ≤ Real.exp (-(L ^ (1 / 4 : ℝ))) := by
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    have u1 := measureReal_union_le (μ := P) ((eventEDeltaAlpha γ W αs δ)ᶜ ∪ E2ᶜ ∪ U1) Uu
    have u2 := measureReal_union_le (μ := P) ((eventEDeltaAlpha γ W αs δ)ᶜ ∪ E2ᶜ) U1
    have u3 := measureReal_union_le (μ := P) (eventEDeltaAlpha γ W αs δ)ᶜ E2ᶜ
    have := hL₀ L (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hLmax))
    have b4' := b45 u hu
    have b5' := b45 v hv
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal htot


/-- **DZZ Lemma 3.12** from the ring node `L312CoreR` and packet P-6 (D93/D99). -/
theorem dzz_lemma312_of_coreR (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : L312CoreR γ) (hR : CellRingOfCross) : DZZLemma312 P γ W :=
  dzz_lemma312_of_X hW hγ hγ2 (dzz_lemma316X hW hγ hγ2)
    ((l312SurgeryCR_of_stepR hγ hγ2 (l312StepR_of_replaceR (l312ReplaceR_of_coreR hC))).toSurgeryX hR)

end DZZ
end LQGMetric
