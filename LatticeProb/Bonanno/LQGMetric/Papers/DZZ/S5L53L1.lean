/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Cov
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G3

/-!
# DZZ Lemma 5.3, part 1, R3: the conditioning event `𝓕*` as an event of the white noise (P2-DZZ53L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`. In the proof of Lemma 5.3 (l. 2364–2378,
Definition of `𝓔*_{δ,α*,u,v}`) the chain `𝒞 = 𝖢_1, …, 𝖢_d` is a sequence of dyadic boxes, measurable
with respect to `𝓕*` (the partition), such that the fine field
`{η^{s_{𝖢_i}}_{δ'}(x) : δ' < s_{𝖢_i}, x ∈ (𝖢_i)_large}` is independent of `𝓕*`. As in §4.1 (l. 1719–1730)
these boxes are the boxes of Lemma 3.13 (side `(ε*)² s_𝖢̂`, `𝖢̂` the cell containing them), *not* cells
("we abuse notation by denoting by `𝖢_i` a dyadic box which is not necessarily a cell", l. 2379).
(eq-z-open), l. 2452–2453, conditions on `𝓕*` the events of the fields `η̌^𝖡` of the sub-boxes
`𝖡 ∈ 𝓑_i` (side `s_i/K`), which read the white noise in `(0, s_i²) × 𝖡**`.

This file proves the conditional independence in the form `l53_cond_biInter` (S5L53G3) uses:

* **`measurableSet_wnSigma_compl_of_cellSigma`** (stopping-set principle, generalizing the proof of
  `ae_condExp_fineField_l313Sel`, S3L13Main): a `σ(𝒱_δ)`-event `E` on which every box explored by the
  partition reads white noise disjoint from a region `R` is an event of the white noise off `R`.
* `measurableSet_inter_sel_eq`, **`measurableSet_inter_l313Sel_eq`**: for a selected box sequence `l₀`
  (any measurable selection with the L3.13 disjointness, e.g. `l313Sel`), `A ∩ {sel = l₀}` is an event of
  `W|_{(fineReg l₀)ᶜ}` for every `A ∈ σ(𝒱_δ)`.
* `prod_sqBox_subset_fineReg`, **`subBoxReg_subset_fineReg`**: the region `(0, s_b²) × 𝖡**` of a
  sub-box `𝖡 ⊆ b ∈ l₀` with `6 s_𝖡 ≤ s_b` (`K ≥ 6`) lies in `fineReg l₀`.
* **`l53_R3`**: the packaged statement (R3) of handoff P2-DZZ53G, and **`l53_hind_cond`**: the `hind`
  input of the Peierls lemma (node 3) under `P[·|A₀]`.
* `fineReg_append`, `disjoint_fineReg_append`: concatenation of box sequences (the nine segments
  `w_{i−1} → w_i` of l. 2365).

Own elementary formalization of standard steps (DZZ give no details).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option linter.unusedSectionVars false

open Classical in
/-- The masses with the boxes whose region meets `R` switched off (`massOff` with a general region). -/
def massOffR (γ : ℝ) (W : WNSpace → Ω → ℝ) (R : Set (ℝ × ℂ)) (ω : Ω) (b : DyBox) : ℝ :=
  if Disjoint (boxReg b) R then approxLQG γ W ω b else 0

lemma measurable_massOffR (γ : ℝ) (R : Set (ℝ × ℂ)) (b : DyBox) :
    Measurable[wnSigma W Rᶜ] fun ω => massOffR γ W R ω b := by
  unfold massOffR
  split_ifs with h
  · exact measurable_approxLQG_wnSigma γ b h.subset_compl_right
  · exact measurable_const

lemma measurable_isCell_massOffR (γ δ : ℝ) (R : Set (ℝ × ℂ)) :
    Measurable[wnSigma W Rᶜ] fun ω (b : DyBox) => IsCell (massOffR γ W R ω) δ b := by
  refine measurable_pred_of_eval (m := wnSigma W Rᶜ) fun b => ?_
  show MeasurableSet[wnSigma W Rᶜ] ({ω | massOffR γ W R ω b < δ ^ 2} ∩
    {ω | ∀ i < b.n, δ ^ 2 ≤ massOffR γ W R ω (b.anc i)})
  refine (measurableSet_lt (measurable_massOffR γ R b) measurable_const).inter ?_
  have e : {ω | ∀ i < b.n, δ ^ 2 ≤ massOffR γ W R ω (b.anc i)} =
      ⋂ i, ⋂ (_ : i < b.n), {ω | δ ^ 2 ≤ massOffR γ W R ω (b.anc i)} := by
    ext ω; simp
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_massOffR γ R _)

/-- The cell predicates whose explored boxes all read white noise disjoint from `R`. -/
def ExplDisj (R : Set (ℝ × ℂ)) : Set (DyBox → Prop) :=
  {c | ∀ b, Explored c b → Disjoint (boxReg b) R}

lemma measurableSet_explDisj (R : Set (ℝ × ℂ)) : MeasurableSet (ExplDisj R) := by
  refine measurableSet_setOfPred.2 ?_
  unfold Explored
  exact Measurable.forall fun b' => (Measurable.forall fun i =>
    measurable_const.imp (measurable_pi_apply _).not).imp measurable_const

/-- If the explored boxes of `IsCell m δ` avoid `R`, the partitions of `m` and `massOffR` agree. -/
lemma isCell_eq_massOffR (γ δ : ℝ) (R : Set (ℝ × ℂ)) (ω : Ω)
    (h : (fun b => IsCell (approxLQG γ W ω) δ b) ∈ ExplDisj R ∨
      (fun b => IsCell (massOffR γ W R ω) δ b) ∈ ExplDisj R) :
    (fun b => IsCell (approxLQG γ W ω) δ b) = fun b => IsCell (massOffR γ W R ω) δ b := by
  rcases h with h | h
  · refine isCell_eq_of_eqOn_explored _ _ δ fun b hb => ?_
    simp only [massOffR, h b hb, ↓reduceIte]
  · refine (isCell_eq_of_eqOn_explored _ _ δ fun b hb => ?_).symm
    simp only [massOffR, h b hb, ↓reduceIte]

/-- **Stopping-set principle.** A `σ(𝒱_δ)`-event on which every box explored by the partition reads
white noise disjoint from `R` is an event of the white noise off `R`. (Generalizes the argument of
`ae_condExp_fineField_l313Sel`, S3L13Main, from `R = fineReg l₀` and `E ⊆ {seq = l₀}`.) -/
theorem measurableSet_wnSigma_compl_of_cellSigma {γ δ : ℝ} {R : Set (ℝ × ℂ)} {E : Set Ω}
    (hE : MeasurableSet[cellSigma γ W δ] E)
    (hD : ∀ ω ∈ E, ∀ b, Explored (fun b => IsCell (approxLQG γ W ω) δ b) b →
      Disjoint (boxReg b) R) :
    MeasurableSet[wnSigma W Rᶜ] E := by
  obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hE
  have e : (fun ω (b : DyBox) => IsCell (approxLQG γ W ω) δ b) ⁻¹' T =
      (fun ω (b : DyBox) => IsCell (massOffR γ W R ω) δ b) ⁻¹' (T ∩ ExplDisj R) := by
    ext ω
    simp only [mem_preimage, mem_inter_iff]
    constructor
    · intro hω
      have h1 : (fun b => IsCell (approxLQG γ W ω) δ b) ∈ ExplDisj R := hD ω hω
      have he := isCell_eq_massOffR γ δ R ω (Or.inl h1)
      rw [← he]; exact ⟨hω, h1⟩
    · rintro ⟨hω, h2⟩
      rw [isCell_eq_massOffR γ δ R ω (Or.inr h2)]; exact hω
  rw [e]
  exact measurable_isCell_massOffR γ δ R (hT.inter (measurableSet_explDisj R))

/-- For any measurable selection of box sequences from the partition with the Lemma 3.13
disjointness, `A ∩ {sel = l₀}` is an event of the white noise off the fine region of `l₀`. -/
theorem measurableSet_inter_sel_eq {γ δ : ℝ} (sel : (DyBox → Prop) → List DyBox)
    (hsel : ∀ l₀, MeasurableSet {c | sel c = l₀})
    (hdis : ∀ c b, Explored c b → Disjoint (boxReg b) (fineReg (sel c))) (l₀ : List DyBox)
    {A : Set Ω} (hA : MeasurableSet[cellSigma γ W δ] A) :
    MeasurableSet[wnSigma W (fineReg l₀)ᶜ]
      (A ∩ {ω | sel (fun b => IsCell (approxLQG γ W ω) δ b) = l₀}) := by
  refine measurableSet_wnSigma_compl_of_cellSigma (hA.inter
    (MeasurableSpace.measurableSet_comap.2 ⟨_, hsel l₀, rfl⟩)) fun ω hω b hb => ?_
  have h : sel (fun b => IsCell (approxLQG γ W ω) δ b) = l₀ := hω.2
  rw [← h]; exact hdis _ b hb

/-! ### The sub-box regions lie in the fine region -/

lemma etaRad_pos_of_lt_one {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : 0 < etaRad s := by
  unfold etaRad
  refine lt_min ?_ (by norm_num)
  have h1 : Real.log s⁻¹ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (inv_pos.2 hs)
    (by intro h; have := inv_eq_one.1 h; linarith)
  have := abs_pos.2 h1
  have := Real.sqrt_pos.2 hs
  positivity

lemma side_le_one' (b : DyBox) : b.side ≤ 1 := by
  unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- `(0, s_b²) × S ⊆ fineReg l₀` for `b ∈ l₀` and `S ⊆ b_large`. -/
lemma prod_sqBox_subset_fineReg {l₀ : List DyBox} {b : DyBox} (hb : b ∈ l₀) {S : Set ℂ}
    (hS : S ⊆ b.largeBox) : Ioo (0 : ℝ) (b.side ^ 2) ×ˢ S ⊆ fineReg l₀ := by
  rintro ⟨t, z⟩ ⟨ht, hz⟩
  have hs1 : b.side ^ 2 ≤ 1 := pow_le_one₀ (side_pos' b).le (side_le_one' b)
  exact ⟨b, hb, z, hS hz, ht, Metric.mem_ball_self (etaRad_pos_of_lt_one ht.1 (ht.2.trans_le hs1))⟩

/-- `𝖡** = sqBox c_𝖡 (7 s_𝖡) ⊆ b_large` for a sub-box `𝖡 ⊆ b` with `6 s_𝖡 ≤ s_b` (i.e. `K ≥ 6`). -/
lemma sqBox_seven_subset_largeBox {B b : DyBox} (hBb : B.closedBox ⊆ b.closedBox)
    (h6 : 6 * B.side ≤ b.side) : sqBox B.center (7 * B.side) ⊆ b.largeBox := by
  have hsB := side_pos' B
  have hlo : (⟨B.j * B.side, B.k * B.side⟩ : ℂ) ∈ b.closedBox := hBb ⟨le_rfl, by
    show (B.j : ℝ) * B.side ≤ (B.j + 1) * B.side; nlinarith, le_rfl, by
    show (B.k : ℝ) * B.side ≤ (B.k + 1) * B.side; nlinarith⟩
  have hhi : (⟨(B.j + 1) * B.side, (B.k + 1) * B.side⟩ : ℂ) ∈ b.closedBox := hBb ⟨by
    show (B.j : ℝ) * B.side ≤ (B.j + 1) * B.side; nlinarith, le_rfl, by
    show (B.k : ℝ) * B.side ≤ (B.k + 1) * B.side; nlinarith, le_rfl⟩
  obtain ⟨a1, -, a3, -⟩ := hlo
  obtain ⟨-, b2, -, b4⟩ := hhi
  simp only at a1 a3 b2 b4
  intro z ⟨hz1, hz2⟩
  show |z.re - b.center.re| ≤ b.side ∧ |z.im - b.center.im| ≤ b.side
  simp only [DyBox.center, abs_le] at hz1 hz2 ⊢
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hz1.1, hz1.2, hz2.1, hz2.2]

/-! ### The packaged (R3) and the Peierls `hind` -/

/-! ### Concatenation (the nine segments of l. 2365) -/

end DZZ
end LQGMetric
