/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DefsLemmas
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# GM §3.2: Propositions 3.2–3.5 from Proposition 3.6 (task P2-M2F, WP-M2f, row 9 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.

* `gm_P3_4` (**GM.S3.5**, "Proof of Proposition 3.4, assuming Proposition 3.6", l. 1299–1309):
  the contrapositive by counting. If (A) fails, fewer than `μ log₈ ε⁻¹` scales are good, so at
  least `#𝒦 − μ log₈ ε⁻¹ ≥ (ν − μ) log₈ ε⁻¹ − 1 ≥ (ν − μ)/2 · log₈ ε⁻¹` scales satisfy (B) (GA-5:
  GM writes `#𝒦 = ⌊ν log₈ ε⁻¹⌋`; we use `#𝒦 ≥ ν log₈ ε⁻¹ − 1` and `ε` small). A scale where (A)
  has probability `< p` has probability `≥ 1 − p` of the complement, which is contained in the
  event of (B).
* `gm_P3_5` (**GM.S3.4**, l. 1269): Proposition 3.4 for the swapped pair `(D̃, D)`, whose optimal
  constants are `(C_*⁻¹, c_*⁻¹)` (`RatiosAre.swap`).
* `gm_P3_2` (**GM.S3.3**, l. 1263–1267): Proposition 3.4 at `𝕣 = 1`, with the footnote fact
  `S3_2fn` (GM footnote at l. 1222: for `C'' ∈ (0, C_*)` there is `β` with
  `P[Ḡ_1(C'', β)] ≥ β`). GM's sentence "the event of (A) is contained in `Ḡ_r(C', 1 − α)`" is
  imprecise (`v ∈ ∂B_r(0)` is not in the open ball): we apply Prop 3.4 with
  `C₁ = (C' + C_*)/2` and move `v` radially into `B_r(0)` by continuity, giving
  `β̄ = (1 − α)/2` (GA S3.3 note, proposed DEVIATIONS entry).
* `gm_P3_3` ("Proposition 3.5 immediately implies Proposition 3.3", l. 1283): Proposition 3.2 for
  the swapped pair (GM.S3.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-! ## Counting scales -/

/-- the set `𝒦^ε` of indices `k` with `8^{-k} ∈ [ε^{1+ν}, ε]` -/
def scaleSetK (ε ν : ℝ) : Set ℕ := {k | ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε}

lemma scaleSetK_finite {ε ν : ℝ} (hε : 0 < ε) : (scaleSetK ε ν).Finite := by
  refine (Finset.finite_toSet (Finset.Icc ⌈Real.logb 8 ε⁻¹⌉₊ ⌊(1 + ν) * Real.logb 8 ε⁻¹⌋₊)).subset ?_
  intro k ⟨a1, a2⟩
  obtain ⟨b1, b2⟩ := scale_index_bounds hε a1 a2
  simp only [Finset.coe_Icc, mem_Icc]
  exact ⟨Nat.ceil_le.2 b1, Nat.le_floor b2⟩

lemma inv8_pow_eq (k : ℕ) : (8 : ℝ)⁻¹ ^ k = (8 : ℝ) ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

/-- `ε = 8^{-L}` with `L = log₈ ε⁻¹` -/
lemma eps_eq_rpow {ε : ℝ} (hε : 0 < ε) : ε = (8 : ℝ) ^ (-Real.logb 8 ε⁻¹) := by
  rw [Real.logb_inv, neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hε]

lemma mem_scaleSetK_of {ε ν : ℝ} (hε : 0 < ε) {k : ℕ} (h1 : Real.logb 8 ε⁻¹ ≤ k)
    (h2 : (k : ℝ) ≤ (1 + ν) * Real.logb 8 ε⁻¹) : k ∈ scaleSetK ε ν := by
  have e := eps_eq_rpow hε
  refine ⟨?_, ?_⟩
  · rw [inv8_pow_eq, e, ← Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  · rw [inv8_pow_eq]
    conv_rhs => rw [e]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- `#𝒦^ε ≥ ν log₈ ε⁻¹ − 1` for `ε ∈ (0,1)` -/
lemma card_scaleSetK_ge {ε ν : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hν : 0 ≤ ν) :
    ν * Real.logb 8 ε⁻¹ - 1 ≤ ((scaleSetK ε ν).ncard : ℝ) := by
  set L := Real.logb 8 ε⁻¹ with hL
  have hL0 : 0 ≤ L := by
    rw [hL, Real.logb_inv]
    have := Real.logb_neg (b := 8) (by norm_num) hε hε1
    linarith
  have hsub : (Finset.Icc ⌈L⌉₊ ⌊(1 + ν) * L⌋₊ : Set ℕ) ⊆ scaleSetK ε ν := by
    intro k hk
    simp only [Finset.coe_Icc, mem_Icc] at hk
    refine mem_scaleSetK_of hε ((Nat.le_ceil L).trans (by exact_mod_cast hk.1)) ?_
    exact (Nat.cast_le.2 hk.2).trans (Nat.floor_le (by positivity))
  have h1 := Set.ncard_le_ncard hsub (scaleSetK_finite hε)
  rw [Set.ncard_coe_finset, Nat.card_Icc] at h1
  have hc : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL0
  have hf : (1 + ν) * L - 1 < (⌊(1 + ν) * L⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one ((1 + ν) * L); linarith
  have h2 : ((⌊(1 + ν) * L⌋₊ + 1 - ⌈L⌉₊ : ℕ) : ℝ) ≥ (⌊(1 + ν) * L⌋₊ : ℝ) + 1 - ⌈L⌉₊ := by
    by_cases hle : ⌈L⌉₊ ≤ ⌊(1 + ν) * L⌋₊ + 1
    · rw [Nat.cast_sub hle]; push_cast; linarith
    · push Not at hle
      rw [Nat.sub_eq_zero_of_le hle.le]
      have : ((⌊(1 + ν) * L⌋₊ + 1 : ℕ) : ℝ) < ⌈L⌉₊ := by exact_mod_cast hle
      push_cast at this; simp only [CharP.cast_eq_zero]; linarith
  have h3 : ((⌊(1 + ν) * L⌋₊ + 1 - ⌈L⌉₊ : ℕ) : ℝ) ≤ ((scaleSetK ε ν).ncard : ℝ) := by
    exact_mod_cast h1
  nlinarith

lemma scaleCount_eq (ε ν : ℝ) (Q : ℕ → Prop) :
    scaleCount ε ν Q = {k | k ∈ scaleSetK ε ν ∧ Q k}.ncard := by
  unfold scaleCount scaleSetK
  congr 1
  ext k
  simp only [mem_setOf_eq, and_assoc]

lemma scaleCount_mono {ε ν : ℝ} (hε : 0 < ε) {Q Q' : ℕ → Prop}
    (h : ∀ k ∈ scaleSetK ε ν, Q k → Q' k) : scaleCount ε ν Q ≤ scaleCount ε ν Q' := by
  rw [scaleCount_eq, scaleCount_eq]
  exact Set.ncard_le_ncard (fun k hk => ⟨hk.1, h k hk.1 hk.2⟩)
    ((scaleSetK_finite hε).subset fun k hk => hk.1)

/-- if every scale is good for `Q₁` or for `Q₂`, then the two counts add up to `≥ #𝒦^ε` -/
lemma card_le_scaleCount_add {ε ν : ℝ} (hε : 0 < ε) {Q₁ Q₂ : ℕ → Prop}
    (h : ∀ k ∈ scaleSetK ε ν, Q₁ k ∨ Q₂ k) :
    (scaleSetK ε ν).ncard ≤ scaleCount ε ν Q₁ + scaleCount ε ν Q₂ := by
  rw [scaleCount_eq, scaleCount_eq]
  refine (Set.ncard_le_ncard (fun k hk => ?_) ?_).trans (Set.ncard_union_le _ _)
  · rcases h k hk with h1 | h2
    · exact Or.inl ⟨hk, h1⟩
    · exact Or.inr ⟨hk, h2⟩
  · exact (scaleSetK_finite hε).subset (union_subset (fun k hk => hk.1) fun k hk => hk.1)

/-- `log₈ ε⁻¹ ≥ a` for `ε ≤ 8^{-a}` -/
lemma logb_ge_of_le_rpow {ε a : ℝ} (hε : 0 < ε) (h : ε ≤ (8 : ℝ) ^ (-a)) :
    a ≤ Real.logb 8 ε⁻¹ := by
  have := (Real.logb_le_logb (b := 8) (by norm_num) hε (by positivity)).2 h
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
  rw [Real.logb_inv]; linarith

/-! ## Probability of a complement -/

lemma ofReal_one_sub_le_compl {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A : Set Ω} {p : ℝ} (hA : P A < ENNReal.ofReal p) :
    ENNReal.ofReal (1 - p) ≤ P Aᶜ := by
  have h1 : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self A]; exact measure_union_le _ _
  have hp : 0 ≤ p := by
    by_contra hp; push Not at hp
    rw [ENNReal.ofReal_of_nonpos hp.le] at hA; exact (ENNReal.not_lt_zero hA)
  rw [ENNReal.ofReal_sub _ hp, ENNReal.ofReal_one]
  calc 1 - ENNReal.ofReal p ≤ 1 - P A := tsub_le_tsub_left hA.le _
    _ ≤ P Aᶜ := tsub_le_iff_left.2 h1

lemma compl_attainedUp_subset_badScale (D D' : DistC → ContMetric) (α r C' : ℝ) :
    (attainedUp D D' α r C')ᶜ ⊆ badScale D D' α r C' := by
  intro g hg u hu v hv hU
  by_contra hlt
  push Not at hlt
  exact hg ⟨u, hu, v, hv, hlt.le, hU⟩

/-! ## GM.S3.5: Proposition 3.6 ⇒ Proposition 3.4 (l. 1299–1309) -/

/-- **GM Proposition 3.4** from Proposition 3.6 (GM.S3.5, l. 1299–1309) -/
theorem gm_P3_4 (h36 : P3_6) : P3_4 := by
  intro γ D D' c cs Cs hS hR μ ν hμ hμν hν1
  obtain ⟨α₀, p, hα₀, hp, H⟩ := h36 hS hR hμ hμν hν1
  refine ⟨α₀, p, hα₀, hp, fun α hα C' hC' => ?_⟩
  obtain ⟨C'', hC'', H1⟩ := H α hα C' hC'
  refine ⟨C'', hC'', fun β hβ => ?_⟩
  obtain ⟨ε₀, hε₀, H2⟩ := H1 β hβ
  have hd : 0 < ν - μ := by linarith
  refine ⟨min ε₀ (min (1 / 2) ((8 : ℝ) ^ (-(2 / (ν - μ))))),
    lt_min hε₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro Ω _ P _ h hh R hR0 hGβ ε ⟨hε0, hε⟩
  have hεε₀ : ε ≤ ε₀ := hε.trans (min_le_left _ _)
  have hε1 : ε < 1 := (hε.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt
    (by norm_num)
  have hLa : 2 / (ν - μ) ≤ Real.logb 8 ε⁻¹ :=
    logb_ge_of_le_rpow hε0 (hε.trans ((min_le_right _ _).trans (min_le_right _ _)))
  by_contra hlt
  push Not at hlt
  refine (not_lt.2 hGβ) (H2 P h hh R hR0 ε ⟨hε0, hεε₀⟩ ?_)
  set L := Real.logb 8 ε⁻¹
  have hsplit := card_le_scaleCount_add (ν := ν) hε0
    (Q₁ := fun k => ENNReal.ofReal p ≤ P (h ⁻¹' attainedUp D D' α ((8 : ℝ)⁻¹ ^ k * R) C'))
    (Q₂ := fun k => ENNReal.ofReal (1 - p) ≤
      P (h ⁻¹' badScale D D' α ((8 : ℝ)⁻¹ ^ k * R) C')) (fun k _ => by
        by_cases hk : ENNReal.ofReal p ≤ P (h ⁻¹' attainedUp D D' α ((8 : ℝ)⁻¹ ^ k * R) C')
        · exact Or.inl hk
        · push Not at hk
          refine Or.inr ((ofReal_one_sub_le_compl P hk).trans (measure_mono ?_))
          rw [← preimage_compl]
          exact preimage_mono (compl_attainedUp_subset_badScale D D' α _ C'))
  have hK := card_scaleSetK_ge hε0 hε1 (hμ.trans hμν).le
  have hsplitR := (Nat.cast_le (α := ℝ)).2 hsplit
  push_cast at hsplitR
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hLa
  have : 2 ≤ (ν - μ) * L := by rwa [div_le_iff₀' hd] at hLa
  linarith

end LQGMetric.GM
