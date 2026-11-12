/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DefsLemmas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA

/-!
# GM §3 definitions: elementary properties (task P2-M2A, WP-M2a, row 1 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.

* `gm_S1_23` (GM.S1.23, (1.21), l. 660–664 and l. 1184): given Prop 2.2, a.s.
  `C⁻¹ ≤ c_* ≤ C_* ≤ C`, so `0 < c_* ≤ C_* < ∞`; deterministic part `ratio_bounds_of_bilip`.
* GM.S3.4 (symmetry, l. 1269 "By the symmetry between our hypotheses on `D̃_h` and `D_h`"):
  `PairSetting.swap`, `GUp_swap`, `GLow_swap`, `attainedUp_swap`, `attainedLow_swap`,
  `lowerRatio_swap`, `upperRatio_swap`, `RatiosAre.swap`: for the pair `(D̃, D)` the optimal
  constants are `(1/C_*, 1/c_*)` and `Ḡ^{swap}_r(C, β) = G̲_r(1/C, β)` etc.
* GM.S6.1 (pigeonhole, l. 3671–3675): `gm_S6_1` — for `μ > ν/2` and small `ε`, two sets of at
  least `μ log₈ ε⁻¹` scales `8^{-k} ∈ [ε^{1+ν}, ε]` intersect; `GLow_anti_beta` (monotonicity in
  `β`, used with `β̲ ∧ p̲`).

Own elementary proofs (GM states these facts without proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-! ## GM.S1.23 -/

lemma dist_pos_of_ne (D : ContMetric) {u v : ℂ} (h : u ≠ v) : 0 < D.1 (u, v) :=
  lt_of_le_of_ne (Tight.cmetric_nonneg D.2 _) fun h0 => h (D.2.eq_of_eq_zero u v h0.symm)

/-- the ratio `D̃/D` at `p`, `p.1 ≠ p.2`, lies in `[C⁻¹, C]` under the bi-Lipschitz bounds -/
lemma ratio_mem_of_bilip {D D' : ContMetric} {C : ℝ}
    (h : ∀ u v : ℂ, C⁻¹ * D.1 (u, v) ≤ D'.1 (u, v) ∧ D'.1 (u, v) ≤ C * D.1 (u, v))
    (p : {p : ℂ × ℂ // p.1 ≠ p.2}) : C⁻¹ ≤ D'.1 p.1 / D.1 p.1 ∧ D'.1 p.1 / D.1 p.1 ≤ C := by
  have hp := dist_pos_of_ne D p.2
  exact ⟨(le_div_iff₀ hp).2 (h p.1.1 p.1.2).1, (div_le_iff₀ hp).2 (h p.1.1 p.1.2).2⟩

instance : Nonempty {p : ℂ × ℂ // p.1 ≠ p.2} := ⟨⟨(0, 1), zero_ne_one⟩⟩

/-- deterministic part of GM.S1.23 -/
theorem ratio_bounds_of_bilip {D D' : DistC → ContMetric} {g : DistC} {C : ℝ}
    (h : ∀ u v : ℂ, C⁻¹ * (D g).1 (u, v) ≤ (D' g).1 (u, v) ∧ (D' g).1 (u, v) ≤ C * (D g).1 (u, v)) :
    C⁻¹ ≤ lowerRatio D D' g ∧ lowerRatio D D' g ≤ upperRatio D D' g ∧ upperRatio D D' g ≤ C := by
  have hm := ratio_mem_of_bilip h
  have hb : BddBelow (range fun p : {p : ℂ × ℂ // p.1 ≠ p.2} => (D' g).1 p.1 / (D g).1 p.1) :=
    ⟨C⁻¹, by rintro _ ⟨p, rfl⟩; exact (hm p).1⟩
  have ha : BddAbove (range fun p : {p : ℂ × ℂ // p.1 ≠ p.2} => (D' g).1 p.1 / (D g).1 p.1) :=
    ⟨C, by rintro _ ⟨p, rfl⟩; exact (hm p).2⟩
  let p₀ : {p : ℂ × ℂ // p.1 ≠ p.2} := ⟨(0, 1), zero_ne_one⟩
  exact ⟨le_ciInf fun p => (hm p).1, (ciInf_le hb p₀).trans (le_ciSup ha p₀),
    ciSup_le fun p => (hm p).2⟩

/-- **GM.S1.23** (l. 660–664, 1184): given GM Prop 2.2, `C⁻¹ ≤ c_* ≤ C_* ≤ C` a.s. for every
whole-plane GFF, with a deterministic `C > 0`. -/
theorem gm_S1_23 (hP22 : P2_2) {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}
    (hp : PairSetting γ D D' c) : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ᵐ ω ∂P, C⁻¹ ≤ lowerRatio D D' (h ω) ∧
        lowerRatio D D' (h ω) ≤ upperRatio D D' (h ω) ∧ upperRatio D D' (h ω) ≤ C := by
  obtain ⟨C, hC, hb⟩ := hP22 hp
  exact ⟨C, hC, fun P _ h hh => by
    filter_upwards [hb P h hh] with ω hω using ratio_bounds_of_bilip hω⟩

/-! ## GM.S3.4: symmetry -/

lemma PairSetting.swap {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}
    (h : PairSetting γ D D' c) : PairSetting γ D' D c :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

lemma GUp_swap (D D' : DistC → ContMetric) (r β : ℝ) {C' : ℝ} (hC : 0 < C') :
    GUp D' D r C' β = GLow D D' r C'⁻¹ β := by
  ext g
  simp only [GUp, GLow, mem_setOf_eq, le_inv_mul_iff₀ hC]

lemma GLow_swap (D D' : DistC → ContMetric) (r β : ℝ) {c' : ℝ} (hc : 0 < c') :
    GLow D' D r c' β = GUp D D' r c'⁻¹ β := by
  ext g
  simp only [GUp, GLow, mem_setOf_eq, inv_mul_le_iff₀ hc]

lemma attainedUp_swap (D D' : DistC → ContMetric) (α r : ℝ) {C' : ℝ} (hC : 0 < C') :
    attainedUp D' D α r C' = attainedLow D D' α r C'⁻¹ := by
  ext g
  simp only [attainedUp, attainedLow, mem_setOf_eq, le_inv_mul_iff₀ hC]

/-- `inf (1/f) = 1/sup f` for `f` with values in `[C⁻¹, C]` -/
lemma ciInf_inv_eq {ι : Type*} [Nonempty ι] {f : ι → ℝ} {C : ℝ} (hC : 0 < C)
    (hf : ∀ i, C⁻¹ ≤ f i ∧ f i ≤ C) : ⨅ i, (f i)⁻¹ = (⨆ i, f i)⁻¹ := by
  have hpos : ∀ i, 0 < f i := fun i => (inv_pos.2 hC).trans_le (hf i).1
  have ha : BddAbove (range f) := ⟨C, by rintro _ ⟨i, rfl⟩; exact (hf i).2⟩
  have hb : BddBelow (range fun i => (f i)⁻¹) := ⟨0, by rintro _ ⟨i, rfl⟩; exact (inv_pos.2 (hpos i)).le⟩
  have hS : 0 < ⨆ i, f i := (hpos (Classical.arbitrary ι)).trans_le (le_ciSup ha _)
  have hI : C⁻¹ ≤ ⨅ i, (f i)⁻¹ := le_ciInf fun i => by
    rw [inv_le_inv₀ hC (hpos i)]; exact (hf i).2
  have hIpos : 0 < ⨅ i, (f i)⁻¹ := (inv_pos.2 hC).trans_le hI
  refine le_antisymm ?_ (le_ciInf fun i => (inv_le_inv₀ hS (hpos i)).2 (le_ciSup ha i))
  rw [le_inv_comm₀ hIpos hS]
  exact ciSup_le fun i => by
    rw [le_inv_comm₀ (hpos i) hIpos]
    exact ciInf_le hb i

lemma lowerRatio_swap {D D' : DistC → ContMetric} {g : DistC} {C : ℝ} (hC : 0 < C)
    (h : ∀ u v : ℂ, C⁻¹ * (D g).1 (u, v) ≤ (D' g).1 (u, v) ∧ (D' g).1 (u, v) ≤ C * (D g).1 (u, v)) :
    lowerRatio D' D g = (upperRatio D D' g)⁻¹ := by
  unfold lowerRatio upperRatio
  rw [← ciInf_inv_eq hC (ratio_mem_of_bilip h)]
  simp only [inv_div]

lemma upperRatio_swap {D D' : DistC → ContMetric} {g : DistC} {C : ℝ} (hC : 0 < C)
    (h : ∀ u v : ℂ, C⁻¹ * (D g).1 (u, v) ≤ (D' g).1 (u, v) ∧ (D' g).1 (u, v) ≤ C * (D g).1 (u, v)) :
    upperRatio D' D g = (lowerRatio D D' g)⁻¹ := by
  have hm := ratio_mem_of_bilip h
  have hpos : ∀ p : {p : ℂ × ℂ // p.1 ≠ p.2}, 0 < (D' g).1 p.1 / (D g).1 p.1 :=
    fun p => (inv_pos.2 hC).trans_le (hm p).1
  have hinv : ∀ p : {p : ℂ × ℂ // p.1 ≠ p.2},
      C⁻¹ ≤ ((D' g).1 p.1 / (D g).1 p.1)⁻¹ ∧ ((D' g).1 p.1 / (D g).1 p.1)⁻¹ ≤ C := fun p =>
    ⟨(inv_le_inv₀ hC (hpos p)).2 (hm p).2,
      by rw [inv_le_comm₀ (hpos p) hC]; exact (hm p).1⟩
  have e := ciInf_inv_eq hC hinv
  simp only [inv_inv] at e
  unfold lowerRatio upperRatio
  rw [e, inv_inv]
  simp only [inv_div]

/-- GM.S3.4 for the constants: if `(c_*, C_*) = (cs, Cs)` for `(D, D̃)`, then the constants of
`(D̃, D)` are `(Cs⁻¹, cs⁻¹)` (given the bi-Lipschitz bounds of Prop 2.2). -/
theorem RatiosAre.swap {D D' : DistC → ContMetric} {cs Cs C : ℝ} (hC : 0 < C)
    (hb : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, ∀ u v : ℂ,
        C⁻¹ * (D (h ω)).1 (u, v) ≤ (D' (h ω)).1 (u, v) ∧
          (D' (h ω)).1 (u, v) ≤ C * (D (h ω)).1 (u, v))
    (hr : RatiosAre D D' cs Cs) : RatiosAre D' D Cs⁻¹ cs⁻¹ := by
  intro Ω _ P _ h hh
  filter_upwards [hb P h hh, hr P h hh] with ω h1 h2
  rw [lowerRatio_swap hC h1, upperRatio_swap hC h1, h2.1, h2.2]
  exact ⟨rfl, rfl⟩

/-! ## GM.S6.1: pigeonhole -/

lemma GLow_anti_beta (D D' : DistC → ContMetric) {r : ℝ} (hr : 0 ≤ r) (c' : ℝ) {β β' : ℝ}
    (hβ : β' ≤ β) : GLow D D' r c' β ⊆ GLow D D' r c' β' := by
  rintro g ⟨z, hz, w, hw, h1, h2⟩
  exact ⟨z, hz, w, hw, (mul_le_mul_of_nonneg_right hβ hr).trans h1, h2⟩

lemma GUp_anti_beta (D D' : DistC → ContMetric) {r : ℝ} (hr : 0 ≤ r) (C' : ℝ) {β β' : ℝ}
    (hβ : β' ≤ β) : GUp D D' r C' β ⊆ GUp D D' r C' β' := by
  rintro g ⟨z, hz, w, hw, h1, h2⟩
  exact ⟨z, hz, w, hw, (mul_le_mul_of_nonneg_right hβ hr).trans h1, h2⟩

/-- the scales `8^{-k} ∈ [ε^{1+ν}, ε]` have `log₈ ε⁻¹ ≤ k ≤ (1+ν) log₈ ε⁻¹` -/
lemma scale_index_bounds {ε ν : ℝ} (hε : 0 < ε) {k : ℕ} (h1 : ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k)
    (h2 : (8 : ℝ)⁻¹ ^ k ≤ ε) :
    Real.logb 8 ε⁻¹ ≤ k ∧ (k : ℝ) ≤ (1 + ν) * Real.logb 8 ε⁻¹ := by
  have hk : Real.logb 8 ((8 : ℝ)⁻¹ ^ k) = -k := by
    rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]; ring
  have hp : 0 < (8 : ℝ)⁻¹ ^ k := by positivity
  have a2 := (Real.logb_le_logb (b := 8) (by norm_num) hp hε).2 h2
  have a1 := (Real.logb_le_logb (b := 8) (by norm_num) (Real.rpow_pos_of_pos hε _) hp).2 h1
  rw [hk] at a1 a2
  rw [Real.logb_rpow_eq_mul_logb_of_pos hε] at a1
  rw [Real.logb_inv]
  constructor <;> nlinarith

/-- **GM.S6.1** (pigeonhole, l. 3671–3675): for `μ > ν/2` and `ε` small, two sets of scales
`8^{-k} ∈ [ε^{1+ν}, ε]`, each with at least `μ log₈ ε⁻¹` elements, intersect. -/
theorem gm_S6_1 {μ ν : ℝ} (hν : 0 ≤ ν) (hμ : ν / 2 < μ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ Q₁ Q₂ : ℕ → Prop, μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν Q₁ →
      μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν Q₂ →
      ∃ k : ℕ, ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧ Q₁ k ∧ Q₂ k := by
  have hd : 0 < 2 * μ - ν := by linarith
  refine ⟨(8 : ℝ) ^ (-(1 / (2 * μ - ν))), by positivity, fun ε hε Q₁ Q₂ h₁ h₂ => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  set L := Real.logb 8 ε⁻¹ with hL
  have hLbig : 1 / (2 * μ - ν) < L := by
    have := (Real.logb_lt_logb_iff (b := 8) (by norm_num) hε0 (by positivity)).2 hε1
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
    rw [hL, Real.logb_inv]; linarith
  have hL0 : 0 < L := lt_trans (by positivity) hLbig
  have hLd : 1 < (2 * μ - ν) * L := by rwa [div_lt_iff₀' hd] at hLbig
  by_contra hne
  push Not at hne
  set K : Set ℕ := {k | ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε}
  have hKsub : K ⊆ (Finset.Icc ⌈L⌉₊ ⌊(1 + ν) * L⌋₊ : Set ℕ) := fun k ⟨a1, a2⟩ => by
    obtain ⟨b1, b2⟩ := scale_index_bounds hε0 a1 a2
    simp only [Finset.coe_Icc, mem_Icc]
    exact ⟨Nat.ceil_le.2 b1, Nat.le_floor b2⟩
  have hKfin : K.Finite := (Finset.finite_toSet _).subset hKsub
  set A₁ : Set ℕ := {k | ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧ Q₁ k}
  set A₂ : Set ℕ := {k | ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧ Q₂ k}
  have hA₁ : A₁ ⊆ K := fun k hk => ⟨hk.1, hk.2.1⟩
  have hA₂ : A₂ ⊆ K := fun k hk => ⟨hk.1, hk.2.1⟩
  have hdisj : Disjoint A₁ A₂ := Set.disjoint_left.2 fun k hk1 hk2 =>
    hne k hk1.1 hk1.2.1 hk1.2.2 hk2.2.2
  have hcard : A₁.ncard + A₂.ncard ≤ ⌊(1 + ν) * L⌋₊ + 1 - ⌈L⌉₊ := by
    rw [← Set.ncard_union_eq hdisj (hKfin.subset hA₁) (hKfin.subset hA₂)]
    refine (Set.ncard_le_ncard (union_subset hA₁ hA₂) hKfin).trans ?_
    refine (Set.ncard_le_ncard hKsub (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset, Nat.card_Icc]
  have hceil : (L : ℝ) ≤ ⌈L⌉₊ := Nat.le_ceil L
  have hfloor : (⌊(1 + ν) * L⌋₊ : ℝ) ≤ (1 + ν) * L := Nat.floor_le (by positivity)
  have hle : ⌈L⌉₊ ≤ ⌊(1 + ν) * L⌋₊ + 1 := by
    have h3 : ((1 + ν) * L : ℝ) < ⌊(1 + ν) * L⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : L ≤ (1 + ν) * L := by nlinarith
    exact Nat.ceil_le.2 (by push_cast; linarith)
  have hcardR : (A₁.ncard : ℝ) + A₂.ncard ≤ (1 + ν) * L + 1 - L := by
    have : ((A₁.ncard + A₂.ncard : ℕ) : ℝ) ≤ ((⌊(1 + ν) * L⌋₊ + 1 - ⌈L⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [Nat.cast_sub hle] at this
    push_cast at this
    linarith
  have e1 : (scaleCount ε ν Q₁ : ℝ) = A₁.ncard := rfl
  have e2 : (scaleCount ε ν Q₂ : ℝ) = A₂.ncard := rfl
  rw [e1] at h₁
  rw [e2] at h₂
  nlinarith

end LQGMetric.GM
