/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CMW1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317E

/-!
# Walled DZZ (eq-very-crude-prime): `D'` through a cell family `S` (P2-DZZMOMW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 849–853) for the walled approximate distance
`approxDistSetOn S` (S3P32K1; D117/D123, packet P-317K-MOM). The statements and proofs are
copies of P2-DZZCM's (S3CM2, S3CM3) with the cell graph `cellGraph` replaced by its restriction
`cellGraphOn S`; nothing about `S` is used (a geodesic of `cellGraphOn S` still visits distinct
cells of level `≤ k`).

* `approxDistOn_le_of_level`, **`approxDistSetOn_toNat_le`** (copies of `approxDist_le_of_level`,
  `approxDistSet_toNat_le`);
* `approxDistSetOn_le_iff`, **`measurable_approxLGDSetOn`**, **`measurable_logApproxLGDOn`**
  (copies of `approxDistSet_le_iff`, `measurable_approxLGDSet`, `measurable_logApproxLGD`);
* **`lintegral_sq_logApproxLGDOn_le`** (copy of `lintegral_sq_logApproxLGD_le`): uniformly in
  `S`, `A`, `B` and `δ ∈ (0, 1)`, `E (log D'_{S,γ,δ}(A, B))² ≤ a + b (log δ⁻¹)²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

section DetOn

variable (S : Set DyBox) (m : DyBox → ℝ) (δ : ℝ)

/-- all vertices of a walk of the restricted cell graph starting at a cell of `S` are cells of
`S` (copy of `cm_walk_support_isCell`) -/
lemma cmw_walk_support {b b' : DyBox} (p : (cellGraphOn S m δ).Walk b b')
    (hb : IsCell m δ b ∧ b ∈ S) : ∀ c ∈ p.support, IsCell m δ c ∧ c ∈ S := by
  induction p with
  | nil => intro c hc; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hc
           exact hc ▸ hb
  | cons h q ih =>
    intro c hc
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hb
    · exact ih ⟨h.1.2.1, h.2.2⟩ c hc

/-- **`D'_S ≤ (k+1) 4^k`** when every box of level `k` has mass `< δ²` (copy of
`approxDist_le_of_level`) -/
theorem approxDistOn_le_of_level {k : ℕ} (hk : ∀ b : DyBox, b.n = k → m b < δ ^ 2) {x y : ℂ}
    (hfin : approxDistOn S m δ x y ≠ ⊤) :
    approxDistOn S m δ x y ≤ ((k + 1) * 2 ^ k * 2 ^ k : ℕ) := by
  have hlt := lt_top_iff_ne_top.2 hfin
  simp only [approxDistOn, iInf_lt_iff] at hlt
  obtain ⟨b, b', ⟨hb, hbx, hbS⟩, ⟨hb', hby, hbS'⟩, hlt⟩ := hlt
  have hne : (cellGraphOn S m δ).edist b b' ≠ ⊤ := by
    intro h; rw [h, top_add] at hlt; exact lt_irrefl _ hlt
  obtain ⟨p, -⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  set q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hcells := cmw_walk_support S m δ q ⟨hb, hbS⟩
  have hlen := cm_card_le q.support hq.support_nodup fun c hc =>
    IsCell.n_le_of_level hk (hcells c hc).1
  rw [SimpleGraph.Walk.length_support] at hlen
  refine (iInf₂_le_of_le b b' (iInf₂_le_of_le ⟨hb, hbx, hbS⟩ ⟨hb', hby, hbS'⟩ le_rfl)).trans ?_
  refine (add_le_add (SimpleGraph.Walk.edist_le q) le_rfl).trans ?_
  exact_mod_cast hlen

/-- **`D'_S(A, B) ≤ (k+1) 4^k`** (as a natural number) when every box of level `k` has mass
`< δ²` (copy of `approxDistSet_toNat_le`) -/
theorem approxDistSetOn_toNat_le {k : ℕ} (hk : ∀ b : DyBox, b.n = k → m b < δ ^ 2)
    (A B : Set ℂ) : (approxDistSetOn S m δ A B).toNat ≤ (k + 1) * 2 ^ k * 2 ^ k := by
  by_cases hfin : approxDistSetOn S m δ A B = ⊤
  · rw [hfin]; simp
  have hlt := lt_top_iff_ne_top.2 hfin
  simp only [approxDistSetOn, iInf_lt_iff] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := hlt
  have h1 : approxDistSetOn S m δ A B ≤ ((k + 1) * 2 ^ k * 2 ^ k : ℕ) :=
    (iInf₂_le_of_le x hx (iInf₂_le_of_le y hy le_rfl)).trans
      (approxDistOn_le_of_level S m δ hk hxy.ne)
  exact ENat.toNat_le_of_le_natCast h1

/-- a chain of neighbouring cells of `S` bounds the restricted graph distance (copy of
`cm_edist_le_of_chain`) -/
lemma cmw_edist_le_of_chain : ∀ (l : List DyBox) (b b' : DyBox), l.head? = some b →
    l.getLast? = some b' → l.IsChain Neighbour → (∀ c ∈ l, IsCell m δ c ∧ c ∈ S) →
    (cellGraphOn S m δ).edist b b' + 1 ≤ l.length
  | [], _, _, h, _, _, _ => by simp at h
  | [a], b, b', h1, h2, _, _ => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    subst h1; subst h2
    simp
  | a :: c :: t, b, b', h1, h2, hch, hc => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rw [List.isChain_cons_cons] at hch
    have hrec := cmw_edist_le_of_chain (c :: t) c b' (by simp)
      (by rw [List.getLast?_cons_cons] at h2; exact h2) hch.2
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    have hadj : (cellGraphOn S m δ).Adj a c :=
      ⟨⟨(hc a (by simp)).1, (hc c (by simp)).1, hch.1⟩, (hc a (by simp)).2, (hc c (by simp)).2⟩
    have h1 : (cellGraphOn S m δ).edist a c ≤ 1 := (SimpleGraph.edist_eq_one_iff_adj.2 hadj).le
    calc (cellGraphOn S m δ).edist a b' + 1 ≤ ((cellGraphOn S m δ).edist a c +
          (cellGraphOn S m δ).edist c b') + 1 := by gcongr; exact SimpleGraph.edist_triangle
      _ ≤ 1 + (((c :: t).length : ℕ) : ℕ∞) := by
          rw [add_assoc]; exact add_le_add h1 hrec
      _ = ((a :: c :: t).length : ℕ∞) := by
          simp only [List.length_cons]; push_cast; ring

/-- **sublevel sets of `D'_S(A, B)`** (copy of `approxDistSet_le_iff`) -/
theorem approxDistSetOn_le_iff (A B : Set ℂ) (K : ℕ) :
    approxDistSetOn S m δ A B ≤ K ↔ ∃ (b b' : DyBox) (l : List DyBox),
      ((∃ x ∈ A, b.Mem x) ∧ (∃ y ∈ B, b'.Mem y) ∧ l.head? = some b ∧ l.getLast? = some b' ∧
        l.IsChain Neighbour ∧ l.length ≤ K) ∧ ∀ c ∈ l, IsCell m δ c ∧ c ∈ S := by
  constructor
  · intro h
    obtain ⟨x, h⟩ := cm_iInf_le_nat h
    obtain ⟨hx, h⟩ := cm_iInf_le_nat h
    obtain ⟨y, h⟩ := cm_iInf_le_nat h
    obtain ⟨hy, h⟩ := cm_iInf_le_nat h
    obtain ⟨b, h⟩ := cm_iInf_le_nat h
    obtain ⟨b', h⟩ := cm_iInf_le_nat h
    obtain ⟨⟨hb, hbx, hbS⟩, h⟩ := cm_iInf_le_nat h
    obtain ⟨⟨hb', hby, hbS'⟩, h⟩ := cm_iInf_le_nat h
    have hne : (cellGraphOn S m δ).edist b b' ≠ ⊤ := by
      intro he; rw [he, top_add] at h; exact absurd h (by simp)
    obtain ⟨p, hp⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
    refine ⟨b, b', p.support, ⟨⟨x, hx, hbx⟩, ⟨y, hy, hby⟩, ?_, ?_, ?_, ?_⟩,
      cmw_walk_support S m δ p ⟨hb, hbS⟩⟩
    · cases p <;> simp
    · rw [List.getLast?_eq_getLast p.support_ne_nil, SimpleGraph.Walk.getLast_support]
    · exact p.isChain_adj_support.imp fun _ _ h => h.1.2.2
    · rw [SimpleGraph.Walk.length_support]
      rw [← hp] at h
      exact_mod_cast h
  · rintro ⟨b, b', l, ⟨⟨x, hx, hbx⟩, ⟨y, hy, hby⟩, h1, h2, hch, hlen⟩, hc⟩
    have hb := hc b (List.mem_of_mem_head? h1)
    have hb' := hc b' (List.mem_of_mem_getLast? h2)
    refine (iInf₂_le_of_le x hx (iInf₂_le_of_le y hy (iInf₂_le_of_le b b'
      (iInf₂_le_of_le ⟨hb.1, hbx, hb.2⟩ ⟨hb'.1, hby, hb'.2⟩ le_rfl)))).trans ?_
    exact (cmw_edist_le_of_chain S m δ l b b' h1 h2 hch hc).trans (by exact_mod_cast hlen)

end DetOn

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **measurability of `D'_{S,γ,δ}(A, B)`** in `ω` (copy of `measurable_approxLGDSet`) -/
theorem measurable_approxLGDSetOn (hW : IsWhiteNoise P W) (S : Set DyBox) (γ δ : ℝ)
    (A B : Set ℂ) : Measurable fun ω => approxLGDSetOn S γ W δ A B ω := by
  refine measurable_enat_of_le fun K => ?_
  simp_rw [approxLGDSetOn, approxDistSetOn_le_iff]
  refine measurableSet_setOfPred.2 (Measurable.exists fun b => Measurable.exists fun b' =>
    Measurable.exists fun l => Measurable.and measurable_const
      (Measurable.forall fun c => Measurable.forall fun _ =>
        Measurable.and (measurableSet_setOfPred.1 (measurableSet_isCell hW γ δ c))
          measurable_const))

/-- **measurability of `log D'_{S,γ,δ}(A, B)`** -/
theorem measurable_logApproxLGDOn (hW : IsWhiteNoise P W) (S : Set DyBox) (γ δ : ℝ)
    (A B : Set ℂ) : Measurable fun ω => logApproxLGDOn S γ W δ A B ω :=
  measurable_log_toNat.comp (measurable_approxLGDSetOn hW S γ δ A B)

omit [MeasurableSpace Ω] in
lemma logApproxLGDOn_nonneg (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ)
    (A B : Set ℂ) (ω : Ω) : 0 ≤ logApproxLGDOn S γ W δ A B ω :=
  Real.log_natCast_nonneg _

/-- **Walled DZZ (eq-very-crude-prime), `∫⁻` form**: `E (log D'_{S,γ,δ}(A, B))² ≤ a + b (log δ⁻¹)²`,
uniformly in `S`, the sets `A, B` and `δ ∈ (0, 1)`. Copy of `lintegral_sq_logApproxLGD_le`
(P2-DZZCM, S3CM3) with `approxDistSetOn_toNat_le`. -/
theorem lintegral_sq_logApproxLGDOn_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ (S : Set DyBox) (A B : Set ℂ) (δ : ℝ), 0 < δ → δ < 1 →
      ∫⁻ ω, ENNReal.ofReal (logApproxLGDOn S γ W δ A B ω) ^ 2 ∂P ≤
        ENNReal.ofReal (a + b * Real.log δ⁻¹ ^ 2) := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  set p := l31p γ with hpdef
  set q := l31q γ with hqdef
  have hp : 1 ≤ p := by
    rw [hpdef, l31p, le_div_iff₀ (by positivity)]; nlinarith
  have hq0 : 0 < q := l31q_pos hγ hγ2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set l := Real.log 2 with hl
  set l8 := Real.log 8 with hl8
  have hl80 : 0 < l8 := Real.log_pos (by norm_num)
  set C₀ := 2 * p * (p - 1) * γ ^ 2 with hC₀
  set r := Real.exp (-(q * l / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by have := mul_pos hq0 hl2; linarith)
  have hr2 : r ^ 2 = Real.exp (-(q * l)) := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  set G := Real.exp C₀ * ((1 - r)⁻¹) ^ 2 with hG
  have hG0 : 0 ≤ G := by have : 0 < 1 - r := by linarith
                         positivity
  set κ := 2 * p * l8 / (q * l) with hκ
  refine ⟨4 * (2 * l8 ^ 2 + l8 ^ 2 * G), 8 * κ ^ 2, by positivity, by positivity,
    fun S A B δ hδ0 hδ1 => ?_⟩
  set L := Real.log δ⁻¹ with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hδ0).2 hδ1.le)
  set j₀ : ℕ := ⌈2 * p * L / (q * l)⌉₊ with hj₀
  set T' : ℕ → Set Ω := fun K => {ω | ∃ b : DyBox, b.n = K ∧ ω ∈ {ω | δ ^ 2 ≤ approxLQG γ W ω b}}
    with hT'
  set T : ℕ → Set Ω := fun m => toMeasurable P (T' (j₀ + m)) with hT
  have hPq : ∀ m : ℕ, P (T m) ≤ ENNReal.ofReal (Real.exp C₀ * (r ^ 2) ^ m) := fun m => by
    rw [hT, measure_toMeasurable, ← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ((cm_level_bound hW hγ hγ2 hδ0 (j₀ + m)).trans ?_)
    rw [hr2, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have hc : 2 * p * L / (q * l) ≤ j₀ := Nat.le_ceil _
    have hc' : 2 * p * L ≤ j₀ * (q * l) := (div_le_iff₀ (by positivity)).1 hc
    push_cast
    nlinarith
  have hpt : ∀ ω (m : ℕ), ω ∉ T m → ENNReal.ofReal (logApproxLGDOn S γ W δ A B ω) ≤
      ENNReal.ofReal (j₀ * l8 + l8 * m) := fun ω m hω => by
    have hgood : ∀ b : DyBox, b.n = j₀ + m → approxLQG γ W ω b < δ ^ 2 := by
      intro b hb
      by_contra hc
      push Not at hc
      exact hω (subset_toMeasurable P _ ⟨b, hb, hc⟩)
    have h1 := (approxDistSetOn_toNat_le S (approxLQG γ W ω) δ hgood A B).trans
      (cm_succ_mul_le_eight_pow _)
    refine ENNReal.ofReal_le_ofReal ?_
    unfold logApproxLGDOn approxLGDSetOn
    have e : (j₀ : ℝ) * l8 + l8 * m = Real.log ((8 : ℝ) ^ (j₀ + m)) := by
      rw [Real.log_pow, hl8]; push_cast; ring
    rw [e]
    rcases Nat.eq_zero_or_pos (approxDistSetOn S (approxLQG γ W ω) δ A B).toNat with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (one_le_pow₀ (by norm_num))
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast h1)
  have hmain := lintegral_sq_le_of_geom (P := P)
    (fun ω => ENNReal.ofReal (logApproxLGDOn S γ W δ A B ω)) T
    (fun m => measurableSet_toMeasurable P _) (a₀ := j₀ * l8) (c := l8) (C := Real.exp C₀)
    (by positivity) hl80 (Real.exp_pos _).le hr0 hr1 hPq hpt
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hj : (j₀ : ℝ) ≤ 2 * p * L / (q * l) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have ha : (j₀ : ℝ) * l8 ≤ κ * L + l8 := by
    have := mul_le_mul_of_nonneg_right hj hl80.le
    have e : (2 * p * L / (q * l) + 1) * l8 = κ * L + l8 := by
      rw [hκ]; field_simp
    linarith
  have hsq : ((j₀ : ℝ) * l8) ^ 2 ≤ 2 * l8 ^ 2 + 2 * κ ^ 2 * L ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) ha 2
    nlinarith [sq_nonneg (κ * L - l8)]
  rw [← hG]
  nlinarith

end DZZ
end LQGMetric
