/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BWiring at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BTheorem15
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CTheorem39

/-!
# [18] Theorem 1.5 on the good event of T15A's (3.35), and with probability `1 − O(ε^α)`

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18] ,
Theorem 1.5 ((1.9), `[18]`); Theorem 3.9's estimates (3.30′), (3.31′).

The two inputs are:
* (3.35): T15A's `T15A.Lemma311Holds H ε ρ β p` (`GMSMain/T15ACore.lean`); its walk event `T15A.Lemma311Event` is
  verbatim T15B's `DiscEvent` (`disc_of_lemma311Holds`);
* (3.31′): T15C's `T15CBoundaryEstimate H ε ρ β ξ A` (`GMSMain/T15CTheorem39.lean`), produced on T15A's event by
  `t15c_boundaryEstimate_of_lemma311Holds`; it specializes to T15B's `BoundaryEstimate` (`boundaryEstimate_of_t15c`).

* `theorem15_of_lemma311Holds` — **[18] Theorem 1.5, deterministic on one good environment**: (3.35) at an ambient
  radius `ρ' > ρ` (T15A's event), a connected graph with (LC) (`PointConnected`), cells meeting `B_ρ(0)` of diameter
  `≤ ε^q` (Lemma 2.7's event), `0 < β ≤ q ≤ 1`, `0 < ε ≤ 1`: every discrete harmonic extension `g` of `χ`-Hölder
  boundary data on every open `D ⊆ B_ρ(0)` with `ℂ \ D` preconnected satisfies (1.9) with explicit `A₀, ξ`.
* `theorem15_bad_le` — **[18] Theorem 1.5 with probability `1 − O(ε^α)`** for any family of cellular embeddings
  indexed by a type `ι` of meshes `ε i ∈ (0, 1]` (dyadic or real), from bad-event bounds for (3.35) and Lemma 2.7 and
  almost-sure connectivity and (LC): `∃ α > 0, ∀ χ > 0, ∃ ξ > 0, ∀ D f, ∃ A₀ > 0, C, ∀ i, P[(1.9) fails] ≤ C ε_i^α`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-! ### The named inputs in the landed shapes -/

/-- **T15A's (3.35) is T15B's disconnection hypothesis**: on `Lemma311Holds H ε ρ β p` and for `D ⊆ B_ρ(0)`, the walk
event of (3.35) (`DiscEvent`, verbatim T15A's `Lemma311Event`) has probability `≥ p` from every vertex of `V(B_r(z))`
whenever `r ≥ ε^β` and `B_{2r}(z) ⊆ D`. -/
theorem disc_of_lemma311Holds {H : CellularEmbedding G o} {ε ρ β p : ℝ} (hε : 0 < ε)
    (h : T15A.Lemma311Holds H ε ρ β p) {D : Set ℂ} (hD : D ⊆ ball (0 : ℂ) ρ) :
    ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)} := by
  intro z r hr hball v hv
  have hr0 : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos hε β) hr
  have hrρ : r ≤ ρ := by
    have := T15A.norm_add_le_of_ball_subset (by linarith : (0 : ℝ) < 2 * r) (hball.trans hD)
    linarith [norm_nonneg z]
  exact h z r hr hrρ (hball.trans hD) v hv

/-- **T15C's (3.31′) is T15B's boundary estimate** (`BoundaryEstimate`): for `D` open in `B_ρ(0)` with `ℂ \ D`
preconnected and marked points `pt v ∈ H_v`, the error `A M (t/(dist ∨ ε^β))^{−ξ}` is `A M ((dist ∨ ε^β)/t)^ξ`. -/
theorem boundaryEstimate_of_t15c {H : CellularEmbedding G o} {ε ρ β ξ A : ℝ} (hε : 0 < ε)
    (h : T15CBoundaryEstimate H ε ρ β ξ A) {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ)
    (hDc : IsPreconnected Dᶜ) (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v) :
    BoundaryEstimate G H.cell pt D (ε ^ β) A ξ := by
  intro u M hharm hM x hx _ t ht c hc hcM
  have ht0 : 0 < t := lt_of_le_of_lt infDist_nonneg ht
  have hm0 : 0 < max (infDist (pt x) (frontier D)) (ε ^ β) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hε β) (le_max_right _ _)
  have key := (h D hDo hDρ hDc u hharm M hM x hx (pt x) (hpt x) t ht0 c).2
    (fun y hy => hc y hy.1 hy.2) hcM
  have heq : (t / max (infDist (pt x) (frontier D)) (ε ^ β)) ^ (-ξ) =
      (max (infDist (pt x) (frontier D)) (ε ^ β) / t) ^ ξ := by
    rw [Real.rpow_neg (div_nonneg ht0.le hm0.le), ← Real.inv_rpow (div_nonneg ht0.le hm0.le), inv_div]
  rw [heq] at key
  exact key

/-! ### Theorem 1.5 on one good environment -/

/-- The probability parameter used for both estimates: `p' = min p (1/2)`. -/
def probParam (p : ℝ) : ℝ := min p (1 / 2)

/-- The exponent `ξ₁ = t15cXi p'` of T15C's boundary estimate. -/
def boundaryExponent (p : ℝ) : ℝ := t15cXi (probParam p)

/-- The constant `C₁ = 2 κ^{ξ₁}` of T15C's boundary estimate (`κ = t15cKappa ρ ρ'`). -/
def boundaryConst (p ρ ρ' : ℝ) : ℝ := 2 * t15cKappa ρ ρ' ^ boundaryExponent p

theorem probParam_pos {p : ℝ} (hp : 0 < p) : 0 < probParam p := lt_min hp (by norm_num)

theorem probParam_lt_one (p : ℝ) : probParam p < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)

theorem boundaryExponent_pos {p : ℝ} (hp : 0 < p) : 0 < boundaryExponent p :=
  t15cXi_pos (probParam_pos hp) (probParam_lt_one p)

theorem boundaryConst_nonneg {p ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') : 0 ≤ boundaryConst p ρ ρ' :=
  mul_nonneg zero_le_two (Real.rpow_nonneg (t15cKappa_pos hρ hρρ').le _)

/-- **[18] Theorem 1.5 on one good environment** (`[18]`; DB5 Details (c)). Let `H` be a cellular embedding
of a connected graph with (LC), marked points `pt v ∈ H_v`, `0 < ε ≤ 1`, `0 < ρ < ρ'`, `0 < β ≤ q ≤ 1`, `p > 0`,
and assume (3.35) at ambient radius `ρ'` (T15A's `Lemma311Holds H ε ρ' β p`) and that the cells meeting `B_ρ(0)`
have diameter `≤ ε^q`. Then for every open `D ⊆ B_ρ(0)` with `ℂ \ D` preconnected, every `f` that is `χ`-Hölder on
`∂D` (constant `C_f`, `|f| ≤ M_f` there) and every discrete harmonic extension `g` of the (1.6) data of `f`:
`|g(x) − g(y)| ≤ A₀ (ε ∨ |pt x − pt y|)^ξ` on `V(D)`, with `A₀ = theorem15Const p' C₁ ξ₁ β q χ C_f M_f` and
`ξ = theorem15Exponent p' ξ₁ β q χ` (`p' = probParam p`, `ξ₁ = boundaryExponent p`, `C₁ = boundaryConst p ρ ρ'`). -/
theorem theorem15_of_lemma311Holds {H : CellularEmbedding G o} (hconn : G.adj.Connected)
    (hLC : H.PointConnected) (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v)
    {ε ρ ρ' β q p : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hβ : 0 < β)
    (hβq : β ≤ q) (hq1 : q ≤ 1) (hp : 0 < p) (h311 : T15A.Lemma311Holds H ε ρ' β p)
    (hcells : ∀ x, (H.cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam (H.cell x) ≤ ε ^ q)
    {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ) (hDc : IsPreconnected Dᶜ)
    {f : ℂ → ℝ} {Cf χ Mf : ℝ} (hCf : 0 ≤ Cf) (hχ : 0 < χ) (hMf : 0 ≤ Mf)
    (hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ)
    (hfM : ∀ z ∈ frontier D, |f z| ≤ Mf) {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g) :
    ∀ x ∈ verticesMeeting H.cell D, ∀ y ∈ verticesMeeting H.cell D,
      |g x - g y| ≤ theorem15Const (probParam p) (boundaryConst p ρ ρ') (boundaryExponent p) β q χ Cf Mf *
        max ε (dist (pt x) (pt y)) ^ theorem15Exponent (probParam p) (boundaryExponent p) β q χ := by
  have hp' := probParam_pos hp
  have h311' : T15A.Lemma311Holds H ε ρ' β (probParam p) :=
    T15A.Lemma311Holds.mono h311 hε0 hε1 le_rfl le_rfl (min_le_left _ _)
  have hDρ' : D ⊆ ball (0 : ℂ) ρ' := hDρ.trans (ball_subset_ball hρρ'.le)
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  have h331 : BoundaryEstimate G H.cell pt D (ε ^ β) (boundaryConst p ρ ρ') (boundaryExponent p) :=
    boundaryEstimate_of_t15c hε0
      (t15c_boundaryEstimate_of_lemma311Holds hconn hLC hε0 hρ hρρ' hp' (probParam_lt_one p) h311')
      hDo hDρ hDc pt hpt
  refine theorem15_deterministic H hconn pt hpt hDo hDb hε0 hε1 hβ hβq hq1 hp'
    (boundaryConst_nonneg hρ hρρ') (boundaryExponent_pos hp) ?_ (disc_of_lemma311Holds hε0 h311' hDρ')
    h331 hCf hχ hMf hf hfM hg
  rintro v ⟨c, hc, hcD⟩
  exact hcells v ⟨c, hc, hDρ hcD⟩

/-! ### Theorem 1.5 with probability `1 − O(ε^α)` -/

/-- A function Hölder on the bounded set `∂D` is bounded there: `∃ M ≥ 0, |f| ≤ M` on `∂D`. -/
theorem exists_abs_le_of_holder {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℝ} {Cf χ : ℝ}
    (hCf : 0 ≤ Cf) (hχ : 0 < χ) (hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ frontier D, |f z| ≤ M := by
  rcases (frontier D).eq_empty_or_nonempty with h | ⟨z₀, hz₀⟩
  · exact ⟨0, le_rfl, fun z hz => by rw [h] at hz; exact absurd hz (Set.notMem_empty z)⟩
  have hfb : Bornology.IsBounded (frontier D) := hDb.closure.subset frontier_subset_closure
  refine ⟨|f z₀| + Cf * diam (frontier D) ^ χ,
    add_nonneg (abs_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg diam_nonneg _)), fun z hz => ?_⟩
  have h1 : |f z| ≤ |f z₀| + |f z - f z₀| := by
    have := abs_sub_abs_le_abs_sub (f z) (f z₀)
    linarith
  have h2 : Cf * dist z z₀ ^ χ ≤ Cf * diam (frontier D) ^ χ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg (dist_le_diam_of_mem hfb hz hz₀) hχ.le) hCf
  linarith [hf z hz z₀ hz₀]

/-- **[18] Theorem 1.5 with probability `1 − O(ε^α)`** for a family of cellular embeddings `H i ω`
of graphs `G i ω` on a probability space `(Ω, P)`, indexed by meshes `ε i ∈ (0, 1]` (dyadic `CellFamily.mesh k` or real
`ε`), with marked points `pt i ω x ∈ H_x`. Inputs: (3.35) at ambient radius `ρ' > ρ` with probability `1 − O(ε^{α₁})`
(T15A's `Lemma311Holds`), Lemma 2.7 on `B_ρ(0)` with probability `1 − O(ε^{α₂})`, and almost surely connected graphs
with (LC). Conclusion, in [18]'s order of constants for fixed `ρ`: there is `α > 0` such that for every `χ > 0` there is
`ξ > 0` such that for every open `D ⊆ B_ρ(0)` with `ℂ \ D` preconnected and every `f` `χ`-Hölder on `∂D` there are
`A₀ > 0` and `C` with `P[some discrete harmonic extension g of (1.6) violates (1.9)] ≤ C ε_i^α` for every `i`
(outer measure, the project's bad-event convention). -/
theorem theorem15_bad_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} (ε : ι → ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ 1) {E : ι → Ω → Type*} (G : ∀ i ω, LFMultigraph ℤ (E i ω))
    (H : ∀ i ω, CellularEmbedding (G i ω) 0) (pt : ι → Ω → ℤ → ℂ)
    (hpt : ∀ i ω x, pt i ω x ∈ (H i ω).cell x) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (h311 : ∃ α₁ : ℝ, 0 < α₁ ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ, ∀ i,
      P {ω | ¬ T15A.Lemma311Holds (H i ω) (ε i) ρ' β p} ≤ ENNReal.ofReal (C₁ * ε i ^ α₁))
    (hconn : ∀ i, ∀ᵐ ω ∂P, (G i ω).adj.Connected)
    (hLC : ∀ i, ∀ᵐ ω ∂P, (H i ω).PointConnected)
    (h27 : ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ∃ α₂ : ℝ, 0 < α₂ ∧ ∃ C₂ : ℝ, ∀ i,
      P {ω | ¬ ∀ x, ((H i ω).cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam ((H i ω).cell x) ≤ ε i ^ q} ≤
        ENNReal.ofReal (C₂ * ε i ^ α₂)) :
    ∃ α : ℝ, 0 < α ∧ ∀ χ : ℝ, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsPreconnected Dᶜ →
      ∀ f : ℂ → ℝ, (∃ Cf : ℝ, ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ i,
        P {ω | ¬ ∀ g : ℤ → ℝ, IsHarmonicExtension (G i ω) (H i ω).cell D f g →
          ∀ x ∈ verticesMeeting (H i ω).cell D, ∀ y ∈ verticesMeeting (H i ω).cell D,
            |g x - g y| ≤ A₀ * max (ε i) (dist (pt i ω x) (pt i ω y)) ^ ξ} ≤
          ENNReal.ofReal (C * ε i ^ α) := by
  obtain ⟨α₁, hα₁, β, hβ, p, hp, C₁, hC₁⟩ := h311
  obtain ⟨q, hq, hq1, α₂, hα₂, C₂, hC₂⟩ := h27
  set β' := min β q with hβ'def
  have hβ' : 0 < β' := lt_min hβ hq
  refine ⟨min α₁ α₂, lt_min hα₁ hα₂, fun χ hχ => ?_⟩
  set ξ := theorem15Exponent (probParam p) (boundaryExponent p) β' q χ with hξdef
  refine ⟨ξ, theorem15Exponent_pos (probParam_pos hp) (boundaryExponent_pos hp) hβ' hq hχ,
    fun D hDo hDρ hDc f hfH => ?_⟩
  obtain ⟨Cf₀, hCf₀⟩ := hfH
  set Cf := max Cf₀ 0 with hCfdef
  have hCf : 0 ≤ Cf := le_max_right _ _
  have hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ := fun z hz w hw =>
    (hCf₀ z hz w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  obtain ⟨Mf, hMf, hfM⟩ := exists_abs_le_of_holder hDb hCf hχ hf
  set A₀ := max (theorem15Const (probParam p) (boundaryConst p ρ ρ') (boundaryExponent p) β' q χ Cf Mf) 1
    with hA₀def
  refine ⟨A₀, lt_of_lt_of_le one_pos (le_max_right _ _), |C₁| + |C₂|, fun i => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε i
  -- the bad event is covered by the bad events of the inputs
  have hsub : {ω | ¬ ∀ g : ℤ → ℝ, IsHarmonicExtension (G i ω) (H i ω).cell D f g →
      ∀ x ∈ verticesMeeting (H i ω).cell D, ∀ y ∈ verticesMeeting (H i ω).cell D,
        |g x - g y| ≤ A₀ * max (ε i) (dist (pt i ω x) (pt i ω y)) ^ ξ} ⊆
      ({ω | ¬ T15A.Lemma311Holds (H i ω) (ε i) ρ' β p} ∪
        {ω | ¬ ∀ x, ((H i ω).cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam ((H i ω).cell x) ≤ ε i ^ q}) ∪
      ({ω | ¬ (G i ω).adj.Connected} ∪ {ω | ¬ (H i ω).PointConnected}) := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨h311ω, hcellsω⟩, hconnω, hLCω⟩ := hcon
    apply hω
    intro g hg x hx y hy
    have hmain := theorem15_of_lemma311Holds hconnω hLCω (pt i ω) (hpt i ω) hε0 hε1 hρ hρρ' hβ'
      (min_le_right _ _) hq1 hp
      (T15A.Lemma311Holds.mono h311ω hε0 hε1 le_rfl (min_le_left _ _) le_rfl) hcellsω hDo hDρ hDc hCf hχ
      hMf hf hfM hg x hx y hy
    refine hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ?_ _))
    exact le_max_of_le_left hε0.le
  have hN1 : P {ω | ¬ (G i ω).adj.Connected} = 0 := ae_iff.mp (hconn i)
  have hN2 : P {ω | ¬ (H i ω).PointConnected} = 0 := ae_iff.mp (hLC i)
  have hpow : ∀ a : ℝ, min α₁ α₂ ≤ a → ε i ^ a ≤ ε i ^ min α₁ α₂ := fun a ha =>
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 ha
  have hle : ∀ (C a : ℝ), min α₁ α₂ ≤ a →
      ENNReal.ofReal (C * ε i ^ a) ≤ ENNReal.ofReal (|C| * ε i ^ min α₁ α₂) := fun C a ha =>
    ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hε0.le _)).trans
      (mul_le_mul_of_nonneg_left (hpow a ha) (abs_nonneg C)))
  calc P _ ≤ P (({ω | ¬ T15A.Lemma311Holds (H i ω) (ε i) ρ' β p} ∪
        {ω | ¬ ∀ x, ((H i ω).cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam ((H i ω).cell x) ≤ ε i ^ q}) ∪
        ({ω | ¬ (G i ω).adj.Connected} ∪ {ω | ¬ (H i ω).PointConnected})) := measure_mono hsub
    _ ≤ (P {ω | ¬ T15A.Lemma311Holds (H i ω) (ε i) ρ' β p} +
          P {ω | ¬ ∀ x, ((H i ω).cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam ((H i ω).cell x) ≤ ε i ^ q}) +
          (P {ω | ¬ (G i ω).adj.Connected} + P {ω | ¬ (H i ω).PointConnected}) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ (ENNReal.ofReal (|C₁| * ε i ^ min α₁ α₂) + ENNReal.ofReal (|C₂| * ε i ^ min α₁ α₂)) + (0 + 0) := by
        rw [hN1, hN2]
        exact add_le_add (add_le_add ((hC₁ i).trans (hle C₁ α₁ (min_le_left _ _)))
          ((hC₂ i).trans (hle C₂ α₂ (min_le_right _ _)))) le_rfl
    _ = ENNReal.ofReal ((|C₁| + |C₂|) * ε i ^ min α₁ α₂) := by
        have hr := Real.rpow_nonneg hε0.le (min α₁ α₂)
        rw [add_zero, add_zero, ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hr)
          (mul_nonneg (abs_nonneg _) hr), add_mul]

end MatedCRTHarmonic.GMSMain.T15B
