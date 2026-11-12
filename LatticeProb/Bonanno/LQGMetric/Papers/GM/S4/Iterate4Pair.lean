/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4Pair at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3Gt1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateT42

/-!
# GM Theorem 4.2 for one pair of points (DEC-89, D89b: nodes and packet E)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Thm 4.2 (l. 1554–1571); the union
bound over the pairs of grid points (l. 1540, 2437–2441, `gm_T4_2_assembly`). Decision
`decisions/DEC-89.md` (D89b): the chain §4.3–4.7 proves T4.2 for one pair `(𝕫, 𝕨)`
(`T4_2PairOne`, `λ₃ ≤ 1 < λ₄`, dyadic `ε`); `T4_2Pair` is its form for general `λ₃ < λ₄` and every
`ε`; `T4_2Gt1S` is `T4_2Gt1` with `λ₃ < λ₄`.

All three nodes carry `0 < ε₀` (GM l. 1557: "a small number `ε₀ > 0`"); since D95, `T4_2` and
`T4_2Gt1` carry it too (for `ε₀ ≤ 0` the set `ℛ ⊆ (0, ε₀𝕣]` is empty, while
the conclusion asks for `r ∈ ℛ`).

* `gm_T4_2Gt1S_of_pair` (packet E): the union bound `gm_T4_2_assembly` with `M = 4q + 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the witness of T4.2's conclusion for the pair `(𝕫, 𝕨)` at scale `ε`, with a radius
`rr 𝕣 ε k` of condition (1) (`k < ⌊μ log₈ ε⁻¹⌋`) -/
def t42Wit {Ω : Type} (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) (h : Ω → DistC)
    (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) (lam : Fin 5 → ℝ) (rr : ℝ → ℝ → ℕ → ℝ) (μ 𝕣 ε : ℝ)
    (𝕫 𝕨 : ℂ) (ω : Ω) : Prop :=
  ∃ z : ℂ, ∃ k < ⌊μ * Real.logb 8 ε⁻¹⌋₊,
    (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (lam 1 * rr 𝕣 ε k)).Nonempty ∧
    h ω ∈ Ef (rr 𝕣 ε k) z 𝕫 𝕨 ∧ 𝕫 ∉ Metric.ball z (lam 3 * rr 𝕣 ε k) ∧
    𝕨 ∉ Metric.ball z (lam 3 * rr 𝕣 ε k)

/-- the radii of T4.2 (1) at base scale `R`, given as a function -/
def T42Radii (lam : Fin 5 → ℝ) (μ ν R ε₀ : ℝ) (Rad : Set ℝ) (rr : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ ε ∈ Ioc (0 : ℝ) ε₀, (∀ k < ⌊μ * Real.logb 8 ε⁻¹⌋₊,
    rr R ε k ∈ Icc (ε ^ (1 + ν) * R) (ε * R) ∧ rr R ε k ∈ Rad) ∧
    ∀ k, k + 1 < ⌊μ * Real.logb 8 ε⁻¹⌋₊ → lam 3 / lam 0 ≤ rr R ε k / rr R ε (k + 1)

/-- **GM Theorem 4.2 for one pair, `λ₃ ≤ 1 < λ₄`, dyadic `ε`** (GM l. 1611, 1613; the chain
§4.3–4.7: `gm_P4_17_ae`, `gm_L4_20E`, `gm_L4_20F`, L4.7 per `k`, `GMP4_12At`) -/
def T4_2PairOne : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  ∃ νs : ℝ, νs ∈ Ioo (0 : ℝ) 1 ∧ ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν ≤ νs → ∀ lam : Fin 5 → ℝ,
  0 < lam 0 → lam 0 < lam 1 → lam 1 ≤ lam 2 → lam 2 ≤ 1 → 1 < lam 3 → lam 3 < lam 4 →
  ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ (ℓ : ℝ) (U : Set ℂ), ℓ ∈ Ioo (0 : ℝ) 1 → IsOpen U →
  Bornology.IsBounded U → ∀ ε₀ Λ η M : ℝ, 0 < ε₀ → 0 < η → 0 < M → ∃ C ε₁ : ℝ, 0 ≤ C ∧ 0 < ε₁ ∧
  ∀ (R : ℝ) (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    (rr : ℝ → ℝ → ℕ → ℝ), 0 < R → GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef →
    T42Radii lam μ ν R ε₀ Rad rr →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ →
    ∃ Reg : Set Ω, P.real Regᶜ ≤ η ∧
    ∀ 𝕫 𝕨 : ℂ, 𝕫 ∈ (fun x => (R : ℂ) * x) '' U → 𝕨 ∈ (fun x => (R : ℂ) * x) '' U →
      ℓ * R ≤ ‖𝕫 - 𝕨‖ →
      P.real (Reg ∩ {ω | ¬ t42Wit sel h Ef lam rr μ R ((2 : ℝ)⁻¹ ^ n) 𝕫 𝕨 ω}) ≤
        C * ((2 : ℝ)⁻¹ ^ n) ^ M

/-- **GM Theorem 4.2 for one pair**, general `λ₃ < λ₄`, every `ε < ε₁` (D89b) -/
def T4_2Pair : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  ∃ νs : ℝ, νs ∈ Ioo (0 : ℝ) 1 ∧ ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν ≤ νs → ∀ lam : Fin 5 → ℝ,
  0 < lam 0 → lam 0 < lam 1 → lam 1 ≤ lam 2 → lam 2 < lam 3 → lam 3 < lam 4 →
  ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ (ℓ : ℝ) (U : Set ℂ), ℓ ∈ Ioo (0 : ℝ) 1 → IsOpen U →
  Bornology.IsBounded U → ∀ ε₀ Λ η M : ℝ, 0 < ε₀ → 0 < η → 0 < M → ∃ C ε₁ : ℝ, 0 ≤ C ∧ 0 < ε₁ ∧
  ∀ (R : ℝ) (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    (rr : ℝ → ℝ → ℕ → ℝ), 0 < R → GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef →
    T42Radii lam μ ν R ε₀ Rad rr →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    ∃ Reg : Set Ω, P.real Regᶜ ≤ η ∧
    ∀ 𝕫 𝕨 : ℂ, 𝕫 ∈ (fun x => (R : ℂ) * x) '' U → 𝕨 ∈ (fun x => (R : ℂ) * x) '' U →
      ℓ * R ≤ ‖𝕫 - 𝕨‖ →
      P.real (Reg ∩ {ω | ¬ t42Wit sel h Ef lam rr μ R ε 𝕫 𝕨 ω}) ≤ C * ε ^ M

/-- `T4_2Gt1` with the extra hypotheses `lam 2 < lam 3` and `0 < ε₀` (GM l. 1557) -/
def T4_2Gt1S : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  ∃ νs : ℝ, νs ∈ Ioo (0 : ℝ) 1 ∧ ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν ≤ νs → ∀ lam : Fin 5 → ℝ,
  0 < lam 0 → lam 0 < lam 1 → lam 1 ≤ lam 2 → lam 2 ≤ lam 3 → lam 3 < lam 4 → 1 < lam 3 →
  lam 2 < lam 3 →
  ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ (q ℓ : ℝ) (U : Set ℂ), 0 < q → ℓ ∈ Ioo (0 : ℝ) 1 → IsOpen U →
  Bornology.IsBounded U → ∀ ε₀ Λ η : ℝ, 0 < ε₀ → 0 < η → ∃ ε₁ : ℝ, 0 < ε₁ ∧
  ∀ (R : ℝ) (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC), 0 < R →
    GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    P {ω | ∀ a b : ℂ, (∃ m : ℤ × ℤ, a = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      (∃ m : ℤ × ℤ, b = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      a ∈ (fun x => (R : ℂ) * x) '' U → b ∈ (fun x => (R : ℂ) * x) '' U → ℓ * R ≤ ‖a - b‖ →
      ∃ z : ℂ, ∃ r ∈ Rad, r ∈ Icc (ε ^ (1 + ν) * R) (ε * R) ∧
        (range (sel a b (h ω)) ∩ Metric.ball z (lam 1 * r)).Nonempty ∧ h ω ∈ Ef r z a b ∧
        a ∉ Metric.ball z (lam 3 * r) ∧ b ∉ Metric.ball z (lam 3 * r)}ᶜ ≤
      ENNReal.ofReal η

/-- the radii of (1), chosen as a function (`Classical.choose`) -/
theorem gm_exists_T42Radii {D : DistC → ContMetric} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    {μ ν : ℝ} {lam : Fin 5 → ℝ} {𝕡 R ε₀ Λ : ℝ} {Rad : Set ℝ} {E : ℝ → ℂ → Set DistC}
    {Ef : ℝ → ℂ → ℂ → ℂ → Set DistC} (H : GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef) :
    ∃ rr : ℝ → ℝ → ℕ → ℝ, T42Radii lam μ ν R ε₀ Rad rr := by
  classical
  have H1 := H.2.2.2.2.1
  refine ⟨fun _ ε => if hε : ε ∈ Ioc (0 : ℝ) ε₀ then Classical.choose (H1 ε hε) else fun _ => 0,
    fun ε hε => ?_⟩
  simp only [dif_pos hε]
  exact Classical.choose_spec (H1 ε hε)

/-- **packet E** (D89b): the per-pair statement and the union bound over the grid pairs give
`T4_2Gt1S` (GM l. 1540, 2437–2441) -/
theorem gm_T4_2Gt1S_of_pair (H : T4_2Pair) : T4_2Gt1S := by
  intro γ D c hγ hγ2 hD sel hsel
  obtain ⟨νs, hνs, H1⟩ := H hγ hγ2 hD sel hsel
  refine ⟨νs, hνs, fun {μ ν} hμ hμν hν lam h0 h01 h12 _ h34 _ h23 => ?_⟩
  obtain ⟨𝕡, h𝕡, H2⟩ := H1 hμ hμν hν lam h0 h01 h12 h23 h34
  refine ⟨𝕡, h𝕡, fun q ℓ U hq hℓ hU hUb ε₀ Λ η hε₀ hη => ?_⟩
  obtain ⟨C, ε₁', hC, hε₁', H3⟩ := H2 ℓ U hℓ hU hUb ε₀ Λ (η / 2) (4 * q + 1) hε₀ (by positivity)
    (by positivity)
  obtain ⟨ρ₀, hρ₀⟩ := hUb.subset_ball (0 : ℂ)
  have hUρ : U ⊆ Metric.ball (0 : ℂ) (max ρ₀ 0) :=
    hρ₀.trans (Metric.ball_subset_ball (le_max_left _ _))
  obtain ⟨ε₂, hε₂, HA⟩ := gm_T4_2_assembly hq (le_max_right ρ₀ 0) hC hη
  refine ⟨min (min ε₁' ε₂) ε₀, lt_min (lt_min hε₁' hε₂) hε₀, ?_⟩
  intro R Rad E Ef hR hGeo Ω _ P _ h hh ε hε
  obtain ⟨rr, hrr⟩ := gm_exists_T42Radii hGeo
  have hε1 : ε < ε₁' := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ε < ε₂ := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε0 : ε ≤ ε₀ := (hε.2.trans_le (min_le_right _ _)).le
  obtain ⟨Reg, hReg, Hp⟩ := H3 R Rad E Ef rr hR hGeo hrr P h hh ε ⟨hε.1, hε1⟩
  have HB := HA ε ⟨hε.1, hε2⟩ R hR U hUρ P Reg (fun a b => ℓ * R ≤ ‖a - b‖)
    (fun a b => {ω | t42Wit sel h Ef lam rr μ R ε a b ω}) hReg
    (fun a b ha hb hab => Hp a b ha hb hab)
  refine le_trans (measure_mono (compl_subset_compl.mpr ?_)) HB
  intro ω hω a b ha hb haU hbU hab
  obtain ⟨z, k, hk, hhit, hEf, hza, hzb⟩ := hω a b ha hb haU hbU hab
  obtain ⟨hk1, -⟩ := hrr ε ⟨hε.1, hε0⟩
  exact ⟨z, rr R ε k, (hk1 k hk).2, (hk1 k hk).1, hhit, hEf, hza, hzb⟩

end LQGMetric.GM
