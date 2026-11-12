/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6L411 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond7

/-!
# GM Lemma 4.11 for every `a ∈ (0, a₀]` (P2-M2K6)

Source: GM `uniqueness-final.tex`, Lemma 4.11 and its proof, l. 1979–1990. `gm_L4_11A` is
`gm_L4_11` (RegularityL411.lean) with the same proof, concluding for every `a ∈ (0, a₀]`
(`a₀ = regAmin a₂ … a₇`): each condition 2–7 holds with the required probability for all `a`
below its threshold (`RegCondAt`), so any smaller `a` works too; the conclusion is stated as
`P[ℰ_𝕣ᶜ] ≤ 1 − p` (the union bound of the proof, l. 1983–1990).
Theorem 4.2's proof needs `a ≤ ℓ` (GM l. 2004–2006, Lemma 4.19).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Event
variable {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
  {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} {R : RegPar}

/-- the assembly of GM Lemma 4.11 for every `a ∈ (0, regAmin a₂ … a₇]` -/
theorem gm_L4_11_of_condsA [IsProbabilityMeasure P] {p a₂ a₃ a₄ a₅ a₆ a₇ a : ℝ} (hp : p < 1)
    (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) (ha₅ : 0 < a₅) (ha₆ : 0 < a₆) (ha₇ : 0 < a₇)
    (h1 : ∀ 𝕣 : ℝ, 0 < 𝕣 → P (regC1 D h R 𝕣)ᶜ ≤ ENNReal.ofReal ((1 - p) / 7))
    (H2 : RegCondAt P (regC2 D h H R) (1 - (1 - p) / 7) a₂)
    (H3 : RegCondAt P (regC3 D h R) (1 - (1 - p) / 7) a₃)
    (H4 : RegCondAt P (regC4 H R) (1 - (1 - p) / 7) a₄)
    (H5 : RegCondAt P (regC5 h R) (1 - (1 - p) / 7) a₅)
    (H6 : RegCondAt P (regC6 D P h R) (1 - (1 - p) / 7) a₆)
    (H7 : RegCondAt P (regC7 D P h H R) (1 - (1 - p) / 7) a₇)
    (ha : a ∈ Ioc 0 (regAmin a₂ a₃ a₄ a₅ a₆ a₇)) :
    ∀ 𝕣 : ℝ, 0 < 𝕣 → P (regEvent D P h H R 𝕣 a)ᶜ ≤ ENNReal.ofReal (1 - p) := by
  have hδ : 1 - (1 - (1 - p) / 7) = (1 - p) / 7 := by ring
  have ha0 : 0 < a := ha.1
  have hle : a ≤ a₂ ∧ a ≤ a₃ ∧ a ≤ a₄ ∧ a ≤ a₅ ∧ a ≤ a₆ ∧ a ≤ a₇ := by
    have h := ha.2
    simp only [regAmin, le_min_iff] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2⟩
  intro 𝕣 h𝕣
  refine gm_regEvent_compl_le.trans ?_
  unfold RegCondAt at H2 H3 H4 H5 H6 H7
  rw [hδ] at H2 H3 H4 H5 H6 H7
  have e : ENNReal.ofReal (1 - p) = ENNReal.ofReal ((1 - p) / 7) + ENNReal.ofReal ((1 - p) / 7) +
      ENNReal.ofReal ((1 - p) / 7) + ENNReal.ofReal ((1 - p) / 7) + ENNReal.ofReal ((1 - p) / 7) +
      ENNReal.ofReal ((1 - p) / 7) + ENNReal.ofReal ((1 - p) / 7) := by
    have h0 : 0 ≤ (1 - p) / 7 := by linarith
    rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by linarith) h0,
      ← ENNReal.ofReal_add (by linarith) h0, ← ENNReal.ofReal_add (by linarith) h0,
      ← ENNReal.ofReal_add (by linarith) h0, ← ENNReal.ofReal_add (by linarith) h0]
    congr 1
    ring
  rw [e]
  gcongr
  · exact h1 𝕣 h𝕣
  · exact H2 a ⟨ha0, hle.1⟩ 𝕣 h𝕣
  · exact H3 a ⟨ha0, hle.2.1⟩ 𝕣 h𝕣
  · exact H4 a ⟨ha0, hle.2.2.1⟩ 𝕣 h𝕣
  · exact H5 a ⟨ha0, hle.2.2.2.1⟩ 𝕣 h𝕣
  · exact H6 a ⟨ha0, hle.2.2.2.2.1⟩ 𝕣 h𝕣
  · exact H7 a ⟨ha0, hle.2.2.2.2.2⟩ 𝕣 h𝕣

end Event

/-- **GM Lemma 4.11** for every `a ∈ (0, a₀]` -/
theorem gm_L4_11A (h31a : LMLem3_1a) (h24e : GMS2_4e) (h318 : DFGPSProp3_18)
    (h320 : DFGPSLem3_20) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {lam : Fin 5 → ℝ}
    (h0 : 0 < lam 0) (h01 : lam 0 < lam 1) (h12 : lam 1 ≤ lam 2) (h23 : lam 2 ≤ lam 3)
    (h34 : lam 3 < lam 4) :
    ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ {γ : ℝ}, 0 < γ → γ < 2 → ∀ {D : DistC → ContMetric} {c : ℝ → ℝ},
      IsWeakLQGMetric γ D c → ∀ {cp : CONFParams}, CONFLem3_5At γ D c cp →
      ∀ {χ χ' : ℝ}, 0 < χ → χ < xiGamma γ * (Q γ - 2) → xiGamma γ * (Q γ + 2) < χ' →
      ∀ {U : Set ℂ}, Bornology.IsBounded U → ∀ {ℓ : ℝ}, ℓ ∈ Ioo (0 : ℝ) 1 →
      ∀ {p : ℝ}, p ∈ Ioo (0 : ℝ) 1 →
      ∃ V : Set ℂ, IsOpen V ∧ Bornology.IsBounded V ∧ IsConnected V ∧ U ⊆ V ∧
        ∀ ε₀ : ℝ, 0 < ε₀ → ∃ a₀ ∈ Ioo (0 : ℝ) 1, ∀ a ∈ Ioc (0 : ℝ) a₀,
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (H : ℝ → ℂ → Ω → ℝ),
          DFGPS.IsCircleAvgVersion h P H → ∀ R : RegPar, R.ξ = xiGamma γ → R.c = c →
          R.p = cp → R.χ = χ → R.χ' = χ' → R.μ = μ → R.ν = ν → R.lam = lam → R.ℓ = ℓ →
          R.U = U → R.V = V → ∀ Rad : ℝ → Set ℝ,
          (∀ 𝕣 > 0, ∀ ε ∈ Ioc (0 : ℝ) ε₀, (∀ k < ⌊μ * Real.logb 8 ε⁻¹⌋₊,
              R.rr 𝕣 ε k ∈ Icc (ε ^ (1 + ν) * 𝕣) (ε * 𝕣) ∧ R.rr 𝕣 ε k ∈ Rad 𝕣) ∧
            ∀ k, k + 1 < ⌊μ * Real.logb 8 ε⁻¹⌋₊ → lam 3 / lam 0 ≤ R.rr 𝕣 ε k / R.rr 𝕣 ε (k + 1)) →
          (∀ 𝕣 > 0, ∀ z, ∀ r ∈ Rad 𝕣, AEEventIn P (fieldSigma (fun ω => addConst (h ω)
              (-circleAvg (h ω) (lam 4 * r) z)) (annulus z (lam 0 * r) (lam 3 * r)))
              (h ⁻¹' R.E r z)) →
          (∀ 𝕣 > 0, ∀ z, ∀ r ∈ Rad 𝕣, ENNReal.ofReal 𝕡 ≤ P (h ⁻¹' R.E r z)) →
          ∀ 𝕣 : ℝ, 0 < 𝕣 → P (regEvent D P h H R 𝕣 a)ᶜ ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨𝕡, h𝕡, H5⟩ := gm_regC5_prob h31a hμ hν h0 h01 h12 h23 h34
  refine ⟨𝕡, h𝕡, ?_⟩
  intro γ hγ hγ2 D c hD cp h35 χ χ' hχ hχQ hχ' U hU ℓ hℓ p hp
  obtain ⟨V, hVo, hVb, hVc, hUV, H1⟩ := gm_regC1_prob h24e hγ hγ2 hD hU
    (β := (1 - p) / 7) (by linarith [hp.2]) (by linarith [hp.1])
  refine ⟨V, hVo, hVb, hVc, hUV, ?_⟩
  intro ε₀ hε₀
  have hq1 : 1 - (1 - p) / 7 < 1 := by linarith [hp.2]
  obtain ⟨a₂, ha₂, H2⟩ := gm_regC2_prob hγ hγ2 hD hVb hℓ.1 _ hq1
  obtain ⟨a₃, ha₃, H3⟩ := gm_regC3_prob h318 h320 hγ hγ2 hD hχ hχQ hχ' (ℓ := ℓ) hVb _ hq1
  obtain ⟨a₄, ha₄, H4⟩ := gm_regC4_prob hVb _ hq1
  obtain ⟨a₅, ha₅, H5'⟩ := H5 (ℓ := ℓ) hVb ε₀ hε₀ _ hq1
  obtain ⟨a₆, ha₆, H6⟩ := gm_regC6_prob h35 (ℓ := ℓ) hVb _ hq1
  obtain ⟨a₇, ha₇, H7⟩ := gm_regC7_prob h318 h320 hγ hγ2 hD h35 hχ hχQ hχ' hVb hUV hℓ.1 hℓ.2.le
    _ hq1
  refine ⟨regAmin a₂ a₃ a₄ a₅ a₆ a₇, gm_regAmin_pos ha₂ ha₃ ha₄ ha₅ ha₆ ha₇, ?_⟩
  intro a ha Ω _ P _ h hh H hH R hRξ hRc hRp hRχ hRχ' hRμ hRν hRlam hRℓ hRU hRV Rad hrr hEm hEp
  exact gm_L4_11_of_condsA hp.2 ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
    (fun 𝕣 h𝕣 => H1 P h hh R hRU hRV 𝕣 h𝕣) (H2 P h H hh hH R hRξ hRc hRV hRℓ)
    (H3 P h hh R hRξ hRc hRχ hRχ' hRV hRℓ) (H4 P h H hh hH R hRV)
    (H5' P h hh R hRμ hRν hRlam hRV hRℓ Rad hrr hEm hEp) (H6 P h hh R hRξ hRc hRp hRV hRℓ)
    (H7 P h H hh hH R hRξ hRc hRp hRχ hRχ' hRU hRV hRℓ) ha

end LQGMetric.GM
