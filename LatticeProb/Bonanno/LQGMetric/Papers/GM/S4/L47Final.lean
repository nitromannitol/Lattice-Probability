/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Sel2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Conditional
import LatticeProb.Bonanno.LQGMetric.Field.MarkovZBIndep
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47InputsA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47InputsW
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47InputsG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47InputsZ

/-!
# GM Lemma 4.7, (4.12) ⇒ (4.13) at `𝓕_k` with the traces `hA` and `𝕨 ∉ 𝓑^•_{t_k}` discharged
(task P2-L47)

GM, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 4.7, l. 1890–1912.
`gm_L4_7_of_null` is `gm_L4_7_pair_of_null` (P2-E2S) with

* `hA` (traces of `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` on `Stab ∩ Hit`, GM l. 1701–1706) proved:
  `gm_L4_6c_hA` (`L47InputsA.lean`);
* the a.s. hypothesis `hw : 𝕨 ∉ 𝓑^•_{t_k}` (not an a.s. fact; GM use it only on
  `G ⊆ {𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})}`) removed: `gm_L4_6c_nw` (`L47InputsW.lean`);
* `G₀ ∈ σ(h|_{ℂ∖B_ρ(z)})` asked only almost surely (`gm_L4_7_pair_ae`, `L47InputsG.lean`), as
  GM's "by locality" gives it;
* `hρ : ρ ≤ λ₄ε𝕣` derived from `ρ ≤ r < λ₄ε𝕣`; `r < λ₄ε𝕣` holds for GM's radii
  `r ≤ ε𝕣` and `λ₄ = 4 > 1` ((4.59)), `gm_lt_lam4_of_le`.

Remaining inputs: the descriptive-set-theory leaves `hnullGW`, `hnullGC`, `GMAvoidRelAn`
(P2-E3d), GM's hypothesis (4.2) `h42`, and the measurability facts `hF`, `hStab`, `hHit`,
`hEr`, `hEf`, `hHit2`, `hG₀F`, `hG₀G` (see `handoff/P2-L47.md`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `r < λ₄ε𝕣` for GM's radii `r ≤ ε𝕣` when `λ₄ > 1` (GM (4.59): `λ₄ = 4`) -/
theorem gm_lt_lam4_of_le {r ε 𝕣 lam4 : ℝ} (hε𝕣 : 0 < ε * 𝕣) (hr : r ≤ ε * 𝕣) (h4 : 1 < lam4) :
    r < lam4 * ε * 𝕣 := by
  have : ε * 𝕣 < lam4 * (ε * 𝕣) := lt_mul_left hε𝕣 h4
  rw [mul_assoc]
  linarith

/-- **GM (4.12) ⇒ (4.13)** for one pair `(z, r)` at `𝓕_k`, with GM Lemmas 4.5, 4.6 (b), (c)
applied -/
theorem gm_L4_7_of_null (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {𝕫 𝕨 z : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < lam4 * ε * 𝕣) (hρr : ρ ≤ r) (hr : r < lam4 * ε * 𝕣)
    {V : ℕ → Set ℂ} (hVo : ∀ n, IsOpen (V n))
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hnullGW : ∀ (u : unitInterval) (j : Bool × ℚ) (n : ℕ) (s : Finset (ℤ × ℤ)),
      NullMeasurableSet
        (gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u j ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hnullGC : ∀ (u : unitInterval) (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) (n : ℕ)
      (s : Finset (ℤ × ℤ)),
      NullMeasurableSet ({g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
        (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β))) u i} ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hAvAn : GMAvoidRelAn 𝕫 z r)
    (hF : gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k) ≤ ‹MeasurableSpace Ω›)
    {Er Ef Hit2 G₀ : Set Ω} (hEr : MeasurableSet Er) (hEf : MeasurableSet Ef)
    (hStab : MeasurableSet (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r))
    (hHit : MeasurableSet (gmHitBall D h 𝕫 𝕨 η z r)) (hHit2 : MeasurableSet Hit2)
    (hsub : Hit2 ⊆ gmHitBall D h 𝕫 𝕨 η z r)
    (hG₀F : MeasurableSet[gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)] G₀)
    (hG₀G : AEEventIn P (fieldSigmaClosed h (Metric.ball z ρ)ᶜ) G₀) {Λ : ℝ} (hΛ : 0 < Λ)
    (h42 : ∀ᵐ x ∂P, x ∈ G₀ → (P⟦Er ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x ≤
      Λ * (P⟦Ef ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x) :
    ∀ᵐ x ∂P, (P⟦Er ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        G₀.indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((P⟦Ef ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        G₀.indicator (fun _ => (1 : ℝ)) x) := by
  have hE2b := gm_L4_5_E2b_of_null h38 hC24 hC27 hC14 hγ hγ2 hD P h hh h𝕫𝕨 hη k hℓ𝕣 hε hVo hV
    hnullGW hnullGC
  have hρ : ρ < lam4 * ε * 𝕣 := hρr.trans_lt hr
  have hA := gm_L4_6c_hA (𝕫 := 𝕫) (z := z) (𝕨 := 𝕨) (η := η) (lam1 := lam1) (ν := ν) (Rads := Rads) (r := r)
    (ℓ := ℓ) (β := β) (k := k) h38 hγ hγ2 hD hh hε ha hρ
  have hL46 := gm_L4_6c_nw h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hε ha hρ.le hρr hr
    (gm_arcRelAn 𝕫) hAvAn hE2b hA
  have hStabG := gm_L4_6b h38 hC24 hC27 hC14 hγ hγ2 hD hh (ℓ := ℓ) (β := β) (k := k)
    (lam1 := lam1) (ν := ν) (Rads := Rads) hε ha hρ.le hρr (gm_arcRelAn 𝕫) hAvAn
  exact gm_L4_7_pair_ae hF (MarkovZBIndep.fieldSigmaClosed_le hh _) hEr hEf hStab hHit hHit2 hsub
    hG₀F hG₀G hStabG hL46 hΛ h42

/-- **GM (4.12) ⇒ (4.13)** with GM's `G = {(z,r) ∈ 𝒵_k} ∩ {𝕨 ∉ B_R(𝓑^•_{t_k})}` (`G ∈ 𝒢` a.s. proved) for one pair `(z, r)` at `𝓕_k`, with GM Lemmas 4.5, 4.6 (b), (c)
applied -/
theorem gm_L4_7_of_null_G (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {𝕫 𝕨 z : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < lam4 * ε * 𝕣) (hρr : ρ ≤ r) (hr : r < lam4 * ε * 𝕣)
    {V : ℕ → Set ℂ} (hVo : ∀ n, IsOpen (V n))
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hnullGW : ∀ (u : unitInterval) (j : Bool × ℚ) (n : ℕ) (s : Finset (ℤ × ℤ)),
      NullMeasurableSet
        (gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u j ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hnullGC : ∀ (u : unitInterval) (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) (n : ℕ)
      (s : Finset (ℤ × ℤ)),
      NullMeasurableSet ({g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
        (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β))) u i} ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hAvAn : GMAvoidRelAn 𝕫 z r)
    (hF : gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k) ≤ ‹MeasurableSpace Ω›)
    {Er Ef Hit2 : Set Ω} {R : ℝ} (hEr : MeasurableSet Er) (hEf : MeasurableSet Ef)
    (hStab : MeasurableSet (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r))
    (hHit : MeasurableSet (gmHitBall D h 𝕫 𝕨 η z r)) (hHit2 : MeasurableSet Hit2)
    (hsub : Hit2 ⊆ gmHitBall D h 𝕫 𝕨 η z r)
    (hG₀F : MeasurableSet[gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)]
      (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R)) {Λ : ℝ} (hΛ : 0 < Λ)
    (h42 : ∀ᵐ x ∂P, x ∈ gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R →
      (P⟦Er ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x ≤
      Λ * (P⟦Ef ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x) :
    ∀ᵐ x ∂P, (P⟦Er ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((P⟦Ef ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x) :=
  gm_L4_7_of_null h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hℓ𝕣 hε ha hρr hr hVo hV hnullGW hnullGC
    hAvAn hF hEr hEf hStab hHit hHit2 hsub hG₀F
    (gm_G0_aeEventIn h38 hγ hγ2 hD hh hε ha (hρr.trans hr.le)) hΛ h42

end LQGMetric.GM
