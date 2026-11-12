/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5a
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412oRK
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6e-1 (D130B §5): Weyl covariance of the iteration under `normIn`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`:
`σ^ε_{s,𝕣}` (3.17), C:1292–1302, `R^ε_𝕣` C:1154 ("`h` viewed modulo additive constant"),
iteration C:1543–1566; Weyl scaling `D_{h+c} = e^{ξc} D_h` (GM (1.6), Axiom III). Decision D130B
(decisions/DEC-130B.md §3, step SCALE/TRANSFER), DV-D130B-1 (own standard argument: CONF's field
is normalized, C:347, so CONF never spells this out).

* `t39k6_confRKAddConst_pos`: copy of `GM.p412o_confRKAddConst` (whose proof uses only `0 < ε`)
  for every `ε > 0`, in particular `ε = 1`; `t39k6_confRK_normIn_ae`: all dyadic `ε` at once.
* `t39k6_gArc_smul`: adapter of `t39k5_gArc_smul` (S3T39K5b) to `d' = λ d` pointwise.
* `t39k6_confSigma_smul`: `σ` for `λ d` at `λ s` is `λ σ` (`GM.p412n_confSigma_le` twice).
* **`t39k6_iter_normIn`**: a.s., for all `k`, the radii of the iteration for `normIn h ψ` started
  at `λτ` are `λ` times those for `h`, `λ = e^{−ξ h(ψ)}`.
* `t39k6_localSigma0_normIn`, `t39k6_isLocalSetDet0_normIn_of_ae_eq`,
  `t39k6_aeEventIn_localSigma0_of_ae_eq`: the transfers of D130B §3 (TRANSFER, AE-CONGR).
* `t39k6_exists_measurable_nat_of_ae`: EVENTS→FUN (`measurable_find`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric
namespace CONF

/-! ## `R^ε_𝕣` under a random additive constant, every `ε > 0` -/

section RK
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- copy of `GM.p412o_confRKAddConst` with `0 < ε` in place of `ε ∈ (0,1)` (its proof uses only
`0 < ε`): a.s., for all `K` at once, `R^ε_𝕣(K)` of `h + a` equals that of `h` (C:1154) -/
theorem t39k6_confRKAddConst_pos {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (p : CONFParams) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (a : Ω → ℝ) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, confRK (xiGamma γ) c D P (fun ω => addConst (h ω) (a ω)) p R ε K ω =
      confRK (xiGamma γ) c D P h p R ε K ω := by
  set m := ε * R / 4
  have hεR : 0 < ε * R := mul_pos hε hR
  have hall : ∀ z ∈ gridPts m, ∀ᵐ ω ∂P, ∀ k : ℤ, ∀ T : Finset (ℤ × ℤ),
      (ω ∈ confEU (xiGamma γ) c D P (fun ω => addConst (h ω) (a ω)) p ((2 : ℝ) ^ k * (ε * R)) z T ↔
        ω ∈ confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ k * (ε * R)) z T) := fun z _ =>
    ae_all_iff.2 fun k => GM.p412o_ae_confEU_iff hD p hh a (mul_pos (zpow_pos two_pos k) hεR) z
  filter_upwards [(ae_ball_iff (GM.p412o_countable_gridPts m)).2 hall] with ω hω K
  unfold confRK
  congr 2
  refine iSup_congr fun z => iSup_congr fun hz => ?_
  refine GM.p412o_confRho_congr (fun k => ?_) _
  simp only [confE, mem_iInter]
  exact forall_congr' fun T => forall_congr' fun _ => hω z hz.1 k T

/-- a.s., for all dyadic `ε = 2⁻ʲ` (`j ∈ ℕ`, including `ε = 1`) and all `K`,
`R^ε_𝕣(K)` is the same for `normIn h ψ` and `h` -/
theorem t39k6_confRK_normIn_ae {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (p : CONFParams) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (ψ : TestC) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∀ (j : ℕ) (K : Set ℂ),
      confRK (xiGamma γ) c D P (normIn h ψ) p R ((2 : ℝ)⁻¹ ^ j) K ω =
        confRK (xiGamma γ) c D P h p R ((2 : ℝ)⁻¹ ^ j) K ω :=
  ae_all_iff.2 fun j => t39k6_confRKAddConst_pos hD p hh (fun ω => -(h ω ψ)) hR
    (pow_pos (by norm_num) j)

end RK

/-! ## Deterministic scaling of the arcs and of `σ` -/

section Det
variable {d d' : ContMetric} {lm : ℝ}

/-- `d' = λ d` as `ContMetric.smul` -/
theorem t39k6_eq_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) :
    d' = d.smul lm hlm :=
  Subtype.ext (ContinuousMap.ext fun q => hd q.1 q.2)

/-- the arcs `I^{(t)}` (C:1543) are scale invariant (adapter of `t39k5_gArc_smul`) -/
theorem t39k6_gArc_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z₀ : ℂ)
    (t : ℝ) (I : Set ℂ) : t39gArc d' z₀ (lm * t) I = t39gArc d z₀ t I := by
  rw [t39k6_eq_smul hlm hd]; exact t39k5_gArc_smul hlm d z₀ t I

end Det

section Sigma
variable {Ω : Type} [MeasurableSpace Ω]

/-- `σ^ε_{λs,𝕣}` for `D_{h'} = λ D_h` with the same `R^ε_𝕣` equals `λ σ^ε_{s,𝕣}` (CONF (3.17)) -/
theorem t39k6_confSigma_smul {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h h' : Ω → DistC} {p : CONFParams} {z₀ : ℂ} {R ε s lm : ℝ} {ω : Ω} (hlm : 0 < lm)
    (hd : ∀ u v, (D (h' ω)).1 (u, v) = lm * (D (h ω)).1 (u, v))
    (hRK : ∀ K, confRK ξ cc D P h' p R ε K ω = confRK ξ cc D P h p R ε K ω) :
    confSigma ξ cc D P h' p z₀ R ε (lm * s) ω =
      ENNReal.ofReal lm * confSigma ξ cc D P h p z₀ R ε s ω := by
  refine le_antisymm (GM.p412n_confSigma_le hlm hd fun K => (hRK K).le) ?_
  have hinv := GM.p412n_confSigma_le (z₀ := z₀) (s := lm * s) (inv_pos.2 hlm)
    (GM.p412n_inv_smul hlm hd) fun K => (hRK K).ge
  rw [← mul_assoc, inv_mul_cancel₀ hlm.ne', one_mul] at hinv
  calc ENNReal.ofReal lm * confSigma ξ cc D P h p z₀ R ε s ω
      ≤ ENNReal.ofReal lm * (ENNReal.ofReal lm⁻¹ * confSigma ξ cc D P h' p z₀ R ε (lm * s) ω) :=
        by gcongr
    _ = confSigma ξ cc D P h' p z₀ R ε (lm * s) ω := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hlm.le, mul_inv_cancel₀ hlm.ne',
          ENNReal.ofReal_one, one_mul]

end Sigma

/-! ## SCALE: the iteration for `normIn h ψ` -/

section Iter
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **SCALE** (D130B §3): a.s., for every `k`, the `k`-th radius of the iteration of CONF
Theorem 3.9 (C:1543–1556) run for `normIn h ψ = h − h(ψ)` from `e^{−ξh(ψ)} τ` is
`e^{−ξh(ψ)}` times the `k`-th radius for `h` from `τ` -/
theorem t39k6_iter_normIn {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (p : CONFParams) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (ψ : TestC) (z₀ : ℂ) {R : ℝ} (hR : 0 < R) {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ)
    (τ : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ k, t39j7S γ D c p P (normIn h ψ) z₀ R I₀
        (fun ω => Real.exp (-(xiGamma γ * h ω ψ)) * τ ω) k ω =
      Real.exp (-(xiGamma γ * h ω ψ)) * t39j7S γ D c p P h z₀ R I₀ τ k ω := by
  filter_upwards [hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hh),
    t39k6_confRK_normIn_ae hD p hh ψ hR] with ω hW hRK
  have hlm : 0 < Real.exp (-(xiGamma γ * h ω ψ)) := Real.exp_pos _
  have hd : ∀ u v, (D (normIn h ψ ω)).1 (u, v) =
      Real.exp (-(xiGamma γ * h ω ψ)) * (D (h ω)).1 (u, v) := fun u v => by
    show (D (addConst (h ω) (-(h ω ψ)))).1 (u, v) = _
    rw [hW, mul_neg]
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hN : t39j7N D (normIn h ψ) z₀ I₀ (t39j7S γ D c p P (normIn h ψ) z₀ R I₀
        (fun ω => Real.exp (-(xiGamma γ * h ω ψ)) * τ ω) k) ω =
        t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω := by
      classical
      unfold t39j7N; rw [ih]
      exact congrArg Finset.card (Finset.filter_congr fun i _ => by rw [t39k6_gArc_smul hlm hd])
    simp only [t39j7S]
    rw [hN, ih, t39k6_confSigma_smul hlm hd (hRK _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hlm.le]

end Iter

/-! ## TRANSFER and AE-CONGR -/

section Transfer
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- `σ(B, h|_B)` modulo constants does not see the normalization -/
theorem t39k6_localSigma0_normIn (h : Ω → DistC) (ψ : TestC) (B : Ω → Set ℂ) :
    localSigma0 (normIn h ψ) B = localSigma0 h B := by
  unfold localSigma0 hullSigma0
  rw [show fieldSigma0On (normIn h ψ) = fieldSigma0On h from funext (fieldSigma0On_normIn h ψ)]

/-- **TRANSFER**: locality modulo constants passes to `normIn h ψ` and to a.s. equal sets -/
theorem t39k6_isLocalSetDet0_normIn_of_ae_eq {h : Ω → DistC} (ψ : TestC) {A A' : Ω → Set ℂ}
    (hA : IsLocalSetDet0 P h A) (hAA : A =ᵐ[P] A') : IsLocalSetDet0 P (normIn h ψ) A' := by
  intro U hU
  obtain ⟨F, hF, hEF⟩ := hA U hU
  refine ⟨F, by rw [fieldSigma0On_normIn]; exact hF, ?_⟩
  refine EventuallyEq.trans ?_ hEF
  filter_upwards [hAA] with ω hω
  show (A' ω ⊆ U) = (A ω ⊆ U)
  rw [hω]

/-- **AE-CONGR**: an event of `σ(B, h|_B)` mod constants is a.s. an event of `σ(B', h|_{B'})`
mod constants when `B = B'` a.s. (`t39j_inter_localSigma0_ae` with `C = Ω`) -/
theorem t39k6_aeEventIn_localSigma0_of_ae_eq (h : Ω → DistC) {B B' : Ω → Set ℂ}
    (hB' : ∀ ω, IsClosed (B' ω)) (hBB : B =ᵐ[P] B') {E : Set Ω}
    (hE : MeasurableSet[localSigma0 h B] E) : AEEventIn P (localSigma0 h B') E := by
  have := t39j_inter_localSigma0_ae P h hB' (C := univ) MeasurableSet.univ
    (by filter_upwards [hBB] with ω hω _ using hω) hE
  rwa [inter_univ] at this

end Transfer

/-! ## EVENTS→FUN -/

section Nat
variable {Ω : Type} {m m' : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {P : Measure Ω}

open Classical in
/-- **EVENTS→FUN**: an `ℕ`-valued function whose level sets are a.s. `m'`-events has an
`m'`-measurable a.s. version (`Nat.find` on the chosen versions, `measurable_find`) -/
theorem t39k6_exists_measurable_nat_of_ae (N₀ : Ω → ℕ)
    (_hN : Measurable[m] N₀) (hm : ∀ n, AEEventIn P m' {ω | N₀ ω = n}) :
    ∃ N' : Ω → ℕ, Measurable[m'] N' ∧ N₀ =ᵐ[P] N' := by
  choose F hF hEF using hm
  let p : Ω → ℕ → Prop := fun ω n => ω ∈ F n ∨ ω ∉ ⋃ k, F k
  have hp : ∀ ω, ∃ n, p ω n := fun ω => by
    by_cases hω : ω ∈ ⋃ k, F k
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hω; exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hω⟩
  refine ⟨fun ω => Nat.find (hp ω), measurable_find (mα := m') hp fun k => ?_, ?_⟩
  · exact (hF k).union (MeasurableSet.iUnion hF).compl
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ {ω | N₀ ω = n}) = (ω ∈ F n) := ae_all_iff.2 fun n => hEF n
    filter_upwards [hall] with ω hω
    have hmem : ∀ n, (N₀ ω = n) ↔ ω ∈ F n := fun n => Iff.of_eq (hω n)
    have hin : ω ∈ ⋃ k, F k := mem_iUnion.2 ⟨N₀ ω, (hmem _).1 rfl⟩
    have hpn : ∀ n, p ω n ↔ N₀ ω = n := fun n => by
      simp only [p, hin, not_true_eq_false, or_false, hmem]
    symm
    rw [Nat.find_eq_iff]
    exact ⟨(hpn _).2 rfl, fun n hn h' => hn.ne ((hpn n).1 h').symm⟩

end Nat

end CONF
end LQGMetric
