/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47InputsA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD6
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom

/-!
# GM Lemma 4.6 (c), input `hA`: `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` traced on `Stab ∩ Hit` (task P2-L47)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1701–1706 ("`(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` … is determined by
`h|_{ℂ∖B_r(z)}` on the event `{(z,r) ∈ 𝒵_k}`"). The first half (the random set `𝓑^•_{t_k}`,
`gm_trace_hitK`) is P2-E3c's; here the second half (the field on the hull), following the recipe
of `handoff/P2-E3c.md` item 2:

* `gmSigA = ⨅ n, hullSigma n ≤ hullSigma n` for one `n` with `2·2^{-n} < λ₄ε𝕣 − ρ`;
* the generators `{𝓑^{•(n)} = S} ∩ F`, `F ∈ σ(h|_{int S})`: if `int S` meets `B_ρ(z)`, the trace on
  `Stab` is empty (on `Stab`, `dist(z, 𝓑^•_{t_k}) ≥ λ₄ε𝕣`, GM (4.10)); otherwise
  `F ∈ σ(h|_{ℂ∖B_ρ(z)})` and `{𝓑^{•(n)} = S}` is a.s. an event of `σ(𝓑^•_{t_k})`
  (`LocalEvent.measurableSet_hull_eq` applied to the closure, which equals `𝓑^•_{t_k}` a.s.), whose
  generators are traced by `gm_trace_hitK`.

Needs `ρ < λ₄ε𝕣` (GM: `ρ = r ≤ ε𝕣 < λ₄ε𝕣`, `λ₄ = 4`, (4.59)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric MeasurableSpace TopologicalSpace
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

section Generic
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- the traced σ-algebra is closed under a.s. equality -/
theorem gm_traceSigma_of_ae {μ : Measure[mΩ] Ω} {M : MeasurableSpace Ω} {E : Set Ω}
    (hE : MeasurableSet[M] E) {s s' : Set Ω} (hss : s =ᵐ[μ] s')
    (h : MeasurableSet[gmTraceSigma M E hE μ] s') : MeasurableSet[gmTraceSigma M E hE μ] s := by
  obtain ⟨t, ht, h'⟩ := h
  exact ⟨t, ht, (hss.inter (EventuallyEq.refl _ E)).trans h'⟩

end Generic

/-- `σ(h|_U) ≤ σ(h|_C)` for `U ⊆ C`, `U` open -/
theorem gm_fieldSigma_le_fieldSigmaClosed {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    {U : Opens ℂ} {C : Set ℂ} (hUC : (U : Set ℂ) ⊆ C) : fieldSigma h U ≤ fieldSigmaClosed h C :=
  le_iInf₂ fun δ hδ => fieldSigma_mono h (fun x hx => self_subset_thickening hδ C (hUC hx))

/-- a point of a level-`n` dyadic square is within `2 · 2^{-n}` of every other point of it -/
theorem gm_dist_le_of_mem_dyadicSq {n : ℕ} {k : ℤ × ℤ} {x y : ℂ} (hx : x ∈ dyadicSq n k)
    (hy : y ∈ dyadicSq n k) : dist x y ≤ 2 / 2 ^ n := by
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hy
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have e1 : |x.re - y.re| ≤ 1 / 2 ^ n := by
    rw [abs_le]; constructor
    · have : (k.1 + 1 : ℝ) / 2 ^ n - k.1 / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
      linarith
    · have : (k.1 + 1 : ℝ) / 2 ^ n - k.1 / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
      linarith
  have e2 : |x.im - y.im| ≤ 1 / 2 ^ n := by
    rw [abs_le]; constructor
    · have : (k.2 + 1 : ℝ) / 2 ^ n - k.2 / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
      linarith
    · have : (k.2 + 1 : ℝ) / 2 ^ n - k.2 / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
      linarith
  calc dist x y ≤ |x.re - y.re| + |x.im - y.im| := by
        rw [Complex.dist_eq]
        simpa using Complex.norm_le_abs_re_add_abs_im (x - y)
    _ ≤ 1 / 2 ^ n + 1 / 2 ^ n := add_le_add e1 e2
    _ = 2 / 2 ^ n := by ring

variable {Ω : Type} [MeasurableSpace Ω]

/-- **GM Lemma 4.6 (c), input `hA`** (GM l. 1701–1706): every event of
`σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` traced on `E = Stab ∩ {P ∩ B_r(z) ≠ ∅}` is a.s. an event of
`σ(h|_{ℂ∖B_ρ(z)}) ∨ σ(1_E)`. -/
theorem gm_L4_6c_hA (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} {η : Ω → C(unitInterval, ℂ)}
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ < lam4 * ε * 𝕣) :
    ∀ a, MeasurableSet[gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)] a →
      ∃ t, MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔
        generateFrom {gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r}] t ∧
      a ∩ (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) =ᵐ[P] t := by
  set E := gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r with hEdef
  set K : Ω → Set ℂ := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) with hKdef
  have hE : MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}] E := le_sup_right (α := MeasurableSpace Ω) _ (measurableSet_generateFrom rfl)
  -- the level `n`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 / (2 : ℝ) ^ n < lam4 * ε * 𝕣 - ρ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (lam4 * ε * 𝕣 - ρ) / 2 by linarith)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨n, ?_⟩
    rw [div_pow, one_pow] at hn
    have : 2 / (2 : ℝ) ^ n = 2 * (1 / 2 ^ n) := by ring
    linarith
  -- (i) the `setSigma` generators
  have hset : setSigma K ≤ gmTraceSigma (fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}) E hE P := by
    refine generateFrom_le ?_
    rintro _ ⟨V, hV, rfl⟩
    exact gm_trace_hitK (𝕨 := 𝕨) (η := η) (lam1 := lam1) (ν := ν) (Rads := Rads) (r := r)
      h38 hγ hγ2 hD hh hε ha hρ.le hV
  have hsetc : setSigma (fun ω => closure (K ω)) ≤ gmTraceSigma (fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}) E hE P := by
    refine le_trans (le_of_eq ?_) hset
    unfold setSigma
    congr 1
    ext s
    simp only [mem_ofPred_eq]
    refine exists_congr fun V => and_congr_right fun hV => ?_
    have : ∀ ω, (closure (K ω) ∩ V).Nonempty ↔ (K ω ∩ V).Nonempty :=
      fun ω => closure_inter_open_nonempty_iff hV
    simp only [this]
  have hKcl : ∀ᵐ ω ∂P, closure (K ω) = K ω := by
    filter_upwards [ae_mem_lenSet h38 hγ hγ2 hD P h hh] with ω hω
    exact (jb_isClosed_filledBall ((gm_filledBall_isBounded_of_lenSet hω 𝕫 _).subset
      (fun x hx => Or.inl (subset_closure hx)))).closure_eq
  have hhull : ∀ S : Set ℂ, MeasurableSet[gmTraceSigma (fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}) E hE P] {ω | dyadicHull n (K ω) = S} := by
    intro S
    refine gm_traceSigma_of_ae hE (s' := {ω | dyadicHull n (closure (K ω)) = S}) ?_
      (hsetc _ (measurableSet_hull_eq (fun ω => isClosed_closure) n S))
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hKcl] with ω hω
    simp only [hω]
  -- (ii) the field generators
  have hfield : hullSigma h K n ≤ gmTraceSigma (fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}) E hE P := by
    refine sup_le hset (generateFrom_le ?_)
    rintro _ ⟨S, F, hF, rfl⟩
    by_cases hS : interior S ⊆ (Metric.ball z ρ)ᶜ
    · have hFM : MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}] F :=
        le_sup_left (α := MeasurableSpace Ω) _
          (gm_fieldSigma_le_fieldSigmaClosed h (U := toOpens (interior S) isOpen_interior) hS F hF)
      have hFt : MeasurableSet[gmTraceSigma (fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}) E hE P] F :=
        ⟨F ∩ E, hFM.inter hE, EventuallyEq.rfl⟩
      exact (hhull S).inter hFt
    · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔ generateFrom {E}), ?_⟩
      refine Eventually.of_forall (fun ω => ?_)
      simp only [Set.empty_def]
      refine propext ⟨fun hω => ?_, fun hω => hω.elim⟩
      obtain ⟨⟨hhω, -⟩, hSt, -⟩ := hω
      obtain ⟨y, hyS, hyB⟩ := not_subset.1 hS
      simp only [mem_compl_iff, not_not] at hyB
      have hyH : y ∈ dyadicHull n (K ω) := by
        rw [show dyadicHull n (K ω) = S from hhω]; exact interior_subset hyS
      simp only [dyadicHull, mem_iUnion] at hyH
      obtain ⟨q, ⟨x, hxq, hxK⟩, hyq⟩ := hyH
      obtain ⟨hcand, -⟩ := hSt
      obtain ⟨-, hzK, -, hdist⟩ := hcand
      have h1 := gm_infDist_frontier_le_dist hzK hxK
      have h2 := gm_dist_le_of_mem_dyadicSq hyq hxq
      have h3 := dist_triangle z y x
      rw [mem_ball, dist_comm] at hyB
      have h4 := hdist.1
      linarith
  intro a ha
  exact hfield a (iInf_le (fun m => hullSigma h K m) n a ha)

end LQGMetric.GM
