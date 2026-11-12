/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J9
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K0
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J2
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2

/-!
# CONF Theorem 3.9, packet J6d (D130 §4): locality of the arcs `I^{(s_k)}`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1543, 1556, 1559–1561 ("`𝓘_k` is determined by `(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`"); decision D130
§4 "Fields 4–6".

* `t39k5_leftmost_transfer`, **`t39k5_gArc_eq`**: the deterministic content of C:1559–1561 — if
  two metrics agree near `𝓑^•_T` (`GM.GMAgree`: internal metrics on an open `U ⊇ 𝓑^•_T`, balls up
  to `T`), then their leftmost geodesics (D-D1, `DD.IsLeftmostGeod`) from `z₀` of length `t ≤ T`
  and the arcs `t39gArc … t I` coincide (geodesics transfer by `GM.gm_geodL_transfer`, the order
  `WeaklyRightOf` only sees the filled balls `𝓑^•_u`, `u < t`);
* **`t39k5_hnm_of_hit`**: field 4 (`hnm`) of `T39J6Rest` at a radius `s` from the a.s.
  `𝓕_s`-locality of the events `{I^{(s)}_i ≠ ∅}` (`n_s` is a function of the indicator vector).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Blueprint GM

/-! ## Deterministic locality of leftmost geodesics and arcs (C:1559–1561) -/

/-! ## Field 4 (`hnm`) from the locality of the nonemptiness events -/

section Card
variable {Ω : Type} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {P : Measure Ω}

open Classical in
/-- the number of nonempty random sets is a.s. `m`-measurable when each nonemptiness event is
a.s. an `m`-event -/
theorem t39k5_card_ae_meas {ι : Type} [Fintype ι] (J : ι → Ω → Set ℂ)
    (hJ : ∀ i, AEEventIn P m {ω | (J i ω).Nonempty}) :
    ∃ g : Ω → ℕ, Measurable[m] g ∧
      (fun ω => (Finset.univ.filter fun i => (J i ω).Nonempty).card) =ᵐ[P] g := by
  choose F hF hJF using hJ
  let v : Ω → ι → Bool := fun ω i => decide (ω ∈ F i)
  have hv : Measurable[m] v := by
    refine @measurable_pi_iff Ω ι (fun _ => Bool) m _ v |>.2 fun i => ?_
    refine @measurable_to_bool Ω m _ ?_
    convert hF i using 1; ext ω; simp [v]
  refine ⟨fun ω => (Finset.univ.filter fun i => v ω i = true).card,
    (measurable_of_countable (fun w : ι → Bool =>
      (Finset.univ.filter fun i => w i = true).card)).comp hv, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, (ω ∈ {ω | (J i ω).Nonempty}) = (ω ∈ F i) :=
    ae_all_iff.2 fun i => hJF i
  filter_upwards [hall] with ω hω
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only [v, decide_eq_true_eq]
  exact Iff.of_eq (hω i)

end Card

variable {Ω : Type} [m0 : MeasurableSpace Ω]

/-- **field 4 (`hnm`) of `T39J6Rest` at one radius `s`**: `n_s = t39j7N … s` is a.s. equal to
an `𝓕_s`-measurable function, given that each event `{I^{(s)}_i ≠ ∅}` is a.s. an `𝓕_s`-event -/
theorem t39k5_hnm_of_hit {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {z₀ : ℂ}
    {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ) (s : Ω → ℝ)
    (hhit : ∀ i, AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s ω)))
      {ω | (t39gArc (D (h ω)) z₀ (s ω) (I₀ i ω)).Nonempty}) :
    ∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s ω))] g ∧
      (fun ω => t39j7N D h z₀ I₀ s ω) =ᵐ[P] g :=
  t39k5_card_ae_meas (fun i ω => t39gArc (D (h ω)) z₀ (s ω) (I₀ i ω)) hhit

/-! ## Hit patterns: the Effros σ-algebra is countably generated -/

open Classical in
/-- the hit pattern of `Γ` on the open balls `B(c_j, 2r_j)` (rational centres, `r_j = 1/(n+1)`) -/
def t39k5Pat (Γ : Set ℂ) : ℕ → Bool :=
  fun j => decide ((Γ ∩ ball (t39jBc j) (2 * t39jBr j)).Nonempty)

/-- every point of an open set lies in a ball `B(c_j, 2r_j)` inside it -/
theorem t39k5_ball_basis {U : Set ℂ} (hU : IsOpen U) {y : ℂ} (hy : y ∈ U) :
    ∃ j, y ∈ ball (t39jBc j) (2 * t39jBr j) ∧ ball (t39jBc j) (2 * t39jBr j) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
  obtain ⟨j, hyj, hjε⟩ := t39j_ball_basis y (show 0 < ε / 3 by positivity)
  have hr := t39jBr_pos j
  have hyc : dist y (t39jBc j) ≤ t39jBr j := hyj
  have h1 : dist (t39jBc j + (t39jBr j : ℂ)) y < ε / 3 :=
    hjε (show dist (t39jBc j + (t39jBr j : ℂ)) (t39jBc j) ≤ t39jBr j by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr])
  have h2 : dist (t39jBc j - (t39jBr j : ℂ)) y < ε / 3 :=
    hjε (show dist (t39jBc j - (t39jBr j : ℂ)) (t39jBc j) ≤ t39jBr j by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr])
  have h3 : dist (t39jBc j + (t39jBr j : ℂ)) (t39jBc j - (t39jBr j : ℂ)) = 2 * t39jBr j := by
    rw [dist_eq_norm, show t39jBc j + (t39jBr j : ℂ) - (t39jBc j - (t39jBr j : ℂ)) =
      ((2 * t39jBr j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hrε : 2 * t39jBr j < 2 * (ε / 3) := by
    have := dist_triangle_right (t39jBc j + (t39jBr j : ℂ)) (t39jBc j - (t39jBr j : ℂ)) y
    linarith
  refine ⟨j, by rw [mem_ball]; linarith, fun w hw => hεU ?_⟩
  rw [mem_ball] at hw ⊢
  linarith [dist_triangle w (t39jBc j) y, dist_comm y (t39jBc j)]

/-- hit events of open sets are unions of hit events of the pattern balls -/
theorem t39k5_hit_eq_iUnion {U : Set ℂ} (hU : IsOpen U) :
    {Γ : Set ℂ | (Γ ∩ U).Nonempty} =
      ⋃ j ∈ {j | ball (t39jBc j) (2 * t39jBr j) ⊆ U}, {Γ | t39k5Pat Γ j = true} := by
  ext Γ
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop, t39k5Pat, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hyΓ, hyU⟩
    obtain ⟨j, hyj, hjU⟩ := t39k5_ball_basis hU hyU
    exact ⟨j, hjU, y, hyΓ, hyj⟩
  · rintro ⟨j, hjU, y, hyΓ, hyj⟩
    exact ⟨y, hyΓ, hjU hyj⟩

/-- **the Effros σ-algebra is the pull-back of the hit pattern** -/
theorem t39k5_effros_eq_comap :
    effrosSigma = MeasurableSpace.comap t39k5Pat MeasurableSpace.pi := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨U, hU, rfl⟩
    rw [t39k5_hit_eq_iUnion hU]
    refine MeasurableSet.biUnion (to_countable _) fun j _ => ?_
    refine ⟨(fun w : ℕ → Bool => w j) ⁻¹' {true},
      (measurable_pi_apply j) (measurableSet_singleton true), ?_⟩
    ext Γ; simp
  · refine MeasurableSpace.comap_le_iff_le_map.2 (iSup_le fun j => ?_)
    refine (MeasurableSpace.comap_le_iff_le_map.2 ?_)
    intro B _
    show MeasurableSet[effrosSigma] ((fun Γ => t39k5Pat Γ j) ⁻¹' B)
    have hT : MeasurableSet[effrosSigma] {Γ | t39k5Pat Γ j = true} := by
      simp only [t39k5Pat, decide_eq_true_eq]
      exact t39j_hit_open isOpen_ball
    have : (fun Γ => t39k5Pat Γ j) ⁻¹' B = ⋃ b ∈ B, {Γ | t39k5Pat Γ j = b} := by
      ext Γ; simp
    rw [this]
    refine MeasurableSet.biUnion (to_countable _) fun b _ => ?_
    cases b
    · convert hT.compl using 1; ext Γ; simp
    · exact hT

section Version
variable {Ω : Type} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {P : Measure Ω}

open Classical in
/-- a random set whose hit events are a.s. `m`-events has an `m`-measurable hit pattern, a.s.
(`LocalEvent.exists_measurable_code`) -/
theorem t39k5_pat_version (J : Ω → Set ℂ)
    (hJ : ∀ U : Set ℂ, IsOpen U → AEEventIn P m {ω | (J ω ∩ U).Nonempty}) :
    ∃ v : Ω → ℕ → Bool, Measurable[m] v ∧ ∀ᵐ ω ∂P, t39k5Pat (J ω) = v ω := by
  have hJ' : ∀ j, AEEventIn P m {ω | t39k5Pat (J ω) j = true} := fun j => by
    simpa [t39k5Pat] using hJ _ (isOpen_ball (x := t39jBc j) (ε := 2 * t39jBr j))
  obtain ⟨v, hv, hvE⟩ := LocalEvent.exists_measurable_code hJ'
  refine ⟨v, hv, ?_⟩
  filter_upwards [hvE] with ω hω
  funext j
  exact Bool.eq_iff_iff.2 (hω j).symm

/-- the product of two Effros σ-algebras is the pull-back of the pair of hit patterns -/
theorem t39k5_effros_prod_eq :
    (@Prod.instMeasurableSpace (Set ℂ) (Set ℂ) effrosSigma effrosSigma) =
      MeasurableSpace.comap (Prod.map t39k5Pat t39k5Pat) inferInstance := by
  rw [t39k5_effros_eq_comap]
  show (MeasurableSpace.comap t39k5Pat _).comap Prod.fst ⊔
      (MeasurableSpace.comap t39k5Pat _).comap Prod.snd = _
  rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  show _ = (MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd _).comap _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

/-- **composition**: an Effros-measurable functional `Φ q (K, J)` of two random sets whose hit
events are a.s. `m`-events, at an a.s. `m`-measurable index `q = n ω`, is a.s. `m`-measurable -/
theorem t39k5_comp_ae {β : Type} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    (Φ : ℕ → Set ℂ × Set ℂ → β)
    (hΦ : ∀ q, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Φ q))
    (K J : Ω → Set ℂ) (n : Ω → ℕ)
    (hK : ∀ U : Set ℂ, IsOpen U → AEEventIn P m {ω | (K ω ∩ U).Nonempty})
    (hJ : ∀ U : Set ℂ, IsOpen U → AEEventIn P m {ω | (J ω ∩ U).Nonempty})
    (hn : ∃ g : Ω → ℕ, Measurable[m] g ∧ n =ᵐ[P] g) :
    ∃ G : Ω → β, Measurable[m] G ∧ (fun ω => Φ (n ω) (K ω, J ω)) =ᵐ[P] G := by
  have hφ : ∀ q, ∃ φ : (ℕ → Bool) × (ℕ → Bool) → β, Measurable φ ∧
      Φ q = φ ∘ Prod.map t39k5Pat t39k5Pat := fun q => by
    have := hΦ q
    rw [t39k5_effros_prod_eq] at this
    exact this.exists_eq_measurable_comp
  choose φ hφm hφe using hφ
  obtain ⟨vK, hvK, hKv⟩ := t39k5_pat_version K hK
  obtain ⟨vJ, hvJ, hJv⟩ := t39k5_pat_version J hJ
  obtain ⟨g, hg, hng⟩ := hn
  have hF : Measurable fun p : ((ℕ → Bool) × (ℕ → Bool)) × ℕ => φ p.2 p.1 :=
    measurable_from_prod_countable_left fun q => hφm q
  refine ⟨fun ω => φ (g ω) (vK ω, vJ ω), ?_, ?_⟩
  · exact hF.comp (Measurable.prodMk (m := m)
      (Measurable.prodMk (m := m) hvK hvJ) hg)
  · filter_upwards [hKv, hJv, hng] with ω h1 h2 h3
    simp only [h3, hφe, Function.comp_apply, Prod.map_apply, h1, h2]

/-- **composition, events**: `{(K, J) ∈ A_{n ω}}` is a.s. an `m`-event for Effros-measurable
`A q` -/
theorem t39k5_comp_aeEventIn (A : ℕ → Set (Set ℂ × Set ℂ))
    (hA : ∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q))
    (K J : Ω → Set ℂ) (n : Ω → ℕ)
    (hK : ∀ U : Set ℂ, IsOpen U → AEEventIn P m {ω | (K ω ∩ U).Nonempty})
    (hJ : ∀ U : Set ℂ, IsOpen U → AEEventIn P m {ω | (J ω ∩ U).Nonempty})
    (hn : ∃ g : Ω → ℕ, Measurable[m] g ∧ n =ᵐ[P] g) :
    AEEventIn P m {ω | (K ω, J ω) ∈ A (n ω)} := by
  have hB : ∀ q, ∃ B : Set ((ℕ → Bool) × (ℕ → Bool)), MeasurableSet B ∧
      Prod.map t39k5Pat t39k5Pat ⁻¹' B = A q := fun q => by
    have := hA q
    rw [t39k5_effros_prod_eq] at this
    exact this
  choose B hBm hBe using hB
  obtain ⟨vK, hvK, hKv⟩ := t39k5_pat_version K hK
  obtain ⟨vJ, hvJ, hJv⟩ := t39k5_pat_version J hJ
  obtain ⟨g, hg, hng⟩ := hn
  have hv : Measurable[m] fun ω => (vK ω, vJ ω) := Measurable.prodMk (m := m) hvK hvJ
  refine ⟨⋃ q : ℕ, {ω | g ω = q} ∩ (fun ω => (vK ω, vJ ω)) ⁻¹' B q, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun q =>
      (hg (measurableSet_singleton q)).inter (hv (hBm q))
  · filter_upwards [hKv, hJv, hng] with ω h1 h2 h3
    apply propext
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, exists_eq_left', h3]
    rw [← hBe (g ω)]
    simp [h1, h2]

end Version

/-! ## Fields 4–6 of `T39J6Rest` at step `k` -/

section Fields
variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω}

/-- hit events of the filled ball `𝓑^•_s` are (surely) events of `filledBallSigmaAt0` at `s ≥ 0` -/
theorem t39k5_fb_hit (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {s : Ω → ℝ}
    (hs : ∀ ω, 0 ≤ s ω) {U : Set ℂ} (hU : IsOpen U) :
    AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s ω)))
      {ω | (filledBall (D (h ω)) z₀ (s ω) ∩ U).Nonempty} := by
  refine ⟨_, ?_, Filter.EventuallyEq.rfl⟩
  rw [t39h_fbs0_eq D h z₀ hs]
  exact (le_iInf fun _ => le_sup_left :
    setSigma (fun ω => filledBall (D (h ω)) z₀ (s ω)) ≤
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s ω))) _
    (MeasurableSpace.measurableSet_generateFrom ⟨U, hU, rfl⟩)

end Fields

end CONF
end LQGMetric
