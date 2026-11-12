/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iPiece at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iBorel
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic

/-!
# Piece method with field events: `{σ_k ≤ s_{k+1}}` is piecewise local for `𝓑^•_{t_{k+1}}`

Source: CONF (arXiv:1905.00381, `confluence-final.tex`) l. 1258–1260 and 1300–1302 ("Since
`E_r(z)` is determined by `h|_{A_{2r,5r}(z)}`, … `ρ^n_𝕣(z)` is a stopping time …; if `τ` is a
stopping time … then so is `σ^ε_{τ,𝕣}`"), used in GM (arXiv:1905.00383v3) L4.15 Step 4, l. 2189
(D98 (b2), packet P-stop).

* `p412i_piece_aug`: `exists_fieldSigma_piece` (LocalEventRandom2) with the saturation relation
  enlarged by a measurable function `e` of `h|_U` (same proof, `R` and `V` get a second
  coordinate);
* `p412i_sig_congr_grid`: `σ` only queries `E_r(z)` at `r = 2^k ε𝕣`, `z ∈ (ε𝕣/4)ℤ²`;
* `P412iEDet`: CONF l. 1260 in the form used here: `E_r(z)` is a.s. an event of `σ(h|_V)` for every
  open `V ⊇ cl B_{5r}(z)` (CONF write `h|_{A_{2r,5r}(z)}`; with the circle average `h_r(z)` in
  condition 1 the ball `B_{5r}(z)` is needed, as in CONF's own stopping-time claim l. 1260);
* **`p412i_sig_piece`**: for a predicate `Θ(d, τ, σ)` forcing `σ ≤ τ c_s` and stable under
  agreement of the filled balls up to `τ c_T`, and Borel in (metric, coded events), the event
  `{Θ(D_h, τ_R, σ)}` is piecewise local for `𝓑^•_{τ_R c_T}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- **piece method with an extra field coordinate** (copy of `exists_fieldSigma_piece` with the
saturation relation enlarged by `e(h|_U)`) -/
theorem p412i_piece_aug {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hgp : IsGFFPlusCont h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) {U : Set ℂ} (hUo : IsOpen U) (hU : U.Nonempty)
    {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [OpensMeasurableSpace Γ]
    [SecondCountableTopology Γ] {e : DistOn (toOpens U hUo) → Γ} (he : Measurable e)
    {Bs : Set DistC} (hnull : NullMeasurableSet Bs (P.map h))
    (hsat : ∀ g₁ g₂, D g₁ ∈ lenSet → D g₂ ∈ lenSet → (D g₁).internal U = (D g₂).internal U →
      e (restrictTo _ g₁) = e (restrictTo _ g₂) → g₁ ∈ Bs → g₂ ∈ Bs) :
    ∃ F, MeasurableSet[fieldSigma h (toOpens U hUo)] F ∧ h ⁻¹' Bs =ᵐ[P] F := by
  classical
  have hhm : Measurable h := hgp.1
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp (toOpens U hUo)
  have : Nonempty U := hU.to_subtype
  set q : ℕ → ℂ := fun n => (TopologicalSpace.denseSeq U n : ℂ) with hq
  have hqU : ∀ n, q n ∈ U := fun n => (TopologicalSpace.denseSeq U n).2
  have hqd : U ⊆ closure (range q) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq U).exists_mem_open
      (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
    exact ⟨q n, hn, n, rfl⟩
  let R : DistC → (ℕ × ℕ → ℝ≥0∞) × Γ :=
    fun g => (fun p => (D g).chainInf U (q p.1) (q p.2), e (restrictTo _ g))
  let G : DistOn (toOpens U hUo) → (ℕ × ℕ → ℝ≥0∞) × Γ :=
    fun x => (fun p => Φ x (q p.1) (q p.2), e x)
  have hR : Measurable R := (measurable_pi_iff.2 fun p =>
    GM.measurable_chainInf_comp hD.measurable measurable_const measurable_const _).prodMk
      (he.comp (measurable_restrictTo _))
  have hG : Measurable G := (measurable_pi_iff.2 fun p =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)).prodMk he
  have hV : Measurable[fieldSigma h (toOpens U hUo)] fun ω => G (restrictTo _ (h ω)) :=
    hG.comp (Measurable.of_comap_le le_rfl)
  have hVR : ∀ᵐ ω ∂P, G (restrictTo (toOpens U hUo) (h ω)) = R (h ω) := by
    filter_upwards [hΦae, hlen] with ω h1 h3
    refine Prod.ext ?_ rfl
    funext p
    show Φ _ (q p.1) (q p.2) = (D (h ω)).chainInf U (q p.1) (q p.2)
    rw [← h1 _ (hqU _) _ (hqU _)]
    exact (D (h ω)).internal_eq_chainInf (isLength_of_mem_lenSet h3) hUo _ _
  have hW : MeasurableSet (D ⁻¹' lenSet) := measurableSet_lenSet.preimage hD.measurable
  have hs : ∀ g₁ ∈ D ⁻¹' lenSet, ∀ g₂ ∈ D ⁻¹' lenSet, R g₁ = R g₂ → g₁ ∈ Bs → g₂ ∈ Bs := by
    intro g₁ h1 g₂ h2 he' hB
    have l1 := isLength_of_mem_lenSet h1
    have l2 := isLength_of_mem_lenSet h2
    refine hsat g₁ g₂ h1 h2 ?_ (congrArg Prod.snd he') hB
    refine GM.internal_eq_of_dense l1 l2 hUo hqU hqd fun i j => ?_
    rw [(D g₁).internal_eq_chainInf l1 hUo, (D g₂).internal_eq_chainInf l2 hUo]
    exact congrFun (congrArg Prod.fst he') (i, j)
  exact aeEventIn_of_saturated hhm hR hV hVR hW hnull hlen hs

/-- `σ` only queries the events at `r = 2^k ε𝕣`, `z ∈ (ε𝕣/4)ℤ²` -/
theorem p412i_sig_congr_grid {d : ContMetric} {z₀ : ℂ} {N : ℕ} {R ε t : ℝ}
    {E₁ E₂ : ℝ → ℂ → Prop}
    (hE : ∀ k a b : ℤ, E₁ ((2 : ℝ) ^ k * (ε * R)) (p412iGP (ε * R / 4) a b) ↔
      E₂ ((2 : ℝ) ^ k * (ε * R)) (p412iGP (ε * R / 4) a b)) :
    p412iSig d z₀ E₁ N R ε t = p412iSig d z₀ E₂ N R ε t := by
  have hρ : ∀ (a b : ℤ) (n : ℕ), p412iRho E₁ (ε * R) (p412iGP (ε * R / 4) a b) n =
      p412iRho E₂ (ε * R) (p412iGP (ε * R / 4) a b) n := by
    intro a b n
    induction n with
    | zero => rfl
    | succ n ih => simp only [p412iRho, ih, hE]
  have hRK : ∀ K, p412iRK E₁ N R ε K = p412iRK E₂ N R ε K := by
    intro K
    unfold p412iRK
    congr 2
    refine iSup_congr fun z => iSup_congr fun hz => ?_
    obtain ⟨⟨a, b, rfl⟩, -⟩ := hz
    exact hρ a b N
  unfold p412iSig
  simp only [hRK]

/-- **CONF l. 1260 (form used here)**: `E_r(z)` is a.s. an event of `σ(h|_V)` for every open
`V ⊇ cl B_{5r}(z)` -/
def P412iEDet {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric)
    (P : Measure Ω) (h : Ω → DistC) (p : CONFParams) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ (z : ℂ) (V : Set ℂ) (hV : IsOpen V), closedBall z (5 * r) ⊆ V →
    AEEventIn P (fieldSigma h (toOpens V hV)) (confE ξ cc D P h p r z)

theorem p412i_isBounded_hullFin (n : ℕ) (s : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (hullFin n s) :=
  (Bornology.isBounded_biUnion_finset s).2 fun k _ => (gmE_isCompact_dyadicSq n k).isBounded

end LQGMetric.GM
