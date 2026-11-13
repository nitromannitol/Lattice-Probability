/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBMain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBFamily
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBChain

/-!
# [18] Lemma 3.11 (3.35) at every real mesh `ε ∈ (0, 1)`

Source: [18] Lemma 3.11, for each `ε ∈ (0, 1)`. T15A proved (3.35) at the dyadic meshes `2⁻ᵏ` (`T15A.lemma311Bad_of_coupling_all`).
Here it is proved at every real mesh, for the embedded mated-CRT map of every frozen coupling, every `ρ ∈ (0, 1)`,
with graph disconnection and constants independent of `ε`, given [18] Proposition 4.10 at real meshes (`EpsAProp410At`, here `Prop410Real`).

**The good event.** `Lemma311GoodReal bm η ε ρ β p` (on the bundle's own sample space, for its own Brownian pair `bm`
and curve `η`): the mesh-`ε` mated-CRT map `MatedCRT.graph ε (bm ω)` is locally finite, the cells
`η([ε(x−1), εx])` form a cellular embedding of it, and (3.35) (`T15A.Lemma311Holds`) holds at mesh `ε`.

**Route (where dyadic-ness was used, and how it is removed).**
1. The landed machinery is dyadic only through its *nominal scale*: a `CellFamily.RandomCellFamily` member `k` is
   measured against `2⁻ᵏ` (cell bound `2^{−kq}`, radius floors `2^{−kβ}`, grid `2^{−kχ}ℤ²`, rates `2^{−kα}`, the
   `4k` scale representatives of the scale-grid argument, coarse meshes `k < K` absorbed into constants). Nothing uses that the
   member's actual mesh *is* `2⁻ᵏ` except the inputs, which are re-proved at real meshes.
2. For a band sequence `θₖ ∈ (2⁻ᵏ⁻¹, 2⁻ᵏ]`, the band family (`EpsBFamily`) has the mesh-`θₖ` map as member `k`; its
   inputs hold at the nominal scale (Lemma 2.7: `θₖ^q ≤ 2^{−kq}`; Proposition 2.10: admissibility at `2⁻ᵏ` implies
   admissibility at `θₖ`; PeanosphereG0: time change). The assembly (`EpsBChain`) gives (3.35) at nominal scale
   `2⁻ᵏ`; since `2^{−kβ} ≤ θₖ^{β/2}` (`k ≥ 1`) and `2^{−kα} ≤ 2^α θₖ^α`, it holds at the actual mesh `θₖ` with
   exponent `β/2` (`lemma311_bandSeq`).
3. The constants could depend on `θ`; the diagonal argument `uniform_rate_of_bandSeq` (`EpsBDiagonal`) makes them
   uniform over all real `ε ∈ (0, 1)` (`lemma311Real_of_prop410`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-- **[18] Lemma 3.11's environment event at the real mesh `ε`** for a Brownian pair `bm` and a curve `η`: the
mesh-`ε` mated-CRT map is locally finite, the cells `η([ε(x−1), εx])` form a cellular embedding `H` of it, and (3.35)
holds on `H` (`T15A.Lemma311Holds H ε ρ β p`: for every `z`, `r ∈ [ε^β, ρ]` with `B_{2r}(z) ⊂ B_ρ(0)` and every
`x ∈ V(B_r(z))`, the walk graph-disconnects `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` before hitting the latter with
quenched probability `≥ p`). -/
def Lemma311GoodReal {Ω : Type*} (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε ρ β p : ℝ) : Set Ω :=
  {ω | ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), ∃ H : CellularEmbedding (MatedCRT.graph ε (bm ω) h) 0,
    (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧ T15A.Lemma311Holds H ε ρ β p}

theorem lemma311GoodReal_mono {Ω : Type*} {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ε ρ β p β' p' : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hβ : β' ≤ β) (hp : p' ≤ p) :
    Lemma311GoodReal bm η ε ρ β p ⊆ Lemma311GoodReal bm η ε ρ β' p' := by
  rintro ω ⟨h, H, hcell, h311⟩
  exact ⟨h, H, hcell, T15A.Lemma311Holds.mono h311 hε0 hε1 le_rfl hβ hp⟩
/-- **[18] Lemma 3.11 at every real mesh** (the real-mesh analogue of T15A's `Lemma311Bad`): there are
`α, β, p > 0` and `C` with `P[(3.35) fails at mesh ε] ≤ C ε^α` for every `ε ∈ (0, 1)` (outer measure). -/
def Lemma311BadReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bm : Ω → MatedCRT.Path2)
    (η : Ω → C(ℝ, ℂ)) (ρ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
    ∀ ε ∈ Ioo (0 : ℝ) 1, P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ ENNReal.ofReal (C * ε ^ α)


/-- (3.35) is a statement about radii `r ≥ ε^β` only: it transfers between meshes whose floors compare. -/
theorem lemma311Holds_of_floor_le {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}
    {m ε ρ β β' p : ℝ} (h : T15A.Lemma311Holds H m ρ β p) (hle : m ^ β ≤ ε ^ β') :
    T15A.Lemma311Holds H ε ρ β' p := fun z r hr hrρ hball x hx =>
  h z r (hle.trans hr) hrρ hball x hx

/-- **The floor comparison along a band sequence**: for `k ≥ 1`, `(2⁻ᵏ)^β ≤ θₖ^{β/2}`. -/
theorem mesh_rpow_le_band_rpow_half {θ : ℕ → ℝ} (hθ : IsBandSeq θ) {k : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ : 0 ≤ β) :
    CellFamily.mesh k ^ β ≤ θ k ^ (β / 2) := by
  have hm := mesh_pos k
  have hmhalf : CellFamily.mesh k ≤ 1 / 2 := by
    have h1 := mesh_antitone hk
    rw [mesh_succ, mesh_zero] at h1
    simpa using h1
  have hsplit : CellFamily.mesh k ^ β = CellFamily.mesh k ^ (β / 2) * CellFamily.mesh k ^ (β / 2) := by
    rw [← Real.rpow_add hm, add_halves]
  have h1 : CellFamily.mesh k ^ (β / 2) ≤ (1 / 2 : ℝ) ^ (β / 2) := Real.rpow_le_rpow hm.le hmhalf (by linarith)
  have h2 : (1 / 2 : ℝ) ^ (β / 2) * CellFamily.mesh k ^ (β / 2) ≤ θ k ^ (β / 2) := by
    rw [← Real.mul_rpow (by norm_num) hm.le]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have := (hθ k).1
    rw [mesh_succ] at this
    linarith
  calc CellFamily.mesh k ^ β = CellFamily.mesh k ^ (β / 2) * CellFamily.mesh k ^ (β / 2) := hsplit
    _ ≤ (1 / 2 : ℝ) ^ (β / 2) * CellFamily.mesh k ^ (β / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hm.le _)
    _ ≤ θ k ^ (β / 2) := h2

/-- **The rate comparison along a band sequence**: `(2⁻ᵏ)^α ≤ 2^α θₖ^α`. -/
theorem mesh_rpow_le_two_rpow_mul {θ : ℕ → ℝ} (hθ : IsBandSeq θ) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    CellFamily.mesh k ^ α ≤ 2 ^ α * θ k ^ α := by
  rw [← Real.mul_rpow (by norm_num) (hθ.pos k).le]
  exact Real.rpow_le_rpow (mesh_pos k).le (hθ.mesh_le_two_mul k) hα

/-- A polynomial bound at nominal scale `2⁻ᵏ` gives one at the actual band mesh `θₖ` for every `k` (the band
`k = 0`, where `θ₀ > 1/2`, is absorbed into the constant). -/
theorem ofReal_mesh_le_band {θ : ℕ → ℝ} (hθ : IsBandSeq θ) {α C : ℝ} (hα : 0 ≤ α) (k : ℕ) {b : ℝ≥0∞}
    (hb1 : b ≤ 1) (hk : 1 ≤ k → b ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α)) :
    b ≤ ENNReal.ofReal ((max C 0 * 2 ^ α + 2 ^ α) * θ k ^ α) := by
  have hθ0 := hθ.pos k
  have h2α : 0 < (2 : ℝ) ^ α := by positivity
  have hθα : 0 ≤ θ k ^ α := Real.rpow_nonneg hθ0.le _
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- `θ₀ > 1/2`: the bound exceeds one
    refine hb1.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hhalf : (1 / 2 : ℝ) < θ 0 := by
      have := (hθ 0).1
      rw [mesh_succ, mesh_zero] at this
      linarith
    have hpow : (1 / 2 : ℝ) ^ α ≤ θ 0 ^ α := Real.rpow_le_rpow (by norm_num) hhalf.le hα
    have hprod : (2 : ℝ) ^ α * (1 / 2 : ℝ) ^ α = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    have hC0 : 0 ≤ max C 0 * 2 ^ α * θ 0 ^ α := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow h2α.le]
  · refine (hk hk1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hmesh := mesh_rpow_le_two_rpow_mul hθ k hα
    calc C * CellFamily.mesh k ^ α ≤ max C 0 * CellFamily.mesh k ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (mesh_pos k).le _)
      _ ≤ max C 0 * (2 ^ α * θ k ^ α) := mul_le_mul_of_nonneg_left hmesh (le_max_right _ _)
      _ ≤ (max C 0 * 2 ^ α + 2 ^ α) * θ k ^ α := by nlinarith [le_max_right C 0]

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- An outer-measure bound on the band family transfers to the bundle space: `P (val '' A) = P_θ A` and the
complement of the good subspace is null. -/
theorem measure_le_of_bandFamily (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {θ : ℕ → ℝ} (hθ : ∀ k, 0 < θ k) (S : Set Ω) (A : Set (BandSpace D θ hθ))
    (hsub : ∀ ω : BandSpace D θ hθ, ω.1 ∈ S → ω ∈ A) : P S ≤ (bandFamily D θ hθ).P A := by
  have hS := (bandGoodSetData D θ hθ).property
  have hemb : MeasurableEmbedding (Subtype.val : BandSpace D θ hθ → Ω) := MeasurableEmbedding.subtype_coe hS.1
  have hnull : P (bandGoodSetData D θ hθ).valᶜ = 0 := by
    have h := ae_iff.mp hS.2.2
    simpa [Set.compl_def] using h
  have hcover : S ⊆ (Subtype.val '' A) ∪ (bandGoodSetData D θ hθ).valᶜ := by
    intro ω hω
    by_cases hmem : ω ∈ (bandGoodSetData D θ hθ).val
    · exact Or.inl ⟨⟨ω, hmem⟩, hsub ⟨ω, hmem⟩ hω, rfl⟩
    · exact Or.inr hmem
  calc P S ≤ P ((Subtype.val '' A) ∪ (bandGoodSetData D θ hθ).valᶜ) := measure_mono hcover
    _ ≤ P (Subtype.val '' A) + P (bandGoodSetData D θ hθ).valᶜ := measure_union_le _ _
    _ = (bandFamily D θ hθ).P A := by
        rw [hnull, add_zero]
        exact (hemb.comap_apply P A).symm

/-- **[18] Lemma 3.11 on the band family** (nominal scales `2⁻ᵏ`), from Proposition 4.10 at real meshes at one
radius `ρ' ∈ (ρ, 1)`, `C = 100`. -/
theorem bandFamily_lemma311Bad (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {θ : ℕ → ℝ} (hθb : IsBandSeq θ) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hρρ' : ρ < ρ') (hρ' : ρ' < 1) (h410 : Prop410Real P η ρ' 100) :
    T15A.Lemma311Bad (bandFamily D θ hθb.pos) ρ := by
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hden : 0 < (2 + γ) ^ 2 := by
    have : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq0 : 0 < q := by positivity
  have hq2 : q < 2 / (2 + γ) ^ 2 := by
    rw [hqdef]
    exact div_lt_div_of_pos_right (by norm_num) hden
  have hq1 : q < 1 := by
    have hfrac : 2 / (2 + γ) ^ 2 < 1 := (div_lt_iff₀ hden).mpr (by nlinarith [sq_nonneg γ, hγ.1])
    linarith
  set ρ₂ : ℝ := (ρ + ρ') / 2 with hρ₂def
  have hρ₂ : 0 < ρ₂ := by linarith
  have hρρ₂ : ρ < ρ₂ := by linarith
  have hρ₂ρ' : ρ₂ < ρ' := by linarith
  set α : ℝ := GMSLemma27.lemma27Exponent q γ / 2 with hαdef
  have hαpos : 0 < GMSLemma27.lemma27Exponent q γ := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq2
  have hα : 0 < α := by linarith
  have hαlt : α < GMSLemma27.lemma27Exponent q γ := by linarith
  -- [18] Lemma 2.7 at real meshes at `ρ'` (for both consumers: `ρ₂ < ρ'` and `ρ'`)
  obtain ⟨C, hC, hL⟩ := lemma27_real D hstd hγ hq0 hq2 (by linarith) hρ' hαlt
  have h27 := bandFamily_lemma27Bad D θ hθb.pos hθb hq0.le hα hC hρ₂ρ' hL
  have h27' := bandFamily_cellDiamBound_bad D θ hθb.pos hθb hq0.le hα hC hL
  exact lemma311Bad_of_inputs (bandFamily D θ hθb.pos) hγ ⟨hq0, hq2⟩ hq1 hρρ₂ hρ₂ hρ₂ρ' hρ'
    (bandFamily_graphConnected D θ hθb.pos) (bandFamily_graphLoopless D θ hθb.pos)
    (bandFamily_peanosphereG0 D θ hθb.pos) h27 hα hC h27' (bandFamily_prop210At D θ hθb.pos hθb h410)

/-- **[18] Lemma 3.11 along a band sequence, at the actual meshes `θₖ`**: `P[(3.35) fails at mesh θₖ] ≤ C θₖ^α`. -/
theorem lemma311_bandSeq (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {θ : ℕ → ℝ} (hθb : IsBandSeq θ) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hρρ' : ρ < ρ') (hρ' : ρ' < 1) (h410 : Prop410Real P η ρ' 100) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ k, P (Lemma311GoodReal bm η (θ k) ρ β p)ᶜ ≤ ENNReal.ofReal (C * θ k ^ α) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨α, hα, β, hβ, p, hp, C, hC⟩ := bandFamily_lemma311Bad D hstd hγ hθb hρ hρρ' hρ' h410
  refine ⟨α, hα, β / 2, by positivity, p, hp, max C 0 * 2 ^ α + 2 ^ α, fun k => ?_⟩
  refine ofReal_mesh_le_band hθb hα.le k prob_le_one fun hk => ?_
  refine (measure_le_of_bandFamily D hθb.pos (Lemma311GoodReal bm η (θ k) ρ (β / 2) p)ᶜ
    (T15A.Lemma311Good (bandFamily D θ hθb.pos) k ρ β p)ᶜ (fun ω hω hgood => hω ?_)).trans (hC k)
  exact ⟨(bandSpace_good D θ hθb.pos ω).locFin k, bandEmbedding D θ hθb.pos ω k,
    fun x => bandEmbedding_cell D θ hθb.pos ω k x,
    lemma311Holds_of_floor_le hgood (mesh_rpow_le_band_rpow_half hθb hk hβ.le)⟩

/-- **[18] Lemma 3.11 at every real mesh `ε ∈ (0, 1)`** for the embedded mated-CRT map of a frozen coupling, at
every `ρ ∈ (0, 1)`, given [18] Proposition 4.10 at real meshes at one radius `ρ' ∈ (ρ, 1)` (`C = 100`): there are
`α, β, p > 0` and `C` with `P[(3.35) fails at mesh ε] ≤ C ε^α` for all `ε ∈ (0, 1)`. -/
theorem lemma311Real_of_prop410 (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hρ' : ρ' < 1)
    (h410 : Prop410Real P η ρ' 100) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  refine uniform_rate_of_bandSeq (fun ε β p => P (Lemma311GoodReal bm η ε ρ β p)ᶜ) (fun _ _ _ => prob_le_one)
    ?_ (fun θ hθ => lemma311_bandSeq D hstd hγ hθ hρ hρρ' hρ' h410)
  intro ε β p β' p' h0 h1 hβ hp
  exact measure_mono (compl_subset_compl.mpr (lemma311GoodReal_mono h0 h1.le hβ hp))

/-- **[18] Lemma 3.11 at every real mesh and every `ρ ∈ (0, 1)`**, given [18] Proposition 4.10 at real meshes at
every radius (`C = 100`; `epsA_prop410At` has this shape for every `C > 1`). -/
theorem lemma311Real_of_prop410_all (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (h410 : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → Prop410Real P η ρ' 100) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) :=
  lemma311Real_of_prop410 D hstd hγ hρ (by linarith : ρ < (1 + ρ) / 2) (by linarith)
    (h410 _ (by linarith) (by linarith))

end Coupling

end MatedCRTHarmonic.GMSMain.EpsB
