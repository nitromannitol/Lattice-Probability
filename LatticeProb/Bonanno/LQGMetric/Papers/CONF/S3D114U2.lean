/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114U2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114T3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1

/-!
# CONF Lemma 3.6 Step 1 (i): `G^ε_x` is a.s. an event of `σ(𝓑^•_{σ^ε}, h|) mod const`, given the
geometric input `B_{5ρ̃ⁿ}(z) ⊆ 𝓑^•_{σ^ε}`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 1, C:1362–1368; DEC-114 §4 C3.

The σ-algebra of the a.s. events of `σ(A', h|_{A'}) mod const` is `t39hAESig P (localSigma0 h A')`
(S3T39H3). On a piece `E₀ = {ε𝕣 = 𝔢, z = 𝔷}`, CONF's argument reads:
* the events of `(𝓑^•_τ, h|_{𝓑^•_τ})` (`E₀`, `{T_r = 𝔗}`, the connectivity events) are a.s. events
  (`hset`, from `conf36_trace_mono_ae`);
* `E^{Ũ}_r(z) ∩ {B_{5r}(z) ⊆ A'}` and `{fatG} ∩ {B_{5r}(z) ⊆ A'}` are a.s. events
  (`conf36_EUj_Hb`, `conf36_FatJ_Hb`: (DL1), (DL2) of S3D114T1 and `conf36_local_ae`);
* hence the radii `ρ̃^m` are a.s. events on `E₀ ∩ {B_{5·2^K𝔢}(𝔷) ⊆ A'}` (`conf36_measurableSet_rho`);
* `G̃ⁿ` is the union of these events (`conf36GRhs`), up to the null set where `B_{5ρ̃ⁿ}(z) ⊄ A'`
  (input `hgeo`, CONF C:1366 "By (3.21) and (3.17), `B_{5ρ̃ⁿ}(z) ⊆ 𝓑^•_σ`").
Main result: **`conf36_G_aeEventIn_of_geo`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

theorem conf36_sphere_sub_ball {r : ℝ} (hr : 0 < r) {z : ℂ} :
    sphere z r ⊆ ((⟨ball z (5 * r), isOpen_ball⟩ : Opens ℂ) : Set ℂ) := fun y hy => by
  show y ∈ ball z (5 * r)
  rw [mem_sphere] at hy
  rw [mem_ball]
  linarith

/-- the union of a.s. events which is `G̃ⁿ ∩ {ε𝕣 = 𝔢, z = 𝔷}` up to a null set -/
def conf36GRhs {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric)
    (P : Measure Ω) (h : Ω → DistC) (p : CONFParams) (e : Ω → ℝ) (zf : Ω → ℂ)
    (Bf B' : Ω → Set ℂ) (𝔢 : ℝ) (𝔷 : ℂ) (n : ℕ) : Set Ω :=
  ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ (⋂ k : ℤ, {ω | ball 𝔷 (5 * ((2 : ℝ) ^ k * 𝔢)) ⊆ B' ω}) ∩
      {ω | conf36Rho ξ cc D P h p e zf Bf n ω = ⊤}) ∪
    ⋃ k : ℤ, ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ {ω | ball 𝔷 (5 * ((2 : ℝ) ^ k * 𝔢)) ⊆ B' ω} ∩
        {ω | conf36Rho ξ cc D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ k * 𝔢)}) ∩
      conf36EUj ξ cc D P h p Bf 𝔢 𝔷 k ∩ conf36FatJ (fatG p) ξ cc D h p Bf 𝔢 𝔷 k ∩
      {ω | conf36Conn (Bf ω) ((2 : ℝ) ^ k * 𝔢) 𝔷}

section Piece
variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} {Ω : Type}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
  {Bf B' : Ω → Set ℂ} {e : Ω → ℝ} {zf : Ω → ℂ}

theorem conf36_aeSig_of_local {Y : Set Ω} (hY : MeasurableSet[localSigma0 h B'] Y) :
    MeasurableSet[t39hAESig P (localSigma0 h B')] Y := ⟨Y, hY, EventuallyEq.rfl⟩

theorem conf36_Hb_meas (hB'c : ∀ ω, IsClosed (B' ω)) (𝔷 : ℂ) (ρ : ℝ) :
    MeasurableSet[t39hAESig P (localSigma0 h B')] {ω | ball 𝔷 ρ ⊆ B' ω} :=
  conf36_aeSig_of_local (confD110_setSigma_le_localSigma0 h B' _
    (conf36_setSigma_subset_open hB'c isOpen_ball))

/-- `E^{Ũ}_{2^j𝔢}(𝔷) ∩ {B_{5·2^j𝔢}(𝔷) ⊆ A'}` is an a.s. event of `σ(A', h|_{A'}) mod const` -/
theorem conf36_EUj_Hb (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (hBc : ∀ ω, IsClosed (Bf ω)) (hB'c : ∀ ω, IsClosed (B' ω))
    (hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (B' ω) ∨ B' ω = univ)
    (hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y →
      MeasurableSet[t39hAESig P (localSigma0 h B')] Y)
    {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) (𝔷 : ℂ) (j : ℤ) :
    MeasurableSet[t39hAESig P (localSigma0 h B')] (conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 j ∩
      {ω | ball 𝔷 (5 * ((2 : ℝ) ^ j * 𝔢)) ⊆ B' ω}) := by
  have hr' : 0 < (2 : ℝ) ^ j * 𝔢 := mul_pos (zpow_pos (by norm_num) j) h𝔢0
  unfold conf36EUj
  rw [conf36_setOf_mem_eq_iUnion
    (fun T' => confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ j * 𝔢) 𝔷 T')
    (fun ω => conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω)), iUnion_inter]
  refine MeasurableSet.iUnion fun T' => ?_
  rw [inter_assoc]
  exact (hset (conf36_setSigma_T hBc _ _ _ T')).inter (conf36_local_ae h hB'c hA' isOpen_ball
    (conf36_aeEventIn_fieldSigma0On_of_norm hh hr'
      (A := ⟨ball 𝔷 (5 * ((2 : ℝ) ^ j * 𝔢)), isOpen_ball⟩) le_rfl (conf36_sphere_sub_ball hr')
      (conf36_confEU_ball hD hh p hr' 𝔷 T')))

/-- the `fatG` event at `2^j𝔢`, intersected with `{B_{5·2^j𝔢}(𝔷) ⊆ A'}`, is an a.s. event of
`σ(A', h|_{A'}) mod const` -/
theorem conf36_FatJ_Hb (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    (hh : IsWholePlaneGFF h P) (hBc : ∀ ω, IsClosed (Bf ω)) (hB'c : ∀ ω, IsClosed (B' ω))
    (hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (B' ω) ∨ B' ω = univ)
    (hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y →
      MeasurableSet[t39hAESig P (localSigma0 h B')] Y)
    {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) (𝔷 : ℂ) (j : ℤ) :
    MeasurableSet[t39hAESig P (localSigma0 h B')]
      (conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 j ∩
        {ω | ball 𝔷 (5 * ((2 : ℝ) ^ j * 𝔢)) ⊆ B' ω}) := by
  have hr' : 0 < (2 : ℝ) ^ j * 𝔢 := mul_pos (zpow_pos (by norm_num) j) h𝔢0
  unfold conf36FatJ
  have eq := conf36_setOf_mem_eq_iUnion (fun T' => {ω | fatG p (D (h ω))
    (scaleFac (xiGamma γ) c (h ω) ((2 : ℝ) ^ j * 𝔢) 𝔷) ((2 : ℝ) ^ j * 𝔢) 𝔷 T'})
    (fun ω => conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω))
  simp only [mem_ofPred_eq] at eq
  rw [eq, iUnion_inter]
  refine MeasurableSet.iUnion fun T' => ?_
  rw [inter_assoc]
  exact (hset (conf36_setSigma_T hBc _ _ _ T')).inter (conf36_local_ae h hB'c hA' isOpen_ball
    (conf36_aeEventIn_fieldSigma0On_of_norm hh hr'
      (A := ⟨ball 𝔷 (5 * ((2 : ℝ) ^ j * 𝔢)), isOpen_ball⟩) le_rfl (conf36_sphere_sub_ball hr')
      (conf36_fatG_ball hD hh p hδ hδ8 c hr' 𝔷 T')))

theorem conf36_Hb_anti {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) {𝔷 : ℂ} {j k : ℤ} (hjk : j ≤ k) :
    {ω | ball 𝔷 (5 * ((2 : ℝ) ^ k * 𝔢)) ⊆ B' ω} ⊆ {ω | ball 𝔷 (5 * ((2 : ℝ) ^ j * 𝔢)) ⊆ B' ω} :=
  fun ω hω => (ball_subset_ball (by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk
    nlinarith)).trans hω

/-- **the union `conf36GRhs` is an a.s. event** of `σ(A', h|_{A'}) mod const` -/
theorem conf36_GRhs_meas (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    (hh : IsWholePlaneGFF h P) (hBc : ∀ ω, IsClosed (Bf ω)) (hB'c : ∀ ω, IsClosed (B' ω))
    (hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (B' ω) ∨ B' ω = univ)
    (hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y →
      MeasurableSet[t39hAESig P (localSigma0 h B')] Y)
    {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) (𝔷 : ℂ)
    (hE₀ : MeasurableSet[t39hAESig P (localSigma0 h B')] {ω | e ω = 𝔢 ∧ zf ω = 𝔷}) (n : ℕ) :
    MeasurableSet[t39hAESig P (localSigma0 h B')]
      (conf36GRhs (xiGamma γ) c D P h p e zf Bf B' 𝔢 𝔷 n) := by
  set E₀ := {ω | e ω = 𝔢 ∧ zf ω = 𝔷} with hE₀def
  set Hb : ℤ → Set Ω := fun k => {ω | ball 𝔷 (5 * ((2 : ℝ) ^ k * 𝔢)) ⊆ B' ω} with hHb
  have hHbm : ∀ k, MeasurableSet[t39hAESig P (localSigma0 h B')] (Hb k) := fun k => conf36_Hb_meas hB'c 𝔷 _
  -- the radii on `E₀ ∩ Hb K`
  have hρ : ∀ (K : ℤ) (m : ℕ) (ℓ : ℤ), ℓ ≤ K → MeasurableSet[t39hAESig P (localSigma0 h B')] ((E₀ ∩ Hb K) ∩
      {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf m ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢)}) := by
    intro K m ℓ hℓ
    refine conf36_measurableSet_rho (t39hAESig P (localSigma0 h B')) (k := K + 1) h𝔢0 (fun ω hω => hω.1) (hE₀.inter (hHbm K))
      (fun j hj => ?_) m ℓ (by omega)
    have e1 : E₀ ∩ Hb K ∩ conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 j =
        (E₀ ∩ Hb K) ∩ (conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 j ∩ Hb j) := by
      ext ω
      simp only [mem_inter_iff]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, h3, conf36_Hb_anti h𝔢0 (by omega) h2⟩,
        fun ⟨⟨h1, h2⟩, h3, _⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    rw [e1]
    exact (hE₀.inter (hHbm K)).inter (conf36_EUj_Hb hD hh hBc hB'c hA' hset h𝔢0 𝔷 j)
  have hk : ∀ k : ℤ, MeasurableSet[t39hAESig P (localSigma0 h B')] (((E₀ ∩ Hb k) ∩
      {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ k * 𝔢)}) ∩
      conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 k ∩
      conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 k ∩
      {ω | conf36Conn (Bf ω) ((2 : ℝ) ^ k * 𝔢) 𝔷}) := by
    intro k
    have e1 : ((E₀ ∩ Hb k) ∩
        {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ k * 𝔢)}) ∩
        conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 k ∩
        conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 k =
        ((E₀ ∩ Hb k) ∩
          {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ k * 𝔢)}) ∩
        (conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 k ∩ Hb k) ∩
        (conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 k ∩ Hb k) := by
      ext ω
      simp only [mem_inter_iff]
      exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4, h2⟩, h5, h2⟩,
        fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4, _⟩, h5, _⟩ => ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    rw [e1]
    exact (((hρ k n k le_rfl).inter (conf36_EUj_Hb hD hh hBc hB'c hA' hset h𝔢0 𝔷 k)).inter
      (conf36_FatJ_Hb hδ hδ8 hD hh hBc hB'c hA' hset h𝔢0 𝔷 k)).inter
      (hset (conf36_setSigma_conn Bf _ 𝔷))
  have htop : MeasurableSet[t39hAESig P (localSigma0 h B')] (E₀ ∩ (⋂ k : ℤ, Hb k) ∩
      {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤}) := by
    have eq : E₀ ∩ (⋂ k : ℤ, Hb k) ∩ {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤} =
        (E₀ ∩ ⋂ k : ℤ, Hb k) \ ⋃ ℓ : ℤ, ((E₀ ∩ Hb ℓ) ∩
          {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
            ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢)}) := by
      ext ω
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨h0, fun hU => ?_⟩
        obtain ⟨ℓ, -, h2⟩ := mem_iUnion.1 hU
        have h1' : conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤ := h1
        have h2' : conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
          ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢) := h2
        exact ENNReal.ofReal_ne_top (h2'.symm.trans h1')
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        have e1 : e ω = 𝔢 := h0.1.1
        have hpos : 0 < e ω := e1 ▸ h𝔢0
        rcases conf36Rho_cases (ξ := xiGamma γ) (cc := c) (D := D) (P := P) (h := h) (p := p)
          (zf := zf) (Bf := Bf) hpos n with ht | ⟨ℓ, hℓ⟩
        · exact ht
        · rw [e1] at hℓ
          exact absurd (mem_iUnion.2 ⟨ℓ, (⟨⟨h0.1, mem_iInter.1 h0.2 ℓ⟩, hℓ⟩ :
            ω ∈ (E₀ ∩ Hb ℓ) ∩ {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
              ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢)})⟩) h1
    rw [eq]
    exact (hE₀.inter (MeasurableSet.iInter hHbm)).diff
      (MeasurableSet.iUnion fun ℓ => hρ ℓ n ℓ le_rfl)
  exact htop.union (MeasurableSet.iUnion hk)

set_option maxHeartbeats 1000000 in
/-- `conf36GRhs ⊆ {ε𝕣 = 𝔢, z = 𝔷} ∩ G̃ⁿ` -/
theorem conf36_GRhs_sub {𝔢 : ℝ} {𝔷 : ℂ} (n : ℕ) :
    conf36GRhs (xiGamma γ) c D P h p e zf Bf B' 𝔢 𝔷 n ⊆
      {ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ conf36Gt (fatG p) (xiGamma γ) c D P h p e zf Bf n := by
  rw [conf36_Gt_piece_eq n]
  rintro ω (⟨⟨h0, -⟩, h1⟩ | hU)
  · exact Or.inl ⟨h0, h1⟩
  · obtain ⟨k, ⟨⟨⟨⟨h0, -⟩, h2⟩, h3⟩, h4⟩, h5⟩ := mem_iUnion.1 hU
    exact Or.inr (mem_iUnion.2 ⟨k, ⟨⟨⟨h0, h2⟩, h3⟩, h4⟩, h5⟩)

set_option maxHeartbeats 1000000 in
/-- on the event of the geometric input, `{ε𝕣 = 𝔢, z = 𝔷} ∩ G̃ⁿ ⊆ conf36GRhs` -/
theorem conf36_sub_GRhs {𝔢 : ℝ} {𝔷 : ℂ} (n : ℕ) {ω : Ω}
    (hω : ω ∈ {ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ conf36Gt (fatG p) (xiGamma γ) c D P h p e zf Bf n)
    (hg : (∀ k : ℤ, conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
        ENNReal.ofReal ((2 : ℝ) ^ k * e ω) → ball (zf ω) (5 * ((2 : ℝ) ^ k * e ω)) ⊆ B' ω) ∧
      (conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤ → ∀ ρ : ℝ, ball (zf ω) ρ ⊆ B' ω)) :
    ω ∈ conf36GRhs (xiGamma γ) c D P h p e zf Bf B' 𝔢 𝔷 n := by
  have e1 : e ω = 𝔢 := hω.1.1
  have e2 : zf ω = 𝔷 := hω.1.2
  rw [conf36_Gt_piece_eq n] at hω
  rcases hω with ⟨h0, h1⟩ | hU
  · refine Or.inl ⟨⟨h0, mem_iInter.2 fun k => ?_⟩, h1⟩
    have := hg.2 h1 (5 * ((2 : ℝ) ^ k * 𝔢))
    rw [e2] at this
    exact this
  · obtain ⟨k, ⟨⟨⟨h0, h2⟩, h3⟩, h4⟩, h5⟩ := mem_iUnion.1 hU
    have h2' : conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ k * 𝔢) := h2
    have hb := hg.1 k (by rw [e1]; exact h2')
    rw [e1, e2] at hb
    exact Or.inr (mem_iUnion.2 ⟨k, ⟨⟨⟨⟨h0, hb⟩, h2⟩, h3⟩, h4⟩, h5⟩)

end Piece

/-- **Step 1, part (i), given the geometric input** (CONF C:1362–1368): if every
`(𝓑^•_τ, h|_{𝓑^•_τ}) mod const`-event is a.s. an event of `σ(A', h|_{A'}) mod const`, `A'` is closed,
a.s. bounded or `ℂ`, and a.s. `B_{5ρ̃ⁿ}(z) ⊆ A'` for `1 ≤ n ≤ ⌊η log ε⁻¹⌋` (and `A' = ℂ` when
`ρ̃ⁿ = ∞`), then `G^ε_x` is a.s. an event of `σ(A', h|_{A'}) mod const` -/
theorem conf36_G_aeEventIn_of_geo {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    {p : CONFParams} (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {Bf B' : Ω → Set ℂ} (hBc : ∀ ω, IsClosed (Bf ω))
    (hB'c : ∀ ω, IsClosed (B' ω)) (hA' : ∀ᵐ ω ∂P, Bornology.IsBounded (B' ω) ∨ B' ω = univ)
    (hTr : ∀ {Y : Set Ω}, MeasurableSet[localSigma0 h Bf] Y → AEEventIn P (localSigma0 h B') Y)
    {R : ℝ} (hR : 0 < R) (x : Ω → ℂ) (ε : Ω → ℝ)
    (hx : @Measurable Ω ℂ (localSigma0 h Bf) _ x) (hε : @Measurable Ω ℝ (localSigma0 h Bf) _ ε)
    (hε1 : ∀ ω, ε ω ∈ Ioo 0 1) (hεc : (Set.range ε).Countable)
    (hgeo : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → n ≤ confN p (ε ω) →
      (∀ k : ℤ, conf36Rho (xiGamma γ) c D P h p (fun ω => ε ω * R)
          (fun ω => conf36Grid (ε ω * R / 4) (x ω)) Bf n ω =
          ENNReal.ofReal ((2 : ℝ) ^ k * (ε ω * R)) →
        ball (conf36Grid (ε ω * R / 4) (x ω)) (5 * ((2 : ℝ) ^ k * (ε ω * R))) ⊆ B' ω) ∧
      (conf36Rho (xiGamma γ) c D P h p (fun ω => ε ω * R)
          (fun ω => conf36Grid (ε ω * R / 4) (x ω)) Bf n ω = ⊤ →
        ∀ ρ : ℝ, ball (conf36Grid (ε ω * R / 4) (x ω)) ρ ⊆ B' ω)) :
    AEEventIn P (localSigma0 h B') (conf36G (fatG p) (xiGamma γ) c D P h p ε
      (fun ω => ε ω * R) (fun ω => conf36Grid (ε ω * R / 4) (x ω)) Bf) := by
  set e : Ω → ℝ := fun ω => ε ω * R with he
  set zf : Ω → ℂ := fun ω => conf36Grid (ε ω * R / 4) (x ω) with hzf
  have hTrM : ∀ {Y : Set Ω}, MeasurableSet[localSigma0 h Bf] Y → MeasurableSet[t39hAESig P (localSigma0 h B')] Y :=
    fun hY => hTr hY
  have hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y → MeasurableSet[t39hAESig P (localSigma0 h B')] Y := fun hY =>
    hTrM (confD110_setSigma_le_localSigma0 h _ _ hY)
  have hem : Measurable[localSigma0 h Bf] e := hε.mul_const R
  have hzm : Measurable[localSigma0 h Bf] zf :=
    conf36_measurable_grid ((hε.mul_const R).div_const 4) hx
  have hNm : ∀ n : ℕ, MeasurableSet[localSigma0 h Bf] {ω | n ≤ confN p (ε ω)} := fun n => by
    have hg : Measurable (fun t : ℝ => ⌊p.η * Real.log t⁻¹⌋₊) :=
      (measurable_const.mul (Real.measurable_log.comp measurable_inv)).nat_floor
    exact (hg.comp hε) (MeasurableSet.of_discrete (s := {m : ℕ | n ≤ m}))
  have hec : (range e).Countable :=
    (hεc.image (· * R)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨ε ω, mem_range_self ω, rfl⟩)
  have hzc := conf36_range_grid_countable (m := fun ω => ε ω * R / 4)
    ((hεc.image (· * R / 4)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨ε ω, mem_range_self ω, rfl⟩)) x
  -- the a.s. version
  set Rhs : Set Ω := ⋃ 𝔢 ∈ range e, ⋃ 𝔷 ∈ range zf, ⋃ n : ℕ,
    ({ω | 1 ≤ n ∧ n ≤ confN p (ε ω)} ∩ conf36GRhs (xiGamma γ) c D P h p e zf Bf B' 𝔢 𝔷 n)
    with hRhs
  have hRm : MeasurableSet[t39hAESig P (localSigma0 h B')] Rhs := by
    refine MeasurableSet.biUnion hec fun 𝔢 h𝔢 => MeasurableSet.biUnion hzc fun 𝔷 _ =>
      MeasurableSet.iUnion fun n => ?_
    obtain ⟨ω₀, rfl⟩ := h𝔢
    have hE₀ : MeasurableSet[t39hAESig P (localSigma0 h B')] {ω | e ω = e ω₀ ∧ zf ω = 𝔷} :=
      hTrM ((hem (measurableSet_singleton _)).inter (hzm (measurableSet_singleton 𝔷)))
    have h1n : MeasurableSet[t39hAESig P (localSigma0 h B')] {ω | 1 ≤ n ∧ n ≤ confN p (ε ω)} := by
      by_cases hn : 1 ≤ n
      · simp only [hn, true_and]; exact hTrM (hNm n)
      · simp only [hn, false_and, ofPred_false]; exact @MeasurableSet.empty _ (t39hAESig P (localSigma0 h B'))
    exact h1n.inter (conf36_GRhs_meas hδ hδ8 hD hh hBc hB'c hA' hset
      (mul_pos (hε1 ω₀).1 hR) 𝔷 hE₀ n)
  obtain ⟨F, hF, hRF⟩ := hRm
  refine ⟨F, hF, EventuallyEq.trans ?_ hRF⟩
  filter_upwards [hgeo] with ω hg
  apply propext
  constructor
  · rintro ⟨n, h1, h2, hG⟩
    simp only [hRhs, mem_iUnion, mem_inter_iff, exists_prop, mem_range]
    exact ⟨e ω, ⟨ω, rfl⟩, zf ω, ⟨ω, rfl⟩, n, ⟨h1, h2⟩,
      conf36_sub_GRhs (B' := B') n ⟨⟨rfl, rfl⟩, hG⟩ (hg n h1 h2)⟩
  · intro hω
    simp only [hRhs, mem_iUnion, mem_inter_iff, exists_prop, mem_range] at hω
    obtain ⟨_, _, 𝔷, _, n, ⟨h1, h2⟩, hR'⟩ := hω
    exact ⟨n, h1, h2, (conf36_GRhs_sub n hR').2⟩

end LQGMetric.CONF
