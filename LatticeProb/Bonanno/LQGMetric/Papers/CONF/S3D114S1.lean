/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114S1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36H
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36I

/-!
# CONF Lemma 3.6, Step 3: the countable partition and the summation

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Step 3 of Lemma 3.6 (C:1425–1447); decision D114
§4 packet C2 (i), (iii), (iv).

CONF C:1438–1447: "conditional on `{ε = 𝔢, z = 𝔷, ρ̃ⁿ = 𝔯, Ũ = 𝔘}` … by Lemma 3.3 the conditional
probability of `G̃ⁿ` is at least `𝔭`". Here, for the next index `n + 1`:
* `conf36Pc … n i`, `i = (𝔢, 𝔷, k, 𝔗)`: the event `{e = 𝔢, z = 𝔷, ρ̃^{n+1} = 2^k𝔢, T = 𝔗} ∩ E^𝔘_{2^k𝔢}(𝔷)`;
* `conf36Pc_cover` (from `conf36Rho_attained`): off `{ρ̃^{n+1} = ∞}` some piece occurs;
* `conf36Pc_disj`: the pieces are pairwise disjoint;
* `conf36_step_of_pieces`: if `X ∩ conf36Pc … n i` is a.s. `B' ∩ E^𝔘_{2^k𝔢}(𝔷)` with
  `B' ∈ σ((h − h_{2^k𝔢}(𝔷))|_{ℂ∖𝔘})` (CONF (3.25)) and the pieces are null-measurable, then
  `𝔭 P(X) ≤ P(X ∩ G̃^{n+1})` (Lemma 3.3 in the form `L33GenAt`, summed over the countable
  partition; the connectivity conjunct of `G̃^{n+1}` is a.s., DEC-114 §1(d)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

section Pieces
variable {Ω : Type} [MeasurableSpace Ω]

/-- the piece `{e = 𝔢, z = 𝔷, ρ̃^{n+1} = 2^k𝔢, T_{2^k𝔢} = 𝔗} ∩ E^𝔘_{2^k𝔢}(𝔷)` (CONF C:1438) -/
def conf36Pc (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (e : Ω → ℝ) (zf : Ω → ℂ) (Bf : Ω → Set ℂ) (n : ℕ)
    (i : ℝ × ℂ × ℤ × Finset (ℤ × ℤ)) : Set Ω :=
  {ω | e ω = i.1 ∧ zf ω = i.2.1 ∧
    conf36Rho ξ cc D P h p e zf Bf (n + 1) ω = ENNReal.ofReal ((2 : ℝ) ^ i.2.2.1 * i.1) ∧
    conf36T p.δ ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1 (Bf ω) = i.2.2.2 ∧
    ω ∈ confEU ξ cc D P h p ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1 i.2.2.2}

/-- the countable index set of the pieces -/
def conf36Idx (e : Ω → ℝ) (zf : Ω → ℂ) : Set (ℝ × ℂ × ℤ × Finset (ℤ × ℤ)) :=
  range e ×ˢ range zf ×ˢ (univ : Set ℤ) ×ˢ (univ : Set (Finset (ℤ × ℤ)))

variable {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
  {p : CONFParams} {e : Ω → ℝ} {zf : Ω → ℂ} {Bf : Ω → Set ℂ}

omit [MeasurableSpace Ω] in
theorem conf36Idx_countable (he : (range e).Countable) (hz : (range zf).Countable) :
    (conf36Idx e zf).Countable :=
  he.prod (hz.prod (Set.countable_univ.prod Set.countable_univ))

theorem conf36Pc_cover {ω : Ω} (he : 0 < e ω) {n : ℕ}
    (hlt : conf36Rho ξ cc D P h p e zf Bf (n + 1) ω < ⊤) :
    ∃ i ∈ conf36Idx e zf, ω ∈ conf36Pc ξ cc D P h p e zf Bf n i := by
  obtain ⟨k, hk, -, hE⟩ := conf36Rho_attained he hlt
  exact ⟨(e ω, zf ω, k, conf36T p.δ ((2 : ℝ) ^ k * e ω) (zf ω) (Bf ω)),
    ⟨mem_range_self ω, mem_range_self ω, mem_univ _, mem_univ _⟩, rfl, rfl, hk, rfl, hE⟩

theorem conf36Pc_disj (he : ∀ ω, 0 < e ω) {n : ℕ} {i j : ℝ × ℂ × ℤ × Finset (ℤ × ℤ)}
    (hij : i ≠ j) :
    Disjoint (conf36Pc ξ cc D P h p e zf Bf n i) (conf36Pc ξ cc D P h p e zf Bf n j) := by
  rw [Set.disjoint_left]
  rintro ω ⟨a1, a2, a3, a4, -⟩ ⟨b1, b2, b3, b4, -⟩
  apply hij
  obtain ⟨i1, i2, i3, i4⟩ := i
  obtain ⟨j1, j2, j3, j4⟩ := j
  simp only at a1 a2 a3 a4 b1 b2 b3 b4
  have h1 : i1 = j1 := a1.symm.trans b1
  have h2 : i2 = j2 := a2.symm.trans b2
  subst h1 h2
  have hpos : 0 < i1 := a1 ▸ he ω
  have h3 : (2 : ℝ) ^ i3 = (2 : ℝ) ^ j3 := by
    have := a3.symm.trans b3
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at this
    exact mul_right_cancel₀ hpos.ne' this
  have h3' : i3 = j3 := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h3
  subst h3'
  rw [← a4, ← b4]

theorem conf36Pc_ge {n : ℕ} {i : ℝ × ℂ × ℤ × Finset (ℤ × ℤ)} {ω : Ω} (he : 0 < e ω)
    (hω : ω ∈ conf36Pc ξ cc D P h p e zf Bf n i) : e ω ≤ (2 : ℝ) ^ i.2.2.1 * i.1 := by
  obtain ⟨a1, -, a3, -, -⟩ := hω
  have h0 := conf36Rho_ge (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h) (p := p) (e := e)
    (zf := zf) (Bf := Bf) (n + 1) ω
  rw [a3] at h0
  have hpos : 0 ≤ (2 : ℝ) ^ i.2.2.1 * i.1 := by rw [← a1]; positivity
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 h0

theorem conf36Pc_sub_Gt {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop} {n : ℕ}
    {i : ℝ × ℂ × ℤ × Finset (ℤ × ℤ)} {ω : Ω} (hω : ω ∈ conf36Pc ξ cc D P h p e zf Bf n i)
    (hF : Fat (D (h ω)) (scaleFac ξ cc (h ω) ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1)
      ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1 i.2.2.2)
    (hC : conf36Conn (Bf ω) ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1) :
    ω ∈ conf36Gt Fat ξ cc D P h p e zf Bf (n + 1) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hω
  refine Or.inr ⟨i.2.2.1, ?_⟩
  rw [a1, a2, a4]
  exact ⟨a3, a5, hF, hC⟩

end Pieces

/-- **Step 3 summation** (CONF C:1438–1447): from (3.25) on each piece and Lemma 3.3 at `𝔭`,
`𝔭 P(X) ≤ P(X ∩ G̃^{n+1})` -/
theorem conf36_step_of_pieces {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop} {𝔭 : ℝ}
    (H : L33GenAt γ D c p Fat 𝔭) (h𝔭1 : 𝔭 ≤ 1) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {e : Ω → ℝ}
    {zf : Ω → ℂ} {Bf : Ω → Set ℂ} (he : ∀ ω, 0 < e ω) (hec : (range e).Countable)
    (hzc : (range zf).Countable) {n : ℕ} {X : Set Ω}
    (hconn : ∀ᵐ ω ∂P, ∀ r, e ω ≤ r → conf36Conn (Bf ω) r (zf ω))
    (hpm : ∀ i ∈ conf36Idx e zf,
      NullMeasurableSet (conf36Pc (xiGamma γ) c D P h p e zf Bf n i) P)
    (hpc : ∀ i ∈ conf36Idx e zf, ∃ B' : Set Ω,
      MeasurableSet[recSigma h ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1
        (confU ((2 : ℝ) ^ i.2.2.1 * i.1) p.δ i.2.1 i.2.2.2)ᶜ] B' ∧
      X ∩ conf36Pc (xiGamma γ) c D P h p e zf Bf n i =ᵐ[P]
        B' ∩ confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1 i.2.2.2) :
    ENNReal.ofReal 𝔭 * P X ≤ P (X ∩ conf36Gt Fat (xiGamma γ) c D P h p e zf Bf (n + 1)) := by
  set ι := conf36Idx e zf
  have : Countable ι := (conf36Idx_countable hec hzc).to_subtype
  set s : ι → Set Ω := fun i => conf36Pc (xiGamma γ) c D P h p e zf Bf n i.1 with hs_def
  set G := conf36Gt Fat (xiGamma γ) c D P h p e zf Bf (n + 1) with hG_def
  have hd : Pairwise (Function.onFun (AEDisjoint P) s) := fun i j hij =>
    (conf36Pc_disj he (fun hh' => hij (Subtype.ext hh'))).aedisjoint
  have hsm : ∀ i, NullMeasurableSet (s i) P := fun i => hpm i.1 i.2
  have hU : NullMeasurableSet (⋃ i, s i) P := NullMeasurableSet.iUnion hsm
  have hsum : ∀ Y : Set Ω, P (Y ∩ ⋃ i, s i) = ∑' i, P (Y ∩ s i) := by
    intro Y
    rw [← Measure.restrict_apply₀' hU, Measure.restrict_iUnion_ae hd hsm,
      Measure.sum_apply_of_countable]
    exact tsum_congr fun i => Measure.restrict_apply₀' (hsm i)
  have hout : X \ ⋃ i, s i ⊆ (X ∩ G) \ ⋃ i, s i := by
    rintro ω ⟨hX, hn⟩
    refine ⟨⟨hX, Or.inl ?_⟩, hn⟩
    by_contra hne
    obtain ⟨i, hi, hω⟩ := conf36Pc_cover (he ω) (lt_top_iff_ne_top.2 hne)
    exact hn (mem_iUnion.2 ⟨⟨i, hi⟩, hω⟩)
  have hpiece : ∀ i : ι, ENNReal.ofReal 𝔭 * P (X ∩ s i) ≤ P (X ∩ G ∩ s i) := by
    rintro ⟨i, hi⟩
    obtain ⟨B', hB', hae⟩ := hpc i hi
    rcases (s ⟨i, hi⟩).eq_empty_or_nonempty with h0 | ⟨ω₀, hω₀⟩
    · rw [h0]; simp
    set r := (2 : ℝ) ^ i.2.2.1 * i.1 with hr_def
    have hi1 : 0 < i.1 := by
      obtain ⟨⟨ω, hω⟩, -⟩ := hi
      rw [← hω]; exact he ω
    have hr : 0 < r := by positivity
    have hT : ∀ k ∈ i.2.2.2, k ∈ confSqIdx (p.δ * r) i.2.1 (annulus i.2.1 (3 * r) (4 * r)) := by
      intro k hk
      have e4 : conf36T p.δ r i.2.1 (Bf ω₀) = i.2.2.2 := hω₀.2.2.2.1
      rw [← e4] at hk
      exact conf36T_sub hk
    have hdisj : Disjoint (confU r p.δ i.2.1 i.2.2.2) (sphere i.2.1 r) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      have h1 : 3 * r < ‖u - i.2.1‖ := hu.1.1
      rw [mem_sphere, dist_eq_norm] at hu'
      linarith
    have h33 := H P h hh i.2.1 r hr i.2.2.2 hT r i.2.1 hr hdisj B' hB'
    calc ENNReal.ofReal 𝔭 * P (X ∩ s ⟨i, hi⟩)
        = ENNReal.ofReal 𝔭 * P (B' ∩ confEU (xiGamma γ) c D P h p r i.2.1 i.2.2.2) := by
          rw [measure_congr hae]
      _ ≤ _ := h33
      _ = P (X ∩ s ⟨i, hi⟩ ∩ {ω | Fat (D (h ω)) (scaleFac (xiGamma γ) c (h ω) r i.2.1) r i.2.1
            i.2.2.2}) := measure_congr (hae.symm.inter EventuallyEq.rfl)
      _ ≤ P (X ∩ G ∩ s ⟨i, hi⟩) := by
          refine measure_mono_ae ?_
          filter_upwards [hconn] with ω hω
          rintro ⟨⟨hX, hsω⟩, hF⟩
          have hC := hω _ (conf36Pc_ge (he ω) hsω)
          rw [hsω.2.1] at hC
          exact ⟨⟨hX, conf36Pc_sub_Gt hsω hF hC⟩, hsω⟩
  calc ENNReal.ofReal 𝔭 * P X
      = ENNReal.ofReal 𝔭 * (∑' i, P (X ∩ s i)) + ENNReal.ofReal 𝔭 * P (X \ ⋃ i, s i) := by
        rw [← hsum, ← mul_add, measure_inter_add_sdiff₀ _ hU]
    _ ≤ ∑' i, P (X ∩ G ∩ s i) + P ((X ∩ G) \ ⋃ i, s i) := by
        refine add_le_add ?_ ?_
        · rw [← ENNReal.tsum_mul_left]; exact ENNReal.tsum_le_tsum hpiece
        · calc ENNReal.ofReal 𝔭 * P (X \ ⋃ i, s i) ≤ 1 * P (X \ ⋃ i, s i) := by
                gcongr; exact ENNReal.ofReal_le_one.2 h𝔭1
            _ ≤ _ := by rw [one_mul]; exact measure_mono hout
    _ = P (X ∩ G) := by rw [← hsum, measure_inter_add_sdiff₀ _ hU]

end LQGMetric.CONF
