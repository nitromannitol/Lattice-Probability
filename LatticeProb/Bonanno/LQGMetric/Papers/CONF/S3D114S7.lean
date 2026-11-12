/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114S7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S1

/-!
# CONF Lemma 3.6, Step 3: the piece event through events at radii `< 𝔯`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Step 3 (C:1433–1447; (3.25)); decision D114
§4 C2 (ii).

For the piece `i = (𝔢, 𝔷, k, 𝔗)`, `𝔯 = 2^k𝔢`, `conf36_avoid_pc_eq`:
`A ∩ ⋂_{1≤m≤n'} (G̃^m)ᶜ ∩ conf36Pc … n i = conf36W … ∩ E^𝔘_𝔯(𝔷)`, where `conf36W` only involves
`A`, `{e = 𝔢, z = 𝔷}`, `{T_𝔯 = 𝔗}`, the events `{ρ̃^m = 2^ℓ𝔢}`, `ℓ < k`, and the events
`E^{Ũ}_{2^j𝔢}(𝔷)`, `Fat`, `conf36Conn` at the radii `2^j𝔢 < 𝔯`. CONF C:1438–1443: "the event
`{ρ̃ⁿ = 𝔯}` … is determined by `E^{Ũ^𝔯}_𝔯(𝔷)` and the events at smaller radii".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

section Defs
variable {Ω : Type} [MeasurableSpace Ω]

/-- the `Fat` event at `r = 2^j𝔢` with `Ũ^r` built from `Bf` -/
def conf36FatJ (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (h : Ω → DistC) (p : CONFParams) (Bf : Ω → Set ℂ) (𝔢 : ℝ) (𝔷 : ℂ)
    (j : ℤ) : Set Ω :=
  {ω | Fat (D (h ω)) (scaleFac ξ cc (h ω) ((2 : ℝ) ^ j * 𝔢) 𝔷) ((2 : ℝ) ^ j * 𝔢) 𝔷
    (conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω))}

/-- `G̃^m` on the region `ρ̃^m ≤ 𝔯/6`, through radii `2^{k'}𝔢` with `6·2^{k'} ≤ 2^k` -/
def conf36GtR (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (p : CONFParams) (e : Ω → ℝ)
    (zf : Ω → ℂ) (Bf : Ω → Set ℂ) (𝔢 : ℝ) (𝔷 : ℂ) (k : ℤ) (m : ℕ) : Set Ω :=
  ⋃ k' : {k' : ℤ // 6 * (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ k},
    {ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
      {ω | conf36Rho ξ cc D P h p e zf Bf m ω = ENNReal.ofReal ((2 : ℝ) ^ k'.1 * 𝔢)} ∩
      conf36EUj ξ cc D P h p Bf 𝔢 𝔷 k'.1 ∩ conf36FatJ Fat ξ cc D h p Bf 𝔢 𝔷 k'.1 ∩
      {ω | conf36Conn (Bf ω) ((2 : ℝ) ^ k'.1 * 𝔢) 𝔷}

/-- `{ρ̃^{n+1} = 𝔯}` without the event `E^{Ũ}_𝔯(𝔷)` -/
def conf36RR (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (e : Ω → ℝ) (zf : Ω → ℂ) (Bf : Ω → Set ℂ) (𝔢 : ℝ) (𝔷 : ℂ) (k : ℤ)
    (n : ℕ) : Set Ω :=
  ⋃ ℓ' : {ℓ' : ℤ // 6 * (2 : ℝ) ^ ℓ' ≤ (2 : ℝ) ^ k},
    ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
      {ω | conf36Rho ξ cc D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ'.1 * 𝔢)}) ∩
    ⋂ j : {j : ℤ // j < k}, ({_ω | 6 * (2 : ℝ) ^ ℓ'.1 ≤ (2 : ℝ) ^ j.1}ᶜ ∪
      ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ conf36EUj ξ cc D P h p Bf 𝔢 𝔷 j.1)ᶜ)

/-- the event `W` with `A ∩ ⋂_{m ≤ n'} (G̃^m)ᶜ ∩ conf36Pc … n i = W ∩ E^𝔘_𝔯(𝔷)` -/
def conf36W (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (p : CONFParams) (e : Ω → ℝ)
    (zf : Ω → ℂ) (Bf : Ω → Set ℂ) (A : Set Ω) (n n' : ℕ) (𝔢 : ℝ) (𝔷 : ℂ) (k : ℤ)
    (𝔗 : Finset (ℤ × ℤ)) : Set Ω :=
  A ∩ {ω | conf36T p.δ ((2 : ℝ) ^ k * 𝔢) 𝔷 (Bf ω) = 𝔗} ∩
    conf36RR ξ cc D P h p e zf Bf 𝔢 𝔷 k n ∩
    {ω | ∀ m, 1 ≤ m → m ≤ n' → ω ∉ conf36GtR Fat ξ cc D P h p e zf Bf 𝔢 𝔷 k m}

end Defs

section Eq
variable {Ω : Type} [MeasurableSpace Ω] {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop}
  {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
  {p : CONFParams} {e : Ω → ℝ} {zf : Ω → ℂ} {Bf : Ω → Set ℂ} {𝔢 : ℝ} {𝔷 : ℂ} {k : ℤ}

set_option maxHeartbeats 1000000 in
theorem conf36_mem_Gt_iff_GtR (h𝔢 : 0 < 𝔢) {ω : Ω} (he1 : e ω = 𝔢) (hz1 : zf ω = 𝔷)
    {m n : ℕ} (hmn : m ≤ n) {ℓ' : ℤ}
    (h1 : conf36Rho ξ cc D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ' * 𝔢))
    (h2 : 6 * (2 : ℝ) ^ ℓ' ≤ (2 : ℝ) ^ k) :
    ω ∈ conf36Gt Fat ξ cc D P h p e zf Bf m ↔
      ω ∈ conf36GtR Fat ξ cc D P h p e zf Bf 𝔢 𝔷 k m := by
  have hmono := conf36Rho_mono (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h) (p := p) (e := e)
    (zf := zf) (Bf := Bf) ω hmn
  simp only at hmono
  constructor
  · rintro (htop | ⟨k', hρ, hEU, hF, hC⟩)
    · rw [htop, h1] at hmono
      exact absurd hmono (not_le.2 ENNReal.ofReal_lt_top)
    · rw [he1] at hρ
      rw [he1, hz1] at hEU hF hC
      have hb : 6 * (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ k := by
        rw [hρ, h1, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmono
        have := le_of_mul_le_mul_right hmono h𝔢
        linarith
      exact mem_iUnion.2 ⟨⟨k', hb⟩, ⟨⟨⟨⟨⟨he1, hz1⟩, hρ⟩, hEU⟩, hF⟩, hC⟩⟩
  · intro hR
    obtain ⟨⟨k', _hk⟩, ⟨⟨⟨⟨_h0, hρ⟩, hEU⟩, hF⟩, hC⟩⟩ := mem_iUnion.1 hR
    refine Or.inr ⟨k', ?_⟩
    rw [he1, hz1]
    exact ⟨hρ, hEU, hF, hC⟩

set_option maxHeartbeats 1000000 in
/-- **the piece through events at radii `< 𝔯`** -/
theorem conf36_avoid_pc_eq (h𝔢 : 0 < 𝔢) {n n' : ℕ} (hn' : n' ≤ n) (A : Set Ω)
    (𝔗 : Finset (ℤ × ℤ)) :
    conf36Avoid (conf36Gt Fat ξ cc D P h p e zf Bf) A n' ∩
        conf36Pc ξ cc D P h p e zf Bf n (𝔢, 𝔷, k, 𝔗) =
      conf36W Fat ξ cc D P h p e zf Bf A n n' 𝔢 𝔷 k 𝔗 ∩
        confEU ξ cc D P h p ((2 : ℝ) ^ k * 𝔢) 𝔷 𝔗 := by
  ext ω
  constructor
  · rintro ⟨⟨hA, hav⟩, he1, hz1, hρ, hT, hEU⟩
    simp only at he1 hz1 hρ hT hEU
    have key := conf36Rho_succ_eq_iff (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h)
      (p := p) (zf := zf) (Bf := Bf) (he1 ▸ h𝔢) n k
    rw [he1, hz1] at key
    obtain ⟨ℓ', h1, h2, -, h4⟩ := key.1 hρ
    refine ⟨⟨⟨⟨hA, hT⟩, mem_iUnion.2 ⟨⟨ℓ', h2⟩, ⟨⟨he1, hz1⟩, h1⟩, mem_iInter.2 fun j => ?_⟩⟩,
      fun m hm1 hm2 hR => hav m hm1 hm2 ?_⟩, hEU⟩
    · by_cases hc : 6 * (2 : ℝ) ^ ℓ' ≤ (2 : ℝ) ^ j.1
      · exact Or.inr fun hh => h4 j.1 hc j.2 hh.2
      · exact Or.inl hc
    · exact (conf36_mem_Gt_iff_GtR h𝔢 he1 hz1 (hm2.trans hn') h1 h2).2 hR
  · rintro ⟨⟨⟨⟨hA, hT⟩, hRR⟩, hnot⟩, hEU⟩
    obtain ⟨⟨ℓ', h2⟩, ⟨⟨he1, hz1⟩, h1⟩, h4⟩ := mem_iUnion.1 hRR
    have key := conf36Rho_succ_eq_iff (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h)
      (p := p) (zf := zf) (Bf := Bf) (he1 ▸ h𝔢) n k
    rw [he1, hz1] at key
    have hT' : conf36T p.δ ((2 : ℝ) ^ k * 𝔢) 𝔷 (Bf ω) = 𝔗 := hT
    have hρ := key.2 ⟨ℓ', h1, h2, by rw [hT']; exact hEU, fun j hj hjk hEj =>
      (mem_iInter.1 h4 ⟨j, hjk⟩).elim (fun c => c hj) (fun c => c ⟨⟨he1, hz1⟩, hEj⟩)⟩
    refine ⟨⟨hA, fun m hm1 hm2 hG => hnot m hm1 hm2
      ((conf36_mem_Gt_iff_GtR h𝔢 he1 hz1 (hm2.trans hn') h1 h2).1 hG)⟩, he1, hz1, hρ, hT', hEU⟩

end Eq

end LQGMetric.CONF
