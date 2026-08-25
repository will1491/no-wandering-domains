/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.NormalFamilies.Basic
import RMT4.Montel

/-!
# Classical Montel theorem

A locally uniformly bounded family of holomorphic functions on an open set
`U ⊆ ℂ` is normal. The substance is in RMT4's `montel`; here we re-package its
total-boundedness conclusion in the `IsNormal` sequential-subsequence form
used by the dynamics line.
-/

open scoped Uniformity

namespace NoWanderingDomains

open Set Filter Topology

/-- **Classical Montel theorem.** A locally uniformly bounded family of
holomorphic functions on an open set is normal. -/
theorem montel_locallyBounded {𝓕 : Set (ℂ → ℂ)} {U : Set ℂ}
    (hU : IsOpen U) (h : LocallyUniformlyBounded 𝓕 U)
    (hol : ∀ f ∈ 𝓕, DifferentiableOn ℂ f U) : IsNormal 𝓕 U := by
  intro seq
  -- F : the underlying sequence of ℂ → ℂ
  let F : ℕ → ℂ → ℂ := fun n => (seq n : ℂ → ℂ)
  -- Lift to the UniformOnFun space UniformOnFun ℂ ℂ (compacts U).
  let F' : ℕ → (UniformOnFun ℂ ℂ (compacts U)) := fun n => UniformOnFun.ofFun _ (F n)
  -- Holomorphic and uniformly bounded on compacts (in RMT4's form).
  have hF_holo : ∀ n, DifferentiableOn ℂ (F n) U :=
    fun n => hol _ (seq n).property
  have hF_bdd : UniformlyBoundedOn F U := by
    intro K hK
    obtain ⟨hK_sub, hK_compact⟩ := hK
    obtain ⟨M, hM⟩ := h K hK_sub hK_compact
    refine ⟨Metric.closedBall 0 M, isCompact_closedBall _ _, fun i x hx => ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hM (F i) (seq i).property x hx
  -- Apply RMT4's total-boundedness Montel.
  have hTB : TotallyBounded (Set.range F') := montel hU hF_bdd hF_holo
  -- Build a countable cofinal sequence in compacts U via CompactExhaustion of ↑U.
  have : LocallyCompactSpace ↑U := hU.locallyCompactSpace
  let exh : CompactExhaustion ↑U := default
  let E : ℕ → Set ℂ := fun n => Subtype.val '' (exh n)
  have hE_mono : Monotone E := fun m n hmn => Set.image_mono (exh.subset hmn)
  have hE_subU : ∀ n, E n ⊆ U := by
    rintro n _ ⟨w, _, rfl⟩; exact w.property
  have hE_cpt : ∀ n, IsCompact (E n) :=
    fun n => (exh.isCompact n).image continuous_subtype_val
  have hE_mem : ∀ n, E n ∈ compacts U := fun n => ⟨hE_subU n, hE_cpt n⟩
  have hE_cofinal : ∀ s ∈ compacts U, ∃ n, s ⊆ E n := by
    rintro s ⟨hsU, hscpt⟩
    let s' : Set ↑U := Subtype.val ⁻¹' s
    have himg : Subtype.val '' s' = s := by
      ext z
      refine ⟨fun ⟨⟨w, _⟩, hz, hh⟩ => hh ▸ hz, fun hz => ⟨⟨z, hsU hz⟩, hz, rfl⟩⟩
    have hs'_cpt : IsCompact s' :=
      (IsEmbedding.subtypeVal (p := (· ∈ U))).isCompact_iff.mpr (himg ▸ hscpt)
    obtain ⟨n, hn⟩ := exh.exists_superset_of_isCompact hs'_cpt
    refine ⟨n, ?_⟩
    intro z hz
    exact ⟨⟨z, hsU hz⟩, hn hz, rfl⟩
  -- The uniformity on `UniformOnFun ℂ ℂ (compacts U)` is countably generated.
  have : IsCountablyGenerated (𝓤 (UniformOnFun ℂ ℂ (compacts U))) :=
    UniformOnFun.isCountablyGenerated_uniformity (compacts U) hE_mem hE_mono hE_cofinal
  -- The closure of the range is compact in 𝓒 U (which is a complete uniform space).
  have hClosure_cpt : IsCompact (closure (Set.range F')) :=
    hTB.closure.isCompact_of_isClosed isClosed_closure
  -- Each F' n lies in this compact set.
  have hF'_mem : ∀ n, F' n ∈ closure (Set.range F') :=
    fun n => subset_closure (Set.mem_range_self n)
  -- Sequential extraction from a compact set in a first-countable space.
  obtain ⟨g, _, φ, hφ_mono, hg⟩ := hClosure_cpt.tendsto_subseq hF'_mem
  -- Translate convergence in `UniformOnFun ℂ ℂ (compacts U)` to TendstoLocallyUniformlyOn on U.
  refine ⟨φ, hφ_mono, UniformOnFun.toFun _ g, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hKcpt
  exact UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hg K ⟨hKU, hKcpt⟩

end NoWanderingDomains
