/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.JuliaFatou.Def
import NoWanderingDomains.Sphere.OpenMapping

/-!
# Complete invariance of the Fatou and Julia sets

For a continuous open self-map `f` of the sphere, the Fatou set satisfies
`f ⁻¹' (FatouSet f) = FatouSet f`, hence so does the Julia set; under the
additional hypothesis that `f` is surjective the image forms
`f '' (FatouSet f) = FatouSet f` and `f '' (JuliaSet f) = JuliaSet f`
follow. Rational maps satisfy all three hypotheses.

The two directions are proved by different mechanisms:

* `mem_fatouSet_of_apply_mem` (backward): normality near `f z` pulls back
  through the continuous `f` by pre-composition, after splitting off the
  identity `f^[0]` from the family.
* `apply_mem_fatouSet` (forward): normality near `z` pushes forward to the
  open neighborhood `f '' U` of `f z`. A locally uniform limit `h` of
  `f^[kₙ + 1] = f^[kₙ] ∘ f` on `U` is constant on fibres of `f`, so it
  factors as `h = H ∘ f`, and `f^[kₙ] → H` locally uniformly on `f '' U`
  because every compact of `f '' U` is the `f`-image of a compact of `U`
  (`exists_isCompact_subset_of_isCompact_subset_image`).
-/

namespace NoWanderingDomains

/-- A compact subset of the open image `f '' U` of an open map is covered by
the image of a compact subset of `U`. -/
theorem exists_isCompact_subset_of_isCompact_subset_image {f : ℂ̂ → ℂ̂}
    (hfo : IsOpenMap f) {U K : Set ℂ̂} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ f '' U) :
    ∃ K', IsCompact K' ∧ K' ⊆ U ∧ K ⊆ f '' K' := by
  choose x hxU hfx using fun y : K => hKU y.2
  choose C hCc hCi hCU using fun y : K => exists_compact_subset hU (hxU y)
  have hcover : K ⊆ ⋃ y : K, f '' interior (C y) := fun w hw =>
    Set.mem_iUnion.mpr ⟨⟨w, hw⟩, x ⟨w, hw⟩, hCi ⟨w, hw⟩, hfx ⟨w, hw⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => f '' interior (C y))
    (fun y => hfo _ isOpen_interior) hcover
  refine ⟨⋃ y ∈ t, C y, t.isCompact_biUnion fun y _ => hCc y,
    Set.iUnion₂_subset fun y _ => hCU y, fun w hw => ?_⟩
  obtain ⟨y, hyt, a, haint, hfa⟩ := Set.mem_iUnion₂.mp (ht hw)
  exact ⟨a, Set.mem_biUnion hyt (interior_subset haint), hfa⟩

/-- **Backward invariance of the Fatou set**: if `f z` is a Fatou point,
so is `z`. -/
theorem mem_fatouSet_of_apply_mem {f : ℂ̂ → ℂ̂} (hf : Continuous f) {z : ℂ̂}
    (h : f z ∈ FatouSet f) : z ∈ FatouSet f := by
  classical
  obtain ⟨U, hU, hN⟩ := h
  refine ⟨f ⁻¹' U, hf.continuousAt.preimage_mem_nhds hU, fun seq => ?_⟩
  choose m hm using fun n => (seq n).2
  by_cases hinf : {n : ℕ | m n = 0}.Infinite
  · -- the identity `f^[0]` occurs infinitely often: constant subsequence
    have hfreq : ∃ᶠ n in Filter.atTop, m n = 0 :=
      Nat.frequently_atTop_iff_infinite.mpr hinf
    obtain ⟨ψ, hψ, hψ0⟩ := Filter.extraction_of_frequently_atTop hfreq
    have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => (id : ℂ̂ → ℂ̂)) id
        Filter.atTop (f ⁻¹' U) := by
      intro u hu w _
      exact ⟨f ⁻¹' U, self_mem_nhdsWithin,
        Filter.Eventually.of_forall fun n y _ => refl_mem_uniformity hu⟩
    refine ⟨ψ, hψ, id, hbase.congr fun j y _ => ?_⟩
    have h1 : (seq (ψ j) : ℂ̂ → ℂ̂) y = f^[m (ψ j)] y := (congrFun (hm (ψ j)) y).symm
    rw [h1, hψ0 j, Function.iterate_zero]
  · -- cofinitely many indices have `m n ≥ 1`: factor through `f`
    have hfin : {n : ℕ | m n = 0}.Finite := Set.not_infinite.mp hinf
    have hfreq : ∃ᶠ n in Filter.atTop, m n ≠ 0 :=
      Nat.frequently_atTop_iff_infinite.mpr hfin.infinite_compl
    obtain ⟨ψ, hψ, hψ1⟩ := Filter.extraction_of_frequently_atTop hfreq
    obtain ⟨φ', hφ', g, hg⟩ := hN fun j => ⟨f^[m (ψ j) - 1], m (ψ j) - 1, rfl⟩
    have hg' : TendstoLocallyUniformlyOn (fun j => f^[m (ψ (φ' j)) - 1]) g
        Filter.atTop U := hg
    have hcomp := hg'.comp f (Set.mapsTo_preimage f U) hf.continuousOn
    refine ⟨ψ ∘ φ', hψ.comp hφ', g ∘ f, hcomp.congr fun j y _ => ?_⟩
    have hms : m (ψ (φ' j)) - 1 + 1 = m (ψ (φ' j)) :=
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hψ1 (φ' j)))
    calc (f^[m (ψ (φ' j)) - 1] ∘ f) y
        = f^[m (ψ (φ' j)) - 1 + 1] y := (Function.iterate_succ_apply f _ y).symm
      _ = (seq ((ψ ∘ φ') j) : ℂ̂ → ℂ̂) y := by
          rw [hms]; exact congrFun (hm (ψ (φ' j))) y

/-- **Forward invariance of the Fatou set**: if `z` is a Fatou point, so is
`f z`. Openness of `f` is the only hypothesis needed. -/
theorem apply_mem_fatouSet {f : ℂ̂ → ℂ̂} (hfo : IsOpenMap f) {z : ℂ̂}
    (h : z ∈ FatouSet f) : f z ∈ FatouSet f := by
  classical
  obtain ⟨U₀, hU₀, hN₀⟩ := h
  obtain ⟨U, hU, hzU, hN⟩ : ∃ U : Set ℂ̂, IsOpen U ∧ z ∈ U ∧
      IsNormal (Set.range fun n : ℕ => f^[n]) U := by
    refine ⟨interior U₀, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU₀,
      fun seq => ?_⟩
    obtain ⟨φ, hφ, g, hg⟩ := hN₀ seq
    exact ⟨φ, hφ, g, hg.mono interior_subset⟩
  have hV : IsOpen (f '' U) := hfo U hU
  refine ⟨f '' U, hV.mem_nhds ⟨z, hzU, rfl⟩, fun seq => ?_⟩
  choose m hm using fun n => (seq n).2
  obtain ⟨φ, hφ, gU, hlim⟩ := hN fun j => ⟨f^[m j + 1], m j + 1, rfl⟩
  have hlim' : TendstoLocallyUniformlyOn (fun j => f^[m (φ j) + 1]) gU
      Filter.atTop U := hlim
  -- the limit is constant on the fibres of `f` over `U`
  have hfib : ∀ x ∈ U, ∀ x' ∈ U, f x = f x' → gU x = gU x' := by
    intro x hx x' hx' hxx'
    have h1 : Filter.Tendsto (fun j => f^[m (φ j) + 1] x) Filter.atTop
        (nhds (gU x)) := hlim'.tendsto_at hx
    have h2 : Filter.Tendsto (fun j => f^[m (φ j) + 1] x') Filter.atTop
        (nhds (gU x')) := hlim'.tendsto_at hx'
    have heq : (fun j => f^[m (φ j) + 1] x) = fun j => f^[m (φ j) + 1] x' := by
      funext j
      have e1 : f^[m (φ j) + 1] x = f^[m (φ j)] (f x) :=
        Function.iterate_succ_apply f _ x
      have e2 : f^[m (φ j) + 1] x' = f^[m (φ j)] (f x') :=
        Function.iterate_succ_apply f _ x'
      rw [e1, e2, hxx']
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  -- locally uniform convergence on `f '' U` of the un-shifted subsequence,
  -- towards any function `H` with `H ∘ f = gU` on `U`
  have main : ∀ H : ℂ̂ → ℂ̂, (∀ x ∈ U, H (f x) = gU x) →
      TendstoLocallyUniformlyOn (fun j => f^[m (φ j)]) H Filter.atTop (f '' U) := by
    intro H hHf
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hV]
    intro K hKV hK
    obtain ⟨K', hK'c, hK'U, hKK'⟩ :=
      exists_isCompact_subset_of_isCompact_subset_image hfo hU hK hKV
    have huK' : TendstoUniformlyOn (fun j => f^[m (φ j) + 1]) gU Filter.atTop K' :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim' K' hK'U hK'c
    rw [Metric.tendstoUniformlyOn_iff] at huK' ⊢
    intro ε hε
    filter_upwards [huK' ε hε] with j hj y hy
    obtain ⟨x, hxK', rfl⟩ := hKK' hy
    have hstep : f^[m (φ j)] (f x) = f^[m (φ j) + 1] x :=
      (Function.iterate_succ_apply f _ x).symm
    calc dist (H (f x)) (f^[m (φ j)] (f x))
        = dist (gU x) (f^[m (φ j) + 1] x) := by rw [hHf x (hK'U hxK'), hstep]
      _ < ε := hj x hxK'
  refine ⟨φ, hφ,
    fun y => if hy : ∃ x', x' ∈ U ∧ f x' = y then gU hy.choose else gU y, ?_⟩
  have hHf : ∀ x ∈ U,
      (fun y => if hy : ∃ x', x' ∈ U ∧ f x' = y then gU hy.choose else gU y) (f x)
        = gU x := by
    intro x hx
    have hex : ∃ x', x' ∈ U ∧ f x' = f x := ⟨x, hx, rfl⟩
    have hsel : (fun y => if hy : ∃ x', x' ∈ U ∧ f x' = y then gU hy.choose else gU y)
        (f x) = gU hex.choose := dif_pos hex
    rw [hsel]
    exact hfib _ hex.choose_spec.1 x hx hex.choose_spec.2
  exact (main _ hHf).congr fun j y _ => congrFun (hm (φ j)) y

/-- **Complete invariance of the Fatou set** (preimage form). -/
theorem fatouSet_preimage_eq {f : ℂ̂ → ℂ̂} (hf : Continuous f)
    (hfo : IsOpenMap f) : f ⁻¹' (FatouSet f) = FatouSet f := by
  ext w
  exact ⟨fun hw => mem_fatouSet_of_apply_mem hf hw,
    fun hw => apply_mem_fatouSet hfo hw⟩

/-- **Complete invariance of the Julia set** (preimage form). -/
theorem juliaSet_preimage_eq {f : ℂ̂ → ℂ̂} (hf : Continuous f)
    (hfo : IsOpenMap f) : f ⁻¹' (JuliaSet f) = JuliaSet f := by
  change f ⁻¹' (FatouSet f)ᶜ = (FatouSet f)ᶜ
  rw [Set.preimage_compl, fatouSet_preimage_eq hf hfo]

/-- **Complete invariance of the Fatou set** (image form, for surjective
`f`). -/
theorem fatouSet_image_eq {f : ℂ̂ → ℂ̂} (hf : Continuous f)
    (hfo : IsOpenMap f) (hsurj : Function.Surjective f) :
    f '' (FatouSet f) = FatouSet f := by
  conv_lhs => rw [← fatouSet_preimage_eq hf hfo]
  exact Set.image_preimage_eq _ hsurj

/-- **Complete invariance of the Julia set** (image form, for surjective
`f`). -/
theorem juliaSet_image_eq {f : ℂ̂ → ℂ̂} (hf : Continuous f)
    (hfo : IsOpenMap f) (hsurj : Function.Surjective f) :
    f '' (JuliaSet f) = JuliaSet f := by
  conv_lhs => rw [← juliaSet_preimage_eq hf hfo]
  exact Set.image_preimage_eq _ hsurj

/-! ## Rational-map instantiations

A rational map of degree at least one is continuous, open, and surjective
(`Sphere/OpenMapping.lean`), so the invariance theorems above apply. -/

/-- **Complete invariance of the Fatou set of a rational map** (preimage
form). -/
theorem fatouSet_preimage_eq_of_isRational {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f) :
    f ⁻¹' (FatouSet f) = FatouSet f := by
  have hc := hf.continuous
  have hnc := hf.ne_const hd
  have ho := hf.isOpenMap hnc
  exact fatouSet_preimage_eq hc ho

/-- **Complete invariance of the Julia set of a rational map** (preimage
form). -/
theorem juliaSet_preimage_eq_of_isRational {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f) :
    f ⁻¹' (JuliaSet f) = JuliaSet f := by
  have hc := hf.continuous
  have hnc := hf.ne_const hd
  have ho := hf.isOpenMap hnc
  exact juliaSet_preimage_eq hc ho

/-- **Complete invariance of the Fatou set of a rational map** (image
form). -/
theorem fatouSet_image_eq_of_isRational {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f) :
    f '' (FatouSet f) = FatouSet f := by
  have hc := hf.continuous
  have hnc := hf.ne_const hd
  have ho := hf.isOpenMap hnc
  have hs := hf.surjective hnc
  exact fatouSet_image_eq hc ho hs

/-- **Complete invariance of the Julia set of a rational map** (image
form). -/
theorem juliaSet_image_eq_of_isRational {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f) :
    f '' (JuliaSet f) = JuliaSet f := by
  have hc := hf.continuous
  have hnc := hf.ne_const hd
  have ho := hf.isOpenMap hnc
  have hs := hf.surjective hnc
  exact juliaSet_image_eq hc ho hs

end NoWanderingDomains
