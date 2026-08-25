/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.FatouComponents.Periodic
import NoWanderingDomains.Dynamics.JuliaFatou.RepellingDensity
import NoWanderingDomains.Analysis.Winding.GridPrimitives.Primitives
import RMT4.Main
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Fiber counts on a wandering orbit

Frontier containment in the Julia set, the avoidance index, image behavior of
the component orbit, compactness of fibers, the eventually-defined fiber count,
and injectivity once the count is one — culminating in the simply-connected
criterion forcing the count to one.
-/

open Function OnePoint Filter Topology

namespace NoWanderingDomains

/-- The frontier of a Fatou component is contained in the Julia set: the
Fatou set is open, so a frontier point of the component that were in the
Fatou set would lie in the interior of some component meeting `U`, hence in
`U` itself — contradicting that an open set is disjoint from its own
frontier. -/
theorem IsFatouComponent.frontier_subset_juliaSet {f : ℂ̂ → ℂ̂} {U : Set ℂ̂}
    (hU : IsFatouComponent f U) :
    frontier U ⊆ JuliaSet f := by
  intro x hx
  rw [hU.isOpen.frontier_eq] at hx
  obtain ⟨hxcl, hxU⟩ := hx
  by_contra hxJ
  have hxF : x ∈ FatouSet f := by
    by_contra h
    exact hxJ h
  set W := connectedComponentIn (FatouSet f) x with hW
  have hWfc : IsFatouComponent f W := isFatouComponent_connectedComponentIn hxF
  have hxW : x ∈ W := mem_connectedComponentIn hxF
  obtain ⟨y, hyW, hyU⟩ := mem_closure_iff.mp hxcl W hWfc.isOpen hxW
  have hWU : W = U := hWfc.eq_of_mem hU hyW hyU
  exact hxU (hWU ▸ hxW)

/-- **Avoidance pigeonhole.** Along a wandering orbit the components are
pairwise disjoint, so `∞` (one point) and the critical points of `f`
(finitely many, as zeros of the wronskian reading together with the finitely
many `∞`-chart criticalities) meet only finitely many orbit components: from
some index on, every orbit component avoids `∞` and contains no critical
point of `f`. -/
theorem exists_avoidance_index {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (_hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ N : ℕ, ∀ n : ℕ,
      ∞ ∉ fcOrbit f U (N + n) ∧
      ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U (N + n)) →
        deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0 := by
  classical
  obtain ⟨r, hr⟩ := hf
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  -- The bad set on the sphere: `∞` together with the (finitely many) zeros of
  -- the wronskian and of the reduced denominator, read into `ℂ̂`.
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  obtain ⟨B, hBdef⟩ : ∃ s : Set ℂ̂,
      s = (fun x : ℂ => ((x : ℂ̂))) ''
          ({x : ℂ | r.wronskian.IsRoot x} ∪ {x : ℂ | r.denReduced.IsRoot x})
        ∪ {∞} := ⟨_, rfl⟩
  have hBfin : B.Finite := by
    rw [hBdef]
    exact (((Polynomial.finite_setOfPred_isRoot hWr).union
      (Polynomial.finite_setOfPred_isRoot hdenR)).image _).union (Set.finite_singleton _)
  -- Indices whose orbit component meets the bad set; a choice of witness.
  obtain ⟨S, hSdef⟩ : ∃ s : Set ℕ,
      s = {m : ℕ | (fcOrbit f U m ∩ B).Nonempty} := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ̂, g = fun m =>
      if h : (fcOrbit f U m ∩ B).Nonempty then h.choose else ∞ := ⟨_, rfl⟩
  have hgmem : ∀ m ∈ S, g m ∈ fcOrbit f U m ∩ B := by
    intro m hm
    have hm' : (fcOrbit f U m ∩ B).Nonempty := by rw [hSdef] at hm; exact hm
    rw [hgdef]
    change (if h : (fcOrbit f U m ∩ B).Nonempty then h.choose else ∞)
        ∈ fcOrbit f U m ∩ B
    rw [dif_pos hm']
    exact hm'.choose_spec
  -- Pairwise disjointness of the orbit makes the witness injective on `S`.
  have hinj : Set.InjOn g S := by
    intro m hm m' hm' heq
    by_contra hne
    have hdisj : Disjoint (fcOrbit f U m) (fcOrbit f U m') := hW hne
    exact Set.disjoint_left.mp hdisj (hgmem m hm).1 (heq ▸ (hgmem m' hm').1)
  have hSfin : S.Finite :=
    Set.Finite.of_finite_image
      (hBfin.subset (by rintro _ ⟨m, hm, rfl⟩; exact (hgmem m hm).2)) hinj
  obtain ⟨N₀, hN₀⟩ := hSfin.bddAbove
  refine ⟨N₀ + 1, fun n => ?_⟩
  have hnotS : N₀ + 1 + n ∉ S := by
    intro hmem
    have := hN₀ hmem
    omega
  have hempty : ∀ b : ℂ̂, b ∈ fcOrbit f U (N₀ + 1 + n) → b ∉ B := by
    intro b hb hbB
    exact hnotS (by rw [hSdef]; exact ⟨b, hb, hbB⟩)
  constructor
  · intro hinf
    exact hempty ∞ hinf (by rw [hBdef]; exact Set.mem_union_right _ rfl)
  · intro z hz
    have hzB : ((z : ℂ̂)) ∉ B := hempty _ hz
    have hWz : r.wronskian.eval z ≠ 0 := fun h0 =>
      hzB (by rw [hBdef]; exact Set.mem_union_left _ ⟨z, Or.inl h0, rfl⟩)
    have hdz : r.denReduced.eval z ≠ 0 := fun h0 =>
      hzB (by rw [hBdef]; exact Set.mem_union_left _ ⟨z, Or.inr h0, rfl⟩)
    rw [hr, r.deriv_reading hdz]
    exact div_ne_zero hWz (pow_ne_zero 2 hdz)

/-- **Component maps are surjective**: a rational map of degree at least one
sends each orbit component onto the next. The image is open (rational maps
are open) and relatively closed in the connected target component (a
boundary point of the image inside the target would be the image of a
boundary point of the source, but frontiers of Fatou components map into the
Julia set), hence clopen and nonempty. -/
theorem fcOrbit_image_eq {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ) :
    f '' fcOrbit f U n = fcOrbit f U (n + 1) := by
  have hnc := hf.ne_const hd
  have hfo : IsOpenMap f := hf.isOpenMap hnc
  have hc : Continuous f := hf.continuous
  obtain ⟨z₀, hz₀⟩ := hU.nonempty
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd hU
  have hSeq : S = connectedComponentIn (FatouSet f) (f^[n] z₀) :=
    fcOrbit_eq_connectedComponentIn n hf hd hU hz₀
  have hTeq : T = connectedComponentIn (FatouSet f) (f^[n + 1] z₀) :=
    fcOrbit_eq_connectedComponentIn (n + 1) hf hd hU hz₀
  have hiter : ∀ k : ℕ, f^[k] z₀ ∈ FatouSet f := by
    intro k
    induction k with
    | zero => simpa using hU.subset_fatouSet hz₀
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact apply_mem_fatouSet hfo ih
  have hbaseS : f^[n] z₀ ∈ S := by
    rw [hSeq]; exact mem_connectedComponentIn (hiter n)
  have hbaseT : f^[n + 1] z₀ ∈ T := by
    rw [hTeq]; exact mem_connectedComponentIn (hiter (n + 1))
  have himgBase : f^[n + 1] z₀ ∈ f '' S := by
    rw [Function.iterate_succ_apply']
    exact ⟨f^[n] z₀, hbaseS, rfl⟩
  -- the image lies inside the target component
  have hsub : f '' S ⊆ T := by
    have hpre : IsPreconnected (f '' S) :=
      (hSfc.isConnected.isPreconnected).image f hc.continuousOn
    have hFat : f '' S ⊆ FatouSet f := by
      rintro _ ⟨x, hx, rfl⟩
      exact apply_mem_fatouSet hfo (hSfc.subset_fatouSet hx)
    rw [hTeq]
    exact hpre.subset_connectedComponentIn himgBase hFat
  -- the image is open
  have hopen : IsOpen (f '' S) := hfo _ hSfc.isOpen
  -- the image is relatively closed in the target component
  have hclosed : T ∩ closure (f '' S) ⊆ f '' S := by
    have hclosSub : closure (f '' S) ⊆ f '' closure S := by
      have hcpt : IsCompact (closure S) := isClosed_closure.isCompact
      exact closure_minimal (Set.image_mono subset_closure)
        (hcpt.image hc).isClosed
    rintro w ⟨hwT, hwc⟩
    obtain ⟨x, hx, rfl⟩ := hclosSub hwc
    rw [closure_eq_interior_union_frontier, hSfc.isOpen.interior_eq] at hx
    rcases hx with hxS | hxfr
    · exact ⟨x, hxS, rfl⟩
    · exfalso
      have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
      have hfxJ : f x ∈ JuliaSet f := by
        rw [← juliaSet_preimage_eq_of_isRational hf hd] at hxJ
        exact hxJ
      exact hfxJ (hTfc.subset_fatouSet hwT)
  -- nonempty clopen subset of the connected target component
  have hTsub : T ⊆ f '' S := by
    intro w hw
    by_cases hwc : w ∈ closure (f '' S)
    · exact hclosed ⟨hw, hwc⟩
    · exfalso
      have hcover : T ⊆ f '' S ∪ (closure (f '' S))ᶜ := by
        intro y hy
        by_cases h : y ∈ closure (f '' S)
        · exact Or.inl (hclosed ⟨hy, h⟩)
        · exact Or.inr h
      obtain ⟨x, _, hxu, hxv⟩ :=
        hTfc.isConnected.isPreconnected (f '' S) (closure (f '' S))ᶜ hopen
          isClosed_closure.isOpen_compl hcover ⟨f^[n + 1] z₀, hbaseT, himgBase⟩
          ⟨w, hw, hwc⟩
      exact hxv (subset_closure hxu)
  exact Set.Subset.antisymm hsub hTsub

/-- **Properness of the component restriction, fiber form**: the fiber of
the component map over an interior point of the target component is compact
— it is the intersection of the compact global fiber with the source
component, and no boundary point of the source can map into the (Fatou)
target since frontiers map into the Julia set. -/
theorem isCompact_fiber_inter {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    {w : ℂ̂} (hw : w ∈ fcOrbit f U (n + 1)) :
    IsCompact (f ⁻¹' {w} ∩ fcOrbit f U n) := by
  set S := fcOrbit f U n with hS
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd hU
  have hwF : w ∈ FatouSet f :=
    (isFatouComponent_fcOrbit (n + 1) hf hd hU).subset_fatouSet hw
  have hkey : f ⁻¹' {w} ∩ S = f ⁻¹' {w} ∩ closure S := by
    apply Set.Subset.antisymm
    · exact Set.inter_subset_inter_right _ subset_closure
    · rintro x ⟨hxf, hxcl⟩
      refine ⟨hxf, ?_⟩
      by_contra hxS
      have hxfr : x ∈ frontier S := by
        rw [hSfc.isOpen.frontier_eq]
        exact ⟨hxcl, hxS⟩
      have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
      rw [← juliaSet_preimage_eq_of_isRational hf hd] at hxJ
      have hfw : f x = w := hxf
      rw [Set.mem_preimage, hfw] at hxJ
      exact hxJ hwF
  rw [hkey]
  exact ((IsClosed.preimage hf.continuous isClosed_singleton).inter
    isClosed_closure).isCompact

/-- **Constant fiber count**: when the source component contains neither `∞`
nor critical points, the component map is a proper local homeomorphism onto
the connected target, so its fiber cardinality is finite, positive, and the
same over every target point (stack of records: finitely many disjoint local
sheets plus the properness exclusion of stray preimages). -/
theorem exists_fiberCount {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd1 hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have himg : f '' S = T := fcOrbit_image_eq hf hd1 hU n
  have cf : ∀ t : ℂ, chartFiniteMap ((t : ℂ̂)) = t := fun _ => rfl
  have hread : ∀ t : ℂ, r.toSphereMap ((t : ℂ̂))
      = if r.denReduced.eval t = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval t / r.denReduced.eval t : ℂ) : ℂ̂) := fun _ => rfl
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  -- Stage 0: on `S` the reduced denominator does not vanish (a pole would make
  -- the finite-chart reading discontinuous, hence with zero `deriv`).
  have hden_ne : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → r.denReduced.eval x ≠ 0 := by
    intro x hxS h0
    have hcx := hcrit x hxS
    have hdiff : DifferentiableAt ℂ (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) x := by
      by_contra hnd
      exact hcx (deriv_zero_of_not_differentiableAt hnd)
    have hφx : chartFiniteMap (f ((x : ℂ̂))) = 0 := by
      rw [hr, hread x, if_pos h0]
      rfl
    -- eventually on the punctured neighbourhood the denominator is nonzero
    have hZfin : {t : ℂ | r.denReduced.IsRoot t}.Finite :=
      Polynomial.finite_setOfPred_isRoot hdenR
    have hclosed : IsClosed ({t : ℂ | r.denReduced.IsRoot t} \ {x}) :=
      (hZfin.subset Set.sdiff_subset).isClosed
    have hxmem : x ∈ ({t : ℂ | r.denReduced.IsRoot t} \ {x})ᶜ := fun h => h.2 rfl
    have hev_ne : ∀ᶠ t in 𝓝[≠] x, r.denReduced.eval t ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hxmem),
        self_mem_nhdsWithin] with t ht htx
      exact fun h0t => ht ⟨h0t, htx⟩
    -- two incompatible limits along the punctured neighbourhood
    have h1 : Tendsto (fun t : ℂ => f ((t : ℂ̂))) (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) := by
      have hc : ContinuousAt (fun t : ℂ => f ((t : ℂ̂))) x :=
        (hf.continuous.comp OnePoint.continuous_coe).continuousAt
      have hfx : f ((x : ℂ̂)) = ∞ := by rw [hr, hread x, if_pos h0]
      have h := hc.tendsto
      rw [hfx] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (((0 : ℂ) : ℂ̂))) := by
      have hφt := hdiff.continuousAt.tendsto
      rw [hφx] at hφt
      exact ((OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hφt).mono_left
        nhdsWithin_le_nhds
    have heq : (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        =ᶠ[𝓝[≠] x] fun t : ℂ => f ((t : ℂ̂)) := by
      filter_upwards [hev_ne] with t ht
      rw [hr, hread t, if_neg ht, cf]
    have h1' : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) h1
    exact OnePoint.coe_ne_infty (0 : ℂ) (tendsto_nhds_unique h2 h1')
  -- values on `S` are finite
  have hSfin : ∀ u ∈ S, f u ≠ ∞ := by
    intro u huS
    have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
    rw [hr, hread x, if_neg (hden_ne x huS)]
    exact OnePoint.coe_ne_infty _
  have hTfin : ∀ w ∈ T, ∃ y : ℂ, w = ((y : ℂ̂)) := by
    intro w hwT
    rw [← himg] at hwT
    obtain ⟨u, huS, rfl⟩ := hwT
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp (hSfin u huS)
    exact ⟨y, hy.symm⟩
  -- Stage 1: fibers over finite points are finite (they are root sets of the
  -- nonzero polynomial `num - y·den`; its vanishing would kill the Wronskian).
  have hfib_fin : ∀ y : ℂ, (f ⁻¹' {((y : ℂ̂))} ∩ S).Finite := by
    intro y
    have hq : r.numReduced - Polynomial.C y * r.denReduced ≠ 0 := by
      intro h0
      apply hWr
      have hnum : r.numReduced = Polynomial.C y * r.denReduced := sub_eq_zero.mp h0
      unfold RationalData.wronskian
      rw [hnum, Polynomial.derivative_C_mul]
      ring
    have hsub : f ⁻¹' {((y : ℂ̂))} ∩ S ⊆ (fun x : ℂ => ((x : ℂ̂))) ''
        {x : ℂ | (r.numReduced - Polynomial.C y * r.denReduced).IsRoot x} := by
      rintro u ⟨hufy, huS⟩
      have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
      obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
      have hden := hden_ne x huS
      have hfx : f ((x : ℂ̂)) = ((y : ℂ̂)) := hufy
      rw [hr, hread x, if_neg hden] at hfx
      have hdiv : r.numReduced.eval x / r.denReduced.eval x = y :=
        OnePoint.coe_eq_coe.mp hfx
      rw [div_eq_iff hden] at hdiv
      refine ⟨x, ?_, rfl⟩
      change (r.numReduced - Polynomial.C y * r.denReduced).eval x = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hdiv, sub_self]
    exact ((Polynomial.finite_setOfPred_isRoot hq).image _).subset hsub
  -- Local injectivity: near each finite non-critical point `f` is injective
  have hloc : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → ∃ Wc : Set ℂ, IsOpen Wc ∧ x ∈ Wc ∧
      ∀ t₁ ∈ Wc, ∀ t₂ ∈ Wc, f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) → t₁ = t₂ := by
    intro x hxS
    have hcx := hcrit x hxS
    have hden := hden_ne x hxS
    have hev : (fun t : ℂ => r.numReduced.eval t / r.denReduced.eval t)
        =ᶠ[𝓝 x] fun t : ℂ => chartFiniteMap (f ((t : ℂ̂))) := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with t ht
      rw [hr, hread t, if_neg ht, cf]
    obtain ⟨D, hstrict⟩ : ∃ D : ℂ,
        HasStrictDerivAt (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) D x :=
      ⟨_, ((r.numReduced.hasStrictDerivAt x).div
        (r.denReduced.hasStrictDerivAt x) hden).congr_of_eventuallyEq hev⟩
    have hD : D ≠ 0 := hstrict.hasDerivAt.deriv ▸ hcx
    obtain ⟨Wc, hWsub, hWopen, hxW⟩ :=
      mem_nhds_iff.mp (hstrict.eventually_left_inverse hD)
    refine ⟨Wc, hWopen, hxW, ?_⟩
    intro t₁ ht₁ t₂ ht₂ hft
    have h₁ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₁ : ℂ̂)))) = t₁ := hWsub ht₁
    have h₂ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₂ : ℂ̂)))) = t₂ := hWsub ht₂
    rw [← h₁, hft, h₂]
  -- `S` read in the finite chart is open
  have hScopen : IsOpen ((fun t : ℂ => ((t : ℂ̂))) ⁻¹' S) :=
    hSfc.isOpen.preimage OnePoint.continuous_coe
  -- Stage 2: the fiber count is locally constant on `T`
  have hlc : ∀ w₀ ∈ T, ∃ P : Set ℂ̂, P ∈ 𝓝 w₀ ∧ ∀ w ∈ P ∩ T,
      (f ⁻¹' {w} ∩ S).ncard = (f ⁻¹' {w₀} ∩ S).ncard := by
    intro w₀ hw₀T
    obtain ⟨a, rfl⟩ := hTfin w₀ hw₀T
    -- the fiber over the base point, read in the finite chart
    obtain ⟨Fc, hFcdef⟩ : ∃ s : Set ℂ,
        s = (fun t : ℂ => ((t : ℂ̂))) ⁻¹' (f ⁻¹' {((a : ℂ̂))} ∩ S) := ⟨_, rfl⟩
    have hFc_fin : Fc.Finite := by
      rw [hFcdef]
      exact (hfib_fin a).preimage OnePoint.coe_injective.injOn
    have hFC : f ⁻¹' {((a : ℂ̂))} ∩ S = (fun t : ℂ => ((t : ℂ̂))) '' Fc := by
      apply Set.Subset.antisymm
      · rintro u ⟨huf, huS⟩
        have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
        obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
        exact ⟨x, by rw [hFcdef]; exact ⟨huf, huS⟩, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [hFcdef] at hx
        exact hx
    have hFcS : ∀ x ∈ Fc, ((x : ℂ̂)) ∈ S := by
      intro x hx; rw [hFcdef] at hx; exact hx.2
    have hFcf : ∀ x ∈ Fc, f ((x : ℂ̂)) = ((a : ℂ̂)) := by
      intro x hx; rw [hFcdef] at hx; exact hx.1
    -- one local record per fiber point: a branch through it, staying in `S`,
    -- with a capture neighbourhood on which it collects all preimages
    have hrec : ∀ x : ℂ, ∃ (V : Set ℂ) (g : ℂ → ℂ) (O : Set ℂ̂), x ∈ Fc →
        (IsOpen V ∧ a ∈ V ∧ ContinuousOn g V ∧ g a = x ∧
          (∀ y ∈ V, f ((g y : ℂ̂)) = ((y : ℂ̂)) ∧ ((g y : ℂ̂)) ∈ S) ∧
          O ∈ 𝓝 ((x : ℂ̂)) ∧
          (∀ u ∈ O, ∀ y ∈ V, f u = ((y : ℂ̂)) → u = ((g y : ℂ̂)))) := by
      intro x
      by_cases hx : x ∈ Fc
      swap
      · exact ⟨∅, id, ∅, fun h => absurd h hx⟩
      have hxS : ((x : ℂ̂)) ∈ S := hFcS x hx
      obtain ⟨V₀, g, hV₀open, haV₀, hga, hgdiff, hbr⟩ :=
        exists_branch_of_deriv_ne_zero hf (hFcf x hx) (hcrit x hxS)
      obtain ⟨Wc, hWopen, hxW, hWinj⟩ := hloc x hxS
      refine ⟨V₀ ∩ g ⁻¹' (Wc ∩ (fun t : ℂ => ((t : ℂ̂))) ⁻¹' S), g,
        (fun t : ℂ => ((t : ℂ̂))) '' Wc, fun _ => ⟨?_, ⟨haV₀, ?_⟩,
          hgdiff.continuousOn.mono Set.inter_subset_left, hga, ?_, ?_, ?_⟩⟩
      · exact hgdiff.continuousOn.isOpen_inter_preimage hV₀open
          (hWopen.inter hScopen)
      · rw [Set.mem_preimage, hga]
        exact ⟨hxW, hxS⟩
      · intro y hy
        exact ⟨hbr y hy.1, hy.2.2⟩
      · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
          Set.preimage_image_eq _ OnePoint.coe_injective]
        exact hWopen.mem_nhds hxW
      · rintro _ ⟨t, htW, rfl⟩ y hyV hfu
        have hteq : f ((t : ℂ̂)) = f ((g y : ℂ̂)) := by
          rw [hfu, hbr y hyV.1]
        rw [hWinj t htW (g y) hyV.2.1 hteq]
    choose Vr gr Onb hrec using hrec
    have hVor : ∀ x ∈ Fc, IsOpen (Vr x) := fun x hx => (hrec x hx).1
    have haVr : ∀ x ∈ Fc, a ∈ Vr x := fun x hx => (hrec x hx).2.1
    have hgcr : ∀ x ∈ Fc, ContinuousOn (gr x) (Vr x) := fun x hx => (hrec x hx).2.2.1
    have hgar : ∀ x ∈ Fc, gr x a = x := fun x hx => (hrec x hx).2.2.2.1
    have hbrr : ∀ x ∈ Fc, ∀ y ∈ Vr x,
        f ((gr x y : ℂ̂)) = ((y : ℂ̂)) ∧ ((gr x y : ℂ̂)) ∈ S :=
      fun x hx => (hrec x hx).2.2.2.2.1
    have hOnr : ∀ x ∈ Fc, Onb x ∈ 𝓝 ((x : ℂ̂)) := fun x hx => (hrec x hx).2.2.2.2.2.1
    have hcapr : ∀ x ∈ Fc, ∀ u ∈ Onb x, ∀ y ∈ Vr x,
        f u = ((y : ℂ̂)) → u = ((gr x y : ℂ̂)) :=
      fun x hx => (hrec x hx).2.2.2.2.2.2
    -- stray exclusion: near `↑a` every preimage in `S` is captured by a record
    have hexcl : ∃ N ∈ 𝓝 ((a : ℂ̂)), ∀ u, f u ∈ N → u ∈ S → ∃ x ∈ Fc, u ∈ Onb x := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ℱ, hℱdef⟩ : ∃ F : Filter ℂ̂,
          F = Filter.comap f (𝓝 ((a : ℂ̂))) ⊓ 𝓟 (S \ ⋃ x ∈ Fc, Onb x) := ⟨_, rfl⟩
      have hneF : ℱ.NeBot := by
        rw [hℱdef, Filter.inf_principal_neBot_iff]
        intro Uf hUf
        obtain ⟨N, hN, hNsub⟩ := Filter.mem_comap.mp hUf
        obtain ⟨u, hfu, huS, hustray⟩ := hcon N hN
        refine ⟨u, hNsub hfu, huS, ?_⟩
        intro hmem
        obtain ⟨x, hx, hux⟩ := Set.mem_iUnion₂.mp hmem
        exact hustray x hx hux
      have hle : ℱ ≤ 𝓟 (closure S) := by
        rw [hℱdef]
        exact le_trans inf_le_right
          (Filter.principal_mono.mpr (Set.sdiff_subset.trans subset_closure))
      obtain ⟨u, hucl, hclust⟩ := isClosed_closure.isCompact.exists_clusterPt hle
      have hfu : f u = ((a : ℂ̂)) := by
        have ht : Tendsto f ℱ (𝓝 ((a : ℂ̂))) := by
          rw [hℱdef]
          exact Filter.tendsto_iff_comap.mpr inf_le_left
        exact eq_of_nhds_neBot (hclust.map hf.continuous.continuousAt ht)
      have huS : u ∈ S := by
        by_contra huS
        have hufr : u ∈ frontier S := by
          rw [hSfc.isOpen.frontier_eq]
          exact ⟨hucl, huS⟩
        have huJ : u ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hufr
        rw [← juliaSet_preimage_eq_of_isRational hf hd1] at huJ
        have huJ' : f u ∈ JuliaSet f := huJ
        rw [hfu] at huJ'
        exact huJ' (hTfc.subset_fatouSet hw₀T)
      have humem : u ∈ (fun t : ℂ => ((t : ℂ̂))) '' Fc := by
        rw [← hFC]
        exact ⟨hfu, huS⟩
      obtain ⟨x, hxFc, rfl⟩ := humem
      have hstray : (S \ ⋃ x ∈ Fc, Onb x) ∈ ℱ := by
        rw [hℱdef]
        exact Filter.mem_inf_of_right (Filter.mem_principal_self _)
      have : (𝓝 ((x : ℂ̂)) ⊓ ℱ).NeBot := hclust
      obtain ⟨v, hvO, hvS⟩ := Filter.nonempty_of_mem
        (Filter.inter_mem (Filter.mem_inf_of_left (hOnr x hxFc))
          (Filter.mem_inf_of_right hstray))
      exact hvS.2 (Set.mem_iUnion₂.mpr ⟨x, hxFc, hvO⟩)
    obtain ⟨N, hNnhds, hNcap⟩ := hexcl
    -- the final branch domain: common, with pairwise-distinct branch values,
    -- and mapping into the capture neighbourhood
    obtain ⟨Vfin, hVfindef⟩ : ∃ V : Set ℂ, V =
        ((⋂ x ∈ Fc, Vr x) ∩
          ⋂ x₁ ∈ Fc, ⋂ x₂ ∈ Fc, ite (x₁ = x₂) Set.univ
            ((Vr x₁ ∩ Vr x₂) ∩ (fun y => gr x₁ y - gr x₂ y) ⁻¹' {(0 : ℂ)}ᶜ)) ∩
          (fun t : ℂ => ((t : ℂ̂))) ⁻¹' interior N := ⟨_, rfl⟩
    have hVfin_open : IsOpen Vfin := by
      rw [hVfindef]
      refine (IsOpen.inter (hFc_fin.isOpen_biInter hVor) ?_).inter
        (isOpen_interior.preimage OnePoint.continuous_coe)
      refine hFc_fin.isOpen_biInter fun x₁ hx₁ => hFc_fin.isOpen_biInter fun x₂ hx₂ => ?_
      split_ifs with h12
      · exact isOpen_univ
      · exact ContinuousOn.isOpen_inter_preimage
          (((hgcr x₁ hx₁).mono Set.inter_subset_left).sub
            ((hgcr x₂ hx₂).mono Set.inter_subset_right))
          ((hVor x₁ hx₁).inter (hVor x₂ hx₂)) isOpen_compl_singleton
    have haVfin : a ∈ Vfin := by
      rw [hVfindef]
      refine ⟨⟨Set.mem_iInter₂.mpr haVr, ?_⟩, ?_⟩
      · refine Set.mem_iInter₂.mpr fun x₁ hx₁ => Set.mem_iInter₂.mpr fun x₂ hx₂ => ?_
        split_ifs with h12
        · trivial
        · refine ⟨⟨haVr x₁ hx₁, haVr x₂ hx₂⟩, ?_⟩
          change gr x₁ a - gr x₂ a ∉ ({(0 : ℂ)} : Set ℂ)
          rw [hgar x₁ hx₁, hgar x₂ hx₂]
          exact fun h0 => h12 (sub_eq_zero.mp h0)
      · exact mem_interior_iff_mem_nhds.mpr hNnhds
    refine ⟨(fun t : ℂ => ((t : ℂ̂))) '' Vfin, ?_, ?_⟩
    · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
        Set.preimage_image_eq _ OnePoint.coe_injective]
      exact hVfin_open.mem_nhds haVfin
    · rintro w ⟨⟨y, hyVfin, rfl⟩, hwT⟩
      rw [hVfindef] at hyVfin
      obtain ⟨⟨hyVall, hyD⟩, hyN⟩ := hyVfin
      have hyVx : ∀ x ∈ Fc, y ∈ Vr x := Set.mem_iInter₂.mp hyVall
      -- the fiber over `↑y` is exactly the set of branch values
      have himgfib : f ⁻¹' {((y : ℂ̂))} ∩ S = (fun x : ℂ => ((gr x y : ℂ̂))) '' Fc := by
        apply Set.Subset.antisymm
        · rintro u ⟨huf, huS⟩
          have hufeq : f u = ((y : ℂ̂)) := huf
          have huN : f u ∈ N := by
            rw [hufeq]
            exact interior_subset hyN
          obtain ⟨x, hxFc, hxO⟩ := hNcap u huN huS
          exact ⟨x, hxFc, (hcapr x hxFc u hxO y (hyVx x hxFc) hufeq).symm⟩
        · rintro _ ⟨x, hxFc, rfl⟩
          exact ⟨(hbrr x hxFc y (hyVx x hxFc)).1, (hbrr x hxFc y (hyVx x hxFc)).2⟩
      have hinj1 : Set.InjOn (fun x : ℂ => ((gr x y : ℂ̂))) Fc := by
        intro x₁ hx₁ x₂ hx₂ heq
        by_contra h12
        have hy12 := Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hyD x₁ hx₁) x₂ hx₂
        rw [if_neg h12] at hy12
        have hgne : gr x₁ y - gr x₂ y ∉ ({(0 : ℂ)} : Set ℂ) := hy12.2
        exact hgne (sub_eq_zero_of_eq (OnePoint.coe_eq_coe.mp heq))
      rw [himgfib, hFC, hinj1.ncard_image, (OnePoint.coe_injective.injOn).ncard_image]
  -- Stage 3: local constancy on the connected `T` gives a global count
  obtain ⟨w₀, hw₀T⟩ := hTfc.nonempty
  refine ⟨(f ⁻¹' {w₀} ∩ S).ncard, ?_, ?_⟩
  · obtain ⟨y₀, rfl⟩ := hTfin w₀ hw₀T
    have hne : (f ⁻¹' {((y₀ : ℂ̂))} ∩ S).Nonempty := by
      rw [← himg] at hw₀T
      obtain ⟨u, huS, huf⟩ := hw₀T
      exact ⟨u, huf, huS⟩
    exact (Set.ncard_pos (hfib_fin y₀)).mpr hne
  · by_contra hbad
    push Not at hbad
    obtain ⟨w₁, hw₁T, hw₁ne⟩ := hbad
    have hpatch : ∀ w : ℂ̂, ∃ P : Set ℂ̂, w ∈ T → (P ∈ 𝓝 w ∧ ∀ w' ∈ P ∩ T,
        (f ⁻¹' {w'} ∩ S).ncard = (f ⁻¹' {w} ∩ S).ncard) := by
      intro w
      by_cases hw : w ∈ T
      · obtain ⟨P, h1, h2⟩ := hlc w hw
        exact ⟨P, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨∅, fun h => absurd h hw⟩
    choose P hP using hpatch
    have hcover : T ⊆ (⋃ w ∈ {w ∈ T | (f ⁻¹' {w} ∩ S).ncard
          = (f ⁻¹' {w₀} ∩ S).ncard}, interior (P w)) ∪
        ⋃ w ∈ {w ∈ T | (f ⁻¹' {w} ∩ S).ncard ≠ (f ⁻¹' {w₀} ∩ S).ncard},
          interior (P w) := by
      intro w hw
      have hmem : w ∈ interior (P w) := mem_interior_iff_mem_nhds.mpr (hP w hw).1
      by_cases hval : (f ⁻¹' {w} ∩ S).ncard = (f ⁻¹' {w₀} ∩ S).ncard
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hval⟩, hmem⟩)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hval⟩, hmem⟩)
    obtain ⟨z, hzT, hzA, hzB⟩ := hTfc.isConnected.isPreconnected _ _
      (isOpen_biUnion fun _ _ => isOpen_interior)
      (isOpen_biUnion fun _ _ => isOpen_interior) hcover
      ⟨w₀, hw₀T, Set.mem_iUnion₂.mpr ⟨w₀, ⟨hw₀T, rfl⟩,
        mem_interior_iff_mem_nhds.mpr (hP w₀ hw₀T).1⟩⟩
      ⟨w₁, hw₁T, Set.mem_iUnion₂.mpr ⟨w₁, ⟨hw₁T, hw₁ne⟩,
        mem_interior_iff_mem_nhds.mpr (hP w₁ hw₁T).1⟩⟩
    obtain ⟨wa, hwa, hza⟩ := Set.mem_iUnion₂.mp hzA
    obtain ⟨wb, hwb, hzb⟩ := Set.mem_iUnion₂.mp hzB
    have h1 : (f ⁻¹' {z} ∩ S).ncard = (f ⁻¹' {wa} ∩ S).ncard :=
      (hP wa hwa.1).2 z ⟨interior_subset hza, hzT⟩
    have h2 : (f ⁻¹' {z} ∩ S).ncard = (f ⁻¹' {wb} ∩ S).ncard :=
      (hP wb hwb.1).2 z ⟨interior_subset hzb, hzT⟩
    exact hwb.2 (by rw [← h2, h1, hwa.2])

/-- A component step with constant fiber count one is injective on the
source component. -/
theorem injOn_of_fiberCount_one {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (h1 : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = 1) :
    Set.InjOn f (fcOrbit f U n) := by
  intro x hx y hy hxy
  have hwT : f x ∈ fcOrbit f U (n + 1) := by
    rw [← fcOrbit_image_eq hf hd hU n]
    exact ⟨x, hx, rfl⟩
  have hcard := h1 (f x) hwT
  rw [Set.ncard_eq_one] at hcard
  obtain ⟨a, ha⟩ := hcard
  have hxa : x ∈ f ⁻¹' {f x} ∩ fcOrbit f U n := ⟨rfl, hx⟩
  have hya : y ∈ f ⁻¹' {f x} ∩ fcOrbit f U n := ⟨by simp [hxy], hy⟩
  rw [ha, Set.mem_singleton_iff] at hxa hya
  rw [hxa, hya]

/-- **Injectivity telescopes**: if every single component step from index
`N` on is injective, then every iterate is injective on the `N`-th
component (finite induction along the orbit, using that iterates stay in
the orbit components). -/
theorem injOn_iterate_of_tail_injective {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (N : ℕ)
    (hstep : ∀ m : ℕ, N ≤ m → Set.InjOn f (fcOrbit f U m)) :
    ∀ n : ℕ, Set.InjOn (f^[n]) (fcOrbit f U N) := by
  have hV : IsFatouComponent f (fcOrbit f U N) := isFatouComponent_fcOrbit N hf hd hU
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd)
  have hfwd : ∀ k : ℕ, ∀ w : ℂ̂, w ∈ FatouSet f → f^[k] w ∈ FatouSet f := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo (ih w hw)
  have hmem : ∀ n : ℕ, ∀ x ∈ fcOrbit f U N, f^[n] x ∈ fcOrbit f U (N + n) := by
    intro n x hx
    rw [fcOrbit_add N n hf hd hU,
      fcOrbit_eq_connectedComponentIn n hf hd hV hx]
    exact mem_connectedComponentIn (hfwd n x (hV.subset_fatouSet hx))
  intro n
  induction n with
  | zero =>
      intro x _ y _ hxy
      simpa using hxy
  | succ n ih =>
      intro x hx y hy hxy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hxy
      have hxn : f^[n] x ∈ fcOrbit f U (N + n) := hmem n x hx
      have hyn : f^[n] y ∈ fcOrbit f U (N + n) := hmem n y hy
      have hiter : f^[n] x = f^[n] y :=
        hstep (N + n) (Nat.le_add_right N n) hxn hyn hxy
      exact ih hx hy hiter

/-- **Simple connectivity from unbounded complementary components** (the
Riemann-mapping bridge). An open connected proper subset of the plane all of
whose complementary components are unbounded is simply connected: it has
primitives (`has_primitives_of_unbounded_components`), so the vendored
Riemann mapping theorem provides a holomorphic bijection onto the unit ball;
the open mapping theorem upgrades it to a homeomorphism; the ball is convex,
hence contractible, hence simply connected; and simple connectivity
transports along homotopy equivalences. -/
theorem simplyConnectedSpace_of_unbounded_components {T : Set ℂ}
    (hT : IsOpen T) (hconn : IsConnected T) (hne : T ≠ Set.univ)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z)) :
    SimplyConnectedSpace T := by
  -- Primitives exist on `T`, so the vendored Riemann mapping theorem applies.
  obtain ⟨f, hdf, hinj, himg⟩ :=
    RMT hT hconn hne (has_primitives_of_unbounded_components hT hcompl)
  -- `f` maps open subsets of `T` to open sets (open mapping theorem; the
  -- constant alternative contradicts injectivity on the nonempty open `T`).
  have hopen : ∀ s ⊆ T, IsOpen s → IsOpen (f '' s) := by
    rcases (hdf.analyticOnNhd hT).is_constant_or_isOpen hconn.isPreconnected with ⟨w, hw⟩ | h
    · exfalso
      obtain ⟨z₀, hz₀⟩ := hconn.nonempty
      have hmem : T ∩ {z₀}ᶜ ∈ 𝓝[≠] z₀ :=
        Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hT.mem_nhds hz₀))
          self_mem_nhdsWithin
      obtain ⟨y, hyT, hyz⟩ := Filter.nonempty_of_mem hmem
      exact Set.mem_compl_singleton_iff.mp hyz
        (hinj hyT hz₀ ((hw _ hyT).trans (hw _ hz₀).symm))
    · exact h
  -- Package `f` as a map between the subtypes `↥T` and `↥(ball 0 1)`.
  have hmemB : ∀ x : T, f x ∈ Metric.ball (0 : ℂ) 1 := fun x => by
    rw [← himg]; exact Set.mem_image_of_mem f x.2
  let F : T → Metric.ball (0 : ℂ) 1 := fun x => ⟨f x, hmemB x⟩
  have hFinj : Function.Injective F := fun x y hxy =>
    Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
  have hFsurj : Function.Surjective F := by
    rintro ⟨w, hw⟩
    rw [← himg] at hw
    obtain ⟨x, hxT, hfx⟩ := hw
    exact ⟨⟨x, hxT⟩, Subtype.ext hfx⟩
  have hFcont : Continuous F := hdf.continuousOn.domRestrict.subtype_mk hmemB
  have hFopen : IsOpenMap F := by
    intro V hV
    have hval : IsOpen (Subtype.val '' V) := hT.isOpenMap_subtype_val V hV
    have hsub : Subtype.val '' V ⊆ T := by rintro _ ⟨x, -, rfl⟩; exact x.2
    have h1 : IsOpen (f '' (Subtype.val '' V)) := hopen _ hsub hval
    have h2 : F '' V = Subtype.val ⁻¹' (f '' (Subtype.val '' V)) := by
      ext w
      constructor
      · rintro ⟨x, hxV, rfl⟩
        exact ⟨x, ⟨x, hxV, rfl⟩, rfl⟩
      · rintro ⟨-, ⟨x, hxV, rfl⟩, hfx⟩
        exact ⟨x, hxV, Subtype.ext hfx⟩
    rw [h2]
    exact h1.preimage continuous_subtype_val
  -- Upgrade to a homeomorphism `↥T ≃ₜ ↥(ball 0 1)`.
  have hhomeo : (T : Set ℂ) ≃ₜ (Metric.ball (0 : ℂ) 1 : Set ℂ) :=
    (Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen hFcont hFopen
  -- The ball is convex, hence contractible, hence simply connected;
  -- transport along the homotopy equivalence induced by the homeomorphism.
  have : ContinuousSMul ℝ ℂ := by
    refine ⟨?_⟩
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p; exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  have : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace (Metric.nonempty_ball.mpr one_pos)
  exact hhomeo.toHomotopyEquiv.simplyConnectedSpace

/-- Transfer of complement structure to the sphere: for a Fatou-component
avoiding `∞`, disconnectedness of the sphere complement is equivalent to the
existence of a bounded complementary component of its finite part. -/
theorem exists_bounded_component_of_not_isConnected_compl {U : Set ℂ̂}
    (hU : IsOpen U) (_hUne : U.Nonempty) (hinf : ∞ ∉ U)
    (hnc : ¬IsConnected (Uᶜ : Set ℂ̂)) :
    ∃ z : ℂ, ((z : ℂ̂) ∉ U) ∧
      Bornology.IsBounded
        (connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ U} z) := by
  classical
  have hinfc : (∞ : ℂ̂) ∈ Uᶜ := hinf
  -- There is a point of `Uᶜ` outside the connected component of `∞` in `Uᶜ`.
  have hx : ∃ x ∈ (Uᶜ : Set ℂ̂), x ∉ connectedComponentIn (Uᶜ : Set ℂ̂) ∞ := by
    by_contra h
    push Not at h
    refine hnc ?_
    have heq : (Uᶜ : Set ℂ̂) = connectedComponentIn (Uᶜ : Set ℂ̂) ∞ :=
      Set.Subset.antisymm h (connectedComponentIn_subset _ _)
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hinfc
  obtain ⟨x, hxc, hxcc⟩ := hx
  induction x using OnePoint.rec with
  | infty => exact absurd (mem_connectedComponentIn hinfc) hxcc
  | coe z =>
    refine ⟨z, hxc, ?_⟩
    by_contra hub
    set C : Set ℂ := connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ U} z with hCdef
    have hzK : z ∈ {w : ℂ | (w : ℂ̂) ∉ U} := hxc
    have hCz : z ∈ C := mem_connectedComponentIn hzK
    have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCsub : C ⊆ {w : ℂ | (w : ℂ̂) ∉ U} := by
      rw [hCdef]; exact connectedComponentIn_subset _ _
    -- the image of `C` on the sphere and its closure are preconnected
    have himg : IsPreconnected ((fun w : ℂ => (w : ℂ̂)) '' C) :=
      hCpre.image _ OnePoint.continuous_coe.continuousOn
    have hclpre : IsPreconnected (closure ((fun w : ℂ => (w : ℂ̂)) '' C)) := himg.closure
    -- the closure stays inside the closed set `Uᶜ`
    have hsubUc : ((fun w : ℂ => (w : ℂ̂)) '' C) ⊆ Uᶜ := by
      rintro _ ⟨w, hwC, rfl⟩
      exact hCsub hwC
    have hclsub : closure ((fun w : ℂ => (w : ℂ̂)) '' C) ⊆ Uᶜ :=
      hU.isClosed_compl.closure_subset_iff.mpr hsubUc
    -- unboundedness of `C` forces `∞` into the closure of its image
    have hinfcl : (∞ : ℂ̂) ∈ closure ((fun w : ℂ => (w : ℂ̂)) '' C) := by
      rw [mem_closure_iff]
      intro o ho hoinf
      have hcompact : IsCompact (((fun w : ℂ => (w : ℂ̂)) ⁻¹' o)ᶜ) :=
        ((OnePoint.isOpen_iff_of_mem' hoinf).mp ho).1
      have hbdd : Bornology.IsBounded (((fun w : ℂ => (w : ℂ̂)) ⁻¹' o)ᶜ) :=
        hcompact.isBounded
      have hns : ¬ C ⊆ ((fun w : ℂ => (w : ℂ̂)) ⁻¹' o)ᶜ :=
        fun hsub => hub (hbdd.subset hsub)
      obtain ⟨w, hwC, hwo⟩ := Set.not_subset.mp hns
      rw [Set.mem_compl_iff, not_not] at hwo
      exact ⟨(w : ℂ̂), hwo, ⟨w, hwC, rfl⟩⟩
    -- maximality of the component of `∞` swallows the closure, contradiction
    have hzcc : (z : ℂ̂) ∈ connectedComponentIn (Uᶜ : Set ℂ̂) ∞ :=
      hclpre.subset_connectedComponentIn hinfcl hclsub (subset_closure ⟨z, hCz, rfl⟩)
    exact hxcc hzcc

/-- **Degree one over a simply connected target.** A component step whose
target component is simply connected has fiber count one: package the
covering records as a covering map of subtypes, lift the identity through it
(unique lifting over simply connected bases), and observe that the image of
the section is clopen in the connected source. -/
theorem fiberCount_eq_one_of_simplyConnected {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    (hsc : SimplyConnectedSpace (fcOrbit f U (n + 1) : Set ℂ̂))
    {k : ℕ} (hk : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    k = 1 := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd1 hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have himg : f '' S = T := fcOrbit_image_eq hf hd1 hU n
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
  -- ## Stage 0: the sphere is locally path-connected.
  -- Finite points have bases of coe-images of balls; `∞` has the basis of
  -- complements of closed balls, each path-connected via radial rays to `∞`.
  have hlpc : LocallyPathConnectedSpace ℂ̂ := by
    constructor
    intro x
    rw [Filter.hasBasis_self]
    induction x using OnePoint.rec with
    | infty =>
      intro t ht
      obtain ⟨s, ⟨hscl, hscpt⟩, hsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht
      obtain ⟨r0, hr0⟩ := hscpt.isBounded.subset_closedBall 0
      set R := max r0 0 with hRdef
      have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
      have hcompl : ∀ w : ℂ, R < ‖w‖ → w ∈ sᶜ := by
        intro w hw hws
        have h1 := hr0 hws
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        exact absurd (h1.trans (le_max_left _ _)) (not_le.mpr hw)
      refine ⟨(fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | R < ‖w‖} ∪ {∞}, ?_, ?_, ?_⟩
      · refine OnePoint.hasBasis_nhds_infty.mem_iff.mpr
          ⟨Metric.closedBall 0 R,
            ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 R⟩, ?_⟩
        rintro u (⟨w, hw, rfl⟩ | hu)
        · rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
          exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr hu
      · -- the annular neighborhood of `∞` is path-connected
        refine ⟨∞, Or.inr rfl, ?_⟩
        rintro u (⟨a, haR, rfl⟩ | rfl)
        swap
        · exact JoinedIn.refl (Or.inr rfl)
        have haR' : R < ‖a‖ := haR
        have hanorm : (0 : ℝ) < ‖a‖ := lt_of_le_of_lt hR0 haR'
        have hval : ∀ t : unitInterval,
            ‖((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ)‖ = ((t : ℝ))⁻¹ * ‖a‖ := by
          intro t
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr t.2.1)]
        have hmemloc : ∀ t : unitInterval, (t : ℝ) ≠ 0 →
            ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂))
              ∈ (fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | R < ‖w‖} ∪ {∞} := by
          intro t htz
          have htpos : (0 : ℝ) < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm htz)
          have h1 : (1 : ℝ) ≤ ((t : ℝ))⁻¹ := (one_le_inv₀ htpos).mpr t.2.2
          refine Or.inl ⟨_, ?_, rfl⟩
          change R < ‖((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ)‖
          rw [hval t]
          calc R < ‖a‖ := haR'
            _ ≤ ((t : ℝ))⁻¹ * ‖a‖ := le_mul_of_one_le_left (norm_nonneg a) h1
        obtain ⟨γf, hγf⟩ : ∃ g : unitInterval → ℂ̂, g = fun t : unitInterval =>
            if (t : ℝ) = 0 then (∞ : ℂ̂)
            else ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂)) := ⟨_, rfl⟩
        have hγfval : ∀ t : unitInterval, γf t
            = if (t : ℝ) = 0 then (∞ : ℂ̂)
              else ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂)) := by
          intro t
          rw [hγf]
        have hcont : Continuous γf := by
          rw [continuous_iff_continuousAt]
          intro t₀
          by_cases ht₀ : (t₀ : ℝ) = 0
          · have h0eq : γf t₀ = ∞ := by
              rw [hγfval t₀, if_pos ht₀]
            change Filter.Tendsto γf (𝓝 t₀) (𝓝 (γf t₀))
            rw [h0eq, OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
            rintro s' ⟨-, hscpt'⟩
            obtain ⟨m, hm⟩ := hscpt'.isBounded.subset_closedBall 0
            have hMpos : (0 : ℝ) < max m 0 + 1 := by positivity
            have hδ : (0 : ℝ) < ‖a‖ / (max m 0 + 1) := div_pos hanorm hMpos
            have hevlt : ∀ᶠ tt : unitInterval in 𝓝 t₀,
                (tt : ℝ) < ‖a‖ / (max m 0 + 1) := by
              have hc : Tendsto (fun tt : unitInterval => (tt : ℝ)) (𝓝 t₀)
                  (𝓝 ((t₀ : ℝ))) := continuous_subtype_val.continuousAt
              rw [ht₀] at hc
              exact hc.eventually_lt_const hδ
            filter_upwards [hevlt] with tt htt
            by_cases htz : (tt : ℝ) = 0
            · rw [hγfval tt, if_pos htz]
              exact Or.inr rfl
            · rw [hγfval tt, if_neg htz]
              have htpos : (0 : ℝ) < (tt : ℝ) := lt_of_le_of_ne tt.2.1 (Ne.symm htz)
              refine Or.inl ⟨_, ?_, rfl⟩
              intro hmem
              have hle := hm hmem
              rw [Metric.mem_closedBall, dist_zero_right, hval tt] at hle
              have h2 : (tt : ℝ) * (max m 0 + 1) < ‖a‖ := (lt_div_iff₀ hMpos).mp htt
              have h3 : max m 0 + 1 < ((tt : ℝ))⁻¹ * ‖a‖ := by
                rw [← div_eq_inv_mul]
                refine (lt_div_iff₀ htpos).mpr ?_
                rw [mul_comm]
                exact h2
              have hmax : m ≤ max m 0 := le_max_left m 0
              linarith
          · have hev : ∀ᶠ tt : unitInterval in 𝓝 t₀, (tt : ℝ) ≠ 0 :=
              continuous_subtype_val.continuousAt.eventually_ne ht₀
            have hca : ContinuousAt ((fun w : ℂ => ((w : ℂ̂))) ∘
                (fun tt : unitInterval => ((((tt : ℝ)⁻¹ : ℝ) : ℂ) * a))) t₀ := by
              refine ContinuousAt.comp ?_ ?_
              · exact OnePoint.continuous_coe.continuousAt
              · exact (Complex.continuous_ofReal.continuousAt.comp
                  (continuous_subtype_val.continuousAt.inv₀ ht₀)).mul continuousAt_const
            refine hca.congr ?_
            filter_upwards [hev] with tt htt
            rw [hγfval tt, if_neg htt]
            rfl
        refine ⟨⟨⟨γf, hcont⟩, ?_, ?_⟩, ?_⟩
        · change γf 0 = ∞
          rw [hγfval 0]
          exact if_pos rfl
        · change γf 1 = ((a : ℂ̂))
          rw [hγfval 1,
            if_neg (by exact one_ne_zero : ((1 : unitInterval) : ℝ) ≠ 0)]
          change ((((1 : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ̂) = (a : ℂ̂)
          norm_num
        · intro t
          change γf t ∈ _
          by_cases htz : (t : ℝ) = 0
          · rw [hγfval t, if_pos htz]
            exact Or.inr rfl
          · rw [hγfval t, if_neg htz]
            exact hmemloc t htz
      · rintro u (⟨w, hw, rfl⟩ | hu)
        · exact hsub (Or.inl ⟨w, hcompl w hw, rfl⟩)
        · exact hsub (Or.inr hu)
    | coe z =>
      intro t ht
      rw [OnePoint.nhds_coe_eq, Filter.mem_map] at ht
      obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_ball.mem_iff.mp ht
      refine ⟨(fun w : ℂ => ((w : ℂ̂))) '' Metric.ball z ε, ?_, ?_, ?_⟩
      · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
          Set.preimage_image_eq _ OnePoint.coe_injective]
        exact Metric.ball_mem_nhds z hε
      · exact ((convex_ball z ε).isPathConnected
          ⟨z, Metric.mem_ball_self hε⟩).image OnePoint.continuous_coe
      · exact Set.image_subset_iff.mpr hεsub
  -- ## Stage 1: analytic records mined from the `exists_fiberCount` proof.
  have cf : ∀ t : ℂ, chartFiniteMap ((t : ℂ̂)) = t := fun _ => rfl
  have hread : ∀ t : ℂ, r.toSphereMap ((t : ℂ̂))
      = if r.denReduced.eval t = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval t / r.denReduced.eval t : ℂ) : ℂ̂) := fun _ => rfl
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  -- on `S` the reduced denominator does not vanish
  have hden_ne : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → r.denReduced.eval x ≠ 0 := by
    intro x hxS h0
    have hcx := hcrit x hxS
    have hdiff : DifferentiableAt ℂ (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) x := by
      by_contra hnd
      exact hcx (deriv_zero_of_not_differentiableAt hnd)
    have hφx : chartFiniteMap (f ((x : ℂ̂))) = 0 := by
      rw [hr, hread x, if_pos h0]
      rfl
    have hZfin : {t : ℂ | r.denReduced.IsRoot t}.Finite :=
      Polynomial.finite_setOfPred_isRoot hdenR
    have hclosed : IsClosed ({t : ℂ | r.denReduced.IsRoot t} \ {x}) :=
      (hZfin.subset Set.sdiff_subset).isClosed
    have hxmem : x ∈ ({t : ℂ | r.denReduced.IsRoot t} \ {x})ᶜ := fun h => h.2 rfl
    have hev_ne : ∀ᶠ t in 𝓝[≠] x, r.denReduced.eval t ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hxmem),
        self_mem_nhdsWithin] with t ht htx
      exact fun h0t => ht ⟨h0t, htx⟩
    have h1 : Tendsto (fun t : ℂ => f ((t : ℂ̂))) (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) := by
      have hc : ContinuousAt (fun t : ℂ => f ((t : ℂ̂))) x :=
        (hf.continuous.comp OnePoint.continuous_coe).continuousAt
      have hfx : f ((x : ℂ̂)) = ∞ := by rw [hr, hread x, if_pos h0]
      have h := hc.tendsto
      rw [hfx] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (((0 : ℂ) : ℂ̂))) := by
      have hφt := hdiff.continuousAt.tendsto
      rw [hφx] at hφt
      exact ((OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hφt).mono_left
        nhdsWithin_le_nhds
    have heq : (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        =ᶠ[𝓝[≠] x] fun t : ℂ => f ((t : ℂ̂)) := by
      filter_upwards [hev_ne] with t ht
      rw [hr, hread t, if_neg ht, cf]
    have h1' : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) h1
    exact OnePoint.coe_ne_infty (0 : ℂ) (tendsto_nhds_unique h2 h1')
  -- values on `S` are finite
  have hSfin : ∀ u ∈ S, f u ≠ ∞ := by
    intro u huS
    have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
    rw [hr, hread x, if_neg (hden_ne x huS)]
    exact OnePoint.coe_ne_infty _
  have hTfin : ∀ w ∈ T, ∃ y : ℂ, w = ((y : ℂ̂)) := by
    intro w hwT
    rw [← himg] at hwT
    obtain ⟨u, huS, rfl⟩ := hwT
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp (hSfin u huS)
    exact ⟨y, hy.symm⟩
  -- fibers over finite points are finite
  have hfib_fin : ∀ y : ℂ, (f ⁻¹' {((y : ℂ̂))} ∩ S).Finite := by
    intro y
    have hq : r.numReduced - Polynomial.C y * r.denReduced ≠ 0 := by
      intro h0
      apply hWr
      have hnum : r.numReduced = Polynomial.C y * r.denReduced := sub_eq_zero.mp h0
      unfold RationalData.wronskian
      rw [hnum, Polynomial.derivative_C_mul]
      ring
    have hsub : f ⁻¹' {((y : ℂ̂))} ∩ S ⊆ (fun x : ℂ => ((x : ℂ̂))) ''
        {x : ℂ | (r.numReduced - Polynomial.C y * r.denReduced).IsRoot x} := by
      rintro u ⟨hufy, huS⟩
      have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
      obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
      have hden := hden_ne x huS
      have hfx : f ((x : ℂ̂)) = ((y : ℂ̂)) := hufy
      rw [hr, hread x, if_neg hden] at hfx
      have hdiv : r.numReduced.eval x / r.denReduced.eval x = y :=
        OnePoint.coe_eq_coe.mp hfx
      rw [div_eq_iff hden] at hdiv
      refine ⟨x, ?_, rfl⟩
      change (r.numReduced - Polynomial.C y * r.denReduced).eval x = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hdiv, sub_self]
    exact ((Polynomial.finite_setOfPred_isRoot hq).image _).subset hsub
  -- local injectivity near each finite non-critical point
  have hloc : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → ∃ Wc : Set ℂ, IsOpen Wc ∧ x ∈ Wc ∧
      ∀ t₁ ∈ Wc, ∀ t₂ ∈ Wc, f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) → t₁ = t₂ := by
    intro x hxS
    have hcx := hcrit x hxS
    have hden := hden_ne x hxS
    have hev : (fun t : ℂ => r.numReduced.eval t / r.denReduced.eval t)
        =ᶠ[𝓝 x] fun t : ℂ => chartFiniteMap (f ((t : ℂ̂))) := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with t ht
      rw [hr, hread t, if_neg ht, cf]
    obtain ⟨D, hstrict⟩ : ∃ D : ℂ,
        HasStrictDerivAt (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) D x :=
      ⟨_, ((r.numReduced.hasStrictDerivAt x).div
        (r.denReduced.hasStrictDerivAt x) hden).congr_of_eventuallyEq hev⟩
    have hD : D ≠ 0 := hstrict.hasDerivAt.deriv ▸ hcx
    obtain ⟨Wc, hWsub, hWopen, hxW⟩ :=
      mem_nhds_iff.mp (hstrict.eventually_left_inverse hD)
    refine ⟨Wc, hWopen, hxW, ?_⟩
    intro t₁ ht₁ t₂ ht₂ hft
    have h₁ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₁ : ℂ̂)))) = t₁ := hWsub ht₁
    have h₂ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₂ : ℂ̂)))) = t₂ := hWsub ht₂
    rw [← h₁, hft, h₂]
  -- ## Stage 2: the packaged component step between the two subtypes.
  have hmapsto : ∀ u : ℂ̂, u ∈ S → f u ∈ T := by
    intro u hu
    rw [← himg]
    exact ⟨u, hu, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ↥S → ↥T,
      F = fun u => ⟨f u.1, hmapsto u.1 u.2⟩ := ⟨_, rfl⟩
  have hFval : ∀ u : ↥S, ((F u : ℂ̂)) = f u.1 := by
    intro u
    rw [hFdef]
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Continuous.subtype_mk (hf.continuous.comp continuous_subtype_val) _
  -- the packaged map is open
  have hFopen : IsOpenMap F := by
    intro V hV
    obtain ⟨D, hD, hDV⟩ := isOpen_induced_iff.mp hV
    have himgV : F '' V = Subtype.val ⁻¹' (f '' (S ∩ D)) := by
      ext w
      constructor
      · rintro ⟨u, huV, rfl⟩
        have huD : u.1 ∈ D := by
          rw [← hDV] at huV
          exact huV
        exact ⟨u.1, ⟨u.2, huD⟩, (hFval u).symm⟩
      · rintro ⟨v, ⟨hvS, hvD⟩, hfv⟩
        refine ⟨⟨v, hvS⟩, ?_, ?_⟩
        · rw [← hDV]
          exact hvD
        · apply Subtype.ext
          rw [hFval]
          exact hfv
    rw [himgV]
    exact (hfo _ (hSfc.isOpen.inter hD)).preimage continuous_subtype_val
  -- the packaged map is closed (properness via the Julia frontier)
  have hFclosed : IsClosedMap F := by
    intro C hC
    obtain ⟨D, hD, hDC⟩ := isClosed_induced_iff.mp hC
    have hkey : F '' C = Subtype.val ⁻¹' (closure (f '' (S ∩ D))) := by
      ext w
      constructor
      · rintro ⟨u, huC, rfl⟩
        have huD : u.1 ∈ D := by
          rw [← hDC] at huC
          exact huC
        exact subset_closure ⟨u.1, ⟨u.2, huD⟩, (hFval u).symm⟩
      · intro hw
        have hcl : closure (f '' (S ∩ D)) ⊆ f '' closure (S ∩ D) := by
          apply closure_minimal (Set.image_mono subset_closure)
          exact (isClosed_closure.isCompact.image hf.continuous).isClosed
        obtain ⟨x, hxcl, hfx⟩ := hcl hw
        have hxSD : x ∈ closure S ∩ D := by
          have h1 := closure_inter_subset_inter_closure S D hxcl
          rwa [hD.closure_eq] at h1
        by_cases hxS : x ∈ S
        · refine ⟨⟨x, hxS⟩, ?_, ?_⟩
          · rw [← hDC]
            exact hxSD.2
          · apply Subtype.ext
            rw [hFval]
            exact hfx
        · exfalso
          have hxfr : x ∈ frontier S := by
            rw [hSfc.isOpen.frontier_eq]
            exact ⟨hxSD.1, hxS⟩
          have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
          rw [← juliaSet_preimage_eq_of_isRational hf hd1] at hxJ
          have hfxJ : f x ∈ JuliaSet f := hxJ
          rw [hfx] at hfxJ
          exact hfxJ (hTfc.subset_fatouSet w.2)
    rw [hkey]
    exact IsClosed.preimage continuous_subtype_val isClosed_closure
  -- fibers of the packaged map are finite
  have hFfib : ∀ w : ↥T, (F ⁻¹' {w}).Finite := by
    intro w
    obtain ⟨y, hy⟩ := hTfin w.1 w.2
    have hpre : F ⁻¹' {w} = Subtype.val ⁻¹' (f ⁻¹' {((y : ℂ̂))} ∩ S) := by
      ext u
      constructor
      · intro hu
        have h1 : F u = w := hu
        have h2 : f u.1 = ((y : ℂ̂)) := by
          have h3 := congrArg Subtype.val h1
          rw [hFval u] at h3
          rw [h3]
          exact hy
        exact ⟨h2, u.2⟩
      · intro hu
        apply Subtype.ext
        rw [hFval u, hy]
        exact hu.1
    rw [hpre]
    exact Set.Finite.preimage Subtype.coe_injective.injOn (hfib_fin y)
  -- local homeomorphism records for the packaged map
  have hSne : Nonempty ↥S := hSfc.nonempty.to_subtype
  have hFloc : ∀ e : ↥S, ∃ φ : OpenPartialHomeomorph ↥S ↥T,
      e ∈ φ.source ∧ F = ⇑φ := by
    intro e
    have hene : (e : ℂ̂) ≠ ∞ := fun h => hinf (h ▸ e.2)
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp hene
    have hxS : ((x : ℂ̂)) ∈ S := by
      rw [hx]
      exact e.2
    obtain ⟨Wc, hWopen, hxW, hWinj⟩ := hloc x hxS
    set src : Set ↥S := Subtype.val ⁻¹' ((fun t : ℂ => ((t : ℂ̂))) '' Wc) with hsrc
    have hsrcopen : IsOpen src :=
      (OnePoint.isOpenEmbedding_coe.isOpenMap _ hWopen).preimage
        continuous_subtype_val
    have hesrc : e ∈ src := ⟨x, hxW, hx⟩
    have hinjF : Set.InjOn F src := by
      rintro u₁ hu₁ u₂ hu₂ h12
      obtain ⟨t₁, ht₁, htv₁⟩ := hu₁
      obtain ⟨t₂, ht₂, htv₂⟩ := hu₂
      have hf12 : f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) := by
        have htv₁' : ((t₁ : ℂ̂)) = (u₁ : ℂ̂) := htv₁
        have htv₂' : ((t₂ : ℂ̂)) = (u₂ : ℂ̂) := htv₂
        rw [htv₁', htv₂']
        have h3 := congrArg Subtype.val h12
        rw [hFval, hFval] at h3
        exact h3
      have ht12 : t₁ = t₂ := hWinj t₁ ht₁ t₂ ht₂ hf12
      apply Subtype.ext
      rw [← htv₁, ← htv₂, ht12]
    refine ⟨OpenPartialHomeomorph.ofContinuousOpen
      (hinjF.toPartialEquiv F src) ?_ ?_ ?_, ?_, ?_⟩
    · exact hFcont.continuousOn
    · exact hFopen
    · exact hsrcopen
    · exact hesrc
    · rfl
  -- ## Stage 3: the packaged map is a covering map.
  have hcovOn : IsCoveringMapOn F Set.univ :=
    hFclosed.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun w _ => hFfib w) (fun e _ => hFloc e)
  have hcov : IsCoveringMap F := isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  -- ## Stage 4: lift the identity of the simply connected target through `F`.
  have := hsc
  have : LocallyPathConnectedSpace ↥T := hTfc.isOpen.locallyPathConnectedSpace
  obtain ⟨w₀, hw₀T⟩ := hTfc.nonempty
  have hw₀' : w₀ ∈ f '' S := by
    rw [himg]
    exact hw₀T
  obtain ⟨u₀, hu₀S, hu₀f⟩ := hw₀'
  have hbase : F ⟨u₀, hu₀S⟩ = (⟨w₀, hw₀T⟩ : ↥T) := by
    apply Subtype.ext
    rw [hFval]
    exact hu₀f
  obtain ⟨σ, ⟨hσ0, hσlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id ↥T) ⟨w₀, hw₀T⟩ ⟨u₀, hu₀S⟩ hbase
  -- ## Stage 5: the section retracts, so the packaged map is injective.
  have : PreconnectedSpace ↥S :=
    Subtype.preconnectedSpace hSfc.isConnected.isPreconnected
  have hσF : ⇑σ ∘ F = id := by
    apply hcov.eq_of_comp_eq (σ.continuous.comp hFcont) continuous_id ?_
      ⟨u₀, hu₀S⟩ ?_
    · rw [← Function.comp_assoc, hσlift, ContinuousMap.coe_id,
        Function.id_comp, Function.comp_id]
    · change σ (F ⟨u₀, hu₀S⟩) = ⟨u₀, hu₀S⟩
      rw [hbase, hσ0]
  have hFinj : Function.Injective F := by
    intro u₁ u₂ h12
    have h1 := congrFun hσF u₁
    have h2 := congrFun hσF u₂
    simp only [Function.comp_apply, id_eq] at h1 h2
    rw [← h1, ← h2, h12]
  -- ## Stage 6: a fiber is a singleton, so the constant count is one.
  have hfib : f ⁻¹' {w₀} ∩ S = {u₀} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact ⟨hu₀f, hu₀S⟩
    · rintro v ⟨hvf, hvS⟩
      have hvf' : f v = w₀ := hvf
      have hFeq : F ⟨v, hvS⟩ = F ⟨u₀, hu₀S⟩ := by
        apply Subtype.ext
        rw [hFval, hFval]
        change f v = f u₀
        rw [hvf', hu₀f]
      have := hFinj hFeq
      exact congrArg Subtype.val this
  have hk₀ := hk w₀ hw₀T
  rw [hfib, Set.ncard_singleton] at hk₀
  exact hk₀.symm

end NoWanderingDomains
