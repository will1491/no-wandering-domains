/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Sullivan.EventualInjectivity.FiberCount

/-!
# Loops and null homotopies along the orbit

A multiple step disconnects the complement; the sphere is locally
path-connected; a simply connected sandwich exists between a compact and an
open neighborhood; a multiple step yields an essential loop, pushed along the
orbit, whose chart reading is null-homotopic after one step.
-/

open Function OnePoint Filter Topology

namespace NoWanderingDomains

/-- **The separation form of the covering dichotomy**: a component step of
fiber count at least two has a target whose sphere complement is
disconnected. Otherwise the finite part of the target would have only
unbounded complementary components, hence be simply connected by the
Riemann-mapping bridge, forcing fiber count one. -/
theorem not_isConnected_compl_of_multiple_step {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n) (hinf' : ∞ ∉ fcOrbit f U (n + 1))
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hk : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    ¬IsConnected ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) := by
  classical
  intro hcon
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  set W : Set ℂ̂ := fcOrbit f U (n + 1) with hWdef
  have hWfc : IsFatouComponent f W := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have hWopen : IsOpen W := hWfc.isOpen
  have hWconn : IsConnected W := hWfc.isConnected
  -- `W` avoids `∞`, hence lies in the range of the coercion.
  have hWrange : W ⊆ Set.range (fun w : ℂ => (w : ℂ̂)) := by
    intro w hw
    by_contra hnr
    have hweq : w = ∞ := OnePoint.notMem_range_coe_iff.mp hnr
    rw [hweq] at hw
    exact hinf' hw
  -- The finite part of the target component.
  set T : Set ℂ := (fun w : ℂ => (w : ℂ̂)) ⁻¹' W with hTdef
  have himg : (fun w : ℂ => (w : ℂ̂)) '' T = W :=
    Set.image_preimage_eq_of_subset hWrange
  have hTopen : IsOpen T := hWopen.preimage OnePoint.continuous_coe
  have hTne : T.Nonempty := by
    obtain ⟨w, hw⟩ := hWfc.nonempty
    obtain ⟨z0, rfl⟩ := hWrange hw
    exact ⟨z0, hw⟩
  have hTpre : IsPreconnected T := by
    have h1 : IsPreconnected ((fun w : ℂ => (w : ℂ̂)) '' T) := by
      rw [himg]
      exact hWconn.isPreconnected
    exact (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp h1
  have hTconn : IsConnected T := ⟨hTne, hTpre⟩
  -- The finite part is proper: the (infinite) Julia set misses `W`.
  have hTneq : T ≠ Set.univ := by
    intro hTuniv
    have hWeq : W = Set.range (fun w : ℂ => (w : ℂ̂)) := by
      rw [← himg, hTuniv, Set.image_univ]
    have hJsub : JuliaSet f ⊆ {∞} := by
      intro x hx
      have hxW : x ∉ W := fun hxW => hx (hWfc.subset_fatouSet hxW)
      rw [hWeq] at hxW
      rw [Set.mem_singleton_iff]
      exact OnePoint.notMem_range_coe_iff.mp hxW
    exact juliaSet_infinite hf hd ((Set.finite_singleton ∞).subset hJsub)
  -- Šura-Bura: every complementary component of `T` in the plane is
  -- unbounded, else a clopen separation of `Wᶜ` on the sphere appears.
  have hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z) := by
    intro z hzT hbdd
    have hzF : z ∈ (Tᶜ : Set ℂ) := hzT
    have hzC : z ∈ connectedComponentIn Tᶜ z := mem_connectedComponentIn hzF
    obtain ⟨R, hCR⟩ := hbdd.subset_ball (0 : ℂ)
    have hFclosed : IsClosed (Tᶜ : Set ℂ) := hTopen.isClosed_compl
    -- the compact truncation of the complement
    set K : Set ℂ := Tᶜ ∩ Metric.closedBall (0 : ℂ) R with hKdef
    have hKcomp : IsCompact K :=
      (isCompact_closedBall (0 : ℂ) R).inter_left hFclosed
    have hzK : z ∈ K := ⟨hzF, Metric.ball_subset_closedBall (hCR hzC)⟩
    have hCsubK : connectedComponentIn Tᶜ z ⊆ K := fun w hw =>
      ⟨connectedComponentIn_subset _ _ hw,
        Metric.ball_subset_closedBall (hCR hw)⟩
    -- the bounded component is a component of the truncation
    have hCeq : connectedComponentIn K z = connectedComponentIn Tᶜ z := by
      apply Set.Subset.antisymm
      · exact connectedComponentIn_mono z Set.inter_subset_left
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
          hzC hCsubK
    have hKcs : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcomp
    set z' : ↥K := ⟨z, hzK⟩ with hz'def
    have hcc : Subtype.val '' connectedComponent z' =
        connectedComponentIn Tᶜ z := by
      rw [hz'def, ← connectedComponentIn_eq_image hzK]
      exact hCeq
    -- the shell of the truncation, inside the subtype
    set E : Set ↥K := Subtype.val ⁻¹' (Metric.ball (0 : ℂ) R)ᶜ with hEdef
    have hEclosed : IsClosed E :=
      (Metric.isOpen_ball.isClosed_compl).preimage continuous_subtype_val
    have hEcomp : IsCompact E := hEclosed.isCompact
    -- the connected component of `z'` misses the shell
    have hccE : connectedComponent z' ∩ E = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨hwc, hwE⟩
      have hwC : (w : ℂ) ∈ connectedComponentIn Tᶜ z := by
        rw [← hcc]
        exact ⟨w, hwc, rfl⟩
      exact hwE (hCR hwC)
    -- Šura-Bura in the compact subtype: finitely many clopen neighbourhoods
    -- of `z'` already miss the shell
    have hdisj : E ∩ ⋂ (s : {s : Set ↥K // IsClopen s ∧ z' ∈ s}),
        (s : Set ↥K) = ∅ := by
      rw [← connectedComponent_eq_iInter_isClopen z', Set.inter_comm]
      exact hccE
    obtain ⟨u, hu⟩ := hEcomp.elim_finite_subfamily_closed
      (fun s : {s : Set ↥K // IsClopen s ∧ z' ∈ s} => (s : Set ↥K))
      (fun s => s.2.1.isClosed) hdisj
    have hu' : E ∩ ⋂ s ∈ u, (s : Set ↥K) = ∅ := hu
    set A' : Set ↥K := ⋂ s ∈ u, (s : Set ↥K) with hA'def
    have hA'clopen : IsClopen A' := isClopen_biInter_finset (fun s _ => s.2.1)
    have hz'A' : z' ∈ A' := Set.mem_iInter₂.mpr (fun s _ => s.2.2)
    -- the corresponding compact subset of the plane
    have hAcomp : IsCompact (Subtype.val '' A') :=
      (hA'clopen.isClosed.isCompact).image continuous_subtype_val
    have hzA : z ∈ Subtype.val '' A' := ⟨z', hz'A', rfl⟩
    have hAball : Subtype.val '' A' ⊆ Metric.ball (0 : ℂ) R := by
      rintro _ ⟨w, hwA', rfl⟩
      by_contra hnb
      have hwEmem : w ∈ E := hnb
      have hcontra : w ∈ E ∩ A' := ⟨hwEmem, hwA'⟩
      rw [hu'] at hcontra
      exact hcontra
    -- `A` is the trace on `Tᶜ` of an open subset of the ball
    obtain ⟨O₁, hO₁open, hO₁⟩ :=
      Topology.IsInducing.subtypeVal.isOpen_iff.mp hA'clopen.isOpen
    have hAeq : Subtype.val '' A' = Tᶜ ∩ (O₁ ∩ Metric.ball (0 : ℂ) R) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨w, hwA', rfl⟩
        refine ⟨w.2.1, ?_, hAball ⟨w, hwA', rfl⟩⟩
        have hw' : w ∈ Subtype.val ⁻¹' O₁ := by rw [hO₁]; exact hwA'
        exact hw'
      · rintro a ⟨haF, haO₁, haB⟩
        have haK : a ∈ K := ⟨haF, Metric.ball_subset_closedBall haB⟩
        have haA' : (⟨a, haK⟩ : ↥K) ∈ A' := by
          rw [← hO₁]
          exact haO₁
        exact ⟨⟨a, haK⟩, haA', rfl⟩
    -- transfer the clopen trace to the sphere complement `Wᶜ`
    have hpc : PreconnectedSpace ↥(Wᶜ : Set ℂ̂) :=
      Subtype.preconnectedSpace hcon.isPreconnected
    have hAscomp : IsCompact ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) :=
      hAcomp.image OnePoint.continuous_coe
    have hAsubClosed : IsClosed (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) :=
      hAscomp.isClosed.preimage continuous_subtype_val
    have hOs_open : IsOpen ((fun w : ℂ => (w : ℂ̂)) ''
        (O₁ ∩ Metric.ball (0 : ℂ) R)) :=
      OnePoint.isOpenEmbedding_coe.isOpenMap _
        (hO₁open.inter Metric.isOpen_ball)
    have hAsubEq : (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) =
        Subtype.val ⁻¹'
          ((fun w : ℂ => (w : ℂ̂)) '' (O₁ ∩ Metric.ball (0 : ℂ) R)) := by
      ext x
      simp only [Set.mem_preimage]
      constructor
      · rintro ⟨a, haA, hax⟩
        rw [hAeq] at haA
        exact ⟨a, haA.2, hax⟩
      · rintro ⟨a, haO, hax⟩
        have haT : a ∈ (Tᶜ : Set ℂ) := by
          intro haT'
          have hxW : (x : ℂ̂) ∈ (Wᶜ : Set ℂ̂) := x.2
          rw [← hax] at hxW
          exact hxW haT'
        rw [hAeq]
        exact ⟨a, ⟨haT, haO⟩, hax⟩
    have hAsubOpen : IsOpen (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) := by
      rw [hAsubEq]
      exact hOs_open.preimage continuous_subtype_val
    have hclopen : IsClopen (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) :=
      ⟨hAsubClosed, hAsubOpen⟩
    -- a clopen subset of the preconnected `Wᶜ` is empty or everything;
    -- both options fail
    rcases isClopen_iff.mp hclopen with hempty | huniv
    · have hzW : ((z : ℂ̂)) ∈ (Wᶜ : Set ℂ̂) := hzF
      have hmem : (⟨(z : ℂ̂), hzW⟩ : ↥(Wᶜ : Set ℂ̂)) ∈ (Subtype.val ⁻¹'
          ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) :=
        ⟨z, hzA, rfl⟩
      rw [hempty] at hmem
      exact hmem
    · have hinfW : (∞ : ℂ̂) ∈ (Wᶜ : Set ℂ̂) := hinf'
      have hmem : (⟨∞, hinfW⟩ : ↥(Wᶜ : Set ℂ̂)) ∈ (Subtype.val ⁻¹'
          ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) := by
        rw [huniv]
        exact Set.mem_univ _
      exact OnePoint.infty_notMem_image_coe hmem
  -- The Riemann-mapping bridge gives simple connectivity of the finite part,
  -- which transfers to the sphere component along the open embedding.
  have hsc : SimplyConnectedSpace T :=
    simplyConnectedSpace_of_unbounded_components hTopen hTconn hTneq hcompl
  have hscW : SimplyConnectedSpace (W : Set ℂ̂) := by
    have h1 : IsSimplyConnected ((fun w : ℂ => (w : ℂ̂)) '' T) :=
      (OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image).mpr hsc
    rw [himg] at h1
    exact h1.simplyConnectedSpace
  -- Degree one over a simply connected target contradicts `2 ≤ k`.
  have hk1 : k = 1 :=
    fiberCount_eq_one_of_simplyConnected hf hd hU n hinf hcrit hscW hk
  omega

/-- The Riemann sphere is locally path-connected: finite points have chart
balls, and a neighborhood basis at `∞` is given by complements of closed
balls, which are path-connected through radial rays. -/
instance instLocPathConnectedSphere : LocallyPathConnectedSpace ℂ̂ := by
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

open Complex Set in
/-- **Simply connected neighborhoods of full compact sets.** A nonempty
connected compact set all of whose complementary components are unbounded
admits, inside every open superset, an open simply connected neighborhood:
filled dyadic grid hulls of the set shrink down to it, so a sufficiently
fine filled hull separates it from the complement of the open superset, and
the filled hull's interior component around the set has connected unbounded
complement, hence is simply connected by the Riemann-mapping bridge. -/
theorem exists_simplyConnectedSpace_between {K T : Set ℂ} (hK : IsCompact K)
    (hKconn : IsConnected K)
    (hKfull : ∀ z ∉ K, ¬Bornology.IsBounded (connectedComponentIn Kᶜ z))
    (hT : IsOpen T) (hKT : K ⊆ T) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ W ⊆ T ∧ SimplyConnectedSpace W := by
  classical
  -- ------------------------------------------------------------------
  -- Setup: base point, radius bound, far point `zf`, far region.
  -- ------------------------------------------------------------------
  obtain ⟨x₀, hx₀⟩ := hKconn.nonempty
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 + 3 with hRdef
  have hR3 : (3 : ℝ) ≤ R := by
    have h := le_max_right R₀ 0
    rw [hRdef]
    linarith
  have hKR : K ⊆ Metric.closedBall (0 : ℂ) (R - 3) := by
    intro z hz
    have h1 := hR₀ hz
    rw [Metric.mem_closedBall] at h1 ⊢
    have h2 : R₀ ≤ max R₀ 0 := le_max_left _ _
    rw [hRdef]
    linarith
  set zf : ℂ := (R : ℂ) with hzfdef
  have hzfnorm : ‖zf‖ = R := by
    rw [hzfdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ R)]
  have hAconn : IsConnected {z : ℂ | R - 1 < ‖z‖} := isConnected_setOf_lt_norm (R - 1)
  have hzfA : zf ∈ {z : ℂ | R - 1 < ‖z‖} := by
    rw [Set.mem_ofPred_eq, hzfnorm]; linarith
  have hAunb : ¬Bornology.IsBounded {z : ℂ | R - 1 < ‖z‖} := by
    intro hb
    obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : ℂ)
    set w : ℂ := ((max r (R - 1) + 1 : ℝ) : ℂ) with hwdef
    have hw1 : R - 1 ≤ max r (R - 1) := le_max_right r (R - 1)
    have hwnorm : ‖w‖ = max r (R - 1) + 1 := by
      rw [hwdef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ max r (R - 1) + 1)]
    have hwA : w ∈ {z : ℂ | R - 1 < ‖z‖} := by
      rw [Set.mem_ofPred_eq, hwnorm]; linarith
    have h2 := hr hwA
    rw [Metric.mem_closedBall, dist_zero_right, hwnorm] at h2
    have h3 : r ≤ max r (R - 1) := le_max_left r (R - 1)
    linarith
  -- ------------------------------------------------------------------
  -- Closed thickenings `N r`, unbounded components `U r`, fills `F r`.
  -- ------------------------------------------------------------------
  set N : ℝ → Set ℂ := fun r => {z : ℂ | Metric.infDist z K ≤ r} with hNdef
  set U : ℝ → Set ℂ := fun r => connectedComponentIn (N r)ᶜ zf with hUdef
  set F : ℝ → Set ℂ := fun r => (U r)ᶜ with hFdef
  have hNmem : ∀ (r : ℝ) (z : ℂ), z ∈ N r ↔ Metric.infDist z K ≤ r := fun r z => Iff.rfl
  have hFmem : ∀ (r : ℝ) (z : ℂ), z ∈ F r ↔ z ∉ U r := fun r z => Iff.rfl
  have hNclosed : ∀ r : ℝ, IsClosed (N r) := by
    intro r
    rw [hNdef]
    exact isClosed_le (Metric.continuous_infDist_pt K) continuous_const
  have hNball : ∀ r : ℝ, r ≤ 1 → N r ⊆ Metric.ball (0 : ℂ) (R - 1) := by
    intro r hr z hz
    rw [hNmem] at hz
    have h2 : Metric.infDist z K < 2 := lt_of_le_of_lt hz (by linarith)
    obtain ⟨v, hvK, hvd⟩ := (Metric.infDist_lt_iff ⟨x₀, hx₀⟩).mp h2
    have h3 := hKR hvK
    rw [Metric.mem_closedBall] at h3
    rw [Metric.mem_ball]
    calc dist z 0 ≤ dist z v + dist v 0 := dist_triangle _ _ _
      _ < 2 + (R - 3) := by linarith
      _ = R - 1 := by ring
  have hAN : ∀ r : ℝ, r ≤ 1 → {z : ℂ | R - 1 < ‖z‖} ⊆ (N r)ᶜ := by
    intro r hr z hz hzN
    have h1 := hNball r hr hzN
    rw [Metric.mem_ball, dist_zero_right] at h1
    rw [Set.mem_ofPred_eq] at hz
    linarith
  have hUopen : ∀ r : ℝ, IsOpen (U r) := by
    intro r
    rw [hUdef]
    exact (hNclosed r).isOpen_compl.connectedComponentIn
  have hUsub : ∀ r : ℝ, U r ⊆ (N r)ᶜ := by
    intro r
    rw [hUdef]
    exact connectedComponentIn_subset _ _
  have hAU : ∀ r : ℝ, r ≤ 1 → {z : ℂ | R - 1 < ‖z‖} ⊆ U r := by
    intro r hr
    rw [hUdef]
    exact hAconn.isPreconnected.subset_connectedComponentIn hzfA (hAN r hr)
  have hzfU : ∀ r : ℝ, r ≤ 1 → zf ∈ U r := fun r hr => hAU r hr hzfA
  have hUpre : ∀ r : ℝ, IsPreconnected (U r) := by
    intro r
    rw [hUdef]
    exact isPreconnected_connectedComponentIn
  have hNF : ∀ r : ℝ, N r ⊆ F r := by
    intro r z hz
    rw [hFmem]
    intro hzU
    exact hUsub r hzU hz
  have hFsub : ∀ r : ℝ, r ≤ 1 → F r ⊆ Metric.closedBall (0 : ℂ) (R - 1) := by
    intro r hr z hz
    by_contra hzb
    have hzA : z ∈ {v : ℂ | R - 1 < ‖v‖} := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hzb
      exact hzb
    exact (hFmem r z).mp hz (hAU r hr hzA)
  have hUmono : ∀ r s : ℝ, r ≤ s → s ≤ 1 → U s ⊆ U r := by
    intro r s hrs hs1
    have hNrs : N r ⊆ N s := by
      intro z hz
      rw [hNmem] at hz ⊢
      linarith
    have h1 : U s ⊆ (N r)ᶜ := (hUsub s).trans (compl_subset_compl.mpr hNrs)
    rw [hUdef]
    exact (hUpre s).subset_connectedComponentIn (hzfU s hs1) h1
  have hFmono : ∀ r s : ℝ, r ≤ s → s ≤ 1 → F r ⊆ F s := by
    intro r s hrs hs1
    rw [hFdef]
    exact compl_subset_compl.mpr (hUmono r s hrs hs1)
  have hFclosed : ∀ r : ℝ, IsClosed (F r) := by
    intro r
    rw [hFdef]
    exact (hUopen r).isClosed_compl
  have hFcompact : ∀ r : ℝ, r ≤ 1 → IsCompact (F r) := fun r hr =>
    Metric.isCompact_of_isClosed_isBounded (hFclosed r)
      (Metric.isBounded_closedBall.subset (hFsub r hr))
  have hδ1 : ∀ k : ℕ, ((2:ℝ)⁻¹ ^ k) ≤ 1 := fun k =>
    pow_le_one₀ (by norm_num) (by norm_num)
  -- ------------------------------------------------------------------
  -- Escape: every point outside `K` escapes some fine fill.
  -- ------------------------------------------------------------------
  have hesc : ∀ x, x ∉ K → ∃ k : ℕ, x ∉ F ((2:ℝ)⁻¹ ^ k) := by
    intro x hxK
    -- the component of `x` in `Kᶜ` is open, connected and unbounded
    have hxKc : x ∈ Kᶜ := hxK
    have hCopen : IsOpen (connectedComponentIn Kᶜ x) :=
      hK.isClosed.isOpen_compl.connectedComponentIn
    have hCconn : IsConnected (connectedComponentIn Kᶜ x) :=
      ⟨⟨x, mem_connectedComponentIn hxKc⟩, isPreconnected_connectedComponentIn⟩
    -- pick a far point `y₀` of the component
    have hfar : ∃ y₀ ∈ connectedComponentIn Kᶜ x, R - 1 < ‖y₀‖ := by
      by_contra hno
      push Not at hno
      refine hKfull x hxK
        ((Metric.isBounded_closedBall (x := (0:ℂ)) (r := R - 1)).subset ?_)
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hno y hy
    obtain ⟨y₀, hy₀C, hy₀far⟩ := hfar
    -- a path from `x` to `y₀` inside the component
    have hCpath : IsPathConnected (connectedComponentIn Kᶜ x) :=
      hCopen.isConnected_iff_isPathConnected.mp hCconn
    obtain ⟨γ, hγ⟩ := hCpath.joinedIn x (mem_connectedComponentIn hxKc) y₀ hy₀C
    -- its image is a compact connected set avoiding `K`
    have hLcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
    have hLconn : IsConnected (Set.range γ) := isConnected_range γ.continuous
    have hLK : ∀ y ∈ Set.range γ, y ∉ K := by
      rintro y ⟨t, rfl⟩ hyK
      exact connectedComponentIn_subset Kᶜ x (hγ t) hyK
    -- uniform positive distance from the path image to `K`
    have hinf_cont : ContinuousOn (fun y : ℂ => Metric.infDist y K) (Set.range γ) :=
      (Metric.continuous_infDist_pt K).continuousOn
    obtain ⟨ymin, hyminL, hyminOn⟩ :=
      hLcompact.exists_isMinOn ⟨x, 0, γ.source⟩ hinf_cont
    have hymin : ∀ y ∈ Set.range γ, Metric.infDist ymin K ≤ Metric.infDist y K :=
      isMinOn_iff.mp hyminOn
    have hρpos : 0 < Metric.infDist ymin K := by
      rcases (Metric.infDist_nonneg (s := K) (x := ymin)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hycl : ymin ∈ closure K :=
          (Metric.mem_closure_iff_infDist_zero ⟨x₀, hx₀⟩).mpr h.symm
        rw [hK.isClosed.closure_eq] at hycl
        exact hLK ymin hyminL hycl
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρpos (by norm_num : (2:ℝ)⁻¹ < 1)
    refine ⟨k, ?_⟩
    -- the path image avoids the thickening, hence sits in `U`
    have hLN : Set.range γ ⊆ (N ((2:ℝ)⁻¹ ^ k))ᶜ := by
      intro y hyL
      rw [Set.mem_compl_iff]
      intro hyN
      rw [hNmem] at hyN
      have h1 := hymin y hyL
      linarith
    have hy₀U : y₀ ∈ U ((2:ℝ)⁻¹ ^ k) := hAU _ (hδ1 k) hy₀far
    have hLU : Set.range γ ⊆ U ((2:ℝ)⁻¹ ^ k) := by
      have h1 : U ((2:ℝ)⁻¹ ^ k) = connectedComponentIn (N ((2:ℝ)⁻¹ ^ k))ᶜ y₀ := by
        rw [hUdef]
        exact connectedComponentIn_eq hy₀U
      rw [h1]
      exact hLconn.isPreconnected.subset_connectedComponentIn ⟨1, γ.target⟩ hLN
    have hxU : x ∈ U ((2:ℝ)⁻¹ ^ k) := hLU ⟨0, γ.source⟩
    exact fun hxF => (hFmem _ x).mp hxF hxU
  -- ------------------------------------------------------------------
  -- Selection: some fine fill separates `K` from `Tᶜ`.
  -- ------------------------------------------------------------------
  have hsel : ∃ k : ℕ, F ((2:ℝ)⁻¹ ^ k) ⊆ T := by
    by_contra hno
    push Not at hno
    have hne : ∀ k : ℕ, (F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ).Nonempty := by
      intro k
      obtain ⟨z, hzF, hzT⟩ := Set.not_subset.mp (hno k)
      exact ⟨z, hzF, hzT⟩
    have hanti : Antitone (fun k : ℕ => F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ) := by
      intro k l hkl
      exact Set.inter_subset_inter_left _
        (hFmono _ _ (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl) (hδ1 k))
    have hGcompact : ∀ k : ℕ, IsCompact (F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ) := fun k =>
      (hFcompact _ (hδ1 k)).inter_right hT.isClosed_compl
    have hGclosed : ∀ k : ℕ, IsClosed (F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ) := fun k =>
      (hFclosed _).inter hT.isClosed_compl
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      _ hanti.directed_ge hne hGcompact hGclosed
    rw [Set.mem_iInter] at hx
    have hxT : x ∈ Tᶜ := (hx 0).2
    have hxK : x ∉ K := fun hxK => hxT (hKT hxK)
    obtain ⟨k, hk⟩ := hesc x hxK
    exact hk (hx k).1
  obtain ⟨k0, hFT⟩ := hsel
  set δ : ℝ := (2:ℝ)⁻¹ ^ k0 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle1 : δ ≤ 1 := hδ1 k0
  -- ------------------------------------------------------------------
  -- The neighborhood: interior of the fill, component around `K`.
  -- ------------------------------------------------------------------
  have hKint : K ⊆ interior (F δ) := by
    intro z hz
    rw [mem_interior]
    refine ⟨Metric.ball z δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδpos⟩
    intro y hy
    refine hNF δ ?_
    rw [hNmem]
    rw [Metric.mem_ball] at hy
    exact le_of_lt (lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hz) hy)
  set W₀ : Set ℂ := interior (F δ) with hW₀def
  set W : Set ℂ := connectedComponentIn W₀ x₀ with hWdef
  have hW₀open : IsOpen W₀ := isOpen_interior
  have hWopen : IsOpen W := hW₀open.connectedComponentIn
  have hKW : K ⊆ W := hKconn.isPreconnected.subset_connectedComponentIn hx₀ hKint
  have hWW₀ : W ⊆ W₀ := connectedComponentIn_subset _ _
  have hW₀F : W₀ ⊆ F δ := interior_subset
  have hWT : W ⊆ T := fun z hz => hFT (hW₀F (hWW₀ hz))
  have hWconn : IsConnected W := ⟨⟨x₀, mem_connectedComponentIn (hKint hx₀)⟩,
    isPreconnected_connectedComponentIn⟩
  -- ------------------------------------------------------------------
  -- Complement analysis: `Wᶜ` is preconnected and unbounded.
  -- ------------------------------------------------------------------
  have hzfF : zf ∉ F δ := fun h => (hFmem δ zf).mp h (hzfU δ hδle1)
  have hzfW₀ : zf ∉ W₀ := fun h => hzfF (hW₀F h)
  have hzfW : zf ∉ W := fun h => hzfW₀ (hWW₀ h)
  have hFc : (F δ)ᶜ = U δ := compl_compl (U δ)
  have hW₀c : W₀ᶜ = closure (U δ) := by
    rw [hW₀def, ← closure_compl, hFc]
  have hCpre : IsPreconnected W₀ᶜ := by
    rw [hW₀c]
    exact (hUpre δ).closure
  have hzfC : zf ∈ W₀ᶜ := hzfW₀
  -- every point of `Wᶜ` lies in a preconnected subset of `Wᶜ` containing `zf`
  have hWcov : Wᶜ = ⋃₀ {E : Set ℂ | E ⊆ Wᶜ ∧ IsPreconnected E ∧ zf ∈ E} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hzW₀ : z ∈ W₀
      · -- the component `V` of `z` in `W₀`, glued with the outer part `W₀ᶜ`
        have hzV : z ∈ connectedComponentIn W₀ z := mem_connectedComponentIn hzW₀
        have hVW : ∀ v ∈ connectedComponentIn W₀ z, v ∉ W := by
          intro v hvV hvW
          have h1 : connectedComponentIn W₀ x₀ = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hvW
          have h2 : connectedComponentIn W₀ z = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hvV
          have h3 : z ∈ connectedComponentIn W₀ x₀ := by
            rw [h1, ← h2]
            exact hzV
          exact hz h3
        -- closure points of the component inside `W₀` belong to the component
        have hcloV : closure (connectedComponentIn W₀ z) ∩ W₀ ⊆
            connectedComponentIn W₀ z := by
          rintro y ⟨hycl, hyW₀⟩
          have hyy : y ∈ connectedComponentIn W₀ y := mem_connectedComponentIn hyW₀
          obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.mp hycl _
            (hW₀open.connectedComponentIn (x := y)) hyy
          have h1 : connectedComponentIn W₀ y = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hv1
          have h2 : connectedComponentIn W₀ z = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hv2
          rw [h2, ← h1]
          exact hyy
        -- the closure of the component must reach the outer part
        have hfront : (closure (connectedComponentIn W₀ z) ∩ W₀ᶜ).Nonempty := by
          rcases (closure (connectedComponentIn W₀ z) ∩ W₀ᶜ).eq_empty_or_nonempty with
            hemp | hne
          · exfalso
            have hclsub : closure (connectedComponentIn W₀ z) ⊆ W₀ := by
              intro y hy
              by_contra hyW₀
              have hmem : y ∈ closure (connectedComponentIn W₀ z) ∩ W₀ᶜ := ⟨hy, hyW₀⟩
              rw [hemp] at hmem
              exact hmem
            have hVclosed : IsClosed (connectedComponentIn W₀ z) :=
              isClosed_of_closure_subset (fun y hy => hcloV ⟨hy, hclsub hy⟩)
            have hVclopen : IsClopen (connectedComponentIn W₀ z) :=
              ⟨hVclosed, hW₀open.connectedComponentIn⟩
            rcases isClopen_iff.mp hVclopen with h | h
            · rw [h] at hzV
              exact hzV
            · have hzfV : zf ∈ connectedComponentIn W₀ z := by
                rw [h]; exact Set.mem_univ zf
              exact hzfW₀ (connectedComponentIn_subset _ _ hzfV)
          · exact hne
        obtain ⟨w, hwcl, hwC⟩ := hfront
        apply Set.mem_sUnion.mpr
        refine ⟨closure (connectedComponentIn W₀ z) ∪ W₀ᶜ, ⟨?_, ?_, ?_⟩,
          Set.mem_union_left _ (subset_closure hzV)⟩
        · rintro y (hy | hy)
          · rw [Set.mem_compl_iff]
            intro hyW
            obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.mp hy W hWopen hyW
            exact hVW v hv2 hv1
          · exact compl_subset_compl.mpr hWW₀ hy
        · exact IsPreconnected.union w hwcl hwC
            isPreconnected_connectedComponentIn.closure hCpre
        · exact Set.mem_union_right _ hzfC
      · exact Set.mem_sUnion.mpr ⟨W₀ᶜ, ⟨compl_subset_compl.mpr hWW₀, hCpre, hzfC⟩, hzW₀⟩
    · rintro z ⟨E, ⟨hEW, -, -⟩, hzE⟩
      exact hEW hzE
  have hWcpre : IsPreconnected Wᶜ := by
    rw [hWcov]
    exact isPreconnected_sUnion zf _ (fun E hE => hE.2.2) (fun E hE => hE.2.1)
  have hAWc : {z : ℂ | R - 1 < ‖z‖} ⊆ Wᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzW
    exact (hFmem δ z).mp (hW₀F (hWW₀ hzW)) (hAU δ hδle1 hz)
  have hWne : W ≠ Set.univ := by
    intro h
    rw [h] at hzfW
    exact hzfW (Set.mem_univ zf)
  have hcompl : ∀ z ∉ W, ¬Bornology.IsBounded (connectedComponentIn Wᶜ z) := by
    intro z hz hbd
    have h1 : Wᶜ ⊆ connectedComponentIn Wᶜ z :=
      hWcpre.subset_connectedComponentIn hz (subset_refl _)
    exact hAunb (hbd.subset (hAWc.trans h1))
  exact ⟨W, hWopen, hKW, hWT,
    simplyConnectedSpace_of_unbounded_components hWopen hWconn hWne hcompl⟩

/-- **Essential loops at a multiple step.** A component step of fiber count
at least two admits a closed loop in the finite chart of its target
together with a Julia point about which the loop has nonzero winding
number: the target's sphere complement is disconnected, a bounded
complementary component provides a Julia-meeting continuum, and the grid
boundary construction yields the essential loop. -/
theorem exists_essential_loop_of_multiple_step {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n) (hinf' : ∞ ∉ fcOrbit f U (n + 1))
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hk : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    ∃ (γ : C(unitInterval, ℂ)) (z₁ : ℂ), γ 0 = γ 1 ∧
      (∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U (n + 1)) ∧
      ((z₁ : ℂ̂)) ∈ JuliaSet f ∧ windingNumber γ z₁ ≠ 0 := by
  classical
  have hd1 : (1 : ℕ) ≤ degreeOfRational f := le_trans one_le_two hd
  -- Step A: a compact preconnected Julia-meeting continuum in the complement
  -- of the target component's finite part.
  have hcontinuum :
      ∃ z₀ : ℂ,
        z₀ ∈ connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} z₀ ∧
        IsCompact (connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} z₀) ∧
        (∃ z ∈ connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} z₀,
          ((z : ℂ̂)) ∈ JuliaSet f) := by
    have hVfc : IsFatouComponent f (fcOrbit f U (n + 1)) :=
      isFatouComponent_fcOrbit (n + 1) hf hd1 hU
    -- the black-box separation form of the covering dichotomy
    have hnc : ¬IsConnected ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) :=
      not_isConnected_compl_of_multiple_step hf hd hU n hinf hinf'
        hcrit hk2 hk
    obtain ⟨z₀, hz₀, hbdd⟩ := exists_bounded_component_of_not_isConnected_compl
      hVfc.isOpen hVfc.nonempty hinf' hnc
    set F : Set ℂ := {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} with hFdef
    set C : Set ℂ := connectedComponentIn F z₀ with hCdef
    have hz₀F : z₀ ∈ F := hz₀
    have hz₀C : z₀ ∈ C := mem_connectedComponentIn hz₀F
    have hCsub : C ⊆ F := connectedComponentIn_subset _ _
    -- the complement set is closed in the plane
    have hFclosed : IsClosed F :=
      (hVfc.isOpen.isClosed_compl).preimage OnePoint.continuous_coe
    -- a connected component of a closed set is closed, hence compact
    have hCclosed : IsClosed C := by
      rw [hCdef, connectedComponentIn_eq_image hz₀F]
      exact hFclosed.isClosedEmbedding_subtypeVal.isClosedMap _
        isClosed_connectedComponent
    have hCcpt : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCclosed hbdd
    refine ⟨z₀, hz₀C, hCcpt, ?_⟩
    -- the frontier of the bounded component is nonempty
    have : PreconnectedSpace ℂ := ⟨(convex_univ (𝕜 := ℝ) (E := ℂ)).isPreconnected⟩
    have hCne : C.Nonempty := ⟨z₀, hz₀C⟩
    have hfrne : (frontier C).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hopen : IsOpen C := by
        have h1 : C \ interior C = ∅ := by rw [← hCclosed.frontier_eq]; exact hemp
        have h2 : interior C = C :=
          Set.Subset.antisymm interior_subset (Set.sdiff_eq_empty.mp h1)
        rw [← h2]; exact isOpen_interior
      rcases isClopen_iff.mp ⟨hCclosed, hopen⟩ with h | h
      · exact hCne.ne_empty h
      · have hub : Bornology.IsBounded (Set.univ : Set ℂ) := h ▸ hbdd
        obtain ⟨R, hR⟩ := hub.subset_closedBall 0
        have := hR (Set.mem_univ ((R + 1 : ℝ) : ℂ))
        rw [Metric.mem_closedBall, dist_zero_right] at this
        simp only [Complex.norm_real, Real.norm_eq_abs] at this
        cases abs_le.mp this with
        | intro h1 h2 => nlinarith [abs_nonneg R, le_abs_self R]
    obtain ⟨x, hxfr⟩ := hfrne
    have hxC : x ∈ C := hCclosed.closure_eq ▸ frontier_subset_closure hxfr
    -- a frontier point of the component is a frontier point of the whole
    -- closed complement set (maximality of the component swallows balls)
    have hxniF : x ∉ interior F := by
      intro hxint
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      have hballF : Metric.ball x ε ⊆ F := fun y hy => interior_subset (hball hy)
      have hballC : Metric.ball x ε ⊆ C := by
        rw [hCdef, connectedComponentIn_eq hxC]
        exact (convex_ball x ε).isPreconnected.subset_connectedComponentIn
          (Metric.mem_ball_self hε) hballF
      exact hxfr.2 ((interior_maximal hballC Metric.isOpen_ball) (Metric.mem_ball_self hε))
    have hxfrF : x ∈ frontier F := ⟨subset_closure (hCsub hxC), hxniF⟩
    -- transport the frontier through the coercion into the sphere
    have hFeq : F = ((↑) : ℂ → ℂ̂) ⁻¹' ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) := rfl
    have hfrsub : ((x : ℂ̂)) ∈ frontier ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) := by
      have h1 : closure (((↑) : ℂ → ℂ̂) ⁻¹' ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂)) ⊆
          ((↑) : ℂ → ℂ̂) ⁻¹' closure ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) :=
        OnePoint.continuous_coe.closure_preimage_subset _
      have h2 : ((↑) : ℂ → ℂ̂) ⁻¹' interior ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂)
          ⊆ interior (((↑) : ℂ → ℂ̂) ⁻¹' ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂)) :=
        preimage_interior_subset_interior_preimage OnePoint.continuous_coe
      rw [hFeq] at hxfrF
      exact ⟨h1 hxfrF.1, fun hint => hxfrF.2 (h2 hint)⟩
    rw [frontier_compl] at hfrsub
    exact ⟨x, hxC, hVfc.frontier_subset_juliaSet hfrsub⟩
  have hessloop : ∀ T : Set ℂ, IsOpen T → ∀ z₀ : ℂ, z₀ ∉ T →
      Bornology.IsBounded (connectedComponentIn Tᶜ z₀) →
      ∃ lam : C(unitInterval, ℂ), lam 0 = lam 1 ∧ (∀ t : unitInterval, lam t ∈ T) ∧
        windingNumber lam z₀ ≠ 0 := by
    intro T hT z₀ hz₀T hbdd
    -- ---------------------------------------------------------------
    -- Inner grid stage: black box exists_gridLoop_winding_ne_zero
    -- (GridPrimitives/Loop.lean) — the grid boundary loop of the union of
    -- δ-squares meeting the separated compact piece A.
    -- ---------------------------------------------------------------
    have hgrid : ∀ (A : Set ℂ) (ε : ℝ), 0 < ε → IsCompact A → z₀ ∈ A → A ⊆ Tᶜ →
        (∀ w ∈ Tᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a) →
        ∃ lam : C(unitInterval, ℂ), lam 0 = lam 1 ∧ (∀ t : unitInterval, lam t ∈ T) ∧
          windingNumber lam z₀ ≠ 0 := by
      intro A ε hε hA hzA hAT hsep
      exact exists_gridLoop_winding_ne_zero hT A ε hε hA hzA hAT hsep
    -- ---------------------------------------------------------------
    -- Outer stage (Šura-Bura separation): the bounded component C of the
    -- closed complement F := Tᶜ through z₀ admits a compact piece A ⊇ C
    -- that is relatively clopen in F, hence metrically separated from
    -- F \ A.  Work in the compact subspace K := F ∩ closedBall 0 (R + 1):
    -- there the connected component of z₀ is the intersection of its
    -- clopen neighborhoods, and compactness of the boundary shell yields
    -- a single clopen neighborhood A'' avoiding the shell.
    -- ---------------------------------------------------------------
    set F : Set ℂ := Tᶜ with hFdef
    have hFclosed : IsClosed F := hT.isClosed_compl
    have hz₀F : z₀ ∈ F := hz₀T
    set C : Set ℂ := connectedComponentIn F z₀ with hCdef
    have hz₀C : z₀ ∈ C := mem_connectedComponentIn hz₀F
    have hCsub : C ⊆ F := connectedComponentIn_subset _ _
    obtain ⟨R, hRC⟩ := hbdd.subset_closedBall 0
    set K : Set ℂ := F ∩ Metric.closedBall 0 (R + 1) with hKdef
    have hKcpt : IsCompact K :=
      (isCompact_closedBall 0 (R + 1)).inter_left hFclosed
    have hCK : C ⊆ K := by
      intro x hx
      exact ⟨hCsub hx, Metric.closedBall_subset_closedBall (by linarith) (hRC hx)⟩
    have hz₀K : z₀ ∈ K := hCK hz₀C
    -- the component in K agrees with the component in F
    have hCKeq : connectedComponentIn K z₀ = C := by
      apply Set.Subset.antisymm
      · exact connectedComponentIn_mono _ (Set.inter_subset_left)
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hz₀C hCK
    -- the boundary shell of K, compact and missed by C
    set W : Set ℂ := K \ Metric.ball 0 (R + 1) with hWdef
    have hCW : C ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxC hxW
      apply hxW.2
      have hx := hRC hxC
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    -- pass to the compact subspace K
    have : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    set z₀' : K := ⟨z₀, hz₀K⟩ with hz₀'def
    have hccinter := connectedComponent_eq_iInter_isClopen z₀'
    have hWclosed : IsClosed W := hKcpt.isClosed.sdiff Metric.isOpen_ball
    have hW'cpt : IsCompact (Subtype.val ⁻¹' W : Set K) :=
      (hWclosed.preimage continuous_subtype_val).isCompact
    -- the shell misses every point of the component of z₀ in K
    have hdisj : (Subtype.val ⁻¹' W : Set K) ∩
        (⋂ Z : {Z : Set K // IsClopen Z ∧ z₀' ∈ Z}, (Z : Set K)) = ∅ := by
      rw [← hccinter]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxW hxcc
      have hximg : (x : ℂ) ∈ connectedComponentIn K z₀ := by
        rw [connectedComponentIn_eq_image hz₀K]
        exact ⟨x, hxcc, rfl⟩
      rw [hCKeq] at hximg
      have hmem : (x : ℂ) ∈ C ∩ W := ⟨hximg, hxW⟩
      rw [hCW] at hmem
      exact hmem
    -- compactness of the shell extracts a single clopen neighborhood
    obtain ⟨u, hu⟩ := hW'cpt.elim_finite_subfamily_closed
      (fun Z : {Z : Set K // IsClopen Z ∧ z₀' ∈ Z} => (Z : Set K))
      (fun Z => Z.2.1.isClosed) hdisj
    set A'' : Set K := ⋂ Z ∈ u, (Z : Set K) with hA''def
    have hA''clopen : IsClopen A'' := by
      apply Set.Finite.isClopen_biInter u.finite_toSet
      intro Z _
      exact Z.2.1
    have hz₀A'' : z₀' ∈ A'' := by
      rw [hA''def]
      exact Set.mem_biInter fun Z _ => Z.2.2
    -- the piece downstairs: compact, clopen in F, containing C, off the shell
    set A : Set ℂ := Subtype.val '' A'' with hAdef
    have hA''cpt : IsCompact A'' := hA''clopen.isClosed.isCompact
    have hAcpt : IsCompact A := hA''cpt.image continuous_subtype_val
    have hz₀A : z₀ ∈ A := ⟨z₀', hz₀A'', rfl⟩
    have hAK : A ⊆ K := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have hAF : A ⊆ F := fun x hx => (hAK hx).1
    have hAW : A ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨y, hyA'', rfl⟩ hxW
      have hmem : y ∈ (Subtype.val ⁻¹' W : Set K) ∩ ⋂ Z ∈ u, (Z : Set K) :=
        ⟨hxW, hyA''⟩
      rw [hu] at hmem
      exact hmem
    -- A is relatively open in F
    obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hA''clopen.isOpen
    have hAeq : A = F ∩ (V ∩ Metric.ball 0 (R + 1)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hyA'', rfl⟩
        refine ⟨y.2.1, ?_, ?_⟩
        · rw [← hVeq] at hyA''
          exact hyA''
        · by_contra hball
          have hmem : (y : ℂ) ∈ A ∩ W := ⟨⟨y, hyA'', rfl⟩, ⟨y.2, hball⟩⟩
          rw [hAW] at hmem
          exact hmem
      · rintro x ⟨hxF, hxV, hxball⟩
        have hxK : x ∈ K := ⟨hxF, Metric.ball_subset_closedBall hxball⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        rw [← hVeq]
        exact hxV
    have hFAclosed : IsClosed (F \ A) := by
      rw [hAeq, Set.sdiff_self_inter]
      exact hFclosed.sdiff (hVopen.inter Metric.isOpen_ball)
    -- metric separation of the compact clopen piece from the rest
    have hdisjAB : Disjoint A (F \ A) := disjoint_sdiff_self_right
    obtain ⟨ε, hε, hthick⟩ := hdisjAB.exists_thickenings hAcpt hFAclosed
    have hsep : ∀ w ∈ Tᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a := by
      intro w hwF hwA a haA
      by_contra hlt
      push Not at hlt
      have hw₁ : w ∈ Metric.thickening ε A :=
        Metric.mem_thickening_iff.mpr ⟨a, haA, hlt⟩
      have hw₂ : w ∈ Metric.thickening ε (F \ A) :=
        Metric.self_subset_thickening hε _ ⟨hwF, hwA⟩
      exact (Set.disjoint_left.mp hthick hw₁) hw₂
    exact hgrid A ε hε hAcpt hz₀A hAF hsep
  obtain ⟨z₁, hz₁mem, hz₁cpt, hz₁J⟩ := hcontinuum
  set F₁ : Set ℂ := {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} with hF₁def
  set C₁ : Set ℂ := connectedComponentIn F₁ z₁ with hC₁def
  set T₁ : Set ℂ := {w : ℂ | (w : ℂ̂) ∈ fcOrbit f U (n + 1)} with hT₁def
  have hT₁open : IsOpen T₁ :=
    (isFatouComponent_fcOrbit (n + 1) hf hd1 hU).isOpen.preimage OnePoint.continuous_coe
  have hT₁compl : T₁ᶜ = F₁ := by
    ext w; simp [hT₁def, hF₁def]
  have hC₁sub : C₁ ⊆ F₁ := connectedComponentIn_subset _ _
  have hz₁F : z₁ ∈ F₁ := hC₁sub hz₁mem
  have hz₁T : z₁ ∉ T₁ := by
    intro h
    exact hz₁F h
  obtain ⟨lam, hlamcl, hlammem, hlamwind⟩ :=
    hessloop T₁ hT₁open z₁ hz₁T (by rw [hT₁compl]; exact hz₁cpt.isBounded)
  -- the loop trace avoids the continuum
  have hlamC₁ : ∀ t : unitInterval, lam t ∉ C₁ := fun t ht => hC₁sub ht (hlammem t)
  -- winding is constant on the preconnected continuum
  have hwconst : ∀ z ∈ C₁, windingNumber lam z = windingNumber lam z₁ := by
    intro z hz
    exact windingNumber_eq_of_preconnected hlamcl isPreconnected_connectedComponentIn
      hlamC₁ hz hz₁mem
  obtain ⟨zJ, hzJC, hzJJ⟩ := hz₁J
  refine ⟨lam, zJ, hlamcl, ?_, hzJJ, ?_⟩
  · intro t
    have h := hlammem t
    rw [hT₁def] at h
    exact h
  · rw [hwconst zJ hzJC]
    exact hlamwind

/-- Forward images of a chart loop under the iterates, read back in the
finite chart, are continuous chart loops: the orbit components avoid `∞`,
so the readings stay finite. -/
theorem exists_pushed_curve {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)}
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀) (m : ℕ) :
    ∃ Γ : C(unitInterval, ℂ),
      ∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂))) := by
  classical
  have hd1 : (1 : ℕ) ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  -- One-step transport: the forward reading of a chart curve in the next
  -- orbit component is a continuous chart curve (no poles on the trace).
  have hstep : ∀ (Γ : C(unitInterval, ℂ)) (j : ℕ),
      (∀ t : unitInterval, ((Γ t : ℂ̂)) ∈ fcOrbit f U j) →
      ∃ Γ' : C(unitInterval, ℂ),
        (∀ t : unitInterval, Γ' t = chartFiniteMap (f ((Γ t : ℂ̂)))) ∧
        (∀ t : unitInterval, ((Γ' t : ℂ̂)) ∈ fcOrbit f U (j + 1)) := by
    intro Γ j hΓmem
    -- the finite reading of the sphere map on finite points
    have hreadIf : ∀ w : ℂ, r.toSphereMap ((w : ℂ̂))
        = if r.denReduced.eval w = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := fun _ => rfl
    -- the map sends the trace into the next orbit component
    have hnext : ∀ t : unitInterval, f ((Γ t : ℂ̂)) ∈ fcOrbit f U (j + 1) := by
      intro t
      rw [← fcOrbit_image_eq hf hd1 hU j]
      exact ⟨((Γ t : ℂ̂)), hΓmem t, rfl⟩
    -- no poles on the trace: a pole would map to ∞ in the next component
    have hDΓ : ∀ t : unitInterval, r.denReduced.eval (Γ t) ≠ 0 := by
      intro t h0
      have hval : f ((Γ t : ℂ̂)) = ∞ := by
        rw [hr, hreadIf (Γ t), if_pos h0]
      exact hinf (j + 1) (hval ▸ hnext t)
    -- the image points read finitely as the rational quotient
    have hread : ∀ t : unitInterval,
        f ((Γ t : ℂ̂)) = ((r.numReduced.eval (Γ t) / r.denReduced.eval (Γ t) : ℂ) : ℂ̂) := by
      intro t
      rw [hr, hreadIf (Γ t), if_neg (hDΓ t)]
    -- the pushed curve
    have hcont : Continuous fun t : unitInterval =>
        r.numReduced.eval (Γ t) / r.denReduced.eval (Γ t) :=
      (r.numReduced.continuous.comp Γ.continuous).div
        (r.denReduced.continuous.comp Γ.continuous) hDΓ
    set Γ' : C(unitInterval, ℂ) := ⟨_, hcont⟩
    have hΓ'val : ∀ t : unitInterval, Γ' t = chartFiniteMap (f ((Γ t : ℂ̂))) := by
      intro t
      rw [hread t]
      rfl
    have hΓ'mem : ∀ t : unitInterval, ((Γ' t : ℂ̂)) ∈ fcOrbit f U (j + 1) := by
      intro t
      have h := hnext t
      rw [hread t] at h
      exact h
    exact ⟨Γ', hΓ'val, hΓ'mem⟩
  -- Iterate the one-step transport, carrying orbit membership along.
  have hpush : ∀ m : ℕ, ∃ Γ : C(unitInterval, ℂ),
      (∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂)))) ∧
      (∀ t : unitInterval, ((Γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + m)) ∧
      (∀ t : unitInterval, f^[m] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + m)) := by
    intro m
    induction m with
    | zero =>
        refine ⟨γ, ?_, ?_, ?_⟩
        · intro t; simp [chartFiniteMap]
        · intro t; exact hγmem t
        · intro t; simpa using hγmem t
    | succ m ih =>
        obtain ⟨Γm, hval, hmem, hsph⟩ := ih
        obtain ⟨Γ', hΓ'val, hΓ'mem⟩ := hstep Γm (N₀ + m) hmem
        have hsph' : ∀ t : unitInterval,
            f^[m + 1] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + (m + 1)) := by
          intro t
          have h1 : f^[m + 1] ((γ t : ℂ̂)) = f (f^[m] ((γ t : ℂ̂))) :=
            Function.iterate_succ_apply' f m _
          change f^[m + 1] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + m + 1)
          rw [h1, ← fcOrbit_image_eq hf hd1 hU (N₀ + m)]
          exact ⟨_, hsph t, rfl⟩
        have hcoe : ∀ t : unitInterval,
            ((Γm t : ℂ̂)) = f^[m] ((γ t : ℂ̂)) := by
          intro t
          have hne : f^[m] ((γ t : ℂ̂)) ≠ ∞ := fun h => hinf _ (h ▸ hsph t)
          obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hne
          rw [hval t, ← hw]
          rfl
        refine ⟨Γ', ?_, ?_, hsph'⟩
        · intro t
          rw [hΓ'val t, hcoe t, ← Function.iterate_succ_apply' f m]
        · intro t
          change ((Γ' t : ℂ̂)) ∈ fcOrbit f U (N₀ + m + 1)
          exact hΓ'mem t
  obtain ⟨Γ, hΓval, -, -⟩ := hpush m
  exact ⟨Γ, hΓval⟩

/-- A chart-level null homotopy of a closed curve within a plane set: a
continuous square of loops based at the curve's initial point, starting at
the curve, ending at the constant loop, with image inside the set. -/
def IsChartNullHomotopyIn (γ : C(unitInterval, ℂ)) (T : Set ℂ) : Prop :=
  ∃ H : C(unitInterval × unitInterval, ℂ),
    (∀ s : unitInterval, H (0, s) = γ s) ∧
    (∀ s : unitInterval, H (1, s) = γ 0) ∧
    (∀ t : unitInterval, H (t, 0) = γ 0 ∧ H (t, 1) = γ 0) ∧
    (∀ p : unitInterval × unitInterval, H p ∈ T)

/-- **Null homotopies descend through a component covering step.** If the
forward reading of a chart loop in the next orbit component is chart-null-
homotopic within that component's finite part, so is the loop within its
own component's finite part: the step is a covering map of subtypes, the
homotopy square is simply connected so it lifts, and the lifted square has
constant boundary tracks by uniqueness of path lifts. -/
theorem isChartNullHomotopyIn_of_step {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n) (hinf' : ∞ ∉ fcOrbit f U (n + 1))
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {γ Γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U n)
    (hΓ : ∀ t : unitInterval, Γ t = chartFiniteMap (f ((γ t : ℂ̂))))
    (hH : IsChartNullHomotopyIn Γ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (n + 1)}) :
    IsChartNullHomotopyIn γ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U n} := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd1 hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have himg : f '' S = T := fcOrbit_image_eq hf hd1 hU n
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
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
      e ∈ φ.source ∧ ⇑φ = F := by
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
      (fun w _ => hFfib w) (fun e _ => (hFloc e).imp fun φ h => ⟨h.1, h.2.symm⟩)
  have hcov : IsCoveringMap F := isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  -- ## Stage 4: homotopy data and the base loop, packaged on the subtypes.
  obtain ⟨H, hHs0, hHs1, hHtr, hHmem⟩ :
      ∃ H : C(unitInterval × unitInterval, ℂ),
        (∀ s : unitInterval, H (0, s) = Γ s) ∧
        (∀ s : unitInterval, H (1, s) = Γ 0) ∧
        (∀ t : unitInterval, H (t, 0) = Γ 0 ∧ H (t, 1) = Γ 0) ∧
        (∀ p : unitInterval × unitInterval, H p ∈ {w : ℂ | ((w : ℂ̂)) ∈ T}) := hH
  obtain ⟨Hs, hHsdef⟩ : ∃ Hs : C(unitInterval × unitInterval, ↥T),
      Hs = ⟨fun p => ⟨((H p : ℂ̂)), hHmem p⟩,
        Continuous.subtype_mk (OnePoint.continuous_coe.comp H.continuous) _⟩ := ⟨_, rfl⟩
  have hHsval : ∀ p : unitInterval × unitInterval, ((Hs p : ℂ̂)) = ((H p : ℂ̂)) := by
    intro p
    rw [hHsdef]
    rfl
  obtain ⟨γs, hγsdef⟩ : ∃ γs : C(unitInterval, ↥S),
      γs = ⟨fun t => ⟨((γ t : ℂ̂)), hγmem t⟩,
        Continuous.subtype_mk (OnePoint.continuous_coe.comp γ.continuous) _⟩ := ⟨_, rfl⟩
  have hγsval : ∀ t : unitInterval, ((γs t : ℂ̂)) = ((γ t : ℂ̂)) := by
    intro t
    rw [hγsdef]
    rfl
  -- chart readings of points of the two components coerce back to themselves
  have hScoe : ∀ w : ℂ̂, w ∈ S → ((chartFiniteMap w : ℂ) : ℂ̂) = w := by
    intro w hw
    have hne : w ≠ ∞ := fun h => hinf (h ▸ hw)
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hne
    rfl
  have hTcoe : ∀ w : ℂ̂, w ∈ T → ((chartFiniteMap w : ℂ) : ℂ̂) = w := by
    intro w hw
    have hne : w ≠ ∞ := fun h => hinf' (h ▸ hw)
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hne
    rfl
  -- the forward values of the base loop land in the target component
  have hnext : ∀ t : unitInterval, f ((γ t : ℂ̂)) ∈ T := by
    intro t
    rw [← himg]
    exact ⟨_, hγmem t, rfl⟩
  have hΓsph : ∀ t : unitInterval, ((Γ t : ℂ̂)) = f ((γ t : ℂ̂)) := by
    intro t
    rw [hΓ t]
    exact hTcoe _ (hnext t)
  -- the subtype homotopy starts over the packaged image of the base loop
  have hcompat : ∀ s : unitInterval, Hs (0, s) = F (γs s) := by
    intro s
    apply Subtype.ext
    rw [hHsval (0, s), hFval, hγsval s, hHs0 s, hΓsph s]
  -- ## Stage 5: lift the homotopy square and pin its boundary tracks.
  obtain ⟨Ht, hHtdef⟩ : ∃ Ht : C(unitInterval × unitInterval, ↥S),
      Ht = hcov.liftHomotopy Hs γs hcompat := ⟨_, rfl⟩
  have hlifts : ∀ p : unitInterval × unitInterval, F (Ht p) = Hs p := by
    intro p
    rw [hHtdef]
    exact congrFun (hcov.liftHomotopy_lifts Hs γs hcompat) p
  have hzero : ∀ s : unitInterval, Ht (0, s) = γs s := by
    intro s
    rw [hHtdef]
    exact hcov.liftHomotopy_zero Hs γs hcompat s
  have hγscl : γs 1 = γs 0 := by
    apply Subtype.ext
    rw [hγsval 1, hγsval 0, hγcl]
  -- the two vertical tracks lift the constant loop at the base value,
  -- start at the lifted basepoint, hence are constant by unique lifting
  have hside0 : ∀ t : unitInterval, Ht (t, 0) = γs 0 := by
    have hkey : (fun t : unitInterval => Ht (t, 0)) = fun _ : unitInterval => γs 0 := by
      refine hcov.eq_of_comp_eq ?_ continuous_const ?_ 0 (hzero 0)
      · exact Ht.continuous.comp (continuous_id.prodMk continuous_const)
      · funext t
        change F (Ht (t, 0)) = F (γs 0)
        rw [hlifts (t, 0)]
        apply Subtype.ext
        rw [hHsval (t, 0), hFval, hγsval 0, (hHtr t).1, hΓsph 0]
    intro t
    exact congrFun hkey t
  have hside1 : ∀ t : unitInterval, Ht (t, 1) = γs 0 := by
    have hkey : (fun t : unitInterval => Ht (t, 1)) = fun _ : unitInterval => γs 0 := by
      refine hcov.eq_of_comp_eq ?_ continuous_const ?_ 0 ((hzero 1).trans hγscl)
      · exact Ht.continuous.comp (continuous_id.prodMk continuous_const)
      · funext t
        change F (Ht (t, 1)) = F (γs 0)
        rw [hlifts (t, 1)]
        apply Subtype.ext
        rw [hHsval (t, 1), hFval, hγsval 0, (hHtr t).2, hΓsph 0]
    intro t
    exact congrFun hkey t
  -- the top edge lifts the constant loop and starts at the pinned corner
  have htop : ∀ s : unitInterval, Ht (1, s) = γs 0 := by
    have hkey : (fun s : unitInterval => Ht (1, s)) = fun _ : unitInterval => γs 0 := by
      refine hcov.eq_of_comp_eq ?_ continuous_const ?_ 0 (hside0 1)
      · exact Ht.continuous.comp (continuous_const.prodMk continuous_id)
      · funext s
        change F (Ht (1, s)) = F (γs 0)
        rw [hlifts (1, s)]
        apply Subtype.ext
        rw [hHsval (1, s), hFval, hγsval 0, hHs1 s, hΓsph 0]
    intro s
    exact congrFun hkey s
  -- ## Stage 6: read the lifted square back through the finite chart.
  have hchart : ∀ w : ℂ̂, w ≠ ∞ → ContinuousAt chartFiniteMap w := by
    intro w hw
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hw
    rw [OnePoint.continuousAt_coe]
    exact continuousAt_id
  have hHdcont : Continuous fun p : unitInterval × unitInterval =>
      chartFiniteMap ((Ht p : ℂ̂)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have h1 : ContinuousAt (fun q : unitInterval × unitInterval => ((Ht q : ℂ̂))) p :=
      (continuous_subtype_val.comp Ht.continuous).continuousAt
    have h2 : ((Ht p : ℂ̂)) ≠ ∞ := fun h => hinf (h ▸ (Ht p).2)
    change ContinuousAt (chartFiniteMap ∘ fun q : unitInterval × unitInterval => ((Ht q : ℂ̂))) p
    exact ContinuousAt.comp (x := p)
      (f := fun q : unitInterval × unitInterval => ((Ht q : ℂ̂)))
      (g := chartFiniteMap) (hchart _ h2) h1
  change ∃ Hd : C(unitInterval × unitInterval, ℂ),
      (∀ s : unitInterval, Hd (0, s) = γ s) ∧
      (∀ s : unitInterval, Hd (1, s) = γ 0) ∧
      (∀ t : unitInterval, Hd (t, 0) = γ 0 ∧ Hd (t, 1) = γ 0) ∧
      (∀ p : unitInterval × unitInterval, Hd p ∈ {w : ℂ | ((w : ℂ̂)) ∈ S})
  refine ⟨⟨fun p => chartFiniteMap ((Ht p : ℂ̂)), hHdcont⟩, ?_, ?_, ?_, ?_⟩
  · intro s
    change chartFiniteMap ((Ht (0, s) : ℂ̂)) = γ s
    rw [hzero s, hγsval s]
    exact cf _
  · intro s
    change chartFiniteMap ((Ht (1, s) : ℂ̂)) = γ 0
    rw [htop s, hγsval 0]
    exact cf _
  · intro t
    constructor
    · change chartFiniteMap ((Ht (t, 0) : ℂ̂)) = γ 0
      rw [hside0 t, hγsval 0]
      exact cf _
    · change chartFiniteMap ((Ht (t, 1) : ℂ̂)) = γ 0
      rw [hside1 t, hγsval 0]
      exact cf _
  · intro p
    change (((chartFiniteMap ((Ht p : ℂ̂))) : ℂ̂)) ∈ S
    rw [hScoe _ (Ht p).2]
    exact (Ht p).2

end NoWanderingDomains
