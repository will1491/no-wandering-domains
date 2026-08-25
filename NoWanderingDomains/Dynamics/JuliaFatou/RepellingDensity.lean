/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.NormalFamilies.Zalcman
import NoWanderingDomains.Dynamics.JuliaFatou.PeriodicDensity

/-!
# Repelling periodic points are dense in the Julia set

The Fatou–Julia density theorem `juliaSet_eq_closure_repelling`, by the
rescaling argument of Zalcman and Schwick. At a finite Julia point `z₀`
outside a countable bad set (forward critical orbits, the forward orbit of
`∞`), the iterate family is non-normal, so Zalcman's lemma produces
rescalings converging to a nonconstant sphere-holomorphic `g` on `ℂ`.
By the Picard-type theorem `g` omits at most two values, and since the
Julia set is uncountable while the critical set of `g` is countable, the
open set of regular values of `g` meets the Julia set; the backward orbit
of `z₀` is dense in the Julia set, so `g` attains a backward orbit point
`y` of `z₀` regularly. The fixed-point equation
`f^[m] (F k (z k + ρ k ζ)) = z k + ρ k ζ` then has solutions near the
regular preimage by Hurwitz, producing periodic points `p k → z₀` whose
multipliers blow up like `1/ρ k` — repelling cycles in every neighborhood
of `z₀`. A Baire sweep over the countable bad set upgrades this to all of
the Julia set.
-/

open OnePoint Polynomial Filter Topology Metric Function

namespace NoWanderingDomains

/-- **Picard's theorem for sphere-holomorphic maps on `ℂ`**: a map
omitting three distinct values is constant. The affine rescalings
`ζ ↦ g (z₀ + t ζ)` form a family omitting the triple, normal by
Montel–Carathéodory; equicontinuity at `0` over all scales `t` forces
constancy. -/
theorem eq_const_of_sphereHolomorphicOn_univ_omits {g : ℂ → ℂ̂}
    (hg : SphereHolomorphicOn g Set.univ) {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (homit : ∀ ζ : ℂ, g ζ ≠ a ∧ g ζ ≠ b ∧ g ζ ≠ c) :
    ∃ v : ℂ̂, g = Function.const ℂ v := by
  -- The family of all affine rescalings of `g`.
  have hol : ∀ G ∈ {G : ℂ → ℂ̂ | ∃ w t : ℂ, G = fun ζ => g (w + t * ζ)},
      SphereHolomorphicOn G Set.univ := by
    rintro G ⟨w, t, rfl⟩
    have h := hg.comp_affine w t
    rwa [Set.preimage_univ] at h
  have homit' : ∀ G ∈ {G : ℂ → ℂ̂ | ∃ w t : ℂ, G = fun ζ => g (w + t * ζ)},
      ∀ z ∈ Set.univ, G z ≠ a ∧ G z ≠ b ∧ G z ≠ c := by
    rintro G ⟨w, t, rfl⟩ z _
    exact homit _
  -- Montel–Carathéodory: the rescaling family is normal, hence equicontinuous at `0`.
  have hN : IsNormal {G : ℂ → ℂ̂ | ∃ w t : ℂ, G = fun ζ => g (w + t * ζ)} Set.univ :=
    montel_caratheodory_sphere hab hac hbc hol homit'
  have hNat : IsNormalAt {G : ℂ → ℂ̂ | ∃ w t : ℂ, G = fun ζ => g (w + t * ζ)} (0 : ℂ) :=
    ⟨Set.univ, Filter.univ_mem, hN⟩
  have hequi := hNat.equicontinuousAt fun G hG =>
    continuousOn_univ.mp (hol G hG).continuousOn
  -- Equicontinuity over all scales forces all values of `g` to coincide.
  have key : ∀ x y : ℂ, g y = g x := by
    intro x y
    have hdist : ∀ ε : ℝ, 0 < ε → dist (g y) (g x) < ε := by
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hequi ε hε
      have hζ₀ne : ((δ / 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
      -- The rescaling reaching `y` from `x` at parameter `ζ₀ = δ/2`.
      have hGmem : (fun ζ => g (x + (y - x) / ((δ / 2 : ℝ) : ℂ) * ζ))
          ∈ {G : ℂ → ℂ̂ | ∃ w t : ℂ, G = fun ζ => g (w + t * ζ)} :=
        ⟨x, (y - x) / ((δ / 2 : ℝ) : ℂ), rfl⟩
      have harg : x + (y - x) / ((δ / 2 : ℝ) : ℂ) * ((δ / 2 : ℝ) : ℂ) = y := by
        rw [div_mul_cancel₀ _ hζ₀ne]
        ring
      have hd0 : dist (((δ / 2 : ℝ) : ℂ)) (0 : ℂ) < δ := by
        rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      have h := hδ' _ hGmem (((δ / 2 : ℝ) : ℂ)) hd0
      simp only [mul_zero, add_zero] at h
      rwa [harg] at h
    have hle : dist (g y) (g x) ≤ 0 := by
      by_contra h
      push Not at h
      exact lt_irrefl _ (hdist _ h)
    exact dist_le_zero.mp hle
  exact ⟨g 0, funext fun y => (key 0 y).trans (Function.const_apply ..).symm⟩

/-- The critical set of a nonconstant sphere-holomorphic map on `ℂ` is
countable: its chart readings have nonvanishing derivative off a set
without accumulation points. -/
theorem countable_setOf_sphericalDeriv_eq_zero {g : ℂ → ℂ̂}
    (hg : SphereHolomorphicOn g Set.univ)
    (hnc : ¬ ∃ v : ℂ̂, g = Function.const ℂ v) :
    {ζ : ℂ | sphericalDeriv g ζ = 0}.Countable := by
  classical
  -- The inversion is an involution of the sphere.
  have hJJ : inversionGL * inversionGL = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [inversionGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hgc : Continuous g := continuousOn_univ.mp hg.continuousOn
  -- Chart package: near any point, `g` is a Möbius image of an analytic chart
  -- reading `u`, and the spherical derivative obeys the chart formula.
  have main : ∀ ζ₀ : ℂ, ∃ (M : GL (Fin 2) ℂ) (u : ℂ → ℂ) (V : Set ℂ),
      IsOpen V ∧ ζ₀ ∈ V ∧ AnalyticOnNhd ℂ u V ∧
      (∀ ζ ∈ V, g ζ = M • ((u ζ : ℂ) : ℂ̂)) ∧
      ∀ ζ ∈ V, sphericalDeriv g ζ = 2 * ‖deriv u ζ‖ / (1 + ‖u ζ‖ ^ 2) := by
    intro ζ₀
    -- Choose the chart-normalizing Möbius element `N` (identity or inversion).
    obtain ⟨N, hNinvol, hNfin, hNd⟩ : ∃ N : GL (Fin 2) ℂ, (∀ p : ℂ̂, N • N • p = p) ∧
        N • g ζ₀ ≠ ∞ ∧
        ∀ ζ : ℂ, sphericalDeriv (fun w => N • g w) ζ = sphericalDeriv g ζ := by
      by_cases hζ : g ζ₀ = ∞
      · refine ⟨inversionGL, fun p => by rw [← SemigroupAction.mul_smul, hJJ, one_smul], ?_,
          fun ζ => sphericalDeriv_inversionGL_smul g ζ⟩
        rw [hζ, inversionGL_smul_infty]
        exact OnePoint.coe_ne_infty 0
      · exact ⟨1, fun p => by rw [one_smul, one_smul], by rwa [one_smul],
          fun ζ => by simp only [one_smul]⟩
    have hGn : SphereHolomorphicOn (fun w => N • g w) Set.univ := hg.gl_smul N
    have hGnc : Continuous (fun w => N • g w) :=
      continuousOn_univ.mp hGn.continuousOn
    set U₀ : Set ℂ := {x : ℂ | N • g x ≠ ∞} with hU₀_def
    have hU₀_open : IsOpen U₀ := by
      rw [hU₀_def]
      exact (OnePoint.isClosed_infty.isOpen_compl).preimage hGnc
    have hζU₀ : ζ₀ ∈ U₀ := hNfin
    -- Restrict sphere-holomorphy to the finite locus `U₀`.
    have hGn₀ : SphereHolomorphicOn (fun w => N • g w) U₀ := by
      intro z hz
      obtain ⟨V, hVo, hzV, -, hcase⟩ := hGn z (Set.mem_univ z)
      refine ⟨V ∩ U₀, hVo.inter hU₀_open, ⟨hzV, hz⟩, Set.inter_subset_right, ?_⟩
      rcases hcase with ⟨hne, hd⟩ | ⟨hne, hd⟩
      · exact Or.inl ⟨fun w hw => hne w hw.1, hd.mono Set.inter_subset_left⟩
      · exact Or.inr ⟨fun w hw => hne w hw.1, hd.mono Set.inter_subset_left⟩
    have hu_diff : DifferentiableOn ℂ (fun w => chartFiniteMap (N • g w)) U₀ :=
      hGn₀.differentiableOn_chartFiniteMap fun z hz => hz
    have hread : ∀ x ∈ U₀, N • g x = ((chartFiniteMap (N • g x) : ℂ) : ℂ̂) := by
      intro x hx
      cases hNx : N • g x with
      | infty => exact absurd hNx hx
      | coe t =>
        have ct : chartFiniteMap ((t : ℂ) : ℂ̂) = t := rfl
        rw [ct]
    have hMrep : ∀ ζ ∈ U₀, g ζ = N • ((chartFiniteMap (N • g ζ) : ℂ) : ℂ̂) := by
      intro ζ hζ
      rw [← hread ζ hζ]
      exact (hNinvol (g ζ)).symm
    have hform : ∀ ζ ∈ U₀, sphericalDeriv g ζ =
        2 * ‖deriv (fun w => chartFiniteMap (N • g w)) ζ‖ /
          (1 + ‖chartFiniteMap (N • g ζ)‖ ^ 2) := by
      intro ζ hζ
      rw [← hNd ζ]
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_
        (hu_diff.differentiableAt (hU₀_open.mem_nhds hζ))
      filter_upwards [hU₀_open.mem_nhds hζ] with w hw using hread w hw
    exact ⟨N, fun w => chartFiniteMap (N • g w), U₀, hU₀_open, hζU₀,
      hu_diff.analyticOnNhd hU₀_open, hMrep, hform⟩
  -- Local dichotomy from isolated zeros of the analytic derivative.
  have dich : ∀ ζ₀ : ℂ, (∀ᶠ ζ in 𝓝[≠] ζ₀, sphericalDeriv g ζ ≠ 0) ∨
      ∀ᶠ ζ in 𝓝 ζ₀, sphericalDeriv g ζ = 0 := by
    intro ζ₀
    obtain ⟨M, u, V, hVo, hζV, hu_an, -, hform⟩ := main ζ₀
    rcases (hu_an.deriv ζ₀ hζV).eventually_eq_zero_or_eventually_ne_zero with h | h
    · right
      filter_upwards [h, hVo.mem_nhds hζV] with ζ h0 hζ
      rw [hform ζ hζ, h0, norm_zero, mul_zero, zero_div]
    · left
      filter_upwards [h, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hζV)] with ζ hne hζ
      rw [hform ζ hζ]
      have h1 : (0 : ℝ) < 1 + ‖u ζ‖ ^ 2 := by positivity
      exact div_ne_zero (mul_ne_zero two_ne_zero (norm_ne_zero_iff.mpr hne)) (ne_of_gt h1)
  -- The set of points near which the spherical derivative vanishes identically.
  set C : Set ℂ := {ζ₀ : ℂ | ∀ᶠ ζ in 𝓝 ζ₀, sphericalDeriv g ζ = 0} with hC_def
  have hC_open : IsOpen C := by
    rw [hC_def]
    exact isOpen_setOfPred_eventually_nhds
  have hC_closed : IsClosed C := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro ζ₀ hζ₀
    have hζ₀' : ¬ ∀ᶠ ζ in 𝓝 ζ₀, sphericalDeriv g ζ = 0 := hζ₀
    rcases dich ζ₀ with h1 | h2
    · obtain ⟨T, hT, hT_open, hζT⟩ :=
        _root_.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h1)
      refine ⟨T, ?_, hT_open, hζT⟩
      intro ζ hζ
      simp only [Set.mem_compl_iff]
      intro hζC
      have hev : ∀ᶠ ζ' in 𝓝 ζ, sphericalDeriv g ζ' = 0 := hζC
      by_cases hee : ζ = ζ₀
      · exact hζ₀' (hee ▸ hev)
      · exact hT ζ hζ hee hev.self_of_nhds
    · exact absurd h2 hζ₀'
  rcases isClopen_iff.mp ⟨hC_closed, hC_open⟩ with hCe | hCu
  · -- `C = ∅`: zeros of the spherical derivative are isolated, hence countable.
    have hiso : ∀ ζ₀ : ℂ, ∀ᶠ ζ in 𝓝[≠] ζ₀, sphericalDeriv g ζ ≠ 0 := by
      intro ζ₀
      rcases dich ζ₀ with h | h
      · exact h
      · exfalso
        have hζC : ζ₀ ∈ C := h
        rw [hCe] at hζC
        exact hζC
    have hsub : {ζ : ℂ | sphericalDeriv g ζ = 0} ⊆
        ⋃ n : ℕ, ({ζ : ℂ | sphericalDeriv g ζ = 0} ∩ Metric.closedBall 0 n) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      exact Set.mem_iUnion.mpr ⟨n, hz, mem_closedBall_zero_iff.mpr hn⟩
    refine Set.Countable.mono hsub
      (Set.countable_iUnion fun n => Set.Finite.countable ?_)
    by_contra hinf
    obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
      (isCompact_closedBall (0 : ℂ) n) Set.inter_subset_right
    have hfreq : ∃ᶠ ζ in 𝓝[≠] x,
        ζ ∈ {ζ : ℂ | sphericalDeriv g ζ = 0} ∩ Metric.closedBall 0 n :=
      accPt_iff_frequently_nhdsNE.mp hx
    obtain ⟨ζ, hζ1, hζ2⟩ := (hfreq.and_eventually (hiso x)).exists
    exact hζ2 hζ1.1
  · -- `C = univ`: the chart readings are locally constant, so `g` is constant.
    exfalso
    have hall : ∀ ζ : ℂ, sphericalDeriv g ζ = 0 := by
      intro ζ
      have hζC : ζ ∈ C := by
        rw [hCu]
        exact Set.mem_univ ζ
      have hev : ∀ᶠ ζ' in 𝓝 ζ, sphericalDeriv g ζ' = 0 := hζC
      exact hev.self_of_nhds
    have hloc : ∀ ζ₀ : ℂ, ∀ᶠ ζ in 𝓝 ζ₀, g ζ = g ζ₀ := by
      intro ζ₀
      obtain ⟨M, u, V, hVo, hζV, hu_an, hgM, hform⟩ := main ζ₀
      have hderiv0 : ∀ ζ ∈ V, deriv u ζ = 0 := by
        intro ζ hζ
        have h0 := hall ζ
        rw [hform ζ hζ] at h0
        rcases div_eq_zero_iff.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact norm_eq_zero.mp h
        · exfalso
          have h1 : (0 : ℝ) < 1 + ‖u ζ‖ ^ 2 := by positivity
          exact (ne_of_gt h1) h
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo ζ₀ hζV
      have hu_db : DifferentiableOn ℂ u (Metric.ball ζ₀ r) := fun x hx =>
        ((hu_an x (hball hx)).differentiableAt).differentiableWithinAt
      have hconst : ∀ ζ ∈ Metric.ball ζ₀ r, u ζ = u ζ₀ := fun ζ hζ =>
        Metric.isOpen_ball.is_const_of_deriv_eq_zero
          (convex_ball ζ₀ r).isPreconnected hu_db
          (fun x hx => hderiv0 x (hball hx)) hζ (Metric.mem_ball_self hr)
      filter_upwards [Metric.ball_mem_nhds ζ₀ hr] with ζ hζ
      rw [hgM ζ (hball hζ), hconst ζ hζ, ← hgM ζ₀ hζV]
    -- The level set of `g 0` is clopen and nonempty, hence everything.
    have hS_open : IsOpen {ζ : ℂ | g ζ = g 0} := by
      rw [isOpen_iff_mem_nhds]
      intro ζ hζ
      have hζ' : g ζ = g 0 := hζ
      filter_upwards [hloc ζ] with ζ' hζ'' using hζ''.trans hζ'
    have hS_closed : IsClosed {ζ : ℂ | g ζ = g 0} := isClosed_eq hgc continuous_const
    rcases isClopen_iff.mp ⟨hS_closed, hS_open⟩ with hSe | hSu
    · have h0 : (0 : ℂ) ∈ {ζ : ℂ | g ζ = g 0} := rfl
      rw [hSe] at h0
      exact h0
    · refine hnc ⟨g 0, funext fun ζ => ?_⟩
      have hζS : ζ ∈ {ζ : ℂ | g ζ = g 0} := by
        rw [hSu]
        exact Set.mem_univ ζ
      exact hζS

/-- The image of the regular set of a sphere-holomorphic map on `ℂ` is
open: at a regular point the chart reading is locally invertible. -/
theorem isOpen_image_setOf_sphericalDeriv_ne_zero {g : ℂ → ℂ̂}
    (hg : SphereHolomorphicOn g Set.univ) :
    IsOpen (g '' {ζ : ℂ | sphericalDeriv g ζ ≠ 0}) := by
  classical
  -- Local openness of the image at a regular point with finite value.
  have key : ∀ G : ℂ → ℂ̂, SphereHolomorphicOn G Set.univ → ∀ ζ₀ : ℂ,
      sphericalDeriv G ζ₀ ≠ 0 → G ζ₀ ≠ ∞ →
      ∃ W : Set ℂ̂, IsOpen W ∧ G ζ₀ ∈ W ∧
        W ⊆ G '' {ζ : ℂ | sphericalDeriv G ζ ≠ 0} := by
    intro G hG ζ₀ hreg hfin
    have hGc : Continuous G := continuousOn_univ.mp hG.continuousOn
    set U₀ : Set ℂ := {x : ℂ | G x ≠ ∞} with hU₀_def
    have hU₀_open : IsOpen U₀ := by
      rw [hU₀_def]
      exact (OnePoint.isClosed_infty.isOpen_compl).preimage hGc
    have hζ₀U₀ : ζ₀ ∈ U₀ := hfin
    -- Restrict sphere-holomorphy to the finite locus `U₀`.
    have hG₀ : SphereHolomorphicOn G U₀ := by
      intro z hz
      obtain ⟨V, hVo, hzV, -, hcase⟩ := hG z (Set.mem_univ z)
      refine ⟨V ∩ U₀, hVo.inter hU₀_open, ⟨hzV, hz⟩, Set.inter_subset_right, ?_⟩
      rcases hcase with ⟨hne, hd⟩ | ⟨hne, hd⟩
      · exact Or.inl ⟨fun w hw => hne w hw.1, hd.mono Set.inter_subset_left⟩
      · exact Or.inr ⟨fun w hw => hne w hw.1, hd.mono Set.inter_subset_left⟩
    set u : ℂ → ℂ := fun w => chartFiniteMap (G w) with hu_def
    have hu_diff : DifferentiableOn ℂ u U₀ :=
      hG₀.differentiableOn_chartFiniteMap fun z hz => hz
    have hread : ∀ x ∈ U₀, G x = ((u x : ℂ) : ℂ̂) := by
      intro x hx
      cases hGx : G x with
      | infty => exact absurd hGx hx
      | coe t =>
        have ct : u x = t := by
          rw [hu_def]
          simp only [hGx]
          rfl
        rw [ct]
    have hu_an : AnalyticOnNhd ℂ u U₀ := hu_diff.analyticOnNhd hU₀_open
    -- Chart formula for the spherical derivative on `U₀`.
    have hform : ∀ ζ ∈ U₀, sphericalDeriv G ζ = 2 * ‖deriv u ζ‖ / (1 + ‖u ζ‖ ^ 2) := by
      intro ζ hζ
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_
        (hu_diff.differentiableAt (hU₀_open.mem_nhds hζ))
      filter_upwards [hU₀_open.mem_nhds hζ] with w hw using hread w hw
    have hd0 : deriv u ζ₀ ≠ 0 := by
      intro h0
      apply hreg
      rw [hform ζ₀ hζ₀U₀, h0, norm_zero, mul_zero, zero_div]
    -- The open locus of nonvanishing derivative consists of regular points.
    set U₁ : Set ℂ := U₀ ∩ deriv u ⁻¹' {(0 : ℂ)}ᶜ with hU₁_def
    have hU₁_open : IsOpen U₁ :=
      (hu_an.deriv.continuousOn).isOpen_inter_preimage hU₀_open isOpen_compl_singleton
    have hζ₀U₁ : ζ₀ ∈ U₁ := ⟨hζ₀U₀, hd0⟩
    have hU₁_reg : ∀ ζ ∈ U₁, sphericalDeriv G ζ ≠ 0 := by
      intro ζ hζ
      have hne : deriv u ζ ≠ 0 := hζ.2
      rw [hform ζ hζ.1]
      have h1 : (0 : ℝ) < 1 + ‖u ζ‖ ^ 2 := by positivity
      exact div_ne_zero (mul_ne_zero two_ne_zero (norm_ne_zero_iff.mpr hne)) (ne_of_gt h1)
    -- Local right inverse from the inverse function theorem.
    have hstrict : HasStrictDerivAt u (deriv u ζ₀) ζ₀ := (hu_an ζ₀ hζ₀U₀).hasStrictDerivAt
    set ginv : ℂ → ℂ := hstrict.localInverse u (deriv u ζ₀) ζ₀ hd0 with hginv_def
    have hgζ : ginv (u ζ₀) = ζ₀ := (hstrict.eventually_left_inverse hd0).self_of_nhds
    have hg_cont : ContinuousAt ginv (u ζ₀) :=
      (hstrict.to_localInverse hd0).hasDerivAt.differentiableAt.continuousAt
    have hmem₁ : ginv (u ζ₀) ∈ U₁ := by
      rw [hgζ]
      exact hζ₀U₁
    have hev : ∀ᶠ y in 𝓝 (u ζ₀), u (ginv y) = y ∧ ginv y ∈ U₁ :=
      (hstrict.eventually_right_inverse hd0).and
        (hg_cont.eventually_mem (hU₁_open.mem_nhds hmem₁))
    obtain ⟨T, hT, hT_open, hζT⟩ := _root_.eventually_nhds_iff.mp hev
    refine ⟨((↑) : ℂ → ℂ̂) '' T, OnePoint.isOpenEmbedding_coe.isOpenMap T hT_open,
      ⟨u ζ₀, hζT, (hread ζ₀ hζ₀U₀).symm⟩, ?_⟩
    rintro p ⟨y, hyT, rfl⟩
    obtain ⟨h1, h2⟩ := hT y hyT
    refine ⟨ginv y, hU₁_reg _ h2, ?_⟩
    rw [hread _ h2.1, h1]
  -- Main proof: split on whether the regular value is finite or infinite.
  rw [isOpen_iff_forall_mem_open]
  rintro p ⟨ζ₀, hζ₀, rfl⟩
  by_cases hfin : g ζ₀ = ∞
  · -- Infinite value: pass to the inverted map and pull the open set back.
    have hJJ : inversionGL * inversionGL = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [inversionGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.mul_apply, Fin.sum_univ_two]
    have hinvol : ∀ p : ℂ̂, inversionGL • inversionGL • p = p := fun p => by
      rw [← SemigroupAction.mul_smul, hJJ, one_smul]
    have hh : SphereHolomorphicOn (fun w => inversionGL • g w) Set.univ :=
      hg.gl_smul inversionGL
    have hhreg : sphericalDeriv (fun w => inversionGL • g w) ζ₀ ≠ 0 := by
      rw [sphericalDeriv_inversionGL_smul]
      exact hζ₀
    have hhfin : (fun w => inversionGL • g w) ζ₀ ≠ ∞ := by
      change inversionGL • g ζ₀ ≠ ∞
      rw [hfin, inversionGL_smul_infty]
      exact OnePoint.coe_ne_infty 0
    obtain ⟨W', hW'o, hW'mem, hW'sub⟩ := key _ hh ζ₀ hhreg hhfin
    refine ⟨(fun p : ℂ̂ => inversionGL • p) ⁻¹' W', ?_,
      hW'o.preimage (continuous_gl_smul inversionGL), hW'mem⟩
    intro q hq
    obtain ⟨ζ, hζreg, hζeq⟩ := hW'sub hq
    have hζeq' : inversionGL • g ζ = inversionGL • q := hζeq
    refine ⟨ζ, ?_, ?_⟩
    · have hr : sphericalDeriv (fun w => inversionGL • g w) ζ ≠ 0 := hζreg
      rwa [sphericalDeriv_inversionGL_smul] at hr
    · calc g ζ = inversionGL • inversionGL • g ζ := (hinvol (g ζ)).symm
        _ = inversionGL • inversionGL • q := by rw [hζeq']
        _ = q := hinvol q
  · -- Finite value: the local openness applies directly.
    obtain ⟨W, hWo, hWmem, hWsub⟩ := key g hg ζ₀ hζ₀ hfin
    exact ⟨W, hWsub, hWo, hWmem⟩

/-- **Backward orbits of Julia points are dense in the Julia set**: any
open set meeting the Julia set is hit by some iterated image, because the
complement of the union of forward images is finite and backward
invariant, hence contained in the Fatou set. -/
theorem juliaSet_subset_closure_backwardOrbit {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f) {z₀ : ℂ̂}
    (hz₀ : z₀ ∈ JuliaSet f) :
    JuliaSet f ⊆ closure (backwardOrbit f z₀) := by
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  intro w hw
  rw [_root_.mem_closure_iff]
  intro V hVo hwV
  -- KEY CLAIM: `z₀` lies in the union of the forward images of `V`.
  have key : z₀ ∈ ⋃ n : ℕ, f^[n] '' V := by
    by_contra hz₀A
    -- No three distinct points avoid the union (Montel blow-up at `w`).
    have hsmall : ∀ a b c : ℂ̂, a ∉ (⋃ n : ℕ, f^[n] '' V) →
        b ∉ (⋃ n : ℕ, f^[n] '' V) → c ∉ (⋃ n : ℕ, f^[n] '' V) →
        a ≠ b → a ≠ c → b ≠ c → False := by
      intro a b c ha hb hc hab hac hbc
      obtain ⟨n, z, hzV, hzm⟩ :=
        exists_iterate_mem_of_mem_juliaSet hf hd1 hw hVo hwV hab hac hbc
      have hmem : f^[n] z ∈ ⋃ m : ℕ, f^[m] '' V :=
        Set.mem_iUnion.mpr ⟨n, z, hzV, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzm
      rcases hzm with h | h | h
      · exact ha (h ▸ hmem)
      · exact hb (h ▸ hmem)
      · exact hc (h ▸ hmem)
    -- Hence the complement of the union has at most two points.
    have hfin : ((⋃ n : ℕ, f^[n] '' V)ᶜ).Finite := by
      by_contra hinf'
      have hinf : ((⋃ n : ℕ, f^[n] '' V)ᶜ).Infinite := hinf'
      obtain ⟨a, ha⟩ := hinf.nonempty
      obtain ⟨b, hb⟩ := (hinf.sdiff (Set.finite_singleton a)).nonempty
      obtain ⟨c, hc⟩ := (hinf.sdiff ((Set.finite_singleton b).insert a)).nonempty
      have hba : b ≠ a := fun h => hb.2 (Set.mem_singleton_iff.mpr h)
      have hca : c ≠ a := fun h => hc.2 (Set.mem_insert_iff.mpr (Or.inl h))
      have hcb : c ≠ b := fun h =>
        hc.2 (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)))
      exact hsmall a b c ha hb.1 hc.1 hba.symm hca.symm hcb.symm
    -- The complement is backward invariant.
    have hpre : f ⁻¹' (⋃ n : ℕ, f^[n] '' V)ᶜ ⊆ (⋃ n : ℕ, f^[n] '' V)ᶜ := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
      intro hxA
      apply hx
      obtain ⟨n, z, hzV, hz⟩ := Set.mem_iUnion.mp hxA
      exact Set.mem_iUnion.mpr
        ⟨n + 1, z, hzV, by rw [Function.iterate_succ_apply', hz]⟩
    -- A finite backward-invariant set lies in the Fatou set; but `z₀` is
    -- a Julia point in the complement — contradiction.
    exact hz₀ (subset_fatouSet_of_finite_preimage_subset hf hd hfin hpre hz₀A)
  -- Extract the preimage point: it is a backward-orbit point inside `V`.
  obtain ⟨n, z, hzV, hz⟩ := Set.mem_iUnion.mp key
  exact ⟨z, hzV, n, hz⟩

/-- **The Julia set is uncountable**: it is a nonempty perfect set in a
complete space. -/
theorem not_countable_juliaSet {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) : ¬ (JuliaSet f).Countable := by
  intro hc
  -- Cantor's diagonal argument: `ℕ → Bool` is uncountable.
  have hUnc : Uncountable (ℕ → Bool) := by
    rw [uncountable_iff_forall_not_surjective]
    intro g hg
    obtain ⟨n, hn⟩ := hg fun k => !(g k k)
    have hcontra := congrFun hn n
    simp at hcontra
  -- The perfect nonempty Julia set admits a continuous injection from `ℕ → Bool`.
  obtain ⟨F, hFr, -, hFinj⟩ :=
    (juliaSet_perfect hf hd).exists_nat_bool_injection (juliaSet_nonempty hf hd)
  have h1 : (Set.range F).Countable := hc.mono hFr
  have h2 := h1.to_subtype
  exact hUnc.not_countable (Countable.of_equiv _ (Equiv.ofInjective F hFinj).symm)

/-- **The Baire sweep**: removing a countable set from the (perfect,
compact, nonempty) Julia set leaves a dense subset of it. -/
theorem juliaSet_subset_closure_diff_countable {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f) {B : Set ℂ̂}
    (hB : B.Countable) :
    JuliaSet f ⊆ closure (JuliaSet f \ B) := by
  intro z hz
  rw [_root_.mem_closure_iff]
  intro V hVopen hzV
  -- Shrink to a closed ball around `z` inside `V`.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen z hzV
  have hrpos : (0 : ℝ) < r / 2 := half_pos hr
  have hsub : closedBall z (r / 2) ⊆ V :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  -- The local piece `D := closure (ball z (r/2) ∩ JuliaSet f)` is perfect and nonempty.
  obtain ⟨hDperf, hDne⟩ :=
    (juliaSet_perfect hf hd).closure_nhds_inter z hz (mem_ball_self hrpos) isOpen_ball
  have hDV : closure (ball z (r / 2) ∩ JuliaSet f) ⊆ V :=
    (closure_minimal (Set.inter_subset_left.trans ball_subset_closedBall)
      isClosed_closedBall).trans hsub
  have hDJ : closure (ball z (r / 2) ∩ JuliaSet f) ⊆ JuliaSet f :=
    closure_minimal Set.inter_subset_right (isClosed_juliaSet f)
  -- Cantor's diagonal argument: `ℕ → Bool` is uncountable.
  have hUnc : Uncountable (ℕ → Bool) := by
    rw [uncountable_iff_forall_not_surjective]
    intro g hg
    obtain ⟨n, hn⟩ := hg fun k => !(g k k)
    have hcontra := congrFun hn n
    simp at hcontra
  -- The perfect nonempty piece `D` is uncountable, so it cannot lie inside `B`.
  obtain ⟨F, hFr, -, hFinj⟩ := hDperf.exists_nat_bool_injection hDne
  have hDnc : ¬ (closure (ball z (r / 2) ∩ JuliaSet f)).Countable := by
    intro hc
    have h1 : (Set.range F).Countable := hc.mono hFr
    have h2 := h1.to_subtype
    exact hUnc.not_countable (Countable.of_equiv _ (Equiv.ofInjective F hFinj).symm)
  have hdiff : (closure (ball z (r / 2) ∩ JuliaSet f) \ B).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hDnc (hB.mono (Set.sdiff_eq_empty.mp he))
  obtain ⟨x, hxD, hxB⟩ := hdiff
  exact ⟨x, hDV hxD, hDJ hxD, hxB⟩

/-- **Hurwitz root tracking**: if holomorphic functions converge locally
uniformly to a limit with a simple zero at `ζ₀`, then eventually every
member of the sequence has a zero within `ε` of `ζ₀`. -/
theorem eventually_exists_root_of_tendstoLocallyUniformlyOn
    {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (Fn n) U)
    (hF : TendstoLocallyUniformlyOn Fn F atTop U) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ U)
    (h0 : F ζ₀ = 0) (h1 : deriv F ζ₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ ζ : ℂ, ‖ζ - ζ₀‖ < ε ∧ Fn n ζ = 0 := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- a small ball around `ζ₀` inside `U` and inside the `ε`-ball
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU ζ₀ hζ₀
  set δ : ℝ := min r ε with hδ_def
  have hδ : 0 < δ := lt_min hr hε
  have hball : ball ζ₀ δ ⊆ U := (ball_subset_ball (min_le_left r ε)).trans hrU
  -- extract a strictly monotone subsequence of nonvanishing, differentiable members
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop (hcon.and_eventually hd)
  -- the subsequence still converges locally uniformly on the small ball
  have hsub : TendstoLocallyUniformlyOn (fun j => Fn (φ j)) F atTop (ball ζ₀ δ) := by
    intro u hu x hx
    obtain ⟨t, ht, h⟩ := hF.mono hball u hu x hx
    exact ⟨t, ht, hφ.tendsto_atTop.eventually h⟩
  -- Hurwitz: the limit vanishes at the center, hence identically on the ball
  have hzero : ∀ z ∈ ball ζ₀ δ, F z = 0 := by
    refine eqOn_zero_of_tendstoLocallyUniformlyOn_of_ne_zero Metric.isOpen_ball
      ((convex_ball ζ₀ δ).isPreconnected) (fun j => ((hφP j).2).mono hball)
      (fun j z hz hz0 => (hφP j).1 ⟨z, ?_, hz0⟩) hsub (mem_ball_self hδ) h0
    rw [mem_ball, dist_eq_norm] at hz
    exact hz.trans_le (min_le_right r ε)
  -- but then `deriv F ζ₀ = 0`, contradicting `h1`
  have hev : F =ᶠ[nhds ζ₀] fun _ => (0 : ℂ) :=
    Filter.eventuallyEq_of_mem (ball_mem_nhds ζ₀ hδ) hzero
  exact h1 (by rw [hev.deriv_eq]; simp)

/-- **Moving-point derivative convergence**: under locally uniform
convergence of holomorphic functions, derivatives evaluated along a
convergent sequence of points converge to the limit derivative. -/
theorem tendsto_deriv_apply_of_tendstoLocallyUniformlyOn
    {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (Fn n) U)
    (hF : TendstoLocallyUniformlyOn Fn F atTop U) {ζn : ℕ → ℂ} {ζ₀ : ℂ}
    (hζ₀ : ζ₀ ∈ U) (hζ : Tendsto ζn atTop (nhds ζ₀)) :
    Tendsto (fun n => deriv (Fn n) (ζn n)) atTop (nhds (deriv F ζ₀)) := by
  -- the derivatives converge locally uniformly on `U`
  have hdF : TendstoLocallyUniformlyOn (deriv ∘ Fn) (deriv F) atTop U := hF.deriv hd hU
  -- `deriv F` is continuous at `ζ₀` since `F` is analytic on the open set `U`
  have hAn : AnalyticOnNhd ℂ F U := (hF.differentiableOn hd hU).analyticOnNhd hU
  have hcont : ContinuousWithinAt (deriv F) U ζ₀ :=
    (hAn.deriv ζ₀ hζ₀).continuousAt.continuousWithinAt
  -- the moving points eventually lie in `U` and converge within `U`
  have hgU : Tendsto ζn atTop (nhdsWithin ζ₀ U) :=
    tendsto_nhdsWithin_iff.mpr ⟨hζ, hζ.eventually (hU.eventually_mem hζ₀)⟩
  exact hdF.tendsto_comp hcont hζ₀ hgU

set_option maxHeartbeats 400000 in
-- the chart-transfer estimates and the Weierstrass assembly are long
/-- **The chart-reading bundle near a finite limit value**: where the
locally uniform limit of sphere-holomorphic maps is finite, there is a
ball on which the limit and eventually all members are honestly read in
the finite chart, with holomorphic readings converging locally
uniformly. -/
theorem exists_ball_chartReading_of_tendstoLocallyUniformlyOn
    {Fn : ℕ → ℂ → ℂ̂} {g : ℂ → ℂ̂} {U : Set ℂ} (hU : IsOpen U)
    (hol : ∀ n, SphereHolomorphicOn (Fn n) U)
    (hg : TendstoLocallyUniformlyOn Fn g atTop U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hfin : g z₀ ≠ ∞) :
    ∃ δ : ℝ, 0 < δ ∧ ball z₀ δ ⊆ U ∧
      (∀ z ∈ ball z₀ δ, g z = ((chartFiniteMap (g z) : ℂ) : ℂ̂)) ∧
      DifferentiableOn ℂ (fun w => chartFiniteMap (g w)) (ball z₀ δ) ∧
      (∀ᶠ n in atTop, (∀ z ∈ ball z₀ δ,
          Fn n z = ((chartFiniteMap (Fn n z) : ℂ) : ℂ̂)) ∧
        DifferentiableOn ℂ (fun w => chartFiniteMap (Fn n w)) (ball z₀ δ)) ∧
      TendstoLocallyUniformlyOn (fun n w => chartFiniteMap (Fn n w))
        (fun w => chartFiniteMap (g w)) atTop (ball z₀ δ) := by
  -- the limit is continuous on `U`
  have hGc : ContinuousOn g U :=
    hg.continuousOn (Frequently.of_forall fun n => (hol n).continuousOn)
  obtain ⟨ε₀, hε₀, hd4⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ dist (g z₀) (∞ : ℂ̂) = 4 * ε₀ :=
    ⟨dist (g z₀) (∞ : ℂ̂) / 4, by linarith [dist_pos.mpr hfin], by ring⟩
  obtain ⟨d, hd, hd'⟩ := Metric.continuousAt_iff.mp (hGc.continuousAt (hU.mem_nhds hz₀)) ε₀ hε₀
  obtain ⟨r₁, hr₁, hr₁U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
  obtain ⟨r, hr, hrd, hrU⟩ : ∃ r : ℝ, 0 < r ∧ r < d ∧ closedBall z₀ r ⊆ U :=
    ⟨min r₁ (d / 2), lt_min hr₁ (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith),
      (closedBall_subset_closedBall (min_le_left _ _)).trans hr₁U⟩
  -- values of `g` on the closed ball stay spherically far from `∞`
  have hGfar : ∀ w ∈ closedBall z₀ r, 3 * ε₀ ≤ dist (g w) (∞ : ℂ̂) := by
    intro w hw
    have h2 := dist_triangle (g z₀) (g w) (∞ : ℂ̂)
    have h3 : dist (g z₀) (g w) < ε₀ := by
      rw [dist_comm]
      exact hd' (lt_of_le_of_lt (mem_closedBall.mp hw) hrd)
    linarith
  -- points spherically far from `∞` are finite with bounded chart reading
  have hbound : ∀ p : ℂ̂, 2 * ε₀ ≤ dist p (∞ : ℂ̂) →
      p ≠ ∞ ∧ ‖chartFiniteMap p‖ ≤ 2 / (2 * ε₀) := by
    intro p hp
    cases p with
    | infty =>
      rw [dist_self] at hp
      exact absurd hp (not_le.mpr (by linarith))
    | coe x =>
      refine ⟨OnePoint.coe_ne_infty x, ?_⟩
      have hx_eq : dist ((x : ℂ̂)) (∞ : ℂ̂) = 2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
      rw [hx_eq] at hp
      have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hxs : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
        calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
          _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖])
      have h2 : 2 * ε₀ * Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 := (le_div_iff₀ hs).mp hp
      have h3 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 / (2 * ε₀) := by
        rw [le_div_iff₀ (by positivity)]
        linarith [mul_comm (2 * ε₀) (Real.sqrt (1 + ‖x‖ ^ 2))]
      exact hxs.trans h3
  have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
    intro p hp
    cases p with
    | infty => exact absurd rfl hp
    | coe x => rfl
  have hunif : TendstoUniformlyOn Fn g atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hg _ hrU (isCompact_closedBall z₀ r)
  -- eventually the members are close to `g`, hence also far from `∞`, on the ball
  have hFev : ∀ᶠ n in atTop, ∀ w ∈ closedBall z₀ r,
      dist (g w) (Fn n w) < ε₀ ∧ 2 * ε₀ ≤ dist (Fn n w) (∞ : ℂ̂) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif ε₀ hε₀] with n hn w hw
    have h2 := hGfar w hw
    have h3 := dist_triangle (g w) (Fn n w) (∞ : ℂ̂)
    exact ⟨hn w hw, by linarith [hn w hw]⟩
  -- eventually the chart readings of the members are holomorphic on the open ball
  have hudiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun w => chartFiniteMap (Fn n w)) (ball z₀ r) := by
    filter_upwards [hFev] with n hn
    refine SphereHolomorphicOn.differentiableOn_chartFiniteMap (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨V, hVo, hwV, hVU, hcase⟩ := hol n w (hrU (ball_subset_closedBall hw))
      refine ⟨V ∩ ball z₀ r, hVo.inter isOpen_ball, ⟨hwV, hw⟩, Set.inter_subset_right, ?_⟩
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
      · exact Or.inr ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
    · exact (hbound _ (hn w (ball_subset_closedBall hw)).2).1
  obtain ⟨C, hC0, hCdef⟩ : ∃ C : ℝ, 0 < C ∧ C = (1 + (2 / (2 * ε₀)) ^ 2) / 2 :=
    ⟨(1 + (2 / (2 * ε₀)) ^ 2) / 2, by positivity, rfl⟩
  -- the chart readings converge uniformly on the closed ball
  have huTLU : TendstoUniformlyOn (fun n w => chartFiniteMap (Fn n w))
      (fun w => chartFiniteMap (g w)) atTop (closedBall z₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hFev, Metric.tendstoUniformlyOn_iff.mp hunif (ε / C) (by positivity)]
      with n hn hn2 w hw
    obtain ⟨hFne, hFbd⟩ := hbound _ (hn w hw).2
    obtain ⟨hGne, hGbd⟩ := hbound _ (le_trans (by linarith) (hGfar w hw))
    have hnorm := norm_sub_le_sphericalDist_mul hGbd hFbd
    have hds : sphericalDist ((chartFiniteMap (g w) : ℂ) : ℂ̂)
        ((chartFiniteMap (Fn n w) : ℂ) : ℂ̂) = dist (g w) (Fn n w) := by
      rw [hcoe _ hGne, hcoe _ hFne]
      rfl
    rw [hds, ← hCdef] at hnorm
    calc dist (chartFiniteMap (g w)) (chartFiniteMap (Fn n w))
        = ‖chartFiniteMap (g w) - chartFiniteMap (Fn n w)‖ := dist_eq_norm _ _
      _ ≤ C * dist (g w) (Fn n w) := hnorm
      _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn2 w hw) hC0
      _ = ε := by field_simp
  -- planar local uniform convergence of the readings on the open ball
  have hTLUb : TendstoLocallyUniformlyOn (fun n w => chartFiniteMap (Fn n w))
      (fun w => chartFiniteMap (g w)) atTop (ball z₀ r) :=
    huTLU.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  -- planar Weierstrass: the limit chart reading is holomorphic on the open ball
  have huGdiff : DifferentiableOn ℂ (fun w => chartFiniteMap (g w)) (ball z₀ r) :=
    hTLUb.differentiableOn hudiff isOpen_ball
  refine ⟨r, hr, ball_subset_closedBall.trans hrU, fun z hz => ?_, huGdiff, ?_, hTLUb⟩
  · exact (hcoe _ (hbound _ (le_trans (by linarith)
      (hGfar z (ball_subset_closedBall hz)))).1).symm
  · filter_upwards [hFev, hudiff] with n hn hdn
    exact ⟨fun z hz =>
      (hcoe _ (hbound _ (hn z (ball_subset_closedBall hz)).2).1).symm, hdn⟩

/-- A rational map of positive degree is nonconstant already on the
finite chart: the coercion has dense range. -/
theorem ne_const_comp_coe_of_isRational {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 1 ≤ degreeOfRational f) :
    ¬ ∃ v : ℂ̂, (fun w : ℂ => f ((w : ℂ̂))) = Function.const ℂ v := by
  rintro ⟨v, hv⟩
  -- Constancy on the dense coe-range extends to all of the sphere.
  have hext : f = Function.const ℂ̂ v :=
    OnePoint.denseRange_coe.equalizer hf.continuous continuous_const hv
  exact hf.ne_const hd v hext

/-- **The chart bridge for non-normality**: at a finite Julia point the
family of iterates read through the coercion chart is not normal — a
normal restriction would transfer through the open embedding `ℂ → ℂ̂` to
normality of the iterate family itself. -/
theorem not_isNormalAt_comp_coe_of_mem_juliaSet {f : ℂ̂ → ℂ̂}
    {p : ℂ} (hp : ((p : ℂ̂)) ∈ JuliaSet f) :
    ¬ IsNormalAt
      {F : ℂ → ℂ̂ | ∃ n : ℕ, F = fun w : ℂ => f^[n] ((w : ℂ̂))} p := by
  rintro ⟨U, hU, hN⟩
  -- The set-builder family is the range of the chart-read iterates.
  have hset : {F : ℂ → ℂ̂ | ∃ n : ℕ, F = fun w : ℂ => f^[n] ((w : ℂ̂))}
      = Set.range fun n : ℕ => fun w : ℂ => f^[n] ((w : ℂ̂)) := by
    ext F
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
  -- The chart-read family is the sphere family precomposed with the coercion.
  have himg : ((fun F : ℂ̂ → ℂ̂ => F ∘ OnePoint.some) '' (Set.range fun n : ℕ => f^[n]))
      = Set.range fun n : ℕ => fun w : ℂ => f^[n] ((w : ℂ̂)) := by
    rw [← Set.range_comp]
    rfl
  -- Transfer normality through the open embedding `ℂ → ℂ̂`.
  have hNsphere : IsNormal (Set.range fun n : ℕ => f^[n]) (OnePoint.some '' U) := by
    refine IsNormal.of_comp_isOpenEmbedding OnePoint.isOpenEmbedding_coe ?_
    rw [himg, ← hset]
    exact hN
  -- The image of the neighborhood is a neighborhood of `↑p` on the sphere.
  have hpF : ((p : ℂ̂)) ∈ FatouSet f := by
    refine ⟨OnePoint.some '' U, ?_, hNsphere⟩
    rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq p]
    exact Filter.image_mem_map hU
  exact hp hpF

set_option maxHeartbeats 400000 in
-- the Zalcman rescaling, chart transfers, and Hurwitz extraction are long
/-- **Repelling periodic points are dense in the Julia set** (the Schwick
rescaling argument). -/
theorem juliaSet_subset_closure_repelling {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f) :
    JuliaSet f ⊆
      closure {p : ℂ̂ | ∃ n : ℕ, IsRepellingPeriodicPt f n p} := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  -- ## Step I: the countable bad set `B`
  -- the iterate readings through the coercion chart
  have hFm_hol : ∀ k : ℕ,
      SphereHolomorphicOn (fun w : ℂ => f^[k] ((w : ℂ̂))) Set.univ := fun k =>
    (hf.iterate hd1 k).sphereHolomorphicOn_comp_coe isOpen_univ
  have hFm_nc : ∀ k : ℕ,
      ¬ ∃ v : ℂ̂, (fun w : ℂ => f^[k] ((w : ℂ̂))) = Function.const ℂ v := by
    intro k
    refine ne_const_comp_coe_of_isRational (hf.iterate hd1 k) ?_
    rw [degreeOfRational_iterate hf hd1 k]
    exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨B, hB_def⟩ : ∃ B : Set ℂ̂, B = {∞} ∪ forwardOrbit f ∞ ∪
      ⋃ k : ℕ, (fun ζ : ℂ => f^[k] ((ζ : ℂ̂))) ''
        {ζ : ℂ | sphericalDeriv (fun w : ℂ => f^[k] ((w : ℂ̂))) ζ = 0} := ⟨_, rfl⟩
  have hB : B.Countable := by
    rw [hB_def]
    refine ((Set.countable_singleton _).union ?_).union
      (Set.countable_iUnion fun k =>
        (countable_setOf_sphericalDeriv_eq_zero (hFm_hol k) (hFm_nc k)).image _)
    exact Set.countable_range fun n : ℕ => f^[n] (∞ : ℂ̂)
  -- ## Step II: the main claim at points outside the bad set
  have MAIN : JuliaSet f \ B ⊆
      closure {p : ℂ̂ | ∃ n : ℕ, IsRepellingPeriodicPt f n p} := by
    rintro z₀ ⟨hz₀J, hz₀B⟩
    -- ## Step III: `z₀` is finite; Zalcman rescaling of the iterate family
    have hz₀ne : z₀ ≠ ∞ := by
      intro h
      apply hz₀B
      rw [hB_def, h]
      exact Or.inl (Or.inl rfl)
    obtain ⟨zb, rfl⟩ : ∃ w : ℂ, z₀ = ((w : ℂ̂)) := by
      cases z₀ with
      | infty => exact absurd rfl hz₀ne
      | coe w => exact ⟨w, rfl⟩
    have hol : ∀ F ∈ {F : ℂ → ℂ̂ | ∃ n : ℕ, F = fun w : ℂ => f^[n] ((w : ℂ̂))},
        SphereHolomorphicOn F Set.univ := by
      rintro F ⟨n, rfl⟩
      exact hFm_hol n
    have hnot : ¬ IsNormalAt
        {F : ℂ → ℂ̂ | ∃ n : ℕ, F = fun w : ℂ => f^[n] ((w : ℂ̂))} zb :=
      not_isNormalAt_comp_coe_of_mem_juliaSet hz₀J
    obtain ⟨F, z, ρ, g, hFmem, hz, hρpos, hρ0, hg, hg1, -, hTLU⟩ :=
      exists_zalcman_rescale isOpen_univ hol (Set.mem_univ zb) hnot
    choose n hn using hFmem
    -- ## Step IV: the Zalcman limit is nonconstant
    have hnc : ¬ ∃ v : ℂ̂, g = Function.const ℂ v := by
      rintro ⟨v, rfl⟩
      have h0 : sphericalDeriv (Function.const ℂ v) 0 = 0 := by
        simp [sphericalDeriv, Function.const]
      exact one_ne_zero (hg1.symm.trans h0)
    -- ## Step V: the regular image of `g` meets the Julia set away from `z₀`
    have hUstar : IsOpen (g '' {ζ : ℂ | sphericalDeriv g ζ ≠ 0}) :=
      isOpen_image_setOf_sphericalDeriv_ne_zero hg
    have hmeet : ∃ y, y ∈ (g '' {ζ : ℂ | sphericalDeriv g ζ ≠ 0} \ {((zb : ℂ̂))})
        ∩ JuliaSet f := by
      by_contra hcon
      push Not at hcon
      obtain ⟨T, hT_def⟩ : ∃ T : Set ℂ̂,
          T = insert ((zb : ℂ̂)) (g '' {ζ : ℂ | sphericalDeriv g ζ = 0}) := ⟨_, rfl⟩
      have hT : T.Countable := by
        rw [hT_def]
        exact ((countable_setOf_sphericalDeriv_eq_zero hg hnc).image g).insert _
      -- every Julia point outside `T` is omitted by `g`
      have hsub : JuliaSet f \ T ⊆ {v : ℂ̂ | ∀ ζ : ℂ, g ζ ≠ v} := by
        rintro j ⟨hjJ, hjT⟩ ζ hgζ
        have hregζ : sphericalDeriv g ζ ≠ 0 := by
          intro h0
          exact hjT (by rw [hT_def]; exact Set.mem_insert_iff.mpr (Or.inr ⟨ζ, h0, hgζ⟩))
        have hjne : j ≠ ((zb : ℂ̂)) := fun h =>
          hjT (by rw [hT_def]; exact Set.mem_insert_iff.mpr (Or.inl h))
        exact hcon j ⟨⟨⟨ζ, hregζ, hgζ⟩, hjne⟩, hjJ⟩
      -- the Julia set minus `T` is infinite
      have hdiff_unc : ¬ (JuliaSet f \ T).Countable := by
        intro hc
        apply not_countable_juliaSet hf hd
        refine (hc.union hT).mono fun x hx => ?_
        by_cases hxT : x ∈ T
        · exact Or.inr hxT
        · exact Or.inl ⟨hx, hxT⟩
      have hinf : (JuliaSet f \ T).Infinite := fun hfin => hdiff_unc hfin.countable
      -- three distinct omitted values force constancy by Picard
      obtain ⟨a, ha⟩ := hinf.nonempty
      obtain ⟨b, hb⟩ := (hinf.sdiff (Set.finite_singleton a)).nonempty
      obtain ⟨c, hc⟩ := (hinf.sdiff ((Set.finite_singleton b).insert a)).nonempty
      have hba : b ≠ a := fun h => hb.2 (Set.mem_singleton_iff.mpr h)
      have hca : c ≠ a := fun h => hc.2 (Set.mem_insert_iff.mpr (Or.inl h))
      have hcb : c ≠ b := fun h =>
        hc.2 (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)))
      exact hnc (eq_const_of_sphereHolomorphicOn_univ_omits hg hba.symm hca.symm
        hcb.symm fun ζ => ⟨hsub ha ζ, hsub hb.1 ζ, hsub hc.1 ζ⟩)
    -- ## Step VI: a regular backward-orbit point `y = ↑η ≠ z₀`
    obtain ⟨ystar, hystar⟩ := hmeet
    have hWopen : IsOpen (g '' {ζ : ℂ | sphericalDeriv g ζ ≠ 0} \ {((zb : ℂ̂))}) :=
      hUstar.sdiff isClosed_singleton
    have hyB := juliaSet_subset_closure_backwardOrbit hf hd hz₀J hystar.2
    rw [_root_.mem_closure_iff] at hyB
    obtain ⟨y, hyW, hyBO⟩ := hyB _ hWopen hystar.1
    obtain ⟨⟨ζ₀, hreg, hgζ₀⟩, hyne⟩ := hyW
    obtain ⟨m, hmy⟩ := hyBO
    have hyne' : y ≠ ((zb : ℂ̂)) := hyne
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · subst h0
        exact absurd ((Function.iterate_zero_apply f y).symm.trans hmy) hyne'
      · exact h
    -- ## Step VII: `y` is finite and the `m`-iterate is regular at its base
    have hyfin : y ≠ ∞ := by
      intro h
      apply hz₀B
      rw [hB_def]
      exact Or.inl (Or.inr ⟨m, by rw [← h]; exact hmy⟩)
    obtain ⟨η, rfl⟩ : ∃ w : ℂ, y = ((w : ℂ̂)) := by
      cases y with
      | infty => exact absurd rfl hyfin
      | coe w => exact ⟨w, rfl⟩
    have hregm : sphericalDeriv (fun w : ℂ => f^[m] ((w : ℂ̂))) η ≠ 0 := by
      intro h0
      apply hz₀B
      rw [hB_def]
      exact Or.inr (Set.mem_iUnion.mpr ⟨m, ⟨η, h0, hmy⟩⟩)
    -- ## Step VIII(a): the chart reading of the rescalings near `ζ₀`
    have hol_gk : ∀ k, SphereHolomorphicOn
        (fun ζ : ℂ => F k (z k + (ρ k : ℂ) * ζ)) Set.univ := by
      intro k
      have h := (hol (F k) ⟨n k, hn k⟩).comp_affine (z k) ((ρ k : ℂ))
      rwa [Set.preimage_univ] at h
    have hgfin : g ζ₀ ≠ ∞ := by
      rw [hgζ₀]
      exact OnePoint.coe_ne_infty η
    obtain ⟨δ₁, hδ₁, -, hghon, hvdiff, hev_vk, hTLUv⟩ :=
      exists_ball_chartReading_of_tendstoLocallyUniformlyOn isOpen_univ hol_gk hTLU
        (Set.mem_univ ζ₀) hgfin
    -- short names for the chart readings of limit and members
    obtain ⟨v, hv_def⟩ : ∃ v : ℂ → ℂ, v = fun w => chartFiniteMap (g w) := ⟨_, rfl⟩
    obtain ⟨vk, hvk_def⟩ : ∃ vk : ℕ → ℂ → ℂ,
        vk = fun k w => chartFiniteMap (F k (z k + (ρ k : ℂ) * w)) := ⟨_, rfl⟩
    have hvdiff2 : DifferentiableOn ℂ v (ball ζ₀ δ₁) := by
      simp only [hv_def]
      exact hvdiff
    have hev_vk2 : ∀ᶠ k in atTop, (∀ w ∈ ball ζ₀ δ₁,
        F k (z k + (ρ k : ℂ) * w) = ((vk k w : ℂ) : ℂ̂)) ∧
        DifferentiableOn ℂ (vk k) (ball ζ₀ δ₁) := by
      simp only [hvk_def]
      exact hev_vk
    have hTLUv2 : TendstoLocallyUniformlyOn vk v atTop (ball ζ₀ δ₁) := by
      simp only [hv_def, hvk_def]
      exact hTLUv
    have hvζ₀ : v ζ₀ = η := by
      simp only [hv_def]
      rw [hgζ₀]
      exact rfl
    -- regularity of the limit reading at `ζ₀`, by the chart formula
    have hform : sphericalDeriv g ζ₀ =
        2 * ‖deriv (fun w => chartFiniteMap (g w)) ζ₀‖ /
          (1 + ‖chartFiniteMap (g ζ₀)‖ ^ 2) := by
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_
        (hvdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ₁)))
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ₁)] with w hw using hghon w hw
    have hderiv_v : deriv v ζ₀ ≠ 0 := by
      simp only [hv_def]
      intro h0
      apply hreg
      rw [hform, h0, norm_zero, mul_zero, zero_div]
    -- ## Step VIII(b): the chart reading of the `m`-iterate near `η`
    have hFmc : Continuous (fun w : ℂ => f^[m] ((w : ℂ̂))) :=
      continuousOn_univ.mp (hFm_hol m).continuousOn
    obtain ⟨O, hO_def⟩ : ∃ O : Set ℂ, O = {w : ℂ | f^[m] ((w : ℂ̂)) ≠ ∞} := ⟨_, rfl⟩
    have hO_open : IsOpen O := by
      rw [hO_def]
      exact (OnePoint.isClosed_infty.isOpen_compl).preimage hFmc
    have hO_ne : ∀ w ∈ O, f^[m] ((w : ℂ̂)) ≠ ∞ := by
      intro w hw
      rw [hO_def] at hw
      exact hw
    have hηO : η ∈ O := by
      rw [hO_def]
      change f^[m] ((η : ℂ̂)) ≠ ∞
      rw [hmy]
      exact OnePoint.coe_ne_infty zb
    -- restrict sphere-holomorphy of the `m`-iterate reading to `O`
    have hFmO : SphereHolomorphicOn (fun w : ℂ => f^[m] ((w : ℂ̂))) O := by
      intro x hx
      obtain ⟨V, hVo, hxV, -, hcase⟩ := hFm_hol m x (Set.mem_univ x)
      refine ⟨V ∩ O, hVo.inter hO_open, ⟨hxV, hx⟩, Set.inter_subset_right, ?_⟩
      rcases hcase with ⟨hne, hdf⟩ | ⟨hne, hdf⟩
      · exact Or.inl ⟨fun w hw => hne w hw.1, hdf.mono Set.inter_subset_left⟩
      · exact Or.inr ⟨fun w hw => hne w hw.1, hdf.mono Set.inter_subset_left⟩
    obtain ⟨um, hum_def⟩ : ∃ um : ℂ → ℂ,
        um = fun w : ℂ => chartFiniteMap (f^[m] ((w : ℂ̂))) := ⟨_, rfl⟩
    have hum_diff : DifferentiableOn ℂ um O := by
      simp only [hum_def]
      exact hFmO.differentiableOn_chartFiniteMap hO_ne
    have hum_hon : ∀ w ∈ O, f^[m] ((w : ℂ̂)) = ((um w : ℂ) : ℂ̂) := by
      simp only [hum_def]
      intro w hw
      cases hval : f^[m] ((w : ℂ̂)) with
      | infty => exact absurd hval (hO_ne w hw)
      | coe t =>
        have ct : chartFiniteMap ((t : ℂ) : ℂ̂) = t := rfl
        rw [ct]
    have hum_η : um η = zb := by
      simp only [hum_def]
      rw [hmy]
      exact rfl
    -- regularity of the `m`-iterate reading at `η`, by the chart formula
    have hformm : sphericalDeriv (fun w : ℂ => f^[m] ((w : ℂ̂))) η =
        2 * ‖deriv (fun w : ℂ => chartFiniteMap (f^[m] ((w : ℂ̂)))) η‖ /
          (1 + ‖chartFiniteMap (f^[m] ((η : ℂ̂)))‖ ^ 2) := by
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_
        ((hFmO.differentiableOn_chartFiniteMap hO_ne).differentiableAt
          (hO_open.mem_nhds hηO))
      filter_upwards [hO_open.mem_nhds hηO] with w hw
      cases hval : f^[m] ((w : ℂ̂)) with
      | infty => exact absurd hval (hO_ne w hw)
      | coe t =>
        have ct : chartFiniteMap ((t : ℂ) : ℂ̂) = t := rfl
        rw [ct]
    have hderiv_um : deriv um η ≠ 0 := by
      simp only [hum_def]
      intro h0
      apply hregm
      rw [hformm, h0, norm_zero, mul_zero, zero_div]
    -- ## Step VIII(c): composing the readings on a small closed ball
    obtain ⟨σ, hσ, hσO⟩ : ∃ σ : ℝ, 0 < σ ∧ closedBall η σ ⊆ O :=
      nhds_basis_closedBall.mem_iff.mp (hO_open.mem_nhds hηO)
    have hv_cont : ContinuousAt v ζ₀ :=
      (hvdiff2.continuousOn).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ₁))
    obtain ⟨δ₂', hδ₂', hδ₂'cl⟩ := Metric.continuousAt_iff.mp hv_cont (σ / 2) (by positivity)
    obtain ⟨δ₂, hδ₂, hδ₂sub, hδ₂cl⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧
        closedBall ζ₀ δ₂ ⊆ ball ζ₀ δ₁ ∧
        ∀ w ∈ closedBall ζ₀ δ₂, dist (v w) (v ζ₀) < σ / 2 := by
      refine ⟨min (δ₁ / 2) (δ₂' / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
      · exact closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))
      · intro w hw
        refine hδ₂'cl ?_
        rw [mem_closedBall] at hw
        exact lt_of_le_of_lt (hw.trans (min_le_right _ _)) (by linarith)
    have hv_in : ∀ w ∈ closedBall ζ₀ δ₂, v w ∈ ball η (σ / 2) := by
      intro w hw
      rw [mem_ball, ← hvζ₀]
      exact hδ₂cl w hw
    have hv_inO : ∀ w ∈ closedBall ζ₀ δ₂, v w ∈ O := fun w hw =>
      hσO (ball_subset_closedBall (ball_subset_ball (by linarith) (hv_in w hw)))
    -- the member readings converge uniformly on the closed ball
    have hTUv : TendstoUniformlyOn vk v atTop (closedBall ζ₀ δ₂) :=
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hTLUv2)
        _ hδ₂sub (isCompact_closedBall ζ₀ δ₂)
    -- eventually the member readings map the closed ball into `closedBall η σ`
    have hev_map : ∀ᶠ k in atTop, ∀ w ∈ closedBall ζ₀ δ₂,
        vk k w ∈ closedBall η σ := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hTUv (σ / 2) (by positivity)]
        with k hk w hw
      have h1 := hk w hw
      have h2 := hv_in w hw
      rw [mem_ball] at h2
      rw [mem_closedBall]
      have h3 := dist_triangle (vk k w) (v w) η
      rw [dist_comm] at h1
      linarith
    -- the composed readings and their convergence
    obtain ⟨χ, hχ_def⟩ : ∃ χ : ℂ → ℂ, χ = fun ζ => um (v ζ) := ⟨_, rfl⟩
    obtain ⟨χk, hχk_def⟩ : ∃ χk : ℕ → ℂ → ℂ, χk = fun k ζ => um (vk k ζ) := ⟨_, rfl⟩
    have hχ_diff : DifferentiableOn ℂ χ (ball ζ₀ δ₂) := by
      simp only [hχ_def]
      exact hum_diff.comp (hvdiff2.mono (ball_subset_closedBall.trans hδ₂sub))
        fun ζ hζ => hv_inO ζ (ball_subset_closedBall hζ)
    have hev_χk : ∀ᶠ k in atTop, DifferentiableOn ℂ (χk k) (ball ζ₀ δ₂) := by
      filter_upwards [hev_vk2, hev_map] with k hk hmapk
      simp only [hχk_def]
      exact hum_diff.comp (hk.2.mono (ball_subset_closedBall.trans hδ₂sub))
        fun ζ hζ => hσO (hmapk ζ (ball_subset_closedBall hζ))
    -- uniform continuity of `um` on the compact target ball gives the TLU
    have hum_uc : UniformContinuousOn um (closedBall η σ) :=
      (isCompact_closedBall η σ).uniformContinuousOn_of_continuous
        ((hum_diff.continuousOn).mono hσO)
    have hTUχ : TendstoUniformlyOn (fun k ζ => um (vk k ζ)) (fun ζ => um (v ζ))
        atTop (closedBall ζ₀ δ₂) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨δ', hδ', hδ'cl⟩ := Metric.uniformContinuousOn_iff.mp hum_uc ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hTUv (min δ' (σ / 2))
        (lt_min hδ' (by positivity)), hev_map] with k hk hmapk w hw
      refine hδ'cl _ (ball_subset_closedBall (ball_subset_ball (by linarith)
        (hv_in w hw))) _ (hmapk w hw) ?_
      exact lt_of_lt_of_le (hk w hw) (min_le_left _ _)
    have hTLUχ : TendstoLocallyUniformlyOn χk χ atTop (ball ζ₀ δ₂) := by
      simp only [hχ_def, hχk_def]
      exact hTUχ.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
    -- ## Step VIII(d): the key identity for the composed iterate
    have hkey : ∀ᶠ k in atTop, ∀ ζ ∈ closedBall ζ₀ δ₂,
        f^[m + n k] ((z k + (ρ k : ℂ) * ζ : ℂ) : ℂ̂) = ((χk k ζ : ℂ) : ℂ̂) := by
      filter_upwards [hev_vk2, hev_map] with k hk hmapk ζ hζ
      have h1 : f^[m + n k] ((z k + (ρ k : ℂ) * ζ : ℂ) : ℂ̂)
          = f^[m] (f^[n k] ((z k + (ρ k : ℂ) * ζ : ℂ) : ℂ̂)) :=
        Function.iterate_add_apply f m (n k) _
      have h2 : f^[n k] ((z k + (ρ k : ℂ) * ζ : ℂ) : ℂ̂)
          = F k (z k + (ρ k : ℂ) * ζ) := by
        rw [hn k]
      have h4 : f^[m] (((vk k ζ : ℂ) : ℂ̂)) = ((um (vk k ζ) : ℂ) : ℂ̂) :=
        hum_hon _ (hσO (hmapk ζ hζ))
      simp only [hχk_def]
      rw [h1, h2, hk.1 ζ (hδ₂sub hζ), h4]
    -- ## Step IX: the recentred root functions and Hurwitz extraction
    obtain ⟨q, hq_def⟩ : ∃ q : ℂ → ℂ, q = fun ζ => χ ζ - ((zb : ℂ)) := ⟨_, rfl⟩
    obtain ⟨qk, hqk_def⟩ : ∃ qk : ℕ → ℂ → ℂ,
        qk = fun k ζ => χk k ζ - (z k + (ρ k : ℂ) * ζ) := ⟨_, rfl⟩
    -- the affine recenterings converge uniformly to the constant `zb`
    have hTUβ : TendstoUniformlyOn (fun k ζ => z k + (ρ k : ℂ) * ζ)
        (fun _ => (zb : ℂ)) atTop (closedBall ζ₀ δ₂) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hz' : Tendsto (fun k => ‖z k - zb‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp hz
      have hρ' : Tendsto (fun k => ρ k * (‖ζ₀‖ + δ₂)) atTop (𝓝 0) := by
        have h := hρ0.mul_const (‖ζ₀‖ + δ₂)
        rwa [zero_mul] at h
      have hsum : Tendsto (fun k => ‖z k - zb‖ + ρ k * (‖ζ₀‖ + δ₂)) atTop (𝓝 0) := by
        have h := hz'.add hρ'
        rwa [add_zero] at h
      filter_upwards [hsum.eventually (eventually_lt_nhds hε)] with k hk ζ hζ
      have hgoal : dist (zb : ℂ) (z k + (ρ k : ℂ) * ζ) < ε := by
        rw [dist_comm, dist_eq_norm]
        have h3 : ‖ζ‖ ≤ ‖ζ₀‖ + δ₂ := by
          have h4 : ‖ζ - ζ₀‖ ≤ δ₂ := by
            rw [← dist_eq_norm]
            exact mem_closedBall.mp hζ
          calc ‖ζ‖ = ‖ζ₀ + (ζ - ζ₀)‖ := by congr 1; ring
            _ ≤ ‖ζ₀‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
            _ ≤ ‖ζ₀‖ + δ₂ := by linarith
        have h5 : ‖(z k + (ρ k : ℂ) * ζ) - (zb : ℂ)‖
            ≤ ‖z k - zb‖ + ρ k * (‖ζ₀‖ + δ₂) := by
          have h6 : (z k + (ρ k : ℂ) * ζ) - (zb : ℂ)
              = (z k - zb) + (ρ k : ℂ) * ζ := by ring
          rw [h6]
          refine (norm_add_le _ _).trans ?_
          have h7 : ‖(ρ k : ℂ) * ζ‖ = ρ k * ‖ζ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρpos k)]
          rw [h7]
          have h8 := mul_le_mul_of_nonneg_left h3 (hρpos k).le
          linarith
        linarith
      exact hgoal
    have hTLUq : TendstoLocallyUniformlyOn qk q atTop (ball ζ₀ δ₂) := by
      simp only [hq_def, hqk_def, hχ_def, hχk_def]
      exact ((hTUχ.sub hTUβ).tendstoLocallyUniformlyOn).mono ball_subset_closedBall
    have hev_qk : ∀ᶠ k in atTop, DifferentiableOn ℂ (qk k) (ball ζ₀ δ₂) := by
      filter_upwards [hev_χk] with k hk
      simp only [hqk_def]
      exact hk.sub
        (((differentiable_id.const_mul ((ρ k : ℂ))).const_add (z k)).differentiableOn)
    have hq0 : q ζ₀ = 0 := by
      simp only [hq_def, hχ_def]
      rw [hvζ₀, hum_η, sub_self]
    have hχ_derivζ₀ : deriv χ ζ₀ = deriv um η * deriv v ζ₀ := by
      have h1 : DifferentiableAt ℂ um (v ζ₀) := by
        rw [hvζ₀]
        exact hum_diff.differentiableAt (hO_open.mem_nhds hηO)
      have h2 : DifferentiableAt ℂ v ζ₀ :=
        hvdiff2.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ₁))
      have h3 := deriv_comp ζ₀ h1 h2
      rw [hvζ₀] at h3
      simp only [hχ_def]
      exact h3
    have hq_deriv : deriv q ζ₀ ≠ 0 := by
      have h3 : deriv q ζ₀ = deriv χ ζ₀ := by
        simp only [hq_def]
        exact deriv_sub_const _
      rw [h3, hχ_derivζ₀]
      exact mul_ne_zero hderiv_um hderiv_v
    -- Hurwitz roots within shrinking distances, with the needed side conditions
    have hroots : ∀ j : ℕ, ∀ᶠ k in atTop,
        (∃ ζ : ℂ, ‖ζ - ζ₀‖ < min (δ₂ / 2) (1 / ((j : ℝ) + 1)) ∧ qk k ζ = 0) ∧
        (∀ ζ ∈ closedBall ζ₀ δ₂,
          f^[m + n k] ((z k + (ρ k : ℂ) * ζ : ℂ) : ℂ̂) = ((χk k ζ : ℂ) : ℂ̂)) ∧
        DifferentiableOn ℂ (χk k) (ball ζ₀ δ₂) := by
      intro j
      have hεj : 0 < min (δ₂ / 2) (1 / ((j : ℝ) + 1)) :=
        lt_min (by linarith) (by positivity)
      exact (eventually_exists_root_of_tendstoLocallyUniformlyOn isOpen_ball hev_qk
        hTLUq (mem_ball_self hδ₂) hq0 hq_deriv hεj).and (hkey.and hev_χk)
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_eventually hroots
    choose ζ' hζ'lt hζ'root using fun j => (hφP j).1
    have hζ'mem : ∀ j, ζ' j ∈ ball ζ₀ δ₂ := by
      intro j
      rw [mem_ball, dist_eq_norm]
      exact lt_trans (lt_of_lt_of_le (hζ'lt j) (min_le_left _ _)) (by linarith)
    have hζ'tend : Tendsto ζ' atTop (𝓝 ζ₀) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [dist_eq_norm]
      exact le_of_lt (lt_of_lt_of_le (hζ'lt j) (min_le_right _ _))
    -- ## Step X: the extracted points are repelling periodic points near `z₀`
    obtain ⟨b, hb_def⟩ : ∃ b : ℕ → ℂ,
        b = fun j => z (φ j) + (ρ (φ j) : ℂ) * ζ' j := ⟨_, rfl⟩
    have hfix_b : ∀ j, χk (φ j) (ζ' j) = b j := by
      intro j
      have h := hζ'root j
      simp only [hqk_def] at h
      simp only [hb_def]
      exact sub_eq_zero.mp h
    have hperiodic : ∀ j, f^[m + n (φ j)] ((b j : ℂ) : ℂ̂) = ((b j : ℂ) : ℂ̂) := by
      intro j
      have h := (hφP j).2.1 (ζ' j) (ball_subset_closedBall (hζ'mem j))
      have h2 := hfix_b j
      simp only [hb_def] at h2 ⊢
      rw [h, h2]
    -- the composed-reading derivatives converge to a nonzero limit
    have hTLUχφ : TendstoLocallyUniformlyOn (fun j => χk (φ j)) χ atTop (ball ζ₀ δ₂) := by
      intro u hu x hx
      obtain ⟨t, ht, h⟩ := hTLUχ u hu x hx
      exact ⟨t, ht, hφ.tendsto_atTop.eventually h⟩
    have hc_tend : Tendsto (fun j => deriv (χk (φ j)) (ζ' j)) atTop
        (𝓝 (deriv χ ζ₀)) :=
      tendsto_deriv_apply_of_tendstoLocallyUniformlyOn isOpen_ball
        (Filter.Eventually.of_forall fun j => (hφP j).2.2) hTLUχφ (mem_ball_self hδ₂)
        hζ'tend
    have hc_ne : deriv χ ζ₀ ≠ 0 := by
      rw [hχ_derivζ₀]
      exact mul_ne_zero hderiv_um hderiv_v
    have hcpos : 0 < ‖deriv χ ζ₀‖ / 2 := by
      have := norm_pos_iff.mpr hc_ne
      linarith
    -- the multipliers eventually exceed one in norm: they blow up like `1 / ρ`
    have hmult : ∀ᶠ j in atTop,
        1 < ‖multiplier (f^[m + n (φ j)]) ((b j : ℂ) : ℂ̂)‖ := by
      filter_upwards [hc_tend.norm.eventually
          (eventually_gt_nhds (half_lt_self (norm_pos_iff.mpr hc_ne))),
        (hρ0.comp hφ.tendsto_atTop).eventually (eventually_lt_nhds hcpos)]
        with j h1 h2
      have hρj := hρpos (φ j)
      have hρne : ((ρ (φ j) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρj.ne'
      have hι_bj : (b j - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ) = ζ' j := by
        simp only [hb_def, add_sub_cancel_left]
        exact mul_div_cancel_left₀ _ hρne
      -- the iterate reading agrees with the recentred composed reading near `b j`
      have hev_eq : (fun w : ℂ => chartFiniteMap (f^[m + n (φ j)] ((w : ℂ̂))))
          =ᶠ[𝓝 (b j)] fun w => χk (φ j) ((w - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ)) := by
        have hι_cont : Continuous fun w : ℂ => (w - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ) :=
          (continuous_id.sub continuous_const).div_const _
        have hmem_pre : (fun w : ℂ => (w - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ)) ⁻¹'
            (ball ζ₀ δ₂) ∈ 𝓝 (b j) := by
          refine (hι_cont.isOpen_preimage _ isOpen_ball).mem_nhds ?_
          change (b j - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ) ∈ ball ζ₀ δ₂
          rw [hι_bj]
          exact hζ'mem j
        filter_upwards [hmem_pre] with w hw
        have hwmem : (w - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ) ∈ ball ζ₀ δ₂ := hw
        have hβι : z (φ j) + ((ρ (φ j) : ℝ) : ℂ) *
            ((w - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ)) = w := by
          field_simp
          ring
        have h5 := (hφP j).2.1 _ (ball_subset_closedBall hwmem)
        rw [hβι] at h5
        rw [h5]
        exact rfl
      -- the chain rule for the recentred reading
      have hχd' : HasDerivAt (χk (φ j)) (deriv (χk (φ j)) (ζ' j))
          ((b j - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ)) := by
        rw [hι_bj]
        exact ((hφP j).2.2.differentiableAt
          (isOpen_ball.mem_nhds (hζ'mem j))).hasDerivAt
      have hιd' : HasDerivAt (fun w : ℂ => (w - z (φ j)) / ((ρ (φ j) : ℝ) : ℂ))
          (1 / ((ρ (φ j) : ℝ) : ℂ)) (b j) :=
        ((hasDerivAt_id (b j)).sub_const (z (φ j))).div_const ((ρ (φ j) : ℝ) : ℂ)
      have hcomp := hχd'.comp (b j) hιd'
      have hW_deriv : deriv
          (fun w : ℂ => chartFiniteMap (f^[m + n (φ j)] ((w : ℂ̂)))) (b j)
          = deriv (χk (φ j)) (ζ' j) * (1 / ((ρ (φ j) : ℝ) : ℂ)) := by
        rw [hev_eq.deriv_eq]
        exact hcomp.deriv
      -- the multiplier at the finite point is the derivative of the reading
      have hmeq : multiplier (f^[m + n (φ j)]) ((b j : ℂ) : ℂ̂)
          = deriv (fun w : ℂ => chartFiniteMap (f^[m + n (φ j)] ((w : ℂ̂)))) (b j) := rfl
      have hnorm_mult : ‖multiplier (f^[m + n (φ j)]) ((b j : ℂ) : ℂ̂)‖
          = ‖deriv (χk (φ j)) (ζ' j)‖ / ρ (φ j) := by
        rw [hmeq, hW_deriv, norm_mul, norm_div, norm_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hρj, mul_one_div]
      rw [hnorm_mult]
      exact (one_lt_div hρj).mpr (lt_trans h2 h1)
    -- the periodic points converge to `z₀`
    have hb_tend : Tendsto b atTop (𝓝 (zb : ℂ)) := by
      have h1 : Tendsto (fun j => z (φ j)) atTop (𝓝 zb) := hz.comp hφ.tendsto_atTop
      have h3 : Tendsto (fun j => ((ρ (φ j) : ℝ) : ℂ)) atTop (𝓝 (((0 : ℝ) : ℂ))) :=
        (Complex.continuous_ofReal.tendsto 0).comp (hρ0.comp hφ.tendsto_atTop)
      have h4 := h3.mul hζ'tend
      rw [Complex.ofReal_zero, zero_mul] at h4
      have h5 := h1.add h4
      rw [add_zero] at h5
      simp only [hb_def]
      exact h5
    have hp_tend : Tendsto (fun j => ((b j : ℂ) : ℂ̂)) atTop (𝓝 ((zb : ℂ̂))) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have h6 : Tendsto (fun j => 2 * ‖b j - zb‖) atTop (𝓝 0) := by
        have h7 : Tendsto (fun j => ‖b j - zb‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.mp hb_tend
        have h8 := h7.const_mul (2 : ℝ)
        rwa [mul_zero] at h8
      refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h6
      calc dist (((b j : ℂ) : ℂ̂)) ((zb : ℂ̂))
          = sphericalDist (((b j : ℂ) : ℂ̂)) ((zb : ℂ̂)) := rfl
        _ ≤ 2 * ‖b j - zb‖ := sphericalDist_coe_le_norm_sub _ _
    -- conclude: `z₀` is a limit of repelling periodic points
    refine mem_closure_of_tendsto hp_tend ?_
    filter_upwards [hmult] with j hj
    exact ⟨m + n (φ j), Nat.lt_of_lt_of_le hm (Nat.le_add_right m _), hperiodic j, hj⟩
  exact (juliaSet_subset_closure_diff_countable hf hd hB).trans
    (closure_minimal MAIN isClosed_closure)

/-- **The Fatou–Julia density theorem**: the Julia set of a rational map
of degree at least two is the closure of its repelling periodic points. -/
theorem juliaSet_eq_closure_repelling {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) :
    JuliaSet f = closure {p : ℂ̂ | ∃ n : ℕ, IsRepellingPeriodicPt f n p} :=
  Set.Subset.antisymm (juliaSet_subset_closure_repelling hf hd)
    (closure_setOf_isRepellingPeriodicPt_subset_juliaSet hf (le_trans one_le_two hd))

end NoWanderingDomains
