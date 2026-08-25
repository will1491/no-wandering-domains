/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.NormalFamilies.StrongMontel.MontelCaratheodory
import NoWanderingDomains.Sphere.SphereHolomorphic

/-!
# Montel–Carathéodory on the Riemann sphere

The general three-point form of the strong Montel theorem
(`montel_caratheodory_sphere`): a family of sphere-holomorphic maps
`f : U → ℂ̂` omitting three fixed distinct values `a, b, c ∈ ℂ̂` is normal
on `U` for the spherical metric.

The proof is a Möbius conjugation of the two-point theorem
`montel_caratheodory`. A Möbius transformation `g` sends `(a, b, c)` to
`(0, 1, ∞)` (`exists_gl_smul_eq_zero_one_infty`); the transformed family
`g • f` omits `∞`, so it consists of honest holomorphic functions
(`SphereHolomorphicOn.differentiableOn_chartFiniteMap` after
`SphereHolomorphicOn.gl_smul`) omitting `0` and `1`, and the two-point
theorem applies. Normality then transfers back through the inverse Möbius
map `g⁻¹ • ·`, which is uniformly continuous because the sphere is compact
(`IsNormal.comp_uniformContinuous`).
-/

open OnePoint Matrix

namespace NoWanderingDomains

/-- **Montel–Carathéodory on the Riemann sphere.** A family of
sphere-holomorphic maps on `U` omitting three fixed distinct values
`a, b, c ∈ ℂ̂` is normal on `U` for the spherical metric. The openness of
`U` is implied by sphere-holomorphy of any member (and the empty family is
trivially normal). -/
theorem montel_caratheodory_sphere {𝓕 : Set (ℂ → ℂ̂)} {U : Set ℂ} {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hol : ∀ f ∈ 𝓕, SphereHolomorphicOn f U)
    (homit : ∀ f ∈ 𝓕, ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    IsNormal 𝓕 U := by
  rcases Set.eq_empty_or_nonempty 𝓕 with rfl | ⟨f₀, hf₀⟩
  · intro seq
    exact absurd (seq 0).2 (Set.notMem_empty _)
  have hU : IsOpen U := (hol f₀ hf₀).isOpen
  obtain ⟨g, hga, hgb, hgc⟩ := exists_gl_smul_eq_zero_one_infty hab hac hbc
  -- The transformed family `g • f` omits `0`, `1`, `∞` pointwise on `U`.
  have hne : ∀ f ∈ 𝓕, ∀ z ∈ U,
      g • f z ≠ ((0 : ℂ) : ℂ̂) ∧ g • f z ≠ ((1 : ℂ) : ℂ̂) ∧ g • f z ≠ ∞ := by
    intro f hf z hz
    obtain ⟨h1, h2, h3⟩ := homit f hf z hz
    refine ⟨fun hEq => ?_, fun hEq => ?_, fun hEq => ?_⟩
    · rw [← hga] at hEq
      exact h1 (MulAction.injective g hEq)
    · rw [← hgb] at hEq
      exact h2 (MulAction.injective g hEq)
    · rw [← hgc] at hEq
      exact h3 (MulAction.injective g hEq)
  -- The chart reads of the transformed family are holomorphic and omit `0`, `1`.
  have hol' : ∀ h ∈ (fun f : ℂ → ℂ̂ => fun z => chartFiniteMap (g • f z)) '' 𝓕,
      DifferentiableOn ℂ h U := by
    rintro _ ⟨f, hf, rfl⟩
    exact ((hol f hf).gl_smul g).differentiableOn_chartFiniteMap
      fun z hz => (hne f hf z hz).2.2
  have homit' : ∀ h ∈ (fun f : ℂ → ℂ̂ => fun z => chartFiniteMap (g • f z)) '' 𝓕,
      ∀ z ∈ U, h z ≠ 0 ∧ h z ≠ 1 := by
    rintro _ ⟨f, hf, rfl⟩ z hz
    obtain ⟨h0, h1, hinf⟩ := hne f hf z hz
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    have hcx : chartFiniteMap (g • f z) = x := by
      rw [← hx]
      rfl
    change chartFiniteMap (g • f z) ≠ 0 ∧ chartFiniteMap (g • f z) ≠ 1
    rw [hcx]
    constructor
    · rintro rfl
      exact h0 hx.symm
    · rintro rfl
      exact h1 hx.symm
  -- Two-point Montel–Carathéodory for the chart reads.
  have hMC := montel_caratheodory hU hol' homit'
  -- Transfer normality to the family `fun z => g • f z`, `f ∈ 𝓕`.
  have h𝓖 : IsNormal ((fun f : ℂ → ℂ̂ => fun z => g • f z) '' 𝓕) U := by
    refine hMC.of_forall_exists_eqOn ?_
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨fun z => ((chartFiniteMap (g • f z) : ℂ) : ℂ̂),
      ⟨fun z => chartFiniteMap (g • f z), ⟨f, hf, rfl⟩, rfl⟩, fun z hz => ?_⟩
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp (hne f hf z hz).2.2
    change ((chartFiniteMap (g • f z) : ℂ) : ℂ̂) = g • f z
    rw [← hx]
    rfl
  -- Transfer back through the uniformly continuous inverse Möbius map.
  have hT : UniformContinuous (fun y : ℂ̂ => g⁻¹ • y) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_gl_smul g⁻¹)
  have hN2 := h𝓖.comp_uniformContinuous hT
  refine hN2.of_forall_exists_eqOn fun f hf => ?_
  exact ⟨fun z => g⁻¹ • (g • f z), ⟨fun z => g • f z, ⟨f, hf, rfl⟩, rfl⟩,
    fun z _ => inv_smul_smul g (f z)⟩

end NoWanderingDomains
