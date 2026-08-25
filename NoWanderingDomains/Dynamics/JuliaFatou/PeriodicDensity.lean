/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.JuliaFatou.RepellingCycles

/-!
# Periodic points are dense in the Julia set

The Fatou–Julia density argument: every neighborhood of a Julia point of a
rational map of degree at least two contains a periodic point
(`juliaSet_subset_closure_periodicPt`).

Given `z₀ ∈ JuliaSet f` and a neighborhood `U`, perfectness supplies a
finite point `p ∈ JuliaSet f ∩ U` avoiding the finitely many critical
values of `f` and `f^[2]`; non-total-invariance of Julia points supplies
backward orbit points `q ∈ f⁻¹{p} \ {p}` and `r ∈ f⁻¹{q} \ {q, p}`, and
local holomorphic inverse branches `g₁` (of `f`, through `q`) and `g₂`
(of `f^[2]`, through `r`) on a disk `D` around `p`. If no point of `D`
were periodic, the cross-ratio family

`χₙ(z) = ((f^[n] z − g₁ z)(z − g₂ z)) / ((f^[n] z − g₂ z)(z − g₁ z))`

— realized through `mobiusApply` with coefficients holomorphic in `z` —
would consist of honestly holomorphic functions on `D` omitting `0` and
`1` (a value `0`, `1`, or `∞` produces a periodic point of period `n`,
`n`, or `n + k`), so Montel–Carathéodory would make it normal; the
inverse Möbius application (`IsNormal.mobiusApply_comp`) would transfer
normality back to the iterate family, making `p` a Fatou point.

This is half of the density-of-repelling-cycles theorem; combined with
the finiteness of non-repelling cycles it yields
`JuliaSet f = closure {repelling periodic points}`.
-/

open OnePoint Polynomial Filter Topology Metric Function

namespace NoWanderingDomains

/-- **Normality transfers through Möbius applications with continuous
coefficients**: if a family is normal on an open `D` and the coefficient
functions are continuous with nonvanishing determinant on `D`, the
transformed family is normal on `D`. Joint uniform continuity of
`mobiusApply` on compacts carries locally uniform convergence through. -/
theorem IsNormal.mobiusApply_comp {𝓕 : Set (ℂ → ℂ̂)} {D : Set ℂ}
    (hD : IsOpen D) (hN : IsNormal 𝓕 D) {a b c d : ℂ → ℂ}
    (ha : ContinuousOn a D) (hb : ContinuousOn b D) (hc : ContinuousOn c D)
    (hd' : ContinuousOn d D)
    (hdet : ∀ z ∈ D, a z * d z - b z * c z ≠ 0) :
    IsNormal ((fun F : ℂ → ℂ̂ =>
      fun z => mobiusApply (a z) (b z) (c z) (d z) (F z)) '' 𝓕) D := by
  intro seq
  choose f hf hfe using fun n => (seq n).2
  obtain ⟨φ, hφ, G, hG⟩ := hN fun n => ⟨f n, hf n⟩
  refine ⟨φ, hφ, fun z => mobiusApply (a z) (b z) (c z) (d z) (G z), ?_⟩
  have key : TendstoLocallyUniformlyOn
      (fun n => fun z => mobiusApply (a z) (b z) (c z) (d z) (f (φ n) z))
      (fun z => mobiusApply (a z) (b z) (c z) (d z) (G z)) atTop D := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD]
    intro K hKD hK
    have hΘ : ContinuousOn (fun z => (a z, b z, c z, d z)) K :=
      (ha.prodMk (hb.prodMk (hc.prodMk hd'))).mono hKD
    have hSc : IsCompact
        ((((fun z => (a z, b z, c z, d z)) '' K) ×ˢ (Set.univ : Set ℂ̂))) :=
      (hK.image_of_continuousOn hΘ).prod isCompact_univ
    have hSsub : (((fun z => (a z, b z, c z, d z)) '' K) ×ˢ (Set.univ : Set ℂ̂)) ⊆
        {q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ |
          q.1.1 * q.1.2.2.2 - q.1.2.1 * q.1.2.2.1 ≠ 0} := by
      rintro ⟨p, w⟩ ⟨⟨z, hz, rfl⟩, -⟩
      exact hdet z (hKD hz)
    have hUC : UniformContinuousOn (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
        (((fun z => (a z, b z, c z, d z)) '' K) ×ˢ (Set.univ : Set ℂ̂)) :=
      hSc.uniformContinuousOn_of_continuous (continuousOn_mobiusApply.mono hSsub)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
    have hev := Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp hG K hKD hK) δ hδ
    filter_upwards [hev] with n hn z hz
    have hp₁ : (((a z, b z, c z, d z), G z) : (ℂ × ℂ × ℂ × ℂ) × ℂ̂)
        ∈ (((fun z => (a z, b z, c z, d z)) '' K) ×ˢ (Set.univ : Set ℂ̂)) :=
      ⟨⟨z, hz, rfl⟩, Set.mem_univ _⟩
    have hp₂ : (((a z, b z, c z, d z), f (φ n) z) : (ℂ × ℂ × ℂ × ℂ) × ℂ̂)
        ∈ (((fun z => (a z, b z, c z, d z)) '' K) ×ˢ (Set.univ : Set ℂ̂)) :=
      ⟨⟨z, hz, rfl⟩, Set.mem_univ _⟩
    have hd2 : dist ((((a z, b z, c z, d z), G z)) : (ℂ × ℂ × ℂ × ℂ) × ℂ̂)
        (((a z, b z, c z, d z), f (φ n) z)) = dist (G z) (f (φ n) z) := by
      rw [Prod.dist_eq, dist_self]
      exact max_eq_right dist_nonneg
    have hfin := hδε _ hp₁ _ hp₂ (by rw [hd2]; exact hn z hz)
    exact hfin
  exact key.congr fun n z _ => congrFun (hfe (φ n)) z

/-- The finite-chart reading of the cross-ratio of a sphere-holomorphic
map against two separated holomorphic sections is holomorphic: away from
the poles of `F` the cross-ratio is a quotient with nonvanishing
denominator, and across a pole the reading rewrites as a quotient in the
reciprocal chart, holomorphic by the same separation. -/
theorem differentiableOn_chartFiniteMap_mobius_cross {F : ℂ → ℂ̂} {D : Set ℂ}
    (hD : IsOpen D) (hF : SphereHolomorphicOn F D) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D)
    (hsep : ∀ z ∈ D, z ≠ g₁ z ∧ z ≠ g₂ z ∧ g₁ z ≠ g₂ z)
    (hF₂ : ∀ z ∈ D, F z ≠ ((g₂ z : ℂ) : ℂ̂)) :
    DifferentiableOn ℂ (fun z => chartFiniteMap
      (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z)))
        (z - g₁ z) (-(g₂ z * (z - g₁ z))) (F z))) D := by
  have _ := hD
  have cf : ∀ t : ℂ, chartFiniteMap (t : ℂ̂) = t := fun _ => rfl
  have ci : ∀ t : ℂ, chartInftyMap (t : ℂ̂) = t⁻¹ := fun _ => rfl
  have ci0 : chartInftyMap (∞ : ℂ̂) = 0 := rfl
  refine differentiableOn_of_locally_differentiableOn fun z₀ hz₀ => ?_
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hF z₀ hz₀
  refine ⟨V, hVo, hzV, ?_⟩
  have hc1 : ∀ w ∈ V, w - g₁ w ≠ 0 := fun w hw => sub_ne_zero.mpr (hsep w (hVU hw)).1
  rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
  · -- finite-chart disjunct
    have hkey : ∀ w ∈ V,
        chartFiniteMap (mobiusApply (w - g₂ w) (-(g₁ w * (w - g₂ w)))
            (w - g₁ w) (-(g₂ w * (w - g₁ w))) (F w))
          = ((w - g₂ w) * (chartFiniteMap (F w) - g₁ w))
            / ((w - g₁ w) * (chartFiniteMap (F w) - g₂ w))
        ∧ chartFiniteMap (F w) - g₂ w ≠ 0 := by
      intro w hw
      cases hFw : F w with
      | infty => exact absurd hFw (hne w hw)
      | coe x =>
        have hx2 : x - g₂ w ≠ 0 :=
          sub_ne_zero.mpr fun h => hF₂ w (hVU hw) (by rw [hFw, h])
        have hden : (w - g₁ w) * x + -(g₂ w * (w - g₁ w))
            = (w - g₁ w) * (x - g₂ w) := by ring
        have hnum : (w - g₂ w) * x + -(g₁ w * (w - g₂ w))
            = (w - g₂ w) * (x - g₁ w) := by ring
        have hcond : ¬((w - g₁ w) * x + -(g₂ w * (w - g₁ w)) = 0) := by
          rw [hden]
          exact mul_ne_zero (hc1 w hw) hx2
        constructor
        · rw [mobiusApply_coe, if_neg hcond, cf, cf, hnum, hden]
        · rw [cf]
          exact hx2
    have hW : DifferentiableOn ℂ (fun w =>
        ((w - g₂ w) * (chartFiniteMap (F w) - g₁ w))
          / ((w - g₁ w) * (chartFiniteMap (F w) - g₂ w))) V := by
      refine DifferentiableOn.div ?_ ?_ fun w hw => mul_ne_zero (hc1 w hw) (hkey w hw).2
      · exact (differentiableOn_id.sub (hg₂.mono hVU)).mul (hdiff.sub (hg₁.mono hVU))
      · exact (differentiableOn_id.sub (hg₁.mono hVU)).mul (hdiff.sub (hg₂.mono hVU))
    exact (hW.congr fun w hw => (hkey w hw).1).mono Set.inter_subset_right
  · -- infinity-chart disjunct
    have hkey : ∀ w ∈ V,
        chartFiniteMap (mobiusApply (w - g₂ w) (-(g₁ w * (w - g₂ w)))
            (w - g₁ w) (-(g₂ w * (w - g₁ w))) (F w))
          = ((w - g₂ w) * (1 - chartInftyMap (F w) * g₁ w))
            / ((w - g₁ w) * (1 - chartInftyMap (F w) * g₂ w))
        ∧ 1 - chartInftyMap (F w) * g₂ w ≠ 0 := by
      intro w hw
      cases hFw : F w with
      | infty =>
        constructor
        · rw [mobiusApply_infty, if_neg (hc1 w hw), cf, ci0]
          simp
        · rw [ci0]
          simp
      | coe x =>
        have hx0 : x ≠ 0 := fun h => hne w hw (by rw [hFw, h])
        have hx2 : x - g₂ w ≠ 0 :=
          sub_ne_zero.mpr fun h => hF₂ w (hVU hw) (by rw [hFw, h])
        have h1 : 1 - x⁻¹ * g₁ w = x⁻¹ * (x - g₁ w) := by field_simp
        have h2 : 1 - x⁻¹ * g₂ w = x⁻¹ * (x - g₂ w) := by field_simp
        have hden : (w - g₁ w) * x + -(g₂ w * (w - g₁ w))
            = (w - g₁ w) * (x - g₂ w) := by ring
        have hnum : (w - g₂ w) * x + -(g₁ w * (w - g₂ w))
            = (w - g₂ w) * (x - g₁ w) := by ring
        have hcond : ¬((w - g₁ w) * x + -(g₂ w * (w - g₁ w)) = 0) := by
          rw [hden]
          exact mul_ne_zero (hc1 w hw) hx2
        constructor
        · rw [mobiusApply_coe, if_neg hcond, cf, ci, h1, h2, hnum, hden]
          rw [(by ring : (w - g₂ w) * (x⁻¹ * (x - g₁ w))
            = x⁻¹ * ((w - g₂ w) * (x - g₁ w)))]
          rw [(by ring : (w - g₁ w) * (x⁻¹ * (x - g₂ w))
            = x⁻¹ * ((w - g₁ w) * (x - g₂ w)))]
          rw [mul_div_mul_left _ _ (inv_ne_zero hx0)]
        · rw [ci, h2]
          exact mul_ne_zero (inv_ne_zero hx0) hx2
    have hW : DifferentiableOn ℂ (fun w =>
        ((w - g₂ w) * (1 - chartInftyMap (F w) * g₁ w))
          / ((w - g₁ w) * (1 - chartInftyMap (F w) * g₂ w))) V := by
      refine DifferentiableOn.div ?_ ?_ fun w hw => mul_ne_zero (hc1 w hw) (hkey w hw).2
      · exact (differentiableOn_id.sub (hg₂.mono hVU)).mul
          ((differentiableOn_const 1).sub (hdiff.mul (hg₁.mono hVU)))
      · exact (differentiableOn_id.sub (hg₁.mono hVU)).mul
          ((differentiableOn_const 1).sub (hdiff.mul (hg₂.mono hVU)))
    exact (hW.congr fun w hw => (hkey w hw).1).mono Set.inter_subset_right

set_option maxHeartbeats 400000 in
-- Long single-declaration assembly: branch selection, the cross-ratio
-- family, Montel, and the Möbius recovery all live in one proof term.
/-- **Periodic points are dense in the Julia set** of a rational map of
degree at least two. -/
theorem juliaSet_subset_closure_periodicPt {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) :
    JuliaSet f ⊆
      closure {z : ℂ̂ | ∃ n : ℕ, 0 < n ∧ Function.IsPeriodicPt f n z} := by
  intro z₀ hz₀
  rw [_root_.mem_closure_iff]
  intro U hUo hz₀U
  by_contra hno
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hsurj : Function.Surjective f := hf.surjective (hf.ne_const hd1)
  have hfex := hf
  obtain ⟨r, hr⟩ := hfex
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  have e0 : ∀ w : ℂ, r.toSphereMap ((w : ℂ̂)) = if r.denReduced.eval w = 0 then ∞
      else (((r.numReduced.eval w / r.denReduced.eval w : ℂ)) : ℂ̂) := fun _ => rfl
  have hW : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  have hWfin : {x : ℂ | r.wronskian.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hW
  -- The bad set of critical-type points and its forward images.
  obtain ⟨badcrit, hbaddef⟩ : ∃ s : Set ℂ̂,
      s = (fun x : ℂ => ((x : ℂ̂))) '' {x : ℂ | r.wronskian.IsRoot x} ∪ {∞} := ⟨_, rfl⟩
  have hbadfin : badcrit.Finite := by
    rw [hbaddef]; exact (hWfin.image _).union (Set.finite_singleton _)
  obtain ⟨B, hBdef⟩ : ∃ s : Set ℂ̂,
      s = f '' badcrit ∪ f^[2] '' badcrit ∪ {∞} := ⟨_, rfl⟩
  have hBfin : B.Finite := by
    rw [hBdef]
    exact ((hbadfin.image f).union (hbadfin.image _)).union (Set.finite_singleton _)
  have hinfB : ∞ ∈ B := by rw [hBdef]; exact Set.mem_union_right _ rfl
  have hinfbad : ∞ ∈ badcrit := by rw [hbaddef]; exact Set.mem_union_right _ rfl
  -- The Julia set meets `U` in infinitely many points (perfectness).
  have hUJinf : (U ∩ JuliaSet f).Infinite := by
    intro hfin
    have hopen : IsOpen (U \ ((U ∩ JuliaSet f) \ {z₀})) :=
      hUo.sdiff ((hfin.subset Set.sdiff_subset).isClosed)
    have hz₀mem : z₀ ∈ U \ ((U ∩ JuliaSet f) \ {z₀}) := ⟨hz₀U, fun hc => hc.2 rfl⟩
    obtain ⟨y, hy, hyne⟩ := accPt_iff_nhds.mp ((juliaSet_perfect hf hd).acc z₀ hz₀) _
      (hopen.mem_nhds hz₀mem)
    exact hy.1.2 ⟨⟨hy.1.1, hy.2⟩, hyne⟩
  -- Select a Julia point `p ∈ U` avoiding the bad images.
  obtain ⟨p, hp⟩ := (hUJinf.sdiff hBfin).nonempty
  have hpU : p ∈ U := hp.1.1
  have hpJ : p ∈ JuliaSet f := hp.1.2
  have hpB : p ∉ B := hp.2
  have hpinf : p ≠ ∞ := fun h => hpB (h ▸ hinfB)
  obtain ⟨pz, hpz⟩ := OnePoint.ne_infty_iff_exists.mp hpinf
  -- Julia points have a backward-orbit point distinct from themselves.
  have hback : ∀ x : ℂ̂, x ∈ JuliaSet f → ∃ y : ℂ̂, f y = x ∧ y ≠ x := by
    intro x hx
    by_contra hcon
    have hsub : f ⁻¹' {x} ⊆ {x} := by
      intro y hy
      by_contra hne
      exact hcon ⟨y, hy, hne⟩
    have hfix : f x = x := by
      obtain ⟨y₀, hy₀⟩ := hsurj x
      have hyx : y₀ = x := hsub hy₀
      exact hyx ▸ hy₀
    have hpre : f ⁻¹' {x} = {x} := by
      refine Set.Subset.antisymm hsub ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hfix
    exact hx (mem_fatouSet_of_preimage_singleton hf hd hpre)
  -- First backward point `q`.
  obtain ⟨q, hfq, hqp⟩ := hback p hpJ
  have hqJ : q ∈ JuliaSet f := by
    rw [← juliaSet_preimage_eq_of_isRational hf hd1, Set.mem_preimage, hfq]
    exact hpJ
  have hqbad : q ∉ badcrit := fun hq =>
    hpB (by rw [hBdef]; exact Set.mem_union_left _ (Set.mem_union_left _ ⟨q, hq, hfq⟩))
  have hqinf : q ≠ ∞ := fun h => hqbad (h ▸ hinfbad)
  obtain ⟨qz, hqz⟩ := OnePoint.ne_infty_iff_exists.mp hqinf
  have hqW : r.wronskian.eval qz ≠ 0 := fun h0 =>
    hqbad (by rw [hbaddef]; exact Set.mem_union_left _ ⟨qz, h0, hqz⟩)
  -- Second backward point `s` with `f^[2] s = p`.
  obtain ⟨s, hfs, hsq⟩ := hback q hqJ
  have hf2s : f^[2] s = p := by
    have h2 : f^[2] s = f (f s) := rfl
    rw [h2, hfs, hfq]
  have hsbad : s ∉ badcrit := fun hs =>
    hpB (by rw [hBdef]; exact Set.mem_union_left _ (Set.mem_union_right _ ⟨s, hs, hf2s⟩))
  have hsinf : s ≠ ∞ := fun h => hsbad (h ▸ hinfbad)
  obtain ⟨sz, hsz⟩ := OnePoint.ne_infty_iff_exists.mp hsinf
  have hsW : r.wronskian.eval sz ≠ 0 := fun h0 =>
    hsbad (by rw [hbaddef]; exact Set.mem_union_left _ ⟨sz, h0, hsz⟩)
  have hsp : s ≠ p := by
    intro h
    refine hno ⟨p, hpU, 2, two_pos, ?_⟩
    have hper : f^[2] p = p := h ▸ hf2s
    exact hper
  -- Coordinate-level distinctness.
  have hpq : pz ≠ qz := fun h => hqp (by rw [← hqz, ← hpz, h])
  have hps : pz ≠ sz := fun h => hsp (by rw [← hsz, ← hpz, h])
  have hqs : qz ≠ sz := fun h => hsq (by rw [← hsz, ← hqz, h])
  -- Finite-chart readings of the two backward maps.
  have hfqz : f ((qz : ℂ̂)) = ((pz : ℂ̂)) := by rw [hqz, hfq, hpz]
  have hfsz : f ((sz : ℂ̂)) = ((qz : ℂ̂)) := by rw [hsz, hfs, hqz]
  have hden_q : r.denReduced.eval qz ≠ 0 := by
    intro h0
    have h1 : f ((qz : ℂ̂)) = ∞ := by rw [hr, e0 qz, if_pos h0]
    rw [hfqz] at h1
    exact OnePoint.coe_ne_infty pz h1
  have hden_s : r.denReduced.eval sz ≠ 0 := by
    intro h0
    have h1 : f ((sz : ℂ̂)) = ∞ := by rw [hr, e0 sz, if_pos h0]
    rw [hfsz] at h1
    exact OnePoint.coe_ne_infty qz h1
  have hcrit_q : deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) qz ≠ 0 := by
    rw [hr, r.deriv_reading hden_q]
    exact div_ne_zero hqW (pow_ne_zero 2 hden_q)
  have hcrit_s : deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) sz ≠ 0 := by
    rw [hr, r.deriv_reading hden_s]
    exact div_ne_zero hsW (pow_ne_zero 2 hden_s)
  -- Local inverse branches.
  obtain ⟨V₁, g₁, hV₁o, hpV₁, hg₁p, hg₁diff, hg₁inv⟩ :=
    exists_branch_of_deriv_ne_zero hf hfqz hcrit_q
  obtain ⟨V₂, h₂, hV₂o, hqV₂, hh₂q, hh₂diff, hh₂inv⟩ :=
    exists_branch_of_deriv_ne_zero hf hfsz hcrit_s
  obtain ⟨g₂, hg₂def⟩ : ∃ g : ℂ → ℂ, g = fun y => h₂ (g₁ y) := ⟨_, rfl⟩
  have hg₂p : g₂ pz = sz := by rw [hg₂def]; simp only; rw [hg₁p, hh₂q]
  have hg₁cont : ContinuousOn g₁ V₁ := hg₁diff.continuousOn
  have hΩ₂o : IsOpen (V₁ ∩ g₁ ⁻¹' V₂) := hg₁cont.isOpen_inter_preimage hV₁o hV₂o
  have hpΩ₂ : pz ∈ V₁ ∩ g₁ ⁻¹' V₂ := by
    refine ⟨hpV₁, ?_⟩
    rw [Set.mem_preimage, hg₁p]
    exact hqV₂
  have hg₂diff : DifferentiableOn ℂ g₂ (V₁ ∩ g₁ ⁻¹' V₂) := by
    rw [hg₂def]
    exact hh₂diff.comp (hg₁diff.mono Set.inter_subset_left) (fun z hz => hz.2)
  have hg₂cont : ContinuousOn g₂ (V₁ ∩ g₁ ⁻¹' V₂) := hg₂diff.continuousOn
  -- The open separation locus and the disk `D`.
  have hcontprod : ContinuousOn (fun z : ℂ => (z - g₁ z) * (z - g₂ z) * (g₁ z - g₂ z))
      (V₁ ∩ g₁ ⁻¹' V₂) := by
    have h1 : ContinuousOn g₁ (V₁ ∩ g₁ ⁻¹' V₂) := hg₁cont.mono Set.inter_subset_left
    exact ((continuousOn_id.sub h1).mul (continuousOn_id.sub hg₂cont)).mul (h1.sub hg₂cont)
  have hΩo : IsOpen (((V₁ ∩ g₁ ⁻¹' V₂) ∩ (fun x : ℂ => ((x : ℂ̂))) ⁻¹' U) ∩
      (fun z : ℂ => (z - g₁ z) * (z - g₂ z) * (g₁ z - g₂ z)) ⁻¹' {(0 : ℂ)}ᶜ) := by
    have hbase : IsOpen ((V₁ ∩ g₁ ⁻¹' V₂) ∩ (fun x : ℂ => ((x : ℂ̂))) ⁻¹' U) :=
      hΩ₂o.inter (hUo.preimage OnePoint.continuous_coe)
    exact (hcontprod.mono (Set.inter_subset_left)).isOpen_inter_preimage hbase
      isOpen_compl_singleton
  have hpΩ : pz ∈ ((V₁ ∩ g₁ ⁻¹' V₂) ∩ (fun x : ℂ => ((x : ℂ̂))) ⁻¹' U) ∩
      (fun z : ℂ => (z - g₁ z) * (z - g₂ z) * (g₁ z - g₂ z)) ⁻¹' {(0 : ℂ)}ᶜ := by
    refine ⟨⟨hpΩ₂, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, hpz]
      exact hpU
    · rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, hg₁p, hg₂p]
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero_of_ne hpq) (sub_ne_zero_of_ne hps))
        (sub_ne_zero_of_ne hqs)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hΩo pz hpΩ
  have hDo : IsOpen (ball pz ρ) := isOpen_ball
  have hpD : pz ∈ ball pz ρ := mem_ball_self hρpos
  -- Facts on the disk.
  have hDV₁ : ball pz ρ ⊆ V₁ := fun z hz => (hρsub hz).1.1.1
  have hDV₂ : ∀ z ∈ ball pz ρ, g₁ z ∈ V₂ := fun z hz => (hρsub hz).1.1.2
  have hDΩ₂ : ball pz ρ ⊆ V₁ ∩ g₁ ⁻¹' V₂ := fun z hz => (hρsub hz).1.1
  have hDU : ∀ z ∈ ball pz ρ, ((z : ℂ̂)) ∈ U := fun z hz => (hρsub hz).1.2
  have hsep : ∀ z ∈ ball pz ρ, z ≠ g₁ z ∧ z ≠ g₂ z ∧ g₁ z ≠ g₂ z := by
    intro z hz
    have hprod : (z - g₁ z) * (z - g₂ z) * (g₁ z - g₂ z) ≠ 0 := (hρsub hz).2
    exact ⟨sub_ne_zero.mp (left_ne_zero_of_mul (left_ne_zero_of_mul hprod)),
      sub_ne_zero.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hprod)),
      sub_ne_zero.mp (right_ne_zero_of_mul hprod)⟩
  have hnoper : ∀ z ∈ ball pz ρ, ∀ n : ℕ, 0 < n → f^[n] ((z : ℂ̂)) ≠ ((z : ℂ̂)) := by
    intro z hz n hn hfix
    exact hno ⟨((z : ℂ̂)), hDU z hz, n, hn, hfix⟩
  have hg₁invD : ∀ z ∈ ball pz ρ, f ((g₁ z : ℂ̂)) = ((z : ℂ̂)) :=
    fun z hz => hg₁inv z (hDV₁ hz)
  have hg₂invD : ∀ z ∈ ball pz ρ, f^[2] ((g₂ z : ℂ̂)) = ((z : ℂ̂)) := by
    intro z hz
    have h1 : f ((g₂ z : ℂ̂)) = ((g₁ z : ℂ̂)) := by
      have h2 : g₂ z = h₂ (g₁ z) := by rw [hg₂def]
      rw [h2]
      exact hh₂inv (g₁ z) (hDV₂ z hz)
    have h3 : f^[2] ((g₂ z : ℂ̂)) = f (f ((g₂ z : ℂ̂))) := rfl
    rw [h3, h1, hg₁invD z hz]
  -- The iterate family avoids the two branch sections and the diagonal.
  have hFi : ∀ n : ℕ, ∀ z ∈ ball pz ρ, f^[n + 1] ((z : ℂ̂)) ≠ ((g₁ z : ℂ̂)) := by
    intro n z hz heq
    refine hnoper z hz (n + 1 + 1) (Nat.succ_pos _) ?_
    calc f^[n + 1 + 1] ((z : ℂ̂)) = f (f^[n + 1] ((z : ℂ̂))) :=
          Function.iterate_succ_apply' f (n + 1) _
      _ = ((z : ℂ̂)) := by rw [heq]; exact hg₁invD z hz
  have hFii : ∀ n : ℕ, ∀ z ∈ ball pz ρ, f^[n + 1] ((z : ℂ̂)) ≠ ((g₂ z : ℂ̂)) := by
    intro n z hz heq
    refine hnoper z hz (2 + (n + 1)) (by omega) ?_
    calc f^[2 + (n + 1)] ((z : ℂ̂)) = f^[2] (f^[n + 1] ((z : ℂ̂))) :=
          Function.iterate_add_apply f 2 (n + 1) _
      _ = ((z : ℂ̂)) := by rw [heq]; exact hg₂invD z hz
  have hFiii : ∀ n : ℕ, ∀ z ∈ ball pz ρ, f^[n + 1] ((z : ℂ̂)) ≠ ((z : ℂ̂)) :=
    fun n z hz => hnoper z hz (n + 1) (Nat.succ_pos n)
  -- Master pointwise computation for the cross-ratio family.
  have hmaster : ∀ n : ℕ, ∀ z ∈ ball pz ρ, ∃ u : ℂ,
      mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
        (f^[n + 1] ((z : ℂ̂))) = ((u : ℂ̂)) ∧ u ≠ 0 ∧ u ≠ 1 ∧
      mobiusApply (-(g₂ z * (z - g₁ z))) (g₁ z * (z - g₂ z)) (-(z - g₁ z)) (z - g₂ z)
        ((u : ℂ̂)) = f^[n + 1] ((z : ℂ̂)) := by
    intro n z hz
    obtain ⟨hs1, hs2, hs3⟩ := hsep z hz
    have hd1' : z - g₁ z ≠ 0 := sub_ne_zero_of_ne hs1
    have hd2' : z - g₂ z ≠ 0 := sub_ne_zero_of_ne hs2
    have hd3' : g₁ z - g₂ z ≠ 0 := sub_ne_zero_of_ne hs3
    cases hFv : f^[n + 1] ((z : ℂ̂)) with
    | coe x =>
        have hx1 : x ≠ g₁ z := by
          intro h; apply hFi n z hz; rw [hFv, h]
        have hx2 : x ≠ g₂ z := by
          intro h; apply hFii n z hz; rw [hFv, h]
        have hx3 : x ≠ z := by
          intro h; apply hFiii n z hz; rw [hFv, h]
        have hxg1 : x - g₁ z ≠ 0 := sub_ne_zero_of_ne hx1
        have hxg2 : x - g₂ z ≠ 0 := sub_ne_zero_of_ne hx2
        have hxz : x - z ≠ 0 := sub_ne_zero_of_ne hx3
        have hnum : (z - g₂ z) * x + -(g₁ z * (z - g₂ z)) = (z - g₂ z) * (x - g₁ z) := by
          ring
        have hcden : (z - g₁ z) * x + -(g₂ z * (z - g₁ z)) = (z - g₁ z) * (x - g₂ z) := by
          ring
        have hcden_ne : (z - g₁ z) * x + -(g₂ z * (z - g₁ z)) ≠ 0 := by
          rw [hcden]; exact mul_ne_zero hd1' hxg2
        obtain ⟨u, hu⟩ : ∃ u : ℂ, u = ((z - g₂ z) * x + -(g₁ z * (z - g₂ z))) /
            ((z - g₁ z) * x + -(g₂ z * (z - g₁ z))) := ⟨_, rfl⟩
        refine ⟨u, ?_, ?_, ?_, ?_⟩
        · rw [mobiusApply_coe, if_neg hcden_ne, OnePoint.coe_eq_coe]
          exact hu.symm
        · rw [hu]
          have hnum_ne : (z - g₂ z) * x + -(g₁ z * (z - g₂ z)) ≠ 0 := by
            rw [hnum]; exact mul_ne_zero hd2' hxg1
          exact div_ne_zero hnum_ne hcden_ne
        · rw [hu]
          intro h1
          rw [div_eq_one_iff_eq hcden_ne] at h1
          have hfac : (g₁ z - g₂ z) * (x - z) = 0 := by linear_combination h1
          rcases mul_eq_zero.mp hfac with h3 | h3
          · exact hd3' h3
          · exact hxz h3
        · rw [mobiusApply_coe]
          have hkey : -(z - g₁ z) * u + (z - g₂ z) =
              (z - g₁ z) * (z - g₂ z) * (g₁ z - g₂ z) / ((z - g₁ z) * (x - g₂ z)) := by
            rw [hu, hnum, hcden]
            field_simp
            ring
          have hne : -(z - g₁ z) * u + (z - g₂ z) ≠ 0 := by
            rw [hkey]
            exact div_ne_zero (mul_ne_zero (mul_ne_zero hd1' hd2') hd3')
              (mul_ne_zero hd1' hxg2)
          rw [if_neg hne, OnePoint.coe_eq_coe, div_eq_iff hne, hu, hnum, hcden]
          field_simp
          ring
    | infty =>
        obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (z - g₂ z) / (z - g₁ z) := ⟨_, rfl⟩
        refine ⟨u, ?_, ?_, ?_, ?_⟩
        · rw [mobiusApply_infty, if_neg hd1', OnePoint.coe_eq_coe]
          exact hu.symm
        · rw [hu]
          exact div_ne_zero hd2' hd1'
        · rw [hu]
          intro h1
          rw [div_eq_one_iff_eq hd1'] at h1
          exact hd3' (by linear_combination h1)
        · rw [mobiusApply_coe]
          have hzero : -(z - g₁ z) * u + (z - g₂ z) = 0 := by
            rw [hu]; field_simp; ring
          rw [if_pos hzero]
  -- Holomorphy of the chart readings of the cross-ratio family.
  have hu_diff : ∀ n : ℕ, DifferentiableOn ℂ (fun z => chartFiniteMap
      (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
        (f^[n + 1] ((z : ℂ̂))))) (ball pz ρ) := fun n =>
    differentiableOn_chartFiniteMap_mobius_cross hDo
      ((hf.iterate hd1 (n + 1)).sphereHolomorphicOn_comp_coe hDo)
      (hg₁diff.mono hDV₁) (hg₂diff.mono hDΩ₂) hsep (hFii n)
  -- Montel–Carathéodory for the readings.
  have hMont := montel_caratheodory hDo
    (𝓕 := Set.range fun n : ℕ => fun z : ℂ => chartFiniteMap
      (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
        (f^[n + 1] ((z : ℂ̂)))))
    (by rintro g ⟨n, rfl⟩; exact hu_diff n)
    (by
      rintro g ⟨n, rfl⟩
      intro z hz
      obtain ⟨u, hχu, hu0, hu1, _⟩ := hmaster n z hz
      have hcfu : chartFiniteMap
          (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z)
            (-(g₂ z * (z - g₁ z))) (f^[n + 1] ((z : ℂ̂)))) = u :=
        congrArg chartFiniteMap hχu
      refine ⟨fun h0 => hu0 ?_, fun h1 => hu1 ?_⟩
      · rw [← hcfu]; exact h0
      · rw [← hcfu]; exact h1)
  -- Normality of the sphere-valued cross-ratio family.
  have hNχ : IsNormal (Set.range fun n : ℕ => fun z : ℂ =>
      mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
        (f^[n + 1] ((z : ℂ̂)))) (ball pz ρ) := by
    refine hMont.of_forall_exists_eqOn ?_
    rintro g ⟨n, rfl⟩
    refine ⟨_, ⟨fun z : ℂ => chartFiniteMap
      (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
        (f^[n + 1] ((z : ℂ̂)))), ⟨n, rfl⟩, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨u, hχu, _, _, _⟩ := hmaster n z hz
    have hcoe : ((chartFiniteMap (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z)
        (-(g₂ z * (z - g₁ z))) (f^[n + 1] ((z : ℂ̂)))) : ℂ̂))
        = mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
          (f^[n + 1] ((z : ℂ̂))) := by
      rw [hχu]
      rfl
    exact hcoe
  -- Transfer normality back through the inverse Möbius application.
  have hcont₁ : ContinuousOn g₁ (ball pz ρ) := hg₁cont.mono hDV₁
  have hcont₂ : ContinuousOn g₂ (ball pz ρ) := hg₂cont.mono hDΩ₂
  have hNrec := hNχ.mobiusApply_comp hDo
    (a := fun z => -(g₂ z * (z - g₁ z))) (b := fun z => g₁ z * (z - g₂ z))
    (c := fun z => -(z - g₁ z)) (d := fun z => z - g₂ z)
    ((hcont₂.mul (continuousOn_id.sub hcont₁)).neg)
    (hcont₁.mul (continuousOn_id.sub hcont₂))
    ((continuousOn_id.sub hcont₁).neg)
    (continuousOn_id.sub hcont₂)
    (by
      intro z hz hz0
      obtain ⟨hs1, hs2, hs3⟩ := hsep z hz
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero_of_ne hs1) (sub_ne_zero_of_ne hs2))
        (sub_ne_zero_of_ne hs3) (by linear_combination hz0))
  -- Normality of the shifted iterate family on the disk.
  have hNF : IsNormal (Set.range fun n : ℕ => fun z : ℂ => f^[n + 1] ((z : ℂ̂)))
      (ball pz ρ) := by
    refine hNrec.of_forall_exists_eqOn ?_
    rintro g ⟨n, rfl⟩
    refine ⟨_, ⟨fun z : ℂ =>
      mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z) (-(g₂ z * (z - g₁ z)))
        (f^[n + 1] ((z : ℂ̂))), ⟨n, rfl⟩, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨u, hχu, _, _, hrec⟩ := hmaster n z hz
    have hgoal : mobiusApply (-(g₂ z * (z - g₁ z))) (g₁ z * (z - g₂ z)) (-(z - g₁ z))
        (z - g₂ z) (mobiusApply (z - g₂ z) (-(g₁ z * (z - g₂ z))) (z - g₁ z)
          (-(g₂ z * (z - g₁ z))) (f^[n + 1] ((z : ℂ̂)))) = f^[n + 1] ((z : ℂ̂)) := by
      rw [hχu]
      exact hrec
    exact hgoal
  -- Pigeonhole: full iterate family is normal on the disk.
  have hNfull : IsNormal (Set.range fun n : ℕ => fun z : ℂ => f^[n] ((z : ℂ̂)))
      (ball pz ρ) := by
    intro seq
    choose m hm using fun j => (seq j).2
    by_cases hinf0 : {j : ℕ | m j = 0}.Infinite
    · have hfreq : ∃ᶠ j in Filter.atTop, m j = 0 :=
        Nat.frequently_atTop_iff_infinite.mpr hinf0
      obtain ⟨ψ, hψ, hψ0⟩ := Filter.extraction_of_frequently_atTop hfreq
      have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => ((z : ℂ̂)))
          (fun z : ℂ => ((z : ℂ̂))) Filter.atTop (ball pz ρ) := by
        intro u hu w _
        exact ⟨ball pz ρ, self_mem_nhdsWithin,
          Filter.Eventually.of_forall fun n y _ => refl_mem_uniformity hu⟩
      refine ⟨ψ, hψ, fun z : ℂ => ((z : ℂ̂)), hbase.congr fun j y _ => ?_⟩
      have h1 : (seq (ψ j) : ℂ → ℂ̂) y = f^[m (ψ j)] ((y : ℂ̂)) :=
        (congrFun (hm (ψ j)) y).symm
      rw [h1, hψ0 j]
      rfl
    · have hfin : {j : ℕ | m j = 0}.Finite := Set.not_infinite.mp hinf0
      have hfreq : ∃ᶠ j in Filter.atTop, m j ≠ 0 :=
        Nat.frequently_atTop_iff_infinite.mpr hfin.infinite_compl
      obtain ⟨ψ, hψ, hψ1⟩ := Filter.extraction_of_frequently_atTop hfreq
      obtain ⟨φ', hφ', g, hg⟩ := hNF fun j =>
        ⟨fun z : ℂ => f^[m (ψ j) - 1 + 1] ((z : ℂ̂)), m (ψ j) - 1, rfl⟩
      refine ⟨ψ ∘ φ', hψ.comp hφ', g, hg.congr fun j y _ => ?_⟩
      have hms : m (ψ (φ' j)) - 1 + 1 = m (ψ (φ' j)) :=
        Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hψ1 (φ' j)))
      calc f^[m (ψ (φ' j)) - 1 + 1] ((y : ℂ̂))
          = f^[m (ψ (φ' j))] ((y : ℂ̂)) := by rw [hms]
        _ = (seq ((ψ ∘ φ') j) : ℂ → ℂ̂) y := congrFun (hm (ψ (φ' j))) y
  -- Transport to the sphere: `p` is a Fatou point, contradiction.
  have h2 : ((fun F : ℂ̂ → ℂ̂ => F ∘ OnePoint.some) '' (Set.range fun n : ℕ => f^[n]))
      = (Set.range fun n : ℕ => fun z : ℂ => f^[n] ((z : ℂ̂))) := by
    rw [← Set.range_comp]
    rfl
  have hNsphere : IsNormal (Set.range fun n : ℕ => f^[n]) (OnePoint.some '' ball pz ρ) := by
    refine IsNormal.of_comp_isOpenEmbedding OnePoint.isOpenEmbedding_coe ?_
    rw [h2]
    exact hNfull
  have hpF : p ∈ FatouSet f := by
    refine ⟨OnePoint.some '' ball pz ρ, ?_, hNsphere⟩
    refine (OnePoint.isOpenEmbedding_coe.isOpenMap _ hDo).mem_nhds ?_
    exact ⟨pz, hpD, hpz⟩
  exact hpJ hpF

end NoWanderingDomains
