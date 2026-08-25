/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.Schwarz
import NoWanderingDomains.Dynamics.JuliaFatou.Basic
import NoWanderingDomains.Sphere.OpenMapping
import NoWanderingDomains.Sphere.Iterate

/-!
# The Julia set of a rational map of degree at least two is nonempty

If `JuliaSet f = ∅`, the iterate family is normal at every point of the
compact sphere, hence normal on all of it, and uniformly equicontinuous.
A subsequence `f^[φ j]` converges uniformly to a continuous limit `g`, and
the factorization `f^[φ (j+1)] = f^[φ (j+1) - φ j] ∘ f^[φ j]` makes the gap
iterates converge to the identity uniformly on `range g`. Two cases:

* `g` not surjective: a value at positive distance from `range g` is
  eventually omitted by `f^[φ j]`, contradicting the surjectivity of
  nonconstant rational maps.
* `g` surjective: some iterate `F = f^[m]` (`m ≥ 1`) is uniformly close to
  the identity. This contradicts the quantitative separation
  `exists_id_separation`: for such an `F`, all preimages of `0` lie in a
  small disk where the polynomial reading `numReduced / denReduced` has
  derivative close to `1` (Schwarz bound), hence is injective with only
  simple zeros — but `numReduced` has `degreeOfRational F ≥ 2` roots
  counted with multiplicity, all of them in that disk.

No fixed-point index formula, Rouché theorem, or convergence theory of the
limit map is needed: the second extraction has the identity as its limit,
so every estimate is explicit.
-/

open OnePoint Polynomial Filter Topology Metric

namespace NoWanderingDomains

/-- **Rational maps of degree at least two are uniformly separated from the
identity**: there is a universal `ε > 0` such that every rational map of
degree `≥ 2` moves some point of the sphere by at least `ε`. -/
theorem exists_id_separation :
    ∃ ε : ℝ, 0 < ε ∧ ∀ F : ℂ̂ → ℂ̂, IsRational F → 2 ≤ degreeOfRational F →
      ∃ z : ℂ̂, ε ≤ sphericalDist (F z) z := by
  refine ⟨1/1000, by norm_num, ?_⟩
  intro F hF hdeg
  obtain ⟨r, rfl⟩ := hF
  by_contra hsmall
  push Not at hsmall
  -- hsmall : ∀ z, sphericalDist (r.toSphereMap z) z < 1/1000
  -- Square-root comparison helpers.
  have sqrt_le : ∀ t : ℝ, 0 ≤ t → Real.sqrt (1 + t ^ 2) ≤ 1 + t := by
    intro t ht
    have h1 : (1 : ℝ) + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    calc Real.sqrt (1 + t ^ 2) ≤ Real.sqrt ((1 + t) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 1 + t := Real.sqrt_sq (by linarith)
  have one_le_sqrt : ∀ t : ℝ, (1 : ℝ) ≤ Real.sqrt (1 + t ^ 2) := by
    intro t
    have h1 : Real.sqrt 1 ≤ Real.sqrt (1 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
    rwa [Real.sqrt_one] at h1
  -- (1) The witness has degree at least two.
  have hdeg2 : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness r.toSphereMap r rfl]
    exact hdeg
  -- (3) The reduced denominator has no zero in the disk of radius 3.
  have hpole : ∀ z : ℂ, ‖z‖ ≤ 3 → r.denReduced.eval z ≠ 0 := by
    intro z hz hden
    have e : r.toSphereMap (z : ℂ̂) = ∞ := by
      have e0 : r.toSphereMap (z : ℂ̂)
          = if r.denReduced.eval z = 0 then ∞
            else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
      rw [e0, if_pos hden]
    have h1 := hsmall (z : ℂ̂)
    rw [e, sphericalDist_comm, sphericalDist_coe_infty] at h1
    have hs : Real.sqrt (1 + ‖z‖ ^ 2) ≤ 4 :=
      le_trans (sqrt_le _ (norm_nonneg _)) (by linarith)
    have hs' : (1 : ℝ) ≤ Real.sqrt (1 + ‖z‖ ^ 2) := one_le_sqrt _
    unfold chordalDistInfty at h1
    rw [div_lt_iff₀ (lt_of_lt_of_le one_pos hs')] at h1
    linarith
  -- (4) The finite-chart reading of the map on the disk of radius 3.
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ,
      h = fun w => r.numReduced.eval w / r.denReduced.eval w := ⟨_, rfl⟩
  have hval : ∀ z : ℂ, ‖z‖ ≤ 3 → r.toSphereMap (z : ℂ̂) = ((h z : ℂ) : ℂ̂) := by
    intro z hz
    have e0 : r.toSphereMap (z : ℂ̂)
        = if r.denReduced.eval z = 0 then ∞
          else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
    rw [e0, if_neg (hpole z hz)]
    simp only [hh]
  -- (5) The reading is bounded by 15 on the disk of radius 3.
  have hbnd : ∀ z : ℂ, ‖z‖ ≤ 3 → ‖h z‖ ≤ 15 := by
    intro z hz
    by_contra hc
    push Not at hc
    have h1 := hsmall (z : ℂ̂)
    rw [hval z hz, sphericalDist_coe_coe] at h1
    unfold chordalDist at h1
    have hs1 : Real.sqrt (1 + ‖h z‖ ^ 2) ≤ 1 + ‖h z‖ := sqrt_le _ (norm_nonneg _)
    have hs1' : (1 : ℝ) ≤ Real.sqrt (1 + ‖h z‖ ^ 2) := one_le_sqrt _
    have hs2 : Real.sqrt (1 + ‖z‖ ^ 2) ≤ 4 :=
      le_trans (sqrt_le _ (norm_nonneg _)) (by linarith)
    have hs2' : (1 : ℝ) ≤ Real.sqrt (1 + ‖z‖ ^ 2) := one_le_sqrt _
    rw [div_lt_iff₀
      (mul_pos (lt_of_lt_of_le one_pos hs1') (lt_of_lt_of_le one_pos hs2'))] at h1
    have hprod : Real.sqrt (1 + ‖h z‖ ^ 2) * Real.sqrt (1 + ‖z‖ ^ 2)
        ≤ (1 + ‖h z‖) * 4 :=
      mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by linarith [norm_nonneg (h z)])
    linarith [norm_sub_norm_le (h z) z]
  -- (6) The reading is uniformly within 113/1000 of the identity on the disk.
  have heuc : ∀ z : ℂ, ‖z‖ ≤ 3 → ‖h z - z‖ ≤ 113/1000 := by
    intro z hz
    have hb := hbnd z hz
    have h15 : ‖z‖ ≤ (15 : ℝ) := by linarith
    have h1 : ‖h z - z‖
        ≤ (1 + 15 ^ 2) / 2 * sphericalDist ((h z : ℂ) : ℂ̂) (z : ℂ̂) :=
      norm_sub_le_sphericalDist_mul hb h15
    have h2 : sphericalDist ((h z : ℂ) : ℂ̂) (z : ℂ̂) < 1/1000 := by
      have h3 := hsmall (z : ℂ̂)
      rwa [hval z hz] at h3
    linarith
  -- (7) The reading is holomorphic on the disk of radius 3.
  have hdiff : DifferentiableOn ℂ h (ball (0 : ℂ) 3) := by
    rw [hh]
    intro x hx
    have hx3 : ‖x‖ ≤ 3 := le_of_lt (mem_ball_zero_iff.mp hx)
    exact ((r.numReduced.differentiableAt).div (r.denReduced.differentiableAt)
      (hpole x hx3)).differentiableWithinAt
  -- (8) Schwarz-type bound: the derivative of `h - id` is small on the unit ball.
  have hderiv : ∀ z₀ ∈ ball (0 : ℂ) 1, ‖deriv (fun z => h z - z) z₀‖ ≤ 1/4 := by
    intro z₀ hz₀
    have hz₀1 : ‖z₀‖ < 1 := mem_ball_zero_iff.mp hz₀
    have hsubB : ball z₀ 1 ⊆ ball (0 : ℂ) 3 := by
      apply ball_subset_ball'
      rw [dist_zero_right]
      linarith
    have hd1 : DifferentiableOn ℂ (fun z => h z - z) (ball z₀ 1) :=
      (hdiff.mono hsubB).sub differentiableOn_id
    have hmaps : Set.MapsTo (fun z => h z - z) (ball z₀ 1)
        (closedBall (h z₀ - z₀) (1/4)) := by
      intro ζ hζ
      have hζ3 : ‖ζ‖ ≤ 3 := le_of_lt (mem_ball_zero_iff.mp (hsubB hζ))
      have hz₀3 : ‖z₀‖ ≤ 3 := by linarith
      have e1 := heuc ζ hζ3
      have e2 := heuc z₀ hz₀3
      have e3 : ‖(h ζ - ζ) - (h z₀ - z₀)‖ ≤ 1/4 := by
        calc ‖(h ζ - ζ) - (h z₀ - z₀)‖
            ≤ ‖h ζ - ζ‖ + ‖h z₀ - z₀‖ := norm_sub_le _ _
          _ ≤ 1/4 := by linarith
      exact mem_closedBall.mpr (by rw [dist_eq_norm]; exact e3)
    have hfin := Complex.norm_deriv_le_div_of_mapsTo_ball hd1 hmaps one_pos
    linarith [hfin]
  -- (9) The reading is injective on the unit ball.
  have hinj : Set.InjOn h (ball (0 : ℂ) 1) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have hdiffAt : ∀ x ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ (fun z => h z - z) x := by
      intro x hx
      have hx3 : x ∈ ball (0 : ℂ) 3 := by
        rw [mem_ball_zero_iff] at hx ⊢
        linarith
      exact (hdiff.differentiableAt (isOpen_ball.mem_nhds hx3)).sub differentiableAt_id
    have key := Convex.norm_image_sub_le_of_norm_deriv_le hdiffAt hderiv
      (convex_ball 0 1) hz₁ hz₂
    have key2 : ‖z₁ - z₂‖ ≤ 1/4 * ‖z₂ - z₁‖ := by
      have e1 : z₁ - z₂ = (h z₂ - z₂) - (h z₁ - z₁) := by rw [heq]; ring
      rw [e1]
      exact key
    rw [norm_sub_rev z₂ z₁] at key2
    have hnn : (0 : ℝ) ≤ ‖z₁ - z₂‖ := norm_nonneg _
    have h0 : ‖z₁ - z₂‖ = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- (10) The derivative of the reading does not vanish on the unit ball.
  have hderiv_ne : ∀ a ∈ ball (0 : ℂ) 1, deriv h a ≠ 0 := by
    intro a ha hda0
    have ha3 : a ∈ ball (0 : ℂ) 3 := by
      rw [mem_ball_zero_iff] at ha ⊢
      linarith
    have hha : DifferentiableAt ℂ h a := hdiff.differentiableAt (isOpen_ball.mem_nhds ha3)
    have hsub2 : HasDerivAt (fun z => h z - z) (deriv h a - 1) a :=
      hha.hasDerivAt.sub (hasDerivAt_id' a)
    have hb := hderiv a ha
    rw [hsub2.deriv, hda0, zero_sub, norm_neg, norm_one] at hb
    norm_num at hb
  -- (11) The numerator carries the full degree, hence has degree ≥ 2.
  have hFinf : ¬ r.numReduced.natDegree < r.denReduced.natDegree := by
    intro hlt
    have hinf := hsmall ∞
    have e : r.toSphereMap ∞ = ((0 : ℂ) : ℂ̂) := by
      have e0 : r.toSphereMap ∞
          = if r.numReduced.natDegree < r.denReduced.natDegree then ((0 : ℂ) : ℂ̂)
            else if r.numReduced.natDegree = r.denReduced.natDegree then
              ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂)
            else ∞ := rfl
      rw [e0, if_pos hlt]
    rw [e, sphericalDist_coe_infty] at hinf
    norm_num [chordalDistInfty, Real.sqrt_one] at hinf
  have hnum2 : 2 ≤ r.numReduced.natDegree := by
    have e : r.degree = max r.numReduced.natDegree r.denReduced.natDegree := rfl
    have hle : r.denReduced.natDegree ≤ r.numReduced.natDegree := not_lt.mp hFinf
    have h2 := hdeg2
    rw [e, max_eq_left hle] at h2
    exact h2
  have hnum_ne : r.numReduced ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hnum2
    norm_num at hnum2
  -- (12) Every root of the numerator lies in the unit ball and is a zero of `h`.
  have hroots : ∀ a ∈ r.numReduced.roots, ‖a‖ < 1 ∧ h a = 0 := by
    intro a ha
    have haR : r.numReduced.eval a = 0 := (Polynomial.mem_roots hnum_ne).mp ha
    have hdenA : r.denReduced.eval a ≠ 0 :=
      (r.eval_ne_zero_or a).resolve_left (not_not_intro haR)
    have e : r.toSphereMap (a : ℂ̂) = ((0 : ℂ) : ℂ̂) := by
      have e0 : r.toSphereMap (a : ℂ̂)
          = if r.denReduced.eval a = 0 then ∞
            else ((r.numReduced.eval a / r.denReduced.eval a : ℂ) : ℂ̂) := rfl
      rw [e0, if_neg hdenA, haR, zero_div]
    have h1 := hsmall (a : ℂ̂)
    rw [e, sphericalDist_coe_coe] at h1
    have e2 : chordalDist 0 a = 2 * ‖a‖ / Real.sqrt (1 + ‖a‖ ^ 2) := by
      unfold chordalDist
      rw [zero_sub, norm_neg]
      norm_num [Real.sqrt_one]
    rw [e2] at h1
    have hsA : Real.sqrt (1 + ‖a‖ ^ 2) ≤ 1 + ‖a‖ := sqrt_le _ (norm_nonneg _)
    have hsA' : (1 : ℝ) ≤ Real.sqrt (1 + ‖a‖ ^ 2) := one_le_sqrt _
    rw [div_lt_iff₀ (lt_of_lt_of_le one_pos hsA')] at h1
    have ha1 : ‖a‖ < 1 := by linarith
    refine ⟨ha1, ?_⟩
    rw [hh]
    simp only [haR, zero_div]
  -- (13) The numerator has at least two roots with multiplicity.
  have hcard : 2 ≤ Multiset.card r.numReduced.roots := by
    have hsp : r.numReduced.roots.card = r.numReduced.natDegree :=
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits r.numReduced)
    rw [hsp]
    exact hnum2
  -- (14) All roots of the numerator are simple.
  have hsimple : ∀ a ∈ r.numReduced.roots, r.numReduced.roots.count a = 1 := by
    intro a ha
    have haR : r.numReduced.eval a = 0 := (Polynomial.mem_roots hnum_ne).mp ha
    have hpos : 0 < Polynomial.rootMultiplicity a r.numReduced :=
      (Polynomial.rootMultiplicity_pos hnum_ne).mpr haR
    by_contra hne
    rw [Polynomial.count_roots] at hne
    have h2 : 2 ≤ Polynomial.rootMultiplicity a r.numReduced := by omega
    have hd_ne : Polynomial.derivative r.numReduced ≠ 0 := by
      intro h0
      have hd0 := Polynomial.derivative_eq_zero.mp h0
      omega
    have hdmult := Polynomial.derivative_rootMultiplicity_of_root
      (p := r.numReduced) (t := a) haR
    have hdpos : 0 < Polynomial.rootMultiplicity a (Polynomial.derivative r.numReduced) := by
      omega
    have hdroot : (Polynomial.derivative r.numReduced).eval a = 0 :=
      (Polynomial.rootMultiplicity_pos hd_ne).mp hdpos
    have ha1 : ‖a‖ < 1 := (hroots a ha).1
    have hdenA : r.denReduced.eval a ≠ 0 :=
      (r.eval_ne_zero_or a).resolve_left (not_not_intro haR)
    have hquot : HasDerivAt (fun x => r.numReduced.eval x / r.denReduced.eval x)
        ((Polynomial.eval a (Polynomial.derivative r.numReduced) * r.denReduced.eval a
          - r.numReduced.eval a * Polynomial.eval a (Polynomial.derivative r.denReduced))
          / r.denReduced.eval a ^ 2) a :=
      (r.numReduced.hasDerivAt a).div (r.denReduced.hasDerivAt a) hdenA
    rw [hdroot, haR] at hquot
    simp only [zero_mul, sub_zero, zero_div] at hquot
    have hda0 : deriv h a = 0 := by
      rw [hh]
      exact hquot.deriv
    exact hderiv_ne a (mem_ball_zero_iff.mpr ha1) hda0
  -- (15) Extract two distinct roots.
  have hne0 : r.numReduced.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne0
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have htne : t ≠ 0 := by
    intro h0
    rw [ht, h0, Multiset.card_cons, Multiset.card_zero] at hcard
    omega
  obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero htne
  have hbroots : b ∈ r.numReduced.roots := by
    rw [ht]
    exact Multiset.mem_cons_of_mem hb
  have hanott : a ∉ t := by
    intro hat
    have hc1 := hsimple a ha
    rw [ht, Multiset.count_cons_self] at hc1
    have hc0 : Multiset.count a t = 0 := by omega
    exact (Multiset.count_eq_zero.mp hc0) hat
  have hab : a ≠ b := by
    intro he
    rw [← he] at hb
    exact hanott hb
  -- (16) Contradiction with injectivity.
  obtain ⟨ha1, ha0⟩ := hroots a ha
  obtain ⟨hb1, hb0⟩ := hroots b hbroots
  have hfinal : a = b := hinj (mem_ball_zero_iff.mpr ha1) (mem_ball_zero_iff.mpr hb1)
    (by rw [ha0, hb0])
  exact hab hfinal

/-- Under global normality of the iterate family, either iterates come
uniformly arbitrarily close to the identity, or some iterate is not
surjective. The two branches correspond to the uniform limit of a
convergent subsequence being surjective or not. -/
theorem exists_iterate_near_id_or_not_surjective {f : ℂ̂ → ℂ̂}
    (hf : Continuous f)
    (hN : IsNormal (Set.range fun n : ℕ => f^[n]) Set.univ) :
    (∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 1 ≤ m ∧
        ∀ z : ℂ̂, sphericalDist (f^[m] z) z < ε) ∨
      (∃ m : ℕ, 1 ≤ m ∧ ¬ Function.Surjective (f^[m])) := by
  obtain ⟨φ, hφ, g, hTLU⟩ := hN fun n => ⟨f^[n], n, rfl⟩
  have hTLU' : TendstoLocallyUniformlyOn (fun j => f^[φ j]) g atTop Set.univ := hTLU
  have hunif : TendstoUniformlyOn (fun j => f^[φ j]) g atTop Set.univ :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hTLU' Set.univ
      subset_rfl isCompact_univ
  have hg_cont : Continuous g := by
    rw [← continuousOn_univ]
    exact hunif.continuousOn
      (Frequently.of_forall fun j => (hf.iterate (φ j)).continuousOn)
  by_cases hsurj : Function.Surjective g
  · refine Or.inl fun ε hε => ?_
    obtain ⟨δ, hδ, hequi⟩ := hN.uniformEquicontinuous
      (fun F hF => by obtain ⟨n, rfl⟩ := hF; exact hf.iterate n) (ε / 3) (by positivity)
    have hmin : 0 < min δ (ε / 3) := lt_min hδ (by positivity)
    obtain ⟨N, hP⟩ := eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp hunif (min δ (ε / 3)) hmin)
    have hφN : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
    set m := φ (N + 1) - φ N with hm_def
    have hm1 : 1 ≤ m := by omega
    refine ⟨m, hm1, fun z => ?_⟩
    change dist (f^[m] z) z < ε
    obtain ⟨x, rfl⟩ := hsurj z
    have h1 : dist (g x) (f^[φ N] x) < min δ (ε / 3) := hP N le_rfl x (Set.mem_univ x)
    have h2 : dist (g x) (f^[φ (N + 1)] x) < min δ (ε / 3) :=
      hP (N + 1) (Nat.le_succ N) x (Set.mem_univ x)
    have hterm1 : dist (f^[m] (g x)) (f^[m] (f^[φ N] x)) < ε / 3 :=
      hequi (f^[m]) ⟨m, rfl⟩ (g x) (f^[φ N] x) (lt_of_lt_of_le h1 (min_le_left _ _))
    have hsum : m + φ N = φ (N + 1) := by omega
    have hiter : f^[m] (f^[φ N] x) = f^[φ (N + 1)] x := by
      rw [← Function.iterate_add_apply, hsum]
    have hterm2 : dist (f^[m] (f^[φ N] x)) (g x) < ε / 3 := by
      rw [hiter, dist_comm]
      exact lt_of_lt_of_le h2 (min_le_right _ _)
    calc dist (f^[m] (g x)) (g x)
        ≤ dist (f^[m] (g x)) (f^[m] (f^[φ N] x)) + dist (f^[m] (f^[φ N] x)) (g x) :=
          dist_triangle _ _ _
      _ < ε / 3 + ε / 3 := add_lt_add hterm1 hterm2
      _ < ε := by linarith
  · refine Or.inr ?_
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∉ Set.range g := by
      by_contra h
      push Not at h
      exact hsurj fun w => h w
    have hclosed : IsClosed (Set.range g) := (isCompact_range hg_cont).isClosed
    have hη : 0 < infDist w₀ (Set.range g) :=
      (hclosed.notMem_iff_infDist_pos (Set.range_nonempty g)).mp hw₀
    obtain ⟨N', hP⟩ := eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp hunif (infDist w₀ (Set.range g)) hη)
    refine ⟨φ (max N' 1), le_trans (le_max_right N' 1) hφ.le_apply, fun hs => ?_⟩
    obtain ⟨z, hz⟩ := hs w₀
    have h1 : infDist w₀ (Set.range g) ≤ dist w₀ (g z) :=
      infDist_le_dist_of_mem (Set.mem_range_self z)
    have h2 : dist (g z) (f^[φ (max N' 1)] z) < infDist w₀ (Set.range g) :=
      hP (max N' 1) (le_max_left N' 1) z (Set.mem_univ z)
    rw [hz, dist_comm] at h2
    exact absurd h2 (not_lt.mpr h1)

/-- **The Julia set of a rational map of degree at least two is
nonempty.** -/
theorem juliaSet_nonempty {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) : (JuliaSet f).Nonempty := by
  by_contra hne
  have hJ : JuliaSet f = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hFatU : FatouSet f = Set.univ := by
    rw [← compl_juliaSet, hJ, Set.compl_empty]
  have hFat : ∀ z : ℂ̂, IsNormalAt (Set.range fun n : ℕ => f^[n]) z := fun z => by
    have hz : z ∈ FatouSet f := hFatU ▸ Set.mem_univ z
    exact hz
  have hN := isNormal_univ_of_forall_isNormalAt hFat
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hdpos : 0 < degreeOfRational f := lt_of_lt_of_le one_pos hd1
  rcases exists_iterate_near_id_or_not_surjective hf.continuous hN with
    hclose | ⟨m, _, hns⟩
  · obtain ⟨ε, hε, hsep⟩ := exists_id_separation
    obtain ⟨m, hm, hlt⟩ := hclose ε hε
    have hdm : 2 ≤ degreeOfRational (f^[m]) := by
      rw [degreeOfRational_iterate hf hd1 m]
      calc 2 ≤ degreeOfRational f := hd
        _ = degreeOfRational f ^ 1 := (pow_one _).symm
        _ ≤ degreeOfRational f ^ m := Nat.pow_le_pow_right hdpos hm
    obtain ⟨z, hz⟩ := hsep (f^[m]) (hf.iterate hd1 m) hdm
    exact absurd (hlt z) (not_lt.mpr hz)
  · have hdm1 : 1 ≤ degreeOfRational (f^[m]) := by
      rw [degreeOfRational_iterate hf hd1 m]
      exact Nat.one_le_pow m _ hdpos
    exact hns ((hf.iterate hd1 m).surjective fun c => (hf.iterate hd1 m).ne_const hdm1 c)

end NoWanderingDomains
