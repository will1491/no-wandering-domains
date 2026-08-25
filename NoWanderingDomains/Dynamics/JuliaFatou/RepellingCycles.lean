/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.JuliaFatou.Perfect

/-!
# Repelling cycles lie in the Julia set

This file introduces the multiplier of a fixed point of a sphere self-map
(read in the chart adapted to the point) and the predicate
`IsRepellingPeriodicPt`, and proves the containment half of the
density-of-repelling-cycles theorem:

* `mem_juliaSet_of_isRepellingPeriodicPt` — a repelling periodic point lies
  in the Julia set: near a repelling fixed point of `g = f^[n]` the chart
  reading expands distances by a factor `μ > 1` (the difference quotient
  eventually exceeds `μ` in norm), so iterates of points arbitrarily close
  to the cycle escape a fixed spherical distance — contradicting the
  equicontinuity at the point that normality would force.
* `closure_setOf_isRepellingPeriodicPt_subset_juliaSet` — hence the closure
  of the set of repelling periodic points is contained in the Julia set.

The reverse containment — the Julia set is contained in the closure of the
repelling periodic points — is the density theorem of Fatou and Julia; its
two ingredients (periodic points are dense in the Julia set via local
inverse branches and the cross-ratio Montel argument, and all but finitely
many cycles are repelling) are not formalized here.
-/

open OnePoint Polynomial Filter Topology Metric Function

namespace NoWanderingDomains

/-- The *multiplier* of a sphere self-map at a point, read in the chart
adapted to the point: the derivative of the finite-chart reading at a
finite point, and of the inversion-chart reading at `∞`. For a fixed point
of `f` this is the classical multiplier; at other points the value is a
junk chart artifact and no downstream statement consumes it. -/
noncomputable def multiplier (f : ℂ̂ → ℂ̂) (p : ℂ̂) : ℂ :=
  match p with
  | (p₀ : ℂ) => deriv (fun w : ℂ => chartFiniteMap (f ((w : ℂ̂)))) p₀
  | ∞ => deriv (fun w : ℂ => chartInftyMap (f (inversionGL • (w : ℂ̂)))) 0

/-- A point `p` is a *repelling periodic point* of `f` with period `n` if
`n` is positive, `p` is periodic with period `n`, and the multiplier of
the return map `f^[n]` at `p` has norm greater than one. -/
def IsRepellingPeriodicPt (f : ℂ̂ → ℂ̂) (n : ℕ) (p : ℂ̂) : Prop :=
  0 < n ∧ Function.IsPeriodicPt f n p ∧ 1 < ‖multiplier (f^[n]) p‖

/-- The inversion is a spherical isometry: `z ↦ 1/z` is a rotation of the
Riemann sphere by `π` about the real axis, so it preserves the chordal
distance. -/
theorem sphericalDist_inversionGL_smul (x y : ℂ̂) :
    sphericalDist (inversionGL • x) (inversionGL • y) = sphericalDist x y := by
  have key : ∀ r : ℝ, 0 < r →
      Real.sqrt (1 + r⁻¹ ^ 2) = Real.sqrt (1 + r ^ 2) / r := by
    intro r hr
    have h1 : (1 + r⁻¹ ^ 2 : ℝ) = (1 + r ^ 2) / r ^ 2 := by
      field_simp
      ring
    rw [h1, Real.sqrt_div (by positivity) _, Real.sqrt_sq hr.le]
  have h0 : Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 1 := by simp
  have hIC : ∀ c : ℂ, sphericalDist (∞ : ℂ̂) (c : ℂ̂) = chordalDistInfty c :=
    fun _ => rfl
  have hII : sphericalDist (∞ : ℂ̂) (∞ : ℂ̂) = 0 := rfl
  have hcc : ∀ a b : ℂ,
      sphericalDist (inversionGL • (a : ℂ̂)) (inversionGL • (b : ℂ̂)) =
        sphericalDist (a : ℂ̂) (b : ℂ̂) := by
    intro a b
    rw [inversionGL_smul_coe a, inversionGL_smul_coe b, sphericalDist_coe_coe]
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · subst ha; subst hb
      rw [if_pos rfl, hII]
      simp [chordalDist]
    · subst ha
      have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
      have hsb : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_pos rfl, if_neg hb, hIC]
      simp only [chordalDistInfty, chordalDist, norm_inv, zero_sub, norm_neg]
      rw [key ‖b‖ hnb, h0, one_mul]
      field_simp
    · subst hb
      have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
      have hsa : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_neg ha, if_pos rfl, sphericalDist_coe_infty]
      simp only [chordalDistInfty, chordalDist, norm_inv, sub_zero]
      rw [key ‖a‖ hna, h0, mul_one]
      field_simp
    · have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
      have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
      have hsa : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hsb : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_neg ha, if_neg hb, sphericalDist_coe_coe]
      simp only [chordalDist, norm_inv]
      rw [inv_sub_inv ha hb, norm_div, norm_mul, norm_sub_rev b a,
        key ‖a‖ hna, key ‖b‖ hnb]
      field_simp
  have hci : ∀ a : ℂ,
      sphericalDist (inversionGL • (a : ℂ̂)) (inversionGL • (∞ : ℂ̂)) =
        sphericalDist (a : ℂ̂) (∞ : ℂ̂) := by
    intro a
    rw [inversionGL_smul_infty, inversionGL_smul_coe a, sphericalDist_coe_infty]
    by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl]
      exact hIC 0
    · have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
      have hsa : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_neg ha, sphericalDist_coe_coe]
      simp only [chordalDist, chordalDistInfty, norm_inv, sub_zero]
      rw [key ‖a‖ hna, h0, mul_one]
      field_simp
  match x, y with
  | OnePoint.some a, OnePoint.some b => exact hcc a b
  | OnePoint.some a, ∞ => exact hci a
  | ∞, OnePoint.some b =>
      rw [sphericalDist_comm (inversionGL • (∞ : ℂ̂)), sphericalDist_comm (∞ : ℂ̂)]
      exact hci b
  | ∞, ∞ =>
      rw [inversionGL_smul_infty, hII, sphericalDist_coe_coe]
      simp [chordalDist]

/-- **Repelling periodic points lie in the Julia set.** Near a repelling
fixed point of the return map, the chart reading expands by a factor
`μ > 1`, so orbits of arbitrarily nearby points escape a fixed spherical
distance from the cycle — incompatible with the equicontinuity at the
point that normality of the iterate family would force. -/
theorem mem_juliaSet_of_isRepellingPeriodicPt {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f) {n : ℕ} {p : ℂ̂}
    (h : IsRepellingPeriodicPt f n p) : p ∈ JuliaSet f := by
  classical
  obtain ⟨hn, hper, hmul⟩ := h
  rw [← juliaSet_iterate hf.continuous hn]
  set g := f^[n] with hgdef
  have hg_rat : IsRational g := hf.iterate hd n
  have hg_cont : Continuous g := hf.continuous.iterate n
  have hg_fix : g p = p := hper
  by_contra hJ
  have hFat : p ∈ FatouSet g := not_not.mp hJ
  have hNA : IsNormalAt (Set.range fun k : ℕ => g^[k]) p := hFat
  have hmemc : ∀ F ∈ Set.range fun k : ℕ => g^[k], Continuous F := by
    rintro F ⟨k, rfl⟩
    exact hg_cont.iterate k
  have hequi := hNA.equicontinuousAt hmemc
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
  cases p with
  | coe p₀ =>
    -- ===================== FINITE FIXED POINT =====================
    -- The finite-chart reading of `g` near the fixed point.
    obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ,
        φ = fun w : ℂ => chartFiniteMap (g ((w : ℂ̂))) := ⟨_, rfl⟩
    have hU'open : IsOpen {w : ℂ | g ((w : ℂ̂)) ≠ ∞} :=
      isOpen_compl_singleton.preimage (hg_cont.comp OnePoint.continuous_coe)
    have hp₀U' : p₀ ∈ {w : ℂ | g ((w : ℂ̂)) ≠ ∞} := by
      change g ((p₀ : ℂ̂)) ≠ ∞
      rw [hg_fix]
      exact OnePoint.coe_ne_infty p₀
    have hφdiff : DifferentiableOn ℂ φ {w : ℂ | g ((w : ℂ̂)) ≠ ∞} := by
      simp only [hφdef]
      exact (hg_rat.sphereHolomorphicOn_comp_coe hU'open).differentiableOn_chartFiniteMap
        fun z hz => hz
    have hread : ∀ v : ℂ, g ((v : ℂ̂)) ≠ ∞ → g ((v : ℂ̂)) = ((φ v : ℂ) : ℂ̂) := by
      intro v hv
      cases hgv : g ((v : ℂ̂)) with
      | infty => exact absurd hgv hv
      | coe x =>
        simp only [hφdef, hgv]
        rfl
    have hφp₀ : φ p₀ = p₀ := by
      simp only [hφdef]
      rw [hg_fix]
      rfl
    -- The multiplier is the derivative of the reading.
    have hdiffAt : DifferentiableAt ℂ φ p₀ :=
      hφdiff.differentiableAt (hU'open.mem_nhds hp₀U')
    have hderiv : HasDerivAt φ (deriv φ p₀) p₀ := hdiffAt.hasDerivAt
    have hlam : 1 < ‖deriv φ p₀‖ := by
      have h1 : multiplier g ((p₀ : ℂ̂)) = deriv φ p₀ := by
        simp only [hφdef]
        rfl
      rw [← h1]
      exact hmul
    obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = (1 + ‖deriv φ p₀‖) / 2 := ⟨_, rfl⟩
    have hμ1 : 1 < μ := by rw [hμdef]; linarith
    have hμlt : μ < ‖deriv φ p₀‖ := by rw [hμdef]; linarith
    -- The difference quotient eventually exceeds `μ` in norm.
    have hslope_ev : ∀ᶠ z in 𝓝[≠] p₀, μ < ‖slope φ p₀ z‖ :=
      (hasDerivAt_iff_tendsto_slope.mp hderiv).norm.eventually (eventually_gt_nhds hμlt)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hslope_ev
    obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hslope_ev
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ := Metric.isOpen_iff.mp hU'open p₀ hp₀U'
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (ρ₁ / 2) (ρ₂ / 2) := ⟨_, rfl⟩
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min (by linarith) (by linarith)
    have hρ1 : ρ < ρ₁ := by
      rw [hρdef]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hρ2 : ρ < ρ₂ := by
      rw [hρdef]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    -- The closed `ρ`-ball avoids the pole set of `g`.
    have hballU' : ∀ v : ℂ, ‖v - p₀‖ ≤ ρ → g ((v : ℂ̂)) ≠ ∞ := by
      intro v hv
      exact hρ₂sub (mem_ball_iff_norm.mpr (lt_of_le_of_lt hv hρ2))
    -- One-step expansion on the closed `ρ`-ball.
    have hexpand : ∀ v : ℂ, v ≠ p₀ → ‖v - p₀‖ ≤ ρ → μ * ‖v - p₀‖ ≤ ‖φ v - p₀‖ := by
      intro v hv hvρ
      have hdist : dist v p₀ < ρ₁ := by
        rw [dist_eq_norm]
        exact lt_of_le_of_lt hvρ hρ1
      have hs := hρ₁ hdist hv
      rw [slope_def_field, hφp₀, norm_div] at hs
      have hvpos : (0 : ℝ) < ‖v - p₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
      rw [lt_div_iff₀ hvpos] at hs
      linarith
    -- A point outside the `ρ`-ball is a fixed spherical distance from `p₀`.
    have hc₀ : (0 : ℝ) < 1 + ‖p₀‖ := by positivity
    have hc₁ : (0 : ℝ) < 1 + ‖p₀‖ + ρ := by linarith
    obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ,
        ε₀ = 2 * ρ / ((1 + ‖p₀‖ + ρ) * (1 + ‖p₀‖)) := ⟨_, rfl⟩
    have hε₀pos : 0 < ε₀ := by
      rw [hε₀def]
      exact div_pos (by linarith) (mul_pos hc₁ hc₀)
    have hexit : ∀ v : ℂ, ρ < ‖v - p₀‖ →
        ε₀ ≤ sphericalDist ((v : ℂ̂)) ((p₀ : ℂ̂)) := by
      intro v hv
      have ht0 : (0 : ℝ) < ‖v - p₀‖ := lt_trans hρpos hv
      have hs1 : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 1 + ‖v‖ := sqrt_le _ (norm_nonneg _)
      have hs2 : Real.sqrt (1 + ‖p₀‖ ^ 2) ≤ 1 + ‖p₀‖ := sqrt_le _ (norm_nonneg _)
      have hs1' : (1 : ℝ) ≤ Real.sqrt (1 + ‖v‖ ^ 2) := one_le_sqrt _
      have hs2' : (1 : ℝ) ≤ Real.sqrt (1 + ‖p₀‖ ^ 2) := one_le_sqrt _
      have hvnorm : ‖v‖ ≤ ‖p₀‖ + ‖v - p₀‖ := by
        have h1 : v = p₀ + (v - p₀) := by ring
        calc ‖v‖ = ‖p₀ + (v - p₀)‖ := by rw [← h1]
          _ ≤ ‖p₀‖ + ‖v - p₀‖ := norm_add_le _ _
      have hDle : Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖p₀‖ ^ 2)
          ≤ (1 + ‖p₀‖ + ‖v - p₀‖) * (1 + ‖p₀‖) := by
        have h1 : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 1 + ‖p₀‖ + ‖v - p₀‖ := by linarith
        exact mul_le_mul h1 hs2 (Real.sqrt_nonneg _) (by linarith)
      have hstep1 : 2 * ‖v - p₀‖ / ((1 + ‖p₀‖ + ‖v - p₀‖) * (1 + ‖p₀‖))
          ≤ 2 * ‖v - p₀‖ / (Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖p₀‖ ^ 2)) :=
        div_le_div_of_nonneg_left (by linarith)
          (lt_of_lt_of_le one_pos (one_le_mul_of_one_le_of_one_le hs1' hs2')) hDle
      have hstep2 : ε₀ ≤ 2 * ‖v - p₀‖ / ((1 + ‖p₀‖ + ‖v - p₀‖) * (1 + ‖p₀‖)) := by
        rw [hε₀def, div_le_div_iff₀ (mul_pos hc₁ hc₀) (mul_pos (by linarith) hc₀)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hv.le) (mul_pos hc₀ hc₀).le]
      have hfin : sphericalDist ((v : ℂ̂)) ((p₀ : ℂ̂))
          = 2 * ‖v - p₀‖ / (Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖p₀‖ ^ 2)) := rfl
      rw [hfin]
      exact le_trans hstep2 hstep1
    -- Equicontinuity at the fixed point, and the test point.
    obtain ⟨δ, hδpos, hδ⟩ := hequi ε₀ hε₀pos
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min ρ (δ / 4) := ⟨_, rfl⟩
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min hρpos (by linarith)
    have hηρ : η ≤ ρ := by rw [hηdef]; exact min_le_left _ _
    have hηδ : η ≤ δ / 4 := by rw [hηdef]; exact min_le_right _ _
    obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = p₀ + (η : ℂ) := ⟨_, rfl⟩
    have hwsub : w - p₀ = (η : ℂ) := by rw [hwdef]; ring
    have hwnorm : ‖w - p₀‖ = η := by
      rw [hwsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    have hwpos : (0 : ℝ) < ‖w - p₀‖ := by rw [hwnorm]; exact hηpos
    -- The orbit of the chart reading expands geometrically while in the ball.
    have hgrow : ∀ k : ℕ, (∀ i, i < k → ‖φ^[i] w - p₀‖ ≤ ρ) →
        g^[k] ((w : ℂ̂)) = ((φ^[k] w : ℂ) : ℂ̂) ∧
          μ ^ k * ‖w - p₀‖ ≤ ‖φ^[k] w - p₀‖ := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨rfl, le_of_eq ?_⟩
        rw [Function.iterate_zero_apply, pow_zero, one_mul]
      | succ k ih =>
        intro hball
        obtain ⟨hid, hgk⟩ := ih fun i hi => hball i (by omega)
        have hvρ : ‖φ^[k] w - p₀‖ ≤ ρ := hball k (by omega)
        have hvne : φ^[k] w ≠ p₀ := by
          intro h0
          rw [h0, sub_self, norm_zero] at hgk
          have h2 := mul_pos (pow_pos (lt_trans one_pos hμ1) k) hwpos
          linarith
        constructor
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hid]
          exact hread _ (hballU' _ hvρ)
        · rw [Function.iterate_succ_apply']
          calc μ ^ (k + 1) * ‖w - p₀‖ = μ * (μ ^ k * ‖w - p₀‖) := by ring
            _ ≤ μ * ‖φ^[k] w - p₀‖ :=
                mul_le_mul_of_nonneg_left hgk (by linarith)
            _ ≤ ‖φ (φ^[k] w) - p₀‖ := hexpand _ hvne hvρ
    -- The orbit must leave the ball: `μ ^ k → ∞`.
    have hex : ∃ k : ℕ, ρ < ‖φ^[k] w - p₀‖ := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ k : ℕ, μ ^ k * ‖w - p₀‖ ≤ ρ := fun k =>
        le_trans (hgrow k fun i _ => hcon i).2 (hcon k)
      obtain ⟨k, hk⟩ :=
        ((tendsto_pow_atTop_atTop_of_one_lt hμ1).eventually_ge_atTop
          (ρ / ‖w - p₀‖ + 1)).exists
      have h1 : (ρ / ‖w - p₀‖ + 1) * ‖w - p₀‖ ≤ μ ^ k * ‖w - p₀‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hwpos), one_mul] at h1
      linarith [hall k]
    -- The first exit index.
    obtain ⟨k₀, hexit_k₀, hmin⟩ : ∃ k₀ : ℕ, ρ < ‖φ^[k₀] w - p₀‖ ∧
        ∀ i, i < k₀ → ‖φ^[i] w - p₀‖ ≤ ρ :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_lt.mp (Nat.find_min hex hi)⟩
    obtain ⟨hid, -⟩ := hgrow k₀ hmin
    -- The contradiction with equicontinuity.
    have hfix_iter : g^[k₀] ((p₀ : ℂ̂)) = ((p₀ : ℂ̂)) :=
      Function.iterate_fixed hg_fix k₀
    have hdistw : dist ((w : ℂ̂)) ((p₀ : ℂ̂)) < δ := by
      change sphericalDist ((w : ℂ̂)) ((p₀ : ℂ̂)) < δ
      calc sphericalDist ((w : ℂ̂)) ((p₀ : ℂ̂)) ≤ 2 * ‖w - p₀‖ :=
            sphericalDist_coe_le_norm_sub w p₀
        _ = 2 * η := by rw [hwnorm]
        _ < δ := by linarith
    have hcontra := hδ (g^[k₀]) ⟨k₀, rfl⟩ ((w : ℂ̂)) hdistw
    rw [hid, hfix_iter] at hcontra
    have hge := hexit (φ^[k₀] w) hexit_k₀
    change sphericalDist ((φ^[k₀] w : ℂ) : ℂ̂) ((p₀ : ℂ̂)) < ε₀ at hcontra
    linarith
  | infty =>
    -- ===================== FIXED POINT AT `∞` =====================
    -- The inversion-chart reading of `g` near the fixed point.
    obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ,
        φ = fun w : ℂ => chartInftyMap (g (inversionGL • (w : ℂ̂))) := ⟨_, rfl⟩
    have hinv0 : inversionGL • (((0 : ℂ) : ℂ̂)) = ∞ := by
      rw [inversionGL_smul_coe]
      exact if_pos rfl
    have hU'open : IsOpen {w : ℂ | g (inversionGL • ((w : ℂ̂))) ≠ ((0 : ℂ) : ℂ̂)} :=
      isOpen_compl_singleton.preimage
        (hg_cont.comp ((continuous_gl_smul inversionGL).comp OnePoint.continuous_coe))
    have h0U' : (0 : ℂ) ∈ {w : ℂ | g (inversionGL • ((w : ℂ̂))) ≠ ((0 : ℂ) : ℂ̂)} := by
      change g (inversionGL • (((0 : ℂ) : ℂ̂))) ≠ ((0 : ℂ) : ℂ̂)
      rw [hinv0, hg_fix]
      exact OnePoint.infty_ne_coe 0
    -- Differentiability of the reading on the zero-free locus.
    have hφdiff : DifferentiableOn ℂ φ
        {w : ℂ | g (inversionGL • ((w : ℂ̂))) ≠ ((0 : ℂ) : ℂ̂)} := by
      simp only [hφdef]
      refine differentiableOn_of_locally_differentiableOn fun z hz => ?_
      obtain ⟨V, hVo, hzV, hVU, hcase⟩ :=
        (hg_rat.sphereHolomorphicOn_comp_inversionGL hU'open) z hz
      refine ⟨V, hVo, hzV, ?_⟩
      rcases hcase with ⟨hne, hdiff⟩ | ⟨-, hdiff⟩
      · -- Finite-chart branch: the infinity-chart reading is its reciprocal.
        have hkey : ∀ v ∈ V, chartInftyMap (g (inversionGL • ((v : ℂ̂))))
            = (chartFiniteMap (g (inversionGL • ((v : ℂ̂)))))⁻¹
            ∧ chartFiniteMap (g (inversionGL • ((v : ℂ̂)))) ≠ 0 := by
          intro v hv
          cases hgv : g (inversionGL • ((v : ℂ̂))) with
          | infty => exact absurd hgv (hne v hv)
          | coe x =>
            have hx0 : x ≠ 0 := by
              rintro rfl
              exact (hVU hv) hgv
            exact ⟨rfl, hx0⟩
        have hinvdiff : DifferentiableOn ℂ
            (fun v : ℂ => chartFiniteMap (g (inversionGL • ((v : ℂ̂)))))⁻¹ V :=
          hdiff.inv fun v hv => (hkey v hv).2
        exact (hinvdiff.mono Set.inter_subset_right).congr fun v hv => (hkey v hv.2).1
      · exact hdiff.mono Set.inter_subset_right
    have hread : ∀ v : ℂ, g (inversionGL • ((v : ℂ̂))) ≠ ((0 : ℂ) : ℂ̂) →
        g (inversionGL • ((v : ℂ̂))) = inversionGL • ((φ v : ℂ) : ℂ̂) := by
      intro v hv
      simp only [hφdef]
      exact (inversionGL_smul_coe_chartInftyMap hv).symm
    have hφ0 : φ 0 = 0 := by
      simp only [hφdef]
      rw [hinv0, hg_fix]
      rfl
    -- The multiplier is the derivative of the reading.
    have hdiffAt : DifferentiableAt ℂ φ 0 :=
      hφdiff.differentiableAt (hU'open.mem_nhds h0U')
    have hderiv : HasDerivAt φ (deriv φ 0) 0 := hdiffAt.hasDerivAt
    have hlam : 1 < ‖deriv φ 0‖ := by
      have h1 : multiplier g ∞ = deriv φ 0 := by
        simp only [hφdef]
        rfl
      rw [← h1]
      exact hmul
    obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = (1 + ‖deriv φ 0‖) / 2 := ⟨_, rfl⟩
    have hμ1 : 1 < μ := by rw [hμdef]; linarith
    have hμlt : μ < ‖deriv φ 0‖ := by rw [hμdef]; linarith
    -- The difference quotient eventually exceeds `μ` in norm.
    have hslope_ev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), μ < ‖slope φ 0 z‖ :=
      (hasDerivAt_iff_tendsto_slope.mp hderiv).norm.eventually (eventually_gt_nhds hμlt)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hslope_ev
    obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hslope_ev
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ := Metric.isOpen_iff.mp hU'open 0 h0U'
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (ρ₁ / 2) (ρ₂ / 2) := ⟨_, rfl⟩
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min (by linarith) (by linarith)
    have hρ1 : ρ < ρ₁ := by
      rw [hρdef]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hρ2 : ρ < ρ₂ := by
      rw [hρdef]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    -- The closed `ρ`-ball avoids the zero set of `g ∘ inversion`.
    have hballU' : ∀ v : ℂ, ‖v - 0‖ ≤ ρ →
        g (inversionGL • ((v : ℂ̂))) ≠ ((0 : ℂ) : ℂ̂) := by
      intro v hv
      exact hρ₂sub (mem_ball_iff_norm.mpr (lt_of_le_of_lt hv hρ2))
    -- One-step expansion on the closed `ρ`-ball.
    have hexpand : ∀ v : ℂ, v ≠ 0 → ‖v - 0‖ ≤ ρ → μ * ‖v - 0‖ ≤ ‖φ v - 0‖ := by
      intro v hv hvρ
      have hdist : dist v 0 < ρ₁ := by
        rw [dist_eq_norm]
        exact lt_of_le_of_lt hvρ hρ1
      have hs := hρ₁ hdist hv
      rw [slope_def_field, hφ0, norm_div] at hs
      have hvpos : (0 : ℝ) < ‖v - 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
      rw [lt_div_iff₀ hvpos] at hs
      linarith
    -- A point outside the `ρ`-ball is a fixed spherical distance from `0`.
    have hc₀ : (0 : ℝ) < 1 + ‖(0 : ℂ)‖ := by positivity
    have hc₁ : (0 : ℝ) < 1 + ‖(0 : ℂ)‖ + ρ := by linarith
    obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ,
        ε₀ = 2 * ρ / ((1 + ‖(0 : ℂ)‖ + ρ) * (1 + ‖(0 : ℂ)‖)) := ⟨_, rfl⟩
    have hε₀pos : 0 < ε₀ := by
      rw [hε₀def]
      exact div_pos (by linarith) (mul_pos hc₁ hc₀)
    have hexit : ∀ v : ℂ, ρ < ‖v - 0‖ →
        ε₀ ≤ sphericalDist ((v : ℂ̂)) (((0 : ℂ) : ℂ̂)) := by
      intro v hv
      have ht0 : (0 : ℝ) < ‖v - 0‖ := lt_trans hρpos hv
      have hs1 : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 1 + ‖v‖ := sqrt_le _ (norm_nonneg _)
      have hs2 : Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) ≤ 1 + ‖(0 : ℂ)‖ :=
        sqrt_le _ (norm_nonneg _)
      have hs1' : (1 : ℝ) ≤ Real.sqrt (1 + ‖v‖ ^ 2) := one_le_sqrt _
      have hs2' : (1 : ℝ) ≤ Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) := one_le_sqrt _
      have hvnorm : ‖v‖ ≤ ‖(0 : ℂ)‖ + ‖v - 0‖ := by
        have h1 : v = 0 + (v - 0) := by ring
        calc ‖v‖ = ‖(0 : ℂ) + (v - 0)‖ := by rw [← h1]
          _ ≤ ‖(0 : ℂ)‖ + ‖v - 0‖ := norm_add_le _ _
      have hDle : Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2)
          ≤ (1 + ‖(0 : ℂ)‖ + ‖v - 0‖) * (1 + ‖(0 : ℂ)‖) := by
        have h1 : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 1 + ‖(0 : ℂ)‖ + ‖v - 0‖ := by linarith
        exact mul_le_mul h1 hs2 (Real.sqrt_nonneg _) (by linarith)
      have hstep1 : 2 * ‖v - 0‖ / ((1 + ‖(0 : ℂ)‖ + ‖v - 0‖) * (1 + ‖(0 : ℂ)‖))
          ≤ 2 * ‖v - 0‖ / (Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2)) :=
        div_le_div_of_nonneg_left (by linarith)
          (lt_of_lt_of_le one_pos (one_le_mul_of_one_le_of_one_le hs1' hs2')) hDle
      have hstep2 : ε₀ ≤ 2 * ‖v - 0‖ / ((1 + ‖(0 : ℂ)‖ + ‖v - 0‖) * (1 + ‖(0 : ℂ)‖)) := by
        rw [hε₀def, div_le_div_iff₀ (mul_pos hc₁ hc₀) (mul_pos (by linarith) hc₀)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hv.le) (mul_pos hc₀ hc₀).le]
      have hfin : sphericalDist ((v : ℂ̂)) (((0 : ℂ) : ℂ̂))
          = 2 * ‖v - 0‖ / (Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2)) := rfl
      rw [hfin]
      exact le_trans hstep2 hstep1
    -- Equicontinuity at `∞`, and the test point near `0` in the chart.
    obtain ⟨δ, hδpos, hδ⟩ := hequi ε₀ hε₀pos
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min ρ (δ / 4) := ⟨_, rfl⟩
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min hρpos (by linarith)
    have hηρ : η ≤ ρ := by rw [hηdef]; exact min_le_left _ _
    have hηδ : η ≤ δ / 4 := by rw [hηdef]; exact min_le_right _ _
    obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = 0 + (η : ℂ) := ⟨_, rfl⟩
    have hwsub : w - 0 = (η : ℂ) := by rw [hwdef]; ring
    have hwnorm : ‖w - 0‖ = η := by
      rw [hwsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    have hwpos : (0 : ℝ) < ‖w - 0‖ := by rw [hwnorm]; exact hηpos
    -- The orbit of the chart reading expands geometrically while in the ball.
    have hgrow : ∀ k : ℕ, (∀ i, i < k → ‖φ^[i] w - 0‖ ≤ ρ) →
        g^[k] (inversionGL • ((w : ℂ̂))) = inversionGL • ((φ^[k] w : ℂ) : ℂ̂) ∧
          μ ^ k * ‖w - 0‖ ≤ ‖φ^[k] w - 0‖ := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨rfl, le_of_eq ?_⟩
        rw [Function.iterate_zero_apply, pow_zero, one_mul]
      | succ k ih =>
        intro hball
        obtain ⟨hid, hgk⟩ := ih fun i hi => hball i (by omega)
        have hvρ : ‖φ^[k] w - 0‖ ≤ ρ := hball k (by omega)
        have hvne : φ^[k] w ≠ 0 := by
          intro h0
          rw [h0, sub_self, norm_zero] at hgk
          have h2 := mul_pos (pow_pos (lt_trans one_pos hμ1) k) hwpos
          linarith
        constructor
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hid]
          exact hread _ (hballU' _ hvρ)
        · rw [Function.iterate_succ_apply']
          calc μ ^ (k + 1) * ‖w - 0‖ = μ * (μ ^ k * ‖w - 0‖) := by ring
            _ ≤ μ * ‖φ^[k] w - 0‖ :=
                mul_le_mul_of_nonneg_left hgk (by linarith)
            _ ≤ ‖φ (φ^[k] w) - 0‖ := hexpand _ hvne hvρ
    -- The orbit must leave the ball: `μ ^ k → ∞`.
    have hex : ∃ k : ℕ, ρ < ‖φ^[k] w - 0‖ := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ k : ℕ, μ ^ k * ‖w - 0‖ ≤ ρ := fun k =>
        le_trans (hgrow k fun i _ => hcon i).2 (hcon k)
      obtain ⟨k, hk⟩ :=
        ((tendsto_pow_atTop_atTop_of_one_lt hμ1).eventually_ge_atTop
          (ρ / ‖w - 0‖ + 1)).exists
      have h1 : (ρ / ‖w - 0‖ + 1) * ‖w - 0‖ ≤ μ ^ k * ‖w - 0‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hwpos), one_mul] at h1
      linarith [hall k]
    -- The first exit index.
    obtain ⟨k₀, hexit_k₀, hmin⟩ : ∃ k₀ : ℕ, ρ < ‖φ^[k₀] w - 0‖ ∧
        ∀ i, i < k₀ → ‖φ^[i] w - 0‖ ≤ ρ :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_lt.mp (Nat.find_min hex hi)⟩
    obtain ⟨hid, -⟩ := hgrow k₀ hmin
    -- The contradiction with equicontinuity, through the inversion isometry.
    have hfix_iter : g^[k₀] (∞ : ℂ̂) = (∞ : ℂ̂) :=
      Function.iterate_fixed hg_fix k₀
    have hdistw : dist (inversionGL • ((w : ℂ̂))) (∞ : ℂ̂) < δ := by
      change sphericalDist (inversionGL • ((w : ℂ̂))) (∞ : ℂ̂) < δ
      rw [← hinv0, sphericalDist_inversionGL_smul]
      calc sphericalDist ((w : ℂ̂)) (((0 : ℂ) : ℂ̂)) ≤ 2 * ‖w - 0‖ :=
            sphericalDist_coe_le_norm_sub w 0
        _ = 2 * η := by rw [hwnorm]
        _ < δ := by linarith
    have hcontra := hδ (g^[k₀]) ⟨k₀, rfl⟩ (inversionGL • ((w : ℂ̂))) hdistw
    rw [hid, hfix_iter] at hcontra
    have hge := hexit (φ^[k₀] w) hexit_k₀
    change sphericalDist (inversionGL • ((φ^[k₀] w : ℂ) : ℂ̂)) (∞ : ℂ̂) < ε₀ at hcontra
    rw [← hinv0, sphericalDist_inversionGL_smul] at hcontra
    linarith

/-- **The closure of the repelling periodic points is contained in the
Julia set.** -/
theorem closure_setOf_isRepellingPeriodicPt_subset_juliaSet {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f) :
    closure {p : ℂ̂ | ∃ n : ℕ, IsRepellingPeriodicPt f n p} ⊆ JuliaSet f := by
  rw [(isClosed_juliaSet f).closure_subset_iff]
  rintro p ⟨n, hp⟩
  exact mem_juliaSet_of_isRepellingPeriodicPt hf hd hp

end NoWanderingDomains
