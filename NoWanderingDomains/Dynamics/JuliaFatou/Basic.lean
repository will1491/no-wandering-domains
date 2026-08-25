/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.JuliaFatou.Def

/-!
# Basic topology of Fatou and Julia sets

The Fatou set is open (normality at a point is an open condition), so the
Julia set is closed — and compact, since the sphere is. Both sets are
unchanged by passing from `f` to an iterate `f^[k]` (`k ≥ 1`): one
inclusion is the subfamily observation `{(f^[k])^[n]} ⊆ {f^[n]}`, and the
converse splits an arbitrary iterate as `f^[r] ∘ (f^[k])^[q]` by Euclidean
division and post-composes the limit with the uniformly continuous `f^[r]`
(uniform continuity is free on the compact sphere).
-/

namespace NoWanderingDomains

/-- The Fatou set is open. -/
theorem isOpen_fatouSet (f : ℂ̂ → ℂ̂) : IsOpen (FatouSet f) :=
  isOpen_setOf_isNormalAt (Set.range fun n : ℕ => f^[n])

/-- The Julia set is closed. -/
theorem isClosed_juliaSet (f : ℂ̂ → ℂ̂) : IsClosed (JuliaSet f) :=
  (isOpen_fatouSet f).isClosed_compl

/-- The Julia set is compact. -/
theorem isCompact_juliaSet (f : ℂ̂ → ℂ̂) : IsCompact (JuliaSet f) :=
  (isClosed_juliaSet f).isCompact

/-- The Fatou set of `f` is contained in the Fatou set of any iterate: the
`f^[k]`-iterates form a subfamily of the `f`-iterates. -/
theorem fatouSet_subset_fatouSet_iterate (f : ℂ̂ → ℂ̂) (k : ℕ) :
    FatouSet f ⊆ FatouSet (f^[k]) := by
  intro z hz
  obtain ⟨U, hU, hN⟩ := mem_fatouSet_iff.mp hz
  refine mem_fatouSet_iff.mpr ⟨U, hU, hN.of_subfamily ?_⟩
  rintro _ ⟨n, rfl⟩
  exact ⟨k * n, Function.iterate_mul f k n⟩

/-- **The Fatou set is unchanged by passing to iterates.** For continuous
`f` and `k ≥ 1`, `FatouSet (f^[k]) = FatouSet f`. -/
theorem fatouSet_iterate {f : ℂ̂ → ℂ̂} (hf : Continuous f) {k : ℕ}
    (hk : 0 < k) : FatouSet (f^[k]) = FatouSet f := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fatouSet_subset_fatouSet_iterate f k)
  obtain ⟨U, hU, hN⟩ := mem_fatouSet_iff.mp hz
  refine mem_fatouSet_iff.mpr ⟨U, hU, ?_⟩
  intro seq
  -- Extract the iterate index of each member of the sequence.
  choose m hm using fun n => (seq n).2
  -- Pigeonhole: some residue class `r` modulo `k` occurs infinitely often.
  obtain ⟨r, hr⟩ :=
    Finite.exists_infinite_fiber fun n : ℕ => (⟨m n % k, Nat.mod_lt (m n) hk⟩ : Fin k)
  have hinf : {n : ℕ | m n % k = (r : ℕ)}.Infinite := by
    refine (Set.infinite_coe_iff.mp hr).mono fun n hn => ?_
    simpa [Fin.ext_iff] using hn
  -- Enumerate that residue class by a strictly monotone `ψ`.
  obtain ⟨ψ, hψ, hψm⟩ :=
    Filter.extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hinf)
  -- Normality of the `f^[k]`-iterates applied to the quotient sequence.
  obtain ⟨σ, hσ, g, hg⟩ := hN fun j => ⟨(f^[k])^[m (ψ j) / k], ⟨m (ψ j) / k, rfl⟩⟩
  -- Post-compose with the uniformly continuous fixed map `f^[r]`.
  have huc : UniformContinuous f^[(r : ℕ)] :=
    CompactSpace.uniformContinuous_of_continuous (hf.iterate (r : ℕ))
  have hcomp := huc.comp_tendstoLocallyUniformlyOn hg
  refine ⟨ψ ∘ σ, hψ.comp hσ, f^[(r : ℕ)] ∘ g, hcomp.congr fun j => ?_⟩
  have h2 : (r : ℕ) + k * (m (ψ (σ j)) / k) = m (ψ (σ j)) := by
    rw [← hψm (σ j), Nat.add_comm]
    exact Nat.div_add_mod (m (ψ (σ j))) k
  have h3 : f^[(r : ℕ)] ∘ (f^[k])^[m (ψ (σ j)) / k] =
      (seq (ψ (σ j)) : ℂ̂ → ℂ̂) := by
    rw [← Function.iterate_mul, ← Function.iterate_add, h2]
    exact hm (ψ (σ j))
  exact fun x _ => congrFun h3 x

/-- **The Julia set is unchanged by passing to iterates.** -/
theorem juliaSet_iterate {f : ℂ̂ → ℂ̂} (hf : Continuous f) {k : ℕ}
    (hk : 0 < k) : JuliaSet (f^[k]) = JuliaSet f := by
  simp only [JuliaSet, fatouSet_iterate hf hk]

end NoWanderingDomains
