/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.NormalFamilies.Basic
import NoWanderingDomains.NormalFamilies.Spherical
import NoWanderingDomains.Sphere.Basic

/-!
# Fatou and Julia sets

For a self-map `f : ℂ̂ → ℂ̂` of the Riemann sphere, the *Fatou set* is the
set of points at which the family of iterates `{f^[n] : n ∈ ℕ}` is normal
(for the spherical metric on the compact target `ℂ̂`), and the *Julia set*
is its complement. The Fatou set is the locus of stable, tame dynamics; the
Julia set carries the chaotic dynamics.

This file gives the definitions and the membership API. Topological
properties (`FatouSet` open, `JuliaSet` closed and compact, invariance
under `f`, and invariance under passing to iterates) are in `Basic.lean`
and `Invariance.lean`.
-/

namespace NoWanderingDomains

/-- The *Fatou set* of `f : ℂ̂ → ℂ̂`: the set of points at which the family
of iterates `{f^[n] : n ∈ ℕ}` is normal. -/
def FatouSet (f : ℂ̂ → ℂ̂) : Set ℂ̂ :=
  {z | IsNormalAt (Set.range fun n : ℕ => f^[n]) z}

/-- The *Julia set* of `f : ℂ̂ → ℂ̂`: the complement of the Fatou set. -/
def JuliaSet (f : ℂ̂ → ℂ̂) : Set ℂ̂ :=
  (FatouSet f)ᶜ

theorem mem_fatouSet_iff {f : ℂ̂ → ℂ̂} {z : ℂ̂} :
    z ∈ FatouSet f ↔
      ∃ U ∈ nhds z, IsNormal (Set.range fun n : ℕ => f^[n]) U :=
  Iff.rfl

theorem mem_juliaSet_iff {f : ℂ̂ → ℂ̂} {z : ℂ̂} :
    z ∈ JuliaSet f ↔
      ¬ ∃ U ∈ nhds z, IsNormal (Set.range fun n : ℕ => f^[n]) U :=
  Iff.rfl

/-- The Julia set is the complement of the Fatou set. -/
theorem compl_fatouSet (f : ℂ̂ → ℂ̂) : (FatouSet f)ᶜ = JuliaSet f :=
  rfl

/-- The Fatou set is the complement of the Julia set. -/
theorem compl_juliaSet (f : ℂ̂ → ℂ̂) : (JuliaSet f)ᶜ = FatouSet f :=
  compl_compl _

/-- The Fatou and Julia sets partition the sphere. -/
theorem fatouSet_union_juliaSet (f : ℂ̂ → ℂ̂) :
    FatouSet f ∪ JuliaSet f = Set.univ :=
  Set.union_compl_self _

/-- The Fatou and Julia sets are disjoint. -/
theorem disjoint_fatouSet_juliaSet (f : ℂ̂ → ℂ̂) :
    Disjoint (FatouSet f) (JuliaSet f) :=
  disjoint_compl_right

end NoWanderingDomains
