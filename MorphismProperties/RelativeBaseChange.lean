/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Andrew Yang, Joël Riou, Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Relative preservation of maps of pullbacks

A map between two pullbacks is itself a base change of the original map along
the first projection of the target pullback. Consequently stability along that
projection suffices to preserve a morphism property. If `P` is stable against `E`,
`E` is stable under base change, and the base arrow belongs to `E`, this gives
preservation of the existing maps of pullbacks and of the functor `Over.pullback`.
Only the two pullbacks in the pointwise statement are required.

For an arbitrary existing pullback square, preservation when either leg belongs
to a base-change-stable `E` is equivalent to relative stability of `P` against
`E` and absolute stability of `P ⊓ E`. No pullback existence is assumed by this
criterion.

There is also an object-structured alternative: if `P ⊓ E` is stable under
base change and `E` can be cancelled from postcomposition by an `E` arrow,
a map in `P` between two arrows in `E` induces a map in `P ⊓ E` along any
base arrow. Combining this with relative stability covers either two
`E`-structured objects or a base arrow in `E`.

This generalizes Mathlib's `MorphismProperty.pullbackLift_fst_snd` and
`MorphismProperty.overPullbackMap`; the absolute compatibility applications retain
their arrows and hypotheses in the four-object-chain clients.

## References

* Mathlib, `CategoryTheory.MorphismProperty.Limits`, for morphism-property stability,
  the absolute preservation results, and the induced maps used here.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5
  (2017), Chapter 0, §1.4(a), Proposition 1.4.1, for the relative comparison
  motivating the preservation statements and the either-leg stability criterion.
  The results here do not give the full comparison of the axioms for classes
  of morphisms in that section.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C]

/-- For a base-change-stable property `E`, preservation of `P` in every existing
pullback square when either leg belongs to `E` is equivalent to stability of `P`
against `E` together with absolute stability of `P ⊓ E`.

The square `IsPullback p q a b` satisfies `p ≫ a = q ≫ b`; the preserved arrow
is `q`. This criterion requires no pullback existence or isomorphism-invariance
hypothesis. It is motivated by Fujiwara–Kato, *Foundations of Rigid Geometry I*,
Proposition 1.4.1 of Chapter 0 (arXiv:1308.4734v5, 2017); its proof uses Mathlib's
morphism-property stability classes. -/
theorem isStableUnderBaseChange_either_iff
    (P E : MorphismProperty C) [E.IsStableUnderBaseChange] :
    (∀ ⦃X Y Y' T : C⦄ (a : X ⟶ Y) (b : Y' ⟶ Y)
        (p : T ⟶ X) (q : T ⟶ Y'),
        IsPullback p q a b → P a → (E a ∨ E b) → P q) ↔
      (P.IsStableUnderBaseChangeAgainst E ∧
        (P ⊓ E).IsStableUnderBaseChange) := by
  constructor
  · intro h
    constructor
    · constructor
      intro X Y b hb
      constructor
      intro Z T p q a sq ha
      exact h a b p q sq ha (Or.inr hb)
    · constructor
      intro X Y Y' S b a p q sq ha
      exact ⟨h a b p q sq ha.1 (Or.inl ha.2), E.of_isPullback sq ha.2⟩
  · rintro ⟨hAgainst, hInf⟩ X Y Y' T a b p q sq ha (hea | heb)
    · exact (hInf.of_isPullback sq ⟨ha, hea⟩).1
    · exact (hAgainst.isStableUnderBaseChangeAlong b heb).of_isPullback sq ha

set_option backward.isDefEq.respectTransparency false in
/-- A map of pullbacks has property `P` if the original map does and `P` is stable
along the first projection of the target pullback. -/
theorem pullbackLift_fst_snd_of_isStableUnderBaseChangeAlong
    (P : MorphismProperty C) {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y}
    (hv₁₂ : v₁₂ = g ≫ v₂₂)
    [HasPullback v₁₂ f] [HasPullback v₂₂ f]
    [P.IsStableUnderBaseChangeAlong (pullback.fst v₂₂ f)]
    (hg : P g) :
    P (pullback.lift (f := v₂₂) (g := f)
      (pullback.fst v₁₂ f ≫ g) (pullback.snd v₁₂ f)
      (by simp [pullback.condition, ← hv₁₂])) := by
  subst hv₁₂
  refine IsStableUnderBaseChangeAlong.of_isPullback
    (f := pullback.fst v₂₂ f) (f' := pullback.fst (g ≫ v₂₂) f) ?_ hg
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

/-- Relative stability against a base-change-stable property `E` preserves maps
of pullbacks along an arrow in `E`. -/
theorem pullbackLift_fst_snd_of_isStableUnderBaseChangeAgainst
    (P E : MorphismProperty C)
    [P.IsStableUnderBaseChangeAgainst E] [E.IsStableUnderBaseChange]
    {S S' X Y : C} (f : S' ⟶ S) (hf : E f)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y}
    (hv₁₂ : v₁₂ = g ≫ v₂₂)
    [HasPullback v₁₂ f] [HasPullback v₂₂ f]
    (hg : P g) :
    P (pullback.lift (f := v₂₂) (g := f)
      (pullback.fst v₁₂ f ≫ g) (pullback.snd v₁₂ f)
      (by simp [pullback.condition, ← hv₁₂])) := by
  let := IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong
    (P := P) (P' := E) (pullback.fst v₂₂ f) (E.pullback_fst v₂₂ f hf)
  exact P.pullbackLift_fst_snd_of_isStableUnderBaseChangeAlong f hv₁₂ hg

/-- Maps between `E`-structured objects are preserved along any base arrow if
`P ⊓ E` is stable under base change and `E` is cancellable under postcomposition
by an `E` arrow. The induced map belongs to both `P` and `E`.

This is the object-structured preservation branch motivated by Fujiwara--Kato,
Chapter 0, Proposition 1.4.1. Its proof combines Mathlib's `of_postcomp` with
`pullbackLift_fst_snd` for the intersection property. -/
theorem pullbackLift_fst_snd_of_intersection_of_postcomp
    (P E : MorphismProperty C)
    [(P ⊓ E).IsStableUnderBaseChange] [E.HasOfPostcompProperty E]
    {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y}
    (hv₁₂ : v₁₂ = g ≫ v₂₂)
    [HasPullback v₁₂ f] [HasPullback v₂₂ f]
    (hv₁₂E : E v₁₂) (hv₂₂E : E v₂₂) (hg : P g) :
    (P ⊓ E) (pullback.lift (f := v₂₂) (g := f)
      (pullback.fst v₁₂ f ≫ g) (pullback.snd v₁₂ f)
      (by simp [pullback.condition, ← hv₁₂])) := by
  exact (P ⊓ E).pullbackLift_fst_snd f hv₁₂
    ⟨hg, E.of_postcomp g v₂₂ hv₂₂E (hv₁₂ ▸ hv₁₂E)⟩

/-- Relative stability preserves a map of pullbacks if either both objects are
`E`-structured or the base arrow belongs to `E`. The first alternative uses
base-change stability of `P ⊓ E` and postcomposition cancellation for `E`;
the second uses stability of `P` against the base-change-stable `E`.

These are the two pointwise preservation alternatives motivated by
Fujiwara--Kato, Chapter 0, Proposition 1.4.1. -/
theorem pullbackLift_fst_snd_of_relative_alternatives
    (P E : MorphismProperty C)
    [P.IsStableUnderBaseChangeAgainst E] [(P ⊓ E).IsStableUnderBaseChange]
    [E.IsStableUnderBaseChange] [E.HasOfPostcompProperty E]
    {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y}
    (hv₁₂ : v₁₂ = g ≫ v₂₂)
    [HasPullback v₁₂ f] [HasPullback v₂₂ f]
    (hE : (E v₁₂ ∧ E v₂₂) ∨ E f) (hg : P g) :
    P (pullback.lift (f := v₂₂) (g := f)
      (pullback.fst v₁₂ f ≫ g) (pullback.snd v₁₂ f)
      (by simp [pullback.condition, ← hv₁₂])) := by
  rcases hE with ⟨hv₁₂E, hv₂₂E⟩ | hf
  · exact (P.pullbackLift_fst_snd_of_intersection_of_postcomp E f hv₁₂
      hv₁₂E hv₂₂E hg).1
  · exact P.pullbackLift_fst_snd_of_isStableUnderBaseChangeAgainst E f hf hv₁₂ hg

/-- The existing pullback functor on slice categories preserves `P` on morphisms
along an `E` arrow, provided `P` is stable against the base-change-stable `E`. -/
theorem overPullbackMap_of_isStableUnderBaseChangeAgainst
    (P E : MorphismProperty C)
    [P.IsStableUnderBaseChangeAgainst E] [E.IsStableUnderBaseChange]
    {S S' : C} (f : S' ⟶ S) (hf : E f)
    [HasPullbacksAlong f] {X Y : Over S} (g : X ⟶ Y)
    (hg : P g.left) : P ((Over.pullback f).map g).left :=
  P.pullbackLift_fst_snd_of_isStableUnderBaseChangeAgainst E f hf g.w.symm hg

end CategoryTheory.MorphismProperty
