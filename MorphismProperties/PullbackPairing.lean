/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismProperties.RelativeBaseChange
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Pullback pairing over a fixed base

Pairs of structured objects over `S` have a pullback-pairing functor to the ordinary
over-category of `S`. The left and right structure properties are independent;
both horizontal maps satisfy the same multiplicative property. Only pullbacks of
the selected pairs are required. The construction reuses pointwise pullback cones
in the functor category and the ordinary over-category lift.

Stability of `P` against `E`, base-change stability of `P ⊓ E` and `E`, and
cancellation of `E` under postcomposition by `E` preserve the horizontal property
when the left structure arrows satisfy `E`; the right structure arrows need not
satisfy `E`. Neither the pairing's structure map nor its projections are asserted
to satisfy the horizontal property. The universal property used here is that of
the ambient pullback, not a product or a lifting property in a morphism-restricted
structured category.

## References

* Mathlib, `CategoryTheory.MorphismProperty.Comma`,
  `CategoryTheory.Comma.Over.Basic`, and
  `CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks`, for the structured
  categories, natural structure cocones, ordinary over-category lift and assembly
  of pointwise pullback cones into a functor.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5
  (2017), Chapter 0, §1.4(a), Proposition 1.4.1, for the relative preservation
  alternatives motivating the map-membership statement. This fixed-base pairing
  does not establish the full comparison of axioms in that proposition.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]
variable (E Q P : MorphismProperty C) [P.IsMultiplicative] (S : C)

variable [∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]

private def pullbackPairingLeftCocone :
    Cocone ((Prod.fst (E.Over P S) (Q.Over P S) ⋙ Over.forget E P S) ⋙
      CategoryTheory.Over.forget S) :=
  Cocone.whisker (Prod.fst (E.Over P S) (Q.Over P S) ⋙ Over.forget E P S)
    (CategoryTheory.Over.forgetCocone S)

private def pullbackPairingRightCocone :
    Cocone ((Prod.snd (E.Over P S) (Q.Over P S) ⋙ Over.forget Q P S) ⋙
      CategoryTheory.Over.forget S) :=
  Cocone.whisker (Prod.snd (E.Over P S) (Q.Over P S) ⋙ Over.forget Q P S)
    (CategoryTheory.Over.forgetCocone S)

private noncomputable def pullbackPairingCone :
    PullbackCone (pullbackPairingLeftCocone E Q P S).ι
      (pullbackPairingRightCocone E Q P S).ι :=
  PullbackCone.combine _ _
    (fun A ↦ pullback.cone A.1.hom A.2.hom)
    (fun A ↦ pullback.isLimit A.1.hom A.2.hom)

/-- Pair structured objects over a fixed base using their chosen ambient pullback.
The target is the ordinary over-category, with no property required of the new
structure map. Composing with `CategoryTheory.Over.forget S` gives the underlying
category-valued pairing. Identities and composition are those of Mathlib's
pointwise cone assembly and over-category lift. -/
noncomputable def pullbackPairing :
    (E.Over P S × Q.Over P S) ⥤ CategoryTheory.Over S :=
  let leftCocone :=
    Cocone.whisker (Prod.fst (E.Over P S) (Q.Over P S) ⋙ Over.forget E P S)
      (CategoryTheory.Over.forgetCocone S)
  let rightCocone :=
    Cocone.whisker (Prod.snd (E.Over P S) (Q.Over P S) ⋙ Over.forget Q P S)
      (CategoryTheory.Over.forgetCocone S)
  let cone := PullbackCone.combine leftCocone.ι rightCocone.ι
    (fun A ↦ pullback.cone A.1.hom A.2.hom)
    (fun A ↦ pullback.isLimit A.1.hom A.2.hom)
  CategoryTheory.Over.lift cone.pt (cone.fst ≫ leftCocone.ι)

/-- The underlying object of the pairing is the chosen ambient pullback. -/
@[simp]
lemma pullbackPairing_obj_left (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairing E Q P S).obj (A, B)).left = pullback A.hom B.hom := rfl

/-- The pairing's structure map is obtained from the first projection. -/
@[simp]
lemma pullbackPairing_obj_hom (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairing E Q P S).obj (A, B)).hom =
      pullback.fst A.hom B.hom ≫ A.hom := rfl

/-- The second projection gives the same structure map. -/
lemma pullbackPairing_obj_hom_eq_snd (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairing E Q P S).obj (A, B)).hom =
      pullback.snd A.hom B.hom ≫ B.hom := by
  rw [pullbackPairing_obj_hom]
  exact pullback.condition

/-- The first projection of the induced map recovers its left factor. -/
@[reassoc (attr := simp)]
lemma pullbackPairing_map_fst {A B : E.Over P S × Q.Over P S} (f : A ⟶ B) :
    ((pullbackPairing E Q P S).map f).left ≫ pullback.fst B.1.hom B.2.hom =
      pullback.fst A.1.hom A.2.hom ≫ f.1.left :=
  (pullbackPairingCone E Q P S).fst.naturality f

/-- The second projection of the induced map recovers its right factor. -/
@[reassoc (attr := simp)]
lemma pullbackPairing_map_snd {A B : E.Over P S × Q.Over P S} (f : A ⟶ B) :
    ((pullbackPairing E Q P S).map f).left ≫ pullback.snd B.1.hom B.2.hom =
      pullback.snd A.1.hom A.2.hom ≫ f.2.left :=
  (pullbackPairingCone E Q P S).snd.naturality f

/-- The pairing's underlying map is the canonical map between ambient pullbacks. -/
lemma pullbackPairing_map_left {A B : E.Over P S × Q.Over P S} (f : A ⟶ B) :
    ((pullbackPairing E Q P S).map f).left =
      pullback.map A.1.hom A.2.hom B.1.hom B.2.hom f.1.left f.2.left (𝟙 S)
        (by simpa using (Over.w f.1).symm) (by simpa using (Over.w f.2).symm) := by
  apply pullback.hom_ext
  · exact (pullbackPairing_map_fst E Q P S f).trans (pullback.lift_fst _ _ _).symm
  · exact (pullbackPairing_map_snd E Q P S f).trans (pullback.lift_snd _ _ _).symm

/-- Relative stability preserves the pairing's horizontal property when the left
structure arrows satisfy `E`. Right structure arrows are unrestricted beyond `Q`.
The selected-pair family supplies the mixed pullback needed by the object
alternative of `MorphismProperty.pullbackMap_of_relative_alternatives`, motivated
by Fujiwara--Kato, *Foundations of Rigid Geometry I*, Chapter 0, Proposition 1.4.1
(arXiv:1308.4734v5, 2017). -/
theorem pullbackPairing_map_mem_of_relative
    [P.IsStableUnderBaseChangeAgainst E] [(P ⊓ E).IsStableUnderBaseChange]
    [E.IsStableUnderBaseChange] [E.HasOfPostcompProperty E]
    {A B : E.Over P S × Q.Over P S} (f : A ⟶ B) :
    P ((pullbackPairing E Q P S).map f).left := by
  rw [pullbackPairing_map_left E Q P S f]
  exact P.pullbackMap_of_relative_alternatives E f.1.prop_hom_left f.2.prop_hom_left
    (Over.w f.1).symm (Over.w f.2).symm
    (Or.inl ⟨A.1.prop, B.1.prop, inferInstance⟩)

end CategoryTheory.MorphismProperty.Over
