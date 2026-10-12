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

Interchanging the factors gives a natural isomorphism of ordinary-over pairings,
with components given by pullback symmetry. Its projection equations identify
both reversed coordinates, and swapping twice restores each component. Reverse
pullback existence follows from the selected forward family, without further
closure or stability hypotheses.

## References

* Mathlib, `CategoryTheory.MorphismProperty.Comma`,
  `CategoryTheory.Comma.Over.Basic`, and
  `CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks`, for the structured
  categories, natural structure cocones, ordinary over-category lift and assembly
  of pointwise pullback cones into a functor.
* Mathlib, `CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Products.Basic`, and `CategoryTheory.NatIso`, for pullback
  symmetry, swapping product categories, and componentwise natural isomorphisms.
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

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [cat : Category.{v} C]
variable (E Q P : MorphismProperty C) [mult : P.IsMultiplicative] (S : C)
variable [h : ∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]

/-- Interchanging the two structured factors gives a natural isomorphism of
ordinary-over pullback pairings. Reverse pullback existence is derived pointwise
from the selected forward family; no horizontal condition is imposed on the
components. -/
noncomputable def pullbackPairingSymmetry :
    @pullbackPairing C cat E Q P mult S h ≅
      Prod.swap (E.Over P S) (Q.Over P S) ⋙
        @pullbackPairing C cat Q E P mult S
          (fun B A ↦ @hasPullback_symmetry
            C cat A.left B.left S A.hom B.hom (h A B)) := by
  letI : ∀ B : Q.Over P S, ∀ A : E.Over P S, HasPullback B.hom A.hom :=
    fun B A ↦ @hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)
  let e (A : E.Over P S × Q.Over P S) :
      (pullbackPairing E Q P S).obj A ≅
        (Prod.swap (E.Over P S) (Q.Over P S) ⋙ pullbackPairing Q E P S).obj A :=
    CategoryTheory.Over.isoMk (pullbackSymmetry A.1.hom A.2.hom) (by
      rcases A with ⟨A, B⟩
      have hs :
          (pullbackSymmetry A.hom B.hom).hom ≫
              (pullback.fst B.hom A.hom ≫ B.hom) =
            pullback.snd A.hom B.hom ≫ B.hom :=
        pullbackSymmetry_hom_comp_fst_assoc (f := A.hom) (g := B.hom) B.hom
      simpa only [Functor.comp_obj, Prod.swap_obj, pullbackPairing_obj_left,
        pullbackPairing_obj_hom] using
        hs.trans (pullback.condition (f := A.hom) (g := B.hom)).symm)
  refine NatIso.ofComponents e ?_
  rintro ⟨A₁, A₂⟩ ⟨B₁, B₂⟩ f
  have hA : (e (A₁, A₂)).hom.left = (pullbackSymmetry A₁.hom A₂.hom).hom := rfl
  have hB : (e (B₁, B₂)).hom.left = (pullbackSymmetry B₁.hom B₂.hom).hom := rfl
  have hn :
      pullback.map A₁.hom A₂.hom B₁.hom B₂.hom f.1.left f.2.left (𝟙 S)
          (by simpa using (Over.w f.1).symm) (by simpa using (Over.w f.2).symm) ≫
        (pullbackSymmetry B₁.hom B₂.hom).hom =
      (pullbackSymmetry A₁.hom A₂.hom).hom ≫
        pullback.map A₂.hom A₁.hom B₂.hom B₁.hom f.2.left f.1.left (𝟙 S)
          (by simpa using (Over.w f.2).symm) (by simpa using (Over.w f.1).symm) := by
    apply pullback.hom_ext (f := B₂.hom) (g := B₁.hom)
    · simp only [pullback.map, Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullback.lift_snd, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]
    · simp only [pullback.map, Category.assoc, pullbackSymmetry_hom_comp_snd,
        pullback.lift_fst, pullback.lift_snd, pullbackSymmetry_hom_comp_snd_assoc]
  apply CategoryTheory.Over.OverMorphism.ext
  simpa only [CategoryTheory.Over.comp_left, Functor.comp_map, Functor.comp_obj,
    Prod.swap_obj, Prod.swap_map, pullbackPairing_map_left, pullbackPairing_obj_left,
    hA, hB] using hn

/-- The forward component has the underlying ambient symmetry map. -/
@[simp]
lemma pullbackPairingSymmetry_hom_app_left (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).hom.app (A, B)).left =
      (pullbackSymmetry A.hom B.hom).hom := by
  rfl

/-- The inverse component has the underlying inverse ambient symmetry map. -/
@[simp]
lemma pullbackPairingSymmetry_inv_app_left (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).inv.app (A, B)).left =
      (pullbackSymmetry A.hom B.hom).inv := by
  rfl

/-- The first reversed projection is the second forward projection. -/
@[reassoc (attr := simp)]
lemma pullbackPairingSymmetry_hom_app_fst (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).hom.app (A, B)).left ≫
        @pullback.fst C cat B.left A.left S B.hom A.hom
          (@hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)) =
      pullback.snd A.hom B.hom := by
  rw [pullbackPairingSymmetry_hom_app_left]
  exact pullbackSymmetry_hom_comp_fst A.hom B.hom

/-- The second reversed projection is the first forward projection. -/
@[reassoc (attr := simp)]
lemma pullbackPairingSymmetry_hom_app_snd (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).hom.app (A, B)).left ≫
        @pullback.snd C cat B.left A.left S B.hom A.hom
          (@hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)) =
      pullback.fst A.hom B.hom := by
  rw [pullbackPairingSymmetry_hom_app_left]
  exact pullbackSymmetry_hom_comp_snd A.hom B.hom

/-- The first forward projection after the inverse is the second reversed one. -/
@[reassoc (attr := simp)]
lemma pullbackPairingSymmetry_inv_app_fst (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).inv.app (A, B)).left ≫
        pullback.fst A.hom B.hom =
      @pullback.snd C cat B.left A.left S B.hom A.hom
        (@hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)) := by
  rw [pullbackPairingSymmetry_inv_app_left]
  exact pullbackSymmetry_inv_comp_fst A.hom B.hom

/-- The second forward projection after the inverse is the first reversed one. -/
@[reassoc (attr := simp)]
lemma pullbackPairingSymmetry_inv_app_snd (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).inv.app (A, B)).left ≫
        pullback.snd A.hom B.hom =
      @pullback.fst C cat B.left A.left S B.hom A.hom
        (@hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)) := by
  rw [pullbackPairingSymmetry_inv_app_left]
  exact pullbackSymmetry_inv_comp_snd A.hom B.hom

/-- The component with the factors reversed is the inverse component. -/
lemma pullbackPairingSymmetry_hom_app_swap (A : E.Over P S) (B : Q.Over P S) :
    (@pullbackPairingSymmetry C cat Q E P mult S
      (fun B A ↦ @hasPullback_symmetry
        C cat A.left B.left S A.hom B.hom (h A B))).hom.app (B, A) =
      (pullbackPairingSymmetry E Q P S).inv.app (A, B) := by
  let : ∀ B : Q.Over P S, ∀ A : E.Over P S, HasPullback B.hom A.hom :=
    fun B A ↦ @hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)
  apply CategoryTheory.Over.OverMorphism.ext
  apply pullback.hom_ext (f := A.hom) (g := B.hom)
  · exact (pullbackPairingSymmetry_hom_app_fst Q E P S B A).trans
      (pullbackPairingSymmetry_inv_app_fst E Q P S A B).symm
  · exact (pullbackPairingSymmetry_hom_app_snd Q E P S B A).trans
      (pullbackPairingSymmetry_inv_app_snd E Q P S A B).symm

/-- Swapping the factors twice restores the forward pairing component. -/
@[simp]
lemma pullbackPairingSymmetry_hom_app_comp_swap (A : E.Over P S) (B : Q.Over P S) :
    (pullbackPairingSymmetry E Q P S).hom.app (A, B) ≫
        (@pullbackPairingSymmetry C cat Q E P mult S
          (fun B A ↦ @hasPullback_symmetry
            C cat A.left B.left S A.hom B.hom (h A B))).hom.app (B, A) =
      𝟙 ((pullbackPairing E Q P S).obj (A, B)) := by
  rw [pullbackPairingSymmetry_hom_app_swap E Q P S A B]
  exact Iso.hom_inv_id_app (pullbackPairingSymmetry E Q P S) (A, B)

/-- Swapping the factors twice also restores the reversed pairing component. -/
@[simp]
lemma pullbackPairingSymmetry_hom_app_swap_comp (A : E.Over P S) (B : Q.Over P S) :
    (@pullbackPairingSymmetry C cat Q E P mult S
      (fun B A ↦ @hasPullback_symmetry
        C cat A.left B.left S A.hom B.hom (h A B))).hom.app (B, A) ≫
        (pullbackPairingSymmetry E Q P S).hom.app (A, B) =
      𝟙 ((@pullbackPairing C cat Q E P mult S
        (fun B A ↦ @hasPullback_symmetry
          C cat A.left B.left S A.hom B.hom (h A B))).obj (B, A)) := by
  rw [pullbackPairingSymmetry_hom_app_swap E Q P S A B]
  exact Iso.inv_hom_id_app (pullbackPairingSymmetry E Q P S) (A, B)

end CategoryTheory.MorphismProperty.Over
