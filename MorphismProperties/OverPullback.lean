/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismProperties.RelativeBaseChange
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Whiskering

/-!
# Pullback transport between structured over-categories

For `E`-structured objects and `P`-restricted morphisms, base change along `f`
defines a functor using objectwise pullback existence and stability of `E` along
`f`. Horizontal preservation follows from stability of `P ⊓ E` and cancellation
of `E` under postcomposition by an `E` arrow; absolute stability of `P` is not
required. The construction is a lift of Mathlib's pullback functor with unrestricted
horizontal arrows. Its universal properties concern the ambient pullbacks and
uniqueness of the structured lift, not creation of pullbacks or an adjunction.

## References

* Mathlib, `CategoryTheory.MorphismProperty.Comma` and `OverAdjunction`, for the
  structured categories, change of properties, lifting, and objectwise pullback functor.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5
  (2017), Chapter 0, §1.4(a), Proposition 1.4.1, for the object-structured
  preservation alternative motivating this fixed-base-arrow construction. This
  does not establish the full comparison of axioms in that proposition.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]
variable (E P : MorphismProperty C) [P.IsMultiplicative]
variable {S S' : C} (f : S' ⟶ S)
variable [E.HasPullbacksAlong f] [E.IsStableUnderBaseChangeAlong f]
variable [(P ⊓ E).IsStableUnderBaseChange] [E.HasOfPostcompProperty E]

set_option backward.isDefEq.respectTransparency false in
/-- Base change between `E`-structured over-categories with `P`-restricted
morphisms. Intersection stability and postcomposition cancellation preserve
horizontal maps, without absolute stability of `P` or pullbacks for all objects. -/
noncomputable def pullbackOfIntersectionOfPostcomp : E.Over P S ⥤ E.Over P S' :=
  Comma.lift
    (Over.changeProp S (P := E) (Q := P) le_rfl le_top ⋙
      Over.pullback E ⊤ f ⋙ Over.forget E ⊤ S')
    (fun A ↦ ((Over.pullback E ⊤ f).obj
      ((Over.changeProp S le_rfl le_top).obj A)).prop)
    (fun {A B} g ↦
      (P.pullbackLift_fst_snd_of_intersection_of_postcomp E f
        (Over.w g).symm A.prop B.prop g.prop_hom_left).1)
    (fun _ ↦ trivial)

/-- The underlying object is the chosen ambient pullback. -/
@[simp]
lemma pullbackOfIntersectionOfPostcomp_obj_left (A : E.Over P S) :
    ((pullbackOfIntersectionOfPostcomp E P f).obj A).left = Limits.pullback A.hom f := rfl

/-- The structure map is the second pullback projection. -/
@[simp]
lemma pullbackOfIntersectionOfPostcomp_obj_hom (A : E.Over P S) :
    ((pullbackOfIntersectionOfPostcomp E P f).obj A).hom = pullback.snd A.hom f := rfl

/-- The underlying map agrees with the unrestricted structured pullback functor. -/
lemma pullbackOfIntersectionOfPostcomp_map_left {A B : E.Over P S} (g : A ⟶ B) :
    ((pullbackOfIntersectionOfPostcomp E P f).map g).left =
      ((Over.pullback E ⊤ f).map
        ((Over.changeProp S le_rfl le_top).map g)).left := rfl

/-- The underlying map is the canonical pullback lift of the two projections. -/
lemma pullbackOfIntersectionOfPostcomp_map_left_eq_lift {A B : E.Over P S} (g : A ⟶ B) :
    ((pullbackOfIntersectionOfPostcomp E P f).map g).left =
      pullback.lift (f := B.hom) (g := f)
        (pullback.fst A.hom f ≫ g.left) (pullback.snd A.hom f)
        (by simp only [Category.assoc, Over.w, pullback.condition]) := rfl

/-- The first projection of the transported map. -/
@[reassoc (attr := simp)]
lemma pullbackOfIntersectionOfPostcomp_map_fst {A B : E.Over P S} (g : A ⟶ B) :
    ((pullbackOfIntersectionOfPostcomp E P f).map g).left ≫ pullback.fst B.hom f =
      pullback.fst A.hom f ≫ g.left := by
  rw [pullbackOfIntersectionOfPostcomp_map_left_eq_lift]
  exact pullback.lift_fst _ _ _

/-- The second projection of the transported map. -/
@[reassoc (attr := simp)]
lemma pullbackOfIntersectionOfPostcomp_map_snd {A B : E.Over P S} (g : A ⟶ B) :
    ((pullbackOfIntersectionOfPostcomp E P f).map g).left ≫ pullback.snd B.hom f =
      pullback.snd A.hom f := by
  rw [pullbackOfIntersectionOfPostcomp_map_left_eq_lift]
  exact pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The underlying arrow agrees with the canonical map between ambient pullbacks. -/
lemma pullbackOfIntersectionOfPostcomp_map_left_eq_map {A B : E.Over P S} (g : A ⟶ B) :
    ((pullbackOfIntersectionOfPostcomp E P f).map g).left =
      pullback.map A.hom f B.hom f g.left (𝟙 S') (𝟙 S)
        (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp [pullbackOfIntersectionOfPostcomp_map_left_eq_lift, pullback.map]

/-- Base-changed structure maps satisfy `E`. -/
lemma pullbackOfIntersectionOfPostcomp_obj_mem (A : E.Over P S) :
    E ((pullbackOfIntersectionOfPostcomp E P f).obj A).hom :=
  ((pullbackOfIntersectionOfPostcomp E P f).obj A).prop

/-- Transported horizontal maps satisfy `P`. -/
lemma pullbackOfIntersectionOfPostcomp_map_mem {A B : E.Over P S} (g : A ⟶ B) :
    P ((pullbackOfIntersectionOfPostcomp E P f).map g).left :=
  ((pullbackOfIntersectionOfPostcomp E P f).map g).prop_hom_left

/-- Transported horizontal maps also satisfy `E`. -/
lemma pullbackOfIntersectionOfPostcomp_map_mem_inf {A B : E.Over P S} (g : A ⟶ B) :
    (P ⊓ E) ((pullbackOfIntersectionOfPostcomp E P f).map g).left := by
  rw [pullbackOfIntersectionOfPostcomp_map_left_eq_lift]
  exact P.pullbackLift_fst_snd_of_intersection_of_postcomp E f
    (Over.w g).symm A.prop B.prop g.prop_hom_left

/-- Forgetting the lift recovers the composite used to construct it. -/
lemma pullbackOfIntersectionOfPostcomp_comp_forget :
    pullbackOfIntersectionOfPostcomp E P f ⋙ Over.forget E P S' =
      Over.changeProp S (P := E) (Q := P) le_rfl le_top ⋙
        Over.pullback E ⊤ f ⋙ Over.forget E ⊤ S' := rfl

/-- An object with the same underlying over-object is the same structured object. -/
lemma pullbackOfIntersectionOfPostcomp_obj_ext (A : E.Over P S) (B : E.Over P S')
    (h : B.toComma = ((pullbackOfIntersectionOfPostcomp E P f).obj A).toComma) :
    B = (pullbackOfIntersectionOfPostcomp E P f).obj A := by
  generalize (pullbackOfIntersectionOfPostcomp E P f).obj A = D at h ⊢
  cases B
  cases D
  cases h
  rfl

/-- The canonical structured lift is unique among functors with this forgetful
factorization. Predicate witnesses do not contribute additional data. -/
lemma pullbackOfIntersectionOfPostcomp_unique
    (F : E.Over P S ⥤ E.Over P S')
    (h : F ⋙ Over.forget E P S' =
      Over.changeProp S (P := E) (Q := P) le_rfl le_top ⋙
        Over.pullback E ⊤ f ⋙ Over.forget E ⊤ S') :
    F = pullbackOfIntersectionOfPostcomp E P f := by
  have hforget := h.trans (pullbackOfIntersectionOfPostcomp_comp_forget E P f).symm
  have hobj : ∀ A, F.obj A = (pullbackOfIntersectionOfPostcomp E P f).obj A :=
    fun A ↦ pullbackOfIntersectionOfPostcomp_obj_ext E P f A (F.obj A)
      (Functor.congr_obj hforget A)
  refine Functor.ext hobj ?_
  intro A B g
  apply (Over.forget E P S').map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using
    Functor.congr_hom hforget g

/-- The two projections uniquely characterize the transported structured morphism. -/
lemma pullbackOfIntersectionOfPostcomp_map_unique {A B : E.Over P S} (g : A ⟶ B)
    (k : (pullbackOfIntersectionOfPostcomp E P f).obj A ⟶
      (pullbackOfIntersectionOfPostcomp E P f).obj B)
    (hfst : k.left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left)
    (hsnd : k.left ≫ pullback.snd B.hom f = pullback.snd A.hom f) :
    k = (pullbackOfIntersectionOfPostcomp E P f).map g := by
  apply Over.Hom.ext
  apply pullback.hom_ext
  · exact hfst.trans (pullbackOfIntersectionOfPostcomp_map_fst E P f g).symm
  · exact hsnd.trans (pullbackOfIntersectionOfPostcomp_map_snd E P f g).symm

/-- The underlying object satisfies the ambient pullback universal property. -/
lemma pullbackOfIntersectionOfPostcomp_existsUnique_lift (A : E.Over P S)
    {W : C} (a : W ⟶ A.left) (b : W ⟶ S') (h : a ≫ A.hom = b ≫ f) :
    ∃! k : W ⟶ ((pullbackOfIntersectionOfPostcomp E P f).obj A).left,
      k ≫ pullback.fst A.hom f = a ∧ k ≫ pullback.snd A.hom f = b := by
  simp only [pullbackOfIntersectionOfPostcomp_obj_left]
  refine ⟨pullback.lift a b h, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
  intro k hk
  apply pullback.hom_ext
  · exact hk.1.trans (pullback.lift_fst _ _ _).symm
  · exact hk.2.trans (pullback.lift_snd _ _ _).symm

/-- Identity preservation on underlying arrows follows from the functor law. -/
lemma pullbackOfIntersectionOfPostcomp_map_id_left (A : E.Over P S) :
    ((pullbackOfIntersectionOfPostcomp E P f).map (𝟙 A)).left =
      𝟙 ((pullbackOfIntersectionOfPostcomp E P f).obj A).left := by
  rw [Functor.map_id]
  rfl

/-- Composition preservation on underlying arrows follows from the functor law. -/
lemma pullbackOfIntersectionOfPostcomp_map_comp_left {A B D : E.Over P S}
    (g : A ⟶ B) (h : B ⟶ D) :
    ((pullbackOfIntersectionOfPostcomp E P f).map (g ≫ h)).left =
      ((pullbackOfIntersectionOfPostcomp E P f).map g).left ≫
        ((pullbackOfIntersectionOfPostcomp E P f).map h).left := by
  rw [Functor.map_comp]
  rfl

/-- Under absolute stability of `P`, the construction agrees with Mathlib's
structured pullback functor. -/
lemma pullbackOfIntersectionOfPostcomp_eq_pullback [P.IsStableUnderBaseChange] :
    pullbackOfIntersectionOfPostcomp E P f = Over.pullback E P f := by
  rfl

/-- When pullbacks along `f` exist for every over-object, forgetting structured
transport agrees with the ordinary over-category pullback functor. -/
@[simps! hom_app_left inv_app_left]
noncomputable def pullbackOfIntersectionOfPostcompCompForgetIso
    [Limits.HasPullbacksAlong f] :
    pullbackOfIntersectionOfPostcomp E P f ⋙ Over.forget E P S' ≅
      Over.forget E P S ⋙ CategoryTheory.Over.pullback f :=
  eqToIso (pullbackOfIntersectionOfPostcomp_comp_forget E P f) ≪≫
    Functor.isoWhiskerLeft (Over.changeProp S (P := E) (Q := P) le_rfl le_top)
      (Over.pullbackCompForgetIso (P := E) (Q := ⊤) f)

end CategoryTheory.MorphismProperty.Over
