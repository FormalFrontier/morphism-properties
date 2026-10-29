/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismPropertiesExamples.RelativeBaseChange
public import MorphismProperties.PullbackPairing
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases

/-!
# Two-factor maps between pullbacks

The existence clients recover the plain relative alternatives using the existing
morphism-property pullback-existence classes. At the absolute boundary `E = ⊤`,
the relative statement and Mathlib's `MorphismProperty.pullbackMap` have the
same conclusion under Mathlib's original existence hypotheses.

Two finite-type examples change both factors by proper inclusions. One satisfies
only the cross alternative and the other only the object alternative. The
noninjective map `Fin 3 → Fin 2` separates monomorphisms from all morphisms.
The four-object-chain example retains a property which is not absolutely stable;
only its second factor changes. In nonempty finite subsets, both input maps
change and only local pullback cones are used, although the category lacks all
pullbacks. Monomorphisms in that thin category are all morphisms, so this last
example separates existence hypotheses, not morphism properties.

The finite-type pairing client uses monomorphisms for the left structure property
and all arrows for the right one. Its two horizontal factors are proper
inclusions, the target right structure map is not mono, and the induced pairing
map is mono but not surjective or an isomorphism. Membership is checked with the
pairing's relative preservation theorem and independently with the existing
map-of-pullbacks theorem; non-surjectivity uses the pairing's projection API.
The pairing also lifts to the over-category with unrestricted structure arrows
and restricted horizontal arrows using Mathlib's comma-category constructor.
Forgetting this lift recovers the same pairing and its non-surjective finite map.

The finite symmetry clients use the natural comparison and its normalization
equations. Independent finite-model checks use Mathlib's pullback symmetry and
the pairing projection API. The right endomorphism exchanges the two points
over `0` and fixes the point over `1`.

The ordinary-over projection fan has a six-point finite-type example with two
independent coordinates. A proper inclusion induces a nonconstant four-to-six
map, and a horizontal swap moves four target points. Both projection naturality
routes are checked in coordinates; neither target projection is mono.

## References

* Mathlib, `CategoryTheory.MorphismProperty.Limits`,
  `CategoryTheory.MorphismProperty.Comma`, and
  `CategoryTheory.Limits.Types.Pullbacks`, for the absolute comparison,
  restricted comma-category lifting, and existing pullback constructions.
* Mathlib, `CategoryTheory.Limits.Shapes.Pullback.HasPullback`, for the symmetry
  and projection equations used in the finite-model checks.
* Mathlib, `Data.Fintype.Card` and `Logic.Equiv.Basic`, for transporting finite
  cardinalities and fibers along the pullback coordinate equivalence.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.PullbackMapExamples

open Limits

section Existence

variable {C : Type u} [Category.{v} C]
variable (P E : MorphismProperty C)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChangeAgainst E]
    [(P ⊓ E).IsStableUnderBaseChange]
    [E.IsStableUnderBaseChange] [E.HasOfPostcompProperty E]
    {S X X' Y Y' : C} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'}
    [HasPullback f g] [HasPullback f' g']
    (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g')

/-- Pullbacks of `E` arrows supply the mixed span selected by either alternative. -/
example [E.HasPullbacks] (hE : (E f ∧ E f') ∨ (E f ∧ E g')) :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 S)
      ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂)) := by
  apply P.pullbackMap_of_relative_alternatives E h₁ h₂ e₁ e₂
  rcases hE with ⟨hf, hf'⟩ | ⟨hf, hg'⟩
  · exact Or.inl ⟨hf, hf', E.hasPullback g hf'⟩
  · exact Or.inr ⟨hf, hg', E.hasPullback g' hf⟩

/-- Local pullbacks of `E` arrows along the two second legs also suffice;
the endpoint pullbacks remain separate hypotheses. -/
example [E.HasPullbacksAlong g] [E.HasPullbacksAlong g']
    (hE : (E f ∧ E f') ∨ (E f ∧ E g')) :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 S)
      ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂)) := by
  apply P.pullbackMap_of_relative_alternatives E h₁ h₂ e₁ e₂
  rcases hE with ⟨hf, hf'⟩ | ⟨hf, hg'⟩
  · exact Or.inl ⟨hf, hf', HasPullbacksAlong.hasPullback (P := E) f' hf'⟩
  · exact Or.inr ⟨hf, hg', HasPullbacksAlong.hasPullback (P := E) f hf⟩

end Existence

section Absolute

variable {C : Type u} [Category.{v} C]
variable (P : MorphismProperty C)
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {S X X' Y Y' : C} {f : X ⟶ S} [Limits.HasPullbacksAlong f]
    {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S}
    {i₁ : X ⟶ X'} [Limits.HasPullbacksAlong g'] {i₂ : Y ⟶ Y'}
    (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g')

attribute [local instance] hasPullback_symmetry_of_hasPullbacksAlong in
/-- The `E = ⊤` cross alternative uses only Mathlib's existence hypotheses:
source existence follows by symmetry from pullbacks along `f`, and the mixed
and target spans exist along `g'`. -/
example :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 S)
      ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂)) := by
  exact P.pullbackMap_of_relative_alternatives_top h₁ h₂ e₁ e₂

attribute [local instance] hasPullback_symmetry_of_hasPullbacksAlong in
/-- Mathlib's absolute API concludes membership for exactly the same map
with the same hypotheses as the preceding relative specialization. -/
example :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 S)
      ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂)) := by
  exact P.pullbackMap h₁ h₂ e₁ e₂

end Absolute

section RestrictedPairing

variable {C : Type u} [Category.{v} C]
variable (E Q P : MorphismProperty C) [P.IsMultiplicative] (S : C)
variable [∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]
variable [P.IsStableUnderBaseChangeAgainst E] [(P ⊓ E).IsStableUnderBaseChange]
    [E.IsStableUnderBaseChange] [E.HasOfPostcompProperty E]

/-- Relative preservation supplies the horizontal witness for comma-category
lifting. No restriction is imposed on the output structure arrows, and forgetting
recovers the entire ordinary-over pairing. -/
example :
    let F : (E.Over P S × Q.Over P S) ⥤ (⊤ : MorphismProperty C).Over P S :=
      Comma.lift (Over.pullbackPairing E Q P S)
        (fun _ ↦ trivial)
        (fun f ↦ Over.pullbackPairing_map_mem_of_relative E Q P S f)
        (fun _ ↦ trivial)
    F ⋙ Over.forget ⊤ P S = Over.pullbackPairing E Q P S := rfl

end RestrictedPairing

section FiniteTypes

private def inclOne : Fin 1 ⟶ Fin 2 := TypeCat.ofHom fun _ => 0
private def inclTwo : Fin 2 ⟶ Fin 3 :=
  TypeCat.ofHom fun i => ⟨i.val, by omega⟩
private def collapse : Fin 3 ⟶ Fin 2 :=
  TypeCat.ofHom fun i => if i = 1 then 1 else 0

private lemma inclOne_mem : (monomorphisms (Type)) inclOne := by
  rw [monomorphisms.iff, mono_iff_injective]
  change Function.Injective (fun _ : Fin 1 => (0 : Fin 2))
  decide

private lemma inclTwo_mem : (monomorphisms (Type)) inclTwo := by
  rw [monomorphisms.iff, mono_iff_injective]
  intro i j h
  have hv := congrArg (fun k : Fin 3 => k.val) h
  change i.val = j.val at hv
  exact Fin.ext hv

private lemma collapse_not_mem : ¬ (monomorphisms (Type)) collapse := by
  rw [monomorphisms.iff, mono_iff_injective]
  intro h
  have heq : (0 : Fin 3) = 2 := h (by decide : collapse 0 = collapse 2)
  exact (by decide : (0 : Fin 3) ≠ 2) heq

private lemma inclOne_not_isIso : ¬ IsIso inclOne := by
  rw [isIso_iff_bijective]
  intro h
  obtain ⟨i, hi⟩ := h.2 1
  have : inclOne i = 0 := rfl
  exact (by decide : (0 : Fin 2) ≠ 1) (this.symm.trans hi)

private lemma inclTwo_not_isIso : ¬ IsIso inclTwo := by
  rw [isIso_iff_bijective]
  intro h
  obtain ⟨i, hi⟩ := h.2 2
  have hv := congrArg Fin.val hi
  change i.val = 2 at hv
  omega

private lemma inclTwo_comp_collapse : inclTwo ≫ collapse = 𝟙 (Fin 2) := by
  ext i
  fin_cases i <;> rfl

/-- Both input maps are proper inclusions; only the cross alternative holds.
The failed object alternative is witnessed by the noninjective target first leg. -/
example :
    (monomorphisms (Type)) inclTwo ∧
    (monomorphisms (Type)) inclOne ∧
    ¬ IsIso inclTwo ∧ ¬ IsIso inclOne ∧
    ¬ (monomorphisms (Type)) collapse ∧
    (monomorphisms (Type))
      (pullback.map (𝟙 (Fin 2)) inclOne collapse (𝟙 (Fin 2))
        inclTwo inclOne (𝟙 (Fin 2))
        ((Category.comp_id _).trans inclTwo_comp_collapse.symm)
        ((Category.comp_id _).trans (Category.comp_id inclOne).symm)) := by
  refine ⟨inclTwo_mem, inclOne_mem, inclTwo_not_isIso, inclOne_not_isIso,
    collapse_not_mem, ?_⟩
  exact (monomorphisms (Type)).pullbackMap_of_relative_alternatives
    (monomorphisms (Type)) inclTwo_mem inclOne_mem
    inclTwo_comp_collapse.symm (Category.comp_id inclOne).symm
    (Or.inr ⟨by infer_instance, by infer_instance, inferInstance⟩)

/-- The mirror configuration satisfies only the object alternative.
Its target second leg is noninjective, while both input maps are proper inclusions. -/
example :
    (monomorphisms (Type)) inclOne ∧
    (monomorphisms (Type)) inclTwo ∧
    ¬ IsIso inclOne ∧ ¬ IsIso inclTwo ∧
    ¬ (monomorphisms (Type)) collapse ∧
    (monomorphisms (Type))
      (pullback.map inclOne (𝟙 (Fin 2)) (𝟙 (Fin 2)) collapse
        inclOne inclTwo (𝟙 (Fin 2))
        ((Category.comp_id _).trans (Category.comp_id inclOne).symm)
        ((Category.comp_id _).trans inclTwo_comp_collapse.symm)) := by
  refine ⟨inclOne_mem, inclTwo_mem, inclOne_not_isIso, inclTwo_not_isIso,
    collapse_not_mem, ?_⟩
  exact (monomorphisms (Type)).pullbackMap_of_relative_alternatives
    (monomorphisms (Type)) inclOne_mem inclTwo_mem
    (Category.comp_id inclOne).symm inclTwo_comp_collapse.symm
    (Or.inl ⟨inclOne_mem, by infer_instance, inferInstance⟩)

private def pairingSource :
    (monomorphisms (Type)).Over (monomorphisms (Type)) (Fin 2) ×
      (⊤ : MorphismProperty (Type)).Over (monomorphisms (Type)) (Fin 2) :=
  (Over.mk (monomorphisms (Type)) inclOne inclOne_mem,
    Over.mk (monomorphisms (Type)) (𝟙 (Fin 2)) trivial)

private def pairingTarget :
    (monomorphisms (Type)).Over (monomorphisms (Type)) (Fin 2) ×
      (⊤ : MorphismProperty (Type)).Over (monomorphisms (Type)) (Fin 2) :=
  (Over.mk (monomorphisms (Type)) (𝟙 (Fin 2)) (by infer_instance),
    Over.mk (monomorphisms (Type)) collapse trivial)

private def pairingHorizontal : pairingSource ⟶ pairingTarget :=
  Prod.mkHom (Over.homMk inclOne (Category.comp_id inclOne) inclOne_mem)
    (Over.homMk inclTwo inclTwo_comp_collapse inclTwo_mem)

private noncomputable def pairingImage :=
  (Over.pullbackPairing (monomorphisms (Type)) ⊤ (monomorphisms (Type)) (Fin 2)).map
    pairingHorizontal

/-- The pairing's first projection recovers the first proper inclusion. -/
example : pairingImage.left ≫ pullback.fst pairingTarget.1.hom pairingTarget.2.hom =
    pullback.fst pairingSource.1.hom pairingSource.2.hom ≫ pairingHorizontal.1.left :=
  Over.pullbackPairing_map_fst (monomorphisms (Type)) ⊤ (monomorphisms (Type)) (Fin 2)
    pairingHorizontal

/-- The pairing's second projection recovers the second proper inclusion. -/
example : pairingImage.left ≫ pullback.snd pairingTarget.1.hom pairingTarget.2.hom =
    pullback.snd pairingSource.1.hom pairingSource.2.hom ≫ pairingHorizontal.2.left :=
  Over.pullbackPairing_map_snd (monomorphisms (Type)) ⊤ (monomorphisms (Type)) (Fin 2)
    pairingHorizontal

private lemma pairingImage_left_eq :
    pairingImage.left =
      pullback.map inclOne (𝟙 (Fin 2)) (𝟙 (Fin 2)) collapse
        inclOne inclTwo (𝟙 (Fin 2))
        ((Category.comp_id _).trans (Category.comp_id inclOne).symm)
        ((Category.comp_id _).trans inclTwo_comp_collapse.symm) :=
  Over.pullbackPairing_map_left (monomorphisms (Type)) ⊤ (monomorphisms (Type)) (Fin 2)
    pairingHorizontal

-- Membership is independently witnessed by the existing two-factor theorem.
private lemma pairingImage_mem : (monomorphisms (Type)) pairingImage.left := by
  rw [pairingImage_left_eq]
  exact (monomorphisms (Type)).pullbackMap_of_relative_alternatives
    (monomorphisms (Type)) inclOne_mem inclTwo_mem
    (Category.comp_id inclOne).symm inclTwo_comp_collapse.symm
    (Or.inl ⟨inclOne_mem, by infer_instance, inferInstance⟩)

/-- The pairing theorem preserves monomorphisms in the same asymmetric model. -/
example : (monomorphisms (Type)) pairingImage.left :=
  Over.pullbackPairing_map_mem_of_relative (monomorphisms (Type)) ⊤
    (monomorphisms (Type)) (Fin 2) pairingHorizontal

private lemma pairingImage_not_surjective : ¬ Function.Surjective pairingImage.left := by
  intro h
  let y : Types.PullbackObj (𝟙 (Fin 2)) collapse := ⟨(1, 1), by decide⟩
  obtain ⟨x, hx⟩ := h ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv y)
  have hfst : pullback.fst (𝟙 (Fin 2)) collapse (pairingImage.left x) = (0 : Fin 2) :=
    ConcreteCategory.congr_hom (Over.pullbackPairing_map_fst (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2) pairingHorizontal) x
  rw [hx] at hfst
  have hy : pullback.fst (𝟙 (Fin 2)) collapse
      ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv y) = (1 : Fin 2) :=
    ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst (𝟙 (Fin 2)) collapse) y
  exact (by decide : (1 : Fin 2) ≠ 0) (hy.symm.trans hfst)

private lemma pairingImage_not_isIso : ¬ IsIso pairingImage.left := by
  rw [isIso_iff_bijective]
  exact fun h ↦ pairingImage_not_surjective h.2

/-- Both pairing factors are proper monomorphisms, while the right target
structure map is not mono. The image is mono but misses a point in the target
pullback, so it is neither an identity nor an isomorphism. -/
example :
    (monomorphisms (Type)) pairingHorizontal.1.left ∧
    (monomorphisms (Type)) pairingHorizontal.2.left ∧
    ¬ IsIso pairingHorizontal.1.left ∧ ¬ IsIso pairingHorizontal.2.left ∧
    ¬ (monomorphisms (Type)) pairingTarget.2.hom ∧
    (monomorphisms (Type)) pairingImage.left ∧
    ¬ Function.Surjective pairingImage.left ∧ ¬ IsIso pairingImage.left :=
  ⟨inclOne_mem, inclTwo_mem, inclOne_not_isIso, inclTwo_not_isIso,
    collapse_not_mem, pairingImage_mem, pairingImage_not_surjective, pairingImage_not_isIso⟩

set_option backward.isDefEq.respectTransparency false in
/-- The restricted-target lift retains the asymmetric pairing's object and map.
Its horizontal map is mono but still not surjective or an isomorphism. -/
example :
    let F :
        ((monomorphisms (Type)).Over (monomorphisms (Type)) (Fin 2) ×
          (⊤ : MorphismProperty (Type)).Over (monomorphisms (Type)) (Fin 2)) ⥤
            (⊤ : MorphismProperty (Type)).Over (monomorphisms (Type)) (Fin 2) :=
      Comma.lift
        (Over.pullbackPairing (monomorphisms (Type)) ⊤ (monomorphisms (Type)) (Fin 2))
        (fun _ ↦ trivial)
        (fun f ↦ Over.pullbackPairing_map_mem_of_relative (monomorphisms (Type)) ⊤
          (monomorphisms (Type)) (Fin 2) f)
        (fun _ ↦ trivial)
    (F.obj pairingTarget).toComma =
        (Over.pullbackPairing (monomorphisms (Type)) ⊤
          (monomorphisms (Type)) (Fin 2)).obj pairingTarget ∧
      (F.map pairingHorizontal).hom = pairingImage ∧
      (monomorphisms (Type)) (F.map pairingHorizontal).left ∧
      ¬ Function.Surjective (F.map pairingHorizontal).left ∧
      ¬ IsIso (F.map pairingHorizontal).left :=
  ⟨Comma.lift_obj_toComma .., Comma.lift_map_hom ..,
    pairingImage_mem, pairingImage_not_surjective, pairingImage_not_isIso⟩

private def fiberSwap : Fin 3 ⟶ Fin 3 :=
  TypeCat.ofHom fun i ↦ if i = 0 then 2 else if i = 2 then 0 else 1

private lemma fiberSwap_involutive : Function.Involutive fiberSwap := by
  intro i
  fin_cases i <;> rfl

private lemma fiberSwap_mem : (monomorphisms (Type)) fiberSwap := by
  rw [monomorphisms.iff, mono_iff_injective]
  exact fiberSwap_involutive.injective

private lemma fiberSwap_comp_collapse : fiberSwap ≫ collapse = collapse := by
  ext i
  fin_cases i <;> rfl

private def pairingEndomorphism : pairingTarget ⟶ pairingTarget :=
  Prod.mkHom (𝟙 pairingTarget.1)
    (Over.homMk fiberSwap fiberSwap_comp_collapse fiberSwap_mem)

private def targetPoint (y : Fin 3) : Types.PullbackObj (𝟙 (Fin 2)) collapse :=
  ⟨(collapse y, y), rfl⟩

private def reversedTargetPoint (y : Fin 3) :
    Types.PullbackObj collapse (𝟙 (Fin 2)) :=
  ⟨(y, collapse y), rfl⟩

/-- The explicit target graph consists of three distinct points. -/
example (q : Types.PullbackObj (𝟙 (Fin 2)) collapse) :
    q = targetPoint 0 ∨ q = targetPoint 1 ∨ q = targetPoint 2 := by
  rcases q with ⟨⟨x, y⟩, h⟩
  change x = collapse y at h
  subst x
  fin_cases y
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private lemma target_swap_point (y : Fin 3) :
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      ((pullbackSymmetry (𝟙 (Fin 2)) collapse).hom
        ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y))) =
      reversedTargetPoint y := by
  apply Subtype.ext
  apply Prod.ext
  · rw [Types.pullbackIsoPullback_hom_fst]
    exact (ConcreteCategory.congr_hom
      (pullbackSymmetry_hom_comp_fst (𝟙 (Fin 2)) collapse) _).trans
      (ConcreteCategory.congr_hom
        (Types.pullbackIsoPullback_inv_snd (𝟙 (Fin 2)) collapse) (targetPoint y))
  · rw [Types.pullbackIsoPullback_hom_snd]
    exact (ConcreteCategory.congr_hom
      (pullbackSymmetry_hom_comp_snd (𝟙 (Fin 2)) collapse) _).trans
      (ConcreteCategory.congr_hom
        (Types.pullbackIsoPullback_inv_fst (𝟙 (Fin 2)) collapse) (targetPoint y))

private lemma target_inverse_point (y : Fin 3) :
    (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).hom
      ((pullbackSymmetry (𝟙 (Fin 2)) collapse).inv
        ((Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv
          (reversedTargetPoint y))) = targetPoint y := by
  apply Subtype.ext
  apply Prod.ext
  · rw [Types.pullbackIsoPullback_hom_fst]
    exact (ConcreteCategory.congr_hom
      (pullbackSymmetry_inv_comp_fst (𝟙 (Fin 2)) collapse) _).trans
      (ConcreteCategory.congr_hom
        (Types.pullbackIsoPullback_inv_snd collapse (𝟙 (Fin 2)))
          (reversedTargetPoint y))
  · rw [Types.pullbackIsoPullback_hom_snd]
    exact (ConcreteCategory.congr_hom
      (pullbackSymmetry_inv_comp_snd (𝟙 (Fin 2)) collapse) _).trans
      (ConcreteCategory.congr_hom
        (Types.pullbackIsoPullback_inv_fst collapse (𝟙 (Fin 2)))
          (reversedTargetPoint y))

/-- Ambient symmetry sends `(0,2)` to `(2,0)`, and its inverse restores the
point, using ambient pullback symmetry. -/
example :
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      ((pullbackSymmetry (𝟙 (Fin 2)) collapse).hom
        ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv
          ⟨(0, 2), by decide⟩)) = ⟨(2, 0), by decide⟩ ∧
    (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).hom
      ((pullbackSymmetry (𝟙 (Fin 2)) collapse).inv
        ((Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv
          ⟨(2, 0), by decide⟩)) = ⟨(0, 2), by decide⟩ :=
  ⟨target_swap_point 2, target_inverse_point 2⟩

private def sourcePoint : Types.PullbackObj inclOne (𝟙 (Fin 2)) :=
  ⟨(0, 0), rfl⟩

/-- The proper-inclusion square sends the singleton source to `(0,0)` by
both routes, using only existing symmetry and projection equations. -/
example :
    let x := (Types.pullbackIsoPullback inclOne (𝟙 (Fin 2))).inv sourcePoint
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      ((pullbackSymmetry (𝟙 (Fin 2)) collapse).hom (pairingImage.left x)) =
        reversedTargetPoint 0 ∧
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      (((Over.pullbackPairing ⊤ (monomorphisms (Type))
        (monomorphisms (Type)) (Fin 2)).map
          ((Prod.swap _ _).map pairingHorizontal)).left
            ((pullbackSymmetry inclOne (𝟙 (Fin 2))).hom x)) =
      reversedTargetPoint 0 := by
  dsimp only
  have hx₁ := ConcreteCategory.congr_hom
    (Types.pullbackIsoPullback_inv_fst inclOne (𝟙 (Fin 2))) sourcePoint
  have hx₂ := ConcreteCategory.congr_hom
    (Types.pullbackIsoPullback_inv_snd inclOne (𝟙 (Fin 2))) sourcePoint
  constructor
  · apply Subtype.ext
    apply Prod.ext
    · rw [Types.pullbackIsoPullback_hom_fst]
      exact (ConcreteCategory.congr_hom
        (pullbackSymmetry_hom_comp_fst (𝟙 (Fin 2)) collapse) _).trans
        ((ConcreteCategory.congr_hom
          (Over.pullbackPairing_map_snd (monomorphisms (Type)) ⊤
            (monomorphisms (Type)) (Fin 2) pairingHorizontal) _).trans
          (congrArg inclTwo hx₂))
    · rw [Types.pullbackIsoPullback_hom_snd]
      exact (ConcreteCategory.congr_hom
        (pullbackSymmetry_hom_comp_snd (𝟙 (Fin 2)) collapse) _).trans
        ((ConcreteCategory.congr_hom
          (Over.pullbackPairing_map_fst (monomorphisms (Type)) ⊤
            (monomorphisms (Type)) (Fin 2) pairingHorizontal) _).trans
          (congrArg inclOne hx₁))
  · apply Subtype.ext
    apply Prod.ext
    · exact (Types.pullbackIsoPullback_hom_fst collapse (𝟙 (Fin 2)) _).trans
        ((ConcreteCategory.congr_hom
          (Over.pullbackPairing_map_fst ⊤ (monomorphisms (Type))
            (monomorphisms (Type)) (Fin 2)
              ((Prod.swap _ _).map pairingHorizontal)) _).trans
          (congrArg inclTwo ((ConcreteCategory.congr_hom
            (pullbackSymmetry_hom_comp_fst inclOne (𝟙 (Fin 2))) _).trans hx₂)))
    · exact (Types.pullbackIsoPullback_hom_snd collapse (𝟙 (Fin 2)) _).trans
        ((ConcreteCategory.congr_hom
          (Over.pullbackPairing_map_snd ⊤ (monomorphisms (Type))
            (monomorphisms (Type)) (Fin 2)
              ((Prod.swap _ _).map pairingHorizontal)) _).trans
          (congrArg inclOne ((ConcreteCategory.congr_hom
            (pullbackSymmetry_hom_comp_snd inclOne (𝟙 (Fin 2))) _).trans hx₁)))

private lemma target_map_point (y : Fin 3) :
    (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).hom
      (((Over.pullbackPairing (monomorphisms (Type)) ⊤
        (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism).left
          ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y))) =
      targetPoint (fiberSwap y) := by
  apply Subtype.ext
  apply Prod.ext
  · let x : pullback (𝟙 (Fin 2)) collapse :=
      (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y)
    have hmap :
        pullback.fst (𝟙 (Fin 2)) collapse
          (((Over.pullbackPairing (monomorphisms (Type)) ⊤
            (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism).left x) =
          pullback.fst (𝟙 (Fin 2)) collapse x :=
      ConcreteCategory.congr_hom
        (Over.pullbackPairing_map_fst (monomorphisms (Type)) ⊤
          (monomorphisms (Type)) (Fin 2)
          (A := pairingTarget) (B := pairingTarget) pairingEndomorphism) x
    have hinv : pullback.fst (𝟙 (Fin 2)) collapse x = collapse y :=
      ConcreteCategory.congr_hom
        (Types.pullbackIsoPullback_inv_fst (𝟙 (Fin 2)) collapse) (targetPoint y)
    have hcollapse : collapse y = collapse (fiberSwap y) :=
      (ConcreteCategory.congr_hom fiberSwap_comp_collapse y).symm
    exact (Types.pullbackIsoPullback_hom_fst (𝟙 (Fin 2)) collapse
      (((Over.pullbackPairing (monomorphisms (Type)) ⊤
        (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism).left x)).trans
      (hmap.trans (hinv.trans hcollapse))
  · exact (Types.pullbackIsoPullback_hom_snd (𝟙 (Fin 2)) collapse _).trans
      ((ConcreteCategory.congr_hom
        (Over.pullbackPairing_map_snd (monomorphisms (Type)) ⊤
          (monomorphisms (Type)) (Fin 2) pairingEndomorphism) _).trans
        (congrArg fiberSwap (ConcreteCategory.congr_hom
          (Types.pullbackIsoPullback_inv_snd (𝟙 (Fin 2)) collapse) (targetPoint y))))

private lemma reversed_target_map_point (y : Fin 3) :
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      (((Over.pullbackPairing ⊤ (monomorphisms (Type))
        (monomorphisms (Type)) (Fin 2)).map
          ((Prod.swap _ _).map pairingEndomorphism)).left
            ((Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv
              (reversedTargetPoint y))) = reversedTargetPoint (fiberSwap y) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Types.pullbackIsoPullback_hom_fst collapse (𝟙 (Fin 2)) _).trans
      ((ConcreteCategory.congr_hom
        (Over.pullbackPairing_map_fst ⊤ (monomorphisms (Type))
          (monomorphisms (Type)) (Fin 2)
            ((Prod.swap _ _).map pairingEndomorphism)) _).trans
        (congrArg fiberSwap (ConcreteCategory.congr_hom
          (Types.pullbackIsoPullback_inv_fst collapse (𝟙 (Fin 2)))
            (reversedTargetPoint y))))
  · let x : pullback collapse (𝟙 (Fin 2)) :=
      (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv (reversedTargetPoint y)
    have hmap :
        pullback.snd collapse (𝟙 (Fin 2))
          (((Over.pullbackPairing ⊤ (monomorphisms (Type))
            (monomorphisms (Type)) (Fin 2)).map
              ((Prod.swap _ _).map pairingEndomorphism)).left x) =
          pullback.snd collapse (𝟙 (Fin 2)) x :=
      ConcreteCategory.congr_hom
        (Over.pullbackPairing_map_snd ⊤ (monomorphisms (Type))
          (monomorphisms (Type)) (Fin 2)
          (A := (pairingTarget.2, pairingTarget.1))
          (B := (pairingTarget.2, pairingTarget.1))
          ((Prod.swap _ _).map pairingEndomorphism)) x
    have hinv : pullback.snd collapse (𝟙 (Fin 2)) x = collapse y :=
      ConcreteCategory.congr_hom
        (Types.pullbackIsoPullback_inv_snd collapse (𝟙 (Fin 2))) (reversedTargetPoint y)
    have hcollapse : collapse y = collapse (fiberSwap y) :=
      (ConcreteCategory.congr_hom fiberSwap_comp_collapse y).symm
    exact (Types.pullbackIsoPullback_hom_snd collapse (𝟙 (Fin 2))
      (((Over.pullbackPairing ⊤ (monomorphisms (Type))
        (monomorphisms (Type)) (Fin 2)).map
          ((Prod.swap _ _).map pairingEndomorphism)).left x)).trans
      (hmap.trans (hinv.trans hcollapse))

/-- The additional horizontal morphism is mono, exchanges the two points over
`0`, and fixes the point over `1`. Both graph maps therefore move two points. -/
example :
    (monomorphisms (Type)) pairingEndomorphism.2.left ∧
    fiberSwap 0 = 2 ∧ fiberSwap 1 = 1 ∧ fiberSwap 2 = 0 ∧
    targetPoint 0 ≠ targetPoint 2 ∧ reversedTargetPoint 0 ≠ reversedTargetPoint 2 := by
  refine ⟨fiberSwap_mem, rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (congrArg (fun q ↦ q.val.2) h)
  · intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (congrArg (fun q ↦ q.val.1) h)

/-- The nonconstant three-point square commutes in coordinates using only the
existing pullback symmetry and pairing projections. -/
example (y : Fin 3) :
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      ((pullbackSymmetry (𝟙 (Fin 2)) collapse).hom
        (((Over.pullbackPairing (monomorphisms (Type)) ⊤
          (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism).left
            ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y)))) =
      reversedTargetPoint (fiberSwap y) ∧
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      (((Over.pullbackPairing ⊤ (monomorphisms (Type))
        (monomorphisms (Type)) (Fin 2)).map
          ((Prod.swap _ _).map pairingEndomorphism)).left
            ((pullbackSymmetry (𝟙 (Fin 2)) collapse).hom
              ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y)))) =
      reversedTargetPoint (fiberSwap y) := by
  have hm :
      ((Over.pullbackPairing (monomorphisms (Type)) ⊤
        (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism).left
          ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y)) =
        (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv
          (targetPoint (fiberSwap y)) :=
    (ConcreteCategory.congr_hom
      (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).hom_inv_id _).symm.trans
        (congrArg (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv
          (target_map_point y))
  have hs :
      (pullbackSymmetry (𝟙 (Fin 2)) collapse).hom
        ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint y)) =
        (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv
          (reversedTargetPoint y) :=
    (ConcreteCategory.congr_hom
      (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom_inv_id _).symm.trans
        (congrArg (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv
          (target_swap_point y))
  constructor
  · rw [hm]
    exact target_swap_point (fiberSwap y)
  · rw [hs]
    exact reversed_target_map_point y

/-- Naturality on the two proper inclusions uses the reversed ordinary-over
pairing map. -/
example :
    pairingImage ≫
        (Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
          (monomorphisms (Type)) (Fin 2)).hom.app pairingTarget =
      (Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
        (monomorphisms (Type)) (Fin 2)).hom.app pairingSource ≫
          (Over.pullbackPairing ⊤ (monomorphisms (Type))
            (monomorphisms (Type)) (Fin 2)).map
              ((Prod.swap _ _).map pairingHorizontal) :=
  (Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
    (monomorphisms (Type)) (Fin 2)).hom.naturality pairingHorizontal

/-- Naturality applies to the nonconstant endomorphism of the three-point
graph in both directions. -/
example :
    let σ := Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2)
    (Over.pullbackPairing (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism ≫ σ.hom.app pairingTarget =
        σ.hom.app pairingTarget ≫
          (Over.pullbackPairing ⊤ (monomorphisms (Type))
            (monomorphisms (Type)) (Fin 2)).map
              ((Prod.swap _ _).map pairingEndomorphism) ∧
    (Over.pullbackPairing ⊤ (monomorphisms (Type))
      (monomorphisms (Type)) (Fin 2)).map
        ((Prod.swap _ _).map pairingEndomorphism) ≫ σ.inv.app pairingTarget =
          σ.inv.app pairingTarget ≫
            (Over.pullbackPairing (monomorphisms (Type)) ⊤
              (monomorphisms (Type)) (Fin 2)).map pairingEndomorphism :=
  ⟨(Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2)).hom.naturality pairingEndomorphism,
    (Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2)).inv.naturality pairingEndomorphism⟩

/-- Normalization through the characteristic left-map API sends
`(0,2)` to `(2,0)` and restores it through the inverse. -/
example :
    let σ := Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2)
    (Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).hom
      ((σ.hom.app pairingTarget).left
        ((Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).inv (targetPoint 2))) =
      reversedTargetPoint 2 ∧
    (Types.pullbackIsoPullback (𝟙 (Fin 2)) collapse).hom
      ((σ.inv.app pairingTarget).left
        ((Types.pullbackIsoPullback collapse (𝟙 (Fin 2))).inv
          (reversedTargetPoint 2))) = targetPoint 2 := by
  dsimp only
  rw [Over.pullbackPairingSymmetry_hom_app_left,
    Over.pullbackPairingSymmetry_inv_app_left]
  exact ⟨target_swap_point 2, target_inverse_point 2⟩

/-- Normalization through the characteristic projection API
identifies both coordinates, and the reversed component restores the object. -/
example :
    let σ := Over.pullbackPairingSymmetry (monomorphisms (Type)) ⊤
      (monomorphisms (Type)) (Fin 2)
    (σ.hom.app pairingTarget).left ≫ pullback.fst collapse (𝟙 (Fin 2)) =
        pullback.snd (𝟙 (Fin 2)) collapse ∧
    (σ.hom.app pairingTarget).left ≫ pullback.snd collapse (𝟙 (Fin 2)) =
        pullback.fst (𝟙 (Fin 2)) collapse ∧
    σ.hom.app pairingTarget ≫
        (Over.pullbackPairingSymmetry ⊤ (monomorphisms (Type))
          (monomorphisms (Type)) (Fin 2)).hom.app
            (pairingTarget.2, pairingTarget.1) =
      𝟙 ((Over.pullbackPairing (monomorphisms (Type)) ⊤
        (monomorphisms (Type)) (Fin 2)).obj pairingTarget) := by
  exact ⟨Over.pullbackPairingSymmetry_hom_app_fst _ _ _ _ _ _,
    Over.pullbackPairingSymmetry_hom_app_snd _ _ _ _ _ _,
    Over.pullbackPairingSymmetry_hom_app_comp_swap _ _ _ _ _ _⟩

end FiniteTypes

end CategoryTheory.MorphismProperty.PullbackMapExamples

namespace CategoryTheory.MorphismProperty.FourChain

open Limits

-- The nonidentity arrows in `P` start at `0`, so two such arrows cannot compose.
local instance : P.IsStableUnderComposition where
  comp_mem {a b c} f g hf hg := by
    rw [p_iff] at hf hg ⊢
    rcases hf with hab | ⟨ha, hb⟩
    · simpa [hab] using hg
    · rcases hg with hbc | ⟨hb', _⟩
      · exact Or.inr ⟨ha, hbc ▸ hb⟩
      · rcases hb with hb | hb <;> omega

/-- A non-absolutely-stable property preserves the canonical map `0 ⟶ 1`.
The first input factor is an identity, and the second is `0 ⟶ 3`. -/
example :
    ¬ P.IsStableUnderBaseChange ∧
    P (pullback.map oneThree zeroThree oneThree (𝟙 (3 : Fin 4))
      (𝟙 (1 : Fin 4)) zeroThree (𝟙 (3 : Fin 4))
      (by subsingleton) (by subsingleton)) ∧
    ¬ IsIso (pullback.map oneThree zeroThree oneThree (𝟙 (3 : Fin 4))
      (𝟙 (1 : Fin 4)) zeroThree (𝟙 (3 : Fin 4))
      (by subsingleton) (by subsingleton)) := by
  refine ⟨not_isStableUnderBaseChange, ?_, ?_⟩
  · exact P.pullbackMap_of_relative_alternatives E
      (by simp) (by simp) (by subsingleton) (by subsingleton)
      (Or.inl ⟨by simp, by simp, inferInstance⟩)
  · rw [PartialOrder.isIso_iff_eq, CompleteLattice.pullback_eq_inf,
      CompleteLattice.pullback_eq_inf]
    decide

end CategoryTheory.MorphismProperty.FourChain

namespace CategoryTheory.MorphismProperty.NonemptyFinsets

open Limits

local instance : HasPullback v12 f := HasLimit.mk ⟨xPullbackCone, xPullbackIsLimit⟩
local instance : HasPullback v22 f := HasLimit.mk ⟨yPullbackCone, yPullbackIsLimit⟩

/-- Both input inclusions change the objects, although the category has no
pullbacks for all spans. The selected mixed span is the two-element intersection
cone, and the target span consists of two identity arrows. -/
example :
    ¬ Limits.HasPullbacks C ∧ ¬ IsIso v12 ∧ ¬ IsIso f ∧
    (monomorphisms C) (pullback.map v12 f v22 v22 v12 f (𝟙 S)
      (by subsingleton) (by subsingleton)) := by
  refine ⟨not_hasPullbacks, ?_, f_not_isIso, ?_⟩
  · rw [PartialOrder.isIso_iff_eq]
    decide
  · exact (monomorphisms C).pullbackMap_of_relative_alternatives
      (monomorphisms C) (by infer_instance) (by infer_instance)
      (by subsingleton) (by subsingleton)
      (Or.inl ⟨by infer_instance, by infer_instance, inferInstance⟩)

end CategoryTheory.MorphismProperty.NonemptyFinsets

namespace CategoryTheory.MorphismProperty.PullbackMapExamples.ProjectionFan

open Limits

private abbrev Input :=
  (⊤ : MorphismProperty (Type)).Over (monomorphisms (Type)) (Fin 2) ×
    (⊤ : MorphismProperty (Type)).Over (monomorphisms (Type)) (Fin 2)

private abbrev x : Fin 3 ⟶ Fin 2 :=
  TypeCat.ofHom fun i ↦ if i = 2 then 1 else 0

private abbrev y : Fin 4 ⟶ Fin 2 :=
  TypeCat.ofHom fun i ↦ if i = 1 ∨ i = 2 then 1 else 0

private abbrev inclusion : Fin 2 ⟶ Fin 3 :=
  TypeCat.ofHom fun i ↦ if i = 0 then 0 else 2

private abbrev swap : Fin 3 ⟶ Fin 3 :=
  TypeCat.ofHom fun i ↦ if i = 0 then 1 else if i = 1 then 0 else 2

private lemma inclusion_injective : Function.Injective inclusion := by
  decide

private lemma inclusion_mem : (monomorphisms (Type)) inclusion := by
  rw [monomorphisms.iff, mono_iff_injective]
  exact inclusion_injective

private lemma inclusion_comp_x : inclusion ≫ x = 𝟙 (Fin 2) := by
  ext i
  fin_cases i <;> rfl

/-- The horizontal inclusion is a proper monomorphism and preserves the two
base points. -/
example :
    (monomorphisms (Type)) inclusion ∧ ¬ IsIso inclusion ∧
    inclusion 0 = 0 ∧ inclusion 1 = 2 := by
  refine ⟨inclusion_mem, ?_, rfl, rfl⟩
  rw [isIso_iff_bijective]
  intro h
  obtain ⟨i, hi⟩ := h.2 1
  fin_cases i
  · exact (by decide : inclusion 0 ≠ 1) hi
  · exact (by decide : inclusion 1 ≠ 1) hi

private lemma swap_involutive : Function.Involutive swap := by
  intro i
  fin_cases i <;> rfl

private lemma swap_mem : (monomorphisms (Type)) swap := by
  rw [monomorphisms.iff, mono_iff_injective]
  exact swap_involutive.injective

private lemma swap_comp_x : swap ≫ x = x := by
  ext i
  fin_cases i <;> rfl

private abbrev source : Input :=
  ({ left := Fin 2, right := ⟨⟨⟩⟩, hom := 𝟙 (Fin 2), prop := trivial },
    { left := Fin 4, right := ⟨⟨⟩⟩, hom := y, prop := trivial })

private abbrev target : Input :=
  ({ left := Fin 3, right := ⟨⟨⟩⟩, hom := x, prop := trivial },
    { left := Fin 4, right := ⟨⟨⟩⟩, hom := y, prop := trivial })

private abbrev inclusionHorizontal : source ⟶ target :=
  Prod.mkHom (Over.homMk inclusion inclusion_comp_x inclusion_mem) (𝟙 source.2)

private abbrev swapHorizontal : target ⟶ target :=
  Prod.mkHom (Over.homMk swap swap_comp_x swap_mem) (𝟙 target.2)

private noncomputable abbrev inclusionImage :=
  (Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map inclusionHorizontal

private noncomputable abbrev swapImage :=
  (Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map swapHorizontal

private lemma inclusionHorizontal_fst_left : inclusionHorizontal.1.left = inclusion := by
  calc
    _ = (CategoryTheory.Over.homMk (U := source.1.toComma) (V := target.1.toComma)
        inclusion inclusion_comp_x).left :=
      (Comma.Hom.hom_left inclusionHorizontal.1).symm.trans
        (congrArg CategoryTheory.Over.Hom.left
          (Over.homMk_hom (A := source.1) (B := target.1)
            inclusion inclusion_comp_x inclusion_mem))
    _ = inclusion :=
      CategoryTheory.Over.homMk_left (U := source.1.toComma) (V := target.1.toComma)
        inclusion inclusion_comp_x

private lemma inclusionHorizontal_snd_left : inclusionHorizontal.2.left = 𝟙 (Fin 4) := by
  calc
    _ = CategoryTheory.Over.Hom.left (𝟙 source.2.toComma) :=
      (Comma.Hom.hom_left inclusionHorizontal.2).symm.trans
        (congrArg CategoryTheory.Over.Hom.left (Comma.id_hom source.2))
    _ = 𝟙 (Fin 4) := CategoryTheory.Over.id_left source.2.toComma

private lemma swapHorizontal_fst_left : swapHorizontal.1.left = swap := by
  calc
    _ = (CategoryTheory.Over.homMk (U := target.1.toComma) (V := target.1.toComma)
        swap swap_comp_x).left :=
      (Comma.Hom.hom_left swapHorizontal.1).symm.trans
        (congrArg CategoryTheory.Over.Hom.left
          (Over.homMk_hom (A := target.1) (B := target.1) swap swap_comp_x swap_mem))
    _ = swap :=
      CategoryTheory.Over.homMk_left (U := target.1.toComma) (V := target.1.toComma)
        swap swap_comp_x

private lemma swapHorizontal_snd_left : swapHorizontal.2.left = 𝟙 (Fin 4) := by
  calc
    _ = CategoryTheory.Over.Hom.left (𝟙 target.2.toComma) :=
      (Comma.Hom.hom_left swapHorizontal.2).symm.trans
        (congrArg CategoryTheory.Over.Hom.left (Comma.id_hom target.2))
    _ = 𝟙 (Fin 4) := CategoryTheory.Over.id_left target.2.toComma

private lemma iso_hom_inv_apply {X Y : Type} (e : X ≅ Y) (q : Y) :
    e.hom (e.inv q) = q := by
  simpa only [types_comp_apply, types_id_apply] using
    ConcreteCategory.congr_hom e.inv_hom_id q

private lemma iso_inv_equiv_apply {X Y : Type} (e : X ≅ Y) (p : X) :
    e.inv (e.toEquiv p) = p := by
  calc
    _ = e.inv (e.hom p) :=
      congrArg (fun q : Y ↦ e.inv q) (congrFun (Iso.toEquiv_fun e) p)
    _ = p := by
      simpa only [types_comp_apply, types_id_apply] using
        ConcreteCategory.congr_hom e.hom_inv_id p

private lemma fst_map {A B : Input} (f : A ⟶ B)
    (p : pullback A.1.hom A.2.hom) :
    pullback.fst B.1.hom B.2.hom
      (((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left p) =
        f.1.left (pullback.fst A.1.hom A.2.hom p) := by
  calc
    _ = (((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left ≫
        pullback.fst B.1.hom B.2.hom) p :=
      (ConcreteCategory.comp_apply (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left
        (pullback.fst B.1.hom B.2.hom) p).symm
    _ = (pullback.fst A.1.hom A.2.hom ≫ f.1.left) p :=
      ConcreteCategory.congr_hom (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (Over.pullbackPairing_map_fst ⊤ ⊤ (monomorphisms (Type)) (Fin 2) f) p
    _ = _ :=
      ConcreteCategory.comp_apply (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (pullback.fst A.1.hom A.2.hom) f.1.left p

private lemma snd_map {A B : Input} (f : A ⟶ B)
    (p : pullback A.1.hom A.2.hom) :
    pullback.snd B.1.hom B.2.hom
      (((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left p) =
        f.2.left (pullback.snd A.1.hom A.2.hom p) := by
  calc
    _ = (((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left ≫
        pullback.snd B.1.hom B.2.hom) p :=
      (ConcreteCategory.comp_apply (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left
        (pullback.snd B.1.hom B.2.hom) p).symm
    _ = (pullback.snd A.1.hom A.2.hom ≫ f.2.left) p :=
      ConcreteCategory.congr_hom (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (Over.pullbackPairing_map_snd ⊤ ⊤ (monomorphisms (Type)) (Fin 2) f) p
    _ = _ :=
      ConcreteCategory.comp_apply (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (pullback.snd A.1.hom A.2.hom) f.2.left p

private lemma fst_apply (A : Input) (q : Types.PullbackObj A.1.hom A.2.hom) :
    ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app A).left
      ((Types.pullbackIsoPullback A.1.hom A.2.hom).inv q) = q.val.1 := by
  rw [Over.pullbackPairingFst_app_left]
  exact ConcreteCategory.congr_hom
    (Types.pullbackIsoPullback_inv_fst A.1.hom A.2.hom) q

private lemma snd_apply (A : Input) (q : Types.PullbackObj A.1.hom A.2.hom) :
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app A).left
      ((Types.pullbackIsoPullback A.1.hom A.2.hom).inv q) = q.val.2 := by
  rw [Over.pullbackPairingSnd_app_left]
  exact ConcreteCategory.congr_hom
    (Types.pullbackIsoPullback_inv_snd A.1.hom A.2.hom) q

private lemma fst_map_apply {A B : Input} (f : A ⟶ B)
    (q : Types.PullbackObj A.1.hom A.2.hom) :
    ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app B).left
      (((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left
        ((Types.pullbackIsoPullback A.1.hom A.2.hom).inv q)) = f.1.left q.val.1 := by
  rw [Over.pullbackPairingFst_app_left]
  exact (fst_map f _).trans
    (congrArg f.1.left (ConcreteCategory.congr_hom
      (Types.pullbackIsoPullback_inv_fst A.1.hom A.2.hom) q))

private lemma snd_map_apply {A B : Input} (f : A ⟶ B)
    (q : Types.PullbackObj A.1.hom A.2.hom) :
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app B).left
      (((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map f).left
        ((Types.pullbackIsoPullback A.1.hom A.2.hom).inv q)) = f.2.left q.val.2 := by
  rw [Over.pullbackPairingSnd_app_left]
  exact (snd_map f _).trans
    (congrArg f.2.left (ConcreteCategory.congr_hom
      (Types.pullbackIsoPullback_inv_snd A.1.hom A.2.hom) q))

private lemma inclusion_fst_apply (q : Types.PullbackObj (𝟙 (Fin 2)) y) :
    ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (inclusionImage.left ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q)) =
        inclusion q.val.1 :=
  (fst_map_apply (A := source) (B := target) inclusionHorizontal q).trans
    (ConcreteCategory.congr_hom (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
      inclusionHorizontal_fst_left q.val.1)

private lemma inclusion_snd_apply (q : Types.PullbackObj (𝟙 (Fin 2)) y) :
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (inclusionImage.left ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q)) = q.val.2 :=
  (snd_map_apply (A := source) (B := target) inclusionHorizontal q).trans
    ((ConcreteCategory.congr_hom (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
      inclusionHorizontal_snd_left q.val.2).trans
        (ConcreteCategory.id_apply (C := Type) (FC := TypeCat.Fun)
          (CC := fun X ↦ X) (X := Fin 4) q.val.2))

private lemma swap_fst_apply (q : Types.PullbackObj x y) :
    ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (swapImage.left ((Types.pullbackIsoPullback x y).inv q)) = swap q.val.1 :=
  (fst_map_apply (A := target) (B := target) swapHorizontal q).trans
    (ConcreteCategory.congr_hom (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
      swapHorizontal_fst_left q.val.1)

private lemma swap_snd_apply (q : Types.PullbackObj x y) :
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (swapImage.left ((Types.pullbackIsoPullback x y).inv q)) = q.val.2 :=
  (snd_map_apply (A := target) (B := target) swapHorizontal q).trans
    ((ConcreteCategory.congr_hom (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
      swapHorizontal_snd_left q.val.2).trans
        (ConcreteCategory.id_apply (C := Type) (FC := TypeCat.Fun)
          (CC := fun X ↦ X) (X := Fin 4) q.val.2))

/-- Both structure functions are nonconstant, and the two pullback coordinates
vary independently over the first base point. -/
example :
    x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1 ∧
    y 0 = 0 ∧ y 1 = 1 ∧ y 2 = 1 ∧ y 3 = 0 ∧
    (⟨(0, 0), by decide⟩ : Types.PullbackObj x y) ≠ ⟨(1, 0), by decide⟩ ∧
    (⟨(0, 0), by decide⟩ : Types.PullbackObj x y) ≠ ⟨(0, 3), by decide⟩ := by
  decide

@[instance_reducible]
private noncomputable def targetFintype :
    Fintype ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left :=
  Fintype.ofEquiv (Types.PullbackObj x y) (Types.pullbackIsoPullback x y).toEquiv.symm

@[instance_reducible]
private noncomputable def sourceFintype :
    Fintype ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj source).left :=
  Fintype.ofEquiv (Types.PullbackObj (𝟙 (Fin 2)) y)
    (Types.pullbackIsoPullback (𝟙 (Fin 2)) y).toEquiv.symm

attribute [local instance] targetFintype sourceFintype

private lemma base_apply (q : Types.PullbackObj x y) :
    ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).hom
      ((Types.pullbackIsoPullback x y).inv q) = x q.val.1 := by
  rw [Over.pullbackPairing_obj_hom]
  exact congrArg x (ConcreteCategory.congr_hom
    (Types.pullbackIsoPullback_inv_fst x y) q)

private noncomputable def fiberEquiv (b : Fin 2) :
    {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
      ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).hom p = b} ≃
    {q : Types.PullbackObj x y // x q.val.1 = b} :=
  Equiv.subtypeEquiv (Types.pullbackIsoPullback x y).toEquiv (fun p ↦ by
    have h := base_apply ((Types.pullbackIsoPullback x y).toEquiv p)
    rw [iso_inv_equiv_apply (Types.pullbackIsoPullback x y) p] at h
    rw [h]
    rfl)

@[instance_reducible]
private noncomputable def fiberFintype (b : Fin 2) :
    Fintype
      {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
        ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).hom p = b} :=
  Fintype.ofEquiv {q : Types.PullbackObj x y // x q.val.1 = b} (fiberEquiv b).symm

attribute [local instance] fiberFintype

/-- The chosen target pullback has six points, with fibers of sizes four and two.
The source of the proper inclusion has four points. -/
example :
    Fintype.card
      ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left = 6 ∧
    Fintype.card
      {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
        ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).hom p = 0} = 4 ∧
    Fintype.card
      {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
        ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).hom p = 1} = 2 ∧
    Fintype.card
      ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj source).left = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Fintype.card_congr
      (α := ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left)
      (Types.pullbackIsoPullback x y).toEquiv).trans
      (by decide : Fintype.card (Types.PullbackObj x y) = 6)
  · exact (Fintype.card_congr (fiberEquiv 0)).trans
      (by decide : Fintype.card {q : Types.PullbackObj x y // x q.val.1 = 0} = 4)
  · exact (Fintype.card_congr (fiberEquiv 1)).trans
      (by decide : Fintype.card {q : Types.PullbackObj x y // x q.val.1 = 1} = 2)
  · exact (Fintype.card_congr
      (α := ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj source).left)
      (Types.pullbackIsoPullback (𝟙 (Fin 2)) y).toEquiv).trans
      (by decide : Fintype.card (Types.PullbackObj (𝟙 (Fin 2)) y) = 4)

/-- The two legs of the projection fan recover both coordinates at every target
point, without a condition on the projections as horizontal maps. -/
example (q : Types.PullbackObj x y) :
    ((Over.pullbackPairingFan ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).fst.app target).left
      ((Types.pullbackIsoPullback x y).inv q) = q.val.1 ∧
    ((Over.pullbackPairingFan ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).snd.app target).left
      ((Types.pullbackIsoPullback x y).inv q) = q.val.2 := by
  rw [Over.pullbackPairingFan_fst, Over.pullbackPairingFan_snd]
  exact ⟨fst_apply target q, snd_apply target q⟩

private lemma inclusion_coordinates (q : Types.PullbackObj (𝟙 (Fin 2)) y) :
    ((Types.pullbackIsoPullback x y).hom
      (inclusionImage.left ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q))).val =
      (inclusion q.val.1, q.val.2) := by
  apply Prod.ext
  · have h := inclusion_fst_apply q
    rw [Over.pullbackPairingFst_app_left] at h
    exact (Types.pullbackIsoPullback_hom_fst x y _).trans h
  · have h := inclusion_snd_apply q
    rw [Over.pullbackPairingSnd_app_left] at h
    exact (Types.pullbackIsoPullback_hom_snd x y _).trans h

/-- Each projection naturality square for the proper inclusion has both routes
normalized on every source point. -/
example (q : Types.PullbackObj (𝟙 (Fin 2)) y) :
    ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (inclusionImage.left ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q)) =
        inclusion q.val.1 ∧
    inclusion
      (((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app source).left
        ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q)) = inclusion q.val.1 ∧
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (inclusionImage.left ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q)) = q.val.2 ∧
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app source).left
      ((Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q) = q.val.2 := by
  refine ⟨?_, congrArg inclusion (fst_apply source q), ?_, snd_apply source q⟩
  · exact inclusion_fst_apply q
  · exact inclusion_snd_apply q

private lemma inclusionImage_injective : Function.Injective inclusionImage.left := by
  intro p q h
  apply PullbackCone.IsLimit.type_ext (pullbackIsPullback (𝟙 (Fin 2)) y)
  · apply inclusion_injective
    have hp := fst_map inclusionHorizontal p
    have hq := fst_map inclusionHorizontal q
    rw [inclusionHorizontal_fst_left] at hp hq
    exact (hp.symm.trans
      (congrArg (fun z : pullback x y ↦ pullback.fst x y z) h)).trans hq
  · have hp := snd_map inclusionHorizontal p
    have hq := snd_map inclusionHorizontal q
    rw [inclusionHorizontal_snd_left, types_id_apply] at hp hq
    exact (hp.symm.trans
      (congrArg (fun z : pullback x y ↦ pullback.snd x y z) h)).trans hq

private lemma inclusion_ne_one (a : Fin 2) : inclusion a ≠ 1 := by
  fin_cases a <;> decide

private lemma inclusionImage_not_surjective : ¬ Function.Surjective inclusionImage.left := by
  intro h
  let q : Types.PullbackObj x y := ⟨(1, 0), by decide⟩
  obtain ⟨p, hp⟩ := h ((Types.pullbackIsoPullback x y).inv q)
  have hfst := fst_map inclusionHorizontal p
  rw [inclusionHorizontal_fst_left, hp] at hfst
  exact inclusion_ne_one _ (hfst.symm.trans
    (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst x y) q))

private lemma inclusionImage_nonconstant :
    ∃ p q, inclusionImage.left p ≠ inclusionImage.left q := by
  let p : Types.PullbackObj (𝟙 (Fin 2)) y := ⟨(0, 0), by decide⟩
  let q : Types.PullbackObj (𝟙 (Fin 2)) y := ⟨(1, 1), by decide⟩
  refine ⟨(Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv p,
    (Types.pullbackIsoPullback (𝟙 (Fin 2)) y).inv q, ?_⟩
  intro h
  have hc := congrArg (fun z ↦ ((Types.pullbackIsoPullback x y).hom z).val.1) h
  have hp := congrArg _root_.Prod.fst (inclusion_coordinates p)
  have hq := congrArg _root_.Prod.fst (inclusion_coordinates q)
  exact (by decide : inclusion p.val.1 ≠ inclusion q.val.1) ((hp.symm.trans hc).trans hq)

/-- The induced four-to-six map is injective and nonconstant, but misses the
point with coordinates `(1,0)` and is not an isomorphism. -/
example :
    Function.Injective inclusionImage.left ∧
    ¬ Function.Surjective inclusionImage.left ∧ ¬ IsIso inclusionImage.left ∧
    ∃ p q, inclusionImage.left p ≠ inclusionImage.left q := by
  refine ⟨inclusionImage_injective, inclusionImage_not_surjective, ?_,
    inclusionImage_nonconstant⟩
  rw [isIso_iff_bijective]
  exact fun h ↦ inclusionImage_not_surjective h.2

private lemma swap_coordinates (q : Types.PullbackObj x y) :
    ((Types.pullbackIsoPullback x y).hom
      (swapImage.left ((Types.pullbackIsoPullback x y).inv q))).val =
      (swap q.val.1, q.val.2) := by
  apply Prod.ext
  · have h := swap_fst_apply q
    rw [Over.pullbackPairingFst_app_left] at h
    exact (Types.pullbackIsoPullback_hom_fst x y _).trans h
  · have h := swap_snd_apply q
    rw [Over.pullbackPairingSnd_app_left] at h
    exact (Types.pullbackIsoPullback_hom_snd x y _).trans h

/-- Both projection naturality routes for the nonidentity horizontal swap agree
in coordinates on every target point. -/
example (q : Types.PullbackObj x y) :
    ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (swapImage.left ((Types.pullbackIsoPullback x y).inv q)) = swap q.val.1 ∧
    swap (((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      ((Types.pullbackIsoPullback x y).inv q)) = swap q.val.1 ∧
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      (swapImage.left ((Types.pullbackIsoPullback x y).inv q)) = q.val.2 ∧
    ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
      ((Types.pullbackIsoPullback x y).inv q) = q.val.2 := by
  refine ⟨?_, congrArg swap (fst_apply target q), ?_, snd_apply target q⟩
  · exact swap_fst_apply q
  · exact swap_snd_apply q

private lemma swapImage_moves_iff (q : Types.PullbackObj x y) :
    swapImage.left ((Types.pullbackIsoPullback x y).inv q) ≠
      (Types.pullbackIsoPullback x y).inv q ↔ swap q.val.1 ≠ q.val.1 := by
  constructor
  · intro h hcoord
    apply h
    apply (Types.pullbackIsoPullback x y).toEquiv.injective
    apply Subtype.ext
    calc
      _ = (swap q.val.1, q.val.2) := swap_coordinates q
      _ = q.val := by rw [hcoord]
      _ = _ := (congrArg Subtype.val
        (iso_hom_inv_apply (Types.pullbackIsoPullback x y) q)).symm
  · intro h heq
    have hc := congrArg (fun z ↦ ((Types.pullbackIsoPullback x y).hom z).val.1) heq
    have hm := congrArg _root_.Prod.fst (swap_coordinates q)
    have hi := congrArg (fun z : Types.PullbackObj x y ↦ z.val.1)
      (iso_hom_inv_apply (Types.pullbackIsoPullback x y) q)
    exact h ((hm.symm.trans hc).trans hi)

private noncomputable def movedEquiv :
    {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
      swapImage.left p ≠ p} ≃
    {q : Types.PullbackObj x y // swap q.val.1 ≠ q.val.1} :=
  Equiv.subtypeEquiv (Types.pullbackIsoPullback x y).toEquiv (fun p ↦ by
    have h := swapImage_moves_iff ((Types.pullbackIsoPullback x y).toEquiv p)
    rw [iso_inv_equiv_apply (Types.pullbackIsoPullback x y) p] at h
    exact h)

@[instance_reducible]
private noncomputable def movedFintype :
    Fintype
      {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
        swapImage.left p ≠ p} :=
  Fintype.ofEquiv {q : Types.PullbackObj x y // swap q.val.1 ≠ q.val.1} movedEquiv.symm

attribute [local instance] movedFintype

/-- The induced swap moves four of the six chosen pullback points. -/
example :
    Fintype.card
      {p : ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).left //
        swapImage.left p ≠ p} = 4 := by
  exact (Fintype.card_congr movedEquiv).trans
    (by decide : Fintype.card {q : Types.PullbackObj x y // swap q.val.1 ≠ q.val.1} = 4)

/-- Neither projection component is mono: the first forgets two distinct
Y-coordinates, and the second forgets two distinct X-coordinates over `0`. -/
example :
    ¬ Mono ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left ∧
    ¬ Mono ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left := by
  constructor
  · rw [mono_iff_injective]
    intro h
    let p : Types.PullbackObj x y := ⟨(0, 0), by decide⟩
    let q : Types.PullbackObj x y := ⟨(0, 3), by decide⟩
    have heq := h ((fst_apply target p).trans (fst_apply target q).symm)
    exact (by decide : p ≠ q) ((Types.pullbackIsoPullback x y).toEquiv.symm.injective heq)
  · rw [mono_iff_injective]
    intro h
    let p : Types.PullbackObj x y := ⟨(0, 0), by decide⟩
    let q : Types.PullbackObj x y := ⟨(1, 0), by decide⟩
    have heq := h ((snd_apply target p).trans (snd_apply target q).symm)
    exact (by decide : p ≠ q) ((Types.pullbackIsoPullback x y).toEquiv.symm.injective heq)

private noncomputable abbrev targetFan :
    BinaryFan target.1.toComma target.2.toComma :=
  (Over.pullbackPairingFan ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).map
    ((evaluation Input (CategoryTheory.Over (Fin 2))).obj target)

/-- Evaluation preserves binary products in the ordinary over-category of types.
Mathlib's map-cone equivalence identifies the evaluated projection fan. -/
private noncomputable def targetFanIsLimit : IsLimit targetFan := by
  have : HasBinaryProducts (CategoryTheory.Over (Fin 2)) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  exact BinaryFan.isLimitMapConeEquiv
    (isLimitOfPreserves ((evaluation Input (CategoryTheory.Over (Fin 2))).obj target)
      (Over.pullbackPairingFanIsLimit ⊤ ⊤ (monomorphisms (Type)) (Fin 2)))

private abbrev DoubledPullback := Types.PullbackObj x y × Fin 2

@[instance_reducible]
private def doubledSource : CategoryTheory.Over (Fin 2) :=
  CategoryTheory.Over.mk (TypeCat.ofHom fun w : DoubledPullback ↦ x w.1.val.1)

private noncomputable def doubledFst : doubledSource ⟶ target.1.toComma :=
  CategoryTheory.Over.homMk (TypeCat.ofHom fun w : DoubledPullback ↦ w.1.val.1) rfl

private noncomputable def doubledSnd : doubledSource ⟶ target.2.toComma :=
  CategoryTheory.Over.homMk (TypeCat.ofHom fun w : DoubledPullback ↦ w.1.val.2) (by
    change (TypeCat.ofHom (fun w : DoubledPullback ↦ w.1.val.2) ≫ y :
        DoubledPullback ⟶ Fin 2) =
      TypeCat.ofHom (fun w : DoubledPullback ↦ x w.1.val.1)
    refine ConcreteCategory.hom_ext (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
      _ _ fun w ↦ ?_
    change y w.1.val.2 = x w.1.val.1
    exact w.1.property.symm)

private noncomputable def doubledFan : BinaryFan target.1.toComma target.2.toComma :=
  BinaryFan.mk doubledFst doubledSnd

private noncomputable def doubledLift : doubledSource ⟶ targetFan.pt :=
  targetFanIsLimit.lift doubledFan

private lemma doubledLift_fst : doubledLift ≫ targetFan.fst = doubledFst :=
  targetFanIsLimit.fac doubledFan ⟨WalkingPair.left⟩

private lemma doubledLift_snd : doubledLift ≫ targetFan.snd = doubledSnd :=
  targetFanIsLimit.fac doubledFan ⟨WalkingPair.right⟩

private lemma doubledLift_apply (w : DoubledPullback) :
    doubledLift.left w = (Types.pullbackIsoPullback x y).inv w.1 := by
  let k : doubledSource ⟶ targetFan.pt :=
    CategoryTheory.Over.homMk
      (TypeCat.ofHom fun z : DoubledPullback ↦ (Types.pullbackIsoPullback x y).inv z.1) (by
        change (TypeCat.ofHom (fun z : DoubledPullback ↦
            (Types.pullbackIsoPullback x y).inv z.1) ≫
          ((Over.pullbackPairing ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).obj target).hom :
            DoubledPullback ⟶ Fin 2) =
          TypeCat.ofHom (fun z : DoubledPullback ↦ x z.1.val.1)
        rw [Over.pullbackPairing_obj_hom]
        change (TypeCat.ofHom (fun z : DoubledPullback ↦
            (Types.pullbackIsoPullback x y).inv z.1) ≫ (pullback.fst x y ≫ x) :
            DoubledPullback ⟶ Fin 2) =
          TypeCat.ofHom (fun z : DoubledPullback ↦ x z.1.val.1)
        refine ConcreteCategory.hom_ext (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
          _ _ fun z ↦ ?_
        change x (pullback.fst x y ((Types.pullbackIsoPullback x y).inv z.1)) =
          x z.1.val.1
        have hbase := base_apply z.1
        rw [Over.pullbackPairing_obj_hom] at hbase
        exact hbase)
  have hk : doubledLift = k := by
    apply BinaryFan.IsLimit.hom_ext targetFanIsLimit
    · calc
        doubledLift ≫ targetFan.fst = doubledFst := doubledLift_fst
        _ = k ≫ targetFan.fst := by
          apply CategoryTheory.Over.OverMorphism.ext
          have hcomp : CategoryTheory.Over.Hom.left (k ≫ targetFan.fst) =
              k.left ≫ targetFan.fst.left :=
            CategoryTheory.Over.comp_left doubledSource targetFan.pt target.1.toComma
              k targetFan.fst
          rw [hcomp]
          change doubledFst.left =
            k.left ≫
              ((Over.pullbackPairingFst ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
          rw [Over.pullbackPairingFst_app_left]
          change (TypeCat.ofHom (fun z : DoubledPullback ↦ z.1.val.1) :
              DoubledPullback ⟶ Fin 3) =
            (TypeCat.ofHom (fun z : DoubledPullback ↦
              (Types.pullbackIsoPullback x y).inv z.1) : DoubledPullback ⟶ pullback x y) ≫
                pullback.fst x y
          refine ConcreteCategory.hom_ext (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
            _ _ fun z ↦ ?_
          change z.1.val.1 = pullback.fst x y ((Types.pullbackIsoPullback x y).inv z.1)
          have hfst := fst_apply target z.1
          rw [Over.pullbackPairingFst_app_left] at hfst
          exact hfst.symm
    · calc
        doubledLift ≫ targetFan.snd = doubledSnd := doubledLift_snd
        _ = k ≫ targetFan.snd := by
          apply CategoryTheory.Over.OverMorphism.ext
          have hcomp : CategoryTheory.Over.Hom.left (k ≫ targetFan.snd) =
              k.left ≫ targetFan.snd.left :=
            CategoryTheory.Over.comp_left doubledSource targetFan.pt target.2.toComma
              k targetFan.snd
          rw [hcomp]
          change doubledSnd.left =
            k.left ≫
              ((Over.pullbackPairingSnd ⊤ ⊤ (monomorphisms (Type)) (Fin 2)).app target).left
          rw [Over.pullbackPairingSnd_app_left]
          change (TypeCat.ofHom (fun z : DoubledPullback ↦ z.1.val.2) :
              DoubledPullback ⟶ Fin 4) =
            (TypeCat.ofHom (fun z : DoubledPullback ↦
              (Types.pullbackIsoPullback x y).inv z.1) : DoubledPullback ⟶ pullback x y) ≫
                pullback.snd x y
          refine ConcreteCategory.hom_ext (C := Type) (FC := TypeCat.Fun) (CC := fun X ↦ X)
            _ _ fun z ↦ ?_
          change z.1.val.2 = pullback.snd x y ((Types.pullbackIsoPullback x y).inv z.1)
          have hsnd := snd_apply target z.1
          rw [Over.pullbackPairingSnd_app_left] at hsnd
          exact hsnd.symm
  exact ConcreteCategory.congr_hom (congrArg CategoryTheory.Over.Hom.left hk) w

/-- The universal joint lift retains every pullback point and discards only the
extra bit, on all points of the doubled cone. -/
example (q : Types.PullbackObj x y) (b : Fin 2) :
    doubledLift.left (q, b) = (Types.pullbackIsoPullback x y).inv q :=
  doubledLift_apply (q, b)

private lemma doubledLift_surjective : Function.Surjective doubledLift.left := by
  intro p
  refine ⟨((Types.pullbackIsoPullback x y).toEquiv p, 0), ?_⟩
  exact (doubledLift_apply _).trans (iso_inv_equiv_apply (Types.pullbackIsoPullback x y) p)

private lemma doubledLift_not_injective : ¬ Function.Injective doubledLift.left := by
  intro h
  let q : Types.PullbackObj x y := ⟨(0, 0), by decide⟩
  have heq : (q, (0 : Fin 2)) = (q, (1 : Fin 2)) :=
    h ((doubledLift_apply (q, 0)).trans (doubledLift_apply (q, 1)).symm)
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg _root_.Prod.snd heq)

private lemma doubledLift_nonconstant : ∃ w z, doubledLift.left w ≠ doubledLift.left z := by
  let p : Types.PullbackObj x y := ⟨(0, 0), by decide⟩
  let q : Types.PullbackObj x y := ⟨(1, 0), by decide⟩
  refine ⟨(p, 0), (q, 0), ?_⟩
  intro h
  rw [doubledLift_apply, doubledLift_apply] at h
  exact (by decide : p ≠ q) ((Types.pullbackIsoPullback x y).toEquiv.symm.injective h)

/-- The product's ordinary-over joint lift is surjective and nonconstant, but
not mono: two distinct bits have the same image. Thus joint lifts need not have
the monomorphism property restricting the input horizontal arrows. -/
example :
    Function.Surjective doubledLift.left ∧ ¬ Function.Injective doubledLift.left ∧
    ¬ Mono doubledLift.left ∧ ∃ w z, doubledLift.left w ≠ doubledLift.left z := by
  refine ⟨doubledLift_surjective, doubledLift_not_injective, ?_, doubledLift_nonconstant⟩
  rw [mono_iff_injective]
  exact doubledLift_not_injective

end CategoryTheory.MorphismProperty.PullbackMapExamples.ProjectionFan
