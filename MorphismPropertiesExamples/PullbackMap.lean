/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismPropertiesExamples.RelativeBaseChange
public import MorphismProperties.PullbackPairing
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
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

## References

* Mathlib, `CategoryTheory.MorphismProperty.Limits`,
  `CategoryTheory.MorphismProperty.Comma`, and
  `CategoryTheory.Limits.Types.Pullbacks`, for the absolute comparison,
  restricted comma-category lifting, and existing pullback constructions.
* Mathlib, `CategoryTheory.Limits.Shapes.Pullback.HasPullback`, for the symmetry
  and projection equations used in the finite-model checks.
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
