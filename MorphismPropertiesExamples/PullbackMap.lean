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

## References

* Mathlib, `CategoryTheory.MorphismProperty.Limits` and
  `CategoryTheory.Limits.Types.Pullbacks`, for the absolute comparison and
  the existing pullback constructions.
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
