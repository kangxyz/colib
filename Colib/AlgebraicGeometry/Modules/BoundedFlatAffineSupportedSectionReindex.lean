/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback

/-!
# Actual supported affine coefficient restriction and its geometric comparison

The original cocartesian transition proves support preservation for every specified
commuting affine open square, without flatness or a cartesian hypothesis. Restriction
is strictly functorial, while geometric evaluation is compared by its actual natural
isomorphism, not asserted strictly natural.

Adapted from Quillen `SupportedSections.lean:55-91`,
and `SupportedSectionReindex.lean:32-61`
in `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt

/-- The specified square as a morphism of native scheme-open pairs. -/
def boundedAboveFlatAffineSupportedPairSquare
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    (MorphismProperty.Arrow.mk j' inferInstance : Scheme.OpenPairs) ⟶
      MorphismProperty.Arrow.mk j inferInstance :=
  MorphismProperty.Arrow.homMk l (Spec.map f) h

/-- The original coefficient reindexing preserves support along the specified whole open square.
-/
theorem boundedAboveFlatAffineSectionsMap_supported
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
    (s : BoundedAboveFlatAffineSections R) (hs : boundedAboveFlatAffineSectionSupported j s) :
    boundedAboveFlatAffineSectionSupported j' ((boundedAboveFlatAffineSectionsMap f).obj s) := by
  let sq := boundedAboveFlatAffineSupportedPairSquare j j' f l h
  have hp := boundedAboveFlatPerfectSupported_pairPullback sq
    (K := ((boundedAboveFlatAffineOriginalEvaluation R).obj s).obj)
    ⟨((boundedAboveFlatAffineOriginalEvaluation R).obj s).property, hs⟩
  change (((restrictFunctor j').mapHomologicalComplex (.up ℤ)).obj
    ((boundedAboveFlatAffineSectionsMap f ⋙
      boundedAboveFlatAffineOriginalEvaluation S).obj s).obj).Acyclic
  rw [boundedAboveFlatAffineSectionsMap_comp_evaluation]
  intro n
  exact (hp.2 n).of_iso (((restrictFunctor j').mapHomologicalComplex (.up ℤ)).mapIso
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.mapIso
      ((boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).app s)))

/-- Restrict the unchanged coefficient functor to its actual supported objects. -/
def boundedAboveFlatAffineSupportedSectionsMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    BoundedAboveFlatAffineSupportedSections j ⥤ BoundedAboveFlatAffineSupportedSections j' :=
  (boundedAboveFlatAffineSectionSupported j').lift
    ((boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineSectionsMap f)
    (fun s ↦ boundedAboveFlatAffineSectionsMap_supported j j' f l h s.obj s.property)

/-- Forgetting support retains the same coefficient reindexing, on objects and morphisms. -/
theorem boundedAboveFlatAffineSupportedSectionsMap_forget
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
        (boundedAboveFlatAffineSectionSupported j').ι =
      (boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineSectionsMap f := rfl

private theorem supported_lift_congr {C : Type*} [Category* C] {D : Type*} [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ x, P (F.obj x)) (hG : ∀ x, P (G.obj x)) : P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- Restriction along the original identity square is literally the identity functor. -/
theorem boundedAboveFlatAffineSupportedSectionsMap_id
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (h : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedAboveFlatAffineSupportedSectionsMap j j (𝟙 R) (𝟙 U) h =
      𝟭 (BoundedAboveFlatAffineSupportedSections j) := by
  change (boundedAboveFlatAffineSectionSupported j).lift
    ((boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineSectionsMap (𝟙 R)) _ =
      (boundedAboveFlatAffineSectionSupported j).lift (boundedAboveFlatAffineSectionSupported j).ι _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedAboveFlatAffineSectionSupported j).ι ⋙ F)
    (boundedAboveFlatAffineSectionsMap_id R)

/-- Original supported coefficient reindexing composes strictly through the actual open maps. -/
theorem boundedAboveFlatAffineSupportedSectionsMap_comp
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) (j'' : W ⟶ Spec T)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : R ⟶ S) (g : S ⟶ T) (l : V ⟶ U) (m : W ⟶ V)
    (hf : l ≫ j = j' ≫ Spec.map f) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedAboveFlatAffineSupportedSectionsMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedAboveFlatAffineSupportedSectionsMap j j' f l hf ⋙
        boundedAboveFlatAffineSupportedSectionsMap j' j'' g m hg := by
  change (boundedAboveFlatAffineSectionSupported j'').lift
    ((boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineSectionsMap (f ≫ g)) _ =
      (boundedAboveFlatAffineSectionSupported j'').lift
        ((boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineSectionsMap f ⋙
          boundedAboveFlatAffineSectionsMap g) _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedAboveFlatAffineSectionSupported j).ι ⋙ F)
    (boundedAboveFlatAffineSectionsMap_comp f g)

end AlgebraicGeometry.Scheme.Modules


attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedSections.lean:55-91"
  "adaptation" "Actual supported restriction across arbitrary commuting affine open squares"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionsMap_supported
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap_forget

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedSectionReindex.lean:32-61"
  "adaptation" "Strict identity and composition of the unchanged supported coefficient functors"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap_id
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap_comp
