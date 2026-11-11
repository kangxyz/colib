/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit
public import Colib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation
public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality
public import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-!
# Original units on the joint native coefficient sections

Faithful original evaluation lifts each actual geometric unit. Its genuine transition
isomorphism proves preservation by every joint reindexing map. Pulling a coefficient unit
along the original coefficient projection gives the same forward action after coefficient
change or scheme restriction. In particular the original Laurent coordinate is retained.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u v₁ v₂ v₃ w₁ w₂ w₃
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso

/-- The actual geometric unit lifted through the unchanged original evaluation equivalence. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:40"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientSectionUnitIso (i : Index R) (r : (Γ(space i, ⊤))ˣ) :
    𝟭 (BoundedAboveFlatCoefficientSections i) ≅ 𝟭 (BoundedAboveFlatCoefficientSections i) :=
  lift (boundedAboveFlatCoefficientOriginalEvaluation i) (boundedAboveFlatPerfectGlobalUnitIso
    (space i) r)

private theorem coefficientSectionUnitIso_eq (i : Index R) (r : (Γ(space i, ⊤))ˣ) :
    boundedAboveFlatCoefficientSectionUnitIso i r =
      lift (boundedAboveFlatCoefficientOriginalEvaluation i)
        (boundedAboveFlatPerfectGlobalUnitIso (space i) r) := rfl

/-- Original evaluation retains each prescribed forward unit component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:50"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionUnitIso_evaluation_hom (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) (S : BoundedAboveFlatCoefficientSections i) :
    (boundedAboveFlatCoefficientOriginalEvaluation i).map
        ((boundedAboveFlatCoefficientSectionUnitIso i r).hom.app S) =
      (boundedAboveFlatPerfectGlobalUnitIso (space i) r).hom.app
        ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S) := by
  rw [coefficientSectionUnitIso_eq]
  exact map_lift_hom (boundedAboveFlatCoefficientOriginalEvaluation i)
    (boundedAboveFlatPerfectGlobalUnitIso (space i) r) S

/-- Original evaluation also retains the inverse of that same unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:61"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionUnitIso_evaluation_inv (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) (S : BoundedAboveFlatCoefficientSections i) :
    (boundedAboveFlatCoefficientOriginalEvaluation i).map
        ((boundedAboveFlatCoefficientSectionUnitIso i r).inv.app S) =
      (boundedAboveFlatPerfectGlobalUnitIso (space i) r).inv.app
        ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S) := by
  rw [coefficientSectionUnitIso_eq]
  exact map_lift_inv (boundedAboveFlatCoefficientOriginalEvaluation i)
    (boundedAboveFlatPerfectGlobalUnitIso (space i) r) S

private theorem preserves_of_evaluation_iso
    {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
    {E : Type v₃} [Category.{w₃} E] (F : C ⥤ D) (P : D ⥤ E) [P.Faithful]
    (Q : C ⥤ E) (e : F ⋙ P ≅ Q)
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (γ : 𝟭 E ≅ 𝟭 E)
    (ha : Preserves Q α γ) (hb : Preserves P β γ) : Preserves F α β := by
  intro S
  apply P.map_injective
  exact (map_hom_eq_of_iso (F ⋙ P) Q e α γ ha S).trans (hb (F.obj S)).symm

/-- Every original joint reindexing preserves the original pulled-back forward unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:82"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionsMap_unit_preserves {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSectionsMap f)
      (boundedAboveFlatCoefficientSectionUnitIso i r)
      (boundedAboveFlatCoefficientSectionUnitIso k
        (Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f).appTop.hom.toMonoidHom
          r)) := by
  apply preserves_of_evaluation_iso (boundedAboveFlatCoefficientSectionsMap f)
    (boundedAboveFlatCoefficientOriginalEvaluation k)
    (boundedAboveFlatCoefficientOriginalEvaluation i ⋙
      boundedAboveFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (boundedAboveFlatCoefficientSectionReindexIso f) _ _
    (boundedAboveFlatPerfectGlobalUnitIso (space k)
      (Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f).appTop.hom.toMonoidHom r))
  · intro S
    change (boundedAboveFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      f)).map
      ((boundedAboveFlatCoefficientOriginalEvaluation i).map
        ((boundedAboveFlatCoefficientSectionUnitIso i r).hom.app S)) = _
    rw [boundedAboveFlatCoefficientSectionUnitIso_evaluation_hom,
      boundedAboveFlatPerfectPullback_map_globalUnit]
    rfl
  · exact boundedAboveFlatCoefficientSectionUnitIso_evaluation_hom k _

/-- A coefficient unit pulled back along the actual native coefficient projection. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:105"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientUnit (i : Index R) (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    (Γ(space i, ⊤))ˣ :=
  Units.map (coefficientProjection i).appTop.hom.toMonoidHom r

/-- The original projection square preserves the exact coefficient-unit map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:110"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientUnit_map {i k : Index R} (f : i ⟶ k)
    (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f).appTop.hom.toMonoidHom
        (boundedAboveFlatCoefficientUnit i r) =
      boundedAboveFlatCoefficientUnit k
        (Units.map (Spec.map f.2.right).appTop.hom.toMonoidHom r) := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (map_coefficientProjection f)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- The original ambient and restricted units agree through the actual native open map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:122"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientUnit_restriction {P Q : Over (Spec R)} (f : P ⟶ Q)
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (schemeMap f a).appTop.hom.toMonoidHom
        (boundedAboveFlatCoefficientUnit (op Q, a) r) =
      boundedAboveFlatCoefficientUnit (op P, a) r := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (schemeMap_coefficientProjection f a)
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- Every joint section map retains the same scalar after its actual coefficient map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:133"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionsMap_coefficientUnit_preserves
    {i k : Index R} (f : i ⟶ k) (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSectionsMap f)
      (boundedAboveFlatCoefficientSectionUnitIso i (boundedAboveFlatCoefficientUnit i r))
      (boundedAboveFlatCoefficientSectionUnitIso k (boundedAboveFlatCoefficientUnit k
        (Units.map (Spec.map f.2.right).appTop.hom.toMonoidHom r))) := by
  rw [← boundedAboveFlatCoefficientUnit_map f r]
  exact boundedAboveFlatCoefficientSectionsMap_unit_preserves f (boundedAboveFlatCoefficientUnit i
    r)

/-- Native scheme restriction keeps the unchanged forward coefficient unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:143"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionsRestriction_unit_preserves {P Q : Over (Spec R)}
    (f : P ⟶ Q) (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op P, a))
      (f.op, 𝟙 a))
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a)
        (boundedAboveFlatCoefficientUnit (op Q, a) r))
      (boundedAboveFlatCoefficientSectionUnitIso (op P, a)
        (boundedAboveFlatCoefficientUnit (op P, a) r)) := by
  have h := boundedAboveFlatCoefficientSectionsMap_unit_preserves
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (boundedAboveFlatCoefficientUnit (op Q, a) r)
  change Preserves _ _ (boundedAboveFlatCoefficientSectionUnitIso (op P, a)
    (Units.map (schemeMap f a).appTop.hom.toMonoidHom
      (boundedAboveFlatCoefficientUnit (op Q, a) r))) at h
  rw [boundedAboveFlatCoefficientUnit_restriction] at h
  exact h

/-- The forward Laurent coordinate on the specified actual native coefficient fiber. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:161"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientSectionLaurentUnitIso (P : Over (Spec R)) (a : Under R) :
    𝟭 (BoundedAboveFlatCoefficientSections (op P, (laurentUnderFunctor R).obj a)) ≅
      𝟭 (BoundedAboveFlatCoefficientSections (op P, (laurentUnderFunctor R).obj a)) :=
  boundedAboveFlatCoefficientSectionUnitIso (op P, (laurentUnderFunctor R).obj a)
    (boundedAboveFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a) (laurentCoordinate
      a.right))

/-- Coefficient change preserves the original forward Laurent coordinate on native sections. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:168"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient
    (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedAboveFlatCoefficientSectionsMap
      (i := (op P, (laurentUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj b)) (𝟙 (op P), (laurentUnderFunctor R).map g))
      (boundedAboveFlatCoefficientSectionLaurentUnitIso P a)
      (boundedAboveFlatCoefficientSectionLaurentUnitIso P b) := by
  have hr : Units.map (Spec.map ((laurentUnderFunctor R).map g).right).appTop.hom.toMonoidHom
      (laurentCoordinate a.right) = laurentCoordinate b.right :=
    laurentCoordinate_coefficient g.right
  unfold boundedAboveFlatCoefficientSectionLaurentUnitIso
  simpa only [hr] using boundedAboveFlatCoefficientSectionsMap_coefficientUnit_preserves
    (i := (op P, (laurentUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj b))
    (𝟙 (op P), (laurentUnderFunctor R).map g) (laurentCoordinate a.right)

/-- Scheme restriction preserves that same forward Laurent coordinate, without extra premises. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSectionUnits.lean:185"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem boundedAboveFlatCoefficientSectionLaurentUnitIso_restriction
    {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    Preserves (boundedAboveFlatCoefficientSectionsMap
      (i := (op Q, (laurentUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (f.op, 𝟙 _))
      (boundedAboveFlatCoefficientSectionLaurentUnitIso Q a)
      (boundedAboveFlatCoefficientSectionLaurentUnitIso P a) :=
  boundedAboveFlatCoefficientSectionsRestriction_unit_preserves f
    ((laurentUnderFunctor R).obj a) (laurentCoordinate a.right)

end AlgebraicGeometry.Scheme.Modules

