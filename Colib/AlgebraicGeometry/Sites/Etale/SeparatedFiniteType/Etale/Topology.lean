/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# The separated finite-type basis of the small étale site

The existing category of separated quasi-compact étale neighborhoods is given
the topology induced from the actual full small étale site. Over an affine base,
every affine étale neighborhood of an arbitrary smooth object belongs to this
basis. Factoring Mathlib's cover-dense affine site through the inclusion proves
the comparison with the full small site, including its non-quasi-compact objects.

The equivalence uses `AddCommGrpCat.{u + 1}` and its inverse is literal restriction
of the original coefficient sheaf. The smooth object need not itself be affine.
No inclusion of the full small site into the finite-type smooth site is asserted.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Etale/Topology.lean`
in the motivic source checkpoint of 2026-10-21.
The current consumer is ordinary smooth-to-small étale cohomology comparison.
Exact extension and derived cohomology comparison are not supplied by this leaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- The actual inclusion into all étale neighborhoods, retaining schemes and maps. -/
def toSmallEtale (S : Scheme.{u}) : EtaleSeparatedFiniteType S ⥤ S.Etale :=
  MorphismProperty.Over.changeProp S
    (show etaleSeparatedFiniteType ≤ @AlgebraicGeometry.Etale from
      fun _ _ _ h ↦ h.1.1) le_rfl

@[simp]
theorem toSmallEtale_obj_left (S : Scheme.{u}) (U : EtaleSeparatedFiniteType S) :
    ((toSmallEtale S).obj U).left = U.left := rfl

@[simp]
theorem toSmallEtale_obj_hom (S : Scheme.{u}) (U : EtaleSeparatedFiniteType S) :
    ((toSmallEtale S).obj U).hom = U.hom := rfl

@[simp]
theorem toSmallEtale_map_left (S : Scheme.{u}) {U V : EtaleSeparatedFiniteType S}
    (f : U ⟶ V) : ((toSmallEtale S).map f).left = f.left := rfl

instance (S : Scheme.{u}) : (toSmallEtale S).Full := by
  let E : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Etale
  let hE : etaleSeparatedFiniteType ≤ E := fun _ _ _ h ↦ h.1.1
  exact (MorphismProperty.Comma.fullyFaithfulChangeProp
    (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} S)
    (Q := ⊤) (W := ⊤) hE).full

instance (S : Scheme.{u}) : (toSmallEtale S).Faithful := by
  let E : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Etale
  let hE : etaleSeparatedFiniteType ≤ E := fun _ _ _ h ↦ h.1.1
  exact (MorphismProperty.Comma.fullyFaithfulChangeProp
    (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} S)
    (Q := ⊤) (W := ⊤) hE).faithful

/-- The étale topology on separated finite-type neighborhoods is induced from the full site. -/
def etaleTopology (S : Scheme.{u}) : GrothendieckTopology (EtaleSeparatedFiniteType S) :=
  (toSmallEtale S).inducedTopology S.smallEtaleTopology

/-- The identity neighborhood maps to the actual terminal object of the full small site. -/
def toSmallEtaleIdentityIso (S : Scheme.{u}) :
    (toSmallEtale S).obj
        (MorphismProperty.Over.mk ⊤ (𝟙 S) (etaleSeparatedFiniteType.id_mem S)) ≅
      Etale.mk (𝟙 S) :=
  MorphismProperty.Over.isoMk (Iso.refl _)

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- An affine étale neighborhood is separated and quasi-compact over the smooth object. -/
@[simps! obj_left obj_hom map_left]
def affineEtaleToSeparatedFiniteType :
    X.left.AffineEtale ⥤ EtaleSeparatedFiniteType X.left where
  obj U := MorphismProperty.Over.mk ⊤ U.hom (by
    let : IsAffineHom (U.hom ≫ X.hom) := isAffineHom_of_isAffine (Y := B) _
    let : IsAffineHom U.hom := IsAffineHom.of_comp U.hom X.hom
    exact ⟨⟨U.prop, inferInstance⟩, inferInstance⟩)
  map f := MorphismProperty.Over.homMk ((AffineEtale.Spec X.left).map f).left
    (MorphismProperty.Over.w ((AffineEtale.Spec X.left).map f))
  map_id U := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ (Etale.forget X.left ⋙ Over.forget X.left).map f)
      ((AffineEtale.Spec X.left).map_id U)
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ (Etale.forget X.left ⋙ Over.forget X.left).map f)
      ((AffineEtale.Spec X.left).map_comp f g)

/-- This factorization retains the original affine étale scheme and structure morphism. -/
def affineEtaleToSeparatedFiniteTypeCompIso :
    affineEtaleToSeparatedFiniteType X ⋙ toSmallEtale X.left ≅ AffineEtale.Spec X.left :=
  NatIso.ofComponents (fun U ↦ MorphismProperty.Over.isoMk
    (Iso.refl ((AffineEtale.Spec X.left).obj U).left) (by
      change 𝟙 _ ≫ U.hom = U.hom
      exact Category.id_comp _)) (by
    intro U V f
    apply MorphismProperty.Over.Hom.ext
    change ((AffineEtale.Spec X.left).map f).left ≫ 𝟙 _ =
      𝟙 _ ≫ ((AffineEtale.Spec X.left).map f).left
    simp only [Category.comp_id, Category.id_comp])

/-- Every full small étale object is covered by the separated quasi-compact basis. -/
theorem toSmallEtale_isCoverDense :
    (toSmallEtale X.left).IsCoverDense X.left.smallEtaleTopology where
  is_cover U := by
    apply X.left.smallEtaleTopology.superset_covering
      (S := Sieve.coverByImage (AffineEtale.Spec X.left) U) ?_
      (Functor.is_cover_of_isCoverDense (AffineEtale.Spec X.left) _ U)
    rintro V f ⟨⟨A, g, h, w⟩⟩
    refine ⟨⟨(affineEtaleToSeparatedFiniteType X).obj A,
      g ≫ (affineEtaleToSeparatedFiniteTypeCompIso X).inv.app A,
      (affineEtaleToSeparatedFiniteTypeCompIso X).hom.app A ≫ h, ?_⟩⟩
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using w

/-- The induced étale topology gives a genuine dense subsite of the full small site. -/
theorem toSmallEtale_isDenseSubsite :
    (toSmallEtale X.left).IsDenseSubsite (etaleTopology X.left)
      X.left.smallEtaleTopology := by
  let := toSmallEtale_isCoverDense X
  unfold etaleTopology
  infer_instance

/-- Ordinary abelian sheaves on this basis and on the full small étale site are equivalent. -/
@[colib_tag "COL-1060", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/DenseSubsite/InducedTopology.lean:154-162"
  "ingredient" "Cover-dense sheaf comparison; density of the actual finite-type etale basis is \
    proved here."]
def sheafEquivSmallEtale :
    Sheaf (etaleTopology X.left) AddCommGrpCat.{u + 1} ≌
      Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  letI := toSmallEtale_isCoverDense X
  exact (toSmallEtale X.left).sheafInducedTopologyEquivOfIsCoverDense
    X.left.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- On coefficients, the inverse equivalence is the original presheaf restriction. -/
@[simp]
theorem sheafEquivSmallEtale_inverse_obj_obj
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((sheafEquivSmallEtale X).inverse.obj F).obj = (toSmallEtale X.left).op ⋙ F.obj := rfl

/-- On coefficient morphisms, the inverse equivalence is literal precomposition. -/
@[simp]
theorem sheafEquivSmallEtale_inverse_map_hom
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    ((sheafEquivSmallEtale X).inverse.map f).hom =
      Functor.whiskerLeft (toSmallEtale X.left).op f.hom := rfl

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
