/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectFlatPullback

/-! # Full-signature consumers of genuine flat pullback and its actual comparisons -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
namespace ColibTest.ScalarTrack.FlatPullback
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]

/-- Arbitrary flat morphisms preserve the actual native perfect-complex predicate. -/
theorem nativePerfectness (K : CochainComplex Y.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := Y.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Complex.isPerfectComplex_flatPullback f K hK

/-- The exact functor uses the native ambient cofibrations and quasi-isomorphisms. -/
theorem nativeWaldhausenExactness :
    Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectFlatPullback f) :=
  perfectFlatPullback_waldhausenExact f

/-- The underlying object at each degree is literal module pullback. -/
theorem objectTerm
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)))
    (n : ℤ) : ((perfectFlatPullback f).obj K).obj.X n =
      (pullback f).obj (K.obj.X n) := rfl

/-- The underlying map at each degree is literal module pullback. -/
theorem mapTerm
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))}
    (s : K ⟶ L) (n : ℤ) : ((perfectFlatPullback f).map s).hom.f n =
      (pullback f).map (s.hom.f n) := rfl

/-- The unit acts on the actual target of the pullback functor. -/
def targetUnitIso (q : (Γ(X, ⊤))ˣ) : perfectFlatPullback f ≅ perfectFlatPullback f :=
  perfectFlatPullbackUnitIso f q

/-- Both unitors disappear only by the category laws, leaving the actual target unit. -/
theorem targetUnitComponent (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))) :
    (perfectFlatPullbackUnitIso f q).hom.app K =
      (perfectGlobalUnitIso X q).hom.app ((perfectFlatPullback f).obj K) := by
  change 𝟙 _ ≫ (perfectGlobalUnitIso X q).hom.app ((perfectFlatPullback f).obj K) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- Open restriction is compared with actual flat pullback on the same native full categories. -/
def openRestrictionIso (j : X ⟶ Y) [IsOpenImmersion j] :
    perfectComplexesRestrictOpenImmersion j ≅ perfectFlatPullback j :=
  perfectRestrictIsoFlatPullback j

/-- The raw comparison keeps exactly the original left-unitor source. -/
def openRestrictionWithUnitor (j : X ⟶ Y) [IsOpenImmersion j] :
    (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)))) ⋙
        perfectComplexesRestrictOpenImmersion j ≅ perfectFlatPullback j :=
  perfectOpenRestrictionFlatIso j

end ColibTest.ScalarTrack.FlatPullback
