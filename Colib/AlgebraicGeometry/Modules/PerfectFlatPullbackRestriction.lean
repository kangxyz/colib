/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullback
public import Colib.AlgebraicGeometry.Modules.PerfectGlobalUnit

/-! # Actual flat pullback, restriction and unit isomorphisms

The restriction comparison is the genuine degreewise geometric comparison. Its original
left unitor and the global unit's two right unitors remain explicit.
Implementation provenance: Quillen `PerfectComplexes/FlatPullback.lean`,
`FlatPullbackRestriction.lean` and `GlobalUnit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
universe u

/-- Actual ordinary open restriction agrees with genuine flat geometric pullback. -/
def perfectRestrictIsoFlatPullback {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    perfectComplexesRestrictOpenImmersion j ≅ perfectFlatPullback j :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (Functor.isoWhiskerLeft
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)))
      (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j) (ComplexShape.up ℤ)))

/-- The actual geometric comparison, retaining its original left unitor. -/
def perfectOpenRestrictionFlatIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) ⋙
        perfectComplexesRestrictOpenImmersion j ≅ perfectFlatPullback j :=
  Functor.leftUnitor (perfectComplexesRestrictOpenImmersion j) ≪≫
    perfectRestrictIsoFlatPullback j

/-- Literal multiplication by a global unit on the actual flat pullback functor. -/
def perfectFlatPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) : perfectFlatPullback f ≅ perfectFlatPullback f :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (perfectFlatPullback f) (perfectGlobalUnitIso X q) ≪≫
      Functor.rightUnitor _

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/FlatPullback.lean:135-139"
  "adaptation" "Actual geometric restriction-pullback comparison on native perfect complexes"]
  AlgebraicGeometry.Scheme.Modules.perfectRestrictIsoFlatPullback
attribute [colib_ref "quillen"
  "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/FlatPullbackRestriction.lean:27-31"
  "adaptation" "The original left unitor followed by the actual geometric comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictionFlatIso
attribute [colib_ref "quillen"
  "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalUnit.lean:42-47"
  "adaptation" "The actual target global unit with both original right unitors"]
  AlgebraicGeometry.Scheme.Modules.perfectFlatPullbackUnitIso
