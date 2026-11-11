/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.NisnevichRepresentative
public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes
public import Colib.CategoryTheory.Sites.Simplicial.IntervalKInjectiveReplacement

/-!
# Cohomology representatives for the affine-line interval

The interval is the lifted simplicial Yoneda presheaf of the native affine line.
For the original cochain complex, invariance of reduced hypercohomology under
the pointed cylinder projections gives a representation after interval localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u})

local notation "Cₛ" => SmoothSite S
local notation "Jₛ" => SmoothSite.nisnevichTopology S

/-- The native affine line as a simplicial presheaf in the coefficient universe. -/
abbrev affineLineInterval : Cₛᵒᵖ ⥤ SSet.{u + 1} :=
  (uliftPresheaf.{u + 1, u} Cₛ).obj
    ((simplicialYoneda Cₛ).obj (SmoothSite.additiveGroupObject S))

/-- The interval localization of the smooth Nisnevich homotopy category. -/
abbrev AffineLineHomotopyCategory :=
  IntervalHomotopyCategory Cₛ Jₛ (affineLineInterval S)

/-- The chosen localization functor for the actual affine-line interval. -/
abbrev toAffineLineHomotopyCategory :
    PointedSimplicialPresheaf.{u + 1} Cₛ ⥤ AffineLineHomotopyCategory S :=
  toIntervalHomotopyCategory Cₛ Jₛ (affineLineInterval S)

variable
  [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}]
  [IsGrothendieckAbelian.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- The K-injective cochain representative viewed in the affine-line localization. -/
abbrev affineLineCochainRepresentative (p : ℤ)
    (K : CochainComplex (Sheaf Jₛ AddCommGrpCat.{u + 1}) ℤ) :
    AffineLineHomotopyCategory S :=
  (toAffineLineHomotopyCategory S).obj ((pointedKInjectiveCochainRepresentative Cₛ Jₛ p).obj K)

variable [QuasiSeparatedSpace S]
  [HasDerivedCategory.{d} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

variable (p : ℤ) (K : CochainComplex
  (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ)
  (hK : ∀ X : PointedSimplicialPresheaf.{u + 1} (SmoothSite S),
    Function.Bijective ((reducedHypercohomology.{d} (SmoothSite S)
      (SmoothSite.nisnevichTopology S) K p).map
      (cylinderProjection X (affineLineInterval S)).op))

/-- Under cylinder invariance, the actual affine-line localization represents
reduced hypercohomology with the given coefficients. -/
def affineLineCochainRepresentativeHomEquiv (X : PointedSimplicialPresheaf.{u + 1} Cₛ) :
    ((toAffineLineHomotopyCategory S).obj X ⟶ affineLineCochainRepresentative S p K) ≃
      (reducedHypercohomology Cₛ Jₛ K p).obj (op X) :=
  intervalKInjectiveReplacementHomEquiv Cₛ Jₛ (affineLineInterval S)
    pointedSimplicialSetChainsPreserveRealizationWeakEquivalences p K hK X

/-- For a freely pointed smooth representable, the target is its original
ordinary Nisnevich hypercohomology. -/
def affineLineCochainRepresentativeYonedaHomEquiv (U : Cₛ) :
    ((toAffineLineHomotopyCategory S).obj ((liftedSmoothPointedYoneda S).obj U) ⟶
      affineLineCochainRepresentative S p K) ≃
      (hypercohomologyPresheaf.{d, u + 1} Jₛ K p).obj (op U) :=
  (affineLineCochainRepresentativeHomEquiv S p K hK _).trans
    (((reducedHypercohomologyYonedaIso.{d, u + 1} Cₛ Jₛ K p).app
      (op U)).addCommGroupIsoToAddEquiv.toEquiv)

/-- The equivalence sends precomposition by the original smooth map to the
ordinary Nisnevich hypercohomology restriction. -/
theorem affineLineCochainRepresentativeYonedaHomEquiv_naturality
    {U V : Cₛ} (f : U ⟶ V)
    (a : (toAffineLineHomotopyCategory S).obj ((liftedSmoothPointedYoneda S).obj V) ⟶
      affineLineCochainRepresentative S p K) :
    affineLineCochainRepresentativeYonedaHomEquiv S p K hK U
      ((toAffineLineHomotopyCategory S).map ((liftedSmoothPointedYoneda S).map f) ≫ a) =
      (hypercohomologyPresheaf.{d, u + 1} Jₛ K p).map f.op
        (affineLineCochainRepresentativeYonedaHomEquiv S p K hK V a) := by
  let e := reducedHypercohomologyYonedaIso.{d, u + 1} Cₛ Jₛ K p
  let F := liftedSmoothPointedYoneda S
  let I := affineLineInterval S
  let h := pointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{u + 1}
  let b := intervalKInjectiveReplacementHomEquiv Cₛ Jₛ I h p K hK (F.obj V) a
  change e.hom.app (op U) (intervalKInjectiveReplacementHomEquiv Cₛ Jₛ I h p K hK
    (F.obj U) ((toIntervalHomotopyCategory Cₛ Jₛ I).map (F.map f) ≫ a)) =
    (hypercohomologyPresheaf.{d, u + 1} Jₛ K p).map f.op (e.hom.app (op V) b)
  rw [intervalKInjectiveReplacementHomEquiv_naturality]
  exact congrArg (fun g => g b) (e.hom.naturality f.op)

attribute [colib_tag "COL-1016"]
  affineLineCochainRepresentative
  affineLineCochainRepresentativeHomEquiv
  affineLineCochainRepresentativeYonedaHomEquiv
  affineLineCochainRepresentativeYonedaHomEquiv_naturality

attribute [colib_ref "MorelVoevodsky1999" "§2.3, Definition 3.1 and Remark 3.3, p. 86"
  "adaptation" "Interval localization using the actual pointed affine-line projections"]
  affineLineCochainRepresentativeHomEquiv

end AlgebraicGeometry.MotivicHomotopy
