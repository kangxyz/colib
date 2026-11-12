/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.StrictHenselization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.SmoothSite

noncomputable section

universe u

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : Scheme.SmoothSite S)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left) (s : GeometricPoint X.left)

example : (etaleNeighborhoodToBounded X B hX s).Initial := inferInstance

example : (etaleNeighborhoodToBounded X B hX s).Full := inferInstance

example : (etaleNeighborhoodToBounded X B hX s).Faithful := inferInstance

example : IsLimit (etaleNeighborhoodStrictHenselizationCone X B hX s) :=
  etaleNeighborhoodStrictHenselizationConeIsLimit X B hX s

example : (etaleNeighborhoodStrictHenselizationCone X B hX s).pt =
    strictHenselization B X.left hX s := rfl

example (A : EtaleNeighborhood X s.hom) :
    ((etaleNeighborhoodToBounded X B hX s).obj A).val.val =
      etaleNeighborhoodMark X s.hom A := rfl

example (A : EtaleNeighborhood X s.hom) :
    (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A ≫
        (etaleNeighborhoodHom X s.hom A).left = strictHenselizationToBase B X.left hX s :=
  etaleNeighborhoodStrictHenselizationCone_π_comp_hom X B hX s A

example (A : EtaleNeighborhood X s.hom) :
    geometricPointToStrictHenselization B X.left hX s ≫
        (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A =
      etaleNeighborhoodMark X s.hom A :=
  geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π X B hX s A

example : SmallCategory (SmallEtaleNeighborhood X s) := inferInstance

example : IsCofiltered (SmallEtaleNeighborhood X s) := inferInstance

example : (smallEtaleNeighborhoodInclusion X s).Initial := inferInstance

example : IsLimit (smallEtaleNeighborhoodStrictHenselizationCone X B hX s) :=
  smallEtaleNeighborhoodStrictHenselizationConeIsLimit X B hX s

example : (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).pt =
    strictHenselization B X.left hX s := rfl

example (a : SmallEtaleNeighborhood X s) :
    IsAffine ((smallEtaleNeighborhoodToSmooth X s).obj a).left := inferInstance

example {a b : SmallEtaleNeighborhood X s} (f : a ⟶ b) :
    IsAffineHom ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map f) := by
  change IsAffineHom ((smallEtaleNeighborhoodToSmooth X s).map f).left
  infer_instance

example (a : SmallEtaleNeighborhood X s) :
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a ≫
        (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a)).left =
      strictHenselizationToBase B X.left hX s :=
  smallEtaleNeighborhoodStrictHenselizationCone_π_comp_hom X B hX s a

example (a : SmallEtaleNeighborhood X s) :
    geometricPointToStrictHenselization B X.left hX s ≫
        (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a =
      etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a) :=
  geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π X B hX s a

#print axioms initial_etaleNeighborhoodToBounded
#print axioms etaleNeighborhoodStrictHenselizationConeIsLimit
#print axioms etaleNeighborhoodStrictHenselizationCone_π_comp_hom
#print axioms geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π
#print axioms smallEtaleNeighborhoodStrictHenselizationConeIsLimit
#print axioms smallEtaleNeighborhoodStrictHenselizationCone_π_comp_hom
#print axioms geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π

end
