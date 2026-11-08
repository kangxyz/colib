module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorGrade

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Disconnected ambient schemes and arbitrary fields; the grade is proved, not supplied.
example [IsSeparated h]
    [LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h)]
    [LocallyOfFiniteType (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (η : genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v)) :
    letI := isFinite_correspondenceIncidenceToImage f g h z w hz hw
    let π := correspondenceLeftExteriorProjection f g h i z w v
    let sI := (correspondenceIncidenceMap f g h z w).toImage ≫
      correspondenceIntermediateImageTarget f g h z w ≫ h
    flatPullbackWeight (fieldChowSituation K) (π ≫ sI) π
      (relativeDimension (fieldChowSituation K).dimensionFunction sI (π η.1) +
        (correspondenceThirdSupportDimension K h i v : ℤ)) η.1 =
      (correspondenceLeftExteriorFiberLength f g h i z w v η.1 : ℤ) :=
  flatPullbackWeight_correspondenceLeftExterior_originalGrade K f g h i z w v hz hw η

#check relativeDimension_correspondenceLeftExteriorProjection
#check relativeDimension_correspondenceLeftExterior_generic
#check flatPullbackWeight_correspondenceLeftExterior_originalGrade
