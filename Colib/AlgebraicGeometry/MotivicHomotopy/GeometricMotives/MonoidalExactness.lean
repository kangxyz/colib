/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.TensorExactness
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeLefschetzShift
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusEffectiveShift
import Colib.Util.References
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Exactness of the tensor on geometric motives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction
open scoped MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local instance geometricTensorNativeExactCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance geometricTensorNativeExactSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

/-- The canonical abelian structure used in the native tensor comparisons. -/
local instance geometricTensorNativeExactGenericAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (LargePresheaves k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "D" => GeometricMotives k

private theorem actualGeometricMotivesTensorExactness :
    (∀ A : D, ∃ c : (tensorLeft A).CommShift ℤ, letI := c; (tensorLeft A).IsTriangulated) ∧
      (∀ A : D, ∃ c : (tensorRight A).CommShift ℤ, letI := c; (tensorRight A).IsTriangulated) :=
  geometricMotivesTensorExact_of_lefschetzShift k
    (effectiveLefschetzTensorIso_commShift_of_projective k
      (projectiveEffectiveTorusNatIso_commShift k))

/-- The stabilized left tensor is exact for the original effective shift comparisons. -/
@[colib_tag "COL-1239",
  colib_ref "Voevodsky2000TriangulatedMotives" "Proposition 2.1.3 and Corollary 2.1.5"
    "adaptation" "Exact geometric tensor after inverting the original Lefschetz twist"]
theorem geometricMotivesTensorLeft_exact (A : D) :
    ∃ c : (tensorLeft A).CommShift ℤ, letI := c; (tensorLeft A).IsTriangulated :=
  (actualGeometricMotivesTensorExactness k).1 A

/-- The stabilized right tensor is exact for the original effective shift comparisons. -/
@[colib_tag "COL-1239"]
theorem geometricMotivesTensorRight_exact (A : D) :
    ∃ c : (tensorRight A).CommShift ℤ, letI := c; (tensorRight A).IsTriangulated :=
  (actualGeometricMotivesTensorExactness k).2 A

attribute [colib_tag "COL-1239"]
  geometricMotiveUnitIso geometricMotiveTensorIso
  geometricMotiveTensorIso_naturality geometricMotiveTensorIso_braiding

end AlgebraicGeometry.MotivicHomotopy
