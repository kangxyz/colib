/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientRepresentative
public import Colib.AlgebraicGeometry.KTheory.PerfectGlobalUnitKOne

/-!
# The normalized first coefficient square represents the original forward unit K-one class

Realize the independently constructed and explicitly zero-normalized coefficient square with
separate object-row and automorphism-nerve parameters. Its actual loop-space path is equal to the
original weak-object square path. The existing inverse-prefix `loopKOneNormalization` therefore
gives the original forward unit class, including through the literal perfect inclusion.
No tensor product with arbitrary second K-inputs is inferred from this coefficient-class result.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Convexity Topology
open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual coefficient-square realization; nerve time is first and object-row time second. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:33-38"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSquareValue (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    C(unitInterval × unitInterval, (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).Delooping) :=
  ⟨fun z => bisimplexRealization (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (tensorUnitCoefficientSquare X r).val
      ((isSimplex₂_diagonal_iff _ _ _).mpr (tensorUnitCoefficientSquare X r).property)
      (StdSimplex.homeomorphI.symm z.2, StdSimplex.homeomorphI.symm z.1), by fun_prop⟩

/-- The whole two-parameter square is the original forward weak-object square, with no flip. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:41-51"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSquareValue_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (s t : unitInterval) :
    tensorUnitCoefficientSquareValue X r (s, t) =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareLoopPath
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) s t := by
  exact congrArg (fun A : (sSet (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq) _⦋1⦌ =>
    bisimplexRealization (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) A.val
      ((isSimplex₂_diagonal_iff _ _ _).mpr A.property)
      (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s))
    (tensorUnitCoefficientSquare_eq X r)

/-- Both object-row endpoints and both whole nerve faces retain their original basepoints. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:54-76"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSquareTrack (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).kZeroObjectLoop (boundedAboveFlatRankOne
      X)).Homotopy
      ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).kZeroObjectLoop
      (boundedAboveFlatRankOne X)) where
  toFun := tensorUnitCoefficientSquareValue X r
  continuous_toFun := (tensorUnitCoefficientSquareValue X r).continuous
  map_zero_left t := by
    rw [tensorUnitCoefficientSquareValue_eq]
    exact congrArg (fun p => p t)
      ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareLoopPath
        (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)).source
  map_one_left t := by
    rw [tensorUnitCoefficientSquareValue_eq]
    exact congrArg (fun p => p t)
      ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareLoopPath
        (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)).target
  prop' s t ht := by
    change tensorUnitCoefficientSquareValue X r (s, t) = _
    rw [tensorUnitCoefficientSquareValue_eq]
    exact ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareTrack
      (boundedAboveFlatRankOneUnit X r).hom
      ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)).prop' s t ht

/-- Curry the actual two-parameter tensor coefficient square into its original loop component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:79-86"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientLoopPath (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    Path ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).kZeroObjectLoop
      (boundedAboveFlatRankOne X))
      ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).kZeroObjectLoop
      (boundedAboveFlatRankOne X)) where
  toFun s := (tensorUnitCoefficientSquareTrack X r).eval s
  continuous_toFun :=
    Path.continuous_uncurry_iff.mp (tensorUnitCoefficientSquareTrack X r).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The entire coefficient loop path, before class formation, is the original automorphism path. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:89-97"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientLoopPath_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientLoopPath X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareLoopPath
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact tensorUnitCoefficientSquareValue_eq X r s t

/-- Normalize the actual coefficient path by the pre-existing inverse-prefix K-one class map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:100-103"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientKOneClass (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).K 1 :=
  loopKOneNormalization ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).kZeroObjectLoop
      (boundedAboveFlatRankOne X))
    (FundamentalGroup.fromPath ⟦tensorUnitCoefficientLoopPath X r⟧)

/-- The independently realized coefficient square represents the original forward unit class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:106-111"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientKOneClass_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientKOneClass X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).automorphismKOneClass
      (boundedAboveFlatRankOneUnit X r) := by
  unfold tensorUnitCoefficientKOneClass
  rw [tensorUnitCoefficientLoopPath_eq]
  rfl

/-- The literal perfect inclusion retains the original rank-one forward unit K-one class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientKOne.lean:114-128"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientKOneClass_inclusion (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    KMap (boundedAboveFlatPerfectInclusion_isExact (X := X.toRingedSpace)) 1
      (tensorUnitCoefficientKOneClass X r) =
      perfectGlobalUnitKOneClass X r (rankOnePerfectComplex X) := by
  rw [tensorUnitCoefficientKOneClass_eq, KMap_automorphismKOneClass,
    boundedAboveFlatRankOneUnit_global]
  apply congrArg (perfectComplexesWaldhausen X.toRingedSpace).automorphismKOneClass
  apply Iso.ext
  apply (ObjectProperty.ι (IsPerfectComplex (X := X.toRingedSpace))).map_injective
  change (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectGlobalUnitIso X r).hom.app (boundedAboveFlatRankOne X)) =
    (ObjectProperty.ι (IsPerfectComplex (X := X.toRingedSpace))).map
      ((perfectGlobalUnitIso X r).hom.app
      (rankOnePerfectComplex X))
  rw [boundedAboveFlatPerfectGlobalUnitIso_hom_original]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0556"] tensorUnitCoefficientLoopPath_eq
attribute [colib_tag "COL-0556"] tensorUnitCoefficientKOneClass_eq
attribute [colib_tag "COL-0556"] tensorUnitCoefficientKOneClass_inclusion

end AlgebraicGeometry.Scheme.Modules
