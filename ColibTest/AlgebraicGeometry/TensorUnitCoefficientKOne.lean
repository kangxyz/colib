/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientKOne

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.QuotientRows Topology
open scoped Simplicial Topology unitInterval
noncomputable section
universe u

example (X : Scheme.{u}) :
    (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj (boundedAboveFlatRankOne X) =
      rankOnePerfectComplex X :=
  boundedAboveFlatRankOne_inclusion X

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatRankOneUnit X r =
      (boundedAboveFlatPerfectGlobalUnitIso X r).app (boundedAboveFlatRankOne X) :=
  boundedAboveFlatRankOneUnit_global X r

example (X : Scheme.{u}) :
    IsRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) (tensorUnitCoefficientSingle X) :=
  tensorUnitCoefficientSingle_isRow X

example (X : Scheme.{u})
    (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitCoefficientSingleAutomorphism X r).hom ≫ (tensorUnitCoefficientSingleIso X).hom =
      (tensorUnitCoefficientSingleIso X).hom ≫
        ((oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).map
          (boundedAboveFlatRankOneUnit X r).hom).hom :=
  tensorUnitCoefficientSingleAutomorphism_comparison X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientWeakArrow X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).oneWeakArrow
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) :=
  tensorUnitCoefficientWeakArrow_eq X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientSquare X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSimplex
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) :=
  tensorUnitCoefficientSquare_eq X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (s t : unitInterval) :
    tensorUnitCoefficientSquareValue X r (s, t) =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareLoopPath
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) s t :=
  tensorUnitCoefficientSquareValue_eq X r s t

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientLoopPath X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSquareLoopPath
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) :=
  tensorUnitCoefficientLoopPath_eq X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientKOneClass X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).automorphismKOneClass
      (boundedAboveFlatRankOneUnit X r) :=
  tensorUnitCoefficientKOneClass_eq X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    KMap (boundedAboveFlatPerfectInclusion_isExact (X := X.toRingedSpace)) 1
      (tensorUnitCoefficientKOneClass X r) =
      perfectGlobalUnitKOneClass X r (rankOnePerfectComplex X) :=
  tensorUnitCoefficientKOneClass_inclusion X r

