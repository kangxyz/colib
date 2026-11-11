/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeBetaRecursion
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeAction
public import Colib.KTheory.Bass.NormalizedStageAction

/-!
# Fixed actual cone words preserve the whole induced action

The original twice-cone geometric permutation preserves the actual action. Cone preservation
and composition propagate that local theorem through the already specified finite words.
All tracks are the existing original cone iterates, with unchanged time and inverse index
maps. No whole-word equivariance premise or additional seed condition is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange NaturalTrack
variable {U : Scheme.{u}} (q : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track (baseProductFunctor q).op (NatTrans.op (baseProductProjection q)) F)

/-- Every fixed insertion word preserves the original whole induced action at the same time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWordAction.lean:34"
  "adaptation" "Original induction proving complete fixed-word equivariance, with unchanged time."]
theorem betaAt_equivariant (i : ℕ) :
    Equivariant
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) (i + 1))
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) (i + 1))
      (betaAt i F).hom := by
  induction i with
  | zero =>
    rw [betaAt_zero_hom]
    exact Equivariant.id _
  | succ i ih =>
    rw [betaAt_succ_hom]
    exact (permutation_equivariant q
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) i)).comp
      (ih.cone (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q))

/-- Every accumulated fixed word preserves the original whole induced action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWordAction.lean:58"
  "adaptation" "Original induction proving complete fixed-word equivariance, with unchanged time."]
theorem wordAt_equivariant (i : ℕ) :
    Equivariant
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) i)
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) i)
      (wordAt i F).hom := by
  induction i with
  | zero =>
    rw [wordAt_zero_hom]
    exact Equivariant.id A
  | succ i ih =>
    rw [wordAt_succ_hom]
    exact (ih.cone (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q)).comp
      (betaAt_equivariant q A i)

end KTheory.Bass.GeometricConeFixedWords
