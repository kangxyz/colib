/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSourceTrack
public import Colib.KTheory.Bass.NaturalTrack

/-! # The original whole scheme current-transition comparison

The actual original coefficient track, finite-stage seed and literal row target are retained.
No stable class substitutes for the whole map or normalized boundary homotopy.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSquareInterchange GeometricSeedCospan SquareConeStrength
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The original whole null/unit/null seed, using the actual geometric diagonal. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeNaturalSeed.lean:27"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def seed (A : Track laurent.op coefficient F) :
    F ⟶ (strictDiagramFunctor squareFunctor).obj F :=
  WholeSeedCospan.seed (geometricSquare F) (sourceTrack F A.homotopy)
    (sourceTrack_naturality F A.homotopy A.naturality)

end KTheory.Bass.SchemeNaturalSeed
