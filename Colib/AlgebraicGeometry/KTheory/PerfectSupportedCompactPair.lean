/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedPairPullback

/-! # Original compact-ambient support square -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X' X : Scheme.{u}} {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) [CompactSpace X'] [CompactSpace X]
/-- The same original support square in the existing compact-base pair category. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/PairSquares.lean:41"
  "adaptation" "Original actual supported algebraic pullback and restriction square."]
def qcSupportedBaseSquare :
    (⟨supportOpenPair S, (by change CompactSpace X'; infer_instance)⟩ :
      AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk f

end AlgebraicGeometry.Scheme.Modules
