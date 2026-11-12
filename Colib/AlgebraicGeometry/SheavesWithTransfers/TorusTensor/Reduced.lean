/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Normalization
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor

/-!
# The reduced tensor on transfer representables

The target unit inclusion and projection split the original
torus-product representable. Exact sheafification identifies its
cokernel with the sheafification of the original transfer quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers
open AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- The quotient by the actual unit in the sheafified torus-product representable. -/
abbrev reducedTorusTensorRepresentable (X : Cor k) : SheafWithTransfers.{u + 1} k :=
  cokernel ((transferRepresentable k).map (torusUnitCorrespondence k X))

/-- The reduced tensor is the sheafification of the original target unit quotient. -/
def reducedTorusTensorRepresentableIso (X : Cor k) :
    reducedTorusTensorRepresentable k X ≅ (nisnevichSheafify k).obj
      (torusCancellationCoefficients k X) := by
  let f := (representableLarge k).map (torusUnitCorrespondence k X)
  let a := nisnevichSheafify k
  change cokernel (a.map f) ≅ a.obj (cokernel f)
  exact (PreservesCokernel.iso a f).symm

/-- The target quotient comparison retains the actual cokernel projection. -/
@[reassoc]
theorem reducedTorusTensorRepresentableIso_π (X : Cor k) :
    cokernel.π ((transferRepresentable k).map (torusUnitCorrespondence k X)) ≫
      (reducedTorusTensorRepresentableIso k X).hom =
    (nisnevichSheafify k).map (toTorusCancellationCoefficients k X) := by
  let f := (representableLarge k).map (torusUnitCorrespondence k X)
  let a := nisnevichSheafify k
  let e := PreservesCokernel.iso a f
  change cokernel.π (a.map f) ≫ e.inv = a.map (cokernel.π f)
  exact (e.comp_inv_eq).2 (PreservesCokernel.π_iso_hom a f).symm

end AlgebraicGeometry.SheafWithTransfers
