module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.PresheafWithTransfers

universe u
noncomputable section
variable (k : Type u) [Field k]

example (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ toReducedTorus k q = 0 :=
  torusIdentityAxis_toReducedTorus k q i
example (q : ℕ) (X : Cor k) :
    Function.Surjective ((toReducedTorus k q).hom.app (op X)) :=
  toReducedTorus_surjective k q X
example : reducedTorus k 1 ≅ pointedTorusCokernel k := reducedTorusOneIso k
example (q : ℕ) (P : PresheafWithTransfers.{u + 1} k) :
    (reducedTorus k q ⟶ P) ≃
      {η : torusRepresentable k q ⟶ P //
        ∀ i : Fin q, torusIdentityAxis k q i ≫ η = 0} :=
  reducedTorusHomEquiv k q P
example (q : ℕ) {X Y : Cor k} (α : X ⟶ Y) :
    transfer (torusRepresentable k q) α ≫ (toReducedTorus k q).hom.app (op X) =
      (toReducedTorus k q).hom.app (op Y) ≫ transfer (reducedTorus k q) α :=
  toReducedTorus_naturality k q α
example (q : ℕ) (X : Cor k) :
    sections (reducedTorus k q) X ≅
      AddCommGrpCat.of
        (sections (torusRepresentable k q) X ⧸ torusIdentityRelations k q X) :=
  reducedTorusSectionsIsoQuotient k q X
