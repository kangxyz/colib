import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleRigidityTorsion

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open AlgebraicGeometry.PresheafWithTransfers

universe u

example (k : Type u) [Field k]
    (F : Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :
    IsLocallyConstant k F ↔
      IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F) :=
  Iff.rfl

example {k : Type u} [Field k]
    (P : AlgebraicGeometry.PresheafWithTransfers.{u + 1} k)
    (hA : AlgebraicGeometry.PresheafWithTransfers.IsA1Invariant P)
    (hT : AlgebraicGeometry.PresheafWithTransfers.IsPrimeToCharacteristicTorsion P) :
    IsLocallyConstant k ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((AlgebraicGeometry.PresheafWithTransfers.toPresheaf k).obj P)) :=
  isLocallyConstant_sheafification_of_primeToCharacteristicTorsion
    P hA hT
