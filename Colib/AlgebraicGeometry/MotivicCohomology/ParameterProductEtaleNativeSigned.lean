/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.ParameterProductNativeSigned
public import Colib.AlgebraicGeometry.MotivicCohomology.EtaleNativeParameterSigned

/-! # The original motivic parameter through directed topology change

This identifies the topology-changed original parameter, with its actual forward
comparison tail, with the existing native signed étale arrow at canonical motivic
endpoints. It does not invert parameter pushforward or define a replacement beta.
The AW-coordinate calculation still has to be joined at the integral endpoint.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original parameter keeps the directed topology tail and both canonical
endpoint isomorphisms, including the coefficient-free native signed boundary. -/
theorem motivicSheafParameterProduct_etale_nativeSigned (q : ℕ) :
    let E := (SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)
    let G := (reducedTorusEtaleParameterFunctor k).mapHomologicalComplex (.up ℤ)
    let τ := SmoothSite.parameterChangeOfTopologyComplexComparison
      (Spec (CommRingCat.of k))
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
      AddCommGrpCat.{u + 1} (.up ℤ)
    E.map (motivicSheafParameterProduct k q) ≫
      τ.app ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧) ≫
      G.map ((E.commShiftIso (1 : ℤ)).hom.app (motivicSheafComplex k (q + 1))) =
    signedParameterArrow G (reducedTorusEtaleParameterCochain k q)
      (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega)
      (E.mapIso (motivicSheafComplexOrdinaryShiftIso k q) ≪≫
        reducedTorusEtaleTopologySignedIso k q)
      (E.mapIso (motivicSheafComplexOrdinaryShiftIso k (q + 1)) ≪≫
        reducedTorusEtaleTopologySignedIso k (q + 1)) := by
  intro E G τ
  have ht : τ.app (reducedTorusNisnevichOrdinaryCochain k (q + 1)) =
      (NatTrans.mapHomologicalComplex
        (SmoothSite.parameterNisnevichToEtaleComparison (Spec (CommRingCat.of k))
          AddCommGrpCat.{u + 1}
          (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))))
        (.up ℤ)).app (reducedTorusNisnevichOrdinaryCochain k (q + 1)) := by
    apply HomologicalComplex.hom_ext
    intro i
    exact SmoothSite.parameterChangeOfTopologyComplexComparison_app_f
      (Spec (CommRingCat.of k))
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
      AddCommGrpCat.{u + 1} (.up ℤ) _ i
  have hext : E.map (reducedTorusNisnevichParameterCochain k q) ≫
      τ.app (reducedTorusNisnevichOrdinaryCochain k (q + 1)) ≫
      G.map (reducedTorusEtaleTopologyCochainIso k (q + 1)).hom =
      (reducedTorusEtaleTopologyCochainIso k q).hom ≫
        reducedTorusEtaleParameterCochain k q := by
    rw [ht]
    exact reducedTorusEtaleTopologyCochainSquare k q
  rw [motivicSheafParameterProduct_eq_nativeSigned]
  simpa only [reducedTorusEtaleTopologySignedIso, Iso.trans_assoc] using
    (signedParameterArrow_transport E
      ((torusParameterSheafFunctor k).mapHomologicalComplex (.up ℤ)) G τ
      (reducedTorusNisnevichParameterCochain k q)
      (reducedTorusEtaleParameterCochain k q)
      (reducedTorusEtaleTopologyCochainIso k q)
      (reducedTorusEtaleTopologyCochainIso k (q + 1)) hext
      (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega)
      (motivicSheafComplexOrdinaryShiftIso k q)
      (motivicSheafComplexOrdinaryShiftIso k (q + 1)))

end AlgebraicGeometry.PresheafWithTransfers
