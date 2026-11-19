/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleNativeParameterSquare
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterCoordinateRoof

/-! # The actual coordinate AW roof at integral signed endpoints

Localization is performed after shifting the actual integral complexes. The
parameter pushforward is used only on concrete cochain maps, never on a localized
inverse. The original forward reindex comparison and signed boundary are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{v} (SmoothEtaleIntegralSheaves k)]

/-- The same original parameter AW denominator remains invertible after a native shift. -/
instance reducedTorusEtaleParameterShiftedAW_isIso (q : ℕ) (s : ℤ) :
    IsIso (DerivedCategory.Q.map ((shiftFunctor _ s).map
      (((smoothEtaleIntegralSheafify k).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap
          (((reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ)).map
            (reducedTorusPresheafAW k q)) ComplexShape.embeddingDownNat)))) := by
  infer_instance

/-- The literal coordinate numerator and inverse-AW denominator, followed by the
native directed target tail, recover the original integral signed parameter. -/
theorem reducedTorusEtaleSignedCoordinateRoof_eq (q : ℕ) :
    let S := SmoothEtaleIntegralSheaves k
    let a := smoothEtaleIntegralSheafify k
    let A := ComplexShape.embeddingDownNat.extendFunctor (SmoothEtaleIntegralPresheaves k) ⋙
      a.mapHomologicalComplex (.up ℤ)
    let T := (reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ)
    let L := reducedTorusOrdinaryIntegralChains k (q + 1)
    let F := reducedTorusIntegralEtaleParameterFunctor k
    let H := F.mapHomologicalComplex (.up ℤ)
    let e := ComplexShape.embeddingUpIntLE 0
    let R := SmoothSite.Contraction.parameterProduct
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let δ := (NatTrans.mapHomologicalComplex
      (R.sheafifyReindexComparison J J (ModuleCat.{u + 1} ℤ)) (.down ℕ)).app L
    let B := ((smoothEtaleIntegralNativeExtensionIso k).app (T.obj L)).hom ≫
      (e.extendFunctor S).map δ ≫
      (Stacks.DerivedIndexing.mapExtendIso F e
        ((a.mapHomologicalComplex (.down ℕ)).obj L)).hom
    let s : ℤ := -(q : ℤ)
    let t : ℤ := -((q + 1 : ℕ) : ℤ)
    let hs : t + 1 = s := by dsimp [t, s]; omega
    let W := shiftFunctor (CochainComplex S ℤ) s
    let V := W ⋙ DerivedCategory.Q
    letI : IsIso (V.map (A.map (T.map (reducedTorusPresheafAW k q)))) :=
      reducedTorusEtaleParameterShiftedAW_isIso k q s
    let b := (H.commShiftIso s).inv.app (reducedTorusIntegralEtaleOrdinaryCochain k (q + 1)) ≫
      H.map ((shiftFunctorAdd' _ t 1 s hs).hom.app
        (reducedTorusIntegralEtaleOrdinaryCochain k (q + 1)))
    ((V.map (A.map (reducedTorusChainCoordinateInsertion k q)) ≫
        V.map (A.map (T.map (reducedTorusPresheafAW k q)))) ≫
      (inv (V.map (A.map (T.map (reducedTorusPresheafAW k q)))) ≫
        V.map (A.map (T.map (reducedTorusPresheafChainPairing k q))))) ≫
      DerivedCategory.Q.map (W.map B ≫ b) =
    V.map (reducedTorusEtaleNativeOrdinaryEndpointIso k q).hom ≫
      DerivedCategory.Q.map (reducedTorusIntegralEtaleParameterSigned k q) := by
  intro S a A T L F H e R J δ B s t hs W V b
  let x := (reducedTorusEtaleNativeOrdinaryEndpointIso k q).hom
  let g := reducedTorusIntegralEtaleParameterCochain k q
  let f := reducedTorusChainCoordinateInsertion k q ≫
    T.map (reducedTorusPresheafChainPairing k q)
  have hc : A.map f ≫ B = x ≫ g := reducedTorusEtaleNativeParameterSquare k q
  have hv : V.map (A.map f) ≫ V.map B = V.map x ≫ V.map g :=
    (V.map_comp (A.map f) B).symm.trans
      ((V.congr_map hc).trans (V.map_comp x g))
  have cancelRoof {X Y Z Z' : DerivedCategory S}
      (u : X ⟶ Y) (d : Y ⟶ Z) [IsIso d] (p : Y ⟶ Z') :
      (u ≫ d) ≫ (inv d ≫ p) = u ≫ p := by
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
  have hr := @cancelRoof _ _ _ _
    (V.map (A.map (reducedTorusChainCoordinateInsertion k q)))
    (V.map (A.map (T.map (reducedTorusPresheafAW k q))))
    (reducedTorusEtaleParameterShiftedAW_isIso k q s)
    (V.map (A.map (T.map (reducedTorusPresheafChainPairing k q))))
  have hr' := hr.trans (((A ⋙ V).map_comp
    (reducedTorusChainCoordinateInsertion k q)
    (T.map (reducedTorusPresheafChainPairing k q))).symm)
  have hb : W.map g ≫ b = reducedTorusIntegralEtaleParameterSigned k q :=
    (reducedTorusIntegralEtaleParameterSigned_eq k q).symm
  have hq : V.map g ≫ DerivedCategory.Q.map b =
      DerivedCategory.Q.map (reducedTorusIntegralEtaleParameterSigned k q) :=
    (DerivedCategory.Q.map_comp (W.map g) b).symm.trans
      (DerivedCategory.Q.congr_map hb)
  exact (congrArg (fun z => z ≫ DerivedCategory.Q.map (W.map B ≫ b)) hr').trans
    ((congrArg (fun z => V.map (A.map f) ≫ z)
      (DerivedCategory.Q.map_comp (W.map B) b)).trans
      ((Category.assoc (V.map (A.map f)) (V.map B) (DerivedCategory.Q.map b)).symm.trans
        ((congrArg (fun z => z ≫ DerivedCategory.Q.map b) hv).trans
          ((Category.assoc (V.map x) (V.map g) (DerivedCategory.Q.map b)).trans
            (congrArg (fun z => V.map x ≫ z) hq)))))

end AlgebraicGeometry.PresheafWithTransfers
