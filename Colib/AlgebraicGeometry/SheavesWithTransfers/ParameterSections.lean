/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Pushforward
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.ParameterNaturality

/-!
# Ordinary parameter sections of Nisnevich sheaves with transfers

These are the original reindexing constructions formerly owned by the derived
parameter-sections module. They require no derived category or Ext machinery.
The graph comparisons and the original restriction maps are unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The original integral parameter product agrees with the smooth parameter
product on graph correspondences. -/
def parameterProductGraphIso (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    graphFunctor k ⋙ parameterProduct T ≅
      SmoothSite.Contraction.parameterProduct T ⋙ graphFunctor k :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change (parameterProduct T).map ((graphFunctor k).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (graphFunctor k).map (SmoothSite.productMap f (𝟙 T))
    rw [Category.comp_id, Category.id_comp]
    exact parameterProduct_graph T f)

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "Base(" K ")" => Spec (CommRingCat.of K)
local notation "Nis(" K ")" => SmoothSite.nisnevichTopology Base(K)

variable {T : SmoothSite Base(k)} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

/-- Underlying presheaves of the reindexed coefficients are the ordinary
smooth parameter sections. -/
def parameterPrecomposeUnderlyingIso (P : PresheafWithTransfers.{u + 1} k) :
    (toPresheaf k).obj ((additivePrecompose F).obj P) ≅
      (SmoothSite.Contraction.parameterProduct T).op ⋙ (toPresheaf k).obj P :=
  NatIso.ofComponents (fun X => P.obj.mapIso ((NatIso.op e.symm).app X)) (by
    intro X Y f
    let d := NatIso.op e.symm
    change P.obj.map ((Cor.graphFunctor k ⋙ F).op.map f) ≫ P.obj.map (d.hom.app Y) =
      P.obj.map (d.hom.app X) ≫
        P.obj.map ((SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k).op.map f)
    rw [← P.obj.map_comp, ← P.obj.map_comp, d.hom.naturality])

/-- Reindex along the correspondence functor while retaining the Nisnevich
sheaf condition given by ordinary parameter continuity. -/
def parameterSectionsOfGraphIso : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k :=
  (IsNisnevichSheaf k).lift (SheafWithTransfers.forget k ⋙ additivePrecompose F) (fun I => by
    apply (Presheaf.isSheaf_of_iso_iff (parameterPrecomposeUnderlyingIso e I.obj)).2
    exact (SmoothSite.Contraction.parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ _ I.property)

instance : (parameterSectionsOfGraphIso e).Additive where
  map_add := by
    intro P Q f g
    apply ObjectProperty.hom_ext
    rfl

/-- Forgetting transfers gives ordinary parameter sections, with the
original coefficient restrictions. -/
def parameterSectionsOfGraphIsoToSheaf :
    parameterSectionsOfGraphIso e ⋙ toSheaf k ≅
      toSheaf k ⋙ (SmoothSite.Contraction.parameterProduct T).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} Nis(k) Nis(k) :=
  NatIso.ofComponents (fun I => ObjectProperty.isoMk _ (parameterPrecomposeUnderlyingIso e I.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      exact (f.hom.hom.naturality ((NatIso.op e.symm).hom.app X)).symm)

/-- The original integral parameter sections use the same reindexed
coefficients and signed transfers. -/
def parameterSectionsOfGraphIsoIntegral (T : SmoothSite Base(k)) [GeometricallyIntegral T.hom] :
    parameterSectionsOfGraphIso (Cor.parameterProductGraphIso T) ≅ parameterSectionsFunctor k T :=
  Iso.refl _

end AlgebraicGeometry.SheafWithTransfers
