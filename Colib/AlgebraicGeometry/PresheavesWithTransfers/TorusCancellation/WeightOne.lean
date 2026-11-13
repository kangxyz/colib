/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products

/-! # The base target quotient and the weight-one coefficient -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => SmoothSite.base S
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "A" => representableLarge k

private def baseProductSndIso (T : SmoothSite S) : SmoothSite.product B T ≅ T where
  hom := SmoothSite.productSnd B T
  inv := SmoothSite.productLift (toBase T) (𝟙 T)
  hom_inv_id := by
    apply SmoothSite.product_hom_ext
    · rw [Category.assoc, SmoothSite.productLift_fst, Category.id_comp]
      exact (comp_toBase (SmoothSite.productSnd B T)).trans
        (comp_toBase (SmoothSite.productFst B T)).symm
    · simp only [Category.assoc, SmoothSite.productLift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := SmoothSite.productLift_snd _ _

private theorem baseProductSndIso_unit :
    SmoothSite.productMap (𝟙 B) (SmoothSite.torusOne S) ≫ (baseProductSndIso k G).hom =
      (baseProductSndIso k B).hom ≫ SmoothSite.torusOne S := SmoothSite.productMap_snd _ _

/-- The original target unit quotient at the base is the weight-one coefficient. -/
def torusCancellationBaseWeightOneIso :
    torusCancellationCoefficients k (Cor.mk B) ≅ reducedTorus k 1 := by
  let V : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    PresheafWithTransfers.forget
  let R := representableLarge k
  let F := Cor.graphFunctor k
  let t := SmoothSite.productMap (𝟙 B) (SmoothSite.torusOne S)
  let f := R.map (F.map t)
  let g := R.map (F.map (SmoothSite.torusOne S))
  let e := (F ⋙ R).mapIso (baseProductSndIso k B)
  let d := (F ⋙ R).mapIso (baseProductSndIso k G)
  have h : f ≫ d.hom = e.hom ≫ g := by
    let E := F ⋙ R
    calc
      _ = E.map (t ≫ (baseProductSndIso k G).hom) := (E.map_comp _ _).symm
      _ = E.map ((baseProductSndIso k B).hom ≫ SmoothSite.torusOne S) :=
        E.congr_map (baseProductSndIso_unit k)
      _ = _ := E.map_comp _ _
  let z := PreservesCokernel.iso V f ≪≫
    cokernel.mapIso (V.map f) (V.map g) (V.mapIso e) (V.mapIso d)
      ((V.map_comp _ _).symm.trans ((V.congr_map h).trans (V.map_comp _ _)))
  let r : torusCancellationCoefficients k (Cor.mk B) ≅ pointedTorusCokernel k :=
    (Functor.FullyFaithful.ofFullyFaithful V).preimageIso z
  exact r ≪≫ (reducedTorusOneIso k).symm

end AlgebraicGeometry.PresheafWithTransfers
