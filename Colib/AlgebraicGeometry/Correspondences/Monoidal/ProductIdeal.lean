/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.IntersectionIdeal
public import Colib.Algebra.Category.ModuleCat.Tor.ExteriorQuotient
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionMultiplicity

/-!
# The actual ideal of a product of two closed supports

The product closed immersion has kernel equal to the sum of the two
pulled-back ideals. The proof uses the closed-immersion universal property
in both directions, so the equality keeps nilpotents. This is the geometric
kernel input for the scalar-extended exterior quotient module comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (I : X.IdealSheafData) (J : Y.IdealSheafData)

/-- The literal product of the two original closed subschemes in the ambient product. -/
def productClosedInclusion : pullback (I.subschemeι ≫ f) (J.subschemeι ≫ g) ⟶ pullback f g :=
  pullback.map _ _ _ _ I.subschemeι J.subschemeι (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem productClosedInclusion_fst :
    productClosedInclusion f g I J ≫ pullback.fst f g =
      pullback.fst (I.subschemeι ≫ f) (J.subschemeι ≫ g) ≫ I.subschemeι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem productClosedInclusion_snd :
    productClosedInclusion f g I J ≫ pullback.snd f g =
      pullback.snd (I.subschemeι ≫ f) (J.subschemeι ≫ g) ≫ J.subschemeι :=
  pullback.lift_snd _ _ _

instance productClosedInclusion_isClosedImmersion :
    IsClosedImmersion (productClosedInclusion f g I J) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance rfl rfl

/-- The product ideal is the sum of the two pulled ideals, without taking radicals. -/
theorem productClosedInclusion_ker :
    (productClosedInclusion f g I J).ker =
      I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g) := by
  let r := productClosedInclusion f g I J
  let K := I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)
  apply le_antisymm
  · have hI : (I.comap (pullback.fst f g)).subschemeι.ker ≤ K.subschemeι.ker := by
      rw [IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι]
      exact le_sup_left
    have hJ : (J.comap (pullback.snd f g)).subschemeι.ker ≤ K.subschemeι.ker := by
      rw [IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι]
      exact le_sup_right
    let d := IsClosedImmersion.lift (I.comap (pullback.fst f g)).subschemeι K.subschemeι hI
    let e := IsClosedImmersion.lift (J.comap (pullback.snd f g)).subschemeι K.subschemeι hJ
    let a := d ≫ (I.comapIso (pullback.fst f g)).hom ≫
      pullback.snd (pullback.fst f g) I.subschemeι
    let b := e ≫ (J.comapIso (pullback.snd f g)).hom ≫
      pullback.snd (pullback.snd f g) J.subschemeι
    have ha : a ≫ I.subschemeι = K.subschemeι ≫ pullback.fst f g := by
      dsimp only [a]
      rw [Category.assoc, Category.assoc, ← pullback.condition,
        IdealSheafData.comapIso_hom_fst_assoc, ← Category.assoc]
      exact congrArg (· ≫ pullback.fst f g) (IsClosedImmersion.lift_fac _ _ hI)
    have hb : b ≫ J.subschemeι = K.subschemeι ≫ pullback.snd f g := by
      dsimp only [b]
      rw [Category.assoc, Category.assoc, ← pullback.condition,
        IdealSheafData.comapIso_hom_fst_assoc, ← Category.assoc]
      exact congrArg (· ≫ pullback.snd f g) (IsClosedImmersion.lift_fac _ _ hJ)
    have hab : a ≫ (I.subschemeι ≫ f) = b ≫ (J.subschemeι ≫ g) := by
      rw [← Category.assoc, ha, Category.assoc, pullback.condition,
        ← Category.assoc, ← hb, Category.assoc]
    let w := pullback.lift a b hab
    have hw : w ≫ r = K.subschemeι := by
      apply pullback.hom_ext
      · simpa only [r, w, Category.assoc, productClosedInclusion_fst,
          pullback.lift_fst_assoc] using ha
      · simpa only [r, w, Category.assoc, productClosedInclusion_snd,
          pullback.lift_snd_assoc] using hb
    have hker := Scheme.Hom.le_ker_comp w r
    rwa [hw, IdealSheafData.ker_subschemeι] at hker
  · have hI : I.comap (pullback.fst f g) ≤ r.ker := by
      let a := pullback.lift r (pullback.fst (I.subschemeι ≫ f) (J.subschemeι ≫ g))
        (productClosedInclusion_fst f g I J)
      have hker := Scheme.Hom.le_ker_comp a
        (pullback.fst (pullback.fst f g) I.subschemeι)
      have ha : a ≫ pullback.fst (pullback.fst f g) I.subschemeι = r :=
        pullback.lift_fst _ _ _
      rw [ha, IdealSheafData.ker_fst_of_isClosedImmersion,
        IdealSheafData.ker_subschemeι] at hker
      exact hker
    have hJ : J.comap (pullback.snd f g) ≤ r.ker := by
      let b := pullback.lift r (pullback.snd (I.subschemeι ≫ f) (J.subschemeι ≫ g))
        (productClosedInclusion_snd f g I J)
      have hker := Scheme.Hom.le_ker_comp b
        (pullback.fst (pullback.snd f g) J.subschemeι)
      have hb : b ≫ pullback.fst (pullback.snd f g) J.subschemeι = r :=
        pullback.lift_fst _ _ _
      rw [hb, IdealSheafData.ker_fst_of_isClosedImmersion,
        IdealSheafData.ker_subschemeι] at hker
      exact hker
    exact sup_le hI hJ

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

open scoped TensorProduct

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (I : X.IdealSheafData) (J : Y.IdealSheafData)

/-- At each actual product point the closed product ideal is the sum of the mapped stalk ideals. -/
theorem productClosedInclusion_idealStalk (x : pullback (C := Scheme) f g) :
    IdealSheafData.stalk (Scheme.Hom.productClosedInclusion f g I J).ker x =
      (IdealSheafData.stalk I (pullback.fst f g x)).map ((pullback.fst f g).stalkMap x).hom ⊔
        (IdealSheafData.stalk J (pullback.snd f g x)).map ((pullback.snd f g).stalkMap x).hom := by
  rw [Scheme.Hom.productClosedInclusion_ker, IdealSheafData.stalk_sup,
    IdealSheafData.stalk_comap, IdealSheafData.stalk_comap]

/-- Any tensor-to-stalk map with the two actual projection maps carries the native product ideal
to the actual closed product stalk ideal. In the application the map is supplied by the native
localization theorem for product stalks. -/
theorem productClosedInclusion_idealStalk_eq_map_productIdeal
    {k : Type u} [Field k] (x : pullback (C := Scheme) f g)
    [Algebra k (X.presheaf.stalk (pullback.fst f g x))]
    [Algebra k (Y.presheaf.stalk (pullback.snd f g x))]
    (φ : (X.presheaf.stalk (pullback.fst f g x)) ⊗[k]
      (Y.presheaf.stalk (pullback.snd f g x)) →+* (pullback f g).presheaf.stalk x)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom =
      ((pullback.fst f g).stalkMap x).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap x).hom) :
    IdealSheafData.stalk (Scheme.Hom.productClosedInclusion f g I J).ker x =
      (ModuleCat.Tor.productIdeal (k := k)
        (IdealSheafData.stalk I (pullback.fst f g x))
        (IdealSheafData.stalk J (pullback.snd f g x))).map φ := by
  rw [productClosedInclusion_idealStalk, ModuleCat.Tor.productIdeal,
    Ideal.map_sup, Ideal.map_map, Ideal.map_map]
  rw [← hleft, ← hright]
  rfl

end Stacks.Chow

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y A B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (i : A ⟶ X) (j : B ⟶ Y)

/-- Product of the two given closed immersions, retaining their original source schemes. -/
def productClosedMap : pullback (i ≫ f) (j ≫ g) ⟶ pullback f g :=
  pullback.map _ _ _ _ i j (𝟙 S) (by simp) (by simp)

instance productClosedMap_isClosedImmersion [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (productClosedMap f g i j) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance rfl rfl

/-- The same product-ideal identity for the original closed immersions, without replacing them
by the subschemes of their kernels in the statement. -/
theorem productClosedMap_ker [IsClosedImmersion i] [IsClosedImmersion j] :
    (productClosedMap f g i j).ker =
      i.ker.comap (pullback.fst f g) ⊔ j.ker.comap (pullback.snd f g) := by
  let : IsIso i.toImage := IsClosedImmersion.instIsIsoSchemeToImage i
  let : IsIso j.toImage := IsClosedImmersion.instIsIsoSchemeToImage j
  let m : pullback (i ≫ f) (j ≫ g) ⟶
      pullback (i.ker.subschemeι ≫ f) (j.ker.subschemeι ≫ g) :=
    pullback.map _ _ _ _ i.toImage j.toImage (𝟙 S) (by
      simp only [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι]) (by
      simp only [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι])
  let : IsIso m := by
    dsimp only [m]
    infer_instance
  have hm : m ≫ productClosedInclusion f g i.ker j.ker = productClosedMap f g i j := by
    apply pullback.hom_ext <;>
      simp [m, productClosedInclusion, productClosedMap, pullback.map, Category.assoc]
  rw [← hm, Scheme.Hom.ker_comp_of_isIso, productClosedInclusion_ker]

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

open scoped TensorProduct

variable {S X Y A B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (i : A ⟶ X) (j : B ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]

/-- The mapped product-ideal formula for the actual original closed source schemes. -/
theorem productClosedMap_idealStalk_eq_map_productIdeal
    {k : Type u} [Field k] (x : pullback (C := Scheme) f g)
    [Algebra k (X.presheaf.stalk (pullback.fst f g x))]
    [Algebra k (Y.presheaf.stalk (pullback.snd f g x))]
    (φ : (X.presheaf.stalk (pullback.fst f g x)) ⊗[k]
      (Y.presheaf.stalk (pullback.snd f g x)) →+* (pullback f g).presheaf.stalk x)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom =
      ((pullback.fst f g).stalkMap x).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap x).hom) :
    IdealSheafData.stalk (Scheme.Hom.productClosedMap f g i j).ker x =
      (ModuleCat.Tor.productIdeal (k := k)
        (IdealSheafData.stalk i.ker (pullback.fst f g x))
        (IdealSheafData.stalk j.ker (pullback.snd f g x))).map φ := by
  rw [Scheme.Hom.productClosedMap_ker, IdealSheafData.stalk_sup,
    IdealSheafData.stalk_comap, IdealSheafData.stalk_comap,
    ModuleCat.Tor.productIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_map]
  rw [← hleft, ← hright]
  rfl

end Stacks.Chow
