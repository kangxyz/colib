/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Indexing

/-! # Inverse images of coniveau supports under open immersions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite Order TopologicalSpace AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

attribute [local instance] specializationOrder

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable {X Y T : Sm(k)}

/-- The inverse image of the underlying closed subset under the ambient map. -/
abbrev supportPreimage (f : Y ⟶ X) (Z : Closeds X.left) : Closeds Y.left :=
  Z.preimage f.left.continuous

theorem supportPreimage_mono (f : Y ⟶ X) {Z W : Closeds X.left} (h : Z ≤ W) :
    supportPreimage k f Z ≤ supportPreimage k f W := by
  change f.left ⁻¹' (Z : Set X.left) ⊆ f.left ⁻¹' (W : Set X.left)
  exact Set.preimage_mono h

private theorem supportOpenPreimageMap_range (f : Y ⟶ X) (Z : Closeds X.left) :
    Set.range ((supportOpenInclusion k Y (supportPreimage k f Z)).left ≫ f.left) ⊆
      Set.range (supportOpenInclusion k X Z).left := by
  change Set.range (AlgebraicGeometry.Scheme.Opens.ι (supportPreimage k f Z).compl ≫ f.left) ⊆
    Set.range (AlgebraicGeometry.Scheme.Opens.ι Z.compl)
  rw [AlgebraicGeometry.Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact x.2

/-- The original map on complementary opens over an ambient morphism. -/
@[no_expose]
def supportOpenPreimageMap (f : Y ⟶ X) (Z : Closeds X.left) :
    (SmoothSite.opensFunctor Y).obj (supportPreimage k f Z).compl ⟶
      (SmoothSite.opensFunctor X).obj Z.compl :=
  let i := supportOpenInclusion k Y (supportPreimage k f Z)
  let j := supportOpenInclusion k X Z
  let a := IsOpenImmersion.lift j.left (i.left ≫ f.left) (supportOpenPreimageMap_range k f Z)
  SmoothSite.homMk a (by
    rw [← MorphismProperty.Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac,
      Category.assoc, MorphismProperty.Over.w f, MorphismProperty.Over.w i])

/-- The map on open complements lies over the ambient morphism. -/
@[reassoc]
theorem supportOpenPreimageMap_comp_inclusion (f : Y ⟶ X) (Z : Closeds X.left) :
    supportOpenPreimageMap k f Z ≫ supportOpenInclusion k X Z =
      supportOpenInclusion k Y (supportPreimage k f Z) ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact IsOpenImmersion.lift_fac _ _ _

private instance supportOpenInclusion_mono (Z : Closeds X.left) :
    Mono (supportOpenInclusion k X Z) :=
  (SmoothSite.forgetScheme _).mono_of_mono_map
    (inferInstanceAs (Mono (AlgebraicGeometry.Scheme.Opens.ι (X := X.left) Z.compl)))

/-- The maps on complementary opens commute with inclusions of closed supports. -/
@[reassoc]
theorem supportOpenPreimageMap_naturality (f : Y ⟶ X) {Z W : Closeds X.left} (h : Z ≤ W) :
    supportOpenMap k Y (supportPreimage_mono k f h) ≫ supportOpenPreimageMap k f Z =
      supportOpenPreimageMap k f W ≫ supportOpenMap k X h := by
  apply (cancel_mono (supportOpenInclusion k X Z)).mp
  simp only [Category.assoc, supportOpenPreimageMap_comp_inclusion,
    supportOpenMap_comp_inclusion, supportOpenMap_comp_inclusion_assoc]

/-- Restricting the identity to a complementary open gives its identity. -/
theorem supportOpenPreimageMap_id (Z : Closeds X.left) :
    supportOpenPreimageMap k (𝟙 X) Z = 𝟙 _ := by
  apply (cancel_mono (supportOpenInclusion k X Z)).mp
  rw [supportOpenPreimageMap_comp_inclusion, Category.id_comp, Category.comp_id]
  rfl

/-- Restriction to complementary opens respects composition of ambient maps. -/
theorem supportOpenPreimageMap_comp (f : T ⟶ Y) (g : Y ⟶ X) (Z : Closeds X.left) :
    supportOpenPreimageMap k (f ≫ g) Z =
      supportOpenPreimageMap k f (supportPreimage k g Z) ≫ supportOpenPreimageMap k g Z := by
  apply (cancel_mono (supportOpenInclusion k X Z)).mp
  rw [Category.assoc, supportOpenPreimageMap_comp_inclusion,
    supportOpenPreimageMap_comp_inclusion, supportOpenPreimageMap_comp_inclusion_assoc]
  rfl

/-- Composing smooth-site morphisms preserves the open-immersion condition on their left maps. -/
instance isOpenImmersion_smoothSite_comp (f : T ⟶ Y) (g : Y ⟶ X)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] : IsOpenImmersion (f ≫ g).left :=
  inferInstanceAs (IsOpenImmersion (f.left ≫ g.left))

/-- Taking inverse images along open immersions preserves the codimension bound. -/
def coniveauSupportsPreimage (f : Y ⟶ X) [IsOpenImmersion f.left] (a : ℕ) :
    ConiveauSupports k X a ⥤ ConiveauSupports k Y a :=
  Monotone.functor (f := fun Z ↦ ⟨supportPreimage k f Z.1, fun x hx ↦
    (Z.2 (f.left x) hx).trans (Topology.IsOpenEmbedding.coheight_eq (x := x)
      f.left f.left.isOpenEmbedding).le⟩)
    (fun _ _ h ↦ supportPreimage_mono k f h)

/-- Taking inverse images of both supports in a nested pair. -/
def coniveauSupportPairsPreimage (f : Y ⟶ X) [IsOpenImmersion f.left] (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ ConiveauSupportPairs k Y a b :=
  Monotone.functor (f := fun ZW ↦ ⟨((coniveauSupportsPreimage k f b).obj ZW.1.1,
      (coniveauSupportsPreimage k f a).obj ZW.1.2), supportPreimage_mono k f ZW.2⟩)
    (fun _ _ h ↦ ⟨supportPreimage_mono k f h.1, supportPreimage_mono k f h.2⟩)

/-- The original arrow of open pairs over the preimage of a closed support. -/
def supportOpenPairPreimageMap (f : Y ⟶ X) (Z : Closeds X.left) :
    Arrow.mk (supportOpenInclusion k Y (supportPreimage k f Z)) ⟶
      Arrow.mk (supportOpenInclusion k X Z) :=
  Arrow.homMk' (supportOpenPreimageMap k f Z) f
    (supportOpenPreimageMap_comp_inclusion k f Z)

/-- Restriction of open pairs commutes with inclusions of supports. -/
theorem supportOpenPairPreimageMap_naturality (f : Y ⟶ X) {Z W : Closeds X.left}
    (m : Z ⟶ W) :
    (supportOpenPairFunctor k Y).map (homOfLE (supportPreimage_mono k f m.le)).op ≫
        supportOpenPairPreimageMap k f Z =
      supportOpenPairPreimageMap k f W ≫ (supportOpenPairFunctor k X).map m.op := by
  apply Arrow.hom_ext
  · exact supportOpenPreimageMap_naturality k f m.le
  · exact (Category.id_comp f).trans (Category.comp_id f).symm

/-- The actual map of nested complementary opens. -/
def supportPairPreimageMap (f : Y ⟶ X) [IsOpenImmersion f.left] {a b : ℕ}
    (ZW : ConiveauSupportPairs k X a b) :
    (coniveauSupportPairsInclusion k Y a b).obj
        (op ((coniveauSupportPairsPreimage k f a b).obj ZW)) ⟶
      (coniveauSupportPairsInclusion k X a b).obj (op ZW) :=
  Arrow.homMk' (supportOpenPreimageMap k f ZW.1.2.1) (supportOpenPreimageMap k f ZW.1.1.1)
    (supportOpenPreimageMap_naturality k f ZW.2).symm

/-- Restriction of the nested pairs commutes with enlarging both supports. -/
theorem supportPairPreimageMap_naturality (f : Y ⟶ X) [IsOpenImmersion f.left] {a b : ℕ}
    {ZW ZW' : ConiveauSupportPairs k X a b} (m : ZW ⟶ ZW') :
    (coniveauSupportPairsInclusion k Y a b).map
        ((coniveauSupportPairsPreimage k f a b).map m).op ≫ supportPairPreimageMap k f ZW =
      supportPairPreimageMap k f ZW' ≫ (coniveauSupportPairsInclusion k X a b).map m.op := by
  apply Arrow.hom_ext
  · exact supportOpenPreimageMap_naturality k f m.le.2
  · exact supportOpenPreimageMap_naturality k f m.le.1

/-- Restriction of an open pair along the identity gives its identity arrow. -/
theorem supportOpenPairPreimageMap_id (Z : Closeds X.left) :
    supportOpenPairPreimageMap k (𝟙 X) Z = 𝟙 _ := by
  apply Arrow.hom_ext
  · exact supportOpenPreimageMap_id k Z
  · rfl

/-- Restriction of open pairs respects composition of ambient maps. -/
theorem supportOpenPairPreimageMap_comp (f : T ⟶ Y) (g : Y ⟶ X) (Z : Closeds X.left) :
    supportOpenPairPreimageMap k (f ≫ g) Z =
      supportOpenPairPreimageMap k f (supportPreimage k g Z) ≫
        supportOpenPairPreimageMap k g Z := by
  apply Arrow.hom_ext
  · exact supportOpenPreimageMap_comp k f g Z
  · rfl

/-- Restriction of a nested pair along the identity gives its identity arrow. -/
theorem supportPairPreimageMap_id {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    supportPairPreimageMap k (𝟙 X) ZW = 𝟙 _ := by
  apply Arrow.hom_ext
  · exact supportOpenPreimageMap_id k ZW.1.2.1
  · exact supportOpenPreimageMap_id k ZW.1.1.1

/-- Restriction of nested pairs respects composition of open immersions. -/
theorem supportPairPreimageMap_comp (f : T ⟶ Y) (g : Y ⟶ X)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] {a b : ℕ}
    (ZW : ConiveauSupportPairs k X a b) :
    supportPairPreimageMap k (f ≫ g) ZW =
      supportPairPreimageMap k f ((coniveauSupportPairsPreimage k g a b).obj ZW) ≫
        supportPairPreimageMap k g ZW := by
  apply Arrow.hom_ext
  · exact supportOpenPreimageMap_comp k f g ZW.1.2.1
  · exact supportOpenPreimageMap_comp k f g ZW.1.1.1

end AlgebraicGeometry.MotivicHomotopy
