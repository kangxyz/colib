/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.NaturalTrack
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-! # Realization of original identity units as whole natural tracks -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (F : C ⥤ WideSubcategory preservesZero.{w})
    (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)
    (hunit : ∀ {X Y} (g : X ⟶ Y),
      (∀ S, (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app S) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj S)))

/-- The original identity-unit realization, along the prescribed coefficient projection. -/
@[colib_tag "COL-0529", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalModelUnitTrack.lean:29"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
def ofModelUnits : Track L c (F ⋙ prespectrumFunctor) where
  homotopy X := prespectrumIsoHomotopy (F.map (c.app X))
    (onFunctor (F.map (c.app X)).hom.toFunctor (unit X))
  naturality {X Y} g n r x := by
    have h : F.map (c.app X) ≫ F.map (L.map g) = F.map g ≫ F.map (c.app Y) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (c.naturality g).symm
    exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
      (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h))
        (unit X) (unit Y) (NatTrans.ext (funext (hunit g)))) n r x

/-- A unit-preserving actual Model transformation retains the entire realization time. -/
@[colib_tag "COL-0529", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalModelUnitTrack.lean:41"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem ofModelUnits_equivariant (G : C ⥤ WideSubcategory preservesZero.{w})
    (unit' : ∀ X, 𝟭 (G.obj (L.obj X)).obj.Obj ≅ 𝟭 (G.obj (L.obj X)).obj.Obj)
    (hunit' : ∀ {X Y} (g : X ⟶ Y),
      (∀ S, (G.map (L.map g)).hom.toFunctor.map ((unit' X).hom.app S) =
        (unit' Y).hom.app ((G.map (L.map g)).hom.toFunctor.obj S)))
    (η : F ⟶ G)
    (hη : ∀ X, ∀ S, (η.app (L.obj X)).hom.toFunctor.map ((unit X).hom.app S) =
      (unit' X).hom.app ((η.app (L.obj X)).hom.toFunctor.obj S)) :
    Equivariant (ofModelUnits L c F unit hunit)
      (ofModelUnits L c G unit' hunit') (Functor.whiskerRight η prespectrumFunctor) := by
  intro X r
  exact (prespectrumIsoHomotopy_square_at _ _ _ _ _ _ (η.naturality (c.app X))
    (onFunctor_whisker_square _ _ _ _
      (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) (η.naturality (c.app X))))
      (unit X) (unit' X) (NatTrans.ext (funext (hη X)))) r).symm

end KTheory.Bass.NaturalTrack
