/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-!
# Endpoint transport of original transformation tracks

Changing an equal Model endpoint through the actual functor equality leaves every continuous
level unchanged. This applies to the strict section-composition source transport.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- A literal equality of source Model arrows changes no full transformation track. -/
theorem prespectrumTransformationHomotopy_source_transport_level
    {V W : WideSubcategory preservesZero.{u}} {F F' G : V ⟶ W} (h : F = F')
    (η : F'.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq
      ((eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) h) ≫ η).app A)) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) h) ≫ η) hη').level n =
      (prespectrumTransformationHomotopy η hη).level n := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]

/-- A literal equality of target Model arrows changes no full transformation track. -/
theorem prespectrumTransformationHomotopy_target_transport_level
    {V W : WideSubcategory preservesZero.{u}} {F G' G : V ⟶ W} (h : G' = G)
    (η : F.hom.toFunctor ⟶ G'.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq
      ((η ≫ eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) h)).app A)) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (η ≫ eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) h)) hη').level n =
      (prespectrumTransformationHomotopy η hη).level n := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]

/-- Literal equalities at both Model endpoints preserve the whole transformation track. -/
theorem prespectrumTransformationHomotopy_transport_level
    {V W : WideSubcategory preservesZero.{u}} {F F' G' G : V ⟶ W} (hF : F = F') (hG : G' = G)
    (η : F'.hom.toFunctor ⟶ G'.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq
      ((eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) hF) ≫ η ≫
        eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) hG)).app A)) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) hF) ≫ η ≫
        eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) hG)) hη').level n =
      (prespectrumTransformationHomotopy η hη).level n := by
  subst hF
  subst hG
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Equal Model endpoints and equal original transformations preserve every continuous level. -/
theorem prespectrumTransformationHomotopy_level_eq_of_heq
    {V W : WideSubcategory preservesZero.{u}} {F F' G G' : V ⟶ W}
    (hF : F = F') (hG : G = G')
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (η' : F'.hom.toFunctor ⟶ G'.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A)) (he : HEq η η') (n : ℕ) :
    (prespectrumTransformationHomotopy η hη).level n =
      (prespectrumTransformationHomotopy η' hη').level n := by
  subst hF
  subst hG
  cases he
  rfl

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/PrespectrumTransformationTransport.lean:23-73"
  "adaptation" "Whole native transformation tracks with unchanged independent coordinates"]
  prespectrumTransformationHomotopy_source_transport_level
  prespectrumTransformationHomotopy_target_transport_level
  prespectrumTransformationHomotopy_transport_level
  prespectrumTransformationHomotopy_level_eq_of_heq

end CategoryTheory.Waldhausen.IteratedS
