/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNull
public import Colib.KTheory.Waldhausen.Iterated.TransformationInterchange
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityAction
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-!
# Identity actions on the original reversed zero null

The original whole null commutes with every pair of identity actions intertwined by its
unchanged composite Model functor. The null time and action time are independent, including
the original internal loop coordinate at level zero. The actual intertwining equation is
retained as the generic input; no scalar or Laurent comparison is assumed for a concrete model.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology

/-- A whole prespectrum homotopy intertwines the two actions at independent original times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/DiagramZeroNullUnit.lean:28"
  "adaptation" "Original whole reversed-null identity and independent coefficient-action times."]
def IdentityActionInterchange {V T : WideSubcategory preservesZero.{u}}
    {h k : prespectrum V ⟶ prespectrum T} (N : LoopPrespectrum.Homotopy h k)
    (α : 𝟭 V.obj.Obj ≅ 𝟭 V.obj.Obj) (β : 𝟭 T.obj.Obj ≅ 𝟭 T.obj.Obj) : Prop :=
  ∀ (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n),
    N.level n (s, (prespectrumIsoHomotopy (𝟙 V) α).level n (t, x)) =
      (prespectrumIsoHomotopy (𝟙 T) β).level n (t, N.level n (s, x))

/-- The same whole null intertwines compatible identity actions at both independent times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/DiagramZeroNullUnit.lean:36"
  "adaptation" "Original whole reversed-null identity and independent coefficient-action times."]
def ZeroNullUnitCompatible {V W T : WideSubcategory preservesZero.{u}} (f : V ⟶ W) (g : W ⟶ T)
    (N : LoopPrespectrum.Homotopy (prespectrumMap f ≫ prespectrumMap g)
      (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum T))) : Prop :=
  ∀ (α : 𝟭 V.obj.Obj ≅ 𝟭 V.obj.Obj) (β : 𝟭 T.obj.Obj ≅ 𝟭 T.obj.Obj),
    CategoryTheory.Functor.IdentityAutomorphism.Preserves (f ≫ g).hom.toFunctor α β →
      IdentityActionInterchange N α β

/-- The canonical reversed zero-to-image track has the full identity-action interchange. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/DiagramZeroNullUnit.lean:44"
  "adaptation" "Original whole reversed-null identity and independent coefficient-action times."]
theorem prespectrumCompositeZeroNullHomotopy_unitCompatible
    {V W T : WideSubcategory preservesZero.{u}}
    (f : V ⟶ W) (g : W ⟶ T)
    (η : (zeroHom V T).hom.toFunctor ⟶ (f ≫ g).hom.toFunctor)
    (hη : ∀ S, T.obj.waldhausen.weq (η.app S)) :
    ZeroNullUnitCompatible f g (prespectrumCompositeZeroNullHomotopy f g η hη) := by
  intro α β hunit n s t x
  exact prespectrumTransformationHomotopy_symm_identityAction_interchange
    (F := zeroHom V T) (G := f ≫ g) η α.hom β.hom hη
    (fun S => V.obj.waldhausen.weq_iso _ (show IsIso (α.app S).hom from inferInstance))
    (fun S => T.obj.waldhausen.weq_iso _ (show IsIso (β.app S).hom from inferInstance))
    (fun _ => T.obj.waldhausen.isZero.eq_of_src _ _) hunit n s t x

end CategoryTheory.Waldhausen.IteratedS
