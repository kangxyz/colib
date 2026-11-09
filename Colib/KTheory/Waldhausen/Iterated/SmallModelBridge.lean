/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-!
# Direct small models and their actual AsSmall presentations

Up and down are inverse strict exact model arrows. The resulting spectrum isomorphism
compares the two presentations rather than presuming equality of their spectra.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- The actual chosen-zero preserving universe lift of a direct small model. -/
def smallModelUp (V : WideSubcategory preservesZero.{u}) :
    V ⟶ asSmallCategory V.obj.waldhausen :=
  ⟨⟨AsSmall.up, V.obj.waldhausen.asSmall_up_exact⟩, rfl⟩

/-- The actual chosen-zero preserving lowering functor. -/
def smallModelDown (V : WideSubcategory preservesZero.{u}) :
    asSmallCategory V.obj.waldhausen ⟶ V :=
  ⟨⟨AsSmall.down, V.obj.waldhausen.asSmall_down_exact⟩, rfl⟩

/-- Up and down cancel as actual model arrows, not just up to equivalence. -/
def smallModelAsSmallIso (V : WideSubcategory preservesZero.{u}) :
    V ≅ asSmallCategory V.obj.waldhausen where
  hom := smallModelUp V
  inv := smallModelDown V
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    rfl
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    rfl

/-- The actual direct-small spectrum is isomorphic to its original-universe presentation. -/
def smallModelPrespectrumIso (V : WideSubcategory preservesZero.{u}) :
    prespectrum V ≅ originalPrespectrum V.obj.waldhausen :=
  prespectrumFunctor.mapIso (smallModelAsSmallIso V)

/-- The up/down square retains the original underlying exact functor. -/
theorem smallModelUp_naturality {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    smallModelUp V ≫ asSmallCategoryMap V.obj.waldhausen W.obj.waldhausen
      F.hom.isExact F.property = F ≫ smallModelUp W := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

/-- The spectrum comparison commutes with the unchanged strict model map. -/
theorem smallModelPrespectrumIso_naturality
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    (smallModelPrespectrumIso V).hom ≫ originalPrespectrumMap V.obj.waldhausen
      W.obj.waldhausen F.hom.isExact F.property =
        prespectrumMap F ≫ (smallModelPrespectrumIso W).hom := by
  change prespectrumFunctor.map (smallModelUp V) ≫ prespectrumFunctor.map _ =
    prespectrumFunctor.map F ≫ prespectrumFunctor.map (smallModelUp W)
  rw [← prespectrumFunctor.map_comp, ← prespectrumFunctor.map_comp, smallModelUp_naturality]

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0357",
  colib_ref "Waldhausen1985" "Section 1.3, Proposition 1.3.1, pp. 330-331" "background"
    "Actual exact-functor maps and weak-natural-transformation invariance"]
  CategoryTheory.Waldhausen.IteratedS.smallModelAsSmallIso
  CategoryTheory.Waldhausen.IteratedS.smallModelPrespectrumIso_naturality
