/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Duality.Basic
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak

/-! # Original duality after inverse-image weak enlargement
Implementation provenance: `Quillen/Waldhausen/Duality/InverseImageWeak.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual maps, structural hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen

namespace IsCompatibleDual
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd) {G : C ⥤ D}
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hGd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq G.op)

include hW hV
/-- Inverse-image weak classes retain original zero-square duality on unchanged arrows. -/
theorem withInverseImageWeak : IsCompatibleDual (Structure.withInverseImageWeak hG)
    (Structure.withInverseImageWeak hGd) where
  weak f := hV.weak (G.map f)
  cofiber i z q s hZ := hW.cofiber i z q s hZ

end IsCompatibleDual
end CategoryTheory.Waldhausen
