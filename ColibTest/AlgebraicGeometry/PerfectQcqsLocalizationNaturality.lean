/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectQcqsLocalizationNaturality

open CategoryTheory CategoryTheory.Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u d d'

local instance (A : QuasiCompactOpenPairs.{u}) : CompactSpace A.obj.right := A.property

variable {A B : QuasiCompactOpenPairs.{u}}
  [QuasiSeparatedSpace ((𝟭 Scheme).obj A.obj.right)]
  [QuasiSeparatedSpace ((𝟭 Scheme).obj B.obj.right)]
  [CompactSpace ((𝟭 Scheme).obj A.obj.left)]
  [CompactSpace ((𝟭 Scheme).obj B.obj.left)]
  [HasDerivedCategory.{d} ((𝟭 Scheme).obj A.obj.left).Modules]
  [HasDerivedCategory.{d'} ((𝟭 Scheme).obj B.obj.left).Modules]

-- Mixed derived-category universes, arbitrary pair morphisms, and the supported K₀ boundary.
example (f : A ⟶ B) :
    (perfectSupportedKPullback f 0).comp (perfectQcqsConnectingHom B.obj.hom 0) =
      (perfectQcqsConnectingHom A.obj.hom 0).comp
        (perfectKPullback (Y := ((𝟭 Scheme).obj B.obj.left)) f.hom.left 1) :=
  (perfectQcqsLongExactSequence_pullback f 0).1

-- The first inverse positive localization map uses the actual open restriction equivalence.
example (f : A ⟶ B) :
    (perfectOpenKPullback f 1).comp (perfectQcqsOpenKEquiv B.obj.hom 0).symm.toMonoidHom =
      (perfectQcqsOpenKEquiv A.obj.hom 0).symm.toMonoidHom.comp
        (perfectKPullback (Y := ((𝟭 Scheme).obj B.obj.left)) f.hom.left 1) :=
  perfectQcqsOpenKEquiv_symm_pullback f 0

end AlgebraicGeometry.Scheme.Modules
