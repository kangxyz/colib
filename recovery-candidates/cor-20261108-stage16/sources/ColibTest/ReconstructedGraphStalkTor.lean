/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.StalkTor

/-!
# Newly reconstructed graph-stalk semantic tests

These ten examples were written from the recovered production API on 2026-11-08.
They are NOT the missing historical `ColibTest/ActualGraphStalkTor.lean` bytes.
No example in this file has yet been elaborated or compiled in the recovery view.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

section Lower

variable {A C T X : Scheme.{u}} (i : C ⟶ T) (p : T ⟶ X)
  [IsOpenImmersion (i ≫ p)]

-- 1. Degree zero retains the actual ambient action without any flatness assumption.
example (c : C) (M : ModuleCat (C.presheaf.stalk c)) :
    (((Tor (ModuleCat (T.presheaf.stalk (i c))) 0).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (Scheme.Hom.openSectionStalkExtension i p c)).obj M)) ≅
    (ModuleCat.restrictScalars (i.stalkMap c).hom).obj M :=
  Scheme.Hom.openSectionStalkTorZeroIso i p c M

-- 2. Length one needs an actual reduced closed support at an actual generic point.
example (j : A ⟶ C) [IsClosedImmersion j] [IsReduced A] (a : A) (ha : IsMax a) :
    Module.length (T.presheaf.stalk (i (j a)))
      (((Tor (ModuleCat (T.presheaf.stalk (i (j a)))) 0).obj
        ((ModuleCat.restrictScalars (i.stalkMap (j a)).hom).obj
          (ModuleCat.of (C.presheaf.stalk (j a)) (C.presheaf.stalk (j a))))).obj
        ((ModuleCat.extendScalars (Scheme.Hom.openSectionStalkExtension i p (j a))).obj
          ((ModuleCat.restrictScalars (j.stalkMap a).hom).obj
            (ModuleCat.of (A.presheaf.stalk a) (A.presheaf.stalk a))))) = 1 :=
  Scheme.Hom.length_openSectionStalkTor_zero_closedSupport_eq_one i p j a ha

end Lower

section Graph

open Stacks.Chow

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
  [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X)

local notation "G" => (integralComponentAt (correspondenceGraphMap f g φ hφ t.val))

-- 3. The scalar section is retracted by the actual graph inclusion stalk map.
example (c : (G).subscheme) :
    ((G).subschemeι.stalkMap c).hom.comp (graphComponentStalkExtension f g φ hφ t c) =
      RingHom.id ((G).subscheme.presheaf.stalk c) :=
  stalkMap_comp_graphComponentStalkExtension f g φ hφ t c

-- 4. The extension's flatness comes from the actual target morphism.
example [Flat g] (c : (G).subscheme) :
    (graphComponentStalkExtension f g φ hφ t c).Flat :=
  flat_graphComponentStalkExtension f g φ hφ t c

-- 5. Actual graph degree zero needs no flatness of g or of the arbitrary module.
example (c : (G).subscheme) (M : ModuleCat ((G).subscheme.presheaf.stalk c)) :
    (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) 0).obj
      ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
        (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)) ≅
    (ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj M :=
  graphComponentStalkTorZeroIso f g φ hφ t c M

-- 6. Positive native Tor vanishes for every degree and arbitrary extended module.
example [Flat g] (c : (G).subscheme)
    (M : ModuleCat ((G).subscheme.presheaf.stalk c)) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) (n + 1)).obj
      ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
        (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)) :=
  isZero_graphComponentStalkTor_succ f g φ hφ t c M n

-- 7. The support-first ordering uses the native balanced Tor comparison.
example [Flat g] (c : (G).subscheme)
    (M : ModuleCat ((G).subscheme.presheaf.stalk c)) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) (n + 1)).obj
      ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)).obj
      ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
        (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))) :=
  isZero_graphComponentStalkTor_succ_flip f g φ hφ t c M n

-- 8. Degree-zero length is full ENat length, with no finite-length assumption.
example (c : (G).subscheme) (M : ModuleCat ((G).subscheme.presheaf.stalk c)) :
    Module.length ((pullback f g).presheaf.stalk ((G).subschemeι c))
      (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) 0).obj
        ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
          (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))).obj
        ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)) =
      Module.length ((G).subscheme.presheaf.stalk c) M :=
  length_graphComponentStalkTor_zero f g φ hφ t c M

end Graph

section Field

open Stacks.Chow

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
  [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X)

-- 9. Every field is allowed and flatness of the target map is inferred.
example (c : (integralComponentAt (correspondenceGraphMap f g φ hφ t.val)).subscheme) :
    (graphComponentStalkExtension f g φ hφ t c).Flat := by
  have : Flat g := inferInstance
  exact flat_graphComponentStalkExtension f g φ hφ t c

end Field

-- 10. Empty schemes contribute no generic components.
example (X : Scheme.{u}) [IsEmpty X] : IsEmpty (genericPoints X) := inferInstance
