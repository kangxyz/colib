/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.LeftPulledStalkTor

/-!
# Actual left identity pulled-stalk regression examples
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

-- 1. The actual incidence is the native inverse-image closed subscheme.
example :
    IsPullback (correspondenceIncidenceToLeftPulled f g h z w) (pullback.snd _ _)
      (correspondenceLeftPulledInclusion f g h z ≫
        pullback.snd (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt w).subschemeι :=
  isPullback_correspondenceIncidenceToLeftPulled f g h z w

-- 2. The native comap isomorphism retains its actual inclusion.
example :
    (correspondenceIncidenceLeftRestrictionIso f g h z w).hom ≫
      ((integralComponentAt w).comap
        (correspondenceLeftPulledInclusion f g h z ≫
          pullback.snd (pullback.snd f g) (pullback.fst g h))).subschemeι =
        correspondenceIncidenceToLeftPulled f g h z w :=
  correspondenceIncidenceLeftRestrictionIso_hom_subschemeι f g h z w

end Geometry

-- 3. The identity component, unlike a general left graph, has an open target projection.
example
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsLocallyNoetherian X] [IsNormal X] (s : genericPoints X) :
    IsOpenImmersion
      ((integralComponentAt
        (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val)).subschemeι ≫
        pullback.snd f f) :=
  isOpenImmersion_integralComponentAt_diagonal_snd f s

section Identity

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
  [IsLocallyNoetherian X] [IsNormal X]
  (z : pullback (C := Scheme) f g) (s : genericPoints X)

local notation "δ" => correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val

-- 4. Native balancing returns the original left/right ordering in all positive degrees.
example [Flat f]
    (t : correspondenceIncidence f f g δ z) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
      (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) :=
  isZero_correspondencePulledStalkTor_succ_diagonal_left f g z s t n

-- 5. Degree zero needs neither support-flatness nor outer-source flatness.
example
    (t : correspondenceIncidence f f g δ z) :
    (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))) 0).obj
      (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
      (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceInclusion f f g δ z).stalkMap t).hom).obj
      (ModuleCat.of ((correspondenceIncidence f f g δ z).presheaf.stalk t)
        ((correspondenceIncidence f f g δ z).presheaf.stalk t)) :=
  correspondencePulledStalkTorZeroIso_diagonal_left f g z s t

-- 6. Full ENat local-ring length is retained without a finite-length hypothesis.
example
    (t : correspondenceIncidence f f g δ z) :
    Module.length ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
        (correspondenceIncidenceInclusion f f g δ z t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
        (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) =
    Module.length ((correspondenceIncidence f f g δ z).presheaf.stalk t)
      ((correspondenceIncidence f f g δ z).presheaf.stalk t) :=
  length_correspondencePulledStalkTor_zero_diagonal_left f g z s t

-- 7. Generic length one uses reducedness proved for the actual incidence.
example
    (t : correspondenceIncidence f f g δ z) (ht : IsMax t) :
    Module.length ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
        (correspondenceIncidenceInclusion f f g δ z t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
        (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) = 1 :=
  length_correspondencePulledStalkTor_zero_diagonal_left_eq_one f g z s t ht

end Identity

section Field

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated f]
  [IsLocallyNoetherian X] [IsNormal X]
  (z : pullback (C := Scheme) f g) (s : genericPoints X)

-- 8. Every field is allowed, and outer-source flatness is inferred.
example
    (t : correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g
        (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f f g
        (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z t)).obj
      (correspondenceIncidenceRightPulledStalkModule f f g
        (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z t)) :=
  isZero_correspondencePulledStalkTor_succ_identity_left k f g z s t n

end Field

-- 9. Supports in different components retain the existing actual emptiness behavior.
example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
    [IsLocallyNoetherian X] [IsNormal X] (z : pullback (C := Scheme) f g)
    (s t : genericPoints X) (hst : s ≠ t)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {s.val}) :
    IsEmpty (correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) t.val) z) :=
  isEmpty_correspondenceIncidence_diagonal_left_of_ne f g z s t hst hz

-- 10. Empty ambient sources contribute no generic identity components.
example (X : Scheme.{u}) [IsEmpty X] : IsEmpty (genericPoints X) := inferInstance
