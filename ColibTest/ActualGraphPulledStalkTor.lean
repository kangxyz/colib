/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.PulledStalkTor

/-!
# Actual graph pulled-support stalk Tor regression examples
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

section LocalIdeal

open AlgebraicGeometry.Scheme.Hom

variable {C T X : Scheme.{u}} (i : C ⟶ T) (p : T ⟶ X)
  [IsOpenImmersion (i ≫ p)] (I : X.IdealSheafData) (c : C)

-- 1. Actual inverse-image support stalk, with explicit point/scalar data and no flatness.
example
    (d : (I.comap p).subscheme) (j : (I.comap (i ≫ p)).subscheme)
    (hd : i c = (I.comap p).subschemeι d)
    (hj : c = (I.comap (i ≫ p)).subschemeι j) :
    (ModuleCat.restrictScalars
      ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
        (I.comap p).subschemeι.stalkMap d).hom).obj
      (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
        ((I.comap p).subscheme.presheaf.stalk d)) ≅
    (ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj
      ((ModuleCat.restrictScalars
        ((C.presheaf.stalkCongr (.of_eq hj)).hom ≫
          (I.comap (i ≫ p)).subschemeι.stalkMap j).hom).obj
        (ModuleCat.of ((I.comap (i ≫ p)).subscheme.presheaf.stalk j)
          ((I.comap (i ≫ p)).subscheme.presheaf.stalk j))) :=
  comapStalkIsoExtendOpenSection i p I c d j hd hj

end LocalIdeal

section Geometry

open Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

-- 2. The incidence is an actual cartesian inverse image, not a support-set replacement.
example :
    IsPullback (correspondenceIncidenceToRightPulled f g h z w) (pullback.fst _ _)
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt z).subschemeι :=
  isPullback_correspondenceIncidenceToRightPulled f g h z w

-- 3. The actual comap isomorphism preserves the literal closed inclusion.
example :
    (correspondenceIncidenceRightRestrictionIso f g h z w).hom ≫
      ((integralComponentAt z).comap
        (correspondenceRightPulledInclusion f g h w ≫
          pullback.fst (pullback.snd f g) (pullback.fst g h))).subschemeι =
        correspondenceIncidenceToRightPulled f g h z w :=
  correspondenceIncidenceRightRestrictionIso_hom_subschemeι f g h z w

end Geometry

section Graph

open Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)
  [IsSeparated h] [IsLocallyNoetherian Y] [IsNormal Y] (s : genericPoints Y)

-- 4. Both Tor inputs are the actual pulled stalks, in the original left/right order.
example [Flat h]
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)) :=
  isZero_correspondencePulledStalkTor_succ_graph_right f g h z ψ hψ s t n

-- 5. Degree zero is the actual incidence stalk, with no flatness assumption.
example
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) :
    (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))) 0).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)) ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val)).stalkMap t).hom).obj
      (ModuleCat.of
        ((correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t)
        ((correspondenceIncidence f g h z
          (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t)) :=
  correspondencePulledStalkTorZeroIsoGraphRight f g h z ψ hψ s t

-- 6. Full local-ring length, including infinity, rather than an assumed coefficient one.
example
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)) =
    Module.length
      ((correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t)
      ((correspondenceIncidence f g h z
        (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t) :=
  length_correspondencePulledStalkTor_zero_graph_right f g h z ψ hψ s t

-- 7. Generic length one follows from proved reducedness of the actual open incidence.
example
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val))
    (ht : IsMax t) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)) = 1 :=
  length_correspondencePulledStalkTor_zero_graph_right_eq_one f g h z ψ hψ s t ht

end Graph

section IdentityOverField

open Stacks.Chow

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsSeparated g] [IsLocallyNoetherian Y] [IsNormal Y]
  (z : pullback (C := Scheme) f g) (s : genericPoints Y)

-- 8. Arbitrary field, with projection flatness inferred and no integral ambient hypothesis.
example
    (t : correspondenceIncidence f g g z (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val))
    (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g g).presheaf.stalk
      (correspondenceIncidenceInclusion f g g z
        (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val) t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g g z
        (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val) t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g g z
        (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val) t)) :=
  isZero_correspondencePulledStalkTor_succ_identity_right k f g z s t n

end IdentityOverField
