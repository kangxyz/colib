/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleIncidence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

noncomputable section

universe u
variable {S X Y Z W : Scheme.{u}}
variable (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Reassociation is the actual native pullback isomorphism, not an assumed comparison.
example : correspondenceTripleIncidenceAssoc f g h i z w v =
    pullbackAssoc ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
      ((integralComponentAt w).subschemeι ≫ pullback.snd g h)
      ((integralComponentAt v).subschemeι ≫ pullback.fst h i) := rfl

example : (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫ pullback.fst _ _ =
    correspondenceTripleIncidenceFst f g h i z w v ≫ pullback.fst _ _ :=
  correspondenceTripleIncidenceAssoc_fst f g h i z w v

example : (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
      pullback.snd _ _ ≫ pullback.fst _ _ =
    correspondenceTripleIncidenceFst f g h i z w v ≫ pullback.snd _ _ :=
  correspondenceTripleIncidenceAssoc_snd_fst f g h i z w v

example : (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
      pullback.snd _ _ ≫ pullback.snd _ _ = correspondenceTripleIncidenceSnd f g h i z w v :=
  correspondenceTripleIncidenceAssoc_snd_snd f g h i z w v

example : (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
    correspondenceRightTripleIncidenceMap f g h i z w v =
      correspondenceTripleIncidenceMap f g h i z w v :=
  correspondenceTripleIncidenceAssoc_map f g h i z w v

-- The first triple projection needs only finiteness of the last support.
example (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleIncidenceFst f g h i z w v) :=
  isFinite_correspondenceTripleIncidenceFst f g h i z w v hv

-- The output finiteness is over any base, without normality, smoothness or a field.
example [IsSeparated i] (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleIncidenceMap f g h i z w v) :=
  isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv

example [IsSeparated i] (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (c : AlgebraicCycle (correspondenceTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    letI : IsFinite (correspondenceRightTripleIncidenceMap f g h i z w v) :=
      inferInstanceAs (IsFinite ((correspondenceTripleIncidenceAssoc f g h i z w v).inv ≫
        correspondenceTripleIncidenceMap f g h i z w v))
    finiteCyclePushforward (correspondenceRightTripleIncidenceMap f g h i z w v)
        (finiteCyclePushforward (correspondenceTripleIncidenceAssoc f g h i z w v).hom (-c)) =
      finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v) (-c) :=
  finiteCyclePushforward_correspondenceTripleIncidenceAssoc f g h i z w v hz hw hv (-c)
