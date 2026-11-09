/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.OpenIncidenceGeometry
public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledStalkModules

/-!
# Actual pulled-support open squares

Implementation source: motivic@a6805c4,
Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean,
`openLeftPulledMap` and `openRightPulledMap`. Native comap comparison:
Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow.CorrespondenceOpenNeighborhoods

variable {S X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (z' : pullback (C := Scheme) (uX ≫ f) (uY ≫ g)) (w' : pullback (C := Scheme) (uY ≫ g) (uZ ≫ h))
  (vI : (integralComponentAt z').subscheme ⟶ (integralComponentAt z).subscheme)
  (vJ : (integralComponentAt w').subscheme ⟶ (integralComponentAt w).subscheme)
  (hi : vI ≫ (integralComponentAt z).subschemeι =
    (integralComponentAt z').subschemeι ≫ productMap f g uX uY)
  (hj : vJ ≫ (integralComponentAt w).subschemeι =
    (integralComponentAt w').subschemeι ≫ productMap g h uY uZ)

/-- The actual left pulled support maps through its full Cartesian ideal comparison. -/
def leftPulledMap :
    (correspondenceLeftPulledIdeal (uX ≫ f) (uY ≫ g) (uZ ≫ h) z').subscheme ⟶
      (correspondenceLeftPulledIdeal f g h z).subscheme :=
  ((integralComponentAt z').comapIso _).hom ≫
    pullback.map _ _ _ _ (tripleMap f g h uX uY uZ) vI
      (productMap f g uX uY) (tripleMap_fst f g h uX uY uZ).symm hi.symm ≫
    ((integralComponentAt z).comapIso _).inv

/-- The actual right pulled support keeps its original, possibly nonreduced structure. -/
def rightPulledMap :
    (correspondenceRightPulledIdeal (uX ≫ f) (uY ≫ g) (uZ ≫ h) w').subscheme ⟶
      (correspondenceRightPulledIdeal f g h w).subscheme :=
  ((integralComponentAt w').comapIso _).hom ≫
    pullback.map _ _ _ _ (tripleMap f g h uX uY uZ) vJ
      (productMap g h uY uZ) (tripleMap_snd f g h uX uY uZ).symm hj.symm ≫
    ((integralComponentAt w).comapIso _).inv

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ]
    [IsOpenImmersion vI] :
    IsOpenImmersion (leftPulledMap f g h uX uY uZ z z' vI hi) := by
  unfold leftPulledMap
  infer_instance

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ]
    [IsOpenImmersion vJ] :
    IsOpenImmersion (rightPulledMap f g h uX uY uZ w w' vJ hj) := by
  unfold rightPulledMap
  infer_instance

/-- The left actual open square commutes on the literal ideal inclusion. -/
@[reassoc (attr := simp)]
theorem leftPulledMap_inclusion :
    leftPulledMap f g h uX uY uZ z z' vI hi ≫
      correspondenceLeftPulledInclusion f g h z =
    correspondenceLeftPulledInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' ≫
      tripleMap f g h uX uY uZ := by
  simp [leftPulledMap, correspondenceLeftPulledInclusion, correspondenceLeftPulledIdeal]

/-- The right actual open square commutes on the literal ideal inclusion. -/
@[reassoc (attr := simp)]
theorem rightPulledMap_inclusion :
    rightPulledMap f g h uX uY uZ w w' vJ hj ≫
      correspondenceRightPulledInclusion f g h w =
    correspondenceRightPulledInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) w' ≫
      tripleMap f g h uX uY uZ := by
  simp [rightPulledMap, correspondenceRightPulledInclusion, correspondenceRightPulledIdeal]

/-- The constructed local incidence point maps to the original left pulled point. -/
@[reassoc (attr := simp)]
theorem incidenceMap_toLeftPulled :
    incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj ≫
      correspondenceIncidenceToLeftPulled f g h z w =
    correspondenceIncidenceToLeftPulled (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ≫
      leftPulledMap f g h uX uY uZ z z' vI hi := by
  rw [← cancel_mono (correspondenceLeftPulledInclusion f g h z)]
  simp only [Category.assoc, correspondenceIncidenceToLeftPulled_inclusion,
    leftPulledMap_inclusion, correspondenceIncidenceToLeftPulled_inclusion_assoc,
    incidenceMap_inclusion]

/-- The same incidence lift gives the original right pulled-support point. -/
@[reassoc (attr := simp)]
theorem incidenceMap_toRightPulled :
    incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj ≫
      correspondenceIncidenceToRightPulled f g h z w =
    correspondenceIncidenceToRightPulled (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ≫
      rightPulledMap f g h uX uY uZ w w' vJ hj := by
  rw [← cancel_mono (correspondenceRightPulledInclusion f g h w)]
  simp only [Category.assoc, correspondenceIncidenceToRightPulled_inclusion,
    rightPulledMap_inclusion, correspondenceIncidenceToRightPulled_inclusion_assoc,
    incidenceMap_inclusion]

end Stacks.Chow.CorrespondenceOpenNeighborhoods
