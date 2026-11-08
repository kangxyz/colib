/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberIteratedFiber
public import Colib.KTheory.Waldhausen.Fibration.CofiberBoundaryTrack
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarKOne

/-!
# Pasting the original scalar cofiber and weak-composition triangles

The prescribed quotient prefix followed by the original cofiber/projection path is compared
with the actual identity-cofiber suffix followed by the unchanged scalar square. All paths
are the original geometric ones. This is the route equation used to compute the loop produced
by the existing iterated-fiber map; it does not assume a localization boundary identity.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberPasting.lean:37-131`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology HomotopyGroup
open CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

/-- The original forward zero-to-cofiber prefix, with its actual coarse object-loop endpoints. -/
def perfectScalarCofiberPrefixPath :
    Path (((perfectOpenNested j).coarse.kZeroObjectLoop K).trans
      (Path.refl (perfectOpenNested j).coarse.kBasepoint))
      (((perfectOpenNested j).coarse.kZeroObjectLoop K).trans
        ((perfectOpenNested j).coarse.kZeroObjectLoop
          ((ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
            (perfectScalarExtension X r K)))) :=
  (perfectOpenNested j).coarse.cofiberPrismPrefixLoopPath (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarInclusion_openWeak r j q hq K)
    (perfectScalarCofiber_isPushout r j K)

/-- The original coarse cofiber triangle is retained as a specified loop-space path. -/
def perfectScalarCofiberCoarsePath :
    Path (((perfectOpenNested j).coarse.kZeroObjectLoop K).trans
      ((perfectOpenNested j).coarse.kZeroObjectLoop
        ((ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K))))
      ((perfectOpenNested j).coarse.kZeroObjectLoop
        ((ExtensionCategory.middle (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K))) :=
  (perfectOpenNested j).coarse.cofiberObjectLoopPath (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarCofiber_isPushout r j K)

/-- The original fine weak projection is viewed through its unchanged coarse square. -/
def perfectScalarProjectionCoarsePath :
    Path ((perfectOpenNested j).coarse.kZeroObjectLoop
      ((ExtensionCategory.middle (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
        (perfectScalarExtension X r K)))
      ((perfectOpenNested j).coarse.kZeroObjectLoop K) :=
  (perfectOpenNested j).coarse.weakObjectSquareLoopPath (perfectScalarProjection X r K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))

/-- The actual two triangles give the original forward-prefix pasting equation. -/
def perfectScalarCofiberPastingTrack :
    ((perfectScalarCofiberPrefixPath j r q hq K).trans
      ((perfectScalarCofiberCoarsePath j r K).trans
        (perfectScalarProjectionCoarsePath j r K))).Homotopy
      (((perfectOpenNested j).coarse.identityCofiberSuffixPath K).trans
        (perfectScalarWeakLoop j K r q hq)) := by
  let P := perfectScalarCofiberPrefixPath j r q hq K
  let H := perfectScalarCofiberCoarsePath j r K
  let J := perfectScalarProjectionCoarsePath j r K
  let I := (perfectOpenNested j).coarse.weakObjectSquareLoopPath
    (perfectScalarInclusion X r K) (perfectScalarInclusion_openWeak r j q hq K)
  let E := (perfectOpenNested j).coarse.identityCofiberSuffixPath K
  have h₁ := (perfectOpenNested j).coarse.cofiberBoundaryTrack (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarInclusion_openWeak r j q hq K)
    (perfectScalarCofiber_isPushout r j K)
  have h₂ := (perfectOpenNested j).coarse.weakObjectSquareCompositionTrack
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    (perfectScalarInclusion_openWeak r j q hq K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))
  have h := (Path.Homotopy.transAssoc P H J).symm.trans
    ((h₁.hcomp (Path.Homotopy.refl J)).trans
      ((Path.Homotopy.transAssoc E I J).trans ((Path.Homotopy.refl E).hcomp h₂)))
  exact h.cast rfl (by simp only [perfectScalarInclusion_projection]; rfl)

/-- The mapped fine return path is precisely the original coarse cofiber/projection path. -/
theorem perfectScalarCofiberSourceLoopPath_changeWeak :
    (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _)).comp
        (perfectScalarCofiberSourceLoopPath X r K).toContinuousMap =
      ((perfectScalarCofiberCoarsePath j r K).trans
        (perfectScalarProjectionCoarsePath j r K)).toContinuousMap := by
  apply ContinuousMap.ext
  intro s
  apply Path.ext
  funext t
  change changeWeakMap (perfectOpenNested j)
    (perfectScalarCofiberSourceTrack X r K (s, t)) =
      ((perfectScalarCofiberCoarsePath j r K).trans
        (perfectScalarProjectionCoarsePath j r K) s) t
  unfold perfectScalarCofiberSourceTrack
  rw [Path.Homotopy.trans_apply, Path.trans_apply]
  split_ifs with h
  · exact perfectScalarCofiberObjectTrack_changeWeak j r K _ t
  · exact perfectScalarProjectionObjectTrack_changeWeak j r K _ t

/-- The original prefixed canonical-fiber path is exactly the reversed forward prism prefix. -/
theorem perfectScalarCofiberPrefixedPath_eq :
    (canonicalFiberObjectPrefixed (perfectOpenNested j) K
      (perfectOpenScalarCofiberAcyclic r j q hq K)).val.2 =
        (perfectScalarCofiberPrefixPath j r q hq K).symm.toContinuousMap := by
  apply ContinuousMap.ext
  intro s
  apply Path.ext
  funext t
  rw [canonicalFiberObjectPrefixed_path]
  exact (perfectOpenScalarCofiberCompositionCube_zero j r q hq K t s).symm

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberPasting.lean:37-131" "adaptation"
  "The actual cofiber and composition triangles give the original forward-prefix route equation; no
    boundary identity is assumed"]
  perfectScalarCofiberPastingTrack perfectScalarCofiberPrefixedPath_eq

end AlgebraicGeometry.Scheme.Modules
