/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityMap

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalRawBass
open scoped Topology unitInterval

universe u

noncomputable example (X : Scheme.{u}) :
    Homotopy (map (𝟙 X)) (𝟙 (step X)) :=
  InputIdentity.mapHomotopy X

example (X : Scheme.{u}) (n : ℕ) (r s : unitInterval) (γ : (step X).space n) :
    Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n (r, γ)) s =
      (InputIdentity.coneHomotopy X).level n (r, Path.toContinuousMap γ s) :=
  InputIdentity.mapHomotopy_apply X n r s γ

example (X : Scheme.{u}) :
    Topology.SimplexCubeExtension.EdgeCompatible (fun a ↦ InputIdentityCarrierCube.faces X a) :=
  InputIdentityCarrierCube.face_compatible X
