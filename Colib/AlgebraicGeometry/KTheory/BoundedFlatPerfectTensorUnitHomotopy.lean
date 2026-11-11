/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.KTheory.Waldhausen.Iterated.ExactPastingHomotopy

/-!
# Original iterated-S tracks of the restricted tensor-unit action

Tensoring by the actual structure module is exact through its genuine unitor. The actual
coefficient-unit automorphism therefore supplies an original iterated-S track. Its categorical
unitor square gives a whole relative prism comparison with the existing forward scalar track,
including the original zero-level loops and independent spectrum structure parameter.

This is the restricted tensor-unit comparison. No full K-theory product or identification of
arbitrary Bass towers with the classical TT construction is asserted here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Genuine tensor by the structure module preserves zero, cofibrations, weak equivalences and
pushouts through the actual left unitor. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:33"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
theorem boundedAboveFlatPerfectTensorUnit_exact (X : Scheme.{u}) :
    CategoryTheory.Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq (boundedAboveFlatPerfectWaldhausen
        X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq (boundedAboveFlatPerfectTensorUnit
        X) :=
  (CategoryTheory.Waldhausen.IsExact.id _ _).of_iso (boundedAboveFlatPerfectTensorUnitIso X).symm

/-- The actual tensor-unit pullback, with no flatness hypothesis on the scheme map, is exact. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:40"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
theorem boundedAboveFlatPerfectTensorUnitPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CategoryTheory.Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq (boundedAboveFlatPerfectWaldhausen
        X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
        (boundedAboveFlatPerfectTensorUnitPullback f) :=
  (boundedAboveFlatPerfectPullback_isExact f).of_iso
    (boundedAboveFlatPerfectTensorUnitPullbackIso f).symm

/-- The original tensor automorphism fixes the actual zero input before canonical rebasing. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:47"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
theorem boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero = 𝟙 _ :=
  ((boundedAboveFlatPerfectTensorUnitPullback_exact f).zero
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).eq_of_src _ _

/-- The normalized original spectrum map of genuine tensor-unit geometric pullback. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:55"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
def boundedAboveFlatPerfectTensorUnitPrespectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectTensorUnitPullback_exact f)

/-- The whole iterated-S track of the actual tensor coefficient automorphism. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:60"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
def boundedAboveFlatPerfectTensorUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedAboveFlatPerfectTensorUnitPrespectrumMap f)
      (boundedAboveFlatPerfectTensorUnitPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r)

/-- The original unitor supplies a full spectrum homotopy to unchanged geometric pullback. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:69"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
def boundedAboveFlatPerfectTensorUnitUnitorHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedAboveFlatPerfectTensorUnitPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectPullback_isExact f) (boundedAboveFlatPerfectTensorUnitPullbackIso f)

/-- The actual tensor-unit square realizes to the whole endpoint-relative iterated-S prism.
Both original times and the independent structure coordinate are retained. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitHomotopy.lean:77"
  "adaptation" "Original tensor-unitor action and endpoint-relative prism."]
def boundedAboveFlatPerfectTensorUnitUnitorPasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    ((boundedAboveFlatPerfectTensorUnitHomotopy f r).trans
      (boundedAboveFlatPerfectTensorUnitUnitorHomotopy f)).RelHomotopy
      ((boundedAboveFlatPerfectTensorUnitUnitorHomotopy f).trans
        (boundedAboveFlatPerfectUnitHomotopy f r)) :=
  exactOriginalPrespectrumPastingHomotopy _ _
    (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectPullback_isExact f) (boundedAboveFlatPerfectPullback_isExact f)
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom
    (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom
    (boundedAboveFlatPerfectPullbackUnitIso f r).hom
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_unitor f r)

end AlgebraicGeometry.Scheme.Modules
