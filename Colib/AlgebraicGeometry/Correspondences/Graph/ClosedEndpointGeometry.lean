/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.AffineLineFiberComponentCoefficient
public import Colib.AlgebraicGeometry.Correspondences.Graph.EndpointSingleFiber
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureRelativeClosure

/-!
# Actual closed support endpoints and their original component maps

The whole endpoint map is the actual pullback of the given closed support map,
followed by the already constructed endpoint ambient isomorphism. The component
comparison is the pullback of the native `integralComponentMap`, which is an
isomorphism for a closed immersion. Every comparison retains its map into the
original ambient scheme; no residue-field degree or nilpotent is discarded.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

open Scheme.AffineLineFiber Scheme.PolynomialSectionPencil

variable {k : Type u} [Field k] {X Y Z D : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  (φ : X ⟶ Y) (hφ : φ ≫ g = f)
  (q : Y ⟶ Spec (.of (Polynomial k))) (a : k)
  (H : IsPullback φ f q (point a))

include H in
/-- The original ambient endpoint map is a closed immersion. -/
theorem isClosedImmersion_correspondenceEndpointAmbientMap :
    IsClosedImmersion (correspondenceGraphFiberAmbientMap f g h φ hφ) := by
  rw [← correspondenceEndpointAmbientIso_hom_inclusion f g h φ hφ q a H]
  infer_instance

/-- The actual full parameter fiber of a closed support maps into the endpoint product. -/
def closedSupportEndpointMap (m : D ⟶ pullback g h) :
    fiber (m ≫ pullback.fst g h ≫ q) a ⟶ pullback f h :=
  fiberMap (pullback.fst g h ≫ q) a m ≫
    (correspondenceEndpointAmbientIso f g h φ hφ q a H).inv

instance closedSupportEndpointMap_isClosedImmersion (m : D ⟶ pullback g h)
    [IsClosedImmersion m] :
    IsClosedImmersion (closedSupportEndpointMap f g h φ hφ q a H m) := by
  unfold closedSupportEndpointMap
  infer_instance

/-- The endpoint map retains the whole original support inclusion. -/
@[reassoc (attr := simp)] theorem closedSupportEndpointMap_ambient
    (m : D ⟶ pullback g h) :
    closedSupportEndpointMap f g h φ hφ q a H m ≫
      correspondenceGraphFiberAmbientMap f g h φ hφ =
        inclusion (m ≫ pullback.fst g h ≫ q) a ≫ m := by
  rw [← correspondenceEndpointAmbientIso_hom_inclusion f g h φ hφ q a H,
    closedSupportEndpointMap, Category.assoc, Iso.inv_hom_id_assoc]
  exact fiberMap_inclusion (pullback.fst g h ≫ q) a m

/-- The whole scalar fiber is the actual whole source-section fiber. -/
def closedSupportEndpointIso (m : D ⟶ pullback g h) :
    fiber (m ≫ pullback.fst g h ≫ q) a ≅ pullback φ (m ≫ pullback.fst g h) :=
  wholeFiberIso φ f q (point a) H (m ≫ pullback.fst g h)

@[reassoc (attr := simp)] theorem closedSupportEndpointIso_total
    (m : D ⟶ pullback g h) :
    (closedSupportEndpointIso f g h φ q a H m).hom ≫
      pullback.snd φ (m ≫ pullback.fst g h) =
        inclusion (m ≫ pullback.fst g h ≫ q) a :=
  wholeFiberIso_hom_total φ f q (point a) H (m ≫ pullback.fst g h)

/-- The source coordinate is the original Cartesian source projection. -/
@[reassoc (attr := simp)] theorem closedSupportEndpointMap_fst
    (m : D ⟶ pullback g h) :
    closedSupportEndpointMap f g h φ hφ q a H m ≫ pullback.fst f h =
      (closedSupportEndpointIso f g h φ q a H m).hom ≫
        pullback.fst φ (m ≫ pullback.fst g h) := by
  let : IsClosedImmersion φ := MorphismProperty.of_isPullback H.flip inferInstance
  apply (cancel_mono φ).mp
  let q₀ := m ≫ pullback.fst g h
  let e := (closedSupportEndpointIso f g h φ q a H m).hom
  let v := Scheme.AffineLineFiber.inclusion (m ≫ pullback.fst g h ≫ q) a
  have he := congrArg (fun t => t ≫ pullback.fst g h)
    (closedSupportEndpointMap_ambient f g h φ hφ q a H m)
  calc
    _ = v ≫ q₀ := by
      simpa only [v, q₀, Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
        pullback.lift_fst] using he
    _ = (e ≫ pullback.snd φ q₀) ≫ q₀ :=
      congrArg (fun t => t ≫ q₀) (closedSupportEndpointIso_total f g h φ q a H m).symm
    _ = _ := by
      simpa only [e, q₀, Category.assoc] using
        congrArg (fun t => e ≫ t) (pullback.condition (f := φ) (g := q₀)).symm

/-- The target coordinate also retains the original whole support map. -/
@[reassoc (attr := simp)] theorem closedSupportEndpointMap_snd
    (m : D ⟶ pullback g h) :
    closedSupportEndpointMap f g h φ hφ q a H m ≫ pullback.snd f h =
      inclusion (m ≫ pullback.fst g h ≫ q) a ≫ m ≫ pullback.snd g h := by
  have he := congrArg (fun v => v ≫ pullback.snd g h)
    (closedSupportEndpointMap_ambient f g h φ hφ q a H m)
  simpa only [Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
    pullback.lift_snd, Category.comp_id] using he

/-- Native component restriction followed by the actual section fiber. -/
def closedSupportComponentEndpointIso (m : D ⟶ pullback g h) [IsClosedImmersion m]
    (z : D) :
    fiber ((integralComponentAt z).subschemeι ≫ m ≫ pullback.fst g h ≫ q) a ≅
      correspondenceGraphFiber g h (m z) φ := by
  let e := asIso (pullback.map
    (point a) ((integralComponentAt z).subschemeι ≫ m ≫ pullback.fst g h ≫ q)
    (point a) (((integralComponentAt (m z)).subschemeι ≫ pullback.fst g h) ≫ q)
    (𝟙 _) (integralComponentMap m z) (𝟙 _) (by simp)
    (by simp only [Category.comp_id, ← Category.assoc, integralComponentMap_subschemeι]))
  exact e ≪≫ wholeFiberIso φ f q (point a) H
    ((integralComponentAt (m z)).subschemeι ≫ pullback.fst g h)

/-- The comparison keeps the original unreduced fiber's map into its integral support. -/
@[reassoc (attr := simp)] theorem closedSupportComponentEndpointIso_snd
    (m : D ⟶ pullback g h) [IsClosedImmersion m] (z : D) :
    (closedSupportComponentEndpointIso f g h φ q a H m z).hom ≫
      pullback.snd φ ((integralComponentAt (m z)).subschemeι ≫ pullback.fst g h) =
        inclusion ((integralComponentAt z).subschemeι ≫ m ≫ pullback.fst g h ≫ q) a ≫
          integralComponentMap m z := by
  simp only [closedSupportComponentEndpointIso, Iso.trans_hom, Category.assoc,
    wholeFiberIso_hom_total, asIso_hom, Scheme.AffineLineFiber.inclusion, pullback.map,
    pullback.lift_snd]

/-- Both actual routes into the endpoint ambient product coincide. -/
@[reassoc (attr := simp)] theorem closedSupportComponentEndpointIso_outer
    (m : D ⟶ pullback g h) [IsClosedImmersion m] (z : D) :
    (closedSupportComponentEndpointIso f g h φ q a H m z).hom ≫
      correspondenceGraphFiberMap f g h (m z) φ hφ =
        fiberMap (m ≫ pullback.fst g h ≫ q) a (integralComponentAt z).subschemeι ≫
          closedSupportEndpointMap f g h φ hφ q a H m := by
  let := isClosedImmersion_correspondenceEndpointAmbientMap f g h φ hφ q a H
  apply (cancel_mono (correspondenceGraphFiberAmbientMap f g h φ hφ)).mp
  rw [Category.assoc, (isPullback_correspondenceGraphFiberMap f g h (m z) φ hφ).w,
    closedSupportComponentEndpointIso_snd_assoc]
  simp only [Category.assoc, closedSupportEndpointMap_ambient, fiberMap_inclusion_assoc,
    integralComponentMap_subschemeι]

end Stacks.Chow
