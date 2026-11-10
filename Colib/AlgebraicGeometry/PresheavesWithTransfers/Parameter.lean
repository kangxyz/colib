/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Composition
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Graph
public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphInterchange
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# Actual parameter products for transfer presheaves

The parameter may be any geometrically integral smooth scheme. Products on
signed correspondences are the existing native exterior-support construction;
its composition, identity and graph-interchange laws are used without extra
provider assumptions. This is the geometric input for affine-line contraction.

Adapted from `motivic_source_a6805c4`,
`Motivic/Transfers/Presheaf/ContractionExterior.lean:32-150`.
`Exterior.Composition` is a separate source candidate pending native validation;
its actual theorem is imported, not replaced by a composition-law hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.Cor
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Product with a geometrically integral smooth parameter, on actual signed cycles. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ContractionExterior.lean:32-39"
  "adaptation" "Native exterior identity and the actual signed incidence Tor composition"]
def parameterProduct (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    Cor k ⥤ Cor k where
  obj X := Cor.mk (SmoothSite.product X.toSmoothSite T)
  map {X Y} α := Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T α
  map_id X := Stacks.Chow.nativeExterior_id X.toSmoothSite T
  map_comp {X Y Z} α β := Stacks.Chow.nativeExterior_incidenceTorPairing
    X.toSmoothSite Y.toSmoothSite Z.toSmoothSite T α β

instance parameterProduct_additive (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] : (parameterProduct T).Additive where
  map_add {X Y} := map_add (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T) _ _

/-- Restricting the actual exterior operation to graphs gives the literal product map. -/
@[simp] theorem parameterProduct_graph (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (parameterProduct T).map ((graphFunctor k).map f) =
      (graphFunctor k).map (SmoothSite.productMap f (𝟙 T)) :=
  Stacks.Chow.nativeExterior_graphFunctor X Y T f

/-- A map of parameters is natural for every signed finite correspondence. -/
def parameterProductMap {T T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom] (f : T ⟶ T') :
    parameterProduct T ⟶ parameterProduct T' where
  app X := (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) f)
  naturality X Y α :=
    (Stacks.Chow.nativeExterior_graph_interchange X.toSmoothSite Y.toSmoothSite T T' f α).symm

@[simp] theorem parameterProductMap_app {T T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom] (f : T ⟶ T')
    (X : Cor k) :
    (parameterProductMap f).app X =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) f) := rfl

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Evaluate coefficients on the actual relative parameter product. -/
def withParameter (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    PresheafWithTransfers.{v} k :=
  AdditiveFunctor.of ((Cor.parameterProduct T).op ⋙ P.obj)

@[simp] theorem withParameter_sections (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] (X : Cor k) :
    sections (withParameter P T) X =
      sections P (Cor.mk (SmoothSite.product X.toSmoothSite T)) := rfl

/-- Parameter-product transfers are the literal exterior signed correspondences. -/
@[simp] theorem withParameter_transfer (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer (withParameter P T) α =
      transfer P (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T α) := rfl

/-- Actual restriction in the parameter variable, natural for all transfers. -/
def parameterPullback (P : PresheafWithTransfers.{v} k)
    {T T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom] (f : T ⟶ T') :
    withParameter P T' ⟶ withParameter P T :=
  ⟨Functor.whiskerRight (NatTrans.op (Cor.parameterProductMap f)) P.obj⟩

@[simp] theorem parameterPullback_app (P : PresheafWithTransfers.{v} k)
    {T T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom] (f : T ⟶ T')
    (X : Cor k) :
    (parameterPullback P f).hom.app (op X) =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productMap (𝟙 X.toSmoothSite) f)) := rfl

@[simp] theorem parameterPullback_id (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    parameterPullback P (𝟙 T) = 𝟙 (withParameter P T) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  change transfer P ((Cor.graphFunctor k).map
    (SmoothSite.productMap (𝟙 X.unop.toSmoothSite) (𝟙 T))) = 𝟙 _
  rw [SmoothSite.productMap_id, (Cor.graphFunctor k).map_id, transfer_id]

/-- Parameter restriction reverses the actual composition of parameter maps. -/
@[reassoc] theorem parameterPullback_comp (P : PresheafWithTransfers.{v} k)
    {T T' T'' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]
    [GeometricallyIntegral T''.hom] (f : T ⟶ T') (g : T' ⟶ T'') :
    parameterPullback P (f ≫ g) = parameterPullback P g ≫ parameterPullback P f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  change transfer P ((Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 X.unop.toSmoothSite) (f ≫ g))) =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 _) g)) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 _) f))
  rw [← transfer_comp, ← Functor.map_comp, ← SmoothSite.productMap_comp,
    Category.id_comp]

/-- Coefficient maps are evaluated on the same actual products. -/
def withParameterMap {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    withParameter P T ⟶ withParameter Q T :=
  ⟨Functor.whiskerLeft (Cor.parameterProduct T).op η.hom⟩

@[reassoc]
theorem parameterPullback_coefficient_naturality
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    {T T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom] (f : T ⟶ T') :
    parameterPullback P f ≫ withParameterMap η T =
      withParameterMap η T' ≫ parameterPullback Q f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  exact η.hom.naturality ((Cor.parameterProductMap f).app X.unop).op

/-- Graph restriction of the signed parameter functor is the already chosen cylinder.
Its components are identities on the actual coefficient groups. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ContractionSheaf.lean:38-49"
  "adaptation" "Underlying comparison before sheafness, on the chosen native cylinders"]
def withParameterUnderlyingIso (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    (toPresheaf k).obj (withParameter P T) ≅
      (SmoothSite.Contraction.parameterProduct T).op ⋙ (toPresheaf k).obj P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change transfer P ((Cor.parameterProduct T).map ((Cor.graphFunctor k).map f.unop)) ≫
        𝟙 _ = 𝟙 _ ≫ transfer P ((Cor.graphFunctor k).map
          (SmoothSite.productMap f.unop (𝟙 T)))
    rw [Category.comp_id, Category.id_comp, Cor.parameterProduct_graph])

@[simp]
theorem withParameterUnderlyingIso_hom_app (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    (withParameterUnderlyingIso P T).hom.app X = 𝟙 _ := rfl

end AlgebraicGeometry.PresheafWithTransfers
