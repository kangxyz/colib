/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
import Colib.AlgebraicGeometry.Correspondences.Additive.Ext
import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterSwap.Point
import Colib.AlgebraicGeometry.Correspondences.Graph.Isomorphism

/-!
# Exchange of two actual signed correspondence parameters

The native permutation identifies the two full iterated prime supports.
Graph transport preserves their coefficient one, and additivity extends
the identity to all signed finite correspondences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (X Y T V : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral V.hom]

local notation "Xₜ" => SmoothSite.product X T
local notation "Yₜ" => SmoothSite.product Y T
local notation "Xᵥ" => SmoothSite.product X V
local notation "Yᵥ" => SmoothSite.product Y V
local notation "Xₜᵥ" => SmoothSite.product Xₜ V
local notation "Yₜᵥ" => SmoothSite.product Yₜ V
local notation "Xᵥₜ" => SmoothSite.product Xᵥ T
local notation "Yᵥₜ" => SmoothSite.product Yᵥ T
local notation "F" => parameterProduct T ⋙ parameterProduct V
local notation "G" => parameterProduct V ⋙ parameterProduct T
local notation "σX" => SmoothSite.productSwapLastIso X T V
local notation "σY" => SmoothSite.productSwapLastIso Y T V
local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)

private theorem parameterProduct_twice_single
    (z : pullback (C := Scheme) X.hom Y.hom) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    (F).map (singleFiniteCorrespondence X.hom Y.hom z hz 1 : Cor.mk X ⟶ Cor.mk Y) =
      singleFiniteCorrespondence (Xₜᵥ).hom (Yₜᵥ).hom
        (nativeExteriorPoint Xₜ Yₜ V (nativeExteriorPoint X Y T z hz)
          (nativeExteriorPoint_admissible X Y T z hz))
        (nativeExteriorPoint_admissible Xₜ Yₜ V _ _) 1 := by
  change nativeExterior Xₜ Yₜ V
    (nativeExterior X Y T (singleFiniteCorrespondence X.hom Y.hom z hz 1)) = _
  rw [nativeExterior_single, one_smul, nativeExteriorPrime_eq_single,
    nativeExterior_single, one_smul, nativeExteriorPrime_eq_single]

private theorem parameterProductSwap_single
    (z : pullback (C := Scheme) X.hom Y.hom) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    (F).map (singleFiniteCorrespondence X.hom Y.hom z hz 1 : Cor.mk X ⟶ Cor.mk Y) ≫
        γ (σY).hom =
      γ (σX).hom ≫
        (G).map (singleFiniteCorrespondence X.hom Y.hom z hz 1 : Cor.mk X ⟶ Cor.mk Y) := by
  classical
  rw [parameterProduct_twice_single X Y T V z hz, parameterProduct_twice_single X Y V T z hz]
  apply Subtype.ext
  rw [single_comp_graph_iso_val, graph_iso_comp_single_val]
  let s := SmoothSite.productMap (σX).hom (σY).hom
  let a := SmoothSite.productMap (𝟙 Xₜᵥ) (σY).hom
  let b := SmoothSite.productMap (σX).inv (𝟙 Yᵥₜ)
  have hcomp : s ≫ b = a := by
    dsimp only [s, a, b]
    rw [← SmoothSite.productMap_comp, Iso.hom_inv_id, Category.comp_id]
  have hmap : s.left ≫ b.left = a.left := congrArg (fun f => f.left) hcomp
  let zₜ := nativeExteriorPoint X Y T z hz
  let zᵥ := nativeExteriorPoint X Y V z hz
  let wₜᵥ := nativeExteriorPoint Xₜ Yₜ V zₜ (nativeExteriorPoint_admissible X Y T z hz)
  let wᵥₜ := nativeExteriorPoint Xᵥ Yᵥ T zᵥ (nativeExteriorPoint_admissible X Y V z hz)
  have hpoint : a.left wₜᵥ = b.left wᵥₜ := by
    calc
      _ = (s.left ≫ b.left) wₜᵥ := congrArg (fun f => f wₜᵥ) hmap.symm
      _ = b.left (s.left wₜᵥ) := rfl
      _ = _ := congrArg b.left (nativeExteriorIteratedPoint_swap X Y T V z hz)
  exact congrArg (fun p => single p (1 : ℤ)) hpoint

/-- The actual permutation is natural for every signed finite correspondence. -/
@[reassoc]
theorem parameterProductSwap_naturality (α : Cor.mk X ⟶ Cor.mk Y) :
    (F).map α ≫ γ (σY).hom = γ (σX).hom ≫ (G).map α := by
  have h : (Preadditive.rightComp ((F).obj (Cor.mk X)) (γ (σY).hom)).comp
      (F).mapAddHom =
      (Preadditive.leftComp ((G).obj (Cor.mk Y)) (γ (σX).hom)).comp (G).mapAddHom := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    exact parameterProductSwap_single X Y T V z hz
  exact DFunLike.congr_fun h α

variable {X Y}

/-- The native correspondence parameter functors exchange via the graph of
the actual smooth-site factor permutation. -/
def parameterProductSwapNatIso : F ≅ G :=
  NatIso.ofComponents
    (fun X => (graphFunctor k).mapIso (SmoothSite.productSwapLastIso X.toSmoothSite T V))
    (by
      intro A B α
      exact parameterProductSwap_naturality A.toSmoothSite B.toSmoothSite T V α)

@[simp]
theorem parameterProductSwapNatIso_hom_app (X : Cor k) :
    (parameterProductSwapNatIso T V).hom.app X =
      γ (SmoothSite.productSwapLastIso X.toSmoothSite T V).hom := rfl

/-- The permutation respects the actual morphism of the first parameter,
including each coface of the algebraic simplex. -/
@[reassoc]
theorem parameterProductSwapNatIso_parameterMap {T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T'.hom] (f : T ⟶ T') (X : Cor k) :
    (parameterProduct V).map ((parameterProductMap f).app X) ≫
        (parameterProductSwapNatIso T' V).hom.app X =
      (parameterProductSwapNatIso T V).hom.app X ≫
        (parameterProductMap f).app ((parameterProduct V).obj X) := by
  simp only [parameterProductMap_app, parameterProductSwapNatIso_hom_app,
    parameterProduct_graph, ← Functor.map_comp]
  apply (graphFunctor k).congr_map
  have h := SmoothSite.productSwapLast_naturality X.toSmoothSite T V (𝟙 _) f (𝟙 V)
  rwa [SmoothSite.productMap_id] at h

end AlgebraicGeometry.Cor
