/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology
public import Colib.CategoryTheory.Sites.ParameterProduct
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# Continuous parameter products on the smooth site

The endofunctor multiplying by a smooth parameter uses the literal relative
scheme product and its original scheme maps. It preserves existing pullbacks
and is continuous for the actual smooth étale topology. Consequently
precomposition preserves sheaves with values in arbitrary category universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {S : Scheme.{u}}

instance parameterProduct_isContinuousEtale (T : SmoothSite S) :
    (parameterProduct T).IsContinuous (etaleTopology S) (etaleTopology S) := by
  let : (prod.functor.flip.obj T).IsContinuous
      (etaleTopology S) (etaleTopology S) :=
    Functor.prodRight_isContinuous (etalePrecoverage S) T
  exact Functor.isContinuous_of_iso (categoricalParameterProductIso T)
    (etaleTopology S) (etaleTopology S)

/-- Restriction along the literal parameter product preserves sheaves without
restricting either universe of the coefficient category. -/
theorem parameterProduct_op_comp_isSheafEtale (T : SmoothSite S)
    {A : Type w} [Category.{v} A] (P : (SmoothSite S)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (etaleTopology S) P) :
    Presheaf.IsSheaf (etaleTopology S) ((parameterProduct T).op ⋙ P) :=
  (parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ P hP

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
