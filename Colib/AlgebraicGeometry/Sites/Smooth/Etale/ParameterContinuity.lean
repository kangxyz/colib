/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology

/-! # Continuous parameter products on the smooth étale site

The literal relative product is continuous for the actual smooth étale topology.
This does not assert that étale sheafification commutes with parameter sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {S : Scheme.{u}}

instance parameterProduct_isContinuous_etale (T : SmoothSite S) :
    (parameterProduct T).IsContinuous (etaleTopology S) (etaleTopology S) := by
  let : (prod.functor.flip.obj T).IsContinuous
      (etaleTopology S) (etaleTopology S) :=
    Functor.prodRight_isContinuous (etalePrecoverage S) T
  exact Functor.isContinuous_of_iso (categoricalParameterProductIso T)
    (etaleTopology S) (etaleTopology S)

/-- Literal parameter reindexing preserves étale sheaves in independent universes. -/
theorem parameterProduct_op_comp_isSheaf_etale (T : SmoothSite S)
    {A : Type w} [Category.{v} A] (P : (SmoothSite S)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (etaleTopology S) P) :
    Presheaf.IsSheaf (etaleTopology S) ((parameterProduct T).op ⋙ P) :=
  (parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ P hP

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
