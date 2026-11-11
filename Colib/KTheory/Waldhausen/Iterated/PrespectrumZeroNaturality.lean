/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ZeroMap
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumTransformationTransport

/-!
# Whole original zero-source transformation tracks under strict Model squares

A strict square of actual chosen-zero-preserving Model maps automatically identifies the whole
realized tracks of transformations from their original zero functors. Pointwise uniqueness from
the actual zero objects proves the categorical transformation square, including the source-zero
transport. The original homotopy time and the degree-zero loop coordinate are unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- Actual zero Model maps commute with the original chosen-zero-preserving square sides. -/
theorem zeroHom_square {V W T U : WideSubcategory preservesZero.{u}} (a : V ⟶ T) (b : W ⟶ U) :
    zeroHom V W ≫ b = a ≫ zeroHom T U := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => b.property) ?_
  intro X Y f
  exact (b.hom.isExact.zero W.obj.waldhausen.isZero).eq_of_src _ _

/-- The whole original zero-source tracks commute with every strict original Model square. -/
theorem prespectrumZeroTransformationHomotopy_naturality
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor)
    (θ : (zeroHom T U).hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X)) (n : ℕ) :
    ((prespectrumTransformationHomotopy η hη).postcomp (prespectrumMap b)).level n =
      (Homotopy.precomp (prespectrumMap a) (prespectrumTransformationHomotopy θ hθ)).level n := by
  let α : (zeroHom V W ≫ b).hom.toFunctor ⟶ (F ≫ b).hom.toFunctor := whiskerRight η b.hom.toFunctor
  let β : (a ≫ zeroHom T U).hom.toFunctor ⟶ (a ≫ G).hom.toFunctor := whiskerLeft a.hom.toFunctor θ
  have hzero := zeroHom_square a b
  have he : α = eqToHom (congrArg (fun f : V ⟶ U => f.hom.toFunctor) hzero) ≫ β ≫
      eqToHom (congrArg (fun f : V ⟶ U => f.hom.toFunctor) h.symm) := by
    ext X
    exact (b.hom.isExact.zero W.obj.waldhausen.isZero).eq_of_src _ _
  have ht : ∀ X, U.obj.waldhausen.weq
      ((eqToHom (congrArg (fun f : V ⟶ U => f.hom.toFunctor) hzero) ≫ β ≫
        eqToHom (congrArg (fun f : V ⟶ U => f.hom.toFunctor) h.symm)).app X) := by
    intro X
    have hx := congrArg (fun σ => σ.app X) he
    rw [← hx]
    exact b.hom.isExact.weak _ (hη X)
  have hc := prespectrumTransformationHomotopy_transport_level hzero h.symm β
    (fun X => hθ (a.hom.toFunctor.obj X)) ht n
  have heLevel : (prespectrumTransformationHomotopy α
      (fun X => b.hom.isExact.weak _ (hη X))).level n =
        (prespectrumTransformationHomotopy
          (eqToHom (congrArg (fun f : V ⟶ U => f.hom.toFunctor) hzero) ≫ β ≫
            eqToHom (congrArg (fun f : V ⟶ U => f.hom.toFunctor) h.symm)) ht).level n := by
    exact prespectrumTransformationHomotopy_level_eq_of_heq rfl rfl _ _ _ _ (heq_of_eq he) n
  exact (prespectrumTransformationHomotopy_postcomp_level η hη b n).symm.trans
    (heLevel.trans (hc.trans (prespectrumTransformationHomotopy_precomp_level θ hθ a n)))

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/PrespectrumZeroNaturality.lean:26-67"
  "adaptation" "Whole native transformation tracks with unchanged independent coordinates"]
  zeroHom_square
  prespectrumZeroTransformationHomotopy_naturality

end CategoryTheory.Waldhausen.IteratedS
