/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNervePointwiseFamily

/-!
# Exact reanchoring of attached common-reference parameters

Attachment and reanchoring commute on full reference nodes. The induced equality holds on the
whole nerve realization, and changing the reference preserves pointwise evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor
open scoped Simplicial Topology

universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory SSet Topology
open ModelSimplex (reanchorNode reanchorNode_assoc reanchorSimplex reanchorSimplex_eq)

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)

/-- The reference change composes with the full dependent attachment node. -/
theorem reanchor_attach_node (τ : G.hom.toFunctor ≅ G.hom.toFunctor)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) (N : Node F) :
    reanchorNode τ (attachPostcompNode F J G ε N) =
      attachPostcompNode F J G (τ ≪≫ ε) N := by
  exact reanchorNode_assoc τ ε ⟨N.1 ≫ J, isoWhiskerRight N.2 J.hom.toFunctor⟩

/-- The full-reference identity holds at each point of the realization. -/
theorem reanchor_attach_parameter (τ : G.hom.toFunctor ≅ G.hom.toFunctor)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) (y : |nerve (Codiscrete (Node F))|) :
    mapParameter (reanchorNode τ) (mapParameter (attachPostcompNode F J G ε) y) =
      mapParameter (attachPostcompNode F J G (τ ≪≫ ε)) y := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F y
  rw [← hz, mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin (k + 1) → Node G ↦ parameter G ns z)
    (funext fun i ↦ reanchor_attach_node F J G τ ε (N i))

/-- Reanchoring preserves native evaluation of the whole realization, including level zero. -/
theorem pointwise_reanchor {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (τ : F.hom.toFunctor ≅ G.hom.toFunctor) (n : ℕ) (y : |nerve (Codiscrete (Node G))|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (mapParameter (reanchorNode τ) y) x =
      pointwisePrespectrumFamily G n y x := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter G y
  rw [← hz, mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  change prespectrumSimplexFamily (reanchorSimplex τ N) n (z, x) = _
  rw [reanchorSimplex_eq]

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
