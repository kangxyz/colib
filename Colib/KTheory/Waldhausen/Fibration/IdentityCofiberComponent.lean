/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.Fibration.CofiberObjectChangeWeak
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportNaturality
public import Colib.KTheory.Waldhausen.GrothendieckComparison.IdentityCofiberSuffix
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.LeftComponentTranslation

/-!
# Component translation using the actual identity-cofiber triangle

The suffix path is the original identity-cofiber triangle, with its literal chosen-zero
quotient. Its localization keeps every original comparison and loop coordinate. The resulting
component equivalence is explicitly matched to that prism face; no equality with the standard
suffix-removal path or final Laurent boundary normalization is asserted here.
-/
/-! Implementation provenance: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The existing `identityCofiberComponentEquiv` at source lines 62–67 is retained unchanged.
The two remaining topological declarations at lines 85–145 are added here; the
identity-grid comparison lives in the categorical cofiber change-weak leaf.
Independent category universes and all original hypotheses are preserved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology SSet
open CategoryTheory.Waldhausen.QuotientRows
open scoped Topology Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- Left prefix followed by the actual identity triangle gives the prism-matched equivalence. -/
def identityCofiberComponentEquiv (n : ℕ) :
    HomotopyGroup.Pi n (Path W.kBasepoint W.kBasepoint) (Path.refl W.kBasepoint) ≃
      HomotopyGroup.Pi n (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
  (loopLeftTranslationHomotopyEquiv (W.kZeroObjectLoop A) n).trans
    (pathTransport (W.identityCofiberSuffixPath A) n)

attribute [colib_tag "COL-0297"] identityCofiberComponentEquiv

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean:62-67" "adaptation"
  "The degree-n constructor is left translation followed by transport along the prescribed
    identity-cofiber suffix; this construction does not assert normalization in every degree"]
  identityCofiberComponentEquiv

end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V) (A : C)

/-- Localization retains the whole specified identity-triangle suffix path. -/
theorem identityCofiberSuffixPath_changeWeak (s t : unitInterval) :
    changeWeakMap N (V.identityCofiberSuffixPath A s t) =
      N.coarse.identityCofiberSuffixPath A s t := by
  have he : (sSetMap (changeWeak_exact N)).app (Opposite.op ⦋2⦌)
      (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
        (cofiberTwo_identity_square V)) =
      N.coarse.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ N.coarse.zero)
        (N.coarse.cof.id_mem A) (cofiberTwo_identity_square N.coarse) := by
    apply Subtype.ext
    change _ ⋙ 𝟭 C = _
    rw [Functor.comp_id]
    exact identityCofiberSimplex_val_of_zero_eq A N.coarse N.zero_eq.symm
  rw [Structure.identityCofiberSuffixPath_apply, Structure.identityCofiberSuffixPath_apply,
    Structure.cofiberObjectLoopTrack_apply, Structure.cofiberObjectLoopTrack_apply,
    realizationEdgeCompositionHomotopy_apply, realizationEdgeCompositionHomotopy_apply]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm
    (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
      (cofiberTwo_identity_square V))) ≫ SSet.toTop.map (sSetMap (changeWeak_exact N))) _ = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp, he]
  rfl

/-- The prism-matched component equivalence is natural for the original localization map. -/
theorem identityCofiberComponentEquiv_naturality (n : ℕ)
    (a : HomotopyGroup.Pi n (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint)) :
    N.coarse.identityCofiberComponentEquiv A n
        (HomotopyGroup.map (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
          (basedLoopMap_refl _ _) a) =
      HomotopyGroup.map (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A)
        (V.identityCofiberComponentEquiv A n a) := by
  let g := basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
  have hA : g (V.kZeroObjectLoop A) = N.coarse.kZeroObjectLoop A :=
    deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A
  have ht : g ((V.kZeroObjectLoop A).trans (Path.refl V.kBasepoint)) =
      (N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint) := by
    rw [basedLoopMap_trans, basedLoopMap_refl, hA]
  have hn : HomotopyGroup.map g ht
        (loopLeftTranslationHomotopyEquiv (V.kZeroObjectLoop A) n a) =
      loopLeftTranslationHomotopyEquiv (N.coarse.kZeroObjectLoop A) n
        (HomotopyGroup.map g (basedLoopMap_refl _ _) a) := by
    induction a using Quotient.inductionOn with
    | h p =>
      change Quotient.mk' (GenLoop.postcomp g ht
        (GenLoop.postcomp (loopLeftTranslationEquiv (V.kZeroObjectLoop A)).toFun _ p)) =
          Quotient.mk' (GenLoop.postcomp (loopLeftTranslationEquiv
            (N.coarse.kZeroObjectLoop A)).toFun _ (GenLoop.postcomp g _ p))
      apply congrArg Quotient.mk'
      ext s t
      change g (loopLeftTranslationEquiv (V.kZeroObjectLoop A) (p s)) t =
        loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A) (g (p s)) t
      rw [loopLeftTranslationEquiv_apply, loopLeftTranslationEquiv_apply,
        basedLoopMap_trans, hA]
  change pathTransport (N.coarse.identityCofiberSuffixPath A) n
    (loopLeftTranslationHomotopyEquiv (N.coarse.kZeroObjectLoop A) n
      (HomotopyGroup.map g (basedLoopMap_refl _ _) a)) = _
  rw [← hn]
  exact pathTransport_naturality_of_track g (V.identityCofiberSuffixPath A)
    (N.coarse.identityCofiberSuffixPath A) ht hA
    (fun s ↦ by ext t; exact identityCofiberSuffixPath_changeWeak N A s t)
    n (loopLeftTranslationHomotopyEquiv (V.kZeroObjectLoop A) n a)

attribute [colib_tag "COL-0299"] identityCofiberSuffixPath_changeWeak

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean:86-105" "adaptation"
  "The actual changeWeak map preserves the entire prescribed identity-cofiber suffix for
    independent path and object-loop times, not only its degree-one transport"]
  identityCofiberSuffixPath_changeWeak

attribute [colib_tag "COL-0299"] identityCofiberComponentEquiv_naturality

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean:108-145" "adaptation"
  "Naturality of the existing prism-matched component equivalence for every homotopy degree
    n, through the original based loop map and whole identity-suffix track"]
  identityCofiberComponentEquiv_naturality

end CategoryTheory.Waldhausen.Fibration
