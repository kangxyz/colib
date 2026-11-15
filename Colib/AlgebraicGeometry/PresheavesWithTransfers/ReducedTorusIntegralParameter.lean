/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusIntegralUnderlying
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusCoordinateInsertion

/-! # The actual integral-to-ordinary parameter comparison square

The coefficient comparison is the previously constructed chain isomorphism,
not a replacement by an isomorphic object with a new parameter map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The previously constructed chain comparison is the identity on the
original underlying reduced-torus section in every degree. -/
theorem reducedTorusIntChainsUnderlyingIso_hom_apply (q n : ℕ)
    (U : SmoothSite (Spec (CommRingCat.of k)))
    (s : sections (reducedTorus k q)
      (Cor.mk (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k n)))) :
    (((reducedTorusIntChainsUnderlyingIso k q).hom.f n).app (op U)) s = s := by
  rfl

/-- The actual integral insertion followed by the actual chain pairing agrees
with the original ordinary parameter map through the verified coefficient isos. -/
theorem reducedTorusIntChainsUnderlyingIso_parameter (q : ℕ) :
    let G := SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
    let U := ((Functor.whiskeringRight
      (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ (ModuleCat.{u + 1} ℤ)
        AddCommGrpCat.{u + 1}).obj
          (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)).mapHomologicalComplex (.down ℕ)
    let T := (AlgebraicSimplex.parameterReindex k
      (A := AddCommGrpCat.{u + 1}) G).mapHomologicalComplex (.down ℕ)
    let T' := (AlgebraicSimplex.parameterReindex k
      (A := ModuleCat.{u + 1} ℤ) G).mapHomologicalComplex (.down ℕ)
    U.map (reducedTorusChainCoordinateInsertion k q ≫
        T'.map (reducedTorusPresheafChainPairing k q)) ≫
      T.map (reducedTorusIntChainsUnderlyingIso k (q + 1)).hom =
    (reducedTorusIntChainsUnderlyingIso k q).hom ≫
      reducedTorusSingularParameterProduct k q := by
  intro G U T T'
  apply HomologicalComplex.hom_ext
  intro n
  apply NatTrans.ext
  funext X
  ext s
  exact reducedTorusChainCoordinateInsertion_pairing k X.unop q n s

end AlgebraicGeometry.PresheafWithTransfers
