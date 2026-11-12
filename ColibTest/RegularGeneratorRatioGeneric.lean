/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularGeneratorRatioGeneric

/-! The actual ordinary unit represents the literal native meromorphic ratio. -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

example (X : Scheme.{u}) [IsIntegral X] (P : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P]
    [P.IsQuasicoherent]
    (U : Stacks.Chow.DenseOpen X) (hU : genericPoint X ∈ U.val)
    (p c : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace P U.val)
    (s t : MeromorphicSection X.sheaf P)
    (hs : IsRegularMeromorphicSection X.sheaf P s)
    (ht : IsRegularMeromorphicSection X.sheaf P t)
    (hc : meromorphicGenericValue X P s = P.presheaf.germ U.val (genericPoint X) hU c.val)
    (hp : meromorphicGenericValue X P t = P.presheaf.germ U.val (genericPoint X) hU p.val) :
    rationalGeneratorRatioUnit X P U p c = meromorphicSectionRatio X P s t hs ht :=
  rationalGeneratorRatioUnit_eq_meromorphicSectionRatio X P U hU p c s t hs ht hc hp

#print axioms AlgebraicGeometry.rationalGeneratorRatioUnit_eq_meromorphicSectionRatio
