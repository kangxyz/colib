/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdjoinRoot.TowerFactorGalois

noncomputable section

open Polynomial Stacks.Chow MonicIrreducibleOfDegree

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

example (σ : Gal((AdjoinRoot p)/k)) :
    (poly (AdjoinRoot.towerFactor p h (f.comp σ.toAlgHom)).1.2).map σ.toRingHom =
      poly (AdjoinRoot.towerFactor p h f).1.2 :=
  AdjoinRoot.towerFactor_compGal_poly_map p h f σ

example (hp : p.Monic) [Normal k (AdjoinRoot p)] (_hnotsep : ¬h.Separable) :
    Function.Bijective (fun σ : Gal((AdjoinRoot p)/k) =>
      AdjoinRoot.towerFactor p h (f.comp σ.toAlgHom)) :=
  AdjoinRoot.towerFactor_comp_gal_bijective p h f hp
