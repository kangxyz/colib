/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Units.KummerLocalSurjectivity

/-! # Regression checks for genuine smooth étale Kummer extraction -/

open CategoryTheory AlgebraicGeometry
open Scheme.SmoothSite

universe u

example (S : Scheme.{u}) :
    Presheaf.IsLocallySurjective (etaleTopology S)
      (1 • 𝟙 (unitsPresheaf S)) :=
  Kummer.power_isLocallySurjective S 1 (by decide) (by simp)

example (S : Scheme.{u})
    [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]
    (h : IsUnit (6 : Γ(S, ⊤))) :
    (Kummer.kummerSequence S 6).ShortExact :=
  Kummer.kummerSequence_shortExact S 6 (by decide) h

#print axioms Kummer.rootObject_cover
#print axioms Kummer.rootOnCover_pow
#print axioms Kummer.kummerSequence_shortExact

example (S : Scheme.{u}) (h : IsUnit (6 : Γ(S, ⊤))) :
    Epi (6 • 𝟙 (largeUnitsEtaleSheaf S)) :=
  Kummer.largeUnitsEtaleSheaf_nsmul_epi S 6 (by decide) h

open Lean Elab Command in
run_cmd do
  for decl in [``Kummer.rootObject_cover, ``Kummer.rootOnCover_pow,
      ``Kummer.largeUnitsEtaleSheaf_nsmul_epi, ``Kummer.kummerSequence_shortExact] do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let primary := ``Kummer.largeUnitsEtaleSheaf_nsmul_epi
  let auxiliary := ``Kummer.kummerSequence_shortExact
  for decl in [primary, auxiliary] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.id == "COL-1233" && b.declName == decl) do
      throwError "Missing compiled COL-1233 binding for {decl}"
  let refs := (Colib.Library.citations env).filter (fun c =>
    c.declName == primary || c.declName == auxiliary)
  unless refs.size == 3 do
    throwError "Expected three compiled COL-1233 references"
  for c in refs do
    logInfo m!"COL1233_REF|{c.source}|{c.locator}"
