/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-! Every public endpoint has the allowed axiom closure and exact compiled source citation. -/
open Lean Elab Command in
run_cmd do
  let declarations : List Name := [
    ``CommRingCat.PolynomialLaurent.polynomialUnderFunctor,
    ``CommRingCat.PolynomialLaurent.laurentUnderFunctor,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient,
    ``CommRingCat.PolynomialLaurent.laurentUnderCoefficient,
    ``CommRingCat.PolynomialLaurent.underToLaurent,
    ``CommRingCat.PolynomialLaurent.underToLaurentInvert,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_toLaurent,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_toLaurentInvert,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquare,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareMap,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquare_forget,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareMap_forget,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor_comp_forget,
    ``CommRingCat.PolynomialLaurent.polynomialUnderFunctor_comp_map,
    ``CommRingCat.PolynomialLaurent.laurentUnderFunctor_comp_map,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_map,
    ``CommRingCat.PolynomialLaurent.laurentUnderCoefficient_map,
    ``CommRingCat.PolynomialLaurent.underToLaurent_map,
    ``CommRingCat.PolynomialLaurent.underToLaurentInvert_map,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquare_map,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareMap_map,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor_comp_map]
  let env ← getEnv
  let citations := Colib.Library.citations env
  for decl in declarations do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "aglib" &&
        c.locator == "Aglib/Algebra/Polynomial/Laurent/UnderSquare.lean:26-137" &&
        (c.relation == "adaptation" || c.relation == "comparison")) do
      throwError "Missing exact compiled source citation for {decl}"
  let tagged : List Name := [
    ``CommRingCat.PolynomialLaurent.polynomialUnderFunctor,
    ``CommRingCat.PolynomialLaurent.laurentUnderFunctor,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient,
    ``CommRingCat.PolynomialLaurent.laurentUnderCoefficient,
    ``CommRingCat.PolynomialLaurent.underToLaurent,
    ``CommRingCat.PolynomialLaurent.underToLaurentInvert,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_toLaurent,
    ``CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_toLaurentInvert,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquare,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareMap,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquare_forget,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareMap_forget,
    ``CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor_comp_forget]
  let bindings := (Colib.Library.bindings env).filter (fun b => b.id == "COL-0379")
  unless bindings.size == tagged.length do
    throwError "Unexpected COL-0379 binding count {bindings.size}"
  for decl in tagged do
    unless bindings.any (fun b => b.declName == decl) do
      throwError "Missing compiled COL-0379 binding for {decl}"
  logInfo m!"Checked {declarations.length} public axiom closures and exact citations; \
    {tagged.length} COL-0379 bindings"
