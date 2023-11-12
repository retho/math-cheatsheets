#!/usr/bin/env wolframscript

(* ? module .lie *)

d[a_] := Subscript[d, a];
dif[u_][vars_] := If[Length[vars] == 0, u, Subscript[u, Row@Sort@vars]]
xx[{spaceX_, spaceU_}][i_] := Indexed[spaceX, i]
uu[{spaceX_, spaceU_}][\[Alpha]_] := Indexed[spaceU, \[Alpha]]

applyVect2Fn[vect_][f_] := vect /. expr_ * Subscript[d, a_] :> expr * D[f, a]
applyVect2Vect[vectX_][vectY_] := vectY /. expr_ * Subscript[d, a_] :> applyVect2Fn[vectX][expr] * Subscript[d, a]
lieBracket[vectX_, vectY_] := applyVect2Vect[vectX][vectY] - applyVect2Vect[vectY][vectX]

tmpCombinations[list_, k_] := Union[Sort /@ Tuples[list, k]]
(* ** *)
tmpCoord[vectX_][a_] := vectX /. {expr_ * Subscript[d, a] :> expr, _ * Subscript[d, _] :> 0}
(* ** *)
tmpVect2\[Xi][{spaceX_, spaceU_}][vectX_] := tmpCoord[vectX] /@ spaceX
tmpVect2\[Eta][{spaceX_, spaceU_}][vectX_] := tmpCoord[vectX] /@ spaceU
tmp\[Xi]2Vect[{spaceX_, spaceU_}][xi_] := Total@Table[Indexed[xi, i] d[Indexed[spaceX, i]], {i, 1, Length@spaceX}]
tmp\[Eta]2Vect[{spaceX_, spaceU_}][xi_] := Total@Table[Indexed[xi, i] d[Indexed[spaceU, i]], {i, 1, Length@spaceU}]

tmpFoldDt[{spaceX_, spaceU_}][f_][js_] := Fold[Dt[#1, Indexed[spaceX, {#2}]] &, f, js]
tmpCollectAllDifs[xs_] := Join @@ ((# /. {{a_, n_} :> Table[a, {i, 1, n}], a_ :> {a}}) & /@ xs)
tmpReplaceRulesDt = {DDD[a_, xs__] :> dif[a]@tmpCollectAllDifs@List@xs};
tmpRulesNonUDt2Zero[{spaceX_, spaceU_}] := (DDD[#, __] :> 0) & /@ spaceX
tmpCalcZetaRules[spaceZ_] := Join[tmpRulesNonUDt2Zero[spaceZ], tmpReplaceRulesDt]
(* ** *)
tmpCalc\[Zeta][spaceZ_][vectX_][\[Alpha]_][js_] := With[{
  spaceX = Indexed[spaceZ, {1}],
  spaceU = Indexed[spaceZ, {2}],
  \[Xi] = tmpVect2\[Xi][spaceZ][vectX],
  \[Eta] = tmpVect2\[Eta][spaceZ][vectX]
}, With[{
  dimX = Length[spaceX],
  u\[Alpha] = Indexed[spaceU, {\[Alpha]}]
}, With[{
  valAinner = Indexed[\[Eta], {\[Alpha]}] - Sum[Dt[u\[Alpha], Indexed[spaceX, {i}]] * Indexed[\[Xi], {i}], {i, 1, dimX}],
  valB = Sum[Indexed[\[Xi], {i}] * tmpFoldDt[spaceZ][u\[Alpha]]@Join[{i}, js], {i, 1, dimX}]
}, With[{
  valA = tmpFoldDt[spaceZ][valAinner]@js,
  sym = Subsuperscript[\[Zeta], Row@js, \[Alpha]]
}, valA + valB /. Dt -> DDD /. tmpCalcZetaRules[spaceZ]]]]]

tmpDifByIndexes[spaceZ_][\[Alpha]_][js_] := dif[uu[spaceZ]@\[Alpha]][xx[spaceZ] /@ js]
(* ** *)
tmpPr[spaceZ_][vectX_][p_] := With[{
  spaceX = Indexed[spaceZ, {1}],
  spaceU = Indexed[spaceZ, {2}]
}, With[{
  dimX = Length[spaceX],
  dimU = Length[spaceU]
}, With[{
  jIdxs = tmpCombinations[Range[1, dimX], p]
}, With[{
  allExpr = Table[
    With[{js = Indexed[jIdxs, j]}, tmpCalc\[Zeta][spaceZ][vectX][\[Alpha]][js] * d[tmpDifByIndexes[spaceZ][\[Alpha]]@js]]
    , {\[Alpha], 1, dimU}
    , {j, 1, Length@jIdxs}]
}, Total[Total /@ allExpr]]]]]
(* ** *)
pr[spaceZ_, k_][vectX_] := With[{
  xi = tmpVect2\[Xi][spaceZ]@vectX,
  eta = tmpVect2\[Eta][spaceZ]@vectX
}, tmp\[Xi]2Vect[spaceZ][xi] + tmp\[Eta]2Vect[spaceZ][eta] + Total@Table[tmpPr[spaceZ][vectX][p], {p, 1, k}]]

(* ? module end *)

(* ? samples *)

sampleSpaceZxyzuv = {{x, y, z}, {u, v}};
sampleSpaceZxu = {{x}, {u}};
sampleSpaceZxyu = {{x, y}, {u}};

(* ** *)
Print@"Переменные"
Print@{d[x], d[u], dif[u][{}], u == dif[u][{}], dif[u][{y, x}], d@dif[u]@{x, y}}
Print@@{xx[sampleSpaceZxyzuv] /@ {1, 2, 3}, uu[sampleSpaceZxyzuv] /@ {1, 2}}
(* ** *)
Print@"скобка Ли"
Print[applyVect2Fn[x d[x] + 2 y d[y] + 3 z d[z]]@(2 x^6 - 5 y^3 + z^2)]
Print@{applyVect2Vect[x d[y]][-y d[x] + x d[y]]}
Print@{lieBracket[-y d[x] + x d[y], -z d[y] + y d[z]], -z d[x] + x d[z]}
(* ** *)
Print@"продолжение оператора"
Print@{pr[sampleSpaceZxu, 2]@{u d[x] - x d[u]}, pr[sampleSpaceZxyu, 2]@{y d[x] - x d[y]}}
(* ** *)

(* ? samples end *)
