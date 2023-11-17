#!/usr/bin/env wolframscript

(* ? module .lie *)

(* print[v_] := Print[v /. (ScalarMulD[expr_, a_] :> expr * Subscript[d, a])] *)

d[v_] := 1 \[CenterDot] Subscript[d, v];
(* * https://mathematica.stackexchange.com/questions/274911/how-to-define-an-operator-like-%E2%8A%95 *)
a_ \[CenterDot] b_ \[CenterDot] c__ := (a * b) \[CenterDot] c; (* * умножение вектора на скаляр *)
CenterDot[a_, CenterDot[b_, c_]] := CenterDot[a b, c]
0 \[CenterDot] _ := 0

vect[expr_] := expr /. {
  c1_ * (c2_ \[CenterDot] Subscript[d, a_]) :> (c1 * c2) \[CenterDot] Subscript[d, a]
}

dif[u_][vars_] := If[Length[vars] == 0, u, Subscript[u, Row@Sort@vars]]
xx[{spaceX_, spaceU_}][i_] := Indexed[spaceX, i]
uu[{spaceX_, spaceU_}][\[Alpha]_] := Indexed[spaceU, \[Alpha]]

applyVect2Fn[vectX_][f_] := Together[vectX /. {
  expr_ \[CenterDot] Subscript[d, a_] :> expr * D[f, a]
  , Subscript[d, a_] :> D[f, a]
}]
applyVect2Vect[vectX_][vectY_] := vectY /. expr_ \[CenterDot] da_ :> applyVect2Fn[vectX][expr] \[CenterDot] da
lieBracket[vectX_, vectY_] := vect[applyVect2Vect[vectX][vectY] - applyVect2Vect[vectY][vectX]]

tmpCombinations[list_, k_] := Union[Sort /@ Tuples[list, k]]
(* ** *)
tmpCoord[vectX_][a_] := vectX /. {expr_ \[CenterDot] Subscript[d, a] :> expr, _ \[CenterDot] Subscript[d, _] :> 0}
(* ** *)
tmpVect2\[Xi][{spaceX_, spaceU_}][vectX_] := tmpCoord[vectX] /@ spaceX
tmpVect2\[Eta][{spaceX_, spaceU_}][vectX_] := tmpCoord[vectX] /@ spaceU
tmp\[Xi]2Vect[{spaceX_, spaceU_}][xi_] := Total@Table[Indexed[xi, i] \[CenterDot] d[Indexed[spaceX, i]], {i, 1, Length@spaceX}]
tmp\[Eta]2Vect[{spaceX_, spaceU_}][eta_] := Total@Table[Indexed[eta, \[Alpha]] \[CenterDot] d[Indexed[spaceU, \[Alpha]]], {\[Alpha], 1, Length@spaceU}]

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
    With[{js = Indexed[jIdxs, j]}, tmpCalc\[Zeta][spaceZ][vectX][\[Alpha]][js] \[CenterDot] d[tmpDifByIndexes[spaceZ][\[Alpha]]@js]]
    , {\[Alpha], 1, dimU}
    , {j, 1, Length@jIdxs}]
}, Total[Total /@ allExpr]]]]]
(* ** *)
pr[spaceZ_, k_][vectX_] := With[{
  xi = tmpVect2\[Xi][spaceZ]@vectX,
  eta = tmpVect2\[Eta][spaceZ]@vectX
}, tmp\[Xi]2Vect[spaceZ][xi] + tmp\[Eta]2Vect[spaceZ][eta] + Total@Table[tmpPr[spaceZ][vectX][p], {p, 1, k}]]

tmpTransformVectMapItem[vectX_][Rule[yi_, expr_]] := applyVect2Fn[vectX][expr] \[CenterDot] d[yi]
transformVect[{coordTransformTo_, coordTransformFrom_}][vectX_] :=
  Total[tmpTransformVectMapItem[vectX] /@ coordTransformTo] /. coordTransformFrom

tmpExpAllVars[_ \[CenterDot] Subscript[d, v_]] := {v}
tmpExpAllVars[Plus[xs__]] := Join@@(tmpExpAllVars /@ List@@xs)
tmpExpEqnsFn[vectX_, a_][v_] := OverBar[v]'[a] == (tmpCoord[vectX][v] /. (# -> OverBar[#][a]& /@ tmpExpAllVars[vectX]))
tmpExpEqnsGn[v_] := OverBar[v][0] == v
tmpExpEqns[vectX_, a_] := With[{
  allVars = tmpExpAllVars[vectX]
}, Join@@{tmpExpEqnsFn[vectX, a] /@ allVars, tmpExpEqnsGn /@ allVars}]
tmpExpSolve[vectX_, a_] := Join@@DSolve[tmpExpEqns[vectX, a], OverBar[#]& /@ tmpExpAllVars[vectX], a]
tmpExp[expr_ \[CenterDot] Subscript[d, a]] := 14
(* ** *)
exp[vectX_] := tmpExpSolve[vectX, $tmpVarA$] /. (OverBar[v_] -> Function[{$tmpVarA$}, expr_]) :> (v -> (expr /. $tmpVarA$ -> 1))

tmpTransformGetAllVars[T_] := T /. (v_ -> _) :> v
(* ** *)
T1_ \[SmallCircle] T2_ \[SmallCircle] Ts__ := (T1 \[SmallCircle] T2) \[SmallCircle] SmallCircle@@Ts
SmallCircle[T_] := T
T1_ \[SmallCircle] T2_ := With[{
  vars1 = tmpTransformGetAllVars[T1],
  vars2 = tmpTransformGetAllVars[T2]
(* }, (Union[vars1, vars2] /. T2) /. T1] *)
}, # -> Simplify[((# /. T2) /. T1)]& /@ Union[vars1, vars2]]

(* ? module end *)

(* * samples *)

sampleSpaceZxyzuv = {{x, y, z}, {u, v}};
sampleSpaceZxu = {{x}, {u}};
sampleSpaceZxyu = {{x, y}, {u}};

(* ** *)
Print@"конструкторы"
Print@{d[x], d[u], dif[u][{}], u == dif[u][{}], dif[u][{y, x}], d@dif[u]@{x, y}}
Print@{xx[sampleSpaceZxyzuv] /@ {1, 2, 3}, uu[sampleSpaceZxyzuv] /@ {1, 2}}
Print@vect@(-y d[x] + x d[y])
(* ** *)
Print@"скобка Ли"
Print[applyVect2Fn[vect@(x d[x] + 2 y d[y] + 3 z d[z])]@(2 x^6 - 5 y^3 + z^2)] (* * [Головин стр. 10] *)
Print@{applyVect2Vect[vect@(x d[y])][vect@(-y d[x] + x d[y])]}
Print@{lieBracket[vect@(-y d[x] + x d[y]), vect@(-z d[y] + y d[z])], vect@(-z d[x] + x d[z])}
Print@lieBracket[vect@(d[y] - (y/z) d[z]), vect@(d[x] - (x/z) d[z])] (* * [Головин стр. 48] *)
(* ** *)
Print@"замена координат"
sampleCoordTransformPolar = {
  {r -> Sqrt[x^2 + y^2], \[Theta] -> ArcTan[y/x]},
  {x -> r Cos[\[Theta]], y -> r Sin[\[Theta]]}
};
Print@transformVect[sampleCoordTransformPolar][-y d[x] + x d[y]]
sampleCoordTransformEx1 = {
  {y1 -> y, y2 -> x, y3 -> Sqrt[y^2 + z^2]},
  {x -> y2, y -> y1, z -> Sqrt[y3^2 - y1^2]}
};
Print[transformVect[sampleCoordTransformEx1]/@vect/@{d[y] - (y/z) d[z], d[x] - (x/z) d[z]}] (* * [Головин стр. 48] *)
(* ** *)
Print@"продолжение оператора"
Print@{pr[sampleSpaceZxu, 2]@vect@(d[x]), pr[sampleSpaceZxyu, 2]@vect@(d[u])}
Print@{pr[sampleSpaceZxu, 2]@vect@(u d[x] - x d[u]), pr[sampleSpaceZxyu, 2]@vect@(y d[x] - x d[y])}
(* ** *)
Print@"exp: g -> G"
Print@exp@vect[-y d[x] + x d[y]]
Print@(vect[x d[x]])
(* Print@(a \[CenterDot] vect[x d[x]]) *)
(* Print@{exp@(a \[CenterDot] vect[d[x]]), exp@(a \[CenterDot] vect[x d[x]])} *)
Print@exp[a \[CenterDot] vect@(y d[x] - x d[y] + d[z])] (* * [Головин стр. 8] *)
sampleR[a_, b_] := vect[-b d[a] + a d[b]]
(* Print@{exp@vect[a * sampleR[x, y]], exp@vect[b * sampleR[x, y]], exp@vect[a * sampleR[x, y]] \[SmallCircle] exp@vect[b * sampleR[x, y]]} *)
Print@{a \[CenterDot] vect@(d[x])}
(* Print@{exp[a \[CenterDot] vect[d[x]]], exp[b \[CenterDot] vect[x d[x]]]} *)
(* Print@{exp@vect[a * vect@(d[x])], exp@vect[b * vect@(x d[x])]} *)
(* Print@{exp@vect[a * vect@(d[x])], exp@vect[b * vect@(x d[x])], exp@vect[a * vect@(d[x])] \[SmallCircle] exp@vect[b * vect@(x d[x])], exp@vect[b * vect@(x d[x])] \[SmallCircle] exp@vect[a * vect@(d[x])]} *)
(* ** *)

(* * samples end *)
