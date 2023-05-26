(* ::Package:: *)

<<AmpToolsM`
<<AmpToolsM`MaschkeAll`
<<AmpToolsM`BasisConstruction`


<<AmpToolsM`CKDual`


fourOneDiags = SortBy[makeFullBasis[1,4,!tadpoleQ[#]&],-Length/@minimalCycles[#]&];
fourOneDiags[[1]] = fourOneDiags[[1]]/.{2->3,3->2};
fourOneCB = makeCanonicalBasis[fourOneDiags];
graphPlot/@fourOneDiags
n1Contacts = generateCutDiagrams[fourOneDiags,1,False];
usefulTrips = findTriplet[#,fourOneCB]&/@n1Contacts[[;;3]];
loadNPointAnalytics[4];
bcjBasis = prepareBCJBasis[fourOneDiags];


numerator1 = makeZBasis[
bcjBasis[[1,1]],
\[Alpha] Product[P[l[i]] - P[l[Mod[i+1,4,5]]],{i,5,8}]
,ColorSignsQ->True];
numerator1["ans"] = numerator1["ans"]//Simplify;
numerator1Eval = convertNumToEval[numerator1];


numerator2 = makeZBasis[
bcjBasis[[1,1]],
Sum[
\[Beta] P[l[i]]*(P[l[i]] - P[l[Mod[i+1,4,5]]])
(P[l[Mod[i+1,4,5]]]-P[l[Mod[i+2,4,5]]])(P[l[Mod[i+2,4,5]]])
,{i,5,8}]
,ColorSignsQ->True];
numerator2Eval = convertNumToEval[numerator2];


numerator3 = makeZBasis[
bcjBasis[[1,1]],
\[Gamma] P[l[5]]^2 P[l[7]]^2 + P[l[6]]^2P[l[8]]^2
,ColorSignsQ->True];
numerator3Eval = convertNumToEval[numerator3];


bcjBasis1 = replaceInAns[bcjBasis,
{zNum[g_Graph,i__]:>numerator1Eval["ans"][i]}
];
bcjBasis2 = replaceInAns[bcjBasis,
{zNum[g_Graph,i__]:>numerator2Eval["ans"][i]}
];
bcjBasis3 = replaceInAns[bcjBasis,
{zNum[g_Graph,i__]:>numerator3Eval["ans"][i]}
];


n1Cuts = {collapsePropagator[fourOneDiags[[1]],7]};
n2Cuts = generateCutDiagrams[n1Cuts,1];


graphPlot/@n1Cuts
graphPlot/@n2Cuts


dressedCompareCuts[n1Cuts[[1]],bcjBasis1,bcjBasis2]
dressedCompareCuts[n1Cuts[[1]],bcjBasis1,bcjBasis3]


dressedCompareCuts[n2Cuts[[1]],bcjBasis1,bcjBasis2]//assocToRat//Simplify
dressedCompareCuts[n2Cuts[[1]],bcjBasis1,bcjBasis3]//assocToRat//Simplify



