(* ::Package:: *)

<<AmpToolsM`
<<AmpToolsM`MaschkeAll`
<<AmpToolsM`BasisConstruction`


<<AmpToolsM`CKDual`


(* ::Section:: *)
(*Prep various Pion reps*)


fourTwoDiags = SortBy[makeFullBasis[2,4,!tadpoleQ[#]&],{cutLevel[#]&,!planarQ[#]&,-Length/@minimalCycles[#]&}];


graphPlot/@fourTwoDiags


fourTwoCB = makeCanonicalBasis[fourTwoDiags];


loadNPointAnalytics[4];
{bcjBasis,{unusedJ}} = Reap[prepareBCJBasis[fourTwoDiags],UNUSEDJACOBIS];


n1Cuts = generateCutDiagrams[fourTwoDiags,1];
n2Cuts = generateCutDiagrams[n1Cuts,1];


bcjBasis[[1;;2,1]]


proposedDB = makeZBasis[bcjBasis[[1,1]],
Times@@(P[l[#1]] - P[l[#2]]&@@@NestList[RotateLeft,{11,8,6,10,9,5},5])
-P[l[10]]^2Times@@(P[l[#1]] - P[l[#2]]&@@@NestList[RotateLeft,{11,8,7,5},3])
-P[l[11]]^2Times@@(P[l[#1]] - P[l[#2]]&@@@NestList[RotateLeft,{7,6,10,9},3])
+ P[l[11]]^2 P[l[7]]^2 P[l[10]]^2
,ColorSignsQ->True
];
proposedPT = makeZBasis[bcjBasis[[2,1]]


]
