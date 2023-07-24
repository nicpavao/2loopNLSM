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


n1Cuts = Select[generateCutDiagrams[fourTwoDiags,1],!tadpoleQ[#]&&idDangTrees[#]=={}&];
n2Cuts = generateCutDiagrams[n1Cuts,1];


graphPlot/@bcjBasis[[1;;2,1]]


makeISPans[gn_Integer,graph_List]:=Block[
	{extK = getk[graph]},
	Array[a[gn,#]&,Length[#]] . #&@Select[DeleteDuplicates[Flatten[Outer[Times
	,Sequence@@((Join[P/@l/@Complement[#,extK],{Z[3],Z[4]}])&/@Abs[Select[graph,Length[#]>1&]])]]],And@@(NonNegative/@({2,2}-Exponent[#,{Z[3],Z[4]}]))&]
]


proposedDB = makeZBasis[bcjBasis[[1,1]],
makeISPans[1,bcjBasis[[1,1]]]
,ColorSignsQ->True
];


proposedPT = makeZBasis[bcjBasis[[2,1]],
makeISPans[2,bcjBasis[[2,1]]]
,ColorSignsQ->True
];


(*proposedDB = makeZBasis[bcjBasis[[1,1]],
 (\[Omega][1](Times@@(P[l[#1]] - P[l[#2]]&@@@NestList[RotateLeft,{11,8,6,10,9,5},5]))
-\[Omega][2](P[l[5]] - P[l[11]])(P[l[11]] - P[l[8]])(P[l[8]] + P[l[5]]-P[l[7]])P[l[10]]^2 P[l[7]]
-\[Omega][3](P[l[6]] - P[l[10]])(P[l[10]] - P[l[9]])(P[l[6]] + P[l[9]]-P[l[7]])P[l[11]]^2 P[l[7]]
+ \[Omega][4]P[l[11]]^2 P[l[7]]^2 P[l[10]]^2)
,ColorSignsQ->True
];*)


(*proposedPT = makeZBasis[bcjBasis[[2,1]],
(\[Alpha] (Times@@(P[l[#1]] - P[l[#2]]&@@@NestList[RotateLeft,{10,8,6,9,5,11},5]))
+\[Beta] P[l[10]]P[l[11]]P[l[7]](P[l[10]]-P[l[11]])(P[l[6]]-P[l[9]])(P[l[6]]+P[l[9]]-P[l[7]])

)
,ColorSignsQ->True
];*)


(*proposedPT = makeZBasis[bcjBasis[[2,1]],
(\[Alpha] (Times@@(P[l[#1]] - P[l[#2]]&@@@NestList[RotateLeft,{10,8,6,9,5,11},5]))
+ \[Beta] (P[l[10]])P[l[6]]P[l[7]](P[l[5]]-P[l[11]])(P[l[11]] - P[l[10]])(P[l[6]] + P[l[5]] - P[l[7]])
+ \[Delta] P[l[11]]P[l[9]]P[l[7]](P[l[11]]-P[l[10]])(P[l[10]]-P[l[8]])(P[l[8]]+P[l[9]] - P[l[7]])
)
,ColorSignsQ->True
];*)


evalBasis = convertToEvalBasis@newBasis[{bcjBasis[[1,1]],bcjBasis[[2,1]]},{proposedDB,proposedPT},ColorSignsQ->True];


bcjBasis1 = replaceInAns[bcjBasis,
{zNum[g_Graph,i__]:>evalZNums[evalBasis][zNum[g,i]]}
];


(*bcjBasisSP = replaceInAns[bcjBasisGen,
{zNum[g_Graph,i__]:>evalZNums[evalBasis][zNum[g,i]]}
];*)


(* ::Subsection:: *)
(*Construct the cut truth*)


<<"data-files/NLSMAmplitudes.m";


realCuts = {collapsePropagator[bcjBasis[[1,1]],{7,10,11}],
collapsePropagator[bcjBasis[[1,1]],{8,5,10}]};
graphPlot/@realCuts


makePiCut[diag_List]:=Block[
{p},
	p[x_]/;x<0:=-p[Abs@x];
	p[x_]/;MemberQ[getk[diag],Abs[x]]:=k[x];
	p[x_]/;!MemberQ[getk[diag],Abs[x]]:=l[x];

	actVerts = Select[diag,Length[#]>2&];
	
	If[Or@@(OddQ/@Length/@actVerts),Return[0]];
	
	 Collect[Expand[makeZBasis[diag,
	Product[
	
		Sum[
			DDM[Abs@ord] NLSM[p/@ord],
		{ord,{hv[[1]],##,hv[[-1]]}&@@@Permutations[hv[[2;;-2]]]}]
	
	,{hv,actVerts}],ColorSignsQ->True]["ans"]/.P[x__]:>0],_DDM]


]


piCutData = a[1000,0]Simplify[makePiCut/@realCuts];


myPiCuts = assocToRat[dressedCompareCuts[#,bcjBasis1,<||>]]&/@realCuts;


cutCheck = myPiCuts - piCutData;


cutSol2 = spasmSolve@coefEqs[Numerator[Together[cutCheck[[2]]]],{Z,DDM}];


Put[cutSol2,"cutSol2.gen"]


cutSol1 = spasmSolve@coefEqs[Numerator[Together[cutCheck[[1]]]],{Z,DDM}];


Put[cutSol1,"cutSol1.gen"]
