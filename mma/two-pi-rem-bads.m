(* ::Package:: *)

<<AmpToolsM`
<<AmpToolsM`MaschkeAll`
<<AmpToolsM`BasisConstruction`


<<AmpToolsM`CKDual`


(* ::Section:: *)
(*Prep various Pion reps*)


(* ::Subsection::Closed:: *)
(*Actual Prep*)


fourTwoDiags = SortBy[makeFullBasis[2,4,!tadpoleQ[#]&],{cutLevel[#]&,!planarQ[#]&,-Length/@minimalCycles[#]&}];


fourTwoCB = makeCanonicalBasis[fourTwoDiags];


loadNPointAnalytics[4];
{bcjBasis,{unusedJ}} = Reap[prepareBCJBasis[fourTwoDiags],UNUSEDJACOBIS];


(*{bcjBasisGen,{unusedJ}} = Reap[prepareBCJBasisSuperPos[fourTwoDiags],UNUSEDJACOBIS];*)


n1Cuts = Select[generateCutDiagrams[fourTwoDiags,1],!tadpoleQ[#]&&idDangTrees[#]=={}&];
n2Cuts = generateCutDiagrams[n1Cuts,1];


(*makeISPans[gn_Integer,graph_List]:=Block[
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
];*)


(* ::Subsection:: *)
(*Load James's data*)


(* ::Subsubsection:: *)
(*Initial load*)


jamesAnsatzSol = Get["MatchToZM/sol.wl"]//Dispatch;


jamesDBGraph = Get["MatchToZM/DoubleBoxGraph.wl"]/.p->Identity/.VerF->List/.VerGraph->Identity;
jamesDBToMe = isoMomRule[jamesDBGraph,bcjBasis[[1,1]]];


(*jamesDBNumer = (Get["FishyAnswer/DoubleBoxNumerator.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]});
jamesDBNumerMyLabels = jamesDBToMe[[1]] * jamesDBNumer/.jamesDBToMe[[2]];*)


jamesDBNumer = (Get["MatchToZM/DoubleBoxNumeratorAnsatz.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]})/.jamesAnsatzSol;
jamesDBNumerMyLabels = jamesDBToMe[[1]] * jamesDBNumer/.jamesDBToMe[[2]];


jamesPTGraph = Get["MatchToZM/PentaTriangleGraph.wl"]/.p->Identity/.VerF->List/.VerGraph->Identity;
jamesPTToMe = isoMomRule[jamesPTGraph,bcjBasis[[2,1]]]


(*jamesPTNumer = (Get["FishyAnswer/PentaTriangleNumerator.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]});
jamesPTNumerMyLabels = jamesPTToMe[[1]] * jamesPTNumer/.jamesPTToMe[[2]];*)


jamesPTNumer = (Get["MatchToZM/PentaTriangleNumeratorAnsatz.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]})/.jamesAnsatzSol;
jamesPTNumerMyLabels = jamesPTToMe[[1]] * jamesPTNumer/.jamesPTToMe[[2]];


fromJamesDB = makeZBasis[bcjBasis[[1,1]],
jamesDBNumerMyLabels,
ColorSignsQ->True
];
fromJamesPT = makeZBasis[bcjBasis[[2,1]],
jamesPTNumerMyLabels,
ColorSignsQ->True
];


jamesRawBasis = newBasis[{bcjBasis[[1,1]],bcjBasis[[2,1]]},{fromJamesDB,fromJamesPT},ColorSignsQ->True];


jamesEval = convertToEvalBasis@jamesRawBasis;


jamesBCJ = replaceInAns[bcjBasis,
{zNum[g_Graph,i__]:>evalZNums[jamesEval][zNum[g,i]]}
];


(* ::Subsubsection:: *)
(*Symmetries*)


Expand/@checkSymGeneric@@@jamesRawBasis


jamesSafe = Select[jamesBCJ,!zeroPropQ[#[[1]]]&];


PossibleZeroQ/@checkSymGeneric@@@jamesSafe


safeTwoDiagsBasis = makeCanonicalBasis[Select[fourTwoDiags,!zeroPropQ[#]&]];


shouldBeSafeJacs = Select[unusedJ[[1]],Count[findTriplet[#,safeTwoDiagsBasis],0,Infinity]===0&];


PossibleZeroQ[maschkeJacobi[#,bcjBasis]//evalZNums[jamesEval]]&/@shouldBeSafeJacs


PossibleZeroQ[maschkeJacobi[#,jamesBCJ]]&/@shouldBeSafeJacs


(* ::Subsection:: *)
(*Fish out Cubic BELs*)


belAndGenTads = Select[jamesBCJ,zeroPropQ[#[[1]]]&];


reallyBadAns = Values@belAndGenTads[[-6;;,2,"ans"]];


zeroReallyBadEqs = coefEqs[#,{Z,P}]&/@reallyBadAns;


Do[ Put[zeroReallyBadEqs[[i]],"remove_tadpoles_eqs_"<>ToString[i]<>".gen"]  ,{i,Length[zeroReallyBadEqs]}]


Clear[zeroReallyBadEqs]


tadpoleEqFiles = FileNames["remove_tadpoles_eqs_*"];


Do[
Print[i];
theSol = spasmSolveNP[Get[tadpoleEqFiles[[i]]]/.{c0->a[1000,0],c[2][i_]:>a[2,i],c[1][i_]:>a[1,i]}];
Put[theSol,"remove_tadpoles_sol_"<>ToString[i]<>".m"];
Clear[theSol];
,{i,Length[tadpoleEqFiles]}]


tadpoleSolFiles = FileNames["remove_tadpoles_sol_*"];
allTadpoleSols = Flatten[Get/@tadpoleSolFiles]/.Rule->Subtract;
reallyBadSol = spasmSolveNP[allTadpoleSols/.{c0->a[1000,0],c[2][i_]:>a[2,i],c[1][i_]:>a[1,i]}];
Put[reallyBadSol,"remove_all_tadpoles.gen"];


moderatelyBadEqs = coefEqs[#,{Z,P}]&/@(Values@belAndGenTads[[;;-7,2,"ans"]]);
Do[ Put[moderatelyBadEqs[[i]],"remove_single_bel_eqs_"<>ToString[i]<>".gen"]  ,{i,Length[moderatelyBadEqs]}]


belEqFiles = FileNames["remove_single_bel_eqs_*"];
Do[
Print[i];
theSol = spasmSolveNP[Get[belEqFiles[[i]]]/.{c0->a[1000,0],c[2][i_]:>a[2,i],c[1][i_]:>a[1,i]}];
Put[theSol,"remove_bel_sol_"<>ToString[i]<>".m"];
Clear[theSol];
,{i,Length[belEqFiles]}]


belSolFiles = FileNames["remove_bel_sol_*"];
allBELSols = Flatten[Get/@belSolFiles]/.Rule->Subtract;
allBELSol = spasmSolveNP[allBELSols/.{c0->a[1000,0],c[2][i_]:>a[2,i],c[1][i_]:>a[1,i]}];
Put[allBELSol,"remove_all_bels.gen"];
