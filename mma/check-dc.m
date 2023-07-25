(* ::Package:: *)

<<AmpToolsM`
<<AmpToolsM`MaschkeAll`
<<AmpToolsM`BasisConstruction`


<<AmpToolsM`CKDual`


<<AmpToolsM`Integrands`


(* ::Section:: *)
(*Prep various Pion reps*)


(* ::Subsection:: *)
(*Actual Prep*)


(* ::Subsubsection:: *)
(*Diag Basis*)


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


(* ::Subsubsection:: *)
(*Initial load from James*)


jamesAnsatzSol = Get["MatchToZM/sol.wl"]//Dispatch;


jamesDBGraph = Get["MatchToZM/DoubleBoxGraph.wl"]/.p->Identity/.VerF->List/.VerGraph->Identity;
jamesDBToMe = isoMomRule[jamesDBGraph,bcjBasis[[1,1]]];


(*jamesDBNumer = (Get["FishyAnswer/DoubleBoxNumerator.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]});
jamesDBNumerMyLabels = jamesDBToMe[[1]] * jamesDBNumer/.jamesDBToMe[[2]];*)


jamesDBNumer = (Get["MatchToZM/DoubleBoxNumeratorAnsatz.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]})/.jamesAnsatzSol/.c[_][_]:>0/.c0->1;
jamesDBNumerMyLabels = jamesDBToMe[[1]] * jamesDBNumer/.jamesDBToMe[[2]];


jamesPTGraph = Get["MatchToZM/PentaTriangleGraph.wl"]/.p->Identity/.VerF->List/.VerGraph->Identity;
jamesPTToMe = isoMomRule[jamesPTGraph,bcjBasis[[2,1]]]


(*jamesPTNumer = (Get["FishyAnswer/PentaTriangleNumerator.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]});
jamesPTNumerMyLabels = jamesPTToMe[[1]] * jamesPTNumer/.jamesPTToMe[[2]];*)


jamesPTNumer = (Get["MatchToZM/PentaTriangleNumeratorAnsatz.wl"]/.{p[i_]/;i<=4:>k[i],p[i_]/;i>4:>l[i]})/.jamesAnsatzSol/.c[_][_]:>0/.c0->1;
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


(* ::Subsection:: *)
(*Construct the cut truth*)


realCuts = {collapsePropagator[bcjBasis[[1,1]],{7,10,11}],
collapsePropagator[bcjBasis[[1,1]],{8,5,10}]};
graphPlot/@realCuts


(* ::Subsubsection:: *)
(*Pions Directly*)


<<"data-files/NLSMAmplitudes.m";


getk[realCuts[[1]]]


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


(* ::Subsubsection:: *)
(*From Nic*)


nicDoubleBubble =Join[ -(List/@Range[4]),
	{Atree[l[4],k[1],k[2],l[3]],Atree[-l[4],-l[1],-l[2],-l[3]],Atree[l[2],k[3],k[4],l[1]]}/.{l[i_]:>i+4,k[i_]:>i}/.Atree->List];
graphPlot@nicDoubleBubble


nicOstrich = Join[ -(List/@Range[4]),{Atree[l[1],k[3],k[4],l[2]],Atree[k[2],l[4],-l[3],-l[1]],Atree[k[1],-l[4],l[3],-l[2]]}/.{l[i_]:>i+4,k[i_]:>i}/.Atree->List];
graphPlot@nicOstrich


Get["evenPointCuts.m"];


sGalOstCut = makeZBasis[realCuts[[2]],
	sGalBIOstrich/.l[i_]:>l[i+4]/.blp->d/.momConsGraph[nicOstrich]/.isoMomRule[nicOstrich,realCuts[[2]]][[2]]
,ColorSignsQ->False];
sGalOstCut["ans"] = Simplify[sGalOstCut["ans"]/.P[x__]:>0];


sGalDBCut = makeZBasis[realCuts[[1]],
	sGalDoubleBubble/.l[i_]:>l[i+4]/.blp->d/.momConsGraph[nicDoubleBubble]/.isoMomRule[nicDoubleBubble,realCuts[[1]]][[2]]
,ColorSignsQ->False];
sGalDBCut["ans"] = Simplify[sGalDBCut["ans"]/.P[x__]:>0];


n4DBIVAOstCut = makeZBasis[realCuts[[2]],
	N4DBIVAOstrich/.l[i_]:>l[i+4]/.blp->d/.d8[_]:>1/.momConsGraph[nicOstrich]/.isoMomRule[nicOstrich,realCuts[[2]]][[2]]
,ColorSignsQ->False];
n4DBIVAOstCut["ans"] = Simplify[n4DBIVAOstCut["ans"]/.P[x__]:>0];


n4DBIVADBCut = makeZBasis[realCuts[[1]],
	N4DBIVADoubleBubble/.l[i_]:>l[i+4]/.blp->d/.d8[_]:>1/.momConsGraph[nicDoubleBubble]/.isoMomRule[nicDoubleBubble,realCuts[[1]]][[2]]
,ColorSignsQ->False];
n4DBIVADBCut["ans"] = Simplify[n4DBIVADBCut["ans"]/.P[x__]:>0];





biOstCut = makeZBasis[realCuts[[2]],
	BIOstrich/.l[i_]:>l[i+4]/.blp->d/.d8[_]:>1/.momConsGraph[nicOstrich]/.isoMomRule[nicOstrich,realCuts[[2]]][[2]]
,ColorSignsQ->False,
Polarizations->True];
biOstCut["ans"] = Simplify[biOstCut["ans"]/.P[x__]:>0];


biDBCut = makeZBasis[realCuts[[1]],
	BIDoubleBubble/.l[i_]:>l[i+4]/.blp->d/.d8[_]:>1/.momConsGraph[nicDoubleBubble]/.isoMomRule[nicDoubleBubble,realCuts[[1]]][[2]]
,ColorSignsQ->False,
Polarizations->True];
biDBCut["ans"] = Simplify[biDBCut["ans"]/.P[x__]:>0];


(* ::Subsection:: *)
(*Double copy*)


(* ::Subsubsection::Closed:: *)
(*Prep N=4*)


{twoCount,twoDiags,twoNumers} = loadLoopIntegrands[2];
twoNumers = twoNumers["BCJ"];

susyYMBasis = newBasis[Values[bcjBasis[[{1,4},1]]],
MapThread[
Function[{diag,numer},

makeZBasis[bcjBasis[[#[[1]],1]],
#[[2]]*(numer/.#[[3]])
,ColorSignsQ->True]&@isoMomFromParents[diag,fourTwoCB]

]
,{twoDiags,twoNumers}],
ColorSignsQ->True];


(* ::Subsubsection::Closed:: *)
(*Prep pure YM*)


Get["bdn-two-ym-numerators.m"];
bdnGraph = vertices;
bdnNumerators = numerators/.{ee[i_,j_]:>d[e[i],e[j]],ke[i_,j_]:>d[If[i>4,l[i],k[i]],e[j]],kk[i_,j_]:>d[If[i>4,l[i],k[i]],If[j>4,l[j],k[j]]]   };


pureYMBasis = newBasis[##,ColorSignsQ->True,Polarizations->True]&@@Transpose@
MapThread[
Function[{diag,numer},

{bcjBasis[[#[[1]],1]],makeZBasis[bcjBasis[[#[[1]],1]],
#[[2]]*(numer/.#[[3]])
,ColorSignsQ->True,Polarizations->True]}&@isoMomFromParents[diag,fourTwoCB]

]
,{bdnGraph,bdnNumerators}];


(* ::Subsubsection:: *)
(*Product reps and cut checks*)


sGalDC = sqrAns[jamesBCJ];


dbivaDC = prodAns[susyYMBasis,jamesBCJ];


biDC = prodAns[jamesBCJ,pureYMBasis];


dbivaDCDBCut = gravityCompareCuts[realCuts[[1]],dbivaDC,<||>];
dbivaDCOstCut = gravityCompareCuts[realCuts[[2]],dbivaDC,<||>];


dbivaDCDBCut["local"]//Simplify
n4DBIVADBCut["ans"]


dbivaDCOstCut["local"]//Simplify
n4DBIVAOstCut["ans"]


sgalDCDBCut = gravityCompareCuts[realCuts[[1]],sGalDC,<||>];
sgalDCOstCut = gravityCompareCuts[realCuts[[2]],sGalDC,<||>];


sgalDCDBCut//assocToRat//Simplify
sGalDBCut["ans"]


sgalDCOstCut//assocToRat//Simplify
sGalOstCut["ans"]


biDCDBCut = gravityCompareCuts[realCuts[[1]],biDC,<||>];
biDCOstCut = gravityCompareCuts[realCuts[[2]],biDC,<||>];


assocToRat[biDCDBCut]/biDBCut["ans"]//Simplify


assocToRat[biDCOstCut]/biOstCut["ans"]//Simplify
