(* ::Package:: *)

<<AmpToolsM`RecycleCuts`
<<AmpToolsM`Integrands`
<<AmpToolsM`MaschkeAll`
<<AmpToolsM`SingularInterface`
<<AmpToolsM`IsecIdeals`


<<AmpToolsM`BasisConstruction`
<<AmpToolsM`CKDual`


<<AmpToolsM`Grassmania`


<<AmpToolsM`FourDNumerics`


loadNPointAnalytics[4];


(* ::Section::Closed:: *)
(*Preps and defs for 4D comparisons*)


{Lam,LamT} = generateExtNumerics[4]


(* ::Section:: *)
(*Build the two-loop rep -- Similar setup to explorations of N=2/1*)


(* ::Subsection:: *)
(*Setup*)


fourTwoDiags = SortBy[makeFullBasis[2,4,!tadpoleQ[#]&],{cutLevel[#]&,!planarQ[#]&,-Length/@minimalCycles[#]&}];


graphPlot/@fourTwoDiags


twoLbcjBasis = prepareBCJBasis[fourTwoDiags,WithE->True];


Length/@Expand/@twoLbcjBasis[[All,2,"ans"]];


mcDiags = Select[fourTwoDiags,idDangTrees[#]==={}&];
graphPlot/@mcDiags


makeAnsatzViaDioph[diag_List,totalDeg_Integer,pcData_List,maxTotalPC_Integer,desiredPols_List]:=Block[
	{polQ = desiredPols!={},loopMom = pcData[[All,2]],polWeights,v},
	theCutBasis = makeZBasis[diag,0,ColorSignsQ->True,Polarizations->polQ]["ZtoD"];
	baseVars = theCutBasis[[All,1]];
	loopMom = pcData[[All,2]];
	If[polQ,polWeights = Exponent[#,e/@Range[4]]&/@
	(baseVars/.{EP[i_,j_]:>e[i]EP[i,j],EE[i_,j_]:>EE[i,j]e[i]e[j]})];
	
	loopWeights = Boole[#>0]&/@Exponent[#,\[Alpha]@@@loopMom]&/@(theCutBasis[[All,2]]/.l[i_]:>\[Alpha][i]l[i]);
	
	conditions = Join[Thread[#>=0],{Total[#]==totalDeg},
		If[polQ,Thread[Transpose[polWeights] . #=={1,1,1,1}],Nothing],
		Thread[Transpose[loopWeights] . #<=pcData[[All,1]]],
		{Total[Transpose[loopWeights] . #]<=maxTotalPC}]&;
	
	allExps = Dispatch/@{ToRules@Reduce[conditions[(v/@Range[Length[baseVars]])],(v/@Range[Length[baseVars]]),Integers]};
	
	IdealAns@(Times@@(baseVars^(v/@Range[Length[baseVars]]))/.allExps)
	
]


makeContAnsatzViaDioph[diag_List,totalDeg_Integer,pcData_List,maxTotalPC_Integer,desiredPols_List]:=Block[
	{polQ = desiredPols!={},loopMom = pcData[[All,2]],polWeights,v},
	theCutBasis = makeZBasis[diag,0,ColorSignsQ->True,Polarizations->polQ]["ZtoD"];
	baseVars = theCutBasis[[All,1]];
	loopMom = pcData[[All,2]];
	If[polQ,polWeights = Exponent[#,e/@Range[4]]&/@
	(baseVars/.{EP[i_,j_]:>e[i]EP[i,j],EE[i_,j_]:>EE[i,j]e[i]e[j]})];
	
	loopWeights = Boole[#>0]&/@Exponent[#,\[Alpha]@@@loopMom]&/@(theCutBasis[[All,2]]/.l[i_]:>\[Alpha][i]l[i])/.\[Alpha][i_]^2:>\[Alpha][i];
	
	propWeights = Boole[Head[#]===P]&/@baseVars;
	
	conditions = Join[Thread[#>=0],{Total[#]==totalDeg},
		If[polQ,Thread[Transpose[polWeights] . #=={1,1,1,1}],Nothing],
		Thread[Transpose[loopWeights] . #<=pcData[[All,1]]],
		{propWeights . #>=1},
		{Total[Transpose[loopWeights] . #]<=maxTotalPC}]&;
	
	allExps = Dispatch/@{ToRules@Reduce[conditions[(v/@Range[Length[baseVars]])],(v/@Range[Length[baseVars]]),Integers]};
	
	IdealAns@(Times@@(baseVars^(v/@Range[Length[baseVars]]))/.allExps)
	
]


makeMCAnsatzViaDioph[diag_List,totalDeg_Integer,pcData_List,maxTotalPC_Integer,desiredPols_List]:=Block[
	{polQ = desiredPols!={},loopMom = pcData[[All,2]],polWeights,v},
	theCutBasis = DeleteCases[makeZBasis[diag,0,ColorSignsQ->True,Polarizations->polQ]["ZtoD"],Rule[_P,_]];
	baseVars = theCutBasis[[All,1]];
	loopMom = pcData[[All,2]];
	If[polQ,polWeights = Exponent[#,e/@Range[4]]&/@
	(baseVars/.{EP[i_,j_]:>e[i]EP[i,j],EE[i_,j_]:>EE[i,j]e[i]e[j]})];
	
	loopWeights = (Exponent[#,\[Alpha]@@@loopMom]&/@(theCutBasis[[All,2]]/.l[i_]:>\[Alpha][i]l[i]));
	
	conditions = Join[Thread[#>=0],{Total[#]==totalDeg},
		If[polQ,Thread[Transpose[polWeights] . #=={1,1,1,1}],Nothing],
		Thread[Transpose[loopWeights] . #<=pcData[[All,1]]],
		{Total[Transpose[loopWeights] . #]<=maxTotalPC}]&;
	
	allExps = Dispatch/@{ToRules@Reduce[conditions[(v/@Range[Length[baseVars]])],(v/@Range[Length[baseVars]]),Integers]};
	
	IdealAns@(Times@@(baseVars^(v/@Range[Length[baseVars]]))/.allExps)
	
]


imposeGI[diag_,theAns_/;Head[theAns]=!=IdealAns]:=Block[
	{giSol,giAns},
		giSol = spasmSolveNP[coefEqs[
	Table[
		theAns/.makeZBasis[diag,0,Polarizations->True]["ZtoD"]/.e[i]->k[i]/.k[4]->-k[1]-k[2]-k[3]
		/.makeZBasis[diag,0,Polarizations->True]["DtoZ"]/.P[x__]:>0,
	{i,1,4}]//Flatten,
	{Z,EP,EE,DDM}]]//Dispatch;
	Sow[giSol,GISOL];
	theAns/.giSol
]


imposeSym[diag_,theAns_/;Head[theAns]=!=IdealAns]:=Block[
	{giSol,giAns,symSol},
	symSol = Dispatch@spasmSolveNP[coefEqs[checkSymGeneric[diag,makeZBasis[diag,theAns,ColorSignsQ->True,Polarizations->True]],{Z,EE,EP,P,DDM}]];
	Sow[symSol];
	theAns/.symSol
]


imposeGIandSym[diag_,theAns_/;Head[theAns]=!=IdealAns]:=Block[
	{giSol,giAns,symSol,symAns},
	{giAns,{giSol}} = Reap@imposeGI[diag,theAns];
	{symAns,{symSol}} = Reap@imposeSym[diag,giAns];
	
	Sow[Join[Normal[giSol]/.symSol,symSol]//Dispatch];
	symAns
(*	
	giSol = spasmSolveNP[coefEqs[
	Table[
		theAns/.makeZBasis[diag,0,Polarizations->True]["ZtoD"]/.e[i]->k[i]/.k[4]->-k[1]-k[2]-k[3]
		/.makeZBasis[diag,0,Polarizations->True]["DtoZ"]/.P[x__]:>0,
	{i,1,4}]//Flatten,
	{Z,EP,EE}]]//Dispatch;
	giAns = theAns/.giSol;
	symSol = Dispatch@spasmSolveNP[coefEqs[checkSymGeneric[diag,makeZBasis[diag,giAns,ColorSignsQ->True,Polarizations->True]],{Z,EE,EP,P}]];
	Sow[symSol];
	giAns/.symSol	*)
]


convertToIdeal[theAns_]:=IdealAns@DeleteCases[CoefficientArrays[theAns,findVars[theAns,{a}]][[-1]]["NonzeroValues"],0]


findGIandSymIdeal[diag_,theAns_IdealAns]:=Block[
	{giSymAns},
	giSymAns = imposeGIandSym[diag,(Array[a[1,#]&,Length[#]] . #&@@theAns)];
	IdealAns@DeleteCases[CoefficientArrays[giSymAns,findVars[giSymAns,{a}]][[-1]]["NonzeroValues"],0]
	
]


(*findGIandSymIdeal[diag_,theAns_IdealAns]:=Block[
	{giSol,giAns,symSol,giSymAns},
	giSol = spasmSolveNP[coefEqs[
	Table[
		(Array[a[1,#]&,Length[#]] . #&@@theAns)/.makeZBasis[diag,0,Polarizations->True]["ZtoD"]/.e[i]->k[i]/.k[4]->-k[1]-k[2]-k[3]
		/.makeZBasis[diag,0,Polarizations->True]["DtoZ"]/.P[x__]:>0,
	{i,1,4}]//Flatten,
	{Z,EP,EE}]]//Dispatch;
	giAns = (Array[a[1,#]&,Length[#]] . #&@@theAns)/.giSol;
	symSol = Dispatch@spasmSolveNP[coefEqs[checkSymGeneric[diag,makeZBasis[diag,giAns,ColorSignsQ->True,Polarizations->True]],{Z,EE,EP,P}]];
	giSymAns = giAns/.symSol;
	IdealAns@DeleteCases[CoefficientArrays[giSymAns,findVars[giSymAns,{a}]][[-1]]["NonzeroValues"],0]
	
]*)


mcNumers = {0,0,0,0};
mcNumersV = {0,0,0,0};
mcNumersH = {0,0,0,0};


(* ::Subsection:: *)
(*Truth from Bern Davies Nohle [1510.03448]*)


Get["bdn-two-ym-numerators.m"];
bdnGraph = vertices;
bdnNumerators = numerators/.{ee[i_,j_]:>d[e[i],e[j]],ke[i_,j_]:>d[If[i>4,l[i],k[i]],e[j]],kk[i_,j_]:>d[If[i>4,l[i],k[i]],If[j>4,l[j],k[j]]]   };


bdnNumeratorsSimp = Cancel/@(bdnNumerators/I/.Ds->4);


bdnBasis = newBasis[bdnGraph,a[1000,0]bdnNumeratorsSimp,ColorSignsQ->True,Polarizations->True];


(* ::Subsection:: *)
(*Construct CK basis graphs*)


(*pc = {{8,l[5]},{8,l[6]}};*)
pcMax = 16;
(*This is more-or-less equivalent to what BDN used*)
(*pc = Association[#->powerCountOwnBase[mcDiags[[#]],0]&/@Range[2]]*)
(*A more-lenient power counting choice*)
pc = Association[#->powerCountOwnBase[mcDiags[[#]],-5]&/@Range[2]]


AbsoluteTiming[contAns = makeContAnsatzViaDioph[mcDiags[[1]],6,pc[1],pcMax,{1,1,1,1}];
mcAns = makeMCAnsatzViaDioph[mcDiags[[1]],6,pc[1],pcMax,{1,1,1,1}];
(Length@@contAns) + (Length@@mcAns)]


DeleteCases[(Identity@@contAns)/.{Z[1]->0,Z[2]->0},0]//Length


Dynamic[diagNum]
ckBasisAnsData = Table[
{mcDiags[[diagNum]],
contAns = makeContAnsatzViaDioph[mcDiags[[diagNum]],5,pc[diagNum],pcMax,{1,1,1,1}];
mcAns = makeMCAnsatzViaDioph[mcDiags[[diagNum]],5,pc[diagNum],pcMax,{1,1,1,1}];
Print[(Length@@contAns) + (Length@@mcAns)];
giIdealMC = findGIandSymIdeal[mcDiags[[diagNum]],mcAns];
giIdealCont = findGIandSymIdeal[mcDiags[[diagNum]],contAns];
makeZBasis[mcDiags[[diagNum]],
Array[a[diagNum,#]&,Length[#]] . #&@Join[Identity@@giIdealMC,Identity@@giIdealCont]
,ColorSignsQ->True,Polarizations->True]
}
,{diagNum,{1,2}}];


ckBasis = newBasis[ckBasisAnsData[[All,1]],ckBasisAnsData[[All,2]],ColorSignsQ->True,Polarizations->True];
ckBasisEval = convertToEvalBasis@ckBasis;
ckBasisFull = replaceInAns[twoLbcjBasis,
{zNum[g_Graph,i__]:>evalZNums[ckBasisEval][zNum[g,i]]}
];


(* ::Subsection:: *)
(*Start checking cuts against BDN*)


(* ::Subsubsection:: *)
(*Max Cuts*)


notDangerousDiags = Select[twoLbcjBasis,!zeroPropQ[#[[1]]](*&&!dangTreeQ[#[[1]]]*)&];
graphPlot/@Values[notDangerousDiags[[All,1]]]


allMaxCuts = dressedCompareCuts[#,ckBasisFull,bdnBasis]["local"]&/@Values[notDangerousDiags[[All,1]]];


maxCutSols = spasmSolveNP[coefEqs[allMaxCuts,{Z,EP,EE}]];


ckBasisMC = replaceInAns[ckBasisFull,maxCutSols];


(* ::Subsubsection:: *)
(*N1MC*)


conservativeN1MC = Select[generateCutDiagrams[notDangerousDiags[[All,1]]//Values,1],!tadpoleQ[#]
&& And@@(!zeroPropQ[#]&/@blowUpGraph[#])
&&
(*Throw out graphs where the contact is not a multiProp but
	one of the parents is*)
!((!multiPropQ[#])&&Or@@(multiPropQ[#]&/@blowUpGraph[#]))&
];
graphPlot/@conservativeN1MC


n1MC = Select[generateCutDiagrams[notDangerousDiags[[All,1]]//Values,1,False],!tadpoleQ[#]&& And@@(!zeroPropQ[#]&/@blowUpGraph[#])&];
graphPlot/@n1MC


allN1MCEvals = assocTogetherNum[dressedCompareCuts[#,ckBasisMC,bdnBasis]]&/@conservativeN1MC;
allN1MCEqs = coefEqs[#,{Z,EP,EE,DDM}]&/@allN1MCEvals;


And@@(Head[#]===a&/@Variables[allN1MCEqs])


n1mcJointSol = spasmSolveNP[Flatten[allN1MCEqs]];


ckBasisN1C = replaceInAns[ckBasisMC,n1mcJointSol];


(*allN1MCSols = spasmSolveNP/@allN1MCEqs;
solPairs = Subsets[allN1MCSols,{2}];
solPairsResol = spasmSolveNP[Flatten[#]/.Rule->Subtract]&/@solPairs;
Length/@allN1MCSols*)


(* ::Subsubsection:: *)
(*N2MC*)


conservativeN2MC = Select[generateCutDiagrams[conservativeN1MC,1,False],!tadpoleQ[#]
&& And@@(!zeroPropQ[#]&/@blowUpGraph[#])
(*&&
(*Throw out graphs where the contact is not a multiProp but
	one of the parents is*)
!((!multiPropQ[#])&&Or@@(multiPropQ[#]&/@blowUpGraph[#]))*)
&
];
graphPlot/@conservativeN2MC


graphPlot/@(conservativeN2MC = conservativeN2MC[[{1,2,3,4,6,7,10}]])


allN2Eqs = Table[
theN2Eqs = coefEqs[assocTogetherNum[dressedCompareCuts[conservativeN2MC[[i]],ckBasisN1C,bdnBasis]],{Z,EP,EE,DDM}];
Put[theN2Eqs,"n2_eqs_"<>ToString[i]<>".gen"];
Print[i];
theN2Eqs
,{i,{1,2,4,5,6,7}}];


FileNames["n2_eqs_*.gen"]


allFoundN2Eqs = Get/@FileNames["n2_eqs_*.gen"];


n2mcSepSols = spasmSolveNP/@allFoundN2Eqs;


Length/@n2mcSepSols


n2mcJointSol = spasmSolveNP[Flatten[allFoundN2Eqs[[;;-2]]]];


ckBasisN2C = replaceInAns[ckBasisN1C,n2mcJointSol];


(* ::Subsubsection:: *)
(*N3 -- Mostly spanning cuts*)


graphPlot/@(conservativeN3MC = generateCutDiagrams[conservativeN2MC,1][[{2,4,8}]])


allN3Eqs = Table[
theN3Eqs = coefEqs[assocTogetherNum[dressedCompareCuts[conservativeN3MC[[i]],ckBasisN2C,bdnBasis]],{Z,EP,EE,DDM}];
Put[theN3Eqs,"n3_eqs_"<>ToString[i]<>".gen"];
Print[i];
theN3Eqs
,{i,Length[conservativeN3MC]}];


n3mcJointSol = spasmSolveNP[Flatten[allN3Eqs]];


(*ckBasisN3C = replaceInAns[ckBasisN1C,n3mcJointSol];*)
