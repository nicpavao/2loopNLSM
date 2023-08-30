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


<<TetanusLink`
(*Define some convenient defaults*)
WorkingGF = 2^MersennePrimeExponent[7] - 1;
(*WorkingGF = 107;*)
tetanusSolve[system_]:=tetanusSolveFull[system,a,a[1000,0],{-#[[1]]&,-#[[2]]&},GroundField->WorkingGF]
tetanusSolveNP[system_]:=tetanusSolveFull[system,a,a[1000,0],{-#[[1]]&,-#[[2]]&},PrintStatusQ->False,GroundField->WorkingGF]


ffSolver = tetanusSolveNP;
(*ffSolver = spasmSolveNP;*)


loadNPointAnalytics[4];


(* ::Section:: *)
(*Build the two-loop rep*)


(* ::Subsection::Closed:: *)
(*New Construction/Constraint functions*)


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
		giSol = ffSolver[coefEqs[
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
	symSol = Dispatch@ffSolver[coefEqs[checkSymGeneric[diag,makeZBasis[diag,theAns,ColorSignsQ->True,Polarizations->True]],{Z,EE,EP,P,DDM}]];
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
	giSol = ffSolver[coefEqs[
	Table[
		theAns/.makeZBasis[diag,0,Polarizations->True]["ZtoD"]/.e[i]->k[i]/.k[4]->-k[1]-k[2]-k[3]
		/.makeZBasis[diag,0,Polarizations->True]["DtoZ"]/.P[x__]:>0,
	{i,1,4}]//Flatten,
	{Z,EP,EE}]]//Dispatch;
	giAns = theAns/.giSol;
	symSol = Dispatch@ffSolver[coefEqs[checkSymGeneric[diag,makeZBasis[diag,giAns,ColorSignsQ->True,Polarizations->True]],{Z,EE,EP,P}]];
	Sow[symSol];
	giAns/.symSol	*)
]


convertToIdeal[theAns_]:=IdealAns@DeleteCases[CoefficientArrays[theAns,findVars[theAns,{a}]][[-1]]["NonzeroValues"],0]


findGIandSymIdeal[diag_,theAns_IdealAns]:=Block[
	{giSymAns},
	giSymAns = imposeGIandSym[diag,(Array[a[1,#]&,Length[#]] . #&@@theAns)];
	IdealAns@DeleteCases[CoefficientArrays[giSymAns,findVars[giSymAns,{a}]][[-1]]["NonzeroValues"],0]
	
]


findSymIdeal[diag_,theAns_IdealAns]:=Block[
	{giSymAns},
	giSymAns = imposeSym[diag,(Array[a[1,#]&,Length[#]] . #&@@theAns)];
	IdealAns@DeleteCases[CoefficientArrays[giSymAns,findVars[giSymAns,{a}]][[-1]]["NonzeroValues"],0]
	
]


(*findGIandSymIdeal[diag_,theAns_IdealAns]:=Block[
	{giSol,giAns,symSol,giSymAns},
	giSol = ffSolver[coefEqs[
	Table[
		(Array[a[1,#]&,Length[#]] . #&@@theAns)/.makeZBasis[diag,0,Polarizations->True]["ZtoD"]/.e[i]->k[i]/.k[4]->-k[1]-k[2]-k[3]
		/.makeZBasis[diag,0,Polarizations->True]["DtoZ"]/.P[x__]:>0,
	{i,1,4}]//Flatten,
	{Z,EP,EE}]]//Dispatch;
	giAns = (Array[a[1,#]&,Length[#]] . #&@@theAns)/.giSol;
	symSol = Dispatch@ffSolver[coefEqs[checkSymGeneric[diag,makeZBasis[diag,giAns,ColorSignsQ->True,Polarizations->True]],{Z,EE,EP,P}]];
	giSymAns = giAns/.symSol;
	IdealAns@DeleteCases[CoefficientArrays[giSymAns,findVars[giSymAns,{a}]][[-1]]["NonzeroValues"],0]
	
]*)


(* ::Subsection::Closed:: *)
(*Truth from Bern Davies Nohle [1510.03448]*)


Get["bdn-two-ym-numerators.m"];
bdnGraph = vertices;
bdnNumerators = numerators/.{ee[i_,j_]:>d[e[i],e[j]],ke[i_,j_]:>d[If[i>4,l[i],k[i]],e[j]],kk[i_,j_]:>d[If[i>4,l[i],k[i]],If[j>4,l[j],k[j]]]   };


bdnNumeratorsSimp = Cancel/@(bdnNumerators/I/.Ds->4);


bdnBasis = newBasis[bdnGraph,a[1000,0]bdnNumeratorsSimp,ColorSignsQ->True,Polarizations->True];


bdnBasisSTU = newBasis[bdnGraph,a[1000,0]STU bdnNumeratorsSimp,ColorSignsQ->True,Polarizations->True];


(* ::Subsection:: *)
(*Setup*)


fourTwoDiags = SortBy[makeFullBasis[2,4,!tadpoleQ[#]&],{cutLevel[#]&,!planarQ[#]&,-Length/@minimalCycles[#]&}];


mcDiags = Select[fourTwoDiags,idDangTrees[#]==={}&];
graphPlot/@mcDiags


targetDiags = mcDiags[[{1,2,4}]];


(*pc = {{8,l[5]},{8,l[6]}};*)
pcMax = 16;
(*This is more-or-less equivalent to what BDN used*)
pcBDN = Association[#->powerCountOwnBase[targetDiags[[#]],0]&/@Range[3]]
(*A more-lenient power counting choice*)
pc = Association[#->powerCountOwnBase[targetDiags[[#]],-pcMax]&/@Range[3]]


STU = Z[1]Z[2](Z[1]+Z[2]);


Dynamic[diagNum]
makeNL = False;
workingPC = pc;
ckBasisAnsData = Table[
{targetDiags[[diagNum]],
fileName = "init_basis_ans_"<>If[makeNL,"nl",""]<>ToString[diagNum]<>"."<>ToString[WorkingGF]<>".gen";
If[FileExistsQ[fileName],
	giIdeal = Get[fileName];
	,
	
	(*The normal local pieces*)
	contAns = makeContAnsatzViaDioph[targetDiags[[diagNum]],5,workingPC[diagNum],pcMax,{1,1,1,1}];
	mcAns = makeMCAnsatzViaDioph[targetDiags[[diagNum]],5,workingPC[diagNum],pcMax,{1,1,1,1}];
	
	If[makeNL,
		nlPurePropAns = Identity@@makeContAnsatzViaDioph[targetDiags[[diagNum]],6,workingPC[diagNum],pcMax,{1,1,1,1}];
		irredS = DeleteDuplicates[DeleteCases[Flatten[(PolynomialReduce[#,{Z[1]},{Z[1]}]&/@nlPurePropAns)[[All,2]]],0]];
		irredT = DeleteDuplicates[DeleteCases[Flatten[(PolynomialReduce[#,{Z[2]},{Z[2]}]&/@nlPurePropAns)[[All,2]]],0]];
		irredU = DeleteDuplicates[DeleteCases[Flatten[(PolynomialReduce[#,{Z[1]+Z[2]},{Z[1],Z[2]}]&/@nlPurePropAns)[[All,2]]],0]];

		Print[diagNum,":",(Length@@contAns) + (Length@@mcAns) + Length[irredS] + Length[irredT] + Length[irredU]];

		(*Modify the ansatz by multiplying through by (-)s*t*u *)
		mcAns = IdealAns[STU(Identity@@mcAns)];
		contAns = IdealAns[Join[STU(Identity@@contAns),Z[1]Z[2] * irredU, Z[1](Z[1]+Z[2]) irredT, Z[2](Z[1]+Z[2]) irredS]];
		,
		Print[diagNum,":",(Length@@contAns) + (Length@@mcAns)];
		mcAns = IdealAns[STU(Identity@@mcAns)];
		contAns = IdealAns[STU(Identity@@contAns)];
	];

	giIdealMC = findSymIdeal[targetDiags[[diagNum]],mcAns];
	giIdealCont = findSymIdeal[targetDiags[[diagNum]],contAns];
	giIdeal = PolynomialMod[Join[Identity@@giIdealMC,Identity@@giIdealCont],WorkingGF];
	Put[giIdeal,fileName];
];

makeZBasis[targetDiags[[diagNum]],
Array[a[diagNum,#]&,Length[#]] . #&@giIdeal
,ColorSignsQ->True,Polarizations->True]
}
,{diagNum,{1,2,3}}];//AbsoluteTiming


Print["Initial Ans Sizes:",Length[findVars[#,{a}]]&/@ckBasisAnsData]


(* ::Section:: *)
(*Check the Hypothesis*)


hypothBasis = newBasis[ckBasisAnsData[[All,1]],ckBasisAnsData[[All,2]],ColorSignsQ->True,Polarizations->True];


(*Fiddle with the 4-pt labeling to get blowUpGraphCO to produce two DB*)
ktDiag = collapsePropagator[targetDiags[[1]],7]/.{6->8,8->6};
graphPlot@ktDiag


graphPlot/@blowUpGraphCO[ktDiag]


coKTCutEqs = coefEqs[assocTogetherNum[orderedCompareCuts[ktDiag,hypothBasis,bdnBasisSTU]],{Z,EE,EP}];


coKTCutSol = ffSolver[coKTCutEqs];


hypothBasisKT = replaceInAns[hypothBasis,coKTCutSol];


jacobiCont = collapsePropagator[targetDiags[[1]],8];
graphPlot/@blowUpGraph[jacobiCont]


rawJacobi = maschkeJacobi[jacobiCont,hypothBasisKT];


jacobiEqs = PolynomialMod[coefEqs[rawJacobi,{Z,EE,EP,P}],WorkingGF]


ffSolver[jacobiEqs]



