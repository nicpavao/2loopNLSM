(* ::Package:: *)

<<AmpToolsM`


<<"data-files/sGalAmplitudes.m";


(* ::Section:: *)
(*Test 6Points*)


loadNPointAnalytics[6];


sGal[k/@Range[6]]


d[k[1]+k[2]+k[3]]


factorized = sGal[{k[1],k[2],k[3],-k[1]-k[2]-k[3]}]*sGal[{k[1]+k[2]+k[3],k[4],k[5],k[6]}]


theRes = SeriesCoefficient[sGal[k/@Range[6]],{d[k[1],k[3]],-d[k[1],k[2]]-d[k[2],k[3]],-1}]


Reduce[coefEqs[factorized - \[Alpha] theRes/.d[k[1],k[3]]->-d[k[1],k[2]] - d[k[2],k[3]]//Simplify,{d}]==0]


testPerm = RandomSample[k/@Range[6]]


PossibleZeroQ[sGal[k/@Range[6]] - sGal[testPerm]/.k[6]->-Sum[k[i],{i,5}]]


(* ::Section:: *)
(*Test 8Points*)


loadNPointAnalytics[8];


factorized = sGal[{k[1],k[2],k[3],-k[1]-k[2]-k[3]}]*sGal[{k[1]+k[2]+k[3],k[4],k[5],k[6],k[7],k[8]}]


theRes = SeriesCoefficient[sGal[k/@Range[8]],{d[k[1],k[3]],-d[k[1],k[2]]-d[k[2],k[3]],-1}]


ratio = (factorized/theRes)/.d[k[1],k[3]]->-d[k[1],k[2]] - d[k[2],k[3]];


ratioEvals = Table[Dispatch@Thread[#->RandomSample[Prime[Range[2,10^4]],Length[#]]],{i,1,10}]&@
findVars[ratio,{d}]


ratio/.ratioEvals


twoCutSol = ToRules@Reduce[{d[k[1]+k[2]+k[3]]==0,d[k[1]+k[2]+k[3]+k[4]+k[5]]==0},{d[k[1],k[3]],d[k[1],k[4]]}]


factorized2 = sGal[{k[1],k[2],k[3],-k[1]-k[2]-k[3]}]*sGal[{k[1]+k[2]+k[3],k[4],k[5],k[6]+k[7]+k[8]}]sGal[{-k[6]-k[7]-k[8],k[6],k[7],k[8]}]/.twoCutSol;


theRes2 = SeriesCoefficient[theRes,{d[k[1],k[4]],-d[k[1],k[5]]-d[k[2],k[4]]-d[k[2],k[5]]-d[k[3],k[4]]-d[k[3],k[5]]-d[k[4],k[5]],-1}]


factorized2 - theRes2/.twoCutSol//PossibleZeroQ


testPerm = RandomSample[k/@Range[8]]
PossibleZeroQ[sGal[k/@Range[8]] - sGal[testPerm]/.k[8]->-Sum[k[i],{i,7}]]
