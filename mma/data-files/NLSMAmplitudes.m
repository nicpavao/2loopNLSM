(* ::Package:: *)


NLSM::usage="NLSM[{p1,p2...pN}] returns the Npt NLSM tree amplitude";

Begin["`Private`"]

SumMomenta[p_,c_,n_,i_,j_]:=d2[Sum[p[[Mod[k+c,n,1]]],{k,i,j}]];

NLSM4pt[p_]:=Module[{sm,c,n}, n=4; sm[i_,j_]:=SumMomenta[p,c,n,i,j];1/2 Sum[1/2*sm[1,2],{c,0,n-1}] ];

NLSM6pt[p_]:=Module[{sm,c,n}, n=6;sm[i_,j_]:=SumMomenta[p,c,n,i,j];-1/4 Sum[-1/2(sm[1,2]+sm[2,3])(sm[1,4]+sm[4,5])/sm[1,3]+sm[1,2],{c,0,n-1}] ];

NLSM8pt[p_]:=Module[{sm,c,n}, n=8;sm[i_,j_]:=SumMomenta[p,c,n,i,j];1/8 Sum[1/2*(sm[1,2]+sm[2,3])(sm[1,4]+sm[4,7])(sm[5,6]+sm[6,7])/(sm[1,3]sm[5,7])+(sm[1,2]+sm[2,3])(sm[1,4]+sm[4,5])(sm[6,7]+sm[7,8])/(sm[1,3]sm[6,8])-(sm[1,2]+sm[2,3])(sm[4,5]+sm[4,7]+sm[5,6]+sm[5,8]+sm[6,7]+sm[7,8])/sm[1,3]+2sm[1,2]+1/2*sm[1,4],{c,0,n-1}] ];

NLSM10pt[p_]:=Module[{sm,c,n}, n=10;sm[i_,j_]:=SumMomenta[p,c,n,i,j];-1/16 Sum[-(sm[1,2]+sm[2,3])/sm[1,3](1/2*(sm[1,4]+sm[4,9])(sm[5,8]+sm[6,9])(sm[6,7]+sm[7,8])/(sm[5,9]sm[6,8])+1/2*(sm[1,4]+sm[4,5])(sm[1,8]+sm[6,9])(sm[6,7]+sm[7,8])/(sm[1,5]sm[6,8])+1/2*(sm[1,8]+sm[4,9])(sm[4,5]+sm[5,8])(sm[6,7]+sm[7,8])/(sm[4,8]sm[6,8])+(sm[1,4]+sm[4,5])(sm[1,6]+sm[6,7])(sm[1,8]+sm[8,9])/(sm[1,5]sm[1,7])+(sm[1,4]+sm[4,5])(sm[1,6]+sm[6,9])(sm[7,8]+sm[8,9])/(sm[1,5]sm[7,9])+(sm[1,8]+sm[4,9])(sm[4,7]+sm[5,8])(sm[5,6]+sm[6,7])/(sm[4,8]sm[5,7])+(sm[1,6]+sm[4,9])(sm[4,5]+sm[5,6])(sm[7,8]+sm[8,9])/(sm[4,6]sm[7,9])-1/2*(sm[1,4]+sm[1,8]+sm[4,5]+sm[4,9]+sm[5,8]+sm[6,9])(sm[6,7]+sm[7,8])/sm[6,8]-(sm[1,8]+sm[4,9])(sm[4,5]+sm[4,7]+sm[5,6]+sm[5,8]+sm[6,7]+sm[7,8])/sm[4,8]-(sm[1,4]+sm[1,6]+sm[4,5]+sm[4,7]+sm[5,6]+sm[6,7])(sm[1,8]+sm[8,9])/sm[1,7]-(sm[1,4]+sm[1,6]+sm[4,5]+sm[4,9]+sm[5,6]+sm[6,9])(sm[7,8]+sm[8,9])/sm[7,9]-(sm[1,4]+sm[4,5])(sm[1,6]+sm[1,8]+sm[6,7]+sm[6,9]+sm[7,8]+sm[8,9])/sm[1,5]-(sm[1,4]+sm[4,9])(sm[5,6]+sm[5,8]+sm[6,7]+sm[6,9]+sm[7,8]+sm[8,9])/sm[5,9]+2sm[1,4]+sm[1,6]+2sm[1,8]+2sm[4,5]+sm[4,7]+2sm[4,9]+2sm[5,6]+sm[5,8]+2sm[6,7]+sm[6,9]+2sm[7,8]+2sm[8,9])-1/2*(sm[1,2]+sm[1,4]+sm[2,3]+sm[2,5]+sm[3,4]+sm[4,5])(sm[1,6]+sm[1,8]+sm[6,7]+sm[6,9]+sm[7,8]+sm[8,9])/sm[1,5]+5sm[1,2]+2sm[1,4],{c,0,n-1}]];

NLSM[pList_]:=Switch[Length[pList],4,NLSM4pt[pList],6,NLSM6pt[pList],8,NLSM8pt[pList],10,NLSM10pt[pList]];

End[]

Print["\n ---- NLSM TREE AMPLITUDES ---- \n\n This package implements the 4,6,8,10pt tree amplitudes for the nonlinear sigma model.  The amplitudes were taken from [1304.3048].  The amplitudes are normalized on factorization channels but the normalization in the package seems to differ from the one in the paper."];
