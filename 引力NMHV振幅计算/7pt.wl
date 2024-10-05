(* ::Package:: *)

Off[Solve::svars]
SetDirectory[NotebookDirectory[]]
Get[FindFile["SpinorHelicity4D`"]]
<<tree_amplitudes.m


n=7;
k=3;
u=1;
v=2;
r=k+1;
sss=k+2;
cm=Table[Subscript[c, i,j],{i,k},{j,n}];
Subscript[c, i_,j_]:=0/;j<=k&&i<j
Subscript[c, i_,i_]:=1;
Subscript[c, i_,j_]:=Subscript[c, j,i]/;i>j
Gr=DeleteCases[Flatten[cm],_Integer];
gm[i_,j_,k_]:=Transpose[{cm[[All,i]],cm[[All,j]],cm[[All,k]]}];
cd[i_,j_,k_,l_]:=Subscript[c, i,k] Subscript[c, j,l]-Subscript[c, i,l] Subscript[c, j,k];
DD[a_,b_,cc_,d_]:={{Subscript[c, a,cc],Subscript[c, a,d]},{Subscript[c, b,cc],Subscript[c, b,d]}};
H[a_,b_,cc_,d_]:=Det[DD[a,b,cc,d]]/Product[Flatten[DD[a,b,cc,d]][[i]],{i,4}];
Subscript[w1, i_,j_]:=SpinorAngleBracket[i,j]/H[i,j,r,sss];
Subscript[w2, A_,B_]:=SpinorSquareBracket[A,B]/H[A,B,u,v];
cyc[i_,I_]:=If [Mod[i,Length[I]]===0,Length[I],Mod[i,Length[I]]];
V[up_,down_]:=Table[Table[Subscript[c, down[[i]],up[[cyc[j,up]]]] Subscript[c, down[[i]],up[[cyc[j+1,up]]]],{j,Length[up]}],{i,Length[down]}];
J[S_,W_]:=FullSimplify[Product[Subscript[w1, S[[i,1]],S[[i,2]]],{i,Length[S]}]Product[Subscript[w2, W[[i,1]],W[[i,2]]],{i,Length[W]}]Det[DD[u,v,r,sss]]^(1+(k-2)(n-k-2))/(Product[Flatten[DD[u,v,r,sss]][[i]],{i,4}]^2*Product[Gr[[i]],{i,Length[Gr]}])];
Ctilde=Table[Det[V[{a,u,v},{r,sss,B}]],{a,Complement[Range[k],{u,v}]},{B,Complement[Range[k+1,n],{r,sss}]}]//Flatten;
Ct=Product[Ctilde[[i]],{i,Length[Ctilde]}];
(*Cachazo\:7684\:516c\:5f0f\:6709typo\:ff0c\:6240\:4ee5\:4e0b\:9762\:4e58\:4e86\:4e2a\:56e0\:5b50\:ff0c\:4f46\:662f\:516d\:70b9\:5de7\:5408\:6070\:597d\:4e0d\:7528\:4e58*)
Jtrees={J[{{1,2},{2,3}},{{6,5},{5,4},{4,7}}],J[{{1,2},{2,3}},{{4,5},{4,6},{4,7}}]}*Subscript[c, 3,4] Subscript[c, 3,5]
tau=Table[Subscript[\[Tau], i],{i,k+1,n}];
myperm[expr_,l__,list__]:=Module[{return=expr,var=Variables@expr},return/. Table[var[[i]]->(var[[i]]/. Table[l[[b]]->list[[b]],{b,1,Length@l}]),{i,1,Length@var}]];


Sol1=Flatten[Table[{Subscript[c, i,1]-> (SpinorAngleBracket[i,3]-SpinorAngleBracket[2,3] Subscript[\[Tau], i])/SpinorAngleBracket[1,3],Subscript[c, i,2]-> Subscript[\[Tau], i],Subscript[c, i,3]-> -(SpinorAngleBracket[i,1]-SpinorAngleBracket[2,1] Subscript[\[Tau], i])/SpinorAngleBracket[1,3]},{i,k+1,n}]];
JtreesSolution={};
ctreesSolution={};
Jactrees={};
For[q=1,q<=Length[Jtrees],q++,
	Print["\:73b0\:5728\:8ba1\:7b97\:7b2c"<>ToString[q]<>"\:68f5\:6570"];
	cSolution={};
	JSolution={};
	Jacobians={};
	poles=DeleteCases[DeleteCases[Flatten[FactorList[Denominator[Jtrees[[q]]]]],1],-1];
	For[i=1,i<Length[poles],i++,
		For[j=i+1,j<=Length[poles],j++,
			pole={poles[[i]],poles[[j]]};
			PolesProduct=Product[pole[[i]],{i,Length[pole]}];
			Print["\:5f53\:524d\:6c42\:89e3:"<>ToString[pole,TraditionalForm]];
			Eq={pole}/.Sol1;
			Sol2=Solve[Eq==0,tau][[1]];
			index=Table[Sol2[[i]][[1]][[2]],{i,Length[Sol2]}];
			indexbar=Complement[Range[k+1,n],index];
			Eqtau1=Table[Sol2[[i]][[1]]-Sol2[[i]][[2]],{i,Length[Sol2]}];
			Eq2=Table[SpinorSquareBracket[2,i]+Sum[Subscript[\[Tau], j]SpinorSquareBracket[j,i],{j,Range[k+1,n]}],{i,index}];
			Sol3=Together[SchoutenSimplify[Solve[{Eq2==0,Eqtau1==0},tau]]][[1]];
			Solc=Together[Sol1/.Sol3];
			Print["\:7ebf\:6027\:65b9\:7a0b\:7ec4\:6c42\:89e3\:ff1a"<> ToString[Solc,TraditionalForm]];
			
			condition=Flatten[{Eq,Eq2}];
			Jac=SchoutenSimplify[FullSimplify[Det[Table[D[condition[[i]],tau[[j]]],{j,Range[4]},{i,Range[4]}]]*SpinorAngleBracket[1,3]^2/SpinorSquareBracket[index[[1]],index[[2]]]]];
			
			SolJ=(FullSimplify[PolesProduct*Jtrees[[q]]/(Ct*Jac)])/.Solc;
			
			LG=littleGroup[SolJ/.{SpinorAngleBracket->ab,SpinorSquareBracket->sb}];
			If[LG!={4,4,4,-4,-4,-4,-4},Print[LG]];
			
			Print["\:6700\:7ec8\:7ed3\:679c\:4e3a"<>ToString[SolJ,TraditionalForm]];
			AppendTo[cSolution,Solc];
			AppendTo[JSolution,SolJ];
			AppendTo[Jacobians,Jac];
		]
	];
	(*\:4fdd\:5b58\:4e2d\:95f4\:7ed3\:679c\:ff0c\:7b2c\:4e00\:4e2a\:662f\:88ab\:79ef\:51fd\:6570\:ff0c\:7b2c\:4e8c\:4e2a\:662fc\:ff0c\:7b2c\:4e09\:4e2a\:662f\:51d1\:51fa\:6765\:7684\:96c5\:53ef\:6bd4\:ff0c\:7b2c\:56db\:4e2a\:662f\:6b63\:7ecf\:7b97\:51fa\:6765\:7684\:96c5\:53ef\:6bd4\:ff0c\:90fd\:662f\:4e24\:91cd\:5217\:8868*)
	AppendTo[JtreesSolution,JSolution];
	AppendTo[ctreesSolution,cSolution];
	AppendTo[Jactrees,Jacobians];
]


J1Amp=JtreesSolution[[1]];
J2Amp=JtreesSolution[[2]];
permtree1={{1->1},{1->2,2->1},{2->3,3->2}};
permtree21=DeleteDuplicates[Table[Table[i+3->Permutations[{6,5,4,7}][[j]][[i]],{i,4}],{j,4!}],Reverse[#1[[All,2]]]==#2[[All,2]]&];
permtree22={{4->4},{4->5,5->4},{4->6,6->4},{4->7,7->4}};
JoinPerm[a_,b_]:=Flatten[Table[Join[a[[i]],b[[j]]],{i,Length[a]},{j,Length[b]}],1];
perm1={1,2,3,6,5,4,7}/.JoinPerm[permtree1,permtree21];
perm2=Range[7]/.JoinPerm[permtree1,permtree22];
Amp=Total[expandSpinorBrackets[grHelicityAmp[mm,mm,mm,pp,pp,pp,pp]]/.{ab->SpinorAngleBracket,sb->SpinorSquareBracket}];
B=Table[Subscript[b, i],{i,Length[J1Amp]+Length[J2Amp]}];


Eq={};
For[j=1,j<=Length[B],j++,
	GenSpinors[{1,2,3,4,5,6,7},AllMassless-> True];
	AppendTo[Eq,ToNum[Amp-(Sum[B[[1;;Length[J1Amp]]] . myperm[J1Amp,{1,2,3,6,5,4,7},perm1[[i]]],{i,Length[perm1]}]+Sum[B[[Length[J1Amp]+1;;]] . myperm[J2Amp,Range[7],perm2[[i]]],{i,Length[perm2]}])]];
	ClearKinematics
]
SolB=Solve[Eq==0,B]
(*\:68c0\:9a8cMMA\:662f\:5426\:89e3\:5bf9\:65b9\:7a0b*)
Eq/.SolB


DeleteFile["saved7pt.m"]
savefile=File["saved7pt.m"]
Save[savefile,{ctreesSolution,JtreesSolution,Jactrees,JacMP}]
